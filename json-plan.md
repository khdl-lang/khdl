# Implementation plan: compile-time JSON inputs

Status: implemented in the workspace, with the deferred features below remaining out of scope. This document records the agreed design and implementation/validation criteria. Parser research evidence is in [json-parser-report.md](json-parser-report.md).

## Agreed design

- Add optional `[data]` manifest entries mapping logical aliases to individual files or recursive trees of `.json` files, including the source-like `_` convention for omitting a namespace prefix.
- Expose `std.json.load(name, T)`: a compile-time logical-name string and explicit destination type, returning a compile-time value. Failures are compiler diagnostics, not `Result` values.
- Paths exist only in manifests. Relative paths resolve against the containing manifest; absolute paths, external directories, and intentional symlinks are allowed. Source code cannot supply filesystem paths to the load operation.
- Read all declared data files up front as raw UTF-8 strings into the immutable `SourceDatabase`, following existing source collection. No IO occurs during compilation/elaboration.
- Parse/map JSON lazily when ordinary elaboration evaluates a load call. Cache by `(FileId, Type)` in `ElaborationArenas` using `ComputeOnceMap`.
- Use unmodified `json-syntax` 0.13.1 with default features disabled, initially pinned to the researched release. Raise Rust/CI versions as necessary; the Rust minimum is not a reason to reject this parser.
- Use existing KHDL structs/enums as schemas. No arbitrary constructors, dynamic type-name resolution, deserialization hooks, or host code execution.
- Preserve JSON byte spans for high-quality diagnostics, including both duplicate key occurrences.
- Standard `Option(T)` maps null to `None` and non-null input to `Some(decoded T)`. Reject a schema if an option payload itself accepts null. No tagged option fallback.
- Anticipate future language-defined field defaults and future arbitrary conversion through `any`, including nested `any` positions. Neither feature is implemented now.
- Multiple manifests, visibility/delegation rules, handles/capabilities, inferred JSON types, and data glob patterns are deferred. Recursive directory entries are included in this implementation.
- Dedicated depth/resource protection is deferred, consistently with current compiler limitations. The researched deep-tree stack overflow remains a known availability limitation; deferral is not a claim of complete safety against hostile inputs or a completed security audit.

## User-visible behavior

### Manifest and API

```toml
[source]
_ = "src"

[data]
config = "data/config.json"
vendor_table = "/opt/vendor/ip/tables/device.json"
tables = "data/tables" # recursively collect .json files under this prefix

foo.coefficients_0 = "data/coefficients_0.json"
foo.coefficients_1 = "data/coefficients_1.json"
```

Use TOML dotted keys to put the logical prefix directly in each key under `[data]`. For example, `foo.coefficients_0` selects the corresponding explicit file. TOML represents these keys as nested tables, so the equivalent `[data.foo]` spelling also works without a separate syntax or parser rule. String leaves name either individual files or directories; determine file versus directory during collection, as for source entries. An absent `[data]` gives an empty registry and preserves existing projects.

Use unquoted dots as TOML key separators. A quoted whole key such as `"foo.coefficients_0"` is a literal TOML key containing a dot, not a dotted path; the initial design does not add a second alias-splitting rule for such literal keys. Quoting individual valid components is equivalent to leaving those components unquoted.

For a directory entry, recursively select files with the exact `.json` extension. Append relative directory components and the file stem to the entry's namespace, stripping only the final `.json` extension:

```text
data/tables/filter.json       -> tables.filter
data/tables/device/a.json     -> tables.device.a
```

Ignore non-JSON files discovered through directory traversal. Explicit single-file entries use their declared alias, without deriving it from the filename or requiring a particular extension. Use source-like identifier validation for alias components, including directory-derived components and stems. Report invalid derived names rather than silently skipping matching files. Reject unsupported manifest leaf types and duplicate full aliases, including collisions between explicit entries, overlapping directory entries, and flattened namespaces. Include both declaring manifest entries and relevant physical paths in collision diagnostics. Sort discovered relative paths for deterministic collection/diagnostics.

Reuse the source manifest's `_` convention: that key contributes no alias component. For example, this alternative manifest section collects a whole tree without a prefix:

```toml
[data]
_ = "data"
```

Here `data/device/a.json` becomes `device.a`. Apply flattening consistently inside nested tables as well. An explicit file must still have a nonempty resulting alias; a root `_` entry naming a single file is an error. Directory and explicit-file entries follow the same agreed manifest-relative, absolute-path, and intentional-symlink policy. Glob patterns are not part of this syntax.

```khdl
import std.json;

struct Config { width: int(1..=64), enabled: bool }
const config = json.load("config", Config);
```

The standard wrapper's intended signature is `pub fn load(name: str, T: type) -> T`, implemented through a new JSON builtin. Both argument values must be compile-time values. Calls inside module/hardware elaboration are allowed when their arguments are compile-time; the result remains compile-time. No KHDL grammar changes or special import declarations are required.

Computed names such as `"foo.coefficients_{i}"` select among manifest-declared aliases during generic elaboration. They never construct disk filenames. Reject empty names/components, path separators, unknown aliases, and invalid logical-name components. Never fall back to filesystem lookup or source-item lookup. Existing imports use `SimpleIdentifier` and do not support `ident(...)`; this design does not change them.

Initially all loads use the current project's one data registry, including calls through standard-library wrappers. Do not introduce dynamic call-stack-based authority or process-global state. Multiple-manifest resolution context and wrapper provenance will be designed when that feature is added.

### Collection versus elaboration failures

This supersedes the earlier draft's proposal for lazy physical file IO:

| Situation | When it is diagnosed |
| --- | --- |
| Invalid manifest alias/entry | Manifest parsing/collection |
| Missing/unreadable entry, directory enumeration failure, invalid derived alias/collision, invalid UTF-8 in a selected file, unsupported file kind | Up-front collection, even if unused |
| Unknown logical name | When the load call is evaluated |
| Invalid JSON syntax | When a load call for that file is evaluated |
| Unsupported schema or failed mapping | When the load call is evaluated |
| Unused validly collected input containing malformed JSON | No JSON parsing error unless a load is evaluated |

All IO is complete before the immutable compilation inputs are constructed. Up-front reads fix input contents during elaboration, but are not an atomic filesystem snapshot across concurrent external edits.

## Architecture and data flow

```text
manifest / in-memory host inputs
    -> collect KHDL and all declared data text
    -> SourceDatabase + SourceHierarchy + DataInputs
    -> ParsedDatabase (KHDL hierarchy files only)
    -> CompileFixed / CompileShared
    -> std.json.load(name, T)
    -> resolve alias to FileId; prepare/validate schema
    -> cached parse + mapping for (FileId, T)
    -> CompileValue or structured diagnostic
```

### Immutable input registry

Add a small `DataInputs` registry, preferably in a focused `syntax/data.rs` module, mapping alias component vectors to entries containing `FileId` and manifest declaration spans. It is separate from `SourceHierarchy`, so matching source/data names are not ambiguous and JSON is never parsed as KHDL.

Add `data: &DataInputs` to `CompileFixed`. Update every constructor/destructuring site in the CLI, Python, WASM, LSP, and tests; empty input sets receive an empty registry. Do not make `SourceDatabase` mutable during compilation or introduce a new IO-provider/query framework.

Provide a shared data-collection helper accepting a host read callback, analogous to `add_source_files_to_tree`. Resolve paths using the same manifest-relative/absolute principles as source collection. For directory entries, generalize/extract the existing tree enumeration and extension filtering (currently hardcoded to `.kh` in `collect_source_files_from_tree`) so data can collect `.json` trees without changing source import semantics. Apply deterministic sorting and alias validation/collision checks to the resulting data entries. Read all selected raw strings and register normal `FileId`/line offsets without invoking the JSON parser. Follow intentionally declared symlinks, and report unsupported file kinds and traversal failures at the manifest entry. Do not expand this feature into unrelated source-traversal hardening.

Do not require symlink canonicalization or physical-file deduplication. Different aliases may share a `FileId` when the host deliberately reuses collected text, but the cache does not identify files by path strings or contents. Preserve a file-to-path map for LSP diagnostics. Rebuilding compilation state after edits naturally gives a fresh cache; never reuse cache entries by raw `FileId` across databases.

`SourceDatabase::files()` and `total_lines_of_code()` cover all stored text, including non-KHDL files already. Review consumers so formatting, language parsing, Python source listings, and reported KHDL source statistics do not accidentally treat JSON as KHDL. Prefer source-hierarchy enumeration where a caller specifically means KHDL files, rather than broad source-database redesign.

### Parser and mapping modules

Add a focused `front/json.rs` module registered in `front/mod.rs`. It can contain internal parser adapters, schema preparation, and recursive conversion helpers initially; split only if their size warrants it.

Use `json_syntax::JsonValue::parse_str` with strict parser defaults, retaining its code map. The adapter converts byte ranges to `file.span(range)` and never searches decoded text for its source position. Traverse object entries and code-map fragment offsets together, preserving source order and raw numeric text. Do not convert through `serde_json::Value`, which loses the required duplicate/range representation.

Keep syntax parsing separate from schema conversion even if both happen within one cache computation. Use the library-owned tree/map initially; do not add a new arena representation, parser fork, preflight scanner, or second validation parser. Revisit representation only if implementation reveals a concrete missing capability.

### Cache and reentrancy

Add a field/accessor in `ElaborationArenas` backed by:

```rust
ComputeOnceMap<(FileId, Type), Result<CompileValue, JsonLoadError>>
```

This follows Karel's suggested key and placement, with a failure representation so unsuccessful mapping is cached as well. `Type` already implements `Clone`, `Eq`, and `Hash`; struct/enum keys retain nominal elaborated identities. Return/clone cached values using existing `CompileValue` conventions. Alias names and call-site spans do not belong in the key: they do not change decoding for a given collected file/type.

`JsonLoadError` should retain reusable JSON/schema labels and error details, without reporting into a particular thread's `Diagnostics` or capturing a first caller's span. At the builtin boundary, render a fresh diagnostic with the current call's context. This avoids nondeterministic "first thread wins" caller labels and allows repeated calls to share a failure. A cloneable unreported `DiagnosticError` can be used if it cleanly supplies this separation; a new general diagnostics framework is unnecessary.

The existing `ComputeOnceMap` uses `OnceLock::get_or_init` and has no cycle detection. Resolve the destination type, obtain standard-option metadata, and prepare/validate schemas through ordinary elaboration **before entering** the `(FileId, T)` cache initialization. Inside initialization, access only immutable collected text, the prepared schema, and already available type metadata. Do not call user functions, evaluate types, or recursively call `json.load` from the closure. This avoids introducing a new reentrant cache dependency. Continue using existing elaboration mechanisms for type/value cycles; do not claim this map fixes existing generic-type deadlocks.

Start with one conversion cache. A load of the same file with a different target type may parse that text again; this is acceptable initially. A second `FileId -> parsed document` cache is an optional later optimization, not a prerequisite. No persistent cache, custom invalidation system, or general query-refactor migration is required.

## Destination schemas and conversion

Validate the full reachable schema before decoding, including fields absent from the JSON and unselected enum payloads, and keep unsupported-type errors tied to available schema declaration spans. Initially prepare a schema tree per call; recursive types remain subject to existing type elaboration restrictions. Separate memoization of schema preparation is a later optimization, alongside the optional parsed-document cache.

| Destination | Accepted JSON and conversion |
| --- | --- |
| `bool` | Boolean only |
| `str` | String, using strict Unicode decoding |
| Integer type | Integer token parsed exactly into KHDL `BigInt`, then checked against the destination's ranges |
| `[N]T` | Array of exactly `N` elements, each decoded against `T` |
| `[_]T` | Array of any length, each decoded against `T` |
| `Tuple(T0, T1, ...)` | Array with exact arity and positional conversion |
| Empty tuple | Empty JSON array |
| Struct | Object with exact decoded field-name matching; order irrelevant |
| Ordinary payload-free enum variant | String naming a variant of the supplied enum |
| Ordinary enum payload variant | Single-entry object whose key names a variant and whose value maps to its payload type |
| Standard `Option(T)` | Null -> `None`; non-null -> `Some(decoded T)`, subject to the nullable-payload restriction |

Reject decimal/exponent tokens, including `1.0` and `1e3`, before any floating-point conversion. Accept integer spelling such as `-0` as integer zero, subject to range membership. Strict JSON parsing handles leading-zero and other lexical errors.

Reject `any` for now, unspecified `Tuple`, `type`, functions, modules, interfaces, packages, references, ranges, and `Undefined`. Generic schemas must be instantiated before mapping; JSON never supplies arbitrary KHDL type names or generic instantiations.

Construct `StructValue`/`EnumValue` and the existing scalar/array/tuple values directly. Do not call `.new` overrides, user factories, methods, conversion hooks, or host callbacks based on input text. Existing hardware checks still apply when decoded values are later used as hardware; compile-time configuration may include strings or unspecified array lengths.

### Objects, arrays, and enums

- Preserve duplicates long enough to compare decoded keys and label both occurrences, including `"a"` versus `"\u0061"`. Reject duplicates rather than silently selecting a value.
- Reject extra fields and unknown variants; report at the original key/tag span. Avoid trial-decoding untagged enums.
- Match fields by name, then store their values in destination declaration order with the exact supplied struct identity.
- Empty arrays are valid for unspecified/zero length destinations. Fixed nested lengths enforce rectangular arrays; unspecified inner lengths permit ragged arrays.
- Array values currently infer their type from their contents, with a bottom element type for an empty array. Validate against the schema without promising the value's inferred type exactly equals that schema. Do not redesign array typing for this feature.
- Ordinary enum encodings include `"Idle"` and `{"Transfer": {"address": 32, "length": 8}}`. Reject multi-entry tag objects and missing/wrong payloads. Standard options use the special nullable mapping instead.

### Standard Option identity and null

Recognize standard `Option` by declaration identity, never by matching a user-visible name or enum shape. Resolve the canonical `std.types.Option` generic enum through existing item resolution and extract the `UniqueDeclaration` from its `FunctionItemBody::Enum` metadata. Compare that identity with `ElaboratedEnumInfo.unique`; the actual `Some` payload type comes from the elaborated enum metadata. Do this before cache initialization, retaining only the metadata needed for conversion. No generic enum arena redesign is required.

Check `accepts_json_null(T)` during schema preparation. Initially only the standard option mapping accepts null. Reject `Option(T)` when its payload itself accepts null, including through aliases, at any position in the schema. Thus `Option(Option(int))` is unsupported, while `Option([_]Option(int))` and an optional struct with optional fields remain unambiguous. Diagnose the conflicting layers where spans are available. A user enum named `Option` follows ordinary enum rules.

Missing fields and explicit null remain distinct. A field of type `Option(T)` is required unless it has a future explicit language-defined default. No tagged option encoding or selectable encoding policy is added.

### Future defaults and `any`

All struct fields are required today: `StructField` contains a name/type, and generated `.new` requires every field. Put missing-field handling behind a small construction/default-resolution boundary so future language-defined defaults can share semantics with ordinary construction. Do not implement defaults now. Once available, a missing field can use its declared default; a present null still goes through its field type's mapping. Future default scope, dependencies, order, type checking, and diagnostics must follow ordinary KHDL elaboration, not JSON-selected hooks.

At every recursive conversion step, dispatch on the target type. Reserve `Type::Any` for future arbitrary conversion: root `any` converts the whole document, while a struct field/array element/tuple element/enum payload typed `any` converts only that subtree arbitrarily. Reject it now with "not supported yet," rather than define it as permanently invalid or silently skip/discard input. The public signature and cache key need no change for that extension.

Do not prematurely settle generated struct identity, heterogeneous arrays, or how nullable `any` interacts with `Option(any)`. Those remain future design decisions. The null-acceptance predicate provides the place to extend the option ambiguity check later.

Karel's proposed representation for arbitrary JSON null is worth preserving for that future design. Additions to `std.types` would be:

```khdl
pub enum Never {}
pub const null = Option(Never).None;
```

`Never` is an uninhabited type: `Option(Never)` can represent `None` while its `Some` variant has no inhabitable payload. A future arbitrary conversion could return this `null` value instead of adding a JSON-only null type. The same `Never` type could also serve as the result type of `return`, `break`, and `continue` if those become expressions. This is a deferred proposal, not part of the initial stdlib/API implementation. Review empty-enum/uninhabited-type behavior and conversions when implementing it; do not silently equate this nominal enum with the existing internal `Type::Undefined` lattice bottom. Preserve ordinary typed `Option(T)` null mapping in the meantime.

## Diagnostics

Use existing KHDL diagnostics with primary labels on JSON source and secondary labels on schema declarations, manifest entries, and relevant user load calls:

- Syntax errors: parser byte position/span; expand zero-width unexpected-character positions to the relevant UTF-8 character where appropriate, keeping EOF zero-width.
- Duplicate fields: both original key spans.
- Wrong kinds, integer range errors, invalid numeric notation: offending value/token span and required destination type.
- Extra fields/unknown variants: original key/tag and expected schema.
- Missing fields/wrong array lengths: object/array container plus destination declaration.
- Nested mapping failures: include a logical path such as `$.channels[3].width` or an escaped key/index path for unusual keys.
- Unknown data names: user call/name context; IO failures: manifest path entry.

The stdlib wrapper means the intrinsic expression is located in `std/json.kh`. Ensure errors also identify the relevant user call using existing `StackEntry::FunctionCall` information; add a narrowly scoped helper if necessary. Do not globally redesign caller provenance or defer ordinary load diagnostics to the future manifest-visibility work.

Cached failures must not store the first caller's context. Test repeated loads and parallel compilation for stable error content and useful call locations. It is acceptable to report a reusable failure at multiple distinct load calls, but avoid duplicate reports within one item evaluation. Successful values need not retain a new per-value provenance tree; source/code-map spans are required during decoding and for cached errors.

## Elaboration scheduling and limits

No new data work-item kind or initial queue is needed. Existing items containing calls are the units of eager/lazy checking:

- `QueueItems::All` evaluates a file-level constant containing a load, including unused constants.
- `QueueItems::None` / top-only compilation evaluates such constants when reached by ordinary dependencies.
- Generic function/type/module calls select names and schemas when ordinary elaboration reaches concrete arguments; do not enumerate possible inputs/instantiations.
- Raw declared files are all read up front, but are not independently queued for JSON parsing or mapping.

Preserve existing compiler cancellation checks at load entry and natural conversion boundaries. Do not promise prompt cancellation while the unmodified parser runs. No dedicated preflight depth scanner, allocation quotas, custom cancellation adapter, safe-drop arena, or denial-of-service hardening is part of this implementation. Record the parser's known deep-tree drop abort and ordinary memory/CPU exhaustion as deferred availability work. This does not authorize additional filesystem access, arbitrary host execution, or writes.

## Implementation sequence and completion criteria

### 1. Dependency and stdlib-facing API

Files: `rust/Cargo.toml`, `rust/Cargo.lock`, `rust/khdl_language/Cargo.toml`, `.github/workflows/ci.yml`, and any release workflow/toolchain references found during implementation.

- Add exact `json-syntax = 0.13.1` with default features disabled; do not replace unrelated `serde_json` usage.
- Raise the declared Rust minimum and pinned CI toolchain consistently to 1.96 or the minimum required by the resolved graph. Verify the actual selected version, including WASM compilation.
- Add `rust/khdl_std/src/std/json.kh` with the `load(name, T)` wrapper. The stdlib build script already discovers `.kh` files; no prelude import is required for this module.

Complete when the dependency builds in supported configurations and the planned wrapper/builtin boundary requires no grammar change. Land the callable builtin with its implementation in step 4, rather than leave a broken public function between changes.

### 2. Manifest entries and immutable collection

Files: `syntax/manifest.rs`, new `syntax/data.rs`, `syntax/collect.rs`, and `syntax/mod.rs`.

- Add optional `ManifestData`/data entries with alias components from TOML dotted keys or equivalent nested tables, `_` flattening, file/directory paths, and declaration spans. Keep required `[source]` behavior unchanged.
- Generalize/extract source-tree enumeration/extension filtering for recursive `.json` discovery. Sort data discovery results, derive relative aliases, and combine them with explicit file entries.
- Add the `DataInputs` registry and a callback-based helper that reads all selected raw data into `SourceDatabase` during collection. Keep source-only collection usable by the formatter.
- Diagnose bad declared/derived aliases, duplicate logical definitions across explicit/directory/flattened entries, non-string leaves, unsupported file kinds, traversal failures, UTF-8 failures, and IO failures with manifest spans. Preserve relative/absolute/symlink semantics.
- Add fixtures proving JSON text is stored for diagnostics and excluded from the KHDL hierarchy/parser.

Complete when hosts can construct `(source, hierarchy, data)` with immutable raw data, including in-memory data, without parsing JSON yet.

### 3. Schema preparation, parser adapter, and conversion

Files: new `front/json.rs`, `front/mod.rs`, and small metadata helpers in `front/item.rs`/`front/compile.rs` as needed.

- Implement reusable unreported JSON errors and parser/code-map adaptation.
- Implement recursive schema preparation and nullable-payload validation, including canonical Option identity and explicit rejection of `any` for now.
- Implement all mapping rules and diagnostic paths using existing values and field/variant metadata.
- Keep type/default preparation outside parser/mapping cache closures. Add no user construction hooks.

Complete when focused Rust tests exercise conversion and byte spans from preloaded text and supplied elaborated schemas, without host IO or hardware lowering.

### 4. Intrinsic, cache, and compiler context

Files: `front/builtin.rs`, `front/item.rs`, `front/compile.rs`, `std/json.kh`, and every `CompileFixed` construction site.

- Add `CompileFixed.data`, empty-registry handling, and the cache field/accessor in `ElaborationArenas`.
- Add the builtin implementation invoked by the wrapper. Require compile-time string/type arguments, resolve only registered aliases, prepare the schema, compute/reuse the `(FileId, Type)` result, and report failures at current call context.
- Ensure the initializer cannot reenter elaboration or another load. Use ordinary item scheduling rather than a JSON work queue.
- Keep cached value/error data independent of thread-local diagnostics and the caller's alias spelling.

Complete when file-level, generic, module-body, repeated, differently typed, and parallel loads behave correctly in both queue modes.

### 5. Host integrations

- **CLI (`khdl_bin/src/main_build.rs`):** collect data before `ParsedDatabase`/compilation setup, pass the registry, report collection errors, and keep source listings/statistics meaningful.
- **Python (`khdl_python/src/lib.rs` and relevant stubs/docs):** retain data in `Source`, load manifest data up front, provide an in-memory `add_data_content`-style method before parsing/compilation, and pass the registry through every compile/evaluation helper. This API must not open arbitrary paths during elaboration.
- **LSP (`server/compile.rs`, VFS/watch helpers):** collect all manifest data through the existing VFS overlay, add exact-file watchers for explicit files and recursive `.json` watchers for directory entries, populate `file_to_path`, and publish JSON diagnostics at JSON URIs. New/deleted files in declared trees must trigger re-enumeration so the alias registry stays current. Use existing unsaved-buffer overlays where available; no new editor protocol is required. On changes, rebuild source/data/compilation state together so old `FileId` caches cannot survive. Changes to data alone must trigger recompilation and clear stale diagnostics.
- **WASM (`khdl_wasm/src/lib.rs`):** update existing compilation setup with an empty registry and provide a backwards-compatible entry point accepting in-memory alias/text inputs for JSON-enabled callers. Existing `run_all` continues to work unchanged; no filesystem assumptions or web-demo file-upload UI is required.
- **Formatter (`main_fmt.rs`):** accept the extended manifest but keep source-only collection/formatting. Do not read or rewrite data just to format KHDL.

Complete when each frontend can compile with the new context, and callers capable of supplying data can load it without adding elaboration-time IO.

### 6. Validation and documentation

Add focused adapter/mapping tests in `khdl_language` and end-to-end coverage alongside existing Python expression/import/query tests. Use temporary manifest projects and in-memory inputs; no Verilator simulation is required for most tests.

Required cases:

- Every supported scalar/compound/root kind, exact very large integers, range boundaries, `-0`, forbidden fraction/exponent tokens, and strict Unicode/syntax handling.
- Empty/fixed/unspecified/ragged arrays, tuples and arity errors, declaration identity/order, ordinary enum tags/payloads, and all null/option ambiguity examples.
- Duplicate equivalent escaped keys, extra/missing fields, unusual valid field keys, unsupported schema members including nested `any`, and a user-defined lookalike `Option`.
- Exact spans through UTF-8 and escapes; EOF, numeric tokens, both duplicate keys, schema locations, and user calls through the wrapper.
- Explicit file and recursive directory entries; equivalent dotted-key/nested-table declarations; prefix/relative-path/stem derivation; nested/root `_` flattening; ignored non-JSON files; invalid derived names; overlapping-entry collisions; and deterministic discovery ordering.
- Nested data aliases, computed generic selection, absolute/relative/external/symlink paths for files and trees, unknown names, and attempts to use undeclared/absolute paths directly from `.kh`.
- Up-front failure for missing/unreadable/non-UTF-8 declared inputs even when unused; no JSON parsing error for unused malformed text; eager versus top-only constants containing loads.
- Same key reused, one file with different schemas, repeated cached failures at different call sites, parallel loads, and no new cache reentrancy. Verify re-collection after data edits and file creation/deletion in declared trees through LSP.
- Python/in-memory data registration, WASM entry-point compatibility, and formatter preservation of data contents.

Run relevant Rust/Python tests during each step, then repository-required checks: Rust formatting, Clippy, workspace tests, Python tests/build, and WASM compilation consistent with CI. Update README/language examples and public API documentation. Record the accepted availability limitation without claiming resource safety. Reuse suitable parser regression inputs from the report; do not add a full upstream parser test suite or dangerous deep-stack-abort tests to normal compiler tests.

Complete when all supported mappings and failure boundaries are documented and the affected frontend/CI checks pass. Future-default semantics and arbitrary `any` mapping remain explicitly unimplemented.

## Deferred work and future manifest graphs

The following do not block this implementation:

- Arbitrary conversion using `any`, generated type identity, heterogeneous arrays, and the proposed `Never` / `null = Option(Never).None` representation. Potential use of `Never` for control-flow expressions is also deferred.
- Struct field defaults; custom schema constraints/validation hooks; dependent JSON-derived type inference.
- Cross-manifest lookup scope, delegation, re-exports, handles/capabilities, data glob patterns, or computed import syntax.
- A separate parsed-document cache, persistent/incremental cache reuse, dedicated resource budgets, and parser-internal cancellation.

When multiple manifests are added, preserve the intended boundary of a file's owning manifest plus referenced manifests for both source and data. The graph may have cycles; discovery and visibility computation must tolerate them. Decide direct versus transitive visibility, qualifying names, physical manifest identity through symlinks, and shared physical files with different owners then. Manifest-reference cycles are not automatically type/value elaboration cycles. The initial separate data registry and `FileId`-based mapping cache leave room for owner-scoped lookup without deciding those rules now.
