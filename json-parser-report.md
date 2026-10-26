# JSON parser research for KHDL

Research date: 2026-10-25. This is a comparison of pinned releases, source inspection, and isolated behavioral probes. It does not select a parser or implement JSON support in KHDL. Requirements are recorded in [json-plan.md](json-plan.md).

Subsequent design decision: use unmodified `json-syntax` 0.13.1 and a KHDL adapter, permitting a Rust minimum-version bump. Dedicated depth/resource protection is deferred, with the availability limitations below acknowledged. Following Karel's guidance, the implementation plan now reads all declared data text up front into immutable `SourceDatabase`; JSON parsing/mapping remains lazy and cached by `(FileId, Type)` in `ElaborationArenas`. The findings below remain the research record; resource-hardening recommendations are follow-up work rather than initial implementation prerequisites. See the updated [implementation plan](json-plan.md) for the current scope.

## Findings

Three approaches remain worth considering:

1. **Adapt `jsonc-parser`'s AST parser.** It provides direct byte ranges, raw number lexemes, and duplicate-preserving objects with no mandatory external dependencies. However, version 0.33.2 accepts invalid JSON even with every extension option disabled. Strict lexical validation needs fixes or an additional validation layer. Its borrowed AST also needs an ownership strategy for query caching.
2. **Use `json-syntax` with explicit resource limits.** Both examined releases provide the required source mapping and exact numbers, preserve duplicates, and passed the corpus's required syntax cases. Version 0.13.1 requires Rust 1.96, above KHDL's declared 1.95; 0.12.5 declares 1.71. Both need protection against excessive nesting, including during destruction of returned values.
3. **Build a JSON parser using KHDL's tokenizer/LALRPOP/diagnostic strategy.** This gives direct control over spans, limits, cancellation, representation, and error presentation. Existing infrastructure can be shared, but JSON's token and string rules need a separate implementation and substantial correctness testing.

`json-spanned-value` 0.2.2 has concrete span and precision problems in the probes and is a weaker starting point. Ordinary `serde_json` remains a useful reference and possible implementation source, but its normal API does not provide the complete span representation required here.

No examined library provides the entire KHDL adapter, schema decoder, resource accounting, cancellation, lazy input/query integration, and diagnostic presentation unchanged. These are separate from the choice of JSON grammar implementation.

## Scope and method

Examined published source archives:

| Package | Version | License declared by package | Toolchain notes |
| --- | --- | --- | --- |
| `jsonc-parser` | 0.33.2 | MIT | Edition 2024; no explicit `rust-version` |
| `json-syntax` | 0.13.1 | MIT / Apache-2.0, choice offered in license text | `rust-version = 1.96.0` |
| `json-syntax` | 0.12.5 | MIT / Apache-2.0, choice offered in license text | `rust-version = 1.71.0` |
| `json-spanned-value` | 0.2.2 | Apache-2.0 OR MIT | Edition 2018; no explicit `rust-version` |
| `serde_json` | 1.0.149 | MIT OR Apache-2.0 | Already installed in the local Cargo registry; baseline |

Package metadata sources: [jsonc-parser 0.33.2 Cargo.toml](https://docs.rs/crate/jsonc-parser/0.33.2/source/Cargo.toml), [json-syntax 0.13.1 Cargo.toml](https://docs.rs/crate/json-syntax/0.13.1/source/Cargo.toml), [json-syntax 0.12.5 Cargo.toml](https://docs.rs/crate/json-syntax/0.12.5/source/Cargo.toml), [json-spanned-value 0.2.2 Cargo.toml](https://docs.rs/crate/json-spanned-value/0.2.2/source/Cargo.toml). Retain applicable notices if adapting or copying code; transitive dependencies also need review before adoption.

The isolated harness used path dependencies on these downloaded archives, with default features disabled for `jsonc-parser` and both `json-syntax` versions. `json-spanned-value` used its default configuration. The baseline initially had no `arbitrary_precision`; a separate run enabled it. A subsequent probe enabled `serde_json/raw_value` to inspect that alternative.

Tests ran natively on Linux with Rust 1.99.1. They do **not** establish minimum-version compatibility, WASM behavior, a full security audit, or performance. Rust 1.95 and WASM were not tested. No production KHDL code or Cargo dependencies were changed. Research harnesses and downloaded sources were placed in `/tmp/khdl-json-parser-research`.

Online documentation can mix release information: in particular, the currently served `jsonc-parser` source documentation showed more extension flags than the downloaded 0.33.2 archive. Findings below refer to the actual pinned archives, not an assumed current API.

## Requirements used for comparison

- Strict JSON syntax, with an explicit stricter Unicode policy that rejects unpaired surrogate escapes rather than silently replacing them. Such escapes are a known JSON interoperability edge case; distinguish that policy from ordinary grammar conformance.
- Half-open UTF-8 byte ranges for values, keys, and containers, plus syntax-error positions.
- Exact integer lexemes; decimals/exponents may parse as JSON syntax but are rejected by the initial KHDL mapping policy. Never round accepted integers through floating point.
- Preserve duplicate entries, including equivalent decoded keys, until KHDL can report both occurrences.
- Pure parsing of supplied text, independent of filesystem authorization and destination-type conversion.
- Bounded resource consumption, including parsing, mapping, cloning, and dropping data structures; integration with compilation cancellation.
- A representation that can be retained safely across parallel compiler queries and incremental revisions.

## Comparison

| Property | jsonc-parser 0.33.2 AST | json-syntax 0.13.1 / 0.12.5 | json-spanned-value 0.2.2 | serde_json normal Value |
| --- | --- | --- | --- | --- |
| Value/container byte spans | Direct node ranges | Separate code map | Present, but root number EOF bug | Absent |
| Object key byte spans | Direct key ranges | Code-map key fragments | Spanned keys | Absent |
| Original number text | Borrowed `&str` | Owned lexical representation | Source slice possible only if span is correct; normal numeric value may round | Requires additional representation/features |
| Both duplicate entries retained | Yes, property vector | Yes | No: reject or overwrite | No: overwrite |
| Required syntax corpus cases | Four invalid cases accepted | No required-case mismatches | Two duplicate-key cases rejected intentionally | No required-case mismatches |
| Empty input | Returns success with no value; adapter must reject | Error | Error | Error |
| Nesting behavior | Recursive AST parser, internal limit 512 | Iterative value parsing; no general exposed depth budget found | Inherits normal Serde parsing depth checks | Normal Value parsing has depth checks |
| Cancellation hook | None found | Character-stream entry point can help | No dedicated hook found | No dedicated span-aware hook |
| Query ownership | Borrows input; conversion/ownership design needed | Owned value plus map | Owned, with thread-local parsing bookkeeping | Owned |

The matrix describes the tested APIs, not every possible use or modification of each package. All candidates still need KHDL-specific schema conversion and diagnostics.

## jsonc-parser 0.33.2

### Useful representation

Use `parse_to_ast`, not `parse_to_value`, CST manipulation, or conversion to `serde_json::Value`. The AST has:

- A range on each value, array, object, and property name.
- `NumberLit.value: &str`, allowing exact integer conversion and detection of decimal/exponent notation.
- Decoded strings represented by `Cow<str>`.
- Objects stored as `Vec<ObjectProp>`, retaining duplicate entries in source order.

These are a good match for duplicate diagnostics and mapping object fields into declaration order. `common::Ranged` explicitly defines byte indices with an exclusive end. [Pinned ast.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/ast.rs), [common.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/common.rs).

`ParseError` exposes both a byte range and an error kind, so KHDL can render its own diagnostics instead of printing the library's line/column message. With `CollectOptions` left at defaults, token/comment collection is off. The package's external dependencies are all optional; the tested AST configuration has no mandatory external dependencies. [errors.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/errors.rs), [Cargo.toml](https://docs.rs/crate/jsonc-parser/0.33.2/source/Cargo.toml).

### Strictness problems observed

The pinned version has seven extension flags. All were explicitly false: comments, loose names, trailing commas, missing commas, single quotes, hexadecimal numbers, and unary plus. Do not use `Default`, which enables them.

Even in that configuration, it accepted:

- A raw newline, tab, or NUL inside a quoted string.
- Vertical tab/form feed as whitespace outside strings; source inspection also shows acceptance of other Unicode whitespace via `char::is_whitespace`.

The scanner's whitespace rules are broader than JSON's four whitespace characters, and the string parser lacks the required raw-control-character rejection. This is a release-specific measured finding, not a claim that every later release has the same behavior. [scanner.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/scanner.rs), [string.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/string.rs).

Possible adaptations:

1. Fix strict whitespace/control-character handling upstream or in a small licensed fork, with regression coverage.
2. Add a strict lexical preflight that also checks nesting/budgets. This avoids changing the dependency but introduces a second scanner that must itself be correct.
3. Validate with another strict JSON parser before obtaining this AST. This adds a second pass and does not automatically provide byte ranges for validation failures. A normal `serde_json::Value` validation pass would also impose numeric conversion limits; `RawValue` behaves differently, as discussed below.

None is selected. Test the exact version eventually chosen; extension flags alone did not establish strictness here.

### Limits, errors, and ownership

The AST parser uses recursive calls and an internal `maximum_nesting_depth` of 512. It rejected a 600-level array. That limit is not a public `ParseOptions` field in 0.33.2, and it is not a general node/string/integer/cancellation budget. Smaller-stack targets may need a lower enforced limit before AST construction. Empty/whitespace-only input returns `Ok` with `value = None`, which the KHDL adapter must turn into an error. [parse_to_ast.rs](https://docs.rs/crate/jsonc-parser/0.33.2/source/src/parse_to_ast.rs).

The successful AST borrows the input. Returning and caching an object that owns both input text and references into itself needs a deliberate design. A KHDL-owned arena with ranges into an independently retained source is an alternative. The AST value itself passed a `Send + Sync` compile-time assertion, but the full `ParseResult` contains an optional `Rc` comment map and should not be assumed thread-safe merely because comment collection is disabled at runtime.

For malformed input `{"é": [1,`, the error range covered the unfinished array, while `json-syntax` supplied a zero-width EOF location. Either can feed KHDL diagnostics; preserving an opening-delimiter label plus a primary EOF label may require extra adapter bookkeeping.

## json-syntax 0.13.1 and 0.12.5

### Spans, numbers, and duplicates

Both releases return an owned value and a separate code map. Fragments include complete entries, keys, values, and containers. Code-map entries explicitly record byte spans and subtree volumes. Traversal must keep value fragments aligned with map offsets; changing the value tree without updating its code map would invalidate that correspondence. Both releases produced the expected UTF-8/key/escaped-string ranges in the probe. [0.13.1 code_map.rs](https://docs.rs/crate/json-syntax/0.13.1/source/src/code_map.rs), [0.12.5 code_map.rs](https://docs.rs/crate/json-syntax/0.12.5/source/src/code_map.rs).

Numbers remain lexical, and duplicate properties remain available rather than being collapsed. KHDL can reject decimal/exponent spelling and convert integer text directly to `BigInt`. The versions differ significantly in public API naming and implementation dependencies: 0.13.1 uses names such as `JsonValue` and `JsonCodeMap`, while 0.12.5 uses `Value` and `CodeMap`. [0.13.1 number.rs](https://docs.rs/crate/json-syntax/0.13.1/source/src/number.rs), [0.13.1 object.rs](https://docs.rs/crate/json-syntax/0.13.1/source/src/object.rs), [0.12.5 lib.rs](https://docs.rs/crate/json-syntax/0.12.5/source/src/lib.rs).

The default parser options are strict for invalid Unicode code points and truncated surrogate pairs. Error APIs expose positions and Unicode-error spans. An ordinary unexpected-character error uses a zero-width position; KHDL can expand it to the offending UTF-8 character where appropriate. Both releases rejected trailing root values in probes. [0.13.1 parse/mod.rs](https://docs.rs/crate/json-syntax/0.13.1/source/src/parse/mod.rs), [0.12.5 parse/mod.rs](https://docs.rs/crate/json-syntax/0.12.5/source/src/parse/mod.rs).

### Resource behavior requires a boundary

The main value parser uses an explicit stack rather than recursing per nesting level. However, it does not expose a general KHDL budget or a maximum depth option in the inspected parser options. Its owned tree can still cause trouble after parsing.

Measured in separate native subprocesses for **both** releases:

- 600 nested arrays: parsed and dropped successfully.
- 10,000 nested arrays: parsed and dropped successfully.
- 100,000 nested arrays: parsing returned successfully, then dropping the result aborted the process with a stack overflow.

Thus a nonrecursive parser does not make the complete value lifecycle safe for arbitrarily deep hostile input. Enforce a depth limit before constructing an excessive tree, or change ownership/destruction to an iterative/arena representation. Rejecting only after parsing is unsafe if rejection itself drops that tree recursively. Error-path cleanup, clones, mapping, and diagnostic traversal need the same consideration. [0.13.1 parse/value.rs](https://docs.rs/crate/json-syntax/0.13.1/source/src/parse/value.rs), [0.12.5 parse/value.rs](https://docs.rs/crate/json-syntax/0.12.5/source/src/parse/value.rs).

The character-stream entry points accept an iterator of fallible decoded characters. In principle an adapter could check cancellation, character budgets, and string-aware delimiter depth before feeding more input. This is an implementation inference, not a tested adapter. Node/allocation budgets may require further hooks or a preflight. Neither byte limits alone nor cancellation alone replaces a depth limit.

### Version and dependency implications

0.13.1's declared Rust 1.96 requirement exceeds KHDL's declared 1.95. Using it means an explicit minimum-toolchain change, a vetted backport, or waiting; a successful build on this machine's 1.99.1 does not resolve that decision. 0.12.5 declares Rust 1.71, but pinning an older line has maintenance implications and its complete resolved dependency graph still needs minimum-toolchain/WASM verification.

Both are larger dependencies than the default `jsonc-parser` AST configuration. Optional serialization/printing functionality is not a reason to enable extra features. 0.13.1 defaults to its `serde` feature; the probes disabled default features. The older and newer object/index implementations differ, so performance and hostile-key behavior should be reviewed for the selected release rather than assumed identical. [0.13.1 Cargo.toml](https://docs.rs/crate/json-syntax/0.13.1/source/Cargo.toml), [0.12.5 Cargo.toml](https://docs.rs/crate/json-syntax/0.12.5/source/Cargo.toml).

## json-spanned-value 0.2.2

This package wraps `serde_json::from_reader` with a byte-at-a-time reader and thread-local bookkeeping to infer token boundaries. It has owned spanned values and keys, and rejects duplicate decoded keys by default. Disabling duplicate rejection overwrites entries, so neither mode retains both occurrences for a later KHDL diagnostic. The existing duplicate error does not expose the two key ranges as a structured pair. [reader.rs](https://docs.rs/crate/json-spanned-value/0.2.2/source/src/reader.rs), [shared.rs](https://docs.rs/crate/json-spanned-value/0.2.2/source/src/shared.rs), [map.rs](https://docs.rs/crate/json-spanned-value/0.2.2/source/src/map.rs).

Concrete probe failures:

| Input/configuration | Observed result | Required behavior |
| --- | --- | --- |
| `1` at EOF | Span `0..0` | Span `0..1` |
| `-12` at EOF | Span `0..2`, slicing `-1` | Span `0..3` |
| `1 ` with trailing space | Span `0..1` | Span `0..1` |
| 40-digit integer, normal Serde features | Rounded numeric value `1.2345678901234567e+39` | Exact integer text/value |
| Same integer with `serde_json/arbitrary_precision` | An object containing Serde's private number marker | A number |

The EOF behavior follows the unconditional one-byte adjustment for number endings in `Spanned::deserialize`. The package's generic value visitor handles ordinary floating-point visits but does not recognize Serde's arbitrary-precision number protocol, so enabling that feature alone is not a fix. [spanned.rs](https://docs.rs/crate/json-spanned-value/0.2.2/source/src/spanned.rs), [value.rs](https://docs.rs/crate/json-spanned-value/0.2.2/source/src/value.rs).

These are repairable, but repairing span inference, numeric representation, duplicate retention, and structured errors would change several central pieces. It is less attractive than starting with an AST already retaining explicit ranges and lexemes. Thread-local state is not by itself a thread race—the package restores state for nested calls—but it is additional complexity to audit. No throughput benchmark was performed.

## Existing serde_json and adapting an established parser

Ordinary `serde_json::Value` does not retain key/value byte ranges or duplicate entries. Without `arbitrary_precision`, large integer conversion can round through floating point. Its public error API provides line/column positions rather than the required full nested ranges. `StreamDeserializer::byte_offset` tracks progress through top-level stream values; it is not a nested-span API. [Value source](https://docs.rs/serde_json/1.0.149/src/serde_json/value/de.rs.html), [stream API](https://docs.rs/serde_json/1.0.149/serde_json/struct.StreamDeserializer.html), [error API](https://docs.rs/serde_json/1.0.149/serde_json/struct.Error.html).

`RawValue` borrows a complete original JSON value, and can be useful for deferring parsing or strict lexical validation. Probes confirmed it accepts a huge integer and `1e9999` without numeric conversion and rejects a raw newline in a string. However, it also accepts a lone surrogate escape as raw text; a later decoded-string pass must enforce KHDL's Unicode policy. It does not provide descendant/key ranges automatically. Recursively reparsing nested raw slices would need care to avoid quadratic work. [RawValue API](https://docs.rs/serde_json/1.0.149/serde_json/value/struct.RawValue.html), [deserializer implementation](https://docs.rs/serde_json/1.0.149/src/serde_json/de.rs.html).

A fork could expose token positions or build a dedicated span-preserving tree while reusing lexical validation. That is feasible under the offered MIT/Apache license, but the extent of the fork and future upstream merge cost need a concrete design. Using a custom Serde visitor alone does not expose the missing parser cursor boundaries. This path is still available, but there is no demonstrated small patch in this research.

## New parser using KHDL's strategy

KHDL currently has a hand-written UTF-8 tokenizer with byte positions and token-specific errors, feeding a generated LALRPOP parser. `ParseContext` builds `FileId`-qualified spans. Parser errors distinguish invalid tokens, unexpected EOF/tokens, extra tokens, and lexer errors; diagnostics use the same renderer as other compiler errors. See [token.rs](rust/khdl_language/src/syntax/token.rs), [parser.rs](rust/khdl_language/src/syntax/parser.rs), [grammar.lalrpop](rust/khdl_language/src/syntax/grammar.lalrpop), [pos.rs](rust/khdl_language/src/syntax/pos.rs), and [build.rs](rust/khdl_language/build.rs).

Code/infrastructure that could be reused or factored:

- `FileId`, `Pos`, `Span`, `Spanned`, source storage, line offsets, and diagnostic rendering.
- Lexer cursor operations tracking `char::len_utf8()` and source slices, where factoring is actually useful.
- The parser-generator dependency/build approach and common expected-token formatting/error presentation. The present `ParseError` alias and conversion are tied to KHDL token types; sharing them requires a generic helper or parallel JSON-specific adapter.
- Existing arena utilities for a flat JSON representation, with child indices rather than recursively owned children.

Pieces that still need JSON-specific work:

- A strict tokenizer: no comments/interpolation, only JSON whitespace, JSON number grammar, forbidden raw controls, JSON escapes, and UTF-16 surrogate-pair decoding for `\u` escapes.
- A JSON grammar preserving object entry order, duplicates, and token/container ranges, with a complete-input start rule.
- Resource checks, cancellation points, and an arena/ownership design with bounded destruction behavior.
- Error messages/recovery appropriate to malformed configuration files. Sharing LALRPOP does not automatically produce ideal JSON messages; expected-token lists and opening-delimiter context still need design.
- A test corpus, differential tests, fuzzing, and coverage of resource/error paths.

A generated parser can avoid recursive-descent nesting, but semantic actions, error cleanup, the resulting AST, and schema conversion must also avoid unbounded recursion. The current large build-thread stack in `build.rs` applies to parser generation at build time; it is not a runtime guarantee for untrusted JSON.

This approach offers the most direct control and no new third-party parser dependency, but KHDL would own correctness and maintenance of a new JSON implementation. Sharing code should be justified by real common behavior; do not broaden the KHDL lexer to accept both languages through a collection of loosely coupled flags. No prototype was implemented, so effort and performance comparisons are qualitative.

## Measured behavior

### Corpus results

Ran the `test_parsing` directory of [JSONTestSuite](https://github.com/nst/JSONTestSuite/tree/1ef36fa01286573e846ac449e8683f8833c5b26a), commit `1ef36fa01286573e846ac449e8683f8833c5b26a`: 95 `y_` required-accept files, 188 `n_` required-reject files, and 35 `i_` implementation-dependent files. Non-UTF-8 files were rejected before calling the string-based parsers; results therefore describe the intended UTF-8 host adapter plus parser, not each library's byte API. This corpus is useful regression evidence, not proof of complete correctness.

| Configuration | Required-accept rejected | Required-reject accepted |
| --- | --- | --- |
| jsonc-parser 0.33.2, all seven flags false, require a root value | 0 / 95 | 4 / 188 |
| json-syntax 0.13.1, defaults disabled, strict parser defaults | 0 / 95 | 0 / 188 |
| json-syntax 0.12.5, defaults disabled, strict parser defaults | 0 / 95 | 0 / 188 |
| json-spanned-value 0.2.2, default settings | 2 / 95 | 0 / 188 |
| serde_json 1.0.149 Value, without arbitrary_precision | 0 / 95 | 0 / 188 |

The four jsonc-parser cases were `n_string_unescaped_ctrl_char.json`, `n_string_unescaped_newline.json`, `n_string_unescaped_tab.json`, and `n_structure_whitespace_formfeed.json`. The two spanned-value rejections were duplicate-key objects; those match KHDL's stricter duplicate policy, so the count alone is not a KHDL defect. The package's representation and span failures are the relevant defects. Implementation-dependent cases were exercised but are not scored as failures.

### Targeted checks

- All candidates rejected comments, trailing commas, missing commas, leading-zero arrays, hexadecimal/unary-plus literals, multiple root values, and lone surrogate escapes through their normal decoded-value APIs in the tested configurations.
- All decoded the valid escaped surrogate pair `"\uD83D\uDE00"` successfully.
- jsonc-parser and both json-syntax versions accepted arbitrary-size integer lexemes and `1e9999` at syntax level; KHDL must subsequently reject fractional/exponent notation under the current mapping policy.
- Key/value spans were checked on a document containing `"é"`, a nested array, an escaped supplementary character, null, and `-12`. jsonc-parser and both json-syntax maps identified key `"é"` at bytes `3..7`, the escaped string at `13..27`, and integer `-12` at `41..44`, preserving original spelling.
- The input `{"a":1,"\u0061":2}` remained two object entries in jsonc-parser/json-syntax, with both keys decoded to `a`; spanned-value rejected it as a duplicate.
- Compile-time assertions confirmed `Send + Sync` for jsonc-parser's AST value, both json-syntax values, the newer code map, and spanned-value's value. This does not solve borrowed-source ownership or make the entire jsonc-parser `ParseResult` thread-safe.
- Depth behavior was tested in native subprocesses with core dumps disabled. The 100,000-depth drop aborts are recorded above; thresholds are environment-dependent and must not be treated as safe portable limits.

## Implications for the plan

Keep the selected logical-name load API, lazy host queries, schema restrictions, and option mapping unchanged. Parser findings do not require handles or different path rules.

Before implementation, refine the plan in these ways:

1. Make pre-construction depth protection and safe cleanup explicit acceptance criteria, alongside byte/node/token budgets and cancellation.
2. Choose whether the retained parse result is a library-owned tree/map or a KHDL-owned flat arena. Keep duplicate entries and raw lexemes until diagnostic/schema processing. This choice affects query caching and destruction safety.
3. Define the adapter contract: strict UTF-8 input, nonempty single root, original-source ranges, decoded strings, exact numeric text, duplicate preservation, and structured syntax errors. Keep schema mapping separate from syntax parsing.
4. If choosing jsonc-parser, resolve its strictness gaps for the exact pinned version and establish an ownership/budget strategy. Do not rely only on disabling extension flags.
5. If choosing json-syntax, resolve the Rust-version/dependency decision and prevent excessive tree depth before parsing completes. Do not rely on the nonrecursive-parser claim as an end-to-end safety guarantee.
6. If choosing a new parser, compare a small tokenizer/grammar/arena design against the concrete library-adapter work before expanding shared KHDL parser abstractions.

Further verification should target the proposed adapter on Rust 1.95 (or an explicitly revised minimum), WASM and small-stack environments, depth/node/size/cancellation limits, cleanup on malformed deeply nested input, and fuzzing. Benchmarks should use realistic configuration and coefficient files, measuring retained memory and cancellation latency as well as throughput. These checks remain outstanding; no performance ranking is claimed.

## Reproducibility notes

Temporary artifacts from this session are under `/tmp/khdl-json-parser-research`: `Cargo.toml`, `Cargo.lock`, `probe.rs`, downloaded source archives, `probe-output.txt`, `probe-ap-output.txt`, `corpus-output.txt`, and depth subprocess results. They are research artifacts, not repository tests or a durable dependency on `/tmp`.

The harness calls these APIs for each UTF-8 input:

```rust
jsonc_parser::parse_to_ast(text, &Default::default(), &strict_options)
    .map(|result| result.value.is_some());
json_syntax::JsonValue::parse_str(text);       // JsonParse trait, 0.13.1
json_syntax_old::Value::parse_str(text);       // Parse trait, 0.12.5
json_spanned_value::from_str::<json_spanned_value::spanned::Value>(text);
serde_json::from_str::<serde_json::Value>(text);
```

Use exact package versions, disable defaults for the first three parser dependencies, and set all seven jsonc-parser extension flags false. For the separate precision experiment enable `serde_json/arbitrary_precision`; for raw validation enable `serde_json/raw_value`. Source archive hashes below allow independent verification. The corpus commit is pinned above.

| Archive | SHA-256 |
| --- | --- |
| jsonc-parser-0.33.2.crate | `9ff5a48f48971be8e762a6ff955725a0802b6e46c441057992da5a673db9fd3a` |
| json-syntax-0.13.1.crate | `1a77d52c04b5ef283ff6843702206599110495080b0d26aef81a3f0bbca30b16` |
| json-syntax-0.12.5.crate | `044a68aba3f96d712f492b72be25e10f96201eaaca3207a7d6e68d6d5105fda9` |
| json-spanned-value-0.2.2.crate | `bb343fa4e3b1b22b344937deedac88da995abf139c2232cbeaa436c38380a210` |

Minimal regression inputs worth retaining regardless of parser choice: root integers at EOF (`1`, `-12`), a 40-digit integer, raw controls in strings, non-JSON whitespace, escaped duplicate keys, an escaped surrogate pair, lone surrogates, empty input, multiple roots, and bounded/deep array nesting including destruction and error paths.
