# KHDL

An experimental new language for hardware design.
See https://khdl-lang.org/ for an overview, or try it without installing anything in the
[web demo](https://khdl-lang.org/demo/).

A short sneak-peak at the language:

```
pub module top ports(
    clk: in clock,
    rst: in async bool,

    sync(clk, async rst) {
        data_to_add: in uint(0..8),
        stream_in: interface axi_stream(uint(0..8)).input,
        stream_out: interface axi_stream(uint(0..16)).output,
        values_transferred: out uint(32),
    }
) {
    comb {
        stream_in.ready = stream_out.ready;
        stream_out.valid = stream_in.valid;
        stream_out.data = stream_in.data + data_to_add;
    }

    clocked(clk, async rst) {
        reg wire values_transferred = 0;
        if (stream_out.valid && stream_out.ready) {
            values_transferred = (values_transferred + 1) % 2**32;
        }
    }
}

interface axi_stream(T: type) {
    ready: bool,
    valid: bool,
    data: T,

    view input { ready: out, valid: in, data: in }
    view output { ready: in, valid: out, data: out }
}
```

## Background

Current Hardware Description Languages (SystemVerilog, VHDL) have some important weaknesses, some examples are listed in
more detail below. Many of those are difficult to fix without major changes and backward compatibility issues. Those
that can can be fixed suffer from the very long implementation cycle in EDA tooling: A new feature needs to be
supported by all the different tools that a project will use during its lifetime. This includes simulation, synthesis,
linting, power estimation, logical equivalence checking, and IDEs. These tools are implemented by different vendors that
don't share compiler frontends, and it takes years of time and many support requests to get more recent language
versions properly supported everywhere.

[//]: # (TODO make some remark about this leading to low productivity for HW dev compared to SW dev?)

This project takes a different approach: we implement a compiler that compiles a newly designed, modern HDL with the
important features we want, and compiles it to a lowest common denominator subset of Verilog. This effectively
decouples language development from tooling development. Improvements to the language, compiler and surrounding
infrastructure can be made without having to wait on all the different EDA vendors to follow. EDA vendors in turn can
focus on improving the core functionality of the tools instead of all doing the duplicate work of keeping up with
language version revisions.

## Language

### Core language

Some of the main ideas behind the language are listed here, where applicable with a comparison to the status-quo in
existing RTL languages, prefixed by _SV_ or _VHDL_.

[//]: # (TODO link to examples for each of these features)

* Strong type system
    * Tracks integer ranges and applies implications from if statements.
    * Support for arrays, struct, enums, tuples.
    * Values are strongly typed, every assignment is typechecked.
    * _SV_: Weak type system, values of any type are assignable to any other type, the bit widths don't even have to
      match. Integer overflow is also not checked without using extra linters.
    * _VHDL_: In some ways the type system is too strong (eg. arrays with the same length and inner type can't always be
      assigned to each other), in some ways it's too weak in that integer ranges are not checked and even types are not
      fully checked at compile-time, only at run- or synthesis time.

* Powerful generics
    * Can be values, types, functions, modules.
    * Can affect the presence or absence of ports.
    * Modules, structs, enums and interfaces can all be generic.
    * _SV_/_VHDL_: both are very slowly marking progress here, but their generics are comparatively very limited.

* Support for interfaces
    * Leads to code generation or lots of duplicate code
    * Makes instantiating and connection modules (one of the most basic and common things to do in RTL) much more
      convenient.
    * _SV_/_VHDL_: the latest versions have a limited form of interfaces, but vendor support is lacking. This means that
      developers have to resort to writing lots of duplicate code, using editor templates or ad-hoc code generation
      tools. This makes instantiating and connecting modules with large interfaces cumbersome.

* Clock and reset domains are tracked by the compiler
    * Every port and signal is marked with its domain, and the compiler checks every assignment and connection to ensure
      that the
      domain crossing is valid.
    * Processes are always clearly marked as `clocked` or `combinatorial`, writing non-synthesizable constructs is not
      possible.
    * _SV_/_VHDL_: neither language checks domains, this is left to a separate linting or domain crossing checking step
      late in the development pipeline, instead of checked on every compilation.

* Registers, wires and temporary variables are all clearly defined as separate items with different keywords, reducing
  the risk of
  confusion.
    * This avoids accidentally creating registers, latches, or writing non-synthesizable constructs.
    * The compiler checks that all assignments are valid, for example registers can be only be set in a single clocked
      block.
    * The compiler also enforces that registers have reset values or that they have been explicitly marked as
      uninitialized.
    * _SV_/_VHDL_: the languages offer little support here. Modern _SV_ uses `logic` for registers, wires and temporary
      variables. _VHDL_ uses `signal` (which is a register or wire depending on the context) and `variable` (which is a
      register or temporary variable depending on the context). The status-quo solution to this is a combination of
      manual code review and linting, both of which have much more latency and overhead than a compiler check.

* Convenient variable declarations
    * Variables can be declared everywhere mixed together with other statements
    * Types can optionally be inferred
    * _SV_/_VHDL_ both have weird limitations on where variables can be declared

* Intuitive assignment semantics
    * There is only a single assignment operator, `=`, which always immediately assigns the value. THe following lines
      in the code always immediately observe the newly assigned value. It is the compiler's responsibility to correctly
      generate code that simulates and synthesizes correctly.
    * Both _SV_ and _VHDL_ have different assignment operators, blocking and non-blocking. The developer constantly has
      to be careful to use the right one, and reason correctly about the delayed assignment effects on non-blocking
      assignments. There seem to be a historic artifact of the early event-driven models of the languages, but there is
      no need to repeat this design mistake in a new language.

* Proper import and file scope system
    * The compiler parses all the source files in the project at once, and then resolves all imports between files as
      needed. This also completely eliminates any name collision issues.
    * There is a full module hierarchy, allowing code to be organized nicely.
    * Developers are free to choose th order of items in a file, the compiler does not simply read files top-down.
        * _SV_ doesn't have a library or import system at all, the user is responsible for compiling all files in the
          right
          order, and names always resolve to the last definition with a matching name.
        * _VHDL_ does a little better, allowing code to organized in libraries. This is still much weaker than a full
          module
          system through, and the user is till responsible for compiling all files in the right order.

### Modern compiler features

The expectations that software developers have for their tooling have risen significantly in the last decates.
Implementing a new compiler for an RTL language gives us the opportunity to implement some of these features
immediately.

* Modern error messages
    * If anything is wrong in the RTL, the compiler emits very clear error messages. EDA tools set the bar ver low here,
      we can do better.
    * ![Example domain crossing error message](docs/error.png)


* The compiler comes with a built-in [LSP](https://microsoft.github.io/language-server-protocol/) server. This allows
  different editors to get IDE-like features. Implementing this as part of the compiler means that there's no need to
  maintain a separate codebase for the LSP server, guaranteeing that the behavior matches that of the actual compiler.

[//]: # (TODO add autoformatter once it's merged)

* Care has been taken to optimize the compiler, for example it is fully multithreaded up to the level of individual
  file-level items and elaborated module. This means that even large projects should compile quickly.

### Interoperability

The goal of this project is not to immediately replace all existing RTL source code, interoperability with existing code
and workflows is very important.

#### Output Verilog

The output of the compiler is Verilog source code, which can be fed into any existing EDA tool and build flow.
We target Verilog 2005, using only a simple subset of language features. If we find that certain constructs are not well
supported by any EDA tool, we can change the Verilog code generation to fix it.

#### External modules

It's possible to declare _external modules_, which are modules with generics and ports but no body.
The compiler then assumes that given module already exists and is implemented in an external language.
These modules can be instantiated exactly like ordinary modules.
This makes it possible to use existing RTL source code and IP modules.

#### Python bindings

Users will always be able to come up with uses cases that the commandline compiler wrapper does not support.
To allow some more flexibility, the compiler can be imported as a library from Python, giving access to the compiler
library. This allows providing a set of source files to the compiler, and then elaborating certain modules or even
calling certain items from within python. Values are automatically converted to and from their Python equivalents.
This convenient bridge is very convenient during during verification and build flow development.

## Getting started

The quickest way to try the language is the [web demo](https://khdl-lang.org/demo/), which runs the compiler in the
browser. There are no prebuilt compiler binaries yet, building from source needs a Rust toolchain (1.95 or newer).

### Command line compiler

```bash
git clone https://github.com/khdl-lang/khdl.git
cd khdl/rust
cargo build --release -p khdl_bin
```

This builds the compiler as `rust/target/release/khdl_bin`, the commands below assume it's on your `PATH`.

A project is a directory with a `khdl.toml` manifest, which maps source directories to namespaces. With this
manifest, a file `src/blink.kh` defines the items `blink.<name>`:

```toml
[source]
_ = "src"
```

From the project directory, check all items, or elaborate a top module and write it out as Verilog:

```bash
khdl_bin build
khdl_bin build --top blink.Blink --output-verilog build/blink.v
```

The top module must be public and have no generic parameters. `khdl_bin fmt` formats all source files of the project.

### Python bindings

The Python bindings can elaborate modules, call compile-time functions, export Verilog and simulate designs through
[Verilator](https://www.veripool.org/verilator/). Install them from the repository root with:

```bash
pip install ./rust/khdl_python
```

```python
import khdl

source = khdl.Source.new_from_manifest_path("khdl.toml")
compiled = source.compile()
module = compiled.resolve_module("blink.Blink")
print(module.as_verilog().source)
```

`module.as_verilated(build_dir).instance()` builds a simulator, this requires Verilator and a C++ compiler. The tests in
`python/src/khdl_sandbox/tests` show more uses of the API.

### VS Code extension

The compiler includes a language server, used by the VS Code extension in `lsp_client`:

```bash
(cd rust && cargo build --release -p khdl_lsp_server)
cd lsp_client
npm ci
npx vsce package
code --install-extension khdl-lsp-client-0.0.1.vsix
```

Then set the `khdl.server.path` setting to the absolute path of `rust/target/release/khdl_lsp_server`.

## Repository structure

* Most of the compiler and surrounding infrastructure is is written in Rust. The workspace is at `rust/` and contains
  multiple crates:
    * The core `khdl_language` library crate contains the compiler implementation. The major sub-modules are:
        * `syntax`: Implements tokenization, parsing, formatting, resolving.
        * `front`: Contains the bulk of the implementation of the language:
          module elaboration, statement and expression evaluation, type checking, domain checking, ....
        * `mid`: the intermediate representation of elaborated and typechecked modules
        * `back`: different backends that consume the intermediate representation and generate the final useful output
            * _Verilog_: writes out synthesizable verilog source code
            * _Verilator_: wrapper around classes generated by [Verilator](https://www.veripool.org/verilator/)
            * _C++_: generates C++ that can be used to directly simulate the design, without having to use any EDA
              simulator.
    * The other crates use this core library and expose it in more convenient ways:
        * khdl_bin: commandline compiler and formatter
        * khdl_lsp_server: [LSP](https://microsoft.github.io/language-server-protocol/) server implementation
        * khdl_python: python module that uses PyO3 to provide python bindings to the compiler
        * hwm_wasm: wasm module that uses wasm_bindgen to provide web bindings
    * There's also the `khdl_util` crate that contains some common utilities.
* There's a VS Code plugin to act as the LSP client at `lsp_client/`, written in Typescript.
* The frontend of the webdemo is a NodeJS node project also using Typescript, located in `web_demo/`.

## Related projects

There are some projects that use general-purpose programming language as a host, and then allow developers to build the
hardware within that language. This has the major benefit of immediately making the features and ecosystem from the host
language available for parametrization and code reuse. One major downside is that this heavily constraints the syntax
and semantics to those of the host language.

* [MyHDL](https://www.myhdl.org/): Uses Python as a host syntax, but compiles the AST into hardware from scratch.
* [Chisel](https://www.chisel-lang.org/): Uses Scala as a host language to build hardware graphs.
* [migen](https://github.com/m-labs/migen): Uses python as a host language to build hardware graphs.
* [ROHD](https://intel.github.io/rohd-website/): Uses Dart as a host language to build hardware graphs.
* [Hardcaml](https://github.com/janestreet/hardcaml): Uses OCaml as a host language to build hardware graphs.

Other projects are building a standalone RTL language, more similar to the approach taken by this project:

* [Veryl](https://veryl-lang.org/)
* [PipelineC](https://github.com/JulianKemmerer/PipelineC)
* [Spade](https://spade-lang.org/)
* [Filament](https://filamenthdl.com/)

There is also ongoing work on the supporting infrastructure necessary to make future EDA tooling and RTL language
development easier:

* [CIRCT](https://circt.llvm.org/) which uses MLIR to define a common intermediate representation for
  hardware. This is similar (but much more feature complete) to the IR defined in this project, at some point it might
  make sense to switch to CIRCT for better interoperability with other tools.
