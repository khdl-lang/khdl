# khdl

Python bindings for [KHDL](https://github.com/khdl-lang/khdl), an experimental new language for hardware design.
A webdemo of the language is available at https://khdl-lang.org/.

The bindings expose the compiler to Python, which allows parsing and compiling KHDL projects, calling functions,
instantiating modules, generating Verilog and simulating modules through [Verilator](https://www.veripool.org/verilator/).

```python
import khdl

source = khdl.Source.new_from_manifest_path("path/to/khdl.toml")
compiled = source.parse().compile()

top = compiled.resolve_module("top.top")
print(top.as_verilog().source)
```

Simulation through Verilator requires `verilator`, `make` and a C++ compiler to be available on the `PATH`.

See the [main repository](https://github.com/khdl-lang/khdl) for more information about the language itself.
