from pathlib import Path

import khdl

# TODO add this to CI
source = khdl.Source.new_from_manifest_path(str(Path(__file__).parent / "../../../../design/project/khdl.toml"))
print("Parsed files:")
for f in source.source_files:
    print(f"  {f}")

parsed = source.parse()
print(parsed)

com = parsed.compile()

top = com.resolve("top.top")
foo_function = com.resolve("top.foo_function")
foo_module = com.resolve("top.foo_module")
print(top, foo_function, foo_module)

# TODO call function
print(foo_function(4, 5))
print(foo_function(4, b=5))

# TODO instantiate module into generated verilog
ty_bool = com.resolve("std.types.bool")
foo_inst = foo_module(T=ty_bool)

foo_verilog = foo_inst.generate_verilog()
print(foo_verilog.source)

# TODO instantiate module into simulator
# foo_sim = foo_inst.to_simulator()
