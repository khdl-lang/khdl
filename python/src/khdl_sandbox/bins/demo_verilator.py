import os
import random
from pathlib import Path

import khdl

# TODO update this and add it to CI
print("Loading, parsing, compiling")
compiled = khdl.Source.new_from_manifest_path(
    str(Path(__file__).parent / "../../../../design/project/khdl.toml")).compile()
print("  parsed files:")
for file in compiled.parsed.source.source_files:
    print(f"    {file}")

print("Resolving")
input_width = 7
output_width = 9

axi_gearbox = compiled.resolve("examples.axi_gearbox.axi_gearbox")
top = axi_gearbox(T=bool, input_width=input_width, output_width=output_width)
print(top)

print("Generating verilog")
print(top.as_verilog())

print("Verilating")
build_dir = "../../../build"
os.makedirs(build_dir, exist_ok=True)
top_verilated = top.as_verilated(build_dir=build_dir)
print(top_verilated)

print("Creating simulator")
sim = top_verilated.instance(trace_path=build_dir + "/trace.vcd")
ports = sim.ports

for port_name in sim.info_ports_flat:
    port = sim.info_ports_flat[port_name]
    print(" ", port.name, port.direction, port.type)

print("Simulating")

input_length = max(8 * input_width, 8 * output_width)
input_length = (input_length + input_width - 1) // input_width * input_width
assert input_length % input_width == 0

random.seed(0xdeadbeef + 1)
input_data = [random.randrange(2) != 0 for _ in range(input_length)]
# input_data = [c != "0" for i in range(input_length // 8) for c in reversed(f"{i+1:08b}")]
# input_data = [i % 2 == 0 for i in range(input_length)]
# input_data = [True] * input_length
output_data = []

# reset
ports.rst = True
ports.clk = False
sim.step(1)
ports.rst = False
ports.clk = True
sim.step(1)
ports.clk = False
sim.step(1)

input_data_left = list(input_data)

for i in range(32):
    print(f"  clock cycle {i}")
    # print(f"  ports: {({p: ports[p] for p in ports})}")

    # [posedge]
    # send input
    # TODO all writes should actually happen after the clock edge, while all reads should happen before
    next_input_valid = ports.input_valid
    next_input_data = ports.input_data
    next_output_ready = ports.output_ready

    if i >= 1:
        if next_input_valid and ports.input_ready:
            print(f"  PY input handshake")
            next_input_valid = False
            next_input_data = [False] * input_width
        if not next_input_valid and len(input_data_left) > 0:
            next_input_valid = True
            next_input_data = input_data_left[:input_width]
            input_data_left = input_data_left[input_width:]

    # read output
    if i >= 5:
        if ports.output_valid and next_output_ready:
            print(f"  PY output handshake")
            output_data.extend(ports.output_data)
        next_output_ready = True

    # set clock
    ports.clk = True
    sim.step(0)

    # actually do writes
    ports.input_valid = next_input_valid
    ports.input_data = next_input_data
    ports.output_ready = next_output_ready
    sim.step(1)

    # [negedge]
    # set clock
    ports.clk = False
    sim.step(1)

sim.save_trace()

print("Input data:  ", "".join(str(int(x)) for x in input_data))
print("Output data: ", "".join(str(int(x)) for x in output_data))

# plt.plot(input_data, label="output")
# plt.plot(output_data, label="output")
# plt.legend()
# plt.show()
