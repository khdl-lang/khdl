"""Interface array references retain their shape, view, and selected endpoints."""
from pathlib import Path

import pytest

from khdl_sandbox.common.util import compile_custom, diag_error


PREFIX = """
interface Link { value: uint(8), view In { value: in } view Out { value: out } }
struct Endpoint { ref channels: [3][2]Link }
struct GenericEndpoint(I: any) { ref channels: I }
struct ExplicitEndpoint { channels: RefInterface([3][2]Link) }
struct Box { value: any }
"""

ROOTS = [
    ("const ep: Endpoint = Endpoint.new(channels=ref(input));", "ep.channels"),
    ("const ep: any = Endpoint.new(channels=ref(input));", "ep.channels"),
    ("const ep: Tuple(any) = (Endpoint.new(channels=ref(input)),);", "ep.0.channels"),
    ("const ep = [false, Endpoint.new(channels=ref(input))];", "ep[1].channels"),
    ("const ep = Box.new(value=Endpoint.new(channels=ref(input)));", "ep.value.channels"),
    ("const ep = GenericEndpoint([3][2]Link).new(channels=ref(input));", "ep.channels"),
    ("const ep: any = ExplicitEndpoint.new(channels=ref(input));", "deref(ep.channels)"),
    ("", "Endpoint.new(channels=ref(input)).channels"),
]


@pytest.mark.parametrize("declaration,path", ROOTS)
@pytest.mark.parametrize("route", ["signals", "instance", "connect", "forward"])
def test_interface_array_field_routing(tmp_dir: Path, declaration, path, route):
    if route == "signals":
        body = f"comb {{ for (i in 0..2) {{ for (j in 0..2) {{ output[i][j].value = {path}[i+1][j].value; }} }} }}"
    elif route == "instance":
        body = f"instance Child ports(input={path}[1..3], output=output);"
    elif route == "connect":
        body = f"connect({path}[1..3] view In, output view Out);"
    else:
        body = f"const forwarded: RefInterface([2][2]Link) = ref({path}[1..3]); instance Child ports(input=deref(forwarded), output=output);"
    c = compile_custom(PREFIX + f"""
        module Child ports(input: interface async [2][2]Link.In, output: interface async [2][2]Link.Out) {{
            comb {{ for (i in 0..2) {{ for (j in 0..2) {{ output[i][j].value = input[i][j].value; }} }} }}
        }}
        module Probe ports(input: interface async [3][2]Link.In, output: interface async [2][2]Link.Out) {{
            {declaration}
            {body}
        }}
    """)
    inst = c.resolve("top.Probe").as_verilated(tmp_dir).instance()
    for offset in [0, 200]:
        for i in range(3):
            for j in range(2):
                inst.ports.input[i][j].value = offset + 10 * i + j
        inst.step(1)
        assert [[port.value for port in row] for row in inst.ports.output] == [
            [offset + 10, offset + 11], [offset + 20, offset + 21],
        ]


def test_interface_array_field_methods_and_returned_references(tmp_dir: Path):
    c = compile_custom(PREFIX + """
        struct Driver {
            ref channels: [2]Link,
            fn drive(self, values: [2]uint(8)) {
                for (i in 0..2) { self.channels[i].value = values[i]; }
            }
        }
        fn forward(ep: Driver) -> RefInterface([2]Link) { return ref(ep.channels); }
        module Probe ports(input: in async [2]uint(8), output: interface async [3][2]Link.Out) {
            const row = Driver.new(channels=ref(output[1]));
            comb {
                row.drive(input);
                for (j in 0..2) {
                    output[0][j].value = 0;
                    deref(forward(row))[j].value ^= 1;
                    output[2][j].value = output[1][j].value;
                }
            }
        }
    """)
    inst = c.resolve("top.Probe").as_verilated(tmp_dir).instance()
    inst.ports.input = [17, 231]
    inst.step(1)
    assert [[port.value for port in row] for row in inst.ports.output] == [[0, 0], [16, 230], [16, 230]]


@pytest.mark.parametrize("actual", ["[2]Link", "[3][1]Link", "[2][3]Link", "[3][2][1]Link", "Link", "[3][2]Other"])
def test_interface_array_field_rejects_wrong_binding_shape_or_identity(actual):
    c = compile_custom(PREFIX + f"""
        interface Other {{ value: uint(8), view In {{ value: in }} }}
        module Probe ports(input: interface async {actual}.In) {{
            const ep = Endpoint.new(channels=ref(input));
        }}
    """)
    with diag_error("type mismatch"):
        c.resolve("top.Probe")


@pytest.mark.parametrize("shape", ["[0]", "[2][0]", "[0][2]"])
def test_interface_array_field_empty_shapes(shape):
    c = compile_custom(f"""
        interface Link {{ value: bool, view In {{ value: in }} view Out {{ value: out }} }}
        struct Endpoint {{ ref channels: {shape}Link }}
        module Child ports(input: interface async {shape}Link.In) {{}}
        module Probe ports(input: interface async {shape}Link.In, output: interface async {shape}Link.Out) {{
            const ep: any = Endpoint.new(channels=ref(input));
            instance Child ports(input=ep.channels);
            connect(ep.channels view In, output view Out);
        }}
    """)
    assert c.resolve("top.Probe").as_verilog().source


@pytest.mark.parametrize("access,diagnostic", [
    ("ep.channels[3][0].value", "array index out of bounds"),
    ("ep.channels[0][2].value", "array index out of bounds"),
    ("ep.channels[0..4][0][0].value", "array slice end out of bounds"),
    ("ep.channels.value", "cannot access signal of interface array"),
    ("ep.channels[0].value", "cannot access signal of interface array"),
    ("ep.channels[index][0].value", "feature not yet implemented: indexing interface arrays with a hardware value"),
    ("ep.channels[index+..1][0][0].value", "feature not yet implemented: slicing interface arrays with a hardware start"),
])
def test_interface_array_field_access_diagnostics(access, diagnostic):
    c = compile_custom(PREFIX + f"""
        module Probe ports(input: interface async [3][2]Link.In, index: in async uint(0..3), output: out async uint(8)) {{
            const ep: any = Endpoint.new(channels=ref(input));
            comb {{ output = {access}; }}
        }}
    """)
    with diag_error(diagnostic):
        c.resolve("top.Probe")


def test_interface_array_field_preserves_input_direction():
    c = compile_custom(PREFIX + """
        module Probe ports(input: interface async [3][2]Link.In) {
            const ep: any = Endpoint.new(channels=ref(input));
            comb { ep.channels[1][0].value = 0; }
        }
    """)
    with diag_error("cannot assign to input port"):
        c.resolve("top.Probe")


@pytest.mark.parametrize("connection,diagnostic", [
    ("instance Child ports(input=ep.channels[1..3]);", "interface array shape mismatch"),
    ("connect(ep.channels[0] view In, output view Out);", "interface array shape mismatch"),
    ("instance Writer ports(output=ep.channels);", "direction mismatch for interface port `value`"),
    ("instance Clocked ports(clk, input=ep.channels);", "invalid domain crossing: async to sync"),
])
def test_interface_array_field_connection_checks(connection, diagnostic):
    c = compile_custom(PREFIX + f"""
        module Child ports(input: interface async [3][2]Link.In) {{}}
        module Writer ports(output: interface async [3][2]Link.Out) {{
            comb {{ for (i in 0..3) {{ for (j in 0..2) {{ output[i][j].value = 0; }} }} }}
        }}
        module Clocked ports(clk: in clock, input: interface sync(clk) [3][2]Link.In) {{}}
        module Probe ports(clk: in clock, input: interface async [3][2]Link.In, output: interface async [3][2]Link.Out) {{
            const ep: any = Endpoint.new(channels=ref(input));
            {connection}
        }}
    """)
    with diag_error(diagnostic):
        c.resolve("top.Probe")


@pytest.mark.parametrize("shape", ["[0x10000000000000000]", "[4294967296][4294967296]"])
def test_interface_array_field_rejects_oversized_shapes(shape):
    c = compile_custom(f"""
        interface Link {{ value: bool }}
        struct Endpoint {{ ref channels: {shape}Link }}
        fn check() {{ Endpoint; }}
    """)
    with diag_error("interface array too large"):
        c.resolve("top.check")()


@pytest.mark.parametrize("op", ["=", "^="])
def test_interface_array_field_binding_timing(tmp_dir: Path, op):
    c = compile_custom(PREFIX + f"""
        module Probe ports(input: in async uint(8), left: interface async [3][2]Link.Out, right: interface async [3][2]Link.Out) {{
            comb {{
                for (i in 0..3) {{ for (j in 0..2) {{
                    left[i][j].value = 7;
                    right[i][j].value = 11;
                }} }}
                var ep: any = Endpoint.new(channels=ref(left));
                var selectors = 0;
                ep.channels[{{ selectors += 1; 1 }}][{{ selectors += 1; 0 }}].value {op} {{
                    assert(selectors == 2);
                    ep = Endpoint.new(channels=ref(right));
                    input
                }};
            }}
        }}
    """)
    inst = c.resolve("top.Probe").as_verilated(tmp_dir).instance()
    inst.ports.input = 3
    inst.step(1)
    expected_left = [[7, 7], [7 if op == "=" else 4, 7], [7, 7]]
    expected_right = [[11, 11], [3 if op == "=" else 11, 11], [11, 11]]
    assert [[p.value for p in row] for row in inst.ports.left] == expected_left
    assert [[p.value for p in row] for row in inst.ports.right] == expected_right
