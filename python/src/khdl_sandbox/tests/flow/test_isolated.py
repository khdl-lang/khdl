from khdl_sandbox.common.util import compile_custom, diag_error

INTF_BUS = """
interface Bus { value: uint(4), view In { value: in } view Out { value: out } }
module child ports(x: interface async Bus.In) {}
"""


def test_isolated_assign_module_const():
    src = INTF_BUS + """
    module top ports(x: interface async Bus.In) {
        const k = 3;
        instance child ports(x={ k = 4; x });
    }
    """
    with diag_error("cannot assign to immutable variable"):
        compile_custom(src).resolve("top.top")


def test_isolated_signal_eval():
    src = INTF_BUS + """
    module top ports(p: in async uint(4), x: interface async Bus.In) {
        instance child ports(x={ val _ = p; x });
    }
    """
    with diag_error("signal evaluation is only allowed in a hardware context"):
        compile_custom(src).resolve("top.top")


def test_isolated_type_of_signal():
    src = INTF_BUS + """
    module top ports(p: in async uint(4), x: interface async Bus.In) {
        const k = 3;
        instance child ports(x=deref({ const { print(type(p)); print(k); } ref(x) }));
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == ["int(0..16)\n", "3\n"]
