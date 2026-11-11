from khdl_sandbox.common.util import compile_custom, diag_error


def test_flow_read_hw_in_hw():
    src = """module foo ports(p: in async bool) { comb { val _ = p; } }"""
    compile_custom(src).resolve("top.foo")


def test_flow_read_hw_in_const():
    src = """module foo ports(p: in async bool) { const { val _ = p + 2; } }"""
    with diag_error("signal evaluation is only allowed in a hardware context"):
        compile_custom(src).resolve("top.foo")


def test_flow_read_hw_in_const_after_branch_assign():
    # the branch knows the signal is hardware, so it must not look further up for a compile value
    src = """
    module foo ports(x: in async uint(8), y: out async uint(8)) {
        comb {
            y = 3;
            if (x == 0) { y = x; const { val _ = y; } }
        }
    }
    """
    with diag_error("signal evaluation is only allowed in a hardware context"):
        compile_custom(src).resolve("top.foo")


def test_flow_assign_signal_in_const():
    src = """module foo ports(y: out async uint(8)) { comb { const { y = 3; } } }"""
    with diag_error("signal assignment is only allowed in a hardware context"):
        compile_custom(src).resolve("top.foo")
