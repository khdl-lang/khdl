from khdl_sandbox.common.util import compile_custom, diag_error


def test_func_capture_const():
    src = """
    const c = 5;
    fn f() -> any {
        fn g() -> int { 
            return c;
        }
        return g;
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f()() == 5


def test_func_capture_param():
    src = """
    fn f(x: int) -> any {
        fn g() -> int {
            return x;
        }
        return g;
    }
    """
    f = compile_custom(src).resolve("top.f")
    for x in [4, 8]:
        assert f(x)() == x


def test_func_capture_iter_var():
    src = """
    fn f(n: uint) -> any {
        var r = [];
        for (i in 0..n) {
            fn g() -> int {
                return i;
            }
            r = [*r, g];
        }
        return r;
    }
    """
    f = compile_custom(src).resolve("top.f")

    n = 4
    r = f(n)
    for i in range(n):
        assert r[i]() == i


def test_func_param_default_only_evaluated_if_used():
    src = """
    fn d() -> int {
        print("default");
        return 0;
    }
    fn f(x: int = d()) -> int { return x; }
    fn g(x: int = undeclared) -> int { return x; }
    """
    c = compile_custom(src)
    f = c.resolve("top.f")
    g = c.resolve("top.g")

    with c.capture_prints() as capture:
        assert f(1) == 1
        assert f(x=1) == 1
    assert capture.prints == []

    with c.capture_prints() as capture:
        assert f() == 0
    assert capture.prints == ["default\n"]

    assert g(1) == 1
    with diag_error("undeclared identifier `undeclared`"):
        g()


def test_func_capture_not_yet_assigned():
    src = "fn f() -> int { val a; fn g() -> int { return a; } return g(); }"
    f = compile_custom(src).resolve("top.f")
    with diag_error("cannot access captured value because it was not fully initialized"):
        f()


def test_func_return_wrong_type():
    src = "fn f() -> bool { return 3; }"
    f = compile_custom(src).resolve("top.f")
    with diag_error("type mismatch"):
        f()
