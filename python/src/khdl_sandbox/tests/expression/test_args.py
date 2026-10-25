from pathlib import Path

from khdl_sandbox.common.compare import compare_expression
from khdl_sandbox.common.util import compile_custom, diag_error


def test_args_order():
    src = """
    fn f(a: int, b: int = 2, c: int = 3) -> int { return a * 100 + b * 10 + c; }
    fn ok_0() -> int { return f(1); }
    fn ok_1() -> int { return f(a=1, b=4, c=5); }
    fn ok_2() -> int { return f(1, 4, c=5); }
    fn ok_3() -> int { return f(a=1, 4, 5); }
    fn skip_default() -> int { return f(1, c=4); }
    fn out_of_order_default() -> int { return f(1, c=4, b=5); }
    fn out_of_order_missing() -> int { return f(b=4, a=1); }
    fn duplicate() -> int { return f(1, a=1); }
    fn unknown() -> int { return f(1, d=1); }
    fn missing() -> int { return f(); }
    fn leftover() -> int { return f(1, 2, 3, 4); }
    """
    c = compile_custom(src)

    assert c.resolve("top.ok_0")() == 123
    assert c.resolve("top.ok_1")() == 145
    assert c.resolve("top.ok_2")() == 145
    assert c.resolve("top.ok_3")() == 145

    for name in ["skip_default", "out_of_order_default", "out_of_order_missing", "duplicate", "unknown"]:
        with diag_error(
            "argument name does not match the parameter at this position", has_info="parameter declared here"
        ):
            c.resolve(f"top.{name}")()
    with diag_error("missing argument for parameter `a`", has_info="parameter declared here"):
        c.resolve("top.missing")()
    with diag_error("argument does not match any parameter", has_info="parameters declared here"):
        c.resolve("top.leftover")()


def test_args_order_struct():
    src = """
    struct S { x: int, y: int }
    fn ok() -> S { return S.new(x=1, y=2); }
    fn out_of_order() -> S { return S.new(y=2, x=1); }
    fn positional() -> S { return S.new(1, y=2); }
    fn missing() -> S { return S.new(x=1); }
    fn leftover() -> S { return S.new(x=1, y=2, z=3); }
    """
    c = compile_custom(src)

    c.resolve("top.ok")()
    with diag_error("argument name does not match the parameter at this position", has_info="parameter declared here"):
        c.resolve("top.out_of_order")()
    with diag_error("positional arguments are not allowed for this call target"):
        c.resolve("top.positional")()
    with diag_error("missing argument for parameter `y`"):
        c.resolve("top.missing")()
    with diag_error("argument does not match any parameter"):
        c.resolve("top.leftover")()


def test_args_positional_only():
    src = """
    enum E { A(int) }
    fn enum_ok() -> bool { return E.A(1) == E.A(1); }
    fn enum_named() -> E { return E.A(x=1); }
    fn enum_too_many() -> E { return E.A(1, 2); }
    fn enum_too_few() -> E { return E.A(); }
    fn int_ok() -> bool { val x: int(8) = -128; val y: uint(0..4, 8..16) = 9; return true; }
    fn int_named() -> type { return int(x=8); }
    fn tuple_ok() -> bool { val x: Tuple(int, bool) = (1, true); return x.1; }
    fn tuple_named() -> type { return Tuple(x=int); }
    """
    c = compile_custom(src)

    assert c.resolve("top.enum_ok")()
    assert c.resolve("top.int_ok")()
    assert c.resolve("top.tuple_ok")()

    with diag_error("named arguments are not allowed for this call target"):
        c.resolve("top.enum_named")()
    with diag_error("argument does not match any parameter"):
        c.resolve("top.enum_too_many")()
    with diag_error("missing argument"):
        c.resolve("top.enum_too_few")()
    with diag_error("named arguments are not allowed for this call target"):
        c.resolve("top.int_named")()
    with diag_error("named arguments are not allowed for this call target"):
        c.resolve("top.tuple_named")()


def test_args_expected_type_from_param():
    src = """
    enum Foo(T: type) { None, Some(T) }
    struct Pair(T: type) { x: T, y: T }
    struct S { p: Foo(bool) }
    fn f(x: Foo(bool)) -> bool { return x == Foo(bool).Some(true); }
    fn g(T: type, x: T) -> T { return x; }
    fn call_function() -> bool { return f(Foo.Some(true)); }
    fn call_function_dependent() -> bool { return g(Pair(bool), Pair.new(x=true, y=false)).x; }
    fn call_struct() -> bool { return S.new(p=Foo.Some(true)).p == Foo(bool).Some(true); }
    fn call_enum() -> bool { return Foo(Foo(bool)).Some(Foo.Some(true)) == Foo(Foo(bool)).Some(Foo(bool).Some(true)); }
    """
    c = compile_custom(src)

    assert c.resolve("top.call_function")()
    assert c.resolve("top.call_function_dependent")()
    assert c.resolve("top.call_struct")()
    assert c.resolve("top.call_enum")()


def test_args_default_uses_earlier_param():
    src = """
    fn f(a: int, b: int = a + 1) -> int { return a * 10 + b; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(1) == 12
    assert f(1, 5) == 15


def test_args_default_expected_type_from_param():
    src = """
    enum Foo(T: type) { None, Some(T) }
    fn f(x: Foo(bool) = Foo.Some(true)) -> bool { return x == Foo(bool).Some(true); }
    """
    f = compile_custom(src).resolve("top.f")
    assert f()


def test_args_default_hardware(tmp_dir: Path):
    prefix = "fn f(a: bool, b: bool = !a) -> bool { return b; }"
    e = compare_expression(["bool"], "bool", "f(a0)", tmp_dir, prefix=prefix)
    e.eval_assert([False], True)
    e.eval_assert([True], False)


def test_args_default_type_mismatch():
    src = """
    fn f(x: bool = 1) -> bool { return x; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(True)
    with diag_error("type mismatch"):
        f()
