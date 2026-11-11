from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


def test_member_struct_static():
    src = """
    struct Foo {
        x: int,
        
        const C: int = 8;
        fn derp(x: uint) -> uint {
            return x * 2;
        }
    }
    fn f(x: uint) -> int {
       return Foo.C + Foo.derp(x);
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(0) == 8
    assert f(4) == 16


def test_member_enum_static():
    src = """
    enum Foo {
        A,
        B(bool),
        
        const C: int = 8;
        fn derp(x: uint) -> uint {
            return x * 2;
        }
    }
    fn f(x: uint) -> int {
       return Foo.C + Foo.derp(x);
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(0) == 8
    assert f(4) == 16


def test_member_duplicate():
    src = """
    struct Foo {
        x: int,
        
        fn derp(x: uint) -> uint { return x * 2; }
        fn derp(x: uint) -> uint { return x * 3; }
    }
    const a = Foo.derp;
    """
    with diag_error("identifier `derp` declared multiple times"):
        _ = compile_custom(src).resolve("top.a")


def test_member_err_builtin():
    src = """
    struct Foo {
        x: int,
        const size_bits = 4;
    }
    """
    with diag_error("struct member name collides with builtin type member"):
        _ = compile_custom(src).resolve("top.Foo")


def test_member_err_field():
    src = """
    struct Foo {
        x: int,
        const x = 4;
    }
    """
    with diag_error("conflicting definitions of struct member"):
        _ = compile_custom(src).resolve("top.Foo")


def test_member_struct_self():
    src = """
    struct Foo {
        x: int,
        y: int,
        fn total(self) -> int {
            return self.x + self.y;
        }
    }
    fn f(x: int, y: int) -> int {
        return Foo.new(x=x, y=y).total();
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(1, 2) == 3


def test_member_enum_self():
    src = """
    enum Foo {
        A(int),
        B,
        fn total(self) -> int {
            match (self) {
                .A(val x) => { return x; }
                .B => { return 0; }
            }
        }
    }
    fn f(x: int) -> int {
        return Foo.A(x).total();
    }
    fn g() -> int {
        return Foo.B.total();
    }   
    """
    c = compile_custom(src)
    f = c.resolve("top.f")
    g = c.resolve("top.g")
    assert f(5) == 5
    assert g() == 0


def test_self_value_none():
    src = """
    fn f() -> int {
        return self;
    }
    """
    f = compile_custom(src).resolve("top.f")
    with diag_error("self is not bound in this scope"):
        _ = f()


def test_self_value_captured():
    src = """
    struct Foo {
        x: int,
        fn f(self) -> Function {
            fn g() -> int {
                return self.x;
            }
            return g;
        }
    }
    fn g(x: int) -> int {
        val foo = Foo.new(x=x);
        val g = foo.f();
        return g();
    }
    """
    f = compile_custom(src).resolve("top.g")
    assert f(0) == 0
    assert f(5) == 5


def test_member_access_generics():
    src = """
    struct Foo(N: uint) {
        fn f() -> uint {
            return N;
        }
        fn g(self) -> uint {
            return N;
        }
    }
    fn f(x: uint) -> uint {
        return Foo(x).f();
    }
    fn g(x: uint) -> uint {
        return Foo(x).new().g();
    }
    """
    c = compile_custom(src)
    f = c.resolve("top.f")
    g = c.resolve("top.g")
    assert f(5) == 5
    assert g(5) == 5


def test_member_self_hardware(tmp_dir: Path):
    src = """
    struct Foo {
        x: uint(8),
        fn f(self) -> uint(8) {
            return self.x;
        }
    }
    module top ports(
        x: in async uint(8),
        y: out async uint(8),
    ) {
        wire w = Foo.new(x=x);
        comb {
            y = w.f();
        }
    }
    """
    top = compile_custom(src).resolve("top.top")
    inst = top.as_verilated(tmp_dir).instance()

    for v in [0, 1, 2, 3]:
        inst.ports.x = v
        inst.step(1)
        assert inst.ports.y == v


def test_member_struct_self_hardware_bound(tmp_dir: Path):
    prefix = """
    struct Foo {
        x: uint(8),
        fn get(self) -> uint(8) { return self.x; }
    }
    """
    src = """
    val m = Foo.new(x=a0).get;
    return m();
    """
    e = compare_body(["uint(8)"], "uint(8)", src, tmp_dir, prefix=prefix)
    for x in [0, 5, 255]:
        e.eval_assert([x], x)
