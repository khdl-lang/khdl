from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


# TODO also test these at signal level, with multiple different processes driving different splits
def test_struct_assign_field_const(tmp_dir: Path):
    src = """
    struct Pair { x: uint(8), y: bool }
    fn f() -> Pair {
        var v = Pair.new(x=0, y=false);
        v.x = 8;
        return v;
    }
    """

    c = compile_custom(src)
    pair = c.resolve("top.Pair")
    f = c.resolve("top.f")

    assert f() == pair.new(x=8, y=False)


def test_struct_assign_field_cond(tmp_dir: Path):
    prefix = """
    struct Pair { x: uint(8), y: bool }
    """
    src = """
    var v = Pair.new(x=0, y=false);
    if (a0) {
        v.x = a1;
    }
    if (a2) {
        v.y = a3;
    }
    return (v.x, v.y);
    """
    e = compare_body(["bool", "uint(8)", "bool", "bool"], "Tuple(uint(8), bool)", src, tmp_dir, prefix=prefix)

    bools = [False, True]
    for a0 in bools:
        for a1 in range(2):
            for a2 in bools:
                for a3 in bools:
                    res_x = 0
                    res_y = False
                    if a0:
                        res_x = a1
                    if a2:
                        res_y = a3

                    e.eval_assert([a0, a1, a2, a3], (res_x, res_y))


def test_tuple_assign_index_const(tmp_dir: Path):
    src = """
    fn f() -> Tuple(uint(8), bool) {
        var v = (0, false);
        v.0 = 8;
        return v;
    }
    """

    c = compile_custom(src)
    f = c.resolve("top.f")

    assert f() == (8, False)


def test_tuple_assign_index_cond(tmp_dir: Path):
    # TODO get this working without the type hint too?
    src = """
    var v: Tuple(uint(8), bool) = (0, false);
    if (a0) {
        v.0 = a1;
    }
    if (a2) {
        v.1 = a3;
    }
    return v;
    """
    e = compare_body(["bool", "uint(8)", "bool", "bool"], "Tuple(uint(8), bool)", src, tmp_dir)

    bools = [False, True]
    for a0 in bools:
        for a1 in range(2):
            for a2 in bools:
                for a3 in bools:
                    res_x = 0
                    res_y = False
                    if a0:
                        res_x = a1
                    if a2:
                        res_y = a3

                    e.eval_assert([a0, a1, a2, a3], (res_x, res_y))


STRUCT_FIELD_ASSIGN_PREFIX = """
struct Inner {
    x: uint(8)
}
struct S {
    x: uint(8),
    xs: [2]uint(8),
    tuple: Tuple(uint(8), bool),
    nested: Inner,
    free: any
}
fn new_s() -> S {
    return S.new(x=0, xs=[0, 0], tuple=(0, false), nested=Inner.new(x=0), free=Inner.new(x=0));
}
"""


def test_struct_field_assign_type_checked():
    assigns = [
        "var s = new_s(); s.x = true;",
        "var s = new_s(); s.x += 256;",
        "var s = new_s(); s.xs[0] = true;",
        "var s = new_s(); s.xs[0..2] = [true, true];",
        "var s = new_s(); s.tuple.0 = true;",
        "var s = new_s(); s.nested.x = true;",
        "var s = new_s(); s.free.x = true;",
        "var a = [new_s(), new_s()]; a[1].x = true;",
    ]
    for assign in assigns:
        src = STRUCT_FIELD_ASSIGN_PREFIX + f"fn f() {{ {assign} }}"
        with diag_error("type mismatch", has_info="target type set here"):
            compile_custom(src).resolve("top.f")()


def test_struct_field_assign_valid():
    c = compile_custom(STRUCT_FIELD_ASSIGN_PREFIX + """
    fn f() -> Tuple(uint(8), [2]uint(8), bool, uint(8), uint(8), bool, uint(8)) {
        var s = new_s();
        s.x = 5;
        s.x += 1;
        s.xs[1] = 7;
        s.xs[0..1] = [3];
        s.tuple.1 = true;
        s.nested.x = 9;
        s.free.x = 11;
        var t = new_s();
        t.free = true;
        var a = [new_s(), new_s()];
        a[1].x = 13;
        return (s.x, s.xs, s.tuple.1, s.nested.x, s.free.x, t.free, a[1].x);
    }
    """)
    assert c.resolve("top.f")() == (6, [3, 7], True, 9, 11, True, 13)
