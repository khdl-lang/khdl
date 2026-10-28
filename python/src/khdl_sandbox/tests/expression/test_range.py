import khdl
import pytest
from typing import Optional

from khdl_sandbox.common.util import compile_custom, diag_error


def test_range_compile():
    check_range_compile(2, "..", 3, valid=True)
    check_range_compile(2, "..", 2, valid=True)
    check_range_compile(2, "..", 1, valid=False)
    check_range_compile(2, "..", 0, valid=False)

    check_range_compile(2, "..=", 3, valid=True)
    check_range_compile(2, "..=", 2, valid=True)
    check_range_compile(2, "..=", 1, valid=True)
    check_range_compile(2, "..=", 0, valid=False)

    check_range_compile(2, "+..", 0, valid=True)
    check_range_compile(2, "+..", 1, valid=True)


def test_range_hardware():
    check_range_hardware("0..3", "..", "4..6", valid=True)
    check_range_hardware("0..3", "..", "3..6", valid=True)
    check_range_hardware("0..3", "..", "2..6", valid=True)
    check_range_hardware("0..3", "..", "1..6", valid=False)
    check_range_hardware("0..3", "..", "0..6", valid=False)

    check_range_hardware("0..3", "..=", "4..6", valid=True)
    check_range_hardware("0..3", "..=", "3..6", valid=True)
    check_range_hardware("0..3", "..=", "2..6", valid=True)
    check_range_hardware("0..3", "..=", "1..6", valid=True)
    check_range_hardware("0..3", "..=", "0..6", valid=False)


def check_range_compile(a: Optional[int], ty_range: str, b: Optional[int], valid: bool):
    assert ty_range in ["..", "..=", "+.."]

    src = f"""
    fn f() -> any {{
         return {a if a is not None else ""}{ty_range}{b if b is not None else ""};
    }}
    """
    c = compile_custom(src)
    f = c.resolve("top.f")
    if valid:
        f()
    else:
        if ty_range == "..":
            title = "invalid range: open range requires that `start <= end`"
        elif ty_range == "..=":
            title = "invalid range: closed range requires that `start <= end_inc + 1`"
        else:
            assert False

        with diag_error(title):
            f()


def check_range_hardware(ty_a: Optional[str], ty_range: str, ty_b: Optional[str], valid: bool):
    assert ty_range in ["..", "..=", "+.."]

    src = f"""
    module foo ports(a: in async int({ty_a}), b: in async int({ty_b})) {{
        comb {{
            val r = a{ty_range}b;
        }}
    }}
    """
    c = compile_custom(src)

    if valid:
        _ = c.resolve("top.foo")
    else:
        if ty_range == "..":
            title = "invalid range: open range requires that `start <= end`"
        elif ty_range == "..=":
            title = "invalid range: closed range requires that `start <= end_inc + 1`"
        else:
            assert False

        with diag_error(title):
            _ = c.resolve("top.foo")


def test_range_arithmetic():
    # check that int and range arithmetic both result in the same ranges
    ops = ["+", "-", "*", "/", "+/", "%", "**", "<<", ">>", "&", "|", "^"]
    a = khdl.Range(1, 4).union(khdl.Range(8, 12))
    b = khdl.Range(2, 3).union(khdl.Range(5, 6))

    for op in ops:
        src = f"""
        module top(A: Range, B: Range) ports(a: in async int(A), b: in async int(B)) {{
            comb {{
                val v = a {op} b;
                const {{ print(type(v)); }}
            }}
        }}
        fn f(A: Range, B: Range) -> Range {{ return A {op} B; }}
        """

        c = compile_custom(src)
        r = c.resolve("top.f")(a, b)
        with c.capture_prints() as cap:
            c.resolve("top.top")(A=a, B=b)

        print(r, cap.prints)
        expected = ", ".join(f"{s.start}..{s.end}" for s in r.ranges)
        assert cap.prints == [f"int({expected})\n"]


def test_range_multi_python():
    r = khdl.Range(0, 4).union(khdl.Range(8, 12))
    assert [(s.start, s.end) for s in r.ranges] == [(0, 4), (8, 12)]

    assert r.contains(8) and not r.contains(4)
    assert r.contains_range(khdl.Range(9, 11))

    assert khdl.Range(2, 2) == khdl.Range(3, 3)
    assert khdl.Range(2, 2).is_empty()

    assert r.len == 8

    assert r.enclosing == khdl.Range(0, 12)
    assert r.complement == khdl.Range(None, 0).union(khdl.Range(4, 8)).union(khdl.Range(12, None))
    assert r.intersect(khdl.Range(2, 10)) == khdl.Range(2, 4).union(khdl.Range(8, 10))
    assert r.subtract(khdl.Range(2, 10)) == khdl.Range(0, 2).union(khdl.Range(10, 12))

    assert str(r) == "Range(0..4, 8..12)"
    assert repr(r.ranges) == "[Range(0..4), Range(8..12)]"
    assert len({r, khdl.Range(0, 4).union(khdl.Range(8, 12)), khdl.Range(2, 2), khdl.Range(3, 3)}) == 2

    with pytest.raises(ValueError):
        _ = r.start


def test_range_multi_khdl():
    src = """
    fn roundtrip(r: Range) -> Range { return r; }
    fn equal() -> bool { return (2..2) == (3..3); }
    fn string() -> any { return "{(0..4).union(8..)}"; }
    fn len() -> int { return (0..4).union(8..12).len; }
    fn int_type() -> any { return int((0..4).union(8..12), 20..22); }
    
    fn enclosing() -> Range { return (0..4).union(8..12).enclosing; }
    fn complement() -> Range { return (0..4).complement; }
    fn intersect() -> Range { return (0..4).intersect(2..10); }
    fn subtract() -> Range { return (0..12).subtract(4..8); }
    """
    c = compile_custom(src)
    r = khdl.Range(0, 4).union(khdl.Range(8, 12))

    assert c.resolve("top.roundtrip")(r) == r
    assert c.resolve("top.equal")()
    assert c.resolve("top.string")() == "Range(0..4, 8..)"
    assert c.resolve("top.len")() == 8
    assert str(c.resolve("top.int_type")()) == "int(0..4, 8..12, 20..22)"

    assert c.resolve("top.enclosing")() == khdl.Range(0, 12)
    assert c.resolve("top.complement")() == khdl.Range(None, 0).union(khdl.Range(4, None))
    assert c.resolve("top.intersect")() == khdl.Range(2, 4)
    assert c.resolve("top.subtract")() == r


def test_range_methods_hardware():
    src = "module top ports(x: in async int(0..8)) { comb { val r = (x..8).union(0..2); } }"
    c = compile_custom(src)
    with diag_error("range attributes and methods require compile-time ranges"):
        _ = c.resolve("top.top")


def test_range_multi_for():
    src = """
    fn f(r: Range) -> any {
        var result = [];
        for (i in r) { result = [*result, i]; }
        return result;
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(khdl.Range(0, 3).union(khdl.Range(5, 7))) == [0, 1, 2, 5, 6]


def test_range_multi_match_hardware():
    src = """
    module top(R: Range) ports(x: in async int(0..16), y: out async int(0..16)) {
        comb {
            match (x) {
                in R => {
                    const { print(type(x)); }
                    y = x;
                }
                _ => { y = 0; }
            }
        }
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        c.resolve("top.top")(R=khdl.Range(0, 3).union(khdl.Range(5, 7)))
    assert cap.prints == ["int(0..3, 5..7)\n"]


def test_range_multi_slice():
    f = compile_custom("fn f(x: [3]uint(8), r: Range) -> any { return x[r]; }").resolve("top.f")
    assert f([1, 2, 3], khdl.Range(5, 5)) == []
    with diag_error("array slice range must be a single contiguous range"):
        f([1, 2, 3], khdl.Range(0, 1).union(khdl.Range(2, 3)))
