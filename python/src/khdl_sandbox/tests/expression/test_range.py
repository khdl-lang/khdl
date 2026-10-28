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
    for op in ops:
        src = f"""
        const A = 1..16;
        const B = 2..4;
        module top ports(a: in async int(A), b: in async int(B)) {{
            comb {{
                val v = a {op} b;
                const {{ print(type(v)); }}
            }}
        }}
        fn f() -> Range {{ return A {op} B; }}
        """

        c = compile_custom(src)
        r = c.resolve("top.f")()
        with c.capture_prints() as cap:
            c.resolve("top.top")

        print(r, cap.prints)
        assert cap.prints == [f"int({r.start}..{r.end})\n"]
