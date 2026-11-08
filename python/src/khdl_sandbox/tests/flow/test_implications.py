import pytest

from khdl_sandbox.common.util import compile_custom, diag_error


def test_signal_does_not_fit():
    src = """
    module top ports(p: in async uint(0..8)) {
        comb {
            var v: uint(0..4) = p;
        }
    }
    """
    c = compile_custom(src)

    with diag_error("type mismatch"):
        _ = c.resolve("top.top")


def test_signal_checked():
    src = """
    module top ports(p: in async uint(0..8)) {
        comb {
            if (p < 4) {
                var v: uint(0..4) = p;
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_signal_reassigned():
    src = """
    module top ports(p: in async uint(0..8), q: in async uint(0..8)) {
        wire w;
        comb {
            w = p;
            if (w < 4) {
                w = q;
                var v: uint(0..4) = w;
            }
        }
    }
    """
    c = compile_custom(src)
    with diag_error("type mismatch"):
        _ = c.resolve("top.top")


def test_variable_does_not_fit():
    src = """
    module top ports(p: in async uint(0..8)) {
        comb {
            var s = p;
            var v: uint(0..4) = s;
        }
    }
    """
    c = compile_custom(src)

    with diag_error("type mismatch"):
        _ = c.resolve("top.top")


def test_variable_checked():
    src = """
    module top ports(p: in async uint(0..8)) {
        comb {
            var s = p;
            if (s < 4) {
                var v: uint(0..4) = s;
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_variable_reassigned():
    src = """
    module top ports(p: in async uint(0..8), q: in async uint(0..8)) {
        comb {
            var s = p;
            if (s < 4) {
                s = q;
                var v: uint(0..4) = s;
            }
        }
    }
    """
    c = compile_custom(src)
    with diag_error("type mismatch"):
        _ = c.resolve("top.top")


def test_implied_type_int_const():
    ty = "0..8"

    check_unary_cond(ty, "p < 4", "0..4", "4..8")
    check_unary_cond(ty, "4 > p", "0..4", "4..8")

    check_unary_cond(ty, "p <= 4", "0..5", "5..8")
    check_unary_cond(ty, "4 >= p", "0..5", "5..8")

    check_unary_cond(ty, "p > 4", "5..8", "0..5")
    check_unary_cond(ty, "4 < p", "5..8", "0..5")

    check_unary_cond(ty, "p >= 4", "4..8", "0..4")
    check_unary_cond(ty, "4 <= p", "4..8", "0..4")

    check_unary_cond(ty, "p == 4", "4..5", "0..4, 5..8")
    check_unary_cond(ty, "4 == p", "4..5", "0..4, 5..8")

    check_unary_cond(ty, "p != 4", "0..4, 5..8", "4..5")
    check_unary_cond(ty, "4 != p", "0..4, 5..8", "4..5")


def test_implied_type_int_int():
    ty_a = "0..8"
    ty_b = "2..6"

    check_binary_cond(ty_a, ty_b, "a < b", "0..5", "2..8")
    check_binary_cond(ty_a, ty_b, "b > a", "0..5", "2..8")

    check_binary_cond(ty_a, ty_b, "a <= b", "0..6", "3..8")
    check_binary_cond(ty_a, ty_b, "b >= a", "0..6", "3..8")

    check_binary_cond(ty_a, ty_b, "a > b", "3..8", "0..6")
    check_binary_cond(ty_a, ty_b, "b < a", "3..8", "0..6")

    check_binary_cond(ty_a, ty_b, "a >= b", "2..8", "0..5")
    check_binary_cond(ty_a, ty_b, "b <= a", "2..8", "0..5")


def test_implied_type_operators():
    # TODO make these stricter once we have better range analysis for composite conditions
    check_unary_cond("0..8", "2 <= p && p < 6", "2..6", "0..8")
    check_unary_cond("0..8", "p < 2 || 6 <= p", "0..8", "2..6")
    check_unary_cond("0..8", "2 <= p ^^ p < 6", "0..8", "0..8")
    check_unary_cond("0..8", "!(2 <= p)", "0..2", "2..8")


def check_unary_cond(ty: str, cond: str, ty_true: str, ty_false: str):
    src = f"""
    module top ports(p: in async int({ty})) {{
        comb {{
            const {{ print(type(p)); }}
            if ({cond}) {{
                val v = p;
                const {{ print(type(v)); }}            
            }} else {{
                val v = p;
                const {{ print(type(v)); }}
            }}
        }}
    }}
    """

    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == [f"int({ty})\n", f"int({ty_true})\n", f"int({ty_false})\n"]


def check_binary_cond(ty_a: str, ty_b: str, cond: str, ty_true_a: str, ty_false_a: str):
    src = f"""
    module top ports(a: in async int({ty_a}), b: in async int({ty_b})) {{
        comb {{
            const {{ print(type(a)); print(type(b)); }}
            if ({cond}) {{
                val va = a;
                val vb = b;
                const {{ print(type(va)); print(type(vb)); }}
            }} else {{
                val va = a;
                val vb = b;
                const {{ print(type(va)); print(type(vb)); }}
            }}
        }}
    }}
    """

    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == [
        f"int({ty_a})\n", f"int({ty_b})\n",
        f"int({ty_true_a})\n", f"int({ty_b})\n",
        f"int({ty_false_a})\n", f"int({ty_b})\n"
    ]


@pytest.mark.parametrize("var", [False, True])
def test_bool_implies_itself(var: bool):
    t = "v" if var else "p"

    src = f"""
    module top ports(p: in async bool) {{
        comb {{
            val v = p;
            if ({t}) {{
                const {{ print("true"); }}
                if ({t}) {{
                    const {{ print("true.true"); }}
                }} else {{
                    const {{ print("true.false"); }}
                }}
            }} else {{
                const {{ print("false"); }}
                if ({t}) {{
                    const {{ print("false.true"); }}
                }} else {{
                    const {{ print("false.false"); }}
                }}
            }}
        }}
    }}
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == [
        "true\n",
        "true.true\n",
        "false\n",
        "false.false\n",
    ]


def test_imply_non_zero_div():
    src_raw = """
    module top ports(x: in async int(-4..=4), y: out async int(-4..=4)) {
        comb {
            y = 4 / x;
        }
    }
    """
    with diag_error("division by zero is not allowed"):
        _ = compile_custom(src_raw).resolve("top.top")

    src_checked = """
    module top ports(x: in async int(-4..=4), y: out async int(-4..=4)) {
        comb {
            if (x != 0) {
                y = 4 / x;
            } else {
                y = 0;
            }
        }
    }
    """
    _ = compile_custom(src_checked).resolve("top.top")


def test_imply_nested():
    src = """
    module top ports(p: in async uint(0..8)) {
        comb {
            if (p < 6) {
                if (p >= 2) {
                    var v: uint(2..6) = p;   
                }
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_signal_bool_const():
    src = """
    module top ports(p: in async bool, q: out async bool) {
        comb {
            q = p;
            if (q) {
                q = false;
            }
            const { assert(!q); } 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_var_bool_const():
    src = """
    module top ports(p: in async bool) {
        comb {
            var v = p;
            if (v) {
                v = false;
            }
            const { assert(!v); } 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_signal_int_const():
    src = """
    module top ports(c: in async bool, q: out async uint(4)) {
        comb {
            if (c) {
                q = 5;
            } else {
                q = 5;
            }
            const { assert(q == 5); } 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_var_int_const():
    src = """
    module top ports(c: in async bool) {
        comb {
            val v;
            if (c) {
                v = 5;
            } else {
                v = 5;
            }
            const { assert(v == 5); } 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_signal_int_range():
    src = """
    module top ports(p: in async int(5), q: out async uint(4)) {
        wire w: int(5);
        comb {
            w = p;
            if (w < 0) {
                w = 0;
            }
            q = w; 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_var_int_range():
    src = """
    module top ports(p: in async int(5), q: out async uint(4)) {
        comb {
            var v = p;
            if (v < 0) {
                v = 0;
            }
            q = v; 
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_merge_implication_signal_int_range_abs():
    src = """
    module top ports(p: in async int(-4..4)) {
        wire w: int(5);
        comb {
            if (p >= 0) {
                w = p;
            } else {
                w = -p;
            }
            val v = w;
            const { print(type(v)); }
        }
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == ["int(0..5)\n"]


def test_merge_implication_var_int_range_abs():
    src = """
    module top ports(p: in async int(-4..4)) {
        comb {
            val v;
            if (p >= 0) {
                v = p;
            } else {
                v = -p;
            }
            const { print(type(v)); }
        }
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == ["int(0..5)\n"]


def test_imply_assume():
    src = """
    module top ports(p: in async int(-4..4)) {
        comb {
            assert_assume(p >= 0);
            const { print(type(p)); }
        }
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        _ = c.resolve("top.top")
    assert cap.prints == ["int(0..4)\n"]


# TODO test cases where if an if statement in between that does not assign, one that does assign, ...
# TODO test const value merging if both sides assign the same constant
# TODO const value merging if one side assigns and the other implies the same constant

def test_imply_assignment_breaks_connection():
    """Test that assigning a new value to a variable breaks previous implications."""
    src = """
    module top ports(p: in async int(-4..4), q: in async int(-4..4)) {
        comb {
            var v = p;
            if (v < 0) {
                v = 0;
            }
            v = q;
            val _: uint = v;
        }
    }
    """
    c = compile_custom(src)
    with diag_error("type mismatch"):
        _ = c.resolve("top.top")


def test_imply_var_changed_type():
    """Test that assigning a variable a different type does not crash the compiler."""

    def case(new: str):
        src = f"""
        module top ports(p_int: in async int(-4..4), p_bool: in async bool) {{
            comb {{
                var v = p_int;
                val c = v >= 0;
                v = {new};
                if (c) {{
                    const {{ print("true"); }}
                }} else {{
                    const {{ print("false"); }}
                }}
            }}
        }}
        """
        c = compile_custom(src)
        with c.capture_prints() as cap:
            _ = c.resolve("top.top")
        assert cap.prints == ["true\n", "false\n"]

    case("p_bool")
    case("true")
    case("false")


def test_var_remembers_implications():
    src = """
    module top ports(p: in async int(-4..4), q: in async int(-4..4)) {
        comb {
            val c = p >= 0;
            if (c) {
                val _: uint = p;
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_signal_remembers_implications():
    src = """
    module top ports(p: in async int(-4..4), q: in async int(-4..4)) {
        wire c: bool;
        comb {
            c = p >= 0;
            if (c) {
                val _: uint = p;
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_implication_through_alias():
    src = """
    module top ports(x: in async uint(0..8), y: out async uint(0..4)) {
        comb {
            val v = x;
            y = 0;
            if (x < 4) {
                y = v;
            }
            if (v < 4) {
                y = x;
            }
        }
    }
    """
    compile_custom(src).resolve("top.top")
