from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom


def assert_xor_count(c, expected: int):
    """
    The tests in this file all check that the verilog source code does not explode in size
    due to expressions being evaluated multiple times.
    We test this by counting occurrences of the xor operator.
    """
    source = c.eval_mod.as_verilog().source
    assert source.count("^") == expected


def test_compact_iterator(tmp_dir: Path):
    src = """
    var r = a0;
    for (x in a1 ^ a2) {
        r ^= x;
    }
    return r;
    """

    c = compare_body(["bool", "[8]bool", "[8]bool"], "bool", src, tmp_dir)
    c.eval_assert([False, [False, True] * 4, [True, False, False, True] * 2], False)
    assert_xor_count(c, 1 + 8)


def test_compact_match_subject(tmp_dir: Path):
    src = """
    match (a0 ^ a1) {
        0 => { return 1; }
        1 => { return 2; }
        _ => { return 0; }
    }
    """
    c = compare_body(["uint(4)", "uint(4)"], "uint(0..3)", src, tmp_dir)
    c.eval_assert([3, 2], 2)
    assert_xor_count(c, 1)


def test_compact_match_range(tmp_dir: Path):
    src = """
    match (a0 ^ a1) {
        in 2..4 => { return true; }
        _ => { return false; }
    }
    """
    c = compare_body(["uint(4)", "uint(4)"], "bool", src, tmp_dir)
    c.eval_assert([3, 0], True)
    assert_xor_count(c, 1)


def test_compact_array_repeat(tmp_dir: Path):
    src = "return [a0 ^ a1] * 4;"
    c = compare_body(["uint(4)", "uint(4)"], "[4]uint(0..32)", src, tmp_dir)
    c.eval_assert([3, 5], [6] * 4)
    assert_xor_count(c, 1)


def test_compact_array_convert():
    src = """
    module top ports(p: in async [8]bool, q: in async [8]bool, y: out async [2]uint(0..32)) {
        comb {
            val T = [2]uint(4);
            y = T.from_bits(p ^ q);
        }
    }
    """
    source = compile_custom(src).resolve_module("top.top").as_verilog().source
    assert source.count("^") == 1, source


def test_compact_compound_assign_index(tmp_dir: Path):
    src = """
    var r = a0;
    r[a1 ^ a2] ^= true;
    return r;
    """
    c = compare_body(["[4]bool", "uint(2)", "uint(2)"], "[4]bool", src, tmp_dir)
    c.eval_assert([[False] * 4, 1, 3], [False, False, True, False])
    assert_xor_count(c, 1)


def test_compact_method_self(tmp_dir: Path):
    prefix = """
    struct Pair {
        a: bool,
        b: bool,
        fn both(self) -> bool {
            return self.a & self.b;
        }
    }
    """
    src = "return Pair.from_bits(a0 ^ a1).both();"
    c = compare_body(["[2]bool", "[2]bool"], "bool", src, tmp_dir, prefix)
    c.eval_assert([[True, False], [False, True]], True)
    assert_xor_count(c, 1)


def test_compact_print_struct(tmp_dir: Path):
    prefix = "struct Pair { a: bool, b: bool }"
    src = """
    print("{Pair.from_bits(a0 ^ a1)}");
    return a0;
    """
    c = compare_body(["[2]bool", "[2]bool"], "[2]bool", src, tmp_dir, prefix)
    c.eval_assert([[True, False], [False, True]], [True, False])
    assert_xor_count(c, 1)


def test_compact_range_start_length(tmp_dir: Path):
    src = """
    print("{(a0 ^ a1) +.. a2}");
    return a0;
    """
    c = compare_body(["uint(4)", "uint(4)", "uint(4)"], "uint(4)", src, tmp_dir)
    c.eval_assert([3, 5, 2], 3)
    assert_xor_count(c, 1)


def test_compact_tuple_chain(tmp_dir: Path):
    src = """
    var t = (a0, a1);
    for (i in 0..20) {
        t = (t.0 ^ t.1, t.0);
    }
    return t.0;
    """
    c = compare_body(["uint(8)", "uint(8)"], "uint(8)", src, tmp_dir)
    x, y = 3, 5
    for _ in range(20):
        x, y = x ^ y, x
    c.eval_assert([3, 5], x)
    assert_xor_count(c, 20)


def test_compact_struct_chain(tmp_dir: Path):
    prefix = "struct S { x: uint(8), y: uint(8) }"
    src = """
    var t = S.new(x=a0, y=a1);
    for (i in 0..20) {
        t = S.new(x=t.x ^ t.y, y=t.x);
    }
    return t.x;
    """
    c = compare_body(["uint(8)", "uint(8)"], "uint(8)", src, tmp_dir, prefix)
    x, y = 3, 5
    for _ in range(20):
        x, y = x ^ y, x
    c.eval_assert([3, 5], x)
    assert_xor_count(c, 20)
