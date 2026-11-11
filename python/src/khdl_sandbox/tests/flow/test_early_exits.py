from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


def test_simple_return(tmp_dir: Path):
    src = """
    return 2;
    """
    e = compare_body([], "int(0..8)", src, tmp_dir)
    e.eval_assert([], 2)


def test_break_compile(tmp_dir: Path):
    src = """
    var result = 0;
    for (i in 0..8) {
        result = i;
        if (i == 4) { break; }     
    }
    return result;
    """
    e = compare_body([], "int(0..8)", src, tmp_dir)
    e.eval_assert([], 4)


def test_break_hardware(tmp_dir: Path):
    src = """
    var result = 0;
    for (i in 0..8) {
        result = i;
        if (i == a0) { break; }     
    }
    return result;
    """
    e = compare_body(["int(-1..=8)"], "int(0..8)", src, tmp_dir)
    e.eval_assert([-1], 7)
    e.eval_assert([0], 0)
    e.eval_assert([4], 4)
    e.eval_assert([8], 7)


def test_continue_hardware(tmp_dir: Path):
    src = """
    var result = 0;
    for (i in 0..8) {
        if (i == a0) { continue; }     
        result += 1;
    }
    return result;
    """
    e = compare_body(["int(-1..=8)"], "int(0..=8)", src, tmp_dir)
    e.eval_assert([-1], 8)
    e.eval_assert([0], 7)
    e.eval_assert([4], 7)
    e.eval_assert([8], 8)


def test_return_select(tmp_dir: Path):
    src = "if (a0) { return 1; } else { return 2; }"
    e = compare_body(["bool"], "int(1..=2)", src, tmp_dir)
    e.eval_assert([True], 1)
    e.eval_assert([False], 2)


def test_return_loop(tmp_dir: Path):
    src = """
    for (i in 0..8) {
        if (a0 && i == 4) { return i; }     
    }
    return 0;
    """
    e = compare_body(["bool"], "int(0..=4)", src, tmp_dir)
    e.eval_assert([False], 0)
    e.eval_assert([True], 4)


def test_mix_all(tmp_dir: Path):
    src = """
    var count = 0;
    for (i in 0..4) {
        if (i == a0) { break; }     
        if (i == a1) { continue; }
        if (i == a2) { return -1; }
        count += 1;      
    }
    return count;
    """
    e = compare_body(
        ["int(-1..4)", "int(-1..4)", "int(-1..4)"],
        "int(-1..=4)",
        src,
        tmp_dir,
    )
    e.eval_assert([-1, -1, -1], 4)
    e.eval_assert([2, -1, -1], 2)
    e.eval_assert([-1, 2, -1], 3)
    e.eval_assert([-1, -1, 2], -1)


def test_nested_loop_break(tmp_dir: Path):
    src = """
    var count = 0;
    for (i0 in 0..4) {
        if (i0 == a0) { break; }
        for (i1 in 0..3) {
            if (i0 == a1) { break; }
            if (i1 == a2) { break; }
            count += 1;
        }
    }
    return count;
    """
    ar = "int(-1..4)"
    e = compare_body([ar, ar, ar], "int(0..=16)", src, tmp_dir)
    e.eval_assert([-1, -1, -1], 12)
    e.eval_assert([2, -1, -1], 6)
    e.eval_assert([-1, 2, -1], 9)
    e.eval_assert([-1, -1, 2], 8)


def test_match_return(tmp_dir: Path):
    src = """
    match (a0) {
        0 => {}
        1 => { return 1; }
    }
    return 0;
    """
    e = compare_body(["int(0..=1)"], "int(0..=1)", src, tmp_dir)
    e.eval_assert([0], 0)
    e.eval_assert([1], 1)


def test_loop_return_or_break_hardware(tmp_dir: Path):
    # the break should cause the code after the loop to become reachable
    src = """
    for (i in 0..4) {
        if (a0) { return 1; } else { break; }
    }
    return 2;
    """
    e = compare_body(["bool"], "int(0..8)", src, tmp_dir)
    e.eval_assert([True], 1)
    e.eval_assert([False], 2)


def test_loop_break_or_continue_hardware(tmp_dir: Path):
    # the loop should continue unrolling after the first iteration
    src = """
    var v: int(0..8) = 0;
    for (i in 0..4) {
        if (a0) { break; } else { v += 1; continue; }
    }
    return v;
    """
    e = compare_body(["bool"], "int(0..8)", src, tmp_dir)
    e.eval_assert([True], 0)
    e.eval_assert([False], 4)


def test_while_break_index_stays_compile(tmp_dir: Path):
    # This is really an xfail test, hopefully at some point in the future this actually starts working.
    # Currently the conditional break causes the `i` variable to become hardware,
    #   even in the while loop condition itself, where technically we know it will always known at compile time.
    src = """
    var i = 0;
    while (i < 4) {
        if (a0) {
            break;
        }
        i += 1;
    }
    return i;
    """
    with diag_error("accessing a hardware variable is only allowed in a hardware context"):
        _ = compare_body(["bool"], "int(0..8)", src, tmp_dir)
    # e.eval_assert([True], 0)
    # e.eval_assert([False], 4)


def test_return_in_wire_expression(tmp_dir: Path):
    src = """
    fn f(c: bool) -> uint(8) { if (c) { return 1; } return 2; }
    module top ports(c: in async bool, y: out async uint(8)) {
        wire w = f(c);
        comb { y = w; }
    }
    """
    inst = compile_custom(src).resolve_module("top.top").as_verilated(tmp_dir).instance()

    for c in [True, False]:
        inst.ports.c = c
        inst.step(1)
        assert inst.ports.y == (1 if c else 2)
