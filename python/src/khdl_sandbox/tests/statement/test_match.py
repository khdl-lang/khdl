from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error, diag_warning


def test_match_bool(tmp_dir: Path):
    src = """
    match (a0) {
        false => { return 0; }
        true => { return 1; }
    }
    """
    c = compare_body(["bool"], "int(0..=1)", src, tmp_dir)

    c.eval_assert([False], 0)
    c.eval_assert([True], 1)


def test_match_int(tmp_dir: Path):
    src = """
    val five = 5;
    match (a0) {
        0 => { return 0; }
        1 => { return 1; }
        in 2..4 => { return 2; }
        five => { return 3; }
        val other => { return -other; }
    }
    """
    c = compare_body(["int(0..8)"], "int(-8..=3)", src, tmp_dir)

    c.eval_assert([0], 0)
    c.eval_assert([1], 1)
    c.eval_assert([2], 2)
    c.eval_assert([3], 2)
    c.eval_assert([5], 3)
    c.eval_assert([6], -6)


def test_match_enum(tmp_dir: Path):
    # TODO simplify this once enums are constructible in python
    prefix = """
    enum ABC { A(bool), B(uint(0..2)), C, D }
    """
    src = """
    val e;
    match (a0) {
        0 => { e = ABC.A(false); }
        1 => { e = ABC.A(true); }
        2 => { e = ABC.B(0); }
        3 => { e = ABC.B(1); }
        4 => { e = ABC.C; }
        5 => { e = ABC.D; }
    }
    
    match (e) {
        .A(val x) => { return -bool_to_int(x); }
        .B(val x) => { return -2 - x; }
        .C => { return -4; }
        _ => { return -5; }  
    }
    """
    c = compare_body(["int(0..=5)"], "int(-5..=0)", src, tmp_dir, prefix)

    c.eval_assert([0], 0)
    c.eval_assert([1], -1)
    c.eval_assert([2], -2)
    c.eval_assert([3], -3)
    c.eval_assert([4], -4)
    c.eval_assert([5], -5)


def test_match_fallthrough_compile():
    src = """
    fn f(x: int) -> int {
        match (x) {
            0 => { return 0; } 
        }
    }
    """
    c = compile_custom(src)
    f = c.resolve("top.f")

    assert f(0) == 0
    with diag_error("compile-time match statement reached end without matching any branch"):
        assert f(1) == 0


def test_match_fallthrough_hardware_int():
    src = """
    module foo_int ports(x: in async int(0..=4)) {
        comb {
            match (x) {
                0 => {}
                in 1..=2 => {}
            }
        }
    }
    """
    c = compile_custom(src)
    with diag_error("hardware match statement must be exhaustive"):
        c.resolve("top.foo_int")


def test_match_fallthrough_hardware_enum():
    src = """
    enum AB { A, B }
    module top ports(x: in async AB) {
        comb {
            match (x) {}        
        }
    }
    """
    c = compile_custom(src)
    with diag_error("hardware match statement must be exhaustive"):
        c.resolve("top.top")

    # TODO setting to allow warnings without crashing?
    src = """
    module top ports(x: in async bool) {
        comb {
            match (x) {
                true => {}
                false => {}
                _ => {}
            }
        }
    }
    """
    c = compile_custom(src)
    with diag_warning("unreachable match branch"):
        c.resolve("top.top")


def test_match_enum_after_wildcard():
    body = """
    module top ports(x: in async Option(bool)) {
        comb {
            match (x) {
                _ => {}
                .Some(_) => {}
            }
        }
    }
    """
    with diag_warning("unreachable match branch"):
        compile_custom(body).resolve("top.top")


def test_match_remaining_range_val_val(tmp_dir: Path):
    src = """
    match (a0) {
        in 0..4 => { return 4; }
        val other => { return other; }
    }
    """
    c = compare_body(["int(0..8)"], "int(4..8)", src, tmp_dir)
    for a0 in range(8):
        c.eval_assert([a0], max(4, a0))


def test_match_remaining_range_val_wildcard(tmp_dir: Path):
    src = """
    match (a0) {
        in 0..4 => { return 4; }
        _ => { return a0; }
    }
    """
    c = compare_body(["int(0..8)"], "int(4..8)", src, tmp_dir)
    for a0 in range(8):
        c.eval_assert([a0], max(4, a0))


def test_match_remaining_range_expr_val(tmp_dir: Path):
    src = """
    match (a0 + a1) {
        in 0..4 => { return 4; }
        val other => { return other; }
    }
    """
    c = compare_body(["int(0..5)", "int(0..4)"], "int(4..8)", src, tmp_dir)
    for a0 in range(5):
        for a1 in range(4):
            c.eval_assert([a0, a1], max(4, a0 + a1))
