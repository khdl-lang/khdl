from pathlib import Path

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


def test_merge_conditional_write():
    src = """
    module foo ports(x: in async int(0..8)) {
        comb {
            var a = false;
            if (x < 4) {
                a = true;
            }
        }
    }
    """
    compile_custom(src).resolve("top.foo")


def test_merge_tuple_compile(tmp_dir: Path):
    src = """
    val result;
    if (a0) {
        result = (false, 1);
    } else {
        result = (true, 0);
    }
    return result;
    """
    e = compare_body(["bool"], "Tuple(bool, uint(1))", src, tmp_dir)
    e.eval_assert([True], (False, 1))
    e.eval_assert([False], (True, 0))


def test_merge_struct_compile(tmp_dir: Path):
    src = """
    struct S { x: bool } 
    val result;
    if (a0) {
        result = S.new(x=false);
    } else {
        result = S.new(x=true);
    }
    return result.x;
    """
    e = compare_body(["bool"], "bool", src, tmp_dir)
    e.eval_assert([True], False)
    e.eval_assert([False], True)


def test_merge_array_compile(tmp_dir: Path):
    src = """
    val result;
    if (a0) {
        result = [1, 2];
    } else {
        result = [3, 4];
    }
    return result;
    """
    e = compare_body(["bool"], "[2]int(1..=4)", src, tmp_dir)
    e.eval_assert([True], [1, 2])
    e.eval_assert([False], [3, 4])


def test_merge_undefined_return_match(tmp_dir: Path):
    src = """
    match (a0) {
        0 => { return 1; }
        1 => { return 2; }
        _ => {}
    }
    return 3;
    """
    e = compare_body(["uint(0..4)"], "int(0..4)", src, tmp_dir)
    for i in range(4):
        e.eval_assert([i], min(3, i + 1))


def test_merge_undefined_return_union_not_hardware():
    src = """
    fn f(a: uint(0..4)) -> any {
        match (a) {
            0 => { return 1; }
            1 => { return true; }
            _ => {}
        }
        return 3;
    }
    module top ports(x: in async uint(0..4)) { comb { val _ = f(x); } }
    """
    with diag_error("branch assignment merging needs hardware type"):
        compile_custom(src).resolve("top.top")


def test_merge_same_version_parent(tmp_dir: Path):
    # this was a bug at some point:
    #   different variables can share versions but still have different IR variables,
    #   and merging wrongly skipped the copies if the versions matched
    src = """
    val v = a1;
    var r = v;
    if (a0) { r = v; }
    return r;
    """
    e = compare_body(["bool", "uint(8)"], "uint(8)", src, tmp_dir)
    for c in [False, True]:
        for x in [0, 5, 255]:
            e.eval_assert([c, x], x)


def test_merge_same_version_kept(tmp_dir: Path):
    # all branches have the same version, so the merged value should also have that version
    src = """
    val v = a1;
    var r = v;
    if (a0) { r = v; }
    if (v < 4) { return r; }
    return 0;
    """
    e = compare_body(["bool", "uint(8)"], "uint(0..4)", src, tmp_dir)
    for c in [False, True]:
        for x in [0, 3, 4, 255]:
            e.eval_assert([c, x], x if x < 4 else 0)


def test_merge_implications_joined(tmp_dir: Path):
    # the branches hold different versions but both imply "v < 4",
    #   so the merged value should also have that implication
    src = """
    val v = a1;
    var b = v < 4;
    if (a0) { b = v < 2; }
    if (b) { return v; }
    return 0;
    """
    e = compare_body(["bool", "uint(8)"], "uint(0..4)", src, tmp_dir)
    for c in [False, True]:
        for x in [0, 2, 3, 4, 255]:
            e.eval_assert([c, x], x if x < (2 if c else 4) else 0)


def test_merge_not_hardware():
    src = """
    module top ports(c: in async bool) {
        comb {
            var a = "x";
            if (c) { a = "y"; }
        }
    }
    """
    with diag_error("branch assignment merging only works for hardware types", has_info="for this variable"):
        compile_custom(src).resolve("top.top")


def test_merge_union_not_hardware():
    # each branch type is hardware, but their union is not
    src = """
    module top ports(c: in async bool) {
        comb {
            var a = 1;
            if (c) { a = true; }
        }
    }
    """
    with diag_error("branch assignment merging needs hardware type", has_info="for this variable"):
        compile_custom(src).resolve("top.top")


def test_merge_struct_non_hardware_field_same():
    src = """
    struct S { s: str, x: uint(8) }
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = S.new(s="a", x=0);
            if (c) { a = S.new(s="a", x=y); }
            print(a);
        }
    }
    """
    compile_custom(src).resolve("top.top")


def test_merge_struct_non_hardware_field_different():
    src = """
    struct S { s: str, x: uint(8) }
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = S.new(s="a", x=0);
            if (c) { a = S.new(s="b", x=y); }
        }
    }
    """
    with diag_error(
            "branch assignment merging only works for hardware types",
            has_info="field `a.s` of value in branch assigned here has type `str`",
    ):
        compile_custom(src).resolve("top.top")


def test_merge_struct_field_union_not_hardware():
    src = """
    struct S { s: any, x: uint(8) }
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = S.new(s=1, x=0);
            if (c) { a = S.new(s=true, x=y); }
        }
    }
    """
    with diag_error(
            "branch assignment merging needs hardware type",
            has_info="field `a.s` of value before branch assigned here has type `int(1..2)`",
    ):
        compile_custom(src).resolve("top.top")


def test_merge_nested_field_path():
    src = """
    struct S { s: str, x: uint(8) }
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = (y, S.new(s="a", x=0));
            if (c) { a = (y, S.new(s="b", x=y)); }
        }
    }
    """
    with diag_error(
            "branch assignment merging only works for hardware types",
            has_info="field `a.1.s` of value in branch assigned here has type `str`",
    ):
        compile_custom(src).resolve("top.top")


def test_merge_tuple_length_mismatch_non_hardware():
    src = """
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = ("a", y);
            if (c) { a = ("a", y, y); }
        }
    }
    """
    with diag_error("branch assignment merging needs hardware type", has_info="for this variable"):
        compile_custom(src).resolve("top.top")


def test_merge_tuple_vs_int():
    src = """
    module top ports(c: in async bool, y: in async uint(8)) {
        comb {
            var a = ("a", y);
            if (c) { a = 5; }
        }
    }
    """
    with diag_error(
            "branch assignment merging needs hardware type",
            has_info="value in branch assigned here has type `int(5..6)`",
    ):
        compile_custom(src).resolve("top.top")


def test_merge_partially_assigned():
    src = """
    module top ports(c: in async bool) {
        comb {
            val a;
            if (c) { a = 1; }
            val _ = a;
        }
    }
    """
    with diag_error("variable has not yet been assigned a value in all preceding branches"):
        compile_custom(src).resolve("top.top")


def test_merge_partially_assigned_then_assign():
    # a partially assigned immutable variable can't be assigned again
    src = """
    module top ports(c: in async bool) {
        comb {
            val a;
            if (c) { a = 1; }
            a = 2;
        }
    }
    """
    with diag_error("cannot assign to immutable variable"):
        compile_custom(src).resolve("top.top")


def test_merge_signal_compile(tmp_dir: Path):
    src = """
    module top ports(c: in async bool, y: out async [2]uint(8)) {
        comb {
            y = [1, 2];
            if (c) { y = [3, 4]; }
        }
    }
    """
    inst = compile_custom(src).resolve_module("top.top").as_verilated(tmp_dir).instance()
    for c in [False, True]:
        inst.ports.c = c
        inst.step(1)
        assert inst.ports.y == ([3, 4] if c else [1, 2])
