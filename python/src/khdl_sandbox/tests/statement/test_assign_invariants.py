"""Nominal field contracts survive every enclosing structural update and `any`."""
from pathlib import Path

import pytest

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


PREFIX = """
struct Pair { x: bool, y: uint(0..4) }
struct Box { value: any }
struct Generic(T: type) { value: T }
struct Outer { pair: Pair }
"""
PAIR = "Pair.new(x=false, y=0)"

# Each path reaches the same nominal field, but its declaration hint can be
# absent, precise, or lose the struct identity at any intermediate depth.
ROOTS = [
    (f"var p = {PAIR};", "p"),
    (f"var p: Pair = {PAIR};", "p"),
    (f"var p: any = {PAIR};", "p"),
    (f"var p = ({PAIR},);", "p.0"),
    (f"var p: Tuple(any) = ({PAIR},);", "p.0"),
    (f"var p = [{PAIR}];", "p[0]"),
    (f"var p: [_]any = [{PAIR}];", "p[0]"),
    (f"var p = [false, {PAIR}];", "p[1]"),
    (f"var p = [{PAIR}];", "p[0..1][0]"),
    (f"var p: Box = Box.new(value={PAIR});", "p.value"),
    (f"var p: Outer = Outer.new(pair={PAIR});", "p.pair"),
    (f"var p = Generic(any).new(value={PAIR});", "p.value"),
    (f"var p: Box = Box.new(value=([false, ({PAIR},)],));", "p.value.0[1].0"),
]


def run(body: str, prefix: str = PREFIX):
    return compile_custom(prefix + "\nfn check() -> any {\n" + body + "\n}").resolve("top.check")()


@pytest.mark.parametrize("declaration,path", ROOTS)
@pytest.mark.parametrize("value", ["-1", "4", "6", "false", '"bad"', "(0,)", "[0]"])
def test_nominal_field_rejects_invalid_values(declaration, path, value):
    with diag_error("type mismatch"):
        run(f"{declaration} {path}.y = {value}; return p;")


@pytest.mark.parametrize("declaration,path", ROOTS)
@pytest.mark.parametrize("value", [0, 1, 3])
def test_nominal_field_accepts_full_declared_range(declaration, path, value):
    assert run(f"{declaration} {path}.y = {value}; return {path}.y;") == value


@pytest.mark.parametrize("declaration,path", ROOTS)
def test_boolean_field_does_not_accept_an_integer(declaration, path):
    with diag_error("type mismatch"):
        run(f"{declaration} {path}.x = 0;")


@pytest.mark.parametrize("declaration,path", ROOTS)
@pytest.mark.parametrize("op,value", [("+=", 4), ("-=", 1), ("|=", 6)])
def test_compound_updates_preserve_nominal_contracts(declaration, path, op, value):
    with diag_error("type mismatch"):
        run(f"{declaration} {path}.y {op} {value}; return p;")


AGGREGATE_PREFIX = """
struct S {
    array: [3]uint(0..4),
    tuple: Tuple(uint(0..4), bool),
    nested: Tuple([2]uint(0..4)),
}
"""
AGGREGATE_INIT = "S.new(array=[0, 0, 0], tuple=(0, false), nested=([0, 0],))"
AGGREGATE_UPDATES = [
    ("array[1]", "6", "3"),
    ("array[0..2]", "[0, 6]", "[1, 3]"),
    ("array[0..2][1]", "6", "3"),
    ("array[0..2][1..2]", "[6]", "[3]"),
    ("tuple.0", "6", "3"),
    ("tuple.1", "0", "true"),
    ("nested.0[1]", "6", "3"),
    ("nested.0[0..2]", "[6, 0]", "[3, 1]"),
    ("array", "[0, 0]", "[1, 2, 3]"),
    ("tuple", "(0, 0)", "(3, true)"),
]


@pytest.mark.parametrize("annotation", ["", ": S", ": any"])
@pytest.mark.parametrize("path,bad,good", AGGREGATE_UPDATES)
def test_enclosing_field_contract_survives_nested_updates(annotation, path, bad, good):
    prefix = PREFIX + AGGREGATE_PREFIX
    with diag_error("type mismatch"):
        run(f"var s{annotation} = {AGGREGATE_INIT}; s.{path} = {bad};", prefix)
    assert run(f"var s{annotation} = {AGGREGATE_INIT}; s.{path} = {good}; return true;", prefix)


@pytest.mark.parametrize("ending", ["return p;", "p.y = 0; return p;", "return Pair.new(x=p.x, y=p.y);"])
def test_invalid_intermediate_values_cannot_escape_or_be_repaired(ending):
    with diag_error("type mismatch"):
        run(f"var p = {PAIR}; p.y = 6; {ending}")


def test_nominal_return_annotation_cannot_launder_invalid_fields():
    c = compile_custom(PREFIX + f"fn check() -> Pair {{ var p = {PAIR}; p.y = 6; return p; }}")
    with diag_error("type mismatch"):
        c.resolve("top.check")()


@pytest.mark.parametrize("suffix", ["", " p.y = 0;"])
def test_original_const_block_reports_assignment_error(suffix):
    # Python compilation is lazy; elaborating the module executes its const block.
    with diag_error("type mismatch"):
        c = compile_custom(PREFIX + f"module Probe ports() {{ const {{ var p = {PAIR}; p.y = 6; {suffix} print(p); }} }}")
        c.resolve("top.Probe")


def test_unconstrained_structural_components_can_change_type():
    assert run("""
        var a = [0]; a[0] = true;
        var t = (0,); t.0 = 8;
        var b = Box.new(value=[0]); b.value[0] = false;
        var p = Pair.new(x=false, y=0); p = true;
        return (a, t, b.value, p);
    """) == ([True], (8,), [False], True)


def test_replacing_a_nominal_value_beneath_any_is_allowed():
    assert run(f"var b = Box.new(value={PAIR}); b.value = false; return b.value;") is False


@pytest.mark.parametrize("value,valid", [(3, True), (6, False)])
def test_rhs_can_initialize_deferred_receiver(value, valid):
    body = f"var p; p.y = {{ p = {PAIR}; {value} }}; return p.y;"
    if valid:
        assert run(body) == value
    else:
        with diag_error("type mismatch"):
            run(body)


@pytest.mark.parametrize("annotation", ["", ": any"])
def test_rhs_replacement_uses_new_receivers_contract(annotation):
    prefix = PREFIX + "struct Other { x: bool, y: bool }\nstruct Wide { x: bool, y: uint(0..8) }"
    with diag_error("type mismatch"):
        run(f"var p{annotation} = {PAIR}; p.y = {{ p = Other.new(x=false, y=false); 1 }};", prefix)
    assert run(f"var p{annotation} = {PAIR}; p.y = {{ p = Wide.new(x=false, y=0); 6 }}; return p.y;", prefix) == 6


def test_rhs_alias_can_replace_receiver():
    prefix = PREFIX + "struct Other { x: bool, y: bool }"
    with diag_error("type mismatch"):
        run(f"var p = {PAIR}; val r = ref(p); p.y = {{ deref(r) = Other.new(x=false, y=false); 1 }};", prefix)


def test_selector_evaluated_once_before_rhs_and_sibling_updates_preserved():
    assert run(f"""
        var ps = [{PAIR}, {PAIR}];
        var calls = 0;
        ps[{{ calls += 1; 0 }}].y = {{
            assert(calls == 1);
            ps[0].x = true;
            3
        }};
        return (calls, ps[0].x, ps[0].y, ps[1].y);
    """) == (1, True, 3, 0)


def test_generated_field_name_evaluated_once_before_rhs():
    assert run(f"""
        var p = {PAIR}; var calls = 0;
        p.ident({{ calls += 1; "y" }}) = {{ assert(calls == 1); 3 }};
        return (calls, p.y);
    """) == (1, 3)


def test_declared_range_is_stricter_than_representation_width():
    with diag_error("type mismatch"):
        run("var s = Small.new(value=0); s.value = 3;", "struct Small { value: uint(0..3) }")


def test_copy_on_write_preserves_other_aggregate_values():
    assert run(f"""
        var p = Box.new(value=[{PAIR}]);
        val saved = p;
        p.value[0].y = 3;
        return (saved.value[0].y, p.value[0].y);
    """) == (0, 3)


@pytest.mark.parametrize("declaration,path", [
    (f"var p = {PAIR};", "p.y"),
    (f"var p: Pair = {PAIR};", "p.y"),
    (f"var p = Outer.new(pair={PAIR});", "p.pair.y"),
    ("var p = S.new(array=[0, 0, 0], tuple=(0, false), nested=([0, 0],));", "p.array[1]"),
])
@pytest.mark.parametrize("source", ["6", "input", "{ var v; if (choose) { v = 6; } else { v = 0; } v }"])
def test_invalid_hardware_updates_report_type_mismatch(declaration, path, source):
    c = compile_custom(PREFIX + AGGREGATE_PREFIX + f"""
        module Probe ports(input: in async uint(0..8), choose: in async bool, output: out async uint(0..4)) {{
            comb {{ {declaration} {path} = {source}; output = {path}; }}
        }}
    """)
    with diag_error("type mismatch"):
        c.resolve("top.Probe")


def test_hardware_dynamic_index_checks_nominal_element_contract():
    c = compile_custom(AGGREGATE_PREFIX + f"""
        module Probe ports(index: in async uint(0..3), input: in async uint(0..8), output: out async [3]uint(0..4)) {{
            comb {{ var s = {AGGREGATE_INIT}; s.array[index] = input; output = s.array; }}
        }}
    """)
    with diag_error("type mismatch"):
        c.resolve("top.Probe")


def test_hardware_dynamic_slice_checks_enclosing_field_contract():
    c = compile_custom(AGGREGATE_PREFIX + f"""
        module Probe ports(index: in async uint(0..2), input: in async [2]uint(0..8)) {{
            comb {{ var s = {AGGREGATE_INIT}; s.array[index+..2] = input; }}
        }}
    """)
    with diag_error("type mismatch"):
        c.resolve("top.Probe")


def test_hardware_dynamic_index_into_struct_array_checks_field_contract():
    c = compile_custom(PREFIX + f"""
        module Probe ports(index: in async uint(0..2), input: in async uint(0..8)) {{
            comb {{ var ps = [{PAIR}, {PAIR}]; ps[index].y = input; }}
        }}
    """)
    with diag_error("type mismatch"):
        c.resolve("top.Probe")


@pytest.mark.parametrize("value,valid", [(3, True), (6, False)])
def test_signal_type_can_be_established_by_rhs(value, valid):
    c = compile_custom(PREFIX + f"""
        module Probe ports(output: out async Pair) {{
            wire p;
            comb {{ p.y = {{ p = {PAIR}; {value} }}; output = p; }}
        }}
    """)
    if valid:
        assert c.resolve("top.Probe").as_verilog().source
    else:
        with diag_error("type mismatch"):
            c.resolve("top.Probe")


def test_valid_hardware_nested_updates_and_dynamic_indices(tmp_dir: Path):
    c = compare_body(
        ["uint(0..4)", "uint(0..3)", "bool"], "Tuple([3]uint(0..4), bool)",
        f"""
        var s = {AGGREGATE_INIT};
        s.array[a1] = a0;
        s.tuple.1 = a2;
        return (s.array, s.tuple.1);
        """, tmp_dir, prefix=AGGREGATE_PREFIX,
    )
    for value in range(4):
        for index in range(3):
            for flag in [False, True]:
                expected = [0, 0, 0]
                expected[index] = value
                c.eval_assert([value, index, flag], (expected, flag))
