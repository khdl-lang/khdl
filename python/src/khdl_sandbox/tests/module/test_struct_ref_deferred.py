"""Logical fields use actual receiver metadata at the documented consumption point."""
from pathlib import Path

import pytest

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom, diag_error


PREFIX = """
struct Alias { ref value: uint(0..4) }
struct Ordinary { value: bool }
struct Box { value: any }
struct Generic(T: type) { value: T }
struct Pair { x: bool, y: uint(0..4) }
"""

ROOTS = [
    ("val s = Alias.new(value=ref(x));", "s.value"),
    ("val s: Alias = Alias.new(value=ref(x));", "s.value"),
    ("val s: any = Alias.new(value=ref(x));", "s.value"),
    ("val s: Tuple(any) = (Alias.new(value=ref(x)),);", "s.0.value"),
    ("val s: [_]any = [Alias.new(value=ref(x))];", "s[0].value"),
    ("val s = [Ordinary.new(value=false), Alias.new(value=ref(x))];", "s[1].value"),
    ("val s = Box.new(value=Alias.new(value=ref(x)));", "s.value.value"),
    ("val s = Generic(any).new(value=Alias.new(value=ref(x)));", "s.value.value"),
    ("val s = Box.new(value=([false, (Alias.new(value=ref(x)),)],));", "s.value.0[1].0.value"),
]


def run(body, prefix=PREFIX):
    return compile_custom(prefix + "\nfn check() -> any {\n" + body + "\n}").resolve("top.check")()


@pytest.mark.parametrize("declaration,path", ROOTS)
def test_transparent_reads_writes_compounds_and_reference_taking(declaration, path):
    assert run(f"""
        var x: uint(0..4) = 1;
        {declaration}
        assert({path} == 1);
        {path} = 2;
        assert(x == 2);
        {path} += 1;
        assert(x == 3);
        val forwarded = ref({path});
        deref(forwarded) = 0;
        return (x, {path});
    """) == (0, 0)


@pytest.mark.parametrize("declaration,path", ROOTS)
@pytest.mark.parametrize("operation", ["= 4", "+= 4", "= false", "= ref(x)"])
def test_transparent_write_enforces_referent_contract(declaration, path, operation):
    with diag_error("type mismatch"):
        run(f"var x: uint(0..4) = 0; {declaration} {path} {operation};")


@pytest.mark.parametrize("annotation", ["", ": Alias", ": any"])
@pytest.mark.parametrize("operation,expected", [("=", (1, 2)), ("+=", (3, 0))])
def test_rhs_rebinding_has_defined_plain_and_compound_order(annotation, operation, expected):
    assert run(f"""
        var x: uint(0..4) = 1;
        var y: uint(0..4) = 0;
        var s{annotation} = Alias.new(value=ref(x));
        s.value {operation} {{ s = Alias.new(value=ref(y)); 2 }};
        return (x, y);
    """) == expected


def test_explicit_reference_is_captured_before_rhs():
    assert run("""
        var x: uint(0..4) = 0; var y: uint(0..4) = 0;
        var s: any = Alias.new(value=ref(x));
        deref(ref(s.value)) = { s = Alias.new(value=ref(y)); 3 };
        return (x, y);
    """) == (3, 0)


def test_finite_projection_through_cyclic_reference_graph():
    assert run("""
        var node: any = 0;
        node = Node.new(next=ref(node));
        node.next.next = 3;
        return node;
    """, "struct Node { ref next: any }") == 3


def test_rhs_can_initialize_transparent_receiver():
    assert run("""
        var x: uint(0..4) = 0;
        var s;
        s.value = { s = Alias.new(value=ref(x)); 3 };
        return x;
    """) == 3


def test_rhs_can_change_field_between_ordinary_and_transparent():
    assert run("""
        var x: uint(0..4) = 0;
        var s = Ordinary.new(value=false);
        s.value = { s = Alias.new(value=ref(x)); 3 };
        s.value = { s = Ordinary.new(value=false); true };
        return (x, s.value);
    """) == (3, True)


def test_nested_referent_field_contract_is_intrinsic_even_through_any_reference():
    with diag_error("type mismatch"):
        run("""
            var p = Pair.new(x=false, y=0);
            val r = ref(p);
            deref(r).y = 6;
        """)


def test_nested_reference_fields_and_one_level_of_dereferencing():
    assert run("""
        var x: uint(0..4) = 0;
        var y: uint(0..4) = 0;
        var pointer: Ref(uint(0..4)) = ref(x);
        val s: any = Indirect.new(pointer=ref(pointer));
        s.pointer = ref(y);
        deref(s.pointer) = 3;
        val inner: any = Alias.new(value=ref(x));
        val outer: any = RefOuter.new(inner=ref(inner));
        outer.inner.value = 2;
        return (x, y);
    """, PREFIX + "struct Indirect { ref pointer: Ref(uint(0..4)) }\nstruct RefOuter { ref inner: any }") == (2, 3)


def test_ordinary_reference_field_still_requires_explicit_dereference():
    assert run("""
        var x: uint(0..4) = 1;
        val s: any = Explicit.new(value=ref(x));
        deref(s.value) = 3;
        return x;
    """, PREFIX + "struct Explicit { value: Ref(uint(0..4)) }") == 3


def test_reference_taken_from_an_uninitialized_transparent_receiver_is_rejected():
    with diag_error("variable has not yet been assigned a value"):
        run("var s; val r = ref(s.value);")


def test_late_transparent_assignment_checks_referent_lifetime():
    with diag_error("cannot access variable after its scope has ended"):
        run("""
            var x: uint(0..4) = 0;
            var s: any = Alias.new(value=ref(x));
            s.value = { s = escape(); 3 };
        """, PREFIX + "fn escape() -> Alias { var dead: uint(0..4) = 0; return Alias.new(value=ref(dead)); }")


def test_transparent_assignment_preserves_target_immutability():
    with diag_error("cannot assign to immutable variable"):
        run("val x: uint(0..4) = 0; val s: any = Alias.new(value=ref(x)); s.value = 3;")


def test_transparent_rhs_expected_type_unwraps_binding():
    assert run("""
        var p: Pair = Pair.new(x=false, y=0);
        val s: PairAlias = PairAlias.new(pair=ref(p));
        s.pair = Pair.new(x=true, y=3);
        return (p.x, p.y);
    """, PREFIX + "struct PairAlias { ref pair: Pair }") == (True, 3)


def test_transparent_expected_type_supports_inferred_generic_constructor():
    assert run("""
        var item: Item(bool) = Item(bool).new(value=false);
        val handle: Handle = Handle.new(item=ref(item));
        handle.item = Item.new(value=true);
        return item.value;
    """, "struct Item(T: type) { value: T }\nstruct Handle { ref item: Item(bool) }") is True


def test_ref_field_hardware_access_beneath_any(tmp_dir: Path):
    c = compare_body(
        ["uint(0..4)", "uint(0..3)"], "[3]uint(0..4)",
        """
        var storage: [3]uint(0..4) = [0, 0, 0];
        val wrapper: any = ArrayAlias.new(values=ref(storage));
        wrapper.values[a1] = a0;
        return storage;
        """, tmp_dir, prefix="struct ArrayAlias { ref values: [3]uint(0..4) }",
    )
    for value in range(4):
        for index in range(3):
            expected = [0, 0, 0]
            expected[index] = value
            c.eval_assert([value, index], expected)


def test_ref_interface_beneath_any_in_instance_connection():
    c = compile_custom("""
        interface Link { value: uint(0..4), view Source { value: out } }
        struct Endpoint { ref channel: Link }
        module Child ports(output: interface async Link.Source) { comb { output.value = 3; } }
        module Probe ports(output: interface async Link.Source) {
            const ep: any = Endpoint.new(channel=ref(output));
            instance Child ports(output=ep.channel);
        }
    """)
    assert c.resolve("top.Probe").as_verilog().source


def test_ref_interface_beneath_any_in_connect():
    c = compile_custom("""
        interface Link { value: uint(0..4), view Input { value: in } view Output { value: out } }
        struct Endpoint { ref channel: Link }
        module Probe ports(input: interface async Link.Input, output: interface async Link.Output) {
            const ep: any = Endpoint.new(channel=ref(output));
            connect(input view Input, ep.channel view Output);
        }
    """)
    assert c.resolve("top.Probe").as_verilog().source


def test_ref_signal_beneath_any_preserves_input_direction():
    c = compile_custom("""
        struct Alias { ref value: uint(0..4) }
        module Probe ports(input: in async uint(0..4)) {
            comb { val wrapper: any = Alias.new(value=ref(input)); wrapper.value = 0; }
        }
    """)
    with diag_error("cannot assign to input port"):
        c.resolve("top.Probe")
