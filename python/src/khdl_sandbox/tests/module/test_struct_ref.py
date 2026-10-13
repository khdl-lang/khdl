"""Struct reference fields project to places, while construction stores bindings."""
from pathlib import Path

import khdl
import pytest

from khdl_sandbox.common.util import compile_custom


def test_struct_ref_value_semantics():
    c = compile_custom('''
        struct Pair { a: uint(8), b: uint(8) }
        struct Alias {
            ref value: uint(8), ref array: [3]uint(8), ref pair: Pair,
            explicit: Ref(uint(8)), tag: bool,
            fn increment(self) { self.value = (self.value + 1) & 255; }
        }
        struct Outer { inner: Alias }
        struct RefOuter { ref inner: Alias }
        fn check() -> uint(8) {
            var x: uint(8) = 5;
            var y: uint(8) = 100;
            var a: [3]uint(8) = [1, 2, 3];
            var p: Pair = Pair.new(a=4, b=6);
            val obj: Alias = Alias.new(value=ref(x), array=ref(a), pair=ref(p), explicit=ref(x), tag=true);
            val copy = obj;
            copy.increment();
            assert(x == 6);
            obj.array[1] = obj.value;
            obj.array[0..2] = [7, 8];
            obj.pair.a = 9;
            obj.pair.b += 1;
            val forwarded = ref(obj.value);
            deref(forwarded) = 10;
            deref(obj.explicit) = 11;
            assert(x == 11 && a == [7, 8, 3] && p.a == 9 && p.b == 7);
            Outer.new(inner=obj).inner.value = 12;
            val outer = RefOuter.new(inner=ref(obj));
            outer.inner.increment();
            assert(x == 13);
            var replace = copy;
            replace = Alias.new(value=ref(y), array=ref(a), pair=ref(p), explicit=ref(y), tag=false);
            replace.increment();
            assert(y == 101 && x == 13);
            return copy.value;
        }
    ''')
    assert c.resolve('top.check')() == 13


def test_struct_ref_generic_generated_fields():
    c = compile_custom('''
        struct Lanes(T: type) { for (i in 0..2) { ref ident("lane_{i}"): T, } }
        fn check() -> uint(8) {
            var a: uint(8) = 3;
            var b: uint(8) = 4;
            val lanes = Lanes(uint(8)).new(lane_0=ref(a), lane_1=ref(b));
            lanes.lane_0 = lanes.lane_1;
            return a;
        }
    ''')
    assert c.resolve('top.check')() == 4


def test_struct_ref_one_dereference_only():
    c = compile_custom('''
        struct Indirect { ref pointer: Ref(uint(8)) }
        fn check() -> uint(8) {
            var x: uint(8) = 1;
            var y: uint(8) = 2;
            var r: Ref(uint(8)) = ref(x);
            val obj = Indirect.new(pointer=ref(r));
            obj.pointer = ref(y);
            deref(obj.pointer) = 3;
            assert(x == 1);
            return y;
        }
    ''')
    assert c.resolve('top.check')() == 3


@pytest.mark.parametrize('transparent', [False, True])
def test_struct_ref_registered_interface(tmp_dir: Path, transparent):
    field = 'ref channel: Link' if transparent else 'channel: RefInterface(Link)'
    access = 'self.channel' if transparent else 'deref(self.channel)'
    c = compile_custom('''
        interface Link { value: uint(8), view Source { value: out } }
        struct Endpoint {
            FIELD,
            fn update(self, value: uint(8)) {
                reg wire ACCESS.value = 0;
                ACCESS.value = value;
            }
        }
        module Child ports(input: in async uint(8), output: out async uint(8)) {
            comb { output = input; }
        }
        module Probe ports(clk: in clock, sync(clk) {
            rst: in bool, input: in uint(8), output: interface Link.Source,
        }) {
            clocked(clk, sync rst) {
                val ep = Endpoint.new(channel=ref(output));
                ep.update(input);
            }
        }
    '''.replace('FIELD', field).replace('ACCESS', access))
    inst = c.resolve('top.Probe').as_verilated(tmp_dir).instance()
    p = inst.ports
    p.clk = False
    p.rst = True
    p.input = 99
    inst.step(1)
    p.clk = True
    inst.step(1)
    assert p.output.value == 0
    for value in [0, 17, 255]:
        p.clk = False
        p.rst = False
        p.input = value
        inst.step(1)
        p.clk = True
        inst.step(1)
        assert p.output.value == value


def test_struct_ref_interface_forwarding_and_instance():
    c = compile_custom('''
        interface Link { x: uint(8), view Source { x: out } }
        struct Endpoint { ref channel: Link }
        fn forward(ep: Endpoint) -> RefInterface(Link) { return ref(ep.channel); }
        module Child ports(output: out async uint(8)) { comb { output = 7; } }
        module Probe ports(output: interface async Link.Source) {
            const ep = Endpoint.new(channel=ref(output));
            const again = Endpoint.new(channel=forward(ep));
            instance Child ports(output=again.channel.x);
        }
    ''')
    assert 'module Probe' in c.resolve('top.Probe').as_verilog().source


@pytest.mark.parametrize('body,expected', [
    ('struct S { ref a: uint(8) } const s = S.new(a=1);', 'type mismatch'),
    ('struct S { ref a: uint(8) } const s = S.new(a=ref({ var v: bool = false; v }));', 'reference'),
    ('''interface I { x: bool, view V { x: out } }
        struct S { ref a: I.V }''', 'reference field annotation'),
    ('struct S { ref a: 42 }', 'reference field annotation'),
    ('''struct S { ref a: uint(8) }
        fn bad() { val x: uint(8) = 0; val s = S.new(a=ref(x)); s.a = 1; }
        const { bad(); }''', 'immutable variable'),
    ('''struct S { ref a: uint(8) }
        fn escape() -> S { var x: uint(8) = 0; return S.new(a=ref(x)); }
        fn bad() { val s = escape(); val _ = s.a; }
        const { bad(); }''', 'scope has ended'),
])
def test_struct_ref_invalid_declarations_and_targets(body, expected):
    # Python compilation is lazy; a callable checks every specialization here.
    source = khdl.Source()
    source.add_file_content(['top'], 'top.kh', body + '\nfn check() { S; }')
    with pytest.raises(khdl.DiagnosticException) as exc:
        c = source.compile()
        c.resolve('top.check')()
        if 'fn bad' in body:
            c.resolve('top.bad')()
        elif 'const s' in body:
            c.resolve('top.s')
    assert expected in exc.value.combined_string
    assert 'internal compiler error' not in exc.value.combined_string


@pytest.mark.parametrize('source,expected', [
    ('''struct S { ref a: uint(8) }
        module Probe ports(input: in async uint(8)) {
            comb { val s = S.new(a=ref(input)); s.a = 0; }
        }''', 'input port'),
    ('''struct S { ref a: uint(8) }
        module Probe ports(clk: in clock, other: in clock, input: in sync(other) uint(8)) {
            clocked(clk) { val s = S.new(a=ref(input)); val _ = s.a; }
        }''', 'domain'),
    ('''struct S { ref a: uint(8) }
        module Child(s: S) ports() {}
        module Probe ports(input: in async uint(8)) {
            const s = S.new(a=ref(input)); instance Child(s) ports();
        }''', 'item parameters cannot contain references'),
    ('''interface I { x: bool, view V { x: out } }
        interface J { x: bool, view V { x: out } }
        struct S { ref channel: I }
        module Probe ports(output: interface async J.V) {
            comb { val s = S.new(channel=ref(output)); }
        }''', 'type mismatch'),
    ('''struct S { ref a: uint(8) }
        module Probe ports(clk: in clock, rst: in sync(clk) bool, output: out sync(clk) uint(8)) {
            clocked(clk, sync rst) {
                val s = S.new(a=ref(output)); reg wire s.a = 0; reg wire s.a = 0;
            }
        }''', 'already marked as a register'),
    ('''struct S { ref a: uint(8) }
        module Probe ports(select: in async bool, result: out async uint(8)) {
            comb {
                var a: uint(8) = 1; var b: uint(8) = 2;
                var s = S.new(a=ref(a));
                if (select) { s = S.new(a=ref(b)); }
                result = s.a;
            }
        }''', 'branch assignment merging only works for hardware types'),
])
def test_struct_ref_invalid_hardware(source, expected):
    with pytest.raises(khdl.DiagnosticException) as exc:
        compile_custom(source).resolve('top.Probe')
    assert expected in exc.value.combined_string
    assert 'internal compiler error' not in exc.value.combined_string


def test_struct_ref_runtime_array_and_method(tmp_dir: Path):
    from khdl_sandbox.common.compare import compare_body

    comparison = compare_body(
        ['uint(8)', 'uint(0..3)'], '[3]uint(8)',
        '''
        var storage: [3]uint(8) = [a0, 0, 0];
        val slot = ArraySlot.new(data=ref(storage));
        slot.set(a1, a0);
        val copied = slot;
        copied.data[0] = copied.data[a1];
        return storage;
        ''', tmp_dir,
        prefix='''
        struct ArraySlot {
            ref data: [3]uint(8),
            fn set(self, index: uint(0..3), value: uint(8)) {
                self.data[index] = value;
            }
        }
        ''',
    )
    for value in [0, 1, 255]:
        for index in range(3):
            expected = [value, 0, 0]
            expected[index] = value
            comparison.eval_assert([value, index], expected)


def test_struct_ref_only_reads_selected_clock_domain():
    c = compile_custom('''
        struct Both { ref selected: uint(8), ref unrelated: uint(8) }
        module Probe ports(clk: in clock, other: in clock,
            a: in sync(clk) uint(8), b: in sync(other) uint(8),
            result: out sync(clk) uint(8)) {
            clocked(clk) {
                val obj = Both.new(selected=ref(a), unrelated=ref(b));
                reg wire result = undef;
                result = obj.selected;
            }
        }
    ''')
    c.resolve('top.Probe').as_verilog()


def test_struct_ref_non_hardware_payload():
    with pytest.raises(khdl.DiagnosticException) as exc:
        compile_custom('''
            struct Alias { ref value: uint(8) }
            module Probe ports(input: in async Alias) {}
        ''').resolve('top.Probe')
    assert 'hardware' in exc.value.combined_string


def test_struct_ref_format_generated_fields_and_comments():
    text = '''
        struct S(T:type) {
            for (i in 0..2) { ref /* binding */ ident("lane_{i}"):T, }
            ref channel:Link(T),
            ordinary:Ref(T),
            fn read(self)->T { return self.ident("lane_0"); }
        }
    '''
    formatted = khdl.format_file(text)
    assert khdl.format_file(formatted) == formatted
    assert 'ref /* binding */ ident(' in formatted
    assert 'ref channel: Link(T)' in formatted
    assert 'ordinary: Ref(T)' in formatted



def test_struct_ref_lookup_preserves_type_member_constructors():
    c = compile_custom('''
        struct Payload { value: uint(8) }
        struct Config { type Payload = Payload; }
        fn make(C: type, value: uint(8)) -> C.Payload { return C.Payload.new(value=value); }
        fn check() -> uint(8) { return make(Config, 37).value; }
        module Probe ports(input: in async uint(8), output: out async uint(8)) {
            comb { output = make(Config, input).value; }
        }
    ''')
    assert c.resolve('top.check')() == 37
    assert c.resolve('top.Probe').as_verilog().source


def test_struct_ref_interface_array_element(tmp_dir: Path):
    c = compile_custom('''
        interface Link { value: uint(8), view Source { value: out } }
        struct Endpoint {
            ref channel: Link,
            fn drive(self, value: uint(8)) { self.channel.value = value; }
        }
        module Probe ports(input: in async [2]uint(8), output: interface async [2]Link.Source) {
            comb {
                for (i in 0..2) {
                    val ep = Endpoint.new(channel=ref(output[i]));
                    ep.drive(input[i]);
                }
            }
        }
    ''')
    inst = c.resolve('top.Probe').as_verilated(tmp_dir).instance()
    inst.ports.input = [17, 231]
    inst.step(1)
    assert [p.value for p in inst.ports.output] == [17, 231]
