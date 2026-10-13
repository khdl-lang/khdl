"""Limited mutable receivers alias whole caller variables, never hidden copies."""
from pathlib import Path

import khdl
import pytest

from khdl_sandbox.common.compare import compare_body
from khdl_sandbox.common.util import compile_custom

COUNTER = '''
struct Counter {
    value: uint(8),
    fn read(self) -> uint(8) { return self.value; }
    fn add(ref self, amount: uint(8)) {
        self.value = (self.value + amount) & 255;
    }
    fn twice(ref self) { self.add(1); self.add(1); }
    fn increment(ref self) { self.add(1); }
}
'''


@pytest.mark.parametrize('annotation', ['', ': Counter', ': any'])
def test_ref_self_inferred_declared_and_any(annotation):
    c = compile_custom(COUNTER + '''
        fn check() -> uint(8) {
            var obj ANNOTATION = Counter.new(value=3);
            obj.add(2);
            obj.twice();
            return obj.read();
        }
    '''.replace('ANNOTATION', annotation))
    assert c.resolve('top.check')() == 7


def test_ref_self_forwarding_aliases_and_copies():
    c = compile_custom(COUNTER + '''
        struct Holder { ref target: Counter }
        fn forward(input: any) { deref(input).twice(); }
        fn check() -> uint(8) {
            var obj: Counter = Counter.new(value=4);
            val alias = ref(obj);
            forward(alias);
            val holder = Holder.new(target=alias);
            holder.target.increment();
            var copy = obj;
            copy.add(100);
            assert(copy.value == 107);
            assert(obj.value == 7);
            return deref(alias).read();
        }
    ''')
    assert c.resolve('top.check')() == 7


def test_ref_self_stored_method_and_argument_evaluation_order():
    c = compile_custom(COUNTER + '''
        fn change(r: Ref(Counter)) -> uint(8) {
            deref(r).value = 100;
            return 3;
        }
        fn make(count: Ref(uint(8))) -> Counter {
            deref(count) = deref(count) + 1;
            return Counter.new(value=6);
        }
        fn check() -> uint(8) {
            var obj: Counter = Counter.new(value=2);
            val read_snapshot = obj.read;
            val update = obj.increment;
            obj.value = 8;
            update();
            assert(obj.value == 9 && read_snapshot() == 2);
            obj.add(change(ref(obj)));
            assert(obj.value == 103);
            var count: uint(8) = 0;
            assert(make(ref(count)).read() == 6);
            assert(count == 1);
            return obj.value;
        }
    ''')
    assert c.resolve('top.check')() == 103


def test_ref_self_nested_function_capture_and_reference_return():
    c = compile_custom(COUNTER + '''
        struct Cell {
            value: uint(8),
            fn nested(ref self) {
                fn inner() { self.value = 9; }
                inner();
            }
            fn reference(ref self) -> Ref(Cell) { return ref(self); }
        }
        fn check() -> uint(8) {
            var obj: Cell = Cell.new(value=1);
            obj.nested();
            val r = obj.reference();
            deref(r).value = 10;
            return obj.value;
        }
    ''')
    assert c.resolve('top.check')() == 10


def test_ref_self_array_scratch(tmp_dir: Path):
    comparison = compare_body(
        ['uint(8)', 'uint(0..3)'], 'Tuple(uint(8), [3]uint(8))',
        '''
        var obj = State.new(storage=a0, scratch=[0, 0, 0], active=false);
        obj.begin();
        obj.update(a1, a0);
        obj.end();
        return (obj.storage, obj.scratch);
        ''', tmp_dir, prefix='''
        struct State {
            storage: uint(8), scratch: [3]uint(8), active: bool,
            fn begin(ref self) { self.active = true; }
            fn update(ref self, index: uint(0..3), value: uint(8)) {
                assert(self.active);
                self.scratch[index] = value;
                self.storage = value ^ 255;
            }
            fn end(ref self) { self.active = false; }
        }
        ''',
    )
    for value in [0, 1, 127, 255]:
        for index in range(3):
            scratch = [0, 0, 0]
            scratch[index] = value
            comparison.eval_assert([value, index], (value ^ 255, scratch))


@pytest.mark.parametrize('body,expected', [
    ('val obj = Counter.new(value=1); obj.increment();', 'receiver must be mutable'),
    ('Counter.new(value=1).increment();', 'mutable whole variable'),
    ('''fn make() -> Counter { print("receiver"); return Counter.new(value=1); }
        make().increment();''', 'mutable whole variable'),
    ('var list = [Counter.new(value=1)]; list[0].increment();', 'target steps'),
    ('struct Outer { inner: Counter } var outer = Outer.new(inner=Counter.new(value=1)); outer.inner.increment();', 'target steps'),
    ('''fn get() -> any { var obj = Counter.new(value=1); return obj.increment; }
        val update = get(); update();''', 'scope has ended'),
    ('''struct Other { value: uint(8) }
        var obj = Counter.new(value=1); val update = obj.increment;
        obj = Other.new(value=2); update();''', 'receiver type changed'),
    ('var obj = Counter.new(value=1); val read = obj.read; val _ = deref(read);', 'non-reference'),
])
def test_ref_self_invalid_receiver(body, expected):
    c = compile_custom(COUNTER + '\nfn check() { ' + body + ' }')
    with c.capture_prints() as prints:
        with pytest.raises(khdl.DiagnosticException) as exc:
            c.resolve('top.check')()
    assert expected in exc.value.combined_string
    assert 'internal compiler error' not in exc.value.combined_string
    if 'print("receiver")' in body:
        assert prints.prints == ['receiver\n']


@pytest.mark.parametrize('body,expected', [
    ('''module Probe ports(input: in async Counter) {
        comb { input.increment(); }
    }''', 'signal and port receivers'),
    ('''module Probe ports(index: in async uint(0..2)) {
        comb { var a = [Counter.new(value=1), Counter.new(value=2)]; a[index].increment(); }
    }''', 'target steps'),
    ('''fn make() -> any { var obj = Counter.new(value=1); return obj.increment; }
        module Child(update: any) ports() {}
        module Probe ports() { const update = make(); instance Child(update) ports(); }
    ''', 'item parameters cannot contain references'),
])
def test_ref_self_invalid_hardware(body, expected):
    with pytest.raises(khdl.DiagnosticException) as exc:
        compile_custom(COUNTER + body).resolve('top.Probe')
    assert expected in exc.value.combined_string
    assert 'internal compiler error' not in exc.value.combined_string


def test_ref_self_rejects_enum_methods():
    with pytest.raises(khdl.DiagnosticException) as exc:
        compile_custom('enum Choice { A, fn update(ref self) {} }').resolve('top.Choice')
    assert 'only supported on struct methods' in exc.value.combined_string


def test_ref_self_python_value_inspection_rejects_missing_target():
    c = compile_custom(COUNTER + 'const obj = Counter.new(value=1);')
    obj = c.resolve('top.obj')
    with pytest.raises((AttributeError, khdl.DiagnosticException)):
        _ = obj.increment


def test_ref_self_formatter():
    text = 'struct S(T:type) { fn foo(ref /* receiver */ self, x:T) { self.x=x; } }'
    formatted = khdl.format_file(text)
    assert 'ref /* receiver */ self' in formatted
    assert khdl.format_file(formatted) == formatted


def test_ref_self_mixed_reference_and_compile_time_scratch(tmp_dir: Path):
    comparison = compare_body(
        ['uint(8)'], 'uint(8)',
        '''var stored: uint(8) = a0;
        var obj = State.new(storage=ref(stored), active=false);
        obj.begin(); obj.update(a0); obj.end();
        assert(!obj.active);
        return stored;''', tmp_dir, prefix='''
        struct State {
            ref storage: uint(8), active: bool,
            fn begin(ref self) { self.active = true; }
            fn update(ref self, value: uint(8)) {
                assert(self.active); self.storage = value ^ 255;
            }
            fn end(ref self) { self.active = false; }
        }''',
    )
    for value in [0, 1, 127, 255]:
        comparison.eval_assert([value], value ^ 255)


@pytest.mark.parametrize('ports,method,expected', [
    ('target: in async uint(8)', 'self.target = 1;', 'input port'),
    ('clk: in clock, other: in clock, target: in sync(other) uint(8)',
     'val _ = self.target;', 'domain'),
])
def test_ref_self_preserves_external_target_checks(ports, method, expected):
    process = 'clocked(clk)' if expected == 'domain' else 'comb'
    with pytest.raises(khdl.DiagnosticException) as exc:
        compile_custom('''
            struct Endpoint {
                ref target: uint(8),
                fn apply(ref self) { METHOD }
            }
            module Probe ports(PORTS) {
                PROCESS { var obj = Endpoint.new(target=ref(target)); obj.apply(); }
            }
        '''.replace('METHOD', method).replace('PORTS', ports).replace('PROCESS', process)).resolve('top.Probe')
    assert expected in exc.value.combined_string
    assert 'internal compiler error' not in exc.value.combined_string


def test_ref_self_captured_nested_function_cannot_outlive_target():
    c = compile_custom('''
        struct Cell {
            value: uint(8),
            fn capture(ref self) -> any {
                fn later() { self.value = 5; }
                return later;
            }
        }
        fn escape() -> any { var obj = Cell.new(value=1); return obj.capture(); }
        fn check() { val later = escape(); later(); }
    ''')
    with pytest.raises(khdl.DiagnosticException) as exc:
        c.resolve('top.check')()
    assert 'scope has ended' in exc.value.combined_string


def test_ref_self_hardware_early_return_preserves_caller_updates(tmp_dir: Path):
    comparison = compare_body(
        ['bool'], 'Tuple(uint(8), uint(8))',
        '''var obj = Choice.new(value=0);
        val result = obj.update(a0);
        return (obj.value, result);''', tmp_dir, prefix='''
        struct Choice {
            value: uint(8),
            fn update(ref self, early: bool) -> uint(8) {
                self.value = 1;
                if (early) { self.value = 2; return 7; }
                self.value = 3;
                return 9;
            }
        }
        ''',
    )
    comparison.eval_assert([False], (3, 9))
    comparison.eval_assert([True], (2, 7))
