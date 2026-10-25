from pathlib import Path

import khdl

from khdl_sandbox.common.util import compile_custom, diag_error


def test_port_reg_name(tmpdir: Path):
    src = """
    module foo ports(clk: in clock, a: out sync(clk) bool) {
        clocked(clk) {
            reg wire a = undef;
            a = !a;
        }
    }
    """

    c = compile_custom(src)
    m: khdl.Module = c.resolve("top.foo")
    m.as_verilated(tmpdir)


def test_module_instance_simple(tmp_dir: Path):
    src = """
    module parent ports(x: in async bool, y: out async bool) { instance child ports(x, y); }
    module child ports(x: in async bool, y: out async bool) { comb { y = x; } }
    """

    c = compile_custom(src)
    parent: khdl.Module = c.resolve("top.parent")
    print(parent.as_verilog().source)
    parent_verilated: khdl.ModuleVerilated = parent.as_verilated(tmp_dir)
    parent_inst: khdl.VerilatedInstance = parent_verilated.instance()

    for v in [False, True, False, True]:
        parent_inst.ports.x = v
        parent_inst.step(1)
        assert parent_inst.ports.y == v


def test_module_instance_generic(tmp_dir: Path):
    src = """
    module parent ports(x: in async uint(4), y: out async uint(4)) { instance child(N=4) ports(x, y); }
    module child(N: uint) ports(x: in async uint(N), y: out async uint(N)) { comb { y = x; } }
    """

    c = compile_custom(src)
    parent: khdl.Module = c.resolve("top.parent")
    print(parent.as_verilog().source)
    parent_verilated: khdl.ModuleVerilated = parent.as_verilated(tmp_dir)
    parent_inst: khdl.VerilatedInstance = parent_verilated.instance()

    for v in range(2 ** 4):
        parent_inst.ports.x = v
        parent_inst.step(1)
        assert parent_inst.ports.y == v


def test_wire_driven_by_child(tmp_dir: Path):
    src = """
    module parent ports(y: out const bool) {
        wire w: bool;
        instance child ports(y=w);
        comb { y = w; }
    }
    module child ports(y: out const bool) { comb { y = true; } }
    """

    c = compile_custom(src)
    parent: khdl.Module = c.resolve("top.parent")
    print(parent.as_verilog().source)
    parent_verilated: khdl.ModuleVerilated = parent.as_verilated(tmp_dir)
    parent_inst: khdl.VerilatedInstance = parent_verilated.instance()

    parent_inst.step(1)
    assert parent_inst.ports.y is True


def test_instantiate_external_module(tmp_dir: Path):
    src = """
    external module external_module(W: uint) ports(x: in async uint(W), y: out async uint(W+1))
    module top ports(x: in async uint(4), y: out async uint(5)) {
        instance external_module(W=4) ports(x, y);
    }
    """
    c = compile_custom(src)
    top: khdl.Module = c.resolve("top.top")
    print(top.as_verilog().source)

    extra_verilog_files = [Path(__file__).parent / "external.v"]
    top_verilated: khdl.ModuleVerilated = top.as_verilated(tmp_dir, extra_verilog_files=extra_verilog_files)
    top_inst: khdl.VerilatedInstance = top_verilated.instance()

    for v in [0, 1, 2, 15]:
        top_inst.ports.x = v
        top_inst.step(1)
        assert top_inst.ports.y == v + 1


def test_instantiate_zero_width_ports(tmp_dir: Path):
    src = """
    module top ports(
        x: in async uint(0),
        y0: out async uint(0),
        y1: out async uint(0),
    ) {
        instance internal_module ports(x, y0=y0, y1=_);
        instance external_module_no_ports ports(x, y0=y1, y1=_);
    }

    module internal_module ports(
        x: in async uint(0),
        y0: out async uint(0),
        y1: out async uint(0),
    ) {
        comb {
            y0 = x;
            y1 = x;
        }
    }
    external module external_module_no_ports ports(
        x: in async uint(0),
        y0: out async uint(0),
        y1: out async uint(0),
    )
    
    """
    c = compile_custom(src)
    top: khdl.Module = c.resolve("top.top")
    print(top.as_verilog().source)

    extra_verilog_files = [Path(__file__).parent / "external.v"]
    top_verilated: khdl.ModuleVerilated = top.as_verilated(tmp_dir, extra_verilog_files=extra_verilog_files)
    top_inst: khdl.VerilatedInstance = top_verilated.instance()

    top_inst.ports.x = 0
    top_inst.step(1)
    assert top_inst.ports.y0 == 0
    assert top_inst.ports.y1 == 0


def test_instantiate_external_module_no_ports(tmp_dir: Path):
    src = """
    external module external_module_no_ports ports()
    module top ports() {
        instance external_module_no_ports ports();
    }
    """
    c = compile_custom(src)
    top: khdl.Module = c.resolve("top.top")
    print(top.as_verilog().source)

    extra_verilog_files = [Path(__file__).parent / "external.v"]
    top_verilated: khdl.ModuleVerilated = top.as_verilated(tmp_dir, extra_verilog_files=extra_verilog_files)
    top_inst: khdl.VerilatedInstance = top_verilated.instance()

    top_inst.step(1)


def test_cyclic_instantiation_almost():
    src = """
    module foo(n: uint) ports(x: in async bool, y: out async bool) {
        if (n == 0) {
            comb { y = x; }
        } else {
            instance foo(n-1) ports(x, y);
        }
    }
    """
    c = compile_custom(src)
    foo: khdl.Module = c.resolve("top.foo")(4)
    print(foo.as_verilog().source)


def test_cyclic_instantiation_real():
    src = """
    module foo ports(x: in async bool, y: out async bool) { instance bar ports(x, y); }
    module bar ports(x: in async bool, y: out async bool) { instance foo ports(x, y); }
    """
    c = compile_custom(src)

    with diag_error("cyclic module instantiation"):
        foo: khdl.Module = c.resolve("top.foo")
        print(foo.as_verilog().source)


def test_undef_expression():
    src = """
    module top ports() {
        wire w: bool = undef;
        comb {
            val v: uint(8) = undef;
        }
    }
    """
    compile_custom(src).resolve("top.top")


def test_reference_escape_simple():
    src = """ 
    module top ports() {
        wire w: bool;
        instance child(ref(w)) ports();
    }
    module child(a: any) ports() {}
    """
    with diag_error("item parameters cannot contain references"):
        compile_custom(src).resolve("top.top")


def test_item_param_hardware_ref():
    src = """
    struct S(b: any) {}
    module top_basic ports(x: in async bool) {
        comb { val s = S(x); }
    }
    module top_ref ports(x: in async bool) {
        comb { val s = S(ref(x)); }
    }
    """
    with diag_error("item parameters must be compile-time"):
        compile_custom(src).resolve("top.top_basic")
    with diag_error("item parameters cannot contain references"):
        compile_custom(src).resolve("top.top_ref")


def test_reference_escape_function():
    src = """
    module top ports() {
        wire w: bool = true;
        const r = ref(w);
        fn f() {
            deref(r).x = false;
        }
        instance child(f) ports();
    }
    module child(f: Function) ports() {
        comb { f(); }
    }
    """
    with diag_error("attempt to use signal reference outside its declaring module"):
        compile_custom(src).resolve("top.top")


def test_diamond_instantiation_0(tmp_dir: Path):
    src = """
    module a ports() { instance b ports(); instance c ports(); }
    module b ports() { instance c ports(); }
    module c ports() {}
    """
    m = compile_custom(src).resolve("top.a")
    print(m.as_verilog().source)
    _ = m.as_verilated(tmp_dir).instance()


def test_diamond_instantiation_1(tmp_dir: Path):
    src = """
    module a ports() { }
    module b ports() { instance a ports(); }
    module c ports() { instance a ports(); instance b ports(); }
    """
    m = compile_custom(src).resolve("top.c")
    print(m.as_verilog().source)
    _ = m.as_verilated(tmp_dir).instance()


def test_self_instance():
    src = """
    module top ports() {
        instance top ports();
    }
    """
    c = compile_custom(src)
    with diag_error("cyclic module instantiation"):
        c.resolve("top.top")


def test_module_inner_decls_can_access_outer():
    # Test that declarations inside the module can access values in parameters and even hardware signals.
    # This requires that flow/scope/capture handling is implemented at least somewhat correctly.

    src = """
    module foo(N: uint) ports() {
        wire w: bool = false;
    
        type array(T: type) = [N]T;
        type foo = type(w);
        
        wire w1: array(bool) = [false] * N;
        wire w2: foo = false;
    }
    """
    foo = compile_custom(src).resolve("top.foo")
    print(foo(N=4).as_verilog().source)


def test_input_port_no_process():
    # Check that just connecting ports through does not create additional processes (and delta cycles!)
    src = """
    module top ports(x: in async uint(8), y: out async uint(8)) {
        instance child ports(x, y);
    }
    module child ports(x: in async uint(8), y: out async uint(8)) {
        comb {
            y = x;
        }
    }
    """
    top = compile_custom(src).resolve("top.top")
    verilog: str = top.as_verilog().source
    print(verilog)

    # we expect exactly one process, in child, no additional process in top
    assert verilog.count("always @(") == 1


def test_module_instance_expand_port_simple(tmp_dir: Path):
    # test that port type expansion works correctly
    src = """
    module parent ports(x: in async uint(2), y: out async uint(5)) {
        instance child ports(x, y);
    }
    module child ports(x: in async uint(3), y: out async uint(4)) {
        comb { y = x; }
    }
    """

    top = compile_custom(src).resolve_module("top.parent")
    print(top.as_verilog().source)
    inst = top.as_verilated(tmp_dir).instance()

    for v in range(2 ** 2):
        inst.ports.x = v
        inst.step(1)
        assert inst.ports.y == v


def test_module_instance_expand_port_tuple(tmp_dir: Path):
    # test that port type expansion works correctly
    src = """
    module parent ports(x: in async Tuple(uint(2), bool), y: out async Tuple(uint(5), bool)) {
        instance child ports(x, y);
    }
    module child ports(x: in async Tuple(uint(3), bool), y: out async Tuple(uint(4), bool)) {
        comb { y = x; }
    }
    """

    top = compile_custom(src).resolve_module("top.parent")
    print(top.as_verilog().source)
    inst = top.as_verilated(tmp_dir).instance()

    for v_i in range(2 ** 2):
        for v_b in [False, True]:
            v = (v_i, v_b)
            inst.ports.x = v
            inst.step(1)
            assert inst.ports.y == v


def test_module_duplicate_port_name_simple():
    src = """
    module top ports(x: in async bool, x: in async bool) {}
    """

    with diag_error("identifier `x` declared multiple times"):
        _ = compile_custom(src).resolve("top.top")


def test_module_duplicate_port_name_interface():
    src = """
    interface foo { d: uint(4), view input { d: in } view output { d: out } }
    module top ports(y: interface async foo.input, y: interface async foo.output) {}
    """

    with diag_error("identifier `y` declared multiple times"):
        compile_custom(src).resolve("top.top")


def test_module_duplicate_port_name_instantiate():
    # this caused an internal compiler error at some point,
    #   the failed module header elaboration did not stop the instantiation from happening
    src = """
    interface foo { d: uint(4), view input { d: in } view output { d: out } }
    module top ports() {
        wire v: interface foo;
        wire w: interface foo;
        instance pass ports(x=v, y=w);
    }
    module pass ports(y: interface async foo.input, y: interface async foo.output) {
        comb { y.d = y.d; }
    }
    """

    with diag_error("identifier `y` declared multiple times"):
        compile_custom(src).resolve("top.top")


def test_module_instance_output_wrong_type(tmp_dir: Path):
    src = """
    module top ports(y: out async bool) {
        instance child ports(y=y);
    }
    module child ports(y: out async uint(4)) {
        comb { y = 0; }
    }
    """

    with diag_error("type mismatch"):
        compile_custom(src).resolve("top.top")


def test_module_instance_output_step(tmp_dir: Path):
    src = """
    module top ports(x: in async [2]bool, y: out async [2]bool) {
        instance child ports(x=x[0], y=y[0]);
        instance child ports(x=x[1], y=y[1]);
    }
    module child ports(x: in async bool, y: out async bool) {
        comb { y = x; }
    }
    """

    top = compile_custom(src).resolve_module("top.top")
    inst = top.as_verilated(tmp_dir).instance()

    for a in [False, True]:
        for b in [False, True]:
            pair = [a, b]
            inst.ports.x = pair
            inst.step(1)
            assert inst.ports.y == pair


def test_module_instance_output_deref(tmp_dir: Path):
    src = """
    module top ports(x: in async bool, y: out async bool) {
        const r = ref(y);
        instance child ports(x=x, y=deref(r));
    }
    module child ports(x: in async bool, y: out async bool) {
        comb { y = x; }
    }
    """
    top = compile_custom(src).resolve_module("top.top")
    inst = top.as_verilated(tmp_dir).instance()

    for v in [False, True]:
        inst.ports.x = v
        inst.step(1)
        assert inst.ports.y == v


def test_module_instance_output_step_dyn(tmp_dir: Path):
    src = """
    module top ports(x: in async [2]bool, y: out async [2]bool, i: in async int(0..2)) {
        instance child ports(x=x[0], y=y[i]);
    }
    module child ports(x: in async bool, y: out async bool) {
        comb { y = x; }
    }
    """
    with diag_error("signal evaluation is only allowed in a hardware context"):
        _ = compile_custom(src).resolve_module("top.top")


def test_module_instance_output_cursed_var(tmp_dir: Path):
    # this does not really test much, just that variables are certainly not accepted
    src = """
    module top ports(x: in async bool) {
        instance child ports(x=x, y=deref({ var v; ref(v) }));
    }
    module child ports(x: in async bool, y: out async bool) {
        comb { y = x; }
    }
    """
    with diag_error("cannot access variable after its scope has ended"):
        _ = compile_custom(src).resolve_module("top.top")
