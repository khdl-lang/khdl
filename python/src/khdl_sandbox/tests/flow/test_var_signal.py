from pathlib import Path

import khdl

from khdl_sandbox.common.util import compile_custom, diag_error


def test_read_const_from_signal(tmp_dir: Path):
    src = """
    module top ports(clk: in clock, p: out async uint(8)) {
        wire w: uint(8);
        wire r: uint(8);
        comb {
            w = 3;
            p = 4;
            const {
                assert(w == 3);
                assert(p == 4);
            }
        }
        clocked(clk) {
            reg wire r = undef;
            r = 5;
            const {
                assert(r == 5);
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_read_const_from_signal_after_step(tmp_dir: Path):
    src = """
    module top ports(clk: in clock) {
        wire w: [2]uint(8);
        comb {
            w = [3, 4];
            w[0] = 5;
            const {
                assert(w[0] == 5);
                assert(w[1] == 4);
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_read_range_from_signal(tmp_dir: Path):
    src = """
    module top ports(p: out async uint(8), q: in async uint(4)) {
        comb {
            p = q;
            val _: uint(4) = p;
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


# TODO test that signals are immediately read back instead of only the next cycle
# def test_signal_readback(tmp_dir: Path):
#     src = """
#     module top ports(clk: in clock, x: in sync(clk) uint(8), y: out sync(clk) uint(8)) {
#         reg out y = undef;
#         clocked(clk) {
#             y = x;
#             y = 255 - y;
#         }
#     }
#     """
#     c = compile_custom(src)
#     foo: khdl.Module = c.resolve("top.top")
#     print(foo.as_verilog())
#     foo_inst = foo.as_verilated(tmp_dir).instance()
#
#     ports = foo_inst.ports
#
#     def cycle():
#         foo_inst.step(1)
#         ports.clk = 1
#         foo_inst.step(1)
#         ports.clk = 0
#
#     ports.clk = 0
#     ports.x = 0
#     cycle()
#     assert ports.y == 255


def test_write_after_read_var(tmp_dir: Path):
    src = """
    module top ports(x: in async uint(8), y: out async uint(16)) {
        comb {
            var v = x;
            val w = v + {
                v = 0;
                1
            };
            y = w;
        }
    }
    """
    check_write_after_read(tmp_dir, src)


def test_write_after_read_var_array(tmp_dir: Path):
    src = """
    module top ports(x: in async uint(8), y: out async uint(16)) {
        comb {
            var v: [1]uint(8) = [x];
            val w = v[0] + {
                v[0] = 0;
                1
            };
            y = w;
        }
    }
    """
    check_write_after_read(tmp_dir, src)


def test_write_after_read_wire(tmp_dir: Path):
    src = """
    module top ports(x: in async uint(8), y: out async uint(16)) {
        wire w: uint(8);
        comb {
            w = x;
            val v = w + {
                w = 0;
                1
            };
            y = v;
        }
    }
    """
    check_write_after_read(tmp_dir, src)


def test_write_after_read_wire_array(tmp_dir: Path):
    src = """
    module top ports(x: in async uint(8), y: out async uint(16)) {
        wire w: [1]uint(8);
        comb {
            w[0] = x;
            val v = w[0] + {
                w[0] = 0;
                1
            };
            y = v;
        }
    }
    """
    check_write_after_read(tmp_dir, src)


def check_write_after_read(tmp_dir: Path, src: str):
    c = compile_custom(src)
    foo: khdl.Module = c.resolve("top.top")
    print(foo.as_verilog().source)
    foo_inst = foo.as_verilated(tmp_dir).instance()

    foo_inst.ports.x = 4
    foo_inst.step(1)
    assert foo_inst.ports.y == 5


def test_const_assign_outside_var():
    src = """
    module top ports(c: in async bool) {
        comb {
            var v = c;
            const {
                v = true;
            }
            const {
                assert(v);
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_var_type_enforced_scalar():
    src_a = """
    module top ports(c: in async bool) {
        comb {
            var v: bool = false;
            v = true;
        }
    }
    """
    _ = compile_custom(src_a).resolve("top.top")

    src_c = """
    module top ports(c: in async bool) {
        comb {
            var v = false;
            v = 5;
        }
    }
    """
    _ = compile_custom(src_c).resolve("top.top")

    src_b = """
    module top ports(c: in async bool) {
        comb {
            var v: bool = false;
            v = 5;
        }
    }
    """
    with diag_error("type mismatch"):
        _ = compile_custom(src_b).resolve("top.top")


def test_var_type_enforced_array():
    src_a = """
    module top ports(c: in async bool) {
        comb {
            var v: [2]bool = [false, true];
            v[0] = true;
        }
    }
    """
    _ = compile_custom(src_a).resolve("top.top")

    src_c = """
    module top ports(c: in async bool) {
        comb {
            var v = [false, true];
            v[0] = 5;
        }
    }
    """
    _ = compile_custom(src_c).resolve("top.top")

    src_b = """
    module top ports(c: in async bool) {
        comb {
            var v: [2]bool = [false, true];
            v[0] = 5;
        }
    }
    """
    with diag_error("type mismatch"):
        _ = compile_custom(src_b).resolve("top.top")


def test_wire_infer_type():
    src = """
    module top ports() {
        wire w;
        comb {
            w = false;
        }
    }
    """
    _ = compile_custom(src).resolve("top.top")


def test_assign_immutable():
    src_a = """
    module top ports() {
        comb {
            val w;
            w = false;
        }
    }
    """
    _ = compile_custom(src_a).resolve("top.top")

    src_b = """
        module top ports() {
            comb {
                val w;
                w = false;
                w = true;
            }
        }
        """
    with diag_error("cannot assign to immutable variable"):
        _ = compile_custom(src_b).resolve("top.top")


def test_read_const_from_signal_with_steps_in_hw():
    src = """
    module top ports(clk: in clock) {
        wire w: [2]uint(8);
        comb {
            w = [3, 4];
            val a = w[1];
            const {
                assert(a == 4);
            }
        }
    }
    """
    c = compile_custom(src)
    _ = c.resolve("top.top")


def test_read_implied_bool_from_signal_with_steps():
    src = """
    module top ports(p: in async bool) {
        comb {
            if (p) {
                val _ = p[0];
            }
        }
    }
    """
    with diag_error("cannot index non-array type"):
        _ = compile_custom(src).resolve("top.top")


def test_read_const_from_signal_parent_of_branch():
    src = """
    module top ports(c: in async bool, y: out async uint(8)) {
        comb {
            y = 3;
            if (c) { const { assert(y == 3); } }
        }
    }
    """
    compile_custom(src).resolve("top.top")


def test_read_const_from_signal_index_error():
    src = """
    module top ports(y: out async [2]uint(8)) {
        comb {
            y = [1, 2];
            const { val _ = y[5]; }
        }
    }
    """
    with diag_error("array index out of bounds"):
        compile_custom(src).resolve("top.top")


def test_type_of_signal_const():
    src = """
    module top ports(y: out async uint(8)) {
        comb {
            y = 3;
            const { print(type(y)); }
        }
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        c.resolve("top.top")
    assert cap.prints == ["int(3..4)\n"]


def test_type_of_var():
    src = """
    fn f() -> int {
        val a = 3;
        val t = (1, false);
        print(type(a));
        print(type(t));
        return 0;
    }
    """
    c = compile_custom(src)
    with c.capture_prints() as cap:
        c.resolve("top.f")()
    assert cap.prints == ["int(3..4)\n", "Tuple(int(1..2), bool)\n"]


def test_var_not_yet_assigned_eval():
    src = "fn f() -> int { val a; return a; }"
    f = compile_custom(src).resolve("top.f")
    with diag_error("variable has not yet been assigned a value", has_info="variable declared here"):
        f()


def test_var_not_yet_assigned_type_of():
    src = "fn f() -> int { val a; print(type(a)); return 0; }"
    f = compile_custom(src).resolve("top.f")
    with diag_error("variable has not yet been assigned a value", has_info="variable declared here"):
        f()
