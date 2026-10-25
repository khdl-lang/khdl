import shutil
from pathlib import Path

import khdl

from khdl_sandbox.common.util import compile_custom


def test_verilator_creates_build_dir(tmp_dir: Path):
    build_dir = tmp_dir / "does" / "not" / "exist"
    assert not build_dir.exists()

    src = "module top ports(y: out async bool) { comb { y = true; } }"
    inst = compile_custom(src).resolve("top.top").as_verilated(build_dir).instance()
    inst.step(1)
    assert inst.ports.y is True


def test_verilator_rebuild_same_dir(tmp_dir: Path):
    src_pass = "module top ports(x: in async bool, y: out async bool) { comb { y = x; } }"""
    src_inv = "module top ports(x: in async bool, y: out async bool) { comb { y = !x; } }"""

    inst_pass = compile_custom(src_pass).resolve("top.top").as_verilated(tmp_dir).instance()
    inst_inv = compile_custom(src_inv).resolve("top.top").as_verilated(tmp_dir).instance()

    def check(inst: khdl.VerilatedInstance, x: bool, y: bool):
        inst.ports.x = x
        inst.step(1)
        assert inst.ports.y is y

    check(inst_pass, False, False)
    check(inst_pass, True, True)
    check(inst_inv, False, True)
    check(inst_inv, True, False)


def test_verilator_rebuild_with_stale_objects(tmp_dir: Path):
    src = "module top ports(x: in async bool, y: out async bool) { comb { y = x; } }"
    top: khdl.Module = compile_custom(src).resolve("top.top")
    top.as_verilated(tmp_dir)

    # simulate an object file left behind by an earlier build with different generated sources
    obj_dir = tmp_dir / "obj_dir"
    obj = next(obj_dir.glob("VTop*.o"))
    shutil.copyfile(obj, obj_dir / "obsolete.o")

    inst = top.as_verilated(tmp_dir).instance()
    inst.ports.x = True
    inst.step(1)
    assert inst.ports.y is True


def test_verilator_constant_comparison(tmp_dir: Path):
    src = "module top ports(x: in async uint(2), y: out async bool) { comb { val low = x & 3; y = low <= 3; } }"
    inst = compile_custom(src).resolve("top.top").as_verilated(tmp_dir).instance()
    for x in range(4):
        inst.ports.x = x
        inst.step(1)
        assert inst.ports.y is True
