from pathlib import Path

import khdl
import pytest

from khdl_sandbox.common.util import compile_custom, diag_error


def test_module_name_set():
    """Check that all items defined in the package have the correct module set"""
    wrong = {}
    for name, item in vars(khdl).items():
        if name.startswith("__") or name == "khdl":
            continue
        module = getattr(item, "__module__", None)
        if module != "khdl":
            wrong[name] = module
    assert wrong == {}


def test_interact_add():
    c = compile_custom("fn f(a: int, b: int) -> int { return a + b; }")
    f = c.resolve("top.f")
    assert f(3, 4) == 7


def test_interact_string_array():
    c = compile_custom("fn f(a: [3]str, b: int) -> str { return a[b]; }")
    f = c.resolve("top.f")
    assert f(["a", "b", "c"], 1) == "b"


def test_interact_types():
    c = compile_custom("fn f(T: type, x: T) -> T { return x; }")
    f = c.resolve("top.f")

    assert f(bool, False) is False
    assert f(bool, True) is True
    with diag_error("type mismatch"):
        f(bool, 0)

    assert f(int, 0) == 0
    with diag_error("type mismatch"):
        f(int, False)


def test_reject_cross_compile_values():
    c0 = compile_custom("struct Foo {}")
    t = c0.resolve("top.Foo")
    c1 = compile_custom("fn f(T: type) -> uint { return T.size_bits; }")
    f = c1.resolve("top.f")

    with pytest.raises(ValueError, match="cannot mix values from different Compile instances"):
        f(t)


def test_compile_manifest():
    manifest_path = Path(__file__).parent / "project/khdl.toml"
    s = khdl.Source.new_from_manifest_path(str(manifest_path))
    c = s.compile()

    assert isinstance(c.resolve("top.top"), khdl.Module)
    assert c.resolve("top.data") == [1, 2, 3]


def test_format():
    src = "const c = a+b;"
    expected = "const c = a + b;\n"
    assert khdl.format_file(src) == expected


def test_capture_prints():
    src = """
    fn f(a: int) -> int {
        print("hello");
        print("world");
        return a + 1;
    }
    """
    c = compile_custom(src)
    f = c.resolve("top.f")

    with c.capture_prints() as capture:
        result = f(5)

    assert result == 6
    assert capture.prints == ["hello\n", "world\n"]


def test_call_type():
    c = compile_custom("")
    uint = c.resolve("std.types.uint")
    assert str(uint) == "uint"
    assert str(uint(8)) == "int(0..256)"


def test_interact_struct(tmp_dir: Path):
    src = """
    struct Pair { x: uint(8), y: bool }
    fn f(x: uint(8), y: bool) -> Pair {
        return Pair.new(x=x, y=y);
    }
    """

    c = compile_custom(src)
    pair = c.resolve("top.Pair")
    f = c.resolve("top.f")

    # check struct construction, indirectly and directly
    assert str(f(4, False)) == "Pair.new(x=4, y=false)"
    assert str(pair.new(x=4, y=False)) == "Pair.new(x=4, y=false)"

    # check struct equality
    a0 = f(4, False)
    a1 = f(4, False)
    b = f(5, False)
    assert a0 == a0
    assert a0 == a1
    assert not (a0 == b)
    assert not (a0 != a1)
    assert a0 != b

    # check comparing values python values works as expected
    assert not (a0 == "test")
    assert a0 != "test"

    # check field access
    assert isinstance(a0, khdl.StructValue)
    assert a0.x == 4
    assert a0.y is False
    assert a0.fields == {"x": 4, "y": False}

    # check that we get normal python behavior for non-existing attributes
    with pytest.raises(AttributeError):
        _ = f(4, False).non_existing


def test_interact_enum():
    src = """
    enum Foo { Empty, Data(uint(8)) }
    fn f(x: bool, y: uint(8)) -> Foo {
        if (x) {
            return Foo.Data(y);
        } else {
            return Foo.Empty;
        }
    }
    """

    c = compile_custom(src)
    foo = c.resolve("top.Foo")
    f = c.resolve("top.f")

    # check enum construction, indirectly and directly
    assert str(f(False, 0)) == "Foo.Empty"
    assert str(f(True, 0)) == "Foo.Data(0)"
    assert str(f(True, 1)) == "Foo.Data(1)"

    assert str(foo.Empty) == "Foo.Empty"
    assert str(foo.Data(0)) == "Foo.Data(0)"
    assert str(foo.Data(1)) == "Foo.Data(1)"

    # check tag and payload access
    assert isinstance(foo.Empty, khdl.EnumValue)
    assert foo.Empty.tag == "Empty"
    assert foo.Empty.payload is None
    assert f(True, 3).tag == "Data"
    assert f(True, 3).payload == 3


def _verilated_port_test_module(tmp_dir: Path) -> khdl.VerilatedInstance:
    src = """
    module top ports(
        x: in async bool,
        y: out async bool,
        n: in async uint(4),
    ) {
        comb { y = x; }
    }
    """
    top: khdl.Module = compile_custom(src).resolve("top.top")
    return top.as_verilated(tmp_dir).instance()


def test_port_interaction_errors(tmp_dir: Path):
    inst = _verilated_port_test_module(tmp_dir)

    # port info cannot be assigned
    with pytest.raises(ValueError, match=r"cannot set port info `info_ports\.x`, set port values through `ports`"):
        inst.info_ports.x = True
    with pytest.raises(ValueError, match=r'cannot set port info `info_ports\["x"\]`'):
        inst.info_ports["x"] = True
    with pytest.raises(ValueError, match=r"cannot set port info `info_ports_flat\.x`"):
        inst.info_ports_flat.x = True

    # accessing a port that does not exist is a plain attribute error
    with pytest.raises(AttributeError, match="port `missing` not found"):
        _ = inst.ports.missing
    with pytest.raises(AttributeError, match="port `missing` not found"):
        _ = inst.ports["missing"]
    with pytest.raises(AttributeError, match="port `missing` not found"):
        inst.ports.missing = True
    with pytest.raises(AttributeError, match="port `missing` not found"):
        _ = inst.info_ports.missing

    # port info is not a bool, mixing up `info_ports` and `ports` should be caught
    with pytest.raises(ValueError, match="cannot be used as a boolean"):
        bool(inst.info_ports.x)
    with pytest.raises(ValueError, match="cannot be used as a boolean"):
        if inst.info_ports.x:
            pass

    # setting a value of the wrong type is reported as a normal compiler diagnostic
    with diag_error("type mismatch"):
        inst.ports.x = "hello"
    with diag_error("type mismatch"):
        inst.ports.n = 999

    # output ports cannot be driven from the python side
    with pytest.raises(khdl.VerilationException, match="Cannot set output port"):
        inst.ports.y = True

    # the correct way to set and read a port works
    inst.ports.x = True
    inst.step(1)
    assert inst.ports.y is True
    assert inst.ports["y"] is True


def test_port_interaction_structured(tmp_dir: Path):
    src = """
    interface Foo { 
        a: uint(8),
        b: bool,
        view In { a: in, b: in }
        view Out { a: out, b: out }
    }
    module top ports(
        async {
            s: in uint(8),
            x: interface [3]Foo.In,
            y: interface [2][3]Foo.Out,
            t: out uint(8),
        }
    ) {
        comb {
            t = s;
            for (i in 0..2) {
                for (j in 0..3) {
                    y[i][j].a = x[j].a;
                    y[i][j].b = x[j].b;
                }
            }
        }
    }
    """
    inst = compile_custom(src).resolve("top.top").as_verilated(tmp_dir).instance()
    ports = inst.ports
    info = inst.info_ports

    # structure and naming
    assert list(ports) == list(info) == ["s", "x", "y", "t"]
    assert isinstance(ports.x[0], khdl.VerilatedInterface)
    assert isinstance(ports.y, khdl.VerilatedInterfaceArray)
    assert isinstance(info.x[0], khdl.VerilatedInfoInterface)
    assert isinstance(info.y, khdl.VerilatedInfoInterfaceArray)
    assert isinstance(info.s, khdl.VerilatedInfoPort)
    assert list(ports.x[0]) == list(info.x[0]) == ["a", "b"]
    assert len(info.y) == 2
    assert len(info.y[0]) == 3
    assert info["y"][-1][-1].a.name == "y_1_2_a"
    assert list(inst.info_ports_flat)[:3] == ["s", "x_0_a", "x_0_b"]
    assert ports.y.shape == info.y.shape == (2, 3)
    assert info.y[1:].shape == (1, 3)
    assert info.y[0].shape == (3,)

    # slicing
    assert [e.a.name for e in info.y[1][::-2]] == ["y_1_2_a", "y_1_0_a"]
    assert [e.a.name for e in info.y[1][::-1][1:]] == ["y_1_1_a", "y_1_0_a"]
    assert [e.a.name for e in info.y[1][1:][::-1][:1]] == ["y_1_2_a"]
    assert len(info.y[5:]) == 0
    assert repr(ports.y[::-1][0]) == "VerilatedInterfaceArray([ports.y[1][0], ports.y[1][1], ports.y[1][2]])"
    assert repr(info.y[::-1][0][2]) == "VerilatedInfoInterface(info_ports.y[1][2])"

    # values, through structured and sliced access
    ports.s = 3
    ports.x[1].a = 5
    ports.x[1]["b"] = True
    inst.step(1)
    assert ports.t == 3
    assert [e.a for e in ports.y[0]] == [0, 5, 0]
    assert ports.y[1][1]["b"] is True
    assert ports.y[1:][0][1].a == 5

    # values through port info
    info.s.value = 2
    inst.info_ports_flat.x_1_a.value = 6
    inst.step(1)
    assert info.t.value == 2
    assert inst.info_ports_flat["y_0_1_a"].value == 6
    assert info.y[1:][0][1].a.value == 6

    # errors
    with pytest.raises(AttributeError, match="port `z` not found"):
        _ = ports.z
    with pytest.raises(AttributeError, match="port `x_0_a` not found"):
        _ = ports.x_0_a
    with pytest.raises(AttributeError, match="interface `info_ports.y\\[1\\]\\[2\\]` does not have port `c`"):
        _ = info.y[::-1][0][2].c
    with pytest.raises(AttributeError, match="interface `ports.x\\[0\\]` does not have port `c`"):
        ports.x[0].c = 1
    with pytest.raises(IndexError, match="index 3 out of range for interface array with length 3"):
        _ = ports.x[3]
    with pytest.raises(TypeError, match="must be integers or slices, not `<class 'str'>`"):
        _ = ports.x["0"]
    with pytest.raises(ValueError, match="cannot set interface `ports.x` directly"):
        ports.x = 1
    with pytest.raises(ValueError, match="cannot set port info `info_ports.x\\[0\\].a`"):
        info.x[0].a = 1
