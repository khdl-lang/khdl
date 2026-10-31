import khdl
import pytest

from khdl_sandbox.common.util import diag_error


def compile_json(body: str, inputs: dict[str, str], prefix: str = "") -> khdl.Compile:
    source = khdl.Source()
    source.add_source_content(["top"], "top.kh", "import std.data.load_json;\n" + prefix + "\n" + body)
    for name, text in inputs.items():
        source.add_data_content(name.split("."), name + ".json", text)
    return source.compile()


def resolve_json(target: str, text: str, prefix: str = ""):
    c = compile_json(f'const result = load_json("input", {target});', {"input": text}, prefix)
    return c.resolve("top.result")


def test_json_values():
    cases = [
        ("bool", "true", True),
        ("str", '"é\\uD83D\\uDE00"', "é😀"),
        ("int", "1234567890123456789012345678901234567890", 1234567890123456789012345678901234567890),
        ("int", "-1234567890123456789012345678901234567890", -1234567890123456789012345678901234567890),
        ("int", '"42"', 42),
        ("uint", "-0", 0),
        ("[3]int", "[1,2,3]", [1, 2, 3]),
        ("[_]bool", "[]", []),
        ("[_][_]int", "[[1],[],[2,3]]", [[1], [], [2, 3]]),
        ("Tuple(int, bool, str)", '[1,true,"s"]', (1, True, "s")),
        ("Tuple()", "[]", ()),
    ]
    for target, text, expected in cases:
        assert resolve_json(target, text) == expected


def test_json_struct_and_generic_selection():
    c = compile_json('''
        fn read(i: uint, T: type) -> T { return load_json("foo.coefficients_{i}", T); }
        const first = read(0, Config);
        const second = read(1, Config);
        const both = [first, second];
    ''', {
        "foo.coefficients_0": '{"enabled":true,"width":8}',
        "foo.coefficients_1": '{"width":16,"enabled":false}',
    }, "struct Config { width: int(1..=64), enabled: bool }")
    assert c.resolve("top.first").fields == {"width": 8, "enabled": True}
    assert c.resolve("top.second").fields == {"width": 16, "enabled": False}
    assert len(c.resolve("top.both")) == 2


def test_json_unusual_field_names():
    prefix = 'struct Config { ident("bus-width"): int }'
    assert resolve_json("Config", '{"bus-width":8}', prefix).fields == {"bus-width": 8}


def test_json_enums_and_options():
    c = compile_json('''
        const idle = load_json("idle", State);
        const transfer = load_json("transfer", State);
        const none = load_json("none", Option(int));
        const some = load_json("some", Option(int));
        const nested = load_json("nested", Option([_]Option(int)));
        const lookalike = load_json("lookalike", FakeOption);
    ''', {
        "idle": '"Idle"',
        "transfer": '{"Transfer":[3,true]}',
        "none": "null",
        "some": "9",
        "nested": "[null, 3]",
        "lookalike": '"None"',
    }, "enum State { Idle, Transfer(Tuple(int, bool)) } enum FakeOption { None, Some(int) }")
    assert c.resolve("top.idle").tag == "Idle"
    assert c.resolve("top.transfer").payload == (3, True)
    assert c.resolve("top.none").tag == "None"
    assert c.resolve("top.some").payload == 9
    nested = c.resolve("top.nested")
    assert nested.tag == "Some"
    assert [v.tag for v in nested.payload] == ["None", "Some"]
    assert c.resolve("top.lookalike").tag == "None"


def test_json_int_errors():
    for text in ["1.0", "1e3", '"abc"']:
        with diag_error("JSON: invalid integer literal"):
            resolve_json("int", text)
    with diag_error("JSON: integer value out of range"):
        resolve_json("int(0..=7)", "8")


def test_json_compound_errors():
    with diag_error("JSON: type mismatch, got value kind null"):
        resolve_json("bool", "null")
    with diag_error("JSON: array length mismatch: expected 2, got 1"):
        resolve_json("[2]int", "[1]")
    with diag_error("JSON: tuple length mismatch"):
        resolve_json("Tuple(int, bool)", "[1]")


def test_json_struct_errors():
    prefix = "struct S { a: int }"
    with diag_error("JSON: duplicate object field"):
        resolve_json("S", '{"a":1,"\\u0061":2}', prefix)
    with diag_error("JSON: leftover struct field: `extra`"):
        resolve_json("S", '{"a":1,"extra":2}', prefix)
    with diag_error("JSON: missing struct field `a`"):
        resolve_json("S", "{}", prefix)
    with diag_error("JSON: type mismatch, got value kind array"):
        resolve_json("S", "[]", prefix)
    with diag_error("JSON: missing struct field `optional`"):
        resolve_json("S", "{}", "struct S { optional: Option(int) }")


def test_json_enum_errors():
    with diag_error("JSON: unknown enum variant `Unknown`"):
        resolve_json("E", '"Unknown"', "enum E { A }")
    for text in ['"A"', '{"B":1}']:
        with diag_error("JSON: enum payload mismatch"):
            resolve_json("E", text, "enum E { A(int), B }")
    for text in ['{"A":1,"B":2}', "5"]:
        with diag_error("JSON: failed to parse as enum"):
            resolve_json("E", text, "enum E { A, B }")


def test_json_schema_errors():
    with diag_error("JSON: ambiguous option type"):
        resolve_json("Option(Option(int))", "null")
    with diag_error("JSON: ambiguous option type"):
        resolve_json("S", '{"value":null}', "type O = Option(int); struct S { value: Option(O) }")
    for target in ["any", "type"]:
        with diag_error(f"JSON: unsupported destination type `{target}`"):
            resolve_json(target, "1")


def test_json_invalid_syntax():
    for text in ["[1,]", "", "1 2", '"raw\nnewline"', '"\\uD800"']:
        with diag_error("invalid JSON"):
            resolve_json("int", text)


def test_json_unknown_path():
    c = compile_json(f"const result = load_json(\"missing\", int);", {})
    with diag_error(f"could not find data path `missing`"):
        c.resolve("top.result")
