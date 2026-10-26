import json
from pathlib import Path

import khdl
import pytest


def compile_json(body: str, inputs: dict[str, str], prefix: str = "") -> khdl.Compile:
    source = khdl.Source()
    source.add_file_content(["top"], "top.kh", "import std.json;\n" + prefix + "\n" + body)
    for name, text in inputs.items():
        source.add_data_content(name, name + ".json", text)
    return source.compile()


@pytest.mark.parametrize("target,text,expected", [
    ("bool", "true", True),
    ("str", '"é\\uD83D\\uDE00"', "é😀"),
    ("int", "1234567890123456789012345678901234567890", 1234567890123456789012345678901234567890),
    ("int", "-1234567890123456789012345678901234567890", -1234567890123456789012345678901234567890),
    ("uint", "-0", 0),
    ("[3]int", "[1,2,3]", [1, 2, 3]),
    ("[_]bool", "[]", []),
    ("[_][_]int", "[[1],[],[2,3]]", [[1], [], [2, 3]]),
    ("Tuple(int, bool, str)", '[1,true,"s"]', (1, True, "s")),
    ("Tuple()", "[]", ()),
])
def test_json_values(target, text, expected):
    c = compile_json(f'const result = json.load("input", {target});', {"input": text})
    assert c.resolve("top.result") == expected


def test_json_struct_and_generic_selection():
    c = compile_json('''
        fn read(i: uint, T: type) -> T { return json.load("foo.coefficients_{i}", T); }
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


def test_json_enums_options_and_lookalike():
    c = compile_json('''
        const idle = json.load("idle", State);
        const transfer = json.load("transfer", State);
        const none = json.load("none", Option(int));
        const some = json.load("some", Option(int));
        const nested = json.load("nested", Option([_]Option(int)));
        const lookalike = json.load("lookalike", FakeOption);
    ''', {"idle": '"Idle"', "transfer": '{"Transfer":[3,true]}', "none": "null", "some": "9",
          "nested": "[null, 3]", "lookalike": '"None"'},
        "enum State { Idle, Transfer(Tuple(int, bool)) } enum FakeOption { None, Some(int) }")
    assert c.resolve("top.idle").tag == "Idle"
    assert c.resolve("top.transfer").payload == (3, True)
    assert c.resolve("top.none").tag == "None"
    assert c.resolve("top.some").payload == 9
    nested = c.resolve("top.nested")
    assert nested.tag == "Some"
    assert [v.tag for v in nested.payload] == ["None", "Some"]
    assert c.resolve("top.lookalike").tag == "None"


@pytest.mark.parametrize("target,text,prefix,title", [
    ("int", "1.0", "", "JSON value does not match destination type"),
    ("int", "1e3", "", "JSON value does not match destination type"),
    ("int(0..=7)", "8", "", "JSON value does not match destination type"),
    ("bool", "null", "", "JSON value does not match destination type"),
    ("[2]int", "[1]", "", "JSON value does not match destination type"),
    ("Tuple(int, bool)", "[1]", "", "JSON value does not match destination type"),
    ("S", '{"a":1,"\\u0061":2}', "struct S { a: int }", "duplicate JSON field"),
    ("S", '{"a":1,"extra":2}', "struct S { a: int }", "unknown JSON field"),
    ("S", "{}", "struct S { a: int }", "JSON value does not match destination type"),
    ("S", "{}", "struct S { optional: Option(int) }", "JSON value does not match destination type"),
    ("E", '"Unknown"', "enum E { A }", "unknown JSON enum variant"),
    ("E", '"A"', "enum E { A(int) }", "JSON value does not match destination type"),
    ("Option(Option(int))", "null", "", "ambiguous JSON option schema"),
    ("S", '{"value":null}', "type O = Option(int); struct S { value: Option(O) }", "ambiguous JSON option schema"),
    ("E", '"A"', "enum E { A, B(Option(Option(int))) }", "ambiguous JSON option schema"),
    ("any", "1", "", "unsupported JSON destination type"),
    ("S", "{}", "struct S { value: any }", "unsupported JSON destination type"),
    ("type", "1", "", "unsupported JSON destination type"),
    ("int", "[1,]", "", "invalid JSON"),
    ("str", '"raw\nnewline"', "", "invalid JSON"),
    ("str", '"\\uD800"', "", "invalid JSON"),
    ("int", "", "", "invalid JSON"),
    ("int", "1 2", "", "invalid JSON"),
])
def test_json_errors(target, text, prefix, title):
    c = compile_json(f'const result = json.load("input", {target});', {"input": text}, prefix)
    with pytest.raises(khdl.DiagnosticException) as error:
        c.resolve("top.result")
    assert [d.title for d in error.value.diagnostics] == [title]
    rendered = error.value.combined_string
    assert "top.kh" in rendered
    if title not in {"unsupported JSON destination type", "ambiguous JSON option schema"}:
        assert "input.json" in rendered


def test_json_unused_and_separate_namespaces():
    c = compile_json('const result = json.load("top", int);', {"top": "5", "unused": "malformed"})
    assert c.resolve("top.result") == 5


def test_json_repeated_failures_keep_call_context():
    c = compile_json('''
        fn first() -> int { return json.load("input", int); }
        fn second() -> int { return json.load("input", int); }
    ''', {"input": "false"})
    for name in ("first", "second"):
        with pytest.raises(khdl.DiagnosticException) as error:
            c.resolve("top." + name)()
        assert "input.json" in error.value.combined_string
        assert "JSON loaded here" in error.value.combined_string


def test_json_cached_failure_does_not_capture_first_schema_use():
    c = compile_json('''
        fn first_helper() -> int { return __builtin("fn", "json_load", "input", int); }
        const first = first_helper();



        fn second_helper() -> int { return __builtin("fn", "json_load", "input", int); }
        const second = second_helper();
    ''', {"input": "false"})
    with pytest.raises(khdl.DiagnosticException):
        c.resolve("top.first")
    with pytest.raises(khdl.DiagnosticException) as error:
        c.resolve("top.second")
    assert "second_helper" in error.value.combined_string
    assert "first_helper" not in error.value.combined_string


@pytest.mark.parametrize("name", ["missing", "/tmp/input.json", "foo..bar", "../input", ""])
def test_json_names(name):
    c = compile_json(f"const result = json.load({json.dumps(name)}, int);", {})
    with pytest.raises(khdl.DiagnosticException) as error:
        c.resolve("top.result")
    assert error.value.diagnostics[0].title.startswith(("unknown data alias", "invalid data alias"))


def make_project(tmp_path: Path, data_section: str):
    (tmp_path / "top.kh").write_text('import std.json; const result = json.load("tables.nested.a", int);')
    (tmp_path / "khdl.toml").write_text('[source]\ntop = "top.kh"\n[data]\n' + data_section)
    return tmp_path / "khdl.toml"


def test_json_manifest_directory(tmp_path):
    folder = tmp_path / "data" / "nested"
    folder.mkdir(parents=True)
    (folder / "a.json").write_text("42")
    (folder / "ignored.txt").write_text("not JSON")
    manifest = make_project(tmp_path, 'tables = "data"\n')
    assert khdl.Source.new_from_manifest_path(str(manifest)).compile().resolve("top.result") == 42


@pytest.mark.parametrize("declaration", [
    'tables.nested.a = "one.data"\n',
    'tables.nested.a._ = "one.data"\n',
    '[data.tables.nested]\na = "one.data"\n',
])
def test_json_manifest_dotted_keys_and_flattening(tmp_path, declaration):
    (tmp_path / "one.data").write_text("42")
    manifest = make_project(tmp_path, declaration)
    assert khdl.Source.new_from_manifest_path(str(manifest)).compile().resolve("top.result") == 42


def test_json_manifest_missing_unused_file(tmp_path):
    manifest = make_project(tmp_path, 'unused = "missing.json"\n')
    with pytest.raises(khdl.DiagnosticException):
        khdl.Source.new_from_manifest_path(str(manifest))


def test_json_manifest_directory_collision(tmp_path):
    (tmp_path / "data").mkdir()
    (tmp_path / "data" / "a.json").write_text("1")
    manifest = make_project(tmp_path, '_ = "data"\na = "data/a.json"\n')
    with pytest.raises(khdl.DiagnosticException) as error:
        khdl.Source.new_from_manifest_path(str(manifest))
    assert error.value.diagnostics[0].title == "duplicate data alias `a`"


def test_json_manifest_invalid_derived_alias(tmp_path):
    (tmp_path / "data").mkdir()
    (tmp_path / "data" / "not-valid.json").write_text("1")
    manifest = make_project(tmp_path, 'tables = "data"\n')
    with pytest.raises(khdl.DiagnosticException) as error:
        khdl.Source.new_from_manifest_path(str(manifest))
    assert error.value.diagnostics[0].title == "invalid data alias `tables.not-valid`"


def test_json_manifest_root_directory_flattening(tmp_path):
    (tmp_path / "data" / "tables" / "nested").mkdir(parents=True)
    (tmp_path / "data" / "tables" / "nested" / "a.json").write_text("42")
    manifest = make_project(tmp_path, '_ = "data"\n')
    assert khdl.Source.new_from_manifest_path(str(manifest)).compile().resolve("top.result") == 42


def test_json_manifest_absolute_symlink(tmp_path):
    outside = tmp_path / "external"
    outside.mkdir()
    (outside / "a.json").write_text("42")
    (tmp_path / "linked").symlink_to(outside, target_is_directory=True)
    manifest = make_project(tmp_path, f'tables.nested = {json.dumps(str(tmp_path / "linked"))}\n')
    assert khdl.Source.new_from_manifest_path(str(manifest)).compile().resolve("top.result") == 42


def test_json_manifest_invalid_utf8_is_eager(tmp_path):
    (tmp_path / "bad.json").write_bytes(b"\xff")
    manifest = make_project(tmp_path, 'unused = "bad.json"\n')
    with pytest.raises(khdl.DiagnosticException):
        khdl.Source.new_from_manifest_path(str(manifest))


def test_json_cache_distinguishes_target_types():
    c = compile_json('''
        const good = json.load("input", int);
        const bad = json.load("input", bool);
        const again = json.load("input", int);
    ''', {"input": "42"})
    assert c.resolve("top.good") == 42
    with pytest.raises(khdl.DiagnosticException):
        c.resolve("top.bad")
    assert c.resolve("top.again") == 42


def test_json_unusual_field_names():
    c = compile_json('const result = json.load("input", Config);', {"input": '{"bus-width":8}'},
                     'struct Config { ident("bus-width"): int }')
    assert c.resolve("top.result").fields == {"bus-width": 8}


def test_json_module_elaboration():
    c = compile_json('''
        module top ports(y: out async bool) {
            const config = json.load("input", bool);
            comb { y = config; }
        }
    ''', {"input": "true"})
    assert "y = 1'b1;" in c.resolve_module("top.top").as_verilog().source


def test_json_hardware_name_is_rejected():
    c = compile_json('''
        module top ports(x: in async bool, y: out async bool) {
            comb { y = json.load("{x}", bool); }
        }
    ''', {"true": "true", "false": "false"})
    with pytest.raises(khdl.DiagnosticException) as error:
        c.resolve_module("top.top").as_verilog()
    assert all("internal compiler error" not in d.title for d in error.value.diagnostics)
