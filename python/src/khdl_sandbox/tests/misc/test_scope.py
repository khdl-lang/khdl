import khdl
import pytest

from khdl_sandbox.common.util import compile_custom


def test_undeclared_suggests_similar():
    # local variables, file items and prelude items are all suggested
    cases = [
        (
            "fn f() -> int { val counter = 1; return countr; }",
            "countr",
            "did you mean `counter`?"
        ),
        (
            "fn f() -> int { val count = 1; val counter = 2; return counte; }",
            "counte",
            "did you mean `count` or `counter`?"),
        (
            "fn helper() -> int { return 1; }\nfn f() -> int { return helpr(); }",
            "helpr",
            "did you mean `helper`?"
        ),
        (
            "fn f() -> any { return boool; }",
            "boool",
            "did you mean `bool`?"),
        (
            "fn f() -> any { return xyzzy_nothing; }",
            "xyzzy_nothing",
            None
        ),
    ]
    for src, name, hint in cases:
        with pytest.raises(khdl.DiagnosticException) as e:
            compile_custom(src).resolve("top.f")()

        (diag,) = e.value.diagnostics
        assert diag.title == f"undeclared identifier `{name}`"
        if hint is None:
            assert "did you mean" not in diag.full_string
        else:
            assert hint in diag.full_string


def test_redeclaration_single_error():
    # multiple redeclarations must be reported as a single error
    src = "module top ports(x: in async bool, x: in async bool, x: in async bool) {}"
    with pytest.raises(khdl.DiagnosticException) as e:
        compile_custom(src).resolve("top.top")

    diags = e.value.diagnostics
    assert len(diags) == 1
    assert diags[0].title == "identifier `x` declared multiple times"
    assert diags[0].messages == ["declared again here", "declared again here"]
    assert diags[0].infos == ["first declared here"]
