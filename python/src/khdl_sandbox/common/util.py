from contextlib import contextmanager

import khdl


def compile_custom(top: str) -> khdl.Compile:
    # TODO compile/elaborate everything by default?
    source = khdl.Source()
    source.add_source_content(["top"], "python.kh", top)
    return source.compile()


def compile_custom_files(files: dict[str, str]) -> khdl.Compile:
    """Compile multiple files, keyed by their dotted package path, eg. `{"a.b": "..."}`."""
    source = khdl.Source()
    for path, content in files.items():
        source.add_source_content(path.split("."), path.replace(".", "/") + ".kh", content)
    return source.compile()


def diag_error(title: str, has_message: str | None = None, has_info: str | None = None):
    return diag_general(level="error", title=title, has_message=has_message, has_info=has_info)


def diag_warning(title: str, has_message: str | None = None, has_info: str | None = None):
    return diag_general(level="warning", title=title, has_message=has_message, has_info=has_info)


@contextmanager
def diag_general(level: str, title: str, has_message: str | None, has_info: str | None):
    raised = False

    try:
        yield
    except khdl.DiagnosticException as e:
        raised = True

        diags = e.diagnostics
        assert len(diags) > 0, "Diagnostic exception should not be empty"

        for d in diags:
            assert "internal compiler error" not in d.title, "Internal compiler errors should not occur"

        assert len(diags) == 1, f"Expected exactly one diagnostic, got {len(diags)}"
        diag = diags[0]

        assert diag.title == title, f"Diagnostic title mismatch, expected {title}"
        assert diag.level == level, f"Diagnostic level mismatch, expected {level}"
        if has_message is not None:
            assert has_message in diag.messages, f"Diagnostic message check failed, expected {has_message}, got {diag.messages}"
        if has_info is not None:
            assert has_info in diag.infos, f"Diagnostic info check failed, expected {has_info}, got {diag.infos}"

    assert raised, "Expected diagnostic, got no exception"
