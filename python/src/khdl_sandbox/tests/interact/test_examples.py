import re
from pathlib import Path

import khdl

from khdl_sandbox.common.util import compile_custom


def test_webdemo():
    # get webdemo source
    path = Path(__file__).parent / "../../../../../design/top_webdemo.kh"
    source = path.read_text()

    # check that it compiles and elaborates
    c = compile_custom(source)
    _ = c.resolve_module("top.top")

    # check that is correctly formatted
    assert khdl.format_file(source) == source


def test_readme():
    # get readme example code block, the only one without a language tag (the others are shell commands and config)
    path = Path(__file__).parent / "../../../../../README.md"
    blocks = re.findall(r"^```([^\n]*)\n(.*?)^```", path.read_text(), flags=re.MULTILINE | re.DOTALL)
    blocks = [code for lang, code in blocks if lang == ""]
    assert len(blocks) == 1
    source = blocks[0]

    # check that it compiles and elaborates
    c = compile_custom(source)
    _ = c.resolve_module("top.top")

    # check that is correctly formatted
    assert khdl.format_file(source) == source
