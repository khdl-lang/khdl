import os
import random
import re
from pathlib import Path

import khdl
import pytest

# The code examples shown on the website. Each example must compile, unless it has a sibling `.err` file, in which case
# it must fail with exactly that (colored) diagnostic, which the website shows next to it.
# Set KHDL_UPDATE_WEBSITE_EXAMPLES=1 to rewrite the `.err` files from the current compiler output.
EXAMPLES_DIR = Path(__file__).parents[5] / "website" / "examples"
EXAMPLES = sorted(EXAMPLES_DIR.glob("*.kh"))


def test_website_examples_exist():
    assert len(EXAMPLES) > 0, f"no examples found in {EXAMPLES_DIR}"


@pytest.mark.parametrize("path", EXAMPLES, ids=lambda p: p.stem)
def test_website_example_formatted(path: Path):
    content = path.read_text()
    assert khdl.format_file(content) == content, "example is not formatted, run the formatter on it"


@pytest.mark.parametrize("path", EXAMPLES, ids=lambda p: p.stem)
def test_website_example(path: Path):
    content = path.read_text()

    # elaborate all non-generic public modules, generic ones need a wrapper in the hidden part of the example
    tops = re.findall(r"^pub module (\w+) ports\(", content, flags=re.MULTILINE)
    assert len(tops) > 0, "example should contain at least one non-generic public module"

    source = khdl.Source()
    source.add_source_content(["example"], path.name, content)
    try:
        compiled = source.compile()
        for top in tops:
            compiled.resolve_module(f"example.{top}").as_verilog()
        actual = None
        actual_plain = None
    except khdl.DiagnosticException as e:
        actual = e.combined_string_colored
        actual_plain = e.combined_string

    err_path = path.with_suffix(".err")
    if os.environ.get("KHDL_UPDATE_WEBSITE_EXAMPLES") == "1":
        if actual is None:
            err_path.unlink(missing_ok=True)
        else:
            err_path.write_text(actual)
        return

    if err_path.exists():
        assert actual is not None, "example should fail with the diagnostic in its .err file, but it compiled"
        assert actual == err_path.read_text(), f"diagnostic changed, got:\n{actual_plain}"
    else:
        assert actual is None, f"example should compile, got:\n{actual_plain}"


@pytest.mark.parametrize("p_valid, p_ready", [(0.5, 0.5), (0.9, 0.3), (0.3, 0.9), (1.0, 1.0)])
def test_website_example_add_five(tmp_dir: Path, p_valid: float, p_ready: float):
    # simulate the ready/valid example with random stalls on both sides, like the animation on the website
    source = khdl.Source()
    source.add_source_content(["example"], "add_five.kh", (EXAMPLES_DIR / "add_five.kh").read_text())
    inst = source.compile().resolve_module("example.AddFive").as_verilated(tmp_dir).instance()
    ports = inst.ports

    def clock():
        ports.clk = True
        inst.step(1)
        ports.clk = False
        inst.step(1)

    ports.rst = True
    ports.input_valid = False
    ports.output_ready = False
    clock()
    ports.rst = False

    rng = random.Random(0)
    sent = []
    received = []
    presenting = None
    previous_output = None
    for _ in range(2000):
        if presenting is None and rng.random() < p_valid:
            presenting = rng.randrange(256)
        ports.input_valid = presenting is not None
        ports.input_data = presenting if presenting is not None else 0
        output_ready = rng.random() < p_ready
        ports.output_ready = output_ready
        inst.step(1)

        # the output must hold its value until it is taken
        output = (ports.output_valid, ports.output_data)
        if previous_output is not None and previous_output[0] and not previous_output[2]:
            assert output == previous_output[:2]
        previous_output = (*output, output_ready)

        if presenting is not None and ports.input_ready:
            sent.append(presenting)
            presenting = None
        if output[0] and output_ready:
            received.append(output[1])
        clock()

    assert received == [(x + 5) % 256 for x in sent][:len(received)]
    assert len(sent) - len(received) <= 2
    if p_valid == 1.0 and p_ready == 1.0:
        # full throughput: one value per cycle after the initial latency
        assert len(received) >= 1998
