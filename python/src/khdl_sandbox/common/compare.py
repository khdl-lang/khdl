from dataclasses import dataclass
from pathlib import Path
from typing import Tuple, List

import khdl

from khdl_sandbox.common.util import compile_custom


@dataclass
class CompiledCompare:
    input_count: int

    compile: khdl.Compile

    eval_func: khdl.Value
    eval_mod: khdl.Module
    eval_mod_inst: khdl.VerilatedInstance

    def eval(self, values: List[object]) -> Tuple[object, object]:
        assert len(values) == self.input_count, \
            f"Input value count mismatch, expected {self.input_count}, got {len(values)}"

        # eval func
        val_res_func = self.eval_func(*values)

        # eval module
        ports = self.eval_mod_inst.ports
        for p_name, v in zip(ports, values):
            ports[p_name] = v
        self.eval_mod_inst.step(1)
        val_res_mod = ports.p_res

        return val_res_func, val_res_mod

    def eval_assert(self, values: List[object], expected: object):
        val_res_func, val_res_mod = self.eval(values)
        assert val_res_func == expected, f"Function result {val_res_func} != expected {expected}"
        assert val_res_mod == expected, f"Module result {val_res_mod} != expected {expected}"


def compare_codegen(ty_inputs: List[str], ty_res: str, body: str, prefix: str) -> khdl.Compile:
    args = ", ".join(f"a{i}: {t}" for i, t in enumerate(ty_inputs))
    ports_in = ", ".join(f"p{i}: in async {t}" for i, t in enumerate(ty_inputs))
    params = ", ".join(f"a{i}=p{i}" for i in range(len(ty_inputs)))
    ports_comma = ", " if ports_in else ""

    body_indented = "\n".join("    " + s for s in body.splitlines())

    src = f"""
{prefix}
fn eval_func({args}) -> any {{
{body_indented}
}}
module print_type_mod ports({ports_in}) {{
    wire w_res = eval_func({params});
    const {{
        print(type(w_res), end="");        
    }}
}}
module eval_mod ports({ports_in}{ports_comma}p_res: out async {ty_res}) {{
    comb {{
        p_res = eval_func({params});
    }}
}}
    """

    # print(src)

    return compile_custom(src)


def compare_get_type(ty_inputs: List[str], body: str, prefix: str) -> str:
    c = compare_codegen(ty_inputs, "dummy", body, prefix)
    with c.capture_prints() as capture:
        c.resolve("top.print_type_mod")

    assert len(capture.prints) == 1
    return capture.prints[0]


def compare_body(
        ty_inputs: List[str],
        ty_res: str,
        body: str,
        build_dir: Path,
        prefix: str = ""
) -> CompiledCompare:
    c = compare_codegen(ty_inputs, ty_res, body, prefix)
    eval_func = c.resolve("top.eval_func")
    eval_mod = c.resolve_module("top.eval_mod")

    print(eval_mod.as_verilog().source)

    build_dir.mkdir(parents=True, exist_ok=True)
    eval_mod_inst = eval_mod.as_verilated(build_dir).instance()

    return CompiledCompare(
        input_count=len(ty_inputs),
        compile=c,
        eval_func=eval_func,
        eval_mod=eval_mod,
        eval_mod_inst=eval_mod_inst
    )


def compare_expression(
        ty_inputs: List[str], ty_res: str, expr: str, build_dir: Path, prefix: str = ""
) -> CompiledCompare:
    body = f"return {expr};"
    return compare_body(ty_inputs=ty_inputs, ty_res=ty_res, body=body, build_dir=build_dir, prefix=prefix)
