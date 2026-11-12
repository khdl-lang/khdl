import {initSync, run_all} from "khdl_wasm";
import type {CompileResponse, CompileResult, WorkerRequest} from "./worker_protocol";

const worker_scope = self as unknown as {
    onmessage: ((event: MessageEvent<WorkerRequest>) => void) | null;
    postMessage(message: CompileResponse): void;
};

worker_scope.onmessage = (event) => {
    const message = event.data;
    if (message.type === "init") {
        initSync({module: message.module});
        return;
    }

    const request = message.request;
    try {
        const result = run_all(request.source, request.include_format, request.include_ir);
        // copy the fields out of the wasm object, it can't be sent to the main thread directly
        const output: CompileResult = {
            compile_diags_ansi: result.compile_diags_ansi,
            compile_prints: result.compile_prints,
            lowered_verilog: result.lowered_verilog,
            format_diags_ansi: result.format_diags_ansi,
            format_debug_str: result.format_debug_str,
            ir_debug_str: result.ir_debug_str,
        };
        result.free();
        worker_scope.postMessage({type: "result", result: output});
    } catch (error) {
        console.error(error);
        const message = error instanceof Error ? error.message : String(error);
        worker_scope.postMessage({type: "error", message});
    }
};
