export type WorkerRequest =
    | { type: "init"; module: WebAssembly.Module }
    | { type: "compile"; request: CompileRequest };

export interface CompileRequest {
    source: string;
    include_format: boolean;
    include_ir: boolean;
}

export interface CompileResult {
    compile_diags_ansi: string;
    compile_prints: string[];
    lowered_verilog: string;
    format_diags_ansi: string;
    format_debug_str: string;
    ir_debug_str: string;
}

export type CompileResponse =
    | { type: "result"; result: CompileResult }
    | { type: "error"; message: string };
