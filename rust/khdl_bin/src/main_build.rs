use crate::args::ArgsBuild;
use crate::util::{ErrorExit, manifest_find_read_parse, print_diagnostics};
use itertools::Itertools;
use khdl_language::back::lower_cpp::lower_to_cpp;
use khdl_language::back::lower_verilog::lower_to_verilog;
use khdl_language::front::compile::{
    CompileFixed, CompileRefs, CompileSettings, CompileShared, ImportValue, QueueItems,
};
use khdl_language::front::diagnostic::{DiagError, Diagnostics};
use khdl_language::front::item::ElaboratedModule;
use khdl_language::front::print::StdoutPrintHandler;
use khdl_language::front::value::{CompileValue, SimpleCompileValue};
use khdl_language::syntax::collect::collect_source_from_manifest;
use khdl_language::syntax::hierarchy::{HierarchyNode, SourceHierarchy};
use khdl_language::syntax::manifest::Manifest;
use khdl_language::syntax::parsed::ParsedDatabase;
use khdl_language::syntax::pos::Spanned;
use khdl_language::syntax::source::SourceDatabase;
use khdl_language::syntax::token::Tokenizer;
use khdl_language::util::arena::IndexType;
use khdl_language::util::pool::ThreadPool;
use khdl_language::util::{NON_ZERO_USIZE_ONE, get_num_cpus};
use khdl_util::io::{IoAction, IoErrorExt};
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

pub fn main_build(args: ArgsBuild) -> ExitCode {
    // interpret args
    let ArgsBuild {
        manifest,
        top,
        top_only,
        output_verilog,
        output_cpp,
        debug_output_ir,
        thread_count,
        debug_profile,
        debug_print_files,
        debug_keep_main_stack,
    } = args;

    if top_only && top.is_empty() {
        eprintln!("error: --top-only requires at least one --top module");
        return ExitCode::FAILURE;
    }

    let thread_count = if debug_keep_main_stack {
        if thread_count.is_some() {
            eprintln!(
                "error: --debug-keep-main-stack is always single-threaded, so changing thread count does nothing"
            );
        }
        None
    } else {
        Some(thread_count.unwrap_or_else(get_num_cpus))
    };
    let settings = CompileSettings { do_ir_cleanup: true };
    let queue_items = if top_only { QueueItems::None } else { QueueItems::All };

    let start_all = Instant::now();
    let start_source = start_all;

    // find and parse manifest
    let mut source = SourceDatabase::new();
    let manifest = match manifest_find_read_parse(&mut source, manifest) {
        Ok(m) => m,
        Err(ErrorExit) => return ExitCode::FAILURE,
    };
    let Manifest {
        source: manifest_source,
    } = manifest.parsed;
    let manifest_span = source.full_span(manifest.file);

    // collect source
    let diags = Diagnostics::new();
    let (hierarchy, _) = match collect_source_from_manifest(
        &diags,
        &mut source,
        manifest.file,
        &manifest.path_parent,
        &manifest_source,
    ) {
        Ok(s) => s,
        Err(_) => {
            print_diagnostics(&source, diags);
            return ExitCode::FAILURE;
        }
    };
    let time_source = start_source.elapsed();

    // print source info
    if debug_print_files {
        eprintln!("Collected sources:");
        for file in source.files() {
            let file_info = &source[file];
            eprintln!("  [{}]: {:?}", file.inner().index(), file_info.debug_info_path);
        }
        eprintln!("Collected packages:");
        fn print_node(hierarchy: &SourceHierarchy, prefix: &str, node: HierarchyNode) {
            let node_info = &hierarchy[node];
            if let Some(file) = node_info.file {
                eprintln!("{prefix}: [{:?}]", file.inner().index());
            }
            for (key, &child) in &node_info.children {
                print_node(hierarchy, &format!("{prefix}/{key}"), child);
            }
        }
        print_node(&hierarchy, "  ", hierarchy.root_node());
    }

    // parse source
    // TODO parallelize parsing
    let start_parse = Instant::now();
    let parsed = ParsedDatabase::new(&diags, &source, &hierarchy);
    let time_parse = start_parse.elapsed();

    // compilation setup
    let should_stop = Arc::new(AtomicBool::new(false));
    {
        let should_stop = should_stop.clone();
        ctrlc::set_handler(move || should_stop.store(true, Ordering::Relaxed)).expect("Failed to set Ctrl+C handler");
    }
    let fixed = CompileFixed {
        settings: &settings,
        source: &source,
        hierarchy: &hierarchy,
        parsed: &parsed,
    };
    let shared = CompileShared::new(&diags, fixed, queue_items, thread_count.unwrap_or(NON_ZERO_USIZE_ONE));
    let refs = CompileRefs {
        diags: &diags,
        fixed,
        shared: &shared,
        print_handler: &StdoutPrintHandler,
        should_stop: &|| should_stop.load(Ordering::Relaxed),
        interrupted_local: &OnceLock::new(),
    };
    let thread_pool = thread_count.map(ThreadPool::new);

    // find top modules
    // TODO print warning if no top modules selected?
    let start_compile = Instant::now();
    let top_values = top
        .iter()
        .map(
            |top| match refs.resolve_path(Spanned::new(manifest_span, top), false)? {
                ImportValue::Item(item) => refs.eval_item(item),
                ImportValue::HierarchyNode(_) => Err(refs.diags.report_error_simple(
                    format!("top `{top}` must be an item, got a package"),
                    manifest_span,
                    "top set here",
                )),
            },
        )
        .collect_vec();

    // run compilation loop
    refs.run_compile_loop(thread_pool.as_ref());

    // filter top modules
    //   we allowed other top values earlier, they could be useful as compilation roots too
    let top_modules = top_values
        .into_iter()
        .filter_map(|v| {
            if let Ok(&CompileValue::Simple(SimpleCompileValue::Module(ElaboratedModule::Internal(v)))) = v {
                let v_ir = refs.shared.elaboration_arenas.module_internal_info(v).module_ir;
                Some(v_ir)
            } else {
                None
            }
        })
        .collect_vec();

    // finish compilation
    let ir_db = shared.finish_ir_database(&diags, manifest_span);
    let time_compile = start_compile.elapsed();

    // lower and write outputs
    let mut time_lower_ir = None;
    let mut time_lower_verilog = None;
    let mut time_lower_cpp = None;
    let mut outputs = vec![];

    if let Ok(ir_db) = ir_db {
        // output debug ir
        if let Some(output_ir) = debug_output_ir {
            let start_lower_ir = Instant::now();
            let str_ir = format!("{:#?}", ir_db);
            time_lower_ir = Some(start_lower_ir.elapsed());
            outputs.push((output_ir, str_ir));
        }

        // output verilog
        if let Some(output_verilog) = output_verilog {
            let start_lower_verilog = Instant::now();
            match lower_to_verilog(&diags, &ir_db, &top_modules) {
                Ok(lowered_verilog) => {
                    // TODO expose module mapping?
                    outputs.push((output_verilog, lowered_verilog.source));
                }
                Err(e) => {
                    // will be reported later, we can ignore it here
                    let _: DiagError = e;
                }
            }
            time_lower_verilog = Some(start_lower_verilog.elapsed());
        }

        // output c++
        if let Some(output_cpp) = output_cpp {
            let start_lower_cpp = Instant::now();
            match lower_to_cpp(&diags, &ir_db, &top_modules) {
                Ok(lowered_cpp) => {
                    // TODO expose module mapping?
                    outputs.push((output_cpp, lowered_cpp));
                }
                Err(e) => {
                    // will be reported later, we can ignore it here
                    let _: DiagError = e;
                }
            }
            time_lower_cpp = Some(start_lower_cpp.elapsed());
        }
    }

    // write outputs
    let mut any_error = false;
    let start_output = Instant::now();
    for (path, output) in outputs {
        let result = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => {
                std::fs::create_dir_all(parent).map_err(|e| e.with_context(IoAction::CreateDir, parent))
            }
            _ => Ok(()),
        }
        .and_then(|()| std::fs::write(&path, output).map_err(|e| e.with_context(IoAction::Write, &path)));

        match result {
            Ok(()) => {}
            Err(e) => {
                eprintln!("error: {e}");
                any_error = true;
            }
        }
    }
    let time_output = start_output.elapsed();

    let time_all = start_all.elapsed();

    // print diagnostics
    // TODO warnings should maybe not cause nonzero exit codes? add -Werr-like flag
    any_error |= print_diagnostics(&source, diags);

    // print profiling info
    // TODO expand to include separate profiling info for each elaborated item
    if debug_profile {
        // profile tokenization separately
        let start_tokenize = Instant::now();
        let mut total_tokens = 0;
        for file in hierarchy.files() {
            total_tokens += Tokenizer::new(file, &source[file].content, false).into_iter().count();
        }
        let time_tokenize = start_tokenize.elapsed();

        eprintln!();
        eprintln!("profiling info:");
        eprintln!("-----------------------------------------------");
        eprintln!("input files:      {}", source.file_count());
        eprintln!("input lines:      {}", source.total_lines_of_code());
        eprintln!("input tokens:     {total_tokens}");
        eprintln!("----------------------------------------");
        eprintln!("read source:      {time_source:?}");
        eprintln!("tokenize:         {time_tokenize:?}");
        eprintln!("parse + tokenize: {time_parse:?}");
        eprintln!("compile:          {time_compile:?}");
        eprintln!("lower ir:         {}", fmt_duration(time_lower_ir));
        eprintln!("lower verilog:    {}", fmt_duration(time_lower_verilog));
        eprintln!("lower c++:        {}", fmt_duration(time_lower_cpp));
        eprintln!("write outputs:    {time_output:?}");
        eprintln!("-----------------------------------------------");
        eprintln!("total:            {time_all:?}");
        eprintln!();
    }

    // proper exit code
    if any_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn fmt_duration(duration: Option<Duration>) -> String {
    match duration {
        Some(d) => format!("{d:?}"),
        None => "(skipped)".to_string(),
    }
}
