use itertools::Itertools;
use khdl_language::back::lower_cpp::lower_to_cpp;
use khdl_language::back::lower_verilog::lower_to_verilog;
use khdl_language::front::compile::{
    CompileFixed, CompileRefs, CompileSettings, CompileShared, ImportValue, QueueItems,
};
use khdl_language::front::diagnostic::{DiagResult, Diagnostics, diags_to_string};
use khdl_language::front::item::ElaboratedModule;
use khdl_language::front::print::CollectPrintHandler;
use khdl_language::front::value::{CompileValue, SimpleCompileValue};
use khdl_language::mid::ir::IrModule;
use khdl_language::syntax::ast;
use khdl_language::syntax::collect::add_std_sources;
use khdl_language::syntax::format::{FormatError, FormatSettings, format_file};
use khdl_language::syntax::hierarchy::SourceHierarchy;
use khdl_language::syntax::parsed::{AstRefItem, ParsedDatabase};
use khdl_language::syntax::pos::Spanned;
use khdl_language::syntax::source::{FileId, SourceDatabase};
use khdl_language::syntax::token::{TokenCategory, Tokenizer};
use khdl_language::util::{NON_ZERO_USIZE_ONE, ResultExt};
use std::sync::OnceLock;
use std::time::Duration;
use strum::IntoEnumIterator;
use wasm_bindgen::prelude::wasm_bindgen;

mod supress_unused {
    // Suppress the "unused crate" warning for `getrandom`.
    // It's in the dependency list for its side effects, not for direct use.
    #[allow(unused_imports)]
    use getrandom as _;
}

/// This function automatically runs when the module gets initialized.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

#[wasm_bindgen(getter_with_clone)]
pub struct RunAllResult {
    pub compile_diags_ansi: String,
    pub compile_prints: Vec<String>,

    pub lowered_verilog: String,
    pub lowered_cpp: String,

    pub format_diags_ansi: String,
    pub format_debug_str: String,

    pub ir_debug_str: String,
}

const TIMEOUT: Duration = Duration::from_millis(500);

#[wasm_bindgen]
pub fn run_all(top_src: String, include_format: bool, include_ir: bool) -> RunAllResult {
    run_with_data(top_src, include_format, include_ir, Vec::new(), Vec::new())
}

/// In-memory data inputs; names use the same logical aliases as manifest entries.
#[wasm_bindgen]
pub fn run_with_data(
    top_src: String,
    include_format: bool,
    include_ir: bool,
    names: Vec<String>,
    contents: Vec<String>,
) -> RunAllResult {
    let diags = Diagnostics::new();
    let settings = CompileSettings { do_ir_cleanup: true };
    let mut source = SourceDatabase::new();
    let hierarchy_file = build_source(&diags, &mut source, top_src);
    let mut data = khdl_language::syntax::data::DataInputs::new();
    if let Ok((_, top_file)) = &hierarchy_file {
        let span = source.full_span(*top_file);
        if names.len() != contents.len() {
            let _ = diags.report_error_simple(
                "data names and contents must have equal length",
                span,
                "invalid data inputs",
            );
        } else {
            for (name, content) in names.into_iter().zip(contents) {
                let file = source.add_file(format!("{name}.json"), content);
                let _ = data.add(
                    &diags,
                    &source,
                    name.split('.').map(str::to_owned).collect(),
                    file,
                    span,
                );
            }
        }
    }

    // compile
    let print_handler = CollectPrintHandler::new();
    let compiled = hierarchy_file.as_ref_ok().and_then(|&(ref hierarchy, top_file)| {
        let parsed = ParsedDatabase::new(&diags, &source, hierarchy);

        let start = js_sys::Date::now();
        let timeout_ms = TIMEOUT.as_millis() as f64;
        let should_stop = || js_sys::Date::now() - start >= timeout_ms;
        let dummy_span = source.full_span(top_file);

        let fixed = CompileFixed {
            data: &data,
            settings: &settings,
            source: &source,
            hierarchy,
            parsed: &parsed,
        };
        let shared = CompileShared::new(&diags, fixed, QueueItems::All, NON_ZERO_USIZE_ONE);
        let mut refs = CompileRefs {
            diags: &diags,
            fixed,
            shared: &shared,
            print_handler: &print_handler,
            should_stop: &should_stop,
            interrupted_local: &OnceLock::new(),
        };

        // compile everything with real diagnostics first
        refs.run_compile_loop(None);
        let db = shared.finish_ir_database_ref(&diags, dummy_span)?;

        // find top modules: the module named `top`, or if there is none, all modules without generic parameters
        // use dummy_diags to suppress "path not found" errors
        // (we already did the main compilation, so no real errors will be discarded)
        let dummy_diags = Diagnostics::new();
        refs.diags = &dummy_diags;
        let mut top_modules = vec![];
        if let Ok(ImportValue::Item(top)) = refs.resolve_path(Spanned::new(dummy_span, "top.top"), false)
            && let Some(top) = eval_module_ir(refs, top)
        {
            top_modules.push(top);
        } else if let Ok(file) = parsed[top_file].as_ref_ok() {
            for (item_ref, item) in file.items_with_ref() {
                if let ast::Item::ModuleInternal(module) = item
                    && module.params.is_none()
                    && let Some(top) = eval_module_ir(refs, item_ref)
                {
                    top_modules.push(top);
                }
            }
        }

        Ok((db, top_modules))
    });

    let fallback_error = "/* error */";
    let fallback_empty = "/* empty, no module without generic parameters */";

    // lower
    let lowered_verilog = compiled.as_ref_ok().and_then(|(db, tops)| {
        (!tops.is_empty())
            .then(|| lower_to_verilog(&diags, db, tops))
            .transpose()
    });
    let lowered_cpp = compiled
        .as_ref_ok()
        .and_then(|(db, tops)| (!tops.is_empty()).then(|| lower_to_cpp(&diags, db, tops)).transpose());

    // ir
    let ir_debug_str = if include_ir {
        compiled
            .as_ref_ok()
            .map_or_else(|_| fallback_error.to_owned(), |(db, _)| format!("{db:#?}"))
    } else {
        String::new()
    };

    // format
    let diags_format = Diagnostics::new();
    let formatted = if include_format {
        Some(hierarchy_file.as_ref_ok().and_then(|&(_, top_file)| {
            format_file(&diags_format, &source, &FormatSettings::default(), top_file)
                .map(|f| f.debug_str())
                .map_err(FormatError::to_diag_error)
        }))
    } else {
        None
    };

    // package results
    // TODO lower diagnostics directly to html instead of through ansi first?
    let compile_diags_ansi = diags_to_string(&source, &diags.finish(), true);

    let lowered_verilog = lowered_verilog.map_or_else(
        |_| fallback_error.to_owned(),
        |lowered| lowered.map_or_else(|| fallback_empty.to_owned(), |v| v.source),
    );
    let lowered_cpp = lowered_cpp.map_or_else(
        |_| fallback_error.to_owned(),
        |lowered| lowered.unwrap_or_else(|| fallback_empty.to_owned()),
    );

    let format_diags_ansi = diags_to_string(&source, &diags_format.finish(), true);
    let format_debug_str = formatted.map_or_else(String::new, |f| f.unwrap_or_else(|_| fallback_error.to_owned()));

    RunAllResult {
        compile_diags_ansi,
        compile_prints: print_handler.finish(),
        lowered_verilog,
        lowered_cpp,
        format_diags_ansi,
        format_debug_str,
        ir_debug_str,
    }
}

fn eval_module_ir(refs: CompileRefs, item: AstRefItem) -> Option<IrModule> {
    if let Ok(value) = refs.eval_item(item)
        && let &CompileValue::Simple(SimpleCompileValue::Module(ElaboratedModule::Internal(module))) = value
    {
        Some(refs.shared.elaboration_arenas.module_internal_info(module).module_ir)
    } else {
        None
    }
}

#[wasm_bindgen]
pub fn format_source(source: String) -> Option<String> {
    let diags = Diagnostics::new();
    let mut src_db = SourceDatabase::new();
    let file = src_db.add_file("dummy.kh".to_owned(), source);
    match format_file(&diags, &src_db, &FormatSettings::default(), file) {
        Ok(result) => Some(result.new_content),
        Err(_) => None,
    }
}

#[wasm_bindgen]
pub fn initial_source() -> String {
    const SRC_INITIAL_TOP: &str = include_str!("../../../design/top_webdemo.kh");
    SRC_INITIAL_TOP.to_owned()
}

fn build_source(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    top_src: String,
) -> DiagResult<(SourceHierarchy, FileId)> {
    let mut hierarchy = SourceHierarchy::new();
    add_std_sources(diags, source, &mut hierarchy)?;

    let file = source.add_file("top.kh".to_owned(), top_src);
    let dummy_span = source.full_span(file);
    hierarchy.add_file(diags, source, dummy_span, &["top".to_owned()], file)?;

    Ok((hierarchy, file))
}

/// See <https://lezer.codemirror.net/docs/ref/#common.Tree^build>
/// for the expected format of the returned array.
///
/// Node type indices refer to [codemirror_node_types].
/// The result also includes the final top node, with should have an index of `codemirror_node_types().length`.
///
/// The offsets are
/// > the number of characters (UTF16 code units) from the start of the document,
/// > counting line breaks as one character
#[wasm_bindgen]
pub fn codemirror_tokenize_to_tree(src: &str) -> Vec<u32> {
    let mut result = vec![];

    // TODO correct offsets: count newlines as one, and utf16 all the way

    let token_category_to_index = token_category_to_index();
    let top_node_index = codemirror_node_types().len();

    for token in Tokenizer::new(FileId::dummy(), src, true) {
        match token {
            Ok(token) => {
                if let Some(category_index) = token_category_to_index[token.ty.category().index()] {
                    result.extend_from_slice(&[
                        category_index,
                        token.span.start_byte as u32,
                        token.span.end_byte as u32,
                        4,
                    ]);
                }
            }
            Err(_) => {
                // just stop, the error will be reported by the following real compiler flow
                break;
            }
        }
    }

    // push final top token
    result.extend_from_slice(&[top_node_index as u32, 0, src.len() as u32, (4 + result.len()) as u32]);

    result
}

#[wasm_bindgen]
pub fn codemirror_node_types() -> Vec<String> {
    TokenCategory::iter()
        .filter_map(token_category_to_tag)
        .map(str::to_owned)
        .collect_vec()
}

/// Mapping to <https://lezer.codemirror.net/docs/ref/#highlight.tags>.
/// This is implemented on the Rust side to check at compile time whether all categories are covered.
fn token_category_to_tag(tc: TokenCategory) -> Option<&'static str> {
    match tc {
        TokenCategory::Comment => Some("comment"),
        TokenCategory::Identifier => Some("name"),
        TokenCategory::IntegerLiteral => Some("number"),
        TokenCategory::StringLiteral => Some("string"),
        TokenCategory::Keyword => Some("keyword"),
        TokenCategory::Symbol => Some("punctuation"),
    }
}

fn token_category_to_index() -> Vec<Option<u32>> {
    let mut next_index = 0;
    let mut result = vec![];

    for tc in TokenCategory::iter() {
        let index = match token_category_to_tag(tc) {
            None => None,
            Some(_) => {
                let index = next_index;
                next_index += 1;
                Some(index)
            }
        };
        result.push(index);
    }

    result
}
