#![no_main]

use khdl_language::front::compile::{CompileFixed, CompileRefs, CompileSettings, CompileShared, QueueItems};
use khdl_language::front::diagnostic::Diagnostics;
use khdl_language::front::print::IgnorePrintHandler;
use khdl_language::syntax::hierarchy::SourceHierarchy;
use khdl_language::syntax::parsed::ParsedDatabase;
use khdl_language::syntax::source::SourceDatabase;
use khdl_language::util::NON_ZERO_USIZE_ONE;
use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

// TODO we can be a lot smarter here, generate only valid asts, reuse identifiers from a limited pool, ...
fuzz_target!(|data: String| target(data));

fn target(data: String) {
    let diags = Diagnostics::new();
    let mut source = SourceDatabase::new();
    let mut hierarchy = SourceHierarchy::new();

    let file = source.add_file("dummy.kh".to_string(), data.to_string());
    let dummy_span = source.full_span(file);
    hierarchy
        .add_file(&diags, &source, dummy_span, &["dummy".to_owned()], file)
        .unwrap();

    let parsed = ParsedDatabase::new(&diags, &source, &hierarchy);

    let settings = CompileSettings { do_ir_cleanup: true };
    let data = khdl_language::syntax::data::DataInputs::new();
    let fixed = CompileFixed {
        data: &data,
        settings: &settings,
        source: &source,
        hierarchy: &hierarchy,
        parsed: &parsed,
    };

    let shared = CompileShared::new(&diags, fixed, QueueItems::All, NON_ZERO_USIZE_ONE);
    let refs = CompileRefs {
        diags: &diags,
        fixed,
        shared: &shared,
        print_handler: &IgnorePrintHandler,
        should_stop: &|| false,
        interrupted_local: &OnceLock::new(),
    };
    refs.run_compile_loop(None);
}
