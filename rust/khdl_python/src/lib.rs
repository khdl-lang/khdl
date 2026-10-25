use crate::convert::compile_value_from_py;
use check::{check_diags, convert_diag_error, map_diag_error};
use convert::{compile_value_to_py, convert_python_args_and_kwargs_to_args};
use indexmap::IndexMap;
use itertools::{Either, Itertools, chain, zip_eq};
use khdl_language::back::lower_verilator::{LoweredVerilator, lower_verilator};
use khdl_language::back::lower_verilog::{LoweredVerilog, lower_to_verilog};
use khdl_language::back::wrap_verilator::{
    SimulationFinished, VerilatedInstance as RustVerilatedInstance, VerilatedLib, VerilatorError,
};
use khdl_language::front::compile::{
    CompileFixed, CompileItemContext, CompileRefs, CompileSettings, CompileShared, QueueItems,
};
use khdl_language::front::diagnostic::Diagnostics;
use khdl_language::front::flow::{FlowCompile, FlowRoot};
use khdl_language::front::function::CallArgs;
use khdl_language::front::item::ElaboratedModule;
use khdl_language::front::print::{CollectPrintHandler, PrintHandler, StdoutPrintHandler};
use khdl_language::front::steps::{SpannedStep, TargetStepCompile, TargetSteps};
use khdl_language::front::string::StringRefs;
use khdl_language::front::types::{Type as RustType, Typed};
use khdl_language::front::value::{
    CompileValue as RustCompileValue, EnumValue as RustEnumValue, NotCompile, SimpleCompileValue,
    StructValue as RustStructValue, Value as RustValue,
};
use khdl_language::mid::ir::{IrDatabase, IrModule, IrPort, IrPortDeclared, IrPortInfo};
use khdl_language::syntax::collect::{
    add_source_files_to_tree, add_std_sources, collect_source_files_from_tree, collect_source_from_manifest,
};
use khdl_language::syntax::format::{FormatError, FormatSettings, format_file as rust_format_file};
use khdl_language::syntax::hierarchy::SourceHierarchy;
use khdl_language::syntax::manifest::Manifest;
use khdl_language::syntax::parsed::ParsedDatabase as RustParsedDatabase;
use khdl_language::syntax::pos::{Span, Spanned};
use khdl_language::syntax::source::SourceDatabase as RustSourceDatabase;
use khdl_language::util::big_int::BigInt;
use khdl_language::util::nd_array::{NdArray, NdArrayShape};
use khdl_language::util::pool::ThreadPool;
use khdl_language::util::range::Range as RustRange;
use khdl_language::util::{NON_ZERO_USIZE_ONE, get_num_cpus};
use khdl_util::io::{IoAction, IoErrorExt, IoErrorWithPath};
use pyo3::exceptions::{PyAttributeError, PyException, PyIOError, PyIndexError, PyTypeError, PyValueError};
use pyo3::types::{
    PyAnyMethods, PyDict, PyIterator, PyList, PyModule, PyModuleMethods, PySlice, PySliceIndices, PySliceMethods,
    PyTuple,
};
use pyo3::{
    Bound, IntoPyObject, IntoPyObjectExt, Py, PyAny, PyClassInitializer, PyErr, PyRef, PyResult, Python,
    create_exception, intern, pyclass, pyfunction, pymethods, pymodule, wrap_pyfunction,
};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;

mod check;
mod convert;

#[pyclass(module = "khdl")]
struct Source {
    source: RustSourceDatabase,
    hierarchy: SourceHierarchy,
    dummy_span: Span,
}

#[pyclass(module = "khdl")]
struct Parsed {
    #[pyo3(get)]
    source: Py<Source>,
    parsed: RustParsedDatabase,
}

#[pyclass(module = "khdl")]
struct Compile {
    pool: Option<ThreadPool>,

    #[pyo3(get)]
    parsed: Py<Parsed>,
    shared: CompileShared,
    capture_prints: Option<Py<CapturePrints>>,
}

#[pyclass(module = "khdl")]
struct CapturePrints {
    #[pyo3(get)]
    prints: Vec<String>,
}

#[pyclass(module = "khdl")]
struct CapturePrintsContext {
    compile: Py<Compile>,
    capture: Py<CapturePrints>,
    prev_capture: Option<Py<CapturePrints>>,
}

// TODO rework this, put all values into an inheritance hierarchy that matches CompileValue
//   (and obviously support all values)
#[pyclass(module = "khdl", subclass)]
struct Value {
    compile: Py<Compile>,
    value: RustCompileValue,
}

// This intentionally does not inherit from Value,
//   to avoid needing a compile reference and being unable to share ranges across compilation contexts.
#[pyclass(module = "khdl")]
struct Range {
    range: RustRange<BigInt>,
}

#[pyclass(module = "khdl", extends=Value)]
struct Module {
    module: ElaboratedModule,
}

// Struct and enum values store a copy of their unwrapped value for convenient access.
#[pyclass(module = "khdl", extends=Value)]
struct StructValue {
    value: RustStructValue<RustCompileValue>,
}

#[pyclass(module = "khdl", extends=Value)]
struct EnumValue {
    value: RustEnumValue<Box<RustCompileValue>>,
}

#[pyclass(module = "khdl")]
struct ModuleVerilog {
    #[pyo3(get)]
    module_name: String,
    #[pyo3(get)]
    source: String,
}

#[pyclass(module = "khdl")]
struct ModuleVerilated {
    compile: Py<Compile>,
    lib: VerilatedLib,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInstance {
    module: Py<ModuleVerilated>,
    instance: RustVerilatedInstance,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedPorts {
    instance: Py<VerilatedInstance>,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInterface {
    inner: InterfaceSelection,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInterfaceArray {
    inner: InterfaceArraySelection,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInfoPorts {
    instance: Py<VerilatedInstance>,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInfoPortsFlat {
    instance: Py<VerilatedInstance>,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInfoInterface {
    inner: InterfaceSelection,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInfoInterfaceArray {
    inner: InterfaceArraySelection,
}

#[pyclass(module = "khdl", unsendable)]
struct VerilatedInfoPort {
    instance: Py<VerilatedInstance>,
    port: IrPort,
}

/// Whether ports are exposed as their values or as their info.
#[derive(Debug, Copy, Clone)]
enum PortsKind {
    Values,
    Info,
}

struct InterfaceSelection {
    instance: Py<VerilatedInstance>,
    kind: PortsKind,
    path: String,
    ports: IndexMap<String, IrPort>,
}

struct InterfaceArraySelection {
    instance: Py<VerilatedInstance>,
    kind: PortsKind,
    path: String,
    elements: NdArray<IndexMap<String, IrPort>>,
    // the selected indices of the first axis of `elements`, after slicing this can be a subset
    indices: Vec<usize>,
}

#[pyclass(module = "khdl", subclass, extends=PyException)]
struct KhdlException {}

#[pyclass(module = "khdl", extends=KhdlException)]
struct DiagnosticException {
    #[pyo3(get)]
    diagnostics: Py<PyList>,

    #[pyo3(get)]
    combined_string: String,
    #[pyo3(get)]
    combined_string_colored: String,
}

// We expose lots of detail here, so it can be used in tests assertions.
#[pyclass(module = "khdl")]
struct Diagnostic {
    #[pyo3(get)]
    level: String,
    #[pyo3(get)]
    title: String,
    #[pyo3(get)]
    messages: Vec<String>,
    #[pyo3(get)]
    infos: Vec<String>,

    #[pyo3(get)]
    full_string: String,
    #[pyo3(get)]
    full_string_colored: String,
}

create_exception!(khdl, SourceSetException, KhdlException);
create_exception!(khdl, GenerateVerilogException, KhdlException);
create_exception!(khdl, VerilationException, KhdlException);
create_exception!(khdl, SimulationFinishedException, KhdlException);
create_exception!(khdl, DiagnosticPreviouslyReportedException, KhdlException);

#[pymethods]
impl KhdlException {
    #[new]
    fn new(msg: String) -> Self {
        // dummy constructor needs to exist for subclass constructors to work
        let _ = msg;
        KhdlException {}
    }
}

impl DiagnosticException {
    pub fn into_err(self, py: Python) -> PyResult<PyErr> {
        // TODO should we include ansi colors in python exceptions by default or not?
        //   it's nice when it works, but will it always work?
        let combined_message_colored = self.combined_string_colored.clone();

        let init = PyClassInitializer::from(KhdlException {}).add_subclass(self);
        let instance = Py::new(py, init)?;

        // set exception message
        // ideally we would immediately pass this to the super constructor, but pyo3 does not yet seem to support that
        instance.setattr(py, intern!(py, "args"), (combined_message_colored,))?;

        Ok(PyErr::from_value(instance.into_bound(py).into_any()))
    }
}

// TODO module level constants for common types, eg. bool, int, uint, ...
//   maybe we can even all of std as a module object? careful about mixing compile contexts though
// TODO add assertions to wrapper types to avoid mixing contexts, those probably hit arena check assertions now
// TODO call Python::check_signals to handle ctrl+C during potentially long running operations
// TODO switch to adding a prefix to python wrappers instead of the original rust types, then rename back in pyclass
#[pymodule]
fn khdl(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    let f_format_file = wrap_pyfunction!(format_file, m)?;
    f_format_file.setattr("__module__", "khdl")?;
    m.add_function(f_format_file)?;

    m.add_class::<Source>()?;
    m.add_class::<Parsed>()?;
    m.add_class::<Compile>()?;
    m.add_class::<CapturePrints>()?;
    m.add_class::<CapturePrintsContext>()?;
    m.add_class::<Value>()?;
    m.add_class::<Range>()?;
    m.add_class::<Module>()?;
    m.add_class::<StructValue>()?;
    m.add_class::<EnumValue>()?;
    m.add_class::<ModuleVerilog>()?;
    m.add_class::<ModuleVerilated>()?;
    m.add_class::<VerilatedInstance>()?;
    m.add_class::<VerilatedPorts>()?;
    m.add_class::<VerilatedInterface>()?;
    m.add_class::<VerilatedInterfaceArray>()?;
    m.add_class::<VerilatedInfoPorts>()?;
    m.add_class::<VerilatedInfoPortsFlat>()?;
    m.add_class::<VerilatedInfoInterface>()?;
    m.add_class::<VerilatedInfoInterfaceArray>()?;
    m.add_class::<VerilatedInfoPort>()?;
    m.add_class::<Diagnostic>()?;
    m.add("KhdlException", py.get_type::<KhdlException>())?;
    m.add("SourceSetException", py.get_type::<SourceSetException>())?;
    m.add("DiagnosticException", py.get_type::<DiagnosticException>())?;
    m.add(
        "DiagnosticPreviouslyReportedException",
        py.get_type::<DiagnosticPreviouslyReportedException>(),
    )?;
    m.add("GenerateVerilogException", py.get_type::<GenerateVerilogException>())?;
    m.add("VerilationException", py.get_type::<VerilationException>())?;
    m.add(
        "SimulationFinishedException",
        py.get_type::<SimulationFinishedException>(),
    )?;
    Ok(())
}

#[pyfunction]
fn format_file(py: Python, src: String) -> PyResult<String> {
    let diags = Diagnostics::new();
    let mut source = RustSourceDatabase::new();
    let file = source.add_file("dummy.kh".to_owned(), src);
    let result = rust_format_file(&diags, &source, &FormatSettings::default(), file);
    let result = map_diag_error(py, &diags, &source, result.map_err(FormatError::to_diag_error))?;
    Ok(result.new_content)
}

const DUMMY_SOURCE: &str = "// dummy file, representing the python caller";

#[pymethods]
impl Source {
    #[new]
    fn new(py: Python) -> PyResult<Self> {
        let mut source = RustSourceDatabase::new();
        let mut hierarchy = SourceHierarchy::new();

        // add dummy file so we have a span to point to for errors caused by the python caller
        let dummy_file = source.add_file("dummy_caller.py".to_owned(), DUMMY_SOURCE.to_owned());
        let dummy_span = source.full_span(dummy_file);

        // add std
        let diags = Diagnostics::new();
        let r = add_std_sources(&diags, &mut source, &mut hierarchy);
        map_diag_error(py, &diags, &source, r)?;

        Ok(Source {
            source,
            hierarchy,
            dummy_span,
        })
    }

    #[staticmethod]
    fn new_from_manifest_path(py: Python, manifest_path: &str) -> PyResult<Self> {
        let diags = Diagnostics::new();
        let mut source = RustSourceDatabase::new();

        // read manifest
        let manifest_path = &PathBuf::from(manifest_path);
        let manifest_parent = manifest_path
            .parent()
            .ok_or_else(|| SourceSetException::new_err("manifest path does not have a parent directory"))?;
        let manifest_content = std::fs::read_to_string(manifest_path)
            .map_err(|e| SourceSetException::new_err(e.with_context(IoAction::Read, manifest_path).to_string()))?;
        let manifest_file = source.add_file(manifest_path.to_string_lossy().into_owned(), manifest_content);

        // parse manifest
        let manifest = Manifest::parse_toml(&diags, &source, manifest_file);
        let manifest = map_diag_error(py, &diags, &source, manifest)?;
        let Manifest {
            source: manifest_source,
        } = manifest;

        // collect hierarchy
        let hierarchy = collect_source_from_manifest(&diags, &mut source, manifest_parent, &manifest_source);
        let (hierarchy, _) = map_diag_error(py, &diags, &source, hierarchy)?;

        let manifest_span = source.full_span(manifest_file);
        Ok(Source {
            source,
            hierarchy,
            dummy_span: manifest_span,
        })
    }

    fn add_file_content(
        &mut self,
        py: Python,
        steps: Vec<String>,
        debug_info_path: String,
        content: String,
    ) -> PyResult<()> {
        let diags = Diagnostics::new();
        let file = self.source.add_file(debug_info_path, content);
        let result = self
            .hierarchy
            .add_file(&diags, &self.source, self.dummy_span, &steps, file)
            .map(|_| ());
        map_diag_error(py, &diags, &self.source, result)
    }

    fn add_tree(&mut self, py: Python, steps: Vec<String>, path: &str) -> PyResult<()> {
        let diags = Diagnostics::new();

        let files = collect_source_files_from_tree(&diags, self.dummy_span, PathBuf::from(path));
        let files = map_diag_error(py, &diags, &self.source, files)?;

        let result = add_source_files_to_tree(
            &diags,
            &mut self.source,
            &mut self.hierarchy,
            self.dummy_span,
            steps,
            &files,
            |path| std::fs::read_to_string(path).map_err(|e| e.with_context(IoAction::Read, path).to_string()),
        );
        map_diag_error(py, &diags, &self.source, result)?;

        Ok(())
    }

    #[getter]
    fn files(&self) -> Vec<String> {
        self.source
            .files()
            // filter out the dummy file
            .skip(1)
            .map(|id| self.source[id].debug_info_path.clone())
            .collect()
    }

    fn parse(slf: Py<Self>, py: Python) -> PyResult<Parsed> {
        let diags = Diagnostics::new();
        let source = slf.borrow(py);
        let parsed = RustParsedDatabase::new(&diags, &source.source, &source.hierarchy);

        check_diags(py, &source.source, &diags)?;
        drop(source);

        Ok(Parsed { source: slf, parsed })
    }

    /// Shortcut for `self.parse().compile()`.
    fn compile(slf: Py<Self>, py: Python) -> PyResult<Compile> {
        let parsed = Self::parse(slf, py)?;
        let py_parsed = Py::new(py, parsed)?;
        Parsed::compile(py_parsed, py)
    }
}

const COMPILE_SETTINGS: CompileSettings = CompileSettings { do_ir_cleanup: true };

#[pymethods]
impl Parsed {
    fn compile(slf: Py<Self>, py: Python) -> PyResult<Compile> {
        let shared = {
            let diags = Diagnostics::new();
            let parsed = slf.borrow(py);
            let source = parsed.source.borrow(py);
            let fixed = CompileFixed {
                settings: &COMPILE_SETTINGS,
                source: &source.source,
                hierarchy: &source.hierarchy,
                parsed: &parsed.parsed,
            };

            // TODO add parameter for queue_all_items, default to true and then set to false for specific tests
            //   then run initial elaboration loop immediately
            let shared = CompileShared::new(&diags, fixed, QueueItems::None, NON_ZERO_USIZE_ONE);
            check_diags(py, &source.source, &diags)?;

            shared
        };

        // TODO make threadpool configurable
        Ok(Compile {
            pool: None,
            parsed: slf,
            shared,
            capture_prints: None,
        })
    }
}

#[pymethods]
impl Compile {
    fn resolve_module(slf: Py<Self>, py: Python, path: &str) -> PyResult<Py<Module>> {
        let value = Self::resolve_impl(&slf, py, path)?;
        if let RustCompileValue::Simple(SimpleCompileValue::Module(_)) = value {
            return compile_value_to_py(py, &slf, &value)?
                .bind(py)
                .extract::<Py<Module>>()
                .map_err(PyErr::from);
        }

        // report error with the actual value type
        let compile = slf.borrow(py);
        let parsed_ref = compile.parsed.borrow(py);
        let source_ref = parsed_ref.source.borrow(py);
        let refs = StringRefs {
            hierarchy: &source_ref.hierarchy,
            interner: &compile.shared.interner,
            elab: &compile.shared.elaboration_arenas,
        };
        let ty_str = value.ty().value_string(refs);
        Err(PyTypeError::new_err(format!(
            "path `{path}` does not resolve to a module, got value with type `{ty_str}`"
        )))
    }

    fn resolve(slf: Py<Self>, py: Python, path: &str) -> PyResult<Py<PyAny>> {
        let value = Self::resolve_impl(&slf, py, path)?;
        compile_value_to_py(py, &slf, &value)
    }

    #[pyo3(signature=(capture=None))]
    fn capture_prints(
        slf: Py<Self>,
        py: Python,
        capture: Option<Py<CapturePrints>>,
    ) -> PyResult<Py<CapturePrintsContext>> {
        let capture = match capture {
            Some(capture) => capture,
            None => Py::new(py, CapturePrints::new())?,
        };
        Py::new(
            py,
            CapturePrintsContext {
                compile: slf,
                capture,
                prev_capture: None,
            },
        )
    }
}

struct PyPrintHandler {
    collect_print_handler: Option<CollectPrintHandler>,
}

impl PyPrintHandler {
    fn handler(&self) -> &(dyn PrintHandler + Sync) {
        match &self.collect_print_handler {
            None => &StdoutPrintHandler,
            Some(handler) => handler,
        }
    }
}

impl Compile {
    fn resolve_impl(slf: &Py<Self>, py: Python, path: &str) -> PyResult<RustCompileValue> {
        // unwrap self
        let slf_ref = &mut *slf.borrow_mut(py);
        let shared = &slf_ref.shared;

        let parsed_ref = slf_ref.parsed.borrow(py);
        let parsed = &parsed_ref.parsed;
        let source_ref = parsed_ref.source.borrow(py);
        let source = &source_ref.source;
        let hierarchy = &source_ref.hierarchy;
        let dummy_span = source_ref.dummy_span;

        let diags = Diagnostics::new();
        let print_handler = slf_ref.start_collect_prints();
        let refs = CompileRefs {
            fixed: CompileFixed {
                settings: &COMPILE_SETTINGS,
                source,
                hierarchy,
                parsed,
            },
            shared,
            diags: &diags,
            print_handler: print_handler.handler(),
            should_stop: &|| false,
            interrupted_local: &OnceLock::new(),
        };

        // resolve the path, python can always access private items for now
        let resolved = refs.resolve_path(Spanned::new(dummy_span, path), true);
        let resolved = map_diag_error(py, &diags, source, resolved)?;

        // eval value and elaborate any necessary items
        let mut item_ctx = CompileItemContext::new_empty(refs, None, None);
        let value = item_ctx.eval_import_value(resolved);
        refs.run_compile_loop(None);

        // build ir database to run final checks
        let ir_database = if value.is_ok() {
            shared.finish_ir_database_ref(&diags, dummy_span).map(|_| ())
        } else {
            Ok(())
        };

        // propagate errors
        let value = map_diag_error(py, &diags, source, value);
        let database = map_diag_error(py, &diags, source, ir_database);
        let result_diags = check_diags(py, source, &diags);

        drop(source_ref);
        drop(parsed_ref);
        slf_ref.finish_collect_prints(py, print_handler);

        let value = value?;
        database?;
        result_diags?;

        Ok(value)
    }

    fn start_collect_prints(&self) -> PyPrintHandler {
        let collect_print_handler = self.capture_prints.as_ref().map(|_| CollectPrintHandler::new());
        PyPrintHandler { collect_print_handler }
    }

    fn finish_collect_prints(&mut self, py: Python, handler: PyPrintHandler) {
        let PyPrintHandler { collect_print_handler } = handler;

        if let Some(capture) = &self.capture_prints {
            if let Some(handler) = collect_print_handler {
                capture.borrow_mut(py).prints.extend(handler.finish());
            }
        }
    }
}

#[pymethods]
impl CapturePrints {
    #[new]
    fn new() -> Self {
        CapturePrints { prints: Vec::new() }
    }
}

#[pymethods]
impl CapturePrintsContext {
    fn __enter__(&mut self, py: Python) -> PyResult<Py<CapturePrints>> {
        let compile = self.compile.clone_ref(py);
        let mut compile = compile.borrow_mut(py);

        // replace the capture destination, keep the previous one to restore later so nesting works properly
        self.prev_capture = Option::replace(&mut compile.capture_prints, self.capture.clone_ref(py));

        // return the capture object for convenience, so the user can bind it
        Ok(self.capture.clone_ref(py))
    }

    fn __exit__(
        &mut self,
        py: Python,
        _exc_type: Option<&Bound<PyAny>>,
        _exc_value: Option<&Bound<PyAny>>,
        _traceback: Option<&Bound<PyAny>>,
    ) -> PyResult<bool> {
        let mut compile = self.compile.borrow_mut(py);

        // restore previous capture destination
        compile.capture_prints = Option::take(&mut self.prev_capture);

        // do not suppress exceptions
        Ok(false)
    }
}

#[pymethods]
impl Value {
    fn __repr__(&self, py: Python) -> String {
        let compile = self.compile.borrow(py);
        let parsed_ref = compile.parsed.borrow(py);
        let source_ref = parsed_ref.source.borrow(py);

        let refs = StringRefs {
            hierarchy: &source_ref.hierarchy,
            interner: &compile.shared.interner,
            elab: &compile.shared.elaboration_arenas,
        };
        self.value.value_string(refs)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match compile_value_from_py(other, Some(&self.compile)) {
            Ok(other) => self.value == other,
            Err(_) => false,
        }
    }

    fn __ne__(&self, other: &Bound<'_, PyAny>) -> bool {
        !self.__eq__(other)
    }

    #[pyo3(signature=(*args, **kwargs))]
    fn __call__(
        &self,
        py: Python,
        args: &Bound<'_, PyTuple>,
        kwargs: Option<&Bound<'_, PyDict>>,
    ) -> PyResult<Py<PyAny>> {
        // borrow self
        let compile_ref = &mut *self.compile.borrow_mut(py);
        let print_handler = compile_ref.start_collect_prints();

        let shared = &mut compile_ref.shared;
        let parsed_ref = compile_ref.parsed.borrow(py);
        let parsed = &parsed_ref.parsed;
        let source_ref = parsed_ref.source.borrow(py);
        let source = &source_ref.source;
        let hierarchy = &source_ref.hierarchy;
        let dummy_span = source_ref.dummy_span;

        // convert target and args
        let target = RustValue::from(self.value.clone());
        let args = convert_python_args_and_kwargs_to_args(&self.compile, &shared.interner, args, kwargs, dummy_span)?;

        // prepare context
        let diags = Diagnostics::new();
        let refs = CompileRefs {
            fixed: CompileFixed {
                settings: &COMPILE_SETTINGS,
                source,
                hierarchy,
                parsed,
            },
            shared,
            diags: &diags,
            print_handler: print_handler.handler(),
            should_stop: &|| false,
            interrupted_local: &OnceLock::new(),
        };

        let mut item_ctx = CompileItemContext::new_empty(refs, None, None);
        let flow_root = FlowRoot::new(&diags, &shared.next_flow_root_id);
        let mut flow = FlowCompile::new_root(&flow_root, dummy_span, "external call");

        // call the function and run any elaboration that is needed
        // TODO release GIL
        let returned = item_ctx.eval_call(
            &mut flow,
            &RustType::Any,
            dummy_span,
            Spanned::new(dummy_span, &target),
            CallArgs::Evaluated(args),
        );
        refs.run_compile_loop(compile_ref.pool.as_ref());

        // extract return value
        let returned = returned.and_then(|returned| {
            RustCompileValue::try_from(&returned).map_err(|_: NotCompile| {
                diags.report_error_internal(dummy_span, "compile-time call return non-compile value")
            })
        });
        let returned = map_diag_error(py, &diags, source, returned);

        // finish up
        drop(source_ref);
        drop(parsed_ref);
        compile_ref.finish_collect_prints(py, print_handler);

        let returned = returned?;
        compile_value_to_py(py, &self.compile, &returned)
    }

    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<Py<PyAny>> {
        // return normal attribute error for builtins, we especially don't want to mess with those
        // TODO should we convert all errors to attribute errors here?
        if attr.starts_with("__") && attr.ends_with("__") {
            return Err(PyAttributeError::new_err(format!(
                "`Value` object has no attribute `{attr}`"
            )));
        }

        // TODO reduce code duplication with other thing that need the full compilation context
        // unwrap self
        let compile = &mut *self.compile.borrow_mut(py);
        let shared = &compile.shared;

        let parsed_ref = compile.parsed.borrow(py);
        let parsed = &parsed_ref.parsed;
        let source_ref = parsed_ref.source.borrow(py);
        let source = &source_ref.source;
        let hierarchy = &source_ref.hierarchy;
        let dummy_span = source_ref.dummy_span;

        // build context
        let diags = Diagnostics::new();
        let print_handler = compile.start_collect_prints();
        let refs = CompileRefs {
            fixed: CompileFixed {
                settings: &COMPILE_SETTINGS,
                source,
                hierarchy,
                parsed,
            },
            shared,
            diags: &diags,
            print_handler: print_handler.handler(),
            should_stop: &|| false,
            interrupted_local: &OnceLock::new(),
        };
        let mut item_ctx = CompileItemContext::new_empty(refs, None, None);

        // evaluate dot index
        // TODO release GIL
        let base = Spanned::new(dummy_span, self.value.clone());
        let step = TargetStepCompile::DotIndexId(shared.interner.push(attr));
        let step = SpannedStep {
            span_full: dummy_span,
            span_step: dummy_span,
            step: &step,
        };
        let steps = TargetSteps::new(vec![step]);
        let result = steps.apply_to_compile_value(&mut item_ctx, base);
        refs.run_compile_loop(compile.pool.as_ref());

        // handle result
        let result_diags = result.is_ok().then(|| check_diags(py, source, &diags));

        drop(source_ref);
        drop(parsed_ref);
        compile.finish_collect_prints(py, print_handler);

        let result =
            result.map_err(|_| PyAttributeError::new_err(format!("`Value` object has no attribute `{attr}`")))?;
        result_diags.transpose()?;

        compile_value_to_py(py, &self.compile, &result)
    }
}

#[pymethods]
impl StructValue {
    #[getter]
    fn fields(slf: PyRef<Self>, py: Python) -> PyResult<Py<PyDict>> {
        let value = &slf.value;
        let base = slf.as_super();

        let names = {
            let compile = base.compile.borrow(py);
            let shared = &compile.shared;
            let info = shared.elaboration_arenas.struct_info(value.ty);
            info.fields
                .keys()
                .map(|id| id.str(&shared.interner).to_owned())
                .collect_vec()
        };

        let result = PyDict::new(py);
        for (name, field) in zip_eq(names, &value.fields) {
            result.set_item(name, compile_value_to_py(py, &base.compile, field)?)?;
        }
        Ok(result.unbind())
    }
}

#[pymethods]
impl EnumValue {
    #[getter]
    fn tag(slf: PyRef<Self>, py: Python) -> PyResult<String> {
        let value = &slf.value;
        let compile = slf.as_super().compile.borrow(py);
        let shared = &compile.shared;
        let info = shared.elaboration_arenas.enum_info(value.ty);
        let (&id, _) = info
            .variants
            .get_index(value.variant)
            .ok_or_else(|| PyException::new_err("internal error: enum variant out of range"))?;
        Ok(id.str(&shared.interner).to_owned())
    }

    #[getter]
    fn payload(slf: PyRef<Self>, py: Python) -> PyResult<Option<Py<PyAny>>> {
        let compile = &slf.as_super().compile;
        slf.value
            .payload
            .as_ref()
            .map(|payload| compile_value_to_py(py, compile, payload))
            .transpose()
    }
}

#[pymethods]
impl Range {
    #[new]
    fn new(start: Option<num_bigint::BigInt>, end: Option<num_bigint::BigInt>) -> PyResult<Range> {
        let start = start.map(BigInt::from_num_bigint);
        let end = end.map(BigInt::from_num_bigint);

        if let (Some(start), Some(end)) = (&start, &end) {
            #[allow(clippy::nonminimal_bool)]
            if !(start <= end) {
                return Err(PyValueError::new_err("Range requires `start <= end`"));
            }
        }

        let range = RustRange { start, end };
        Ok(Range { range })
    }

    #[getter]
    fn start(&self) -> Option<num_bigint::BigInt> {
        self.range.start.as_ref().map(|b| b.clone().into_num_bigint())
    }

    #[getter]
    fn end(&self) -> Option<num_bigint::BigInt> {
        self.range.end.as_ref().map(|b| b.clone().into_num_bigint())
    }

    fn contains(&self, value: num_bigint::BigInt) -> bool {
        let value = BigInt::from_num_bigint(value);
        self.range.contains(&value)
    }

    fn contains_range(&self, other: &Range) -> bool {
        self.range.contains_range(other.range.as_ref())
    }

    fn __str__(&self) -> String {
        format!("Range({})", self.range)
    }
}

#[pymethods]
impl Module {
    #[allow(clippy::wrong_self_convention)]
    fn as_verilog(slf: Py<Self>, py: Python) -> PyResult<ModuleVerilog> {
        let (_, ir_module, lowered) = Self::lower_verilog_impl(&slf, py)?;
        let verilog_name = lowered.module_to_lowered_name.get(&ir_module).unwrap();

        Ok(ModuleVerilog {
            module_name: verilog_name.to_owned(),
            source: lowered.source,
        })
    }

    #[allow(clippy::wrong_self_convention)]
    #[pyo3(signature=(build_dir, *, extra_verilog_files=None, optimization=None, compiler=None, jobs=None))]
    fn as_verilated(
        slf: Py<Self>,
        py: Python,
        build_dir: PathBuf,
        extra_verilog_files: Option<Vec<PathBuf>>,
        optimization: Option<u8>,
        compiler: Option<String>,
        jobs: Option<NonZeroUsize>,
    ) -> PyResult<ModuleVerilated> {
        // handle args
        let extra_verilog_files = extra_verilog_files.unwrap_or_default();
        if optimization.is_some_and(|level| level > 3) {
            return Err(PyValueError::new_err("Verilator optimization must be between 0 and 3"));
        }
        let jobs = jobs.unwrap_or_else(get_num_cpus);

        // Select code-generation workarounds, C++ driver, and matching PCH
        // settings together; Verilator's configured defaults may use another compiler.
        // None preserves the existing toolchain selection and Make overrides.
        let compiler = match compiler.as_deref() {
            None => None,
            Some("gcc") => Some(("gcc", "g++", "-include", "")),
            Some("clang") => Some(("clang", "clang++", "-include-pch", ".gch")),
            Some(_) => return Err(PyValueError::new_err("Verilator compiler must be 'gcc' or 'clang'")),
        };

        // create build_dir
        let build_dir = build_dir.as_path();
        std::fs::create_dir_all(build_dir).map_err(|e| io_error(e.with_context(IoAction::CreateDir, build_dir)))?;

        // lower
        let (ir_database, ir_module, lowered_verilog) = Self::lower_verilog_impl(&slf, py)?;
        let lowered_verilator = lower_verilator(&ir_database.modules, ir_module, &lowered_verilog);

        let LoweredVerilog {
            source: source_verilog,
            module_to_lowered_name,
        } = lowered_verilog;
        let LoweredVerilator {
            source: source_cpp,
            top_class_name,
            check_hash,
        } = lowered_verilator;

        let verilog_name = module_to_lowered_name.get(&ir_module).unwrap();

        // write to files
        // TODO only write if changed to avoid unnecessary rebuilds? or does verilator already do that for us?
        let name_verilog = "lowered.v";
        write_file(&build_dir.join(name_verilog), &source_verilog)?;
        let name_cpp = "lowered.cpp";
        write_file(&build_dir.join(name_cpp), &source_cpp)?;

        // verilate
        // pick a random so file to avoid later `dlopen` calls hitting a stale cache
        let name_so = format!("combined-{:016x}.so", rand::random::<u64>());
        let obj_dir = build_dir.join("obj_dir");
        let path_so = obj_dir.join(&name_so);

        py.detach::<PyResult<()>, _>(|| {
            // TODO get everything properly incremental
            // TODO make tracing optional
            // TODO move this compilation process to somewhere else, not in the python crate
            run_command(
                Command::new("verilator")
                    // C++ compiler settings
                    .args(compiler.into_iter().flat_map(|(name, ..)| ["--compiler", name]))
                    .args(optimization.map(|level| format!("-O{level}")))
                    .arg("-cc")
                    .args(["-CFLAGS", "-fPIC"])
                    // enforce Verilog 2005 to check that we don't accidentally use newer language features
                    .args(["--language", "1364-2005"])
                    // the backend sometimes intentionally uses these
                    .arg("-Wno-WIDTHTRUNC")
                    .arg("-Wno-WIDTHEXPAND")
                    .arg("-Wno-UNSIGNED")
                    .arg("-Wno-CMPCONST")
                    // error on some sketchy constructions
                    .arg("-Werror-IMPLICIT")
                    .arg("-Werror-PINMISSING")
                    // misc settings
                    .arg("--trace")
                    .args(["--top-module", verilog_name])
                    .args(["--prefix", &top_class_name])
                    // source files
                    .args(extra_verilog_files)
                    .arg(name_verilog)
                    .arg(name_cpp),
                build_dir,
                "verilator",
            )?;

            // compile and link
            let name_mk = "combined.mk";
            let source_mk = format!(
                "include {top_class_name}.mk\n\n\
                 {name_so}: $(VK_OBJS) $(VK_USER_OBJS) $(VK_GLOBAL_OBJS)\n\
                 \t$(LINK) $(LDFLAGS) $^ -o $@ -shared $(LDLIBS)\n"
            );
            write_file(&obj_dir.join(name_mk), &source_mk)?;

            // TODO use faster linker
            run_command(
                Command::new("make")
                    .arg("-f")
                    .arg(name_mk)
                    .arg("-j")
                    .arg(jobs.to_string())
                    .args(compiler.into_iter().flat_map(|(_, driver, pch_include, pch_suffix)| {
                        [
                            format!("CXX={driver}"),
                            format!("LINK={driver}"),
                            format!("CFG_CXXFLAGS_PCH_I={pch_include}"),
                            format!("CFG_GCH_IF_CLANG={pch_suffix}"),
                        ]
                    }))
                    .arg(&name_so),
                &obj_dir,
                "make",
            )?;

            Ok(())
        })?;

        // load library
        let lib = unsafe {
            VerilatedLib::new(&ir_database.modules, ir_module, check_hash, &path_so)
                .map_err(|e| VerilationException::new_err(format!("lib loading failed: {e}")))?
        };
        Ok(ModuleVerilated {
            compile: slf.bind(py).as_super().borrow().compile.clone_ref(py),
            lib,
        })
    }
}

// TODO include stderr in the error message
//   https://users.rust-lang.org/t/best-error-handing-practices-when-using-std-command/42259
fn io_error(e: IoErrorWithPath) -> PyErr {
    PyIOError::new_err(e.to_string())
}

fn write_file(path: &Path, content: &str) -> PyResult<()> {
    std::fs::write(path, content).map_err(|e| io_error(e.with_context(IoAction::Write, path)))
}

fn run_command(command: &mut Command, dir: &Path, name: &str) -> PyResult<()> {
    let status = command
        .current_dir(dir)
        .stdout(Stdio::null())
        .status()
        .map_err(|e| VerilationException::new_err(format!("`{name}` failed to launch: error={e:?}")))?;

    if !status.success() {
        return Err(VerilationException::new_err(format!(
            "`{name}` failed: code={:?}",
            status.code()
        )));
    }

    Ok(())
}

impl Module {
    fn lower_verilog_impl(slf: &Py<Self>, py: Python) -> PyResult<(IrDatabase, IrModule, LoweredVerilog)> {
        // borrow self
        let module = slf.bind(py).borrow().module;
        let slf = slf.bind(py).as_super().borrow();
        let compile = slf.compile.borrow(py);
        let parsed_ref = compile.parsed.borrow(py);
        let source_ref = parsed_ref.source.borrow(py);
        let source = &source_ref.source;
        let dummy_span = source_ref.dummy_span;

        // get the module
        let module = match module {
            ElaboratedModule::Internal(module) => module,
            ElaboratedModule::External(_) => {
                return Err(GenerateVerilogException::new_err(
                    "cannot generate verilog for external module",
                ));
            }
        };
        let ir_module = compile.shared.elaboration_arenas.module_internal_info(module).module_ir;

        // create temporary ir database
        // TODO rework the IrDatabase API, this is a mess
        let diags = Diagnostics::new();
        let ir_database = compile.shared.finish_ir_database_ref(&diags, dummy_span);
        let ir_database = map_diag_error(py, &diags, source, ir_database)?;

        if cfg!(debug_assertions) {
            let validate_result = ir_database.validate(&diags);
            map_diag_error(py, &diags, source, validate_result)?;
        }

        // actual lowering
        let lowered = lower_to_verilog(&diags, &ir_database, &[ir_module]);
        let lowered = map_diag_error(py, &diags, source, lowered)?;

        Ok((ir_database, ir_module, lowered))
    }
}

#[pymethods]
impl ModuleVerilated {
    #[pyo3(signature=(trace_path=None))]
    fn instance(slf: Py<Self>, trace_path: Option<&str>, py: Python) -> PyResult<VerilatedInstance> {
        let instance = slf
            .borrow(py)
            .lib
            .instance(trace_path.map(Path::new))
            .map_err(map_verilator_error)?;
        Ok(VerilatedInstance {
            module: slf.clone_ref(py),
            instance,
        })
    }
}

#[pymethods]
impl VerilatedInstance {
    #[getter]
    fn ports(slf: Py<Self>) -> VerilatedPorts {
        VerilatedPorts { instance: slf }
    }

    #[getter]
    fn info_ports(slf: Py<Self>) -> VerilatedInfoPorts {
        VerilatedInfoPorts { instance: slf }
    }

    #[getter]
    fn info_ports_flat(slf: Py<Self>) -> VerilatedInfoPortsFlat {
        VerilatedInfoPortsFlat { instance: slf }
    }

    fn step(&mut self, increment_time: u64) -> PyResult<()> {
        let instance = &mut self.instance;
        let finished = instance.step(increment_time).map_err(map_verilator_error)?;

        match finished {
            SimulationFinished::No => Ok(()),
            SimulationFinished::Yes => Err(SimulationFinishedException::new_err("simulation has finished")),
        }
    }

    fn save_trace(&mut self) {
        self.instance.save_trace();
    }
}

#[pymethods]
impl VerilatedPorts {
    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<Py<PyAny>> {
        get_declared_port(py, &self.instance, PortsKind::Values, attr)
    }

    fn __getitem__(&self, key: &str, py: Python) -> PyResult<Py<PyAny>> {
        get_declared_port(py, &self.instance, PortsKind::Values, key)
    }

    fn __setattr__(&self, attr: &str, value: &Bound<PyAny>) -> PyResult<()> {
        self.set_port(attr, &format!("ports.{attr}"), value)
    }

    fn __setitem__(&self, key: &str, value: &Bound<PyAny>) -> PyResult<()> {
        self.set_port(key, &format!("ports[\"{key}\"]"), value)
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        declared_port_names(py, &self.instance)
    }
}

impl VerilatedPorts {
    fn set_port(&self, name: &str, path: &str, value: &Bound<PyAny>) -> PyResult<()> {
        let py = value.py();
        let port = match find_declared_port(py, &self.instance, name)? {
            IrPortDeclared::Single(port) => port,
            IrPortDeclared::Interface(_) => return Err(err_set_interface(path)),
        };
        set_port_value(&self.instance, port, value)
    }
}

#[pymethods]
impl VerilatedInfoPorts {
    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<Py<PyAny>> {
        get_declared_port(py, &self.instance, PortsKind::Info, attr)
    }

    fn __getitem__(&self, key: &str, py: Python) -> PyResult<Py<PyAny>> {
        get_declared_port(py, &self.instance, PortsKind::Info, key)
    }

    fn __setattr__(&self, attr: &str, value: Py<PyAny>, py: Python) -> PyResult<()> {
        let _ = find_declared_port(py, &self.instance, attr)?;
        let _ = value;
        Err(err_set_info(&format!("info_ports.{attr}")))
    }

    fn __setitem__(&self, key: &str, value: Py<PyAny>, py: Python) -> PyResult<()> {
        let _ = find_declared_port(py, &self.instance, key)?;
        let _ = value;
        Err(err_set_info(&format!("info_ports[\"{key}\"]")))
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        declared_port_names(py, &self.instance)
    }
}

#[pymethods]
impl VerilatedInfoPortsFlat {
    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<VerilatedInfoPort> {
        let port = self.get_port(attr, py)?;
        Ok(VerilatedInfoPort {
            instance: self.instance.clone_ref(py),
            port,
        })
    }

    fn __getitem__(&self, key: &str, py: Python) -> PyResult<VerilatedInfoPort> {
        self.__getattr__(key, py)
    }

    fn __setattr__(&self, attr: &str, value: Py<PyAny>, py: Python) -> PyResult<()> {
        let _ = self.get_port(attr, py)?;
        let _ = value;
        Err(err_set_info(&format!("info_ports_flat.{attr}")))
    }

    fn __setitem__(&self, key: &str, value: Py<PyAny>, py: Python) -> PyResult<()> {
        let _ = self.get_port(key, py)?;
        let _ = value;
        Err(err_set_info(&format!("info_ports_flat[\"{key}\"]")))
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        let names = self
            .instance
            .borrow(py)
            .instance
            .ports_named()
            .keys()
            .cloned()
            .collect_vec();
        names.into_pyobject(py)?.try_iter()
    }
}

impl VerilatedInfoPortsFlat {
    fn get_port(&self, name: &str, py: Python) -> PyResult<IrPort> {
        let instance = &self.instance.borrow(py).instance;
        instance
            .ports_named()
            .get(name)
            .copied()
            .ok_or_else(|| PyAttributeError::new_err(format!("port `{name}` not found")))
    }
}

fn find_declared_port(py: Python, instance: &Py<VerilatedInstance>, name: &str) -> PyResult<IrPortDeclared> {
    instance
        .borrow(py)
        .instance
        .ports_declared()
        .get(name)
        .cloned()
        .ok_or_else(|| PyAttributeError::new_err(format!("port `{name}` not found")))
}

fn get_declared_port(py: Python, instance: &Py<VerilatedInstance>, kind: PortsKind, name: &str) -> PyResult<Py<PyAny>> {
    match find_declared_port(py, instance, name)? {
        IrPortDeclared::Single(port) => port_to_py(py, instance, kind, port),
        IrPortDeclared::Interface(elements) => {
            let path = format!("{}.{name}", kind.root());
            interface_elements_to_py(py, instance, kind, path, &elements)
        }
    }
}

fn declared_port_names<'py>(py: Python<'py>, instance: &Py<VerilatedInstance>) -> PyResult<Bound<'py, PyIterator>> {
    let names = instance
        .borrow(py)
        .instance
        .ports_declared()
        .keys()
        .cloned()
        .collect_vec();
    names.into_pyobject(py)?.try_iter()
}

#[pymethods]
impl VerilatedInterface {
    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<Py<PyAny>> {
        self.inner.get(py, attr)
    }

    fn __getitem__(&self, key: &str, py: Python) -> PyResult<Py<PyAny>> {
        self.inner.get(py, key)
    }

    fn __setattr__(&self, attr: &str, value: &Bound<PyAny>) -> PyResult<()> {
        let port = self.inner.get_port(attr)?;
        set_port_value(&self.inner.instance, port, value)
    }

    fn __setitem__(&self, key: &str, value: &Bound<PyAny>) -> PyResult<()> {
        let port = self.inner.get_port(key)?;
        set_port_value(&self.inner.instance, port, value)
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        self.inner.names(py)
    }

    fn __repr__(&self) -> String {
        format!("VerilatedInterface({})", self.inner.path)
    }
}

#[pymethods]
impl VerilatedInfoInterface {
    fn __getattr__(&self, attr: &str, py: Python) -> PyResult<Py<PyAny>> {
        self.inner.get(py, attr)
    }

    fn __getitem__(&self, key: &str, py: Python) -> PyResult<Py<PyAny>> {
        self.inner.get(py, key)
    }

    fn __setattr__(&self, attr: &str, value: Py<PyAny>) -> PyResult<()> {
        let _ = self.inner.get_port(attr)?;
        let _ = value;
        Err(err_set_info(&format!("{}.{attr}", self.inner.path)))
    }

    fn __setitem__(&self, key: &str, value: Py<PyAny>) -> PyResult<()> {
        let _ = self.inner.get_port(key)?;
        let _ = value;
        Err(err_set_info(&format!("{}[\"{key}\"]", self.inner.path)))
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        self.inner.names(py)
    }

    fn __repr__(&self) -> String {
        format!("VerilatedInfoInterface({})", self.inner.path)
    }
}

impl InterfaceSelection {
    fn get_port(&self, name: &str) -> PyResult<IrPort> {
        self.ports
            .get(name)
            .copied()
            .ok_or_else(|| PyAttributeError::new_err(format!("interface `{}` does not have port `{name}`", self.path)))
    }

    fn get(&self, py: Python, name: &str) -> PyResult<Py<PyAny>> {
        let port = self.get_port(name)?;
        port_to_py(py, &self.instance, self.kind, port)
    }

    fn names<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        let names = self.ports.keys().cloned().collect_vec();
        names.into_pyobject(py)?.try_iter()
    }

    fn into_py(self, py: Python) -> PyResult<Py<PyAny>> {
        match self.kind {
            PortsKind::Values => VerilatedInterface { inner: self }.into_py_any(py),
            PortsKind::Info => VerilatedInfoInterface { inner: self }.into_py_any(py),
        }
    }
}

#[pymethods]
impl VerilatedInterfaceArray {
    #[getter]
    fn shape<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        self.inner.shape(py)
    }

    fn __getitem__(&self, index: &Bound<PyAny>) -> PyResult<Py<PyAny>> {
        self.inner.get_item(index)
    }

    fn __len__(&self) -> usize {
        self.inner.indices.len()
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        self.inner.iter(py)
    }

    fn __repr__(&self) -> String {
        format!("VerilatedInterfaceArray([{}])", self.inner.element_paths())
    }
}

#[pymethods]
impl VerilatedInfoInterfaceArray {
    #[getter]
    fn shape<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        self.inner.shape(py)
    }

    fn __getitem__(&self, index: &Bound<PyAny>) -> PyResult<Py<PyAny>> {
        self.inner.get_item(index)
    }

    fn __len__(&self) -> usize {
        self.inner.indices.len()
    }

    fn __iter__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        self.inner.iter(py)
    }

    fn __repr__(&self) -> String {
        format!("VerilatedInfoInterfaceArray([{}])", self.inner.element_paths())
    }
}

impl InterfaceArraySelection {
    fn get_item(&self, index: &Bound<PyAny>) -> PyResult<Py<PyAny>> {
        let py = index.py();
        let len = self.indices.len();

        // handle index
        if let Ok(index) = index.extract::<isize>() {
            let index_positive = if index < 0 { index + len as isize } else { index };
            let index_inner = usize::try_from(index_positive)
                .ok()
                .and_then(|i| self.indices.get(i))
                .ok_or_else(|| {
                    PyIndexError::new_err(format!(
                        "index {index} out of range for interface array with length {len}"
                    ))
                })?;
            return self.get_element(py, *index_inner);
        }

        // handle slice
        if let Ok(slice) = index.cast::<PySlice>() {
            let PySliceIndices {
                start,
                stop: _,
                step,
                slicelength,
            } = slice.indices(len as isize)?;
            let indices = (0..slicelength)
                .map(|i| self.indices[(start + i as isize * step) as usize])
                .collect();

            let result = InterfaceArraySelection {
                instance: self.instance.clone_ref(py),
                kind: self.kind,
                path: self.path.clone(),
                elements: self.elements.clone(),
                indices,
            };
            return result.into_py(py);
        }

        // error
        let msg = format!(
            "interface array indices must be integers or slices, not `{}`",
            index.get_type()
        );
        Err(PyTypeError::new_err(msg))
    }

    fn iter<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyIterator>> {
        let elements: Vec<_> = self.indices.iter().map(|&i| self.get_element(py, i)).try_collect()?;
        elements.into_pyobject(py)?.try_iter()
    }

    fn shape<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        let rest = match self.elements.shape() {
            NdArrayShape::Scalar => &[][..],
            NdArrayShape::Array { first: _, rest } => rest,
        };
        PyTuple::new(py, chain([self.indices.len()], rest.iter().copied()).collect_vec())
    }

    fn element_paths(&self) -> String {
        self.indices.iter().map(|i| format!("{}[{i}]", self.path)).join(", ")
    }

    fn get_element(&self, py: Python, index_inner: usize) -> PyResult<Py<PyAny>> {
        let element = self.elements.step_index(index_inner).unwrap();
        let path = format!("{}[{index_inner}]", self.path);
        interface_elements_to_py(py, &self.instance, self.kind, path, &element)
    }

    fn into_py(self, py: Python) -> PyResult<Py<PyAny>> {
        match self.kind {
            PortsKind::Values => VerilatedInterfaceArray { inner: self }.into_py_any(py),
            PortsKind::Info => VerilatedInfoInterfaceArray { inner: self }.into_py_any(py),
        }
    }
}

impl PortsKind {
    fn root(self) -> &'static str {
        match self {
            PortsKind::Values => "ports",
            PortsKind::Info => "info_ports",
        }
    }
}

fn interface_elements_to_py(
    py: Python,
    instance: &Py<VerilatedInstance>,
    kind: PortsKind,
    path: String,
    elements: &NdArray<IndexMap<String, IrPort>>,
) -> PyResult<Py<PyAny>> {
    let instance = instance.clone_ref(py);
    match elements.first_len() {
        None => {
            let result = InterfaceSelection {
                instance,
                kind,
                path,
                ports: elements.as_single().unwrap().clone(),
            };
            result.into_py(py)
        }
        Some(len) => {
            let result = InterfaceArraySelection {
                instance,
                kind,
                path,
                elements: elements.clone(),
                indices: (0..len).collect(),
            };
            result.into_py(py)
        }
    }
}

fn port_to_py(py: Python, instance: &Py<VerilatedInstance>, kind: PortsKind, port: IrPort) -> PyResult<Py<PyAny>> {
    match kind {
        PortsKind::Values => get_port_value(py, instance, port),
        PortsKind::Info => VerilatedInfoPort {
            instance: instance.clone_ref(py),
            port,
        }
        .into_py_any(py),
    }
}

fn err_set_interface(path: &str) -> PyErr {
    PyValueError::new_err(format!(
        "cannot set interface `{path}` directly, set its individual ports instead"
    ))
}

fn err_set_info(path: &str) -> PyErr {
    PyValueError::new_err(format!(
        "cannot set port info `{path}`, set port values through `ports` instead"
    ))
}

fn get_port_value(py: Python, instance: &Py<VerilatedInstance>, port: IrPort) -> PyResult<Py<PyAny>> {
    let instance = instance.borrow(py);
    let compile = &instance.module.borrow(py).compile;

    let value = instance.instance.get_port(port).map_err(map_verilator_error)?;
    compile_value_to_py(py, compile, &value)
}

fn set_port_value(instance: &Py<VerilatedInstance>, port: IrPort, value: &Bound<PyAny>) -> PyResult<()> {
    let py = value.py();
    let compile = instance.borrow(py).module.borrow(py).compile.clone_ref(py);
    let value = compile_value_from_py(value, Some(&compile))?;

    let instance = &mut *instance.borrow_mut(py);
    let module = instance.module.borrow(py);
    let compile = &mut *module.compile.borrow_mut(py);
    let parsed = compile.parsed.borrow(py);
    let source = parsed.source.borrow(py);

    let dummy_span = source.dummy_span;

    let diags = Diagnostics::new();
    let print_handler = compile.start_collect_prints();
    let refs = CompileRefs {
        fixed: CompileFixed {
            settings: &COMPILE_SETTINGS,
            source: &source.source,
            hierarchy: &source.hierarchy,
            parsed: &parsed.parsed,
        },
        shared: &compile.shared,
        diags: &diags,
        print_handler: print_handler.handler(),
        should_stop: &|| false,
        interrupted_local: &OnceLock::new(),
    };
    let result = instance.instance.set_port(refs, port, Spanned::new(dummy_span, &value));

    let result = result.map_err(|e| match e {
        Either::Left(e) => map_verilator_error(e),
        Either::Right(e) => convert_diag_error(py, &diags, &source.source, e),
    });
    let result_diags = check_diags(py, &source.source, &diags);

    drop(source);
    drop(parsed);
    compile.finish_collect_prints(py, print_handler);

    result?;
    result_diags
}

#[pymethods]
impl VerilatedInfoPort {
    #[getter]
    fn r#type(&self, py: Python) -> Value {
        let ty = self.map_port_info(py, |info| info.ty.clone()).as_type_hw().as_type();
        Value {
            compile: self.instance.borrow(py).module.borrow(py).compile.clone_ref(py),
            value: RustValue::new_ty(ty),
        }
    }

    #[getter]
    fn name(&self, py: Python) -> String {
        self.map_port_info(py, |info| info.name.clone())
    }

    #[getter]
    fn direction(&self, py: Python) -> &'static str {
        self.map_port_info(py, |info| info.direction.diagnostic_string())
    }

    #[getter]
    fn value(&self, py: Python) -> PyResult<Py<PyAny>> {
        get_port_value(py, &self.instance, self.port)
    }

    #[setter]
    fn set_value(&self, value: &Bound<PyAny>) -> PyResult<()> {
        set_port_value(&self.instance, self.port, value)
    }

    fn __bool__(&self) -> PyResult<bool> {
        Err(PyValueError::new_err(
            "port info cannot be used as a boolean, read port values through `ports` instead",
        ))
    }
}

impl VerilatedInfoPort {
    fn map_port_info<T>(&self, py: Python, f: impl FnOnce(&IrPortInfo) -> T) -> T {
        let instance = self.instance.borrow(py);
        let module = instance.module.borrow(py);
        f(&module.lib.ports()[self.port])
    }
}

fn map_verilator_error(e: VerilatorError) -> PyErr {
    VerilationException::new_err(e.to_string())
}
