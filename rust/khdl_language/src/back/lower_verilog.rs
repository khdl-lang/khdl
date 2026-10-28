use crate::front::diagnostic::{DiagResult, Diagnostics};
use crate::front::range_arithmetic::{range_binary_add, range_binary_sub};
use crate::front::signal::Polarized;
use crate::mid::ir::{
    IrArrayLiteralElement, IrAssignmentTarget, IrAsyncResetInfo, IrBlock, IrBoolBinaryOp, IrBoolCompareOp,
    IrClockedProcess, IrCombinatorialProcess, IrDatabase, IrExpression, IrExpressionLarge, IrForStatement,
    IrIfStatement, IrIntArithmeticOp, IrIntCompareOp, IrIntegerRadix, IrLargeArena, IrModule, IrModuleChild,
    IrModuleExternalInstance, IrModuleInfo, IrModuleInternalInstance, IrModules, IrPort, IrPortConnection, IrPortInfo,
    IrSignal, IrSignalOrVariable, IrSignals, IrStatement, IrString, IrStringSubstitution, IrType, IrVariable,
    IrVariableInfo, IrVariables, IrWire, IrWireInfo, ValueAccess,
};
use crate::mid::steps::{IrTargetStepScalar, IrTargetStepSlice, IrTargetSteps};
use crate::syntax::ast::{PortDirection, StringPiece};
use crate::syntax::pos::{Span, Spanned};
use crate::try_inner;
use crate::util::arena::Arena;
use crate::util::big_int::{BigInt, BigUint, Sign};
use crate::util::data::{IndexMapExt, StableVec, VecExt};
use crate::util::int::{IntRepresentation, Signed};
use crate::util::iter::IterExt;
use crate::util::range::{ClosedNonEmptyRange, ClosedRange};
use crate::util::{Indent, ResultExt, separator_non_trailing};
use indexmap::{IndexMap, IndexSet};
use itertools::{Either, Itertools, enumerate, zip_eq};
use khdl_util::{swrite, swriteln};
use lazy_static::lazy_static;
use std::fmt::{Display, Formatter};
use std::num::NonZeroU32;

const I: &str = Indent::I;

#[derive(Debug, Clone)]
pub struct LoweredVerilog {
    pub source: String,
    pub module_to_lowered_name: IndexMap<IrModule, String>,
}

// TODO make backend configurable between verilog and VHDL?
// TODO ban keywords
// TODO should we still be doing diagnostics here, or should lowering just never start?
// TODO identifier ID: prefix _all_ signals with something: wire, reg, local, ...,
//   so nothing can conflict with ports/module names. Not fully right yet, but maybe a good idea.
// TODO avoid a bunch of string allocations
// TODO should we always shadow output ports with intermediate signals so we can read back from them,
//   even in old verilog versions?
// TODO lower signals that are only used within a single process to local variables? might simulate faster!
pub fn lower_to_verilog(diags: &Diagnostics, db: &IrDatabase, top_modules: &[IrModule]) -> DiagResult<LoweredVerilog> {
    let IrDatabase {
        modules,
        external_modules,
        modules_sorted: _,
    } = db;

    let mut ctx = LowerContext {
        diags,
        modules,
        module_map: IndexMap::new(),
        top_name_scope: LoweredNameScope::new_root(external_modules.clone()),
        result_source: vec![],
    };

    for module in db.modules_sorted_reachable_from(top_modules.iter().copied()) {
        let result = lower_module(&mut ctx, module)?;
        ctx.module_map.insert_first(module, result);
    }

    let source = ctx.result_source.join("\n\n");
    let module_to_lowered_name = ctx.module_map.into_iter().map(|(k, v)| (k, v.name.0)).collect();
    Ok(LoweredVerilog {
        source,
        module_to_lowered_name,
    })
}

struct LowerContext<'a> {
    diags: &'a Diagnostics,
    modules: &'a IrModules,
    module_map: IndexMap<IrModule, LoweredModule>,
    top_name_scope: LoweredNameScope<'static>,
    result_source: Vec<String>,
}

#[derive(Debug, Clone)]
struct LoweredName<S: AsRef<str> = String>(S);

#[derive(Debug, Clone)]
struct LoweredModule {
    name: LoweredName,
    ports: IndexMap<IrPort, Result<LoweredName, ZeroWidth>>,
}

#[derive(Default)]
struct LoweredNameScope<'p> {
    parent: Option<&'p LoweredNameScope<'p>>,
    local_used: IndexSet<String>,
    // track the next suffix to try for each base string to avoid O(n**2) behavior
    next_suffix_to_try: IndexMap<String, u64>,
}

impl<'p> LoweredNameScope<'p> {
    pub fn new_root(used: IndexSet<String>) -> Self {
        Self {
            parent: None,
            local_used: used,
            next_suffix_to_try: IndexMap::new(),
        }
    }

    pub fn new_child(&'p self) -> Self {
        Self {
            parent: Some(self),
            local_used: IndexSet::new(),
            next_suffix_to_try: IndexMap::new(),
        }
    }

    pub fn exact_for_new_id(&mut self, diags: &Diagnostics, span: Span, id: &str) -> DiagResult<LoweredName> {
        check_identifier_valid(diags, Spanned { span, inner: id })?;
        if self.is_used(id) {
            return Err(diags.report_error_internal(span, format!("lowered identifier `{id}` already used its scope")));
        }
        self.local_used.insert(id.to_owned());
        Ok(LoweredName(id.to_owned()))
    }

    pub fn make_unique_maybe_id(&mut self, diags: &Diagnostics, id: Spanned<Option<&str>>) -> DiagResult<LoweredName> {
        self.make_unique_str(diags, id.span, id.inner.unwrap_or("_"), false)
    }

    #[allow(dead_code)]
    pub fn make_unique_id(&mut self, diags: &Diagnostics, id: Spanned<&str>) -> DiagResult<LoweredName> {
        self.make_unique_str(diags, id.span, id.inner, false)
    }

    pub fn make_unique_str(
        &mut self,
        diags: &Diagnostics,
        span: Span,
        string_raw: &str,
        force_index: bool,
    ) -> DiagResult<LoweredName> {
        let string_valid = make_identifier_valid(string_raw);

        if !force_index && !self.is_used(&string_valid) {
            self.local_used.insert(string_valid.clone());
            return Ok(LoweredName(string_valid));
        }

        let start_suffix = self.next_suffix_to_try.get(&string_valid).copied().unwrap_or(0);

        let valid_len = string_valid.len();
        let mut buffer = string_valid;
        buffer.push('_');

        for i in start_suffix.. {
            swrite!(buffer, "{i}");

            if !self.is_used(&buffer) {
                let prefix = buffer[..valid_len].to_owned();
                self.next_suffix_to_try.insert(prefix, i + 1);

                self.local_used.insert(buffer.clone());
                return Ok(LoweredName(buffer));
            }

            buffer.truncate(valid_len + 1);
        }

        Err(diags.report_error_internal(
            span,
            format!("failed to generate unique lowered identifier for `{string_raw}`"),
        ))
    }

    fn is_used(&self, s: &str) -> bool {
        let mut curr = self;
        loop {
            if curr.local_used.contains(s) {
                return true;
            }
            match curr.parent {
                Some(p) => curr = p,
                None => return false,
            }
        }
    }
}

// TODO replace with name mangling that forces everything to be valid
//   then we can get rid of span
// TODO use __ for joining, not really here but for eg. interfaces
fn check_identifier_valid(diags: &Diagnostics, id: Spanned<&str>) -> DiagResult {
    let s = id.inner;

    if s.is_empty() {
        return Err(diags.report_error_simple(
            "invalid verilog identifier: identifier cannot be empty",
            id.span,
            "identifier used here",
        ));
    }
    let first = s.chars().next().unwrap();
    if !(first.is_ascii_alphabetic() || first == '_') {
        return Err(diags.report_error_simple(
            "invalid verilog identifier: first character must be alphabetic or underscore",
            id.span,
            "identifier used here",
        ));
    }
    for c in s.chars() {
        if !(c.is_ascii_alphabetic() || c.is_ascii_digit() || c == '$' || c == '_') {
            return Err(diags.report_error_simple(
                format!("invalid verilog identifier: character `{c}` not allowed in identifier"),
                id.span,
                "identifier used here",
            ));
        }
    }

    Ok(())
}

fn make_identifier_valid(id: &str) -> String {
    if id.is_empty() {
        return "_".to_owned();
    }

    let mut id_clean = String::with_capacity(1 + id.len());

    for c in id.chars() {
        // first character has stricter rules, prepend _ if needed
        if id_clean.is_empty() {
            if !(c.is_ascii_alphabetic() || c == '_') {
                id_clean.push('_');
            }
        }

        // other characters can be digits too
        //   technically they can be $ too, but that's sketchy
        let c_clean = if c.is_ascii_alphabetic() || c.is_ascii_digit() || c == '_' {
            c
        } else {
            // TODO preserve uniqueness
            '_'
        };
        id_clean.push(c_clean);
    }

    id_clean
}

#[derive(Debug, Copy, Clone)]
struct ModuleNameMap<'n> {
    dummy_name: &'n LoweredName,
    ports: &'n IndexMap<IrPort, Result<LoweredName, ZeroWidth>>,
    wires: &'n IndexMap<IrWire, Result<LoweredName, ZeroWidth>>,
}

#[derive(Debug, Copy, Clone)]
struct ProcessNameMap<'n> {
    module_name_map: ModuleNameMap<'n>,
    shadow_name_map: &'n IndexMap<IrSignal, LoweredName>,
    variable_name_map: &'n IndexMap<IrVariable, Result<LoweredName, ZeroWidth>>,
}

impl<'n> ModuleNameMap<'n> {
    pub fn map_signal(&self, s: IrSignal) -> Result<&'n LoweredName, ZeroWidth> {
        match s {
            IrSignal::Port(port) => self.ports.get(&port).unwrap().as_ref_ok(),
            IrSignal::Wire(wire) => self.wires.get(&wire).unwrap().as_ref_ok(),
        }
    }
}

impl<'n> ProcessNameMap<'n> {
    pub fn read_signal(&self, signal: IrSignal) -> Result<&'n LoweredName, ZeroWidth> {
        if let Some(name) = self.shadow_name_map.get(&signal) {
            Ok(name)
        } else {
            self.module_name_map.map_signal(signal)
        }
    }

    pub fn map_var(&self, v: IrVariable) -> Result<&'n LoweredName, ZeroWidth> {
        self.variable_name_map.get(&v).unwrap().as_ref_ok()
    }
}

// Processes with empty sensitivity lists never run, not even at startup
// to avoid this, we make all combinatorial processes sensitive to a dummy signal.
// In many cases this dummy signal could be skipped, but that's extra unnecessary complexity.
const SENSITIVITY_DUMMY_NAME_SIGNAL: &str = "dummy";
const SENSITIVITY_DUMMY_NAME_VAR: &str = "dummy_var";

fn lower_module(ctx: &mut LowerContext, module: IrModule) -> DiagResult<LoweredModule> {
    let diags = ctx.diags;
    assert!(!ctx.module_map.contains_key(&module));

    let module_info = &ctx.modules[module];
    let IrModuleInfo {
        signals,
        large: _,
        children: _,
        debug_info_def_file,
        debug_info_id,
        debug_info_generic_args,
    } = module_info;
    let debug_info_id = maybe_id_as_ref(debug_info_id);
    let module_name = ctx.top_name_scope.make_unique_maybe_id(diags, debug_info_id)?;

    let mut f = String::new();

    // comment above the module containing some metadata
    // TODO don't use absolute paths here, they cause non-reproducible builds
    swriteln!(f, "// module {}", debug_info_id.inner.unwrap_or("_"));
    swriteln!(f, "//   defined in \"{debug_info_def_file}\"",);

    if let Some(generic_args) = debug_info_generic_args {
        swriteln!(f, "//   instantiated with generic arguments:");
        for (arg_name, arg_value) in generic_args {
            swriteln!(f, "//     {}={}", arg_name, arg_value);
        }
    }

    // module header
    let mut module_name_scope = LoweredNameScope::default();
    let signals_driven_by_instances = collect_signals_driven_by_instances(module_info);

    swrite!(f, "module {}(", module_name);
    let port_name_map = lower_module_ports(
        diags,
        &signals_driven_by_instances,
        &signals.ports,
        &mut module_name_scope,
        &mut f,
    )?;
    swriteln!(f, ");");

    // reserve child names as soon as possible, to hopefully get the original names
    let child_names = reserve_module_child_names(diags, &module_info.children, &mut module_name_scope)?;

    // lower wires
    let mut newline_module = NewlineGenerator::new();
    let wire_name_map = lower_module_wires(
        diags,
        &mut module_name_scope,
        &signals_driven_by_instances,
        &signals.wires,
        &mut newline_module,
        &mut f,
    )?;

    // declare dummy signal, used to ensure combinatorial block sensitivity lists are never empty
    // TODO only declare when actually used?
    let dummy_name = module_name_scope.make_unique_str(
        diags,
        module_info.debug_info_id.span,
        SENSITIVITY_DUMMY_NAME_SIGNAL,
        false,
    )?;
    newline_module.start_item(&mut f);
    swriteln!(f, "{I}wire {dummy_name} = 1'b0;");

    // lower statements
    let module_names = ModuleNameMap {
        dummy_name: &dummy_name,
        ports: &port_name_map,
        wires: &wire_name_map,
    };

    lower_module_statements(
        ctx,
        module_info,
        &mut module_name_scope,
        module_names,
        &child_names,
        &mut newline_module,
        &mut f,
    )?;

    // end of module
    swriteln!(f, "endmodule");

    let lowered_module = LoweredModule {
        name: module_name,
        ports: port_name_map,
    };

    ctx.result_source.push(f);
    Ok(lowered_module)
}

fn lower_module_ports(
    diags: &Diagnostics,
    signals_driven_by_child_instances: &IndexSet<IrSignal>,
    ports: &Arena<IrPort, IrPortInfo>,
    module_name_scope: &mut LoweredNameScope,
    f: &mut String,
) -> DiagResult<IndexMap<IrPort, Result<LoweredName, ZeroWidth>>> {
    let mut port_lines = vec![];
    let mut port_name_map = IndexMap::new();
    let mut last_actual_port_index = None;

    // TODO remove second iteration,
    //   we only have it avoid redundant trailing commas which is also possible in a single pass
    for (port_index, (port, port_info)) in enumerate(ports) {
        let IrPortInfo {
            name,
            direction,
            ty,
            debug_span,
            debug_info_ty,
            debug_info_domain,
        } = port_info;

        // allocate port names even for zero-width ports to get some extra stability
        // TODO check that port names are valid and unique
        let lower_name = module_name_scope.exact_for_new_id(diags, *debug_span, name)?;

        let port_ty = VerilogType::new_from_ir(diags, *debug_span, ty)?;

        let (is_non_zero_width, ty_prefix) = match port_ty {
            Ok(port_ty) => (true, Either::Left(port_ty.prefix())),
            Err(ZeroWidth) => (false, Either::Right("[empty] ")),
        };

        let dir_str = match direction {
            PortDirection::Input => "input",
            PortDirection::Output => {
                if signals_driven_by_child_instances.contains(&IrSignal::Port(port)) {
                    "output"
                } else {
                    "output reg"
                }
            }
        };

        if is_non_zero_width {
            last_actual_port_index = Some(port_index);
        }
        port_lines.push((
            is_non_zero_width,
            format!("{dir_str} {ty_prefix}{lower_name}"),
            format!("{debug_info_domain} {}", debug_info_ty.inner),
        ));

        let insert_name = if is_non_zero_width {
            Ok(lower_name)
        } else {
            Err(ZeroWidth)
        };
        port_name_map.insert_first(port, insert_name);
    }

    for (port_index, (is_actual_port, main_str, comment_str)) in enumerate(port_lines) {
        swrite!(f, "\n    ");

        let start_str = if is_actual_port { "" } else { "// " };
        let end_str = separator_non_trailing(",", port_index, last_actual_port_index.unwrap_or(0) + 1);

        swrite!(f, "{start_str}{main_str}{end_str} // {comment_str}")
    }

    if !ports.is_empty() {
        swriteln!(f);
    }

    Ok(port_name_map)
}

// TODO Handle signals partially driven by different drivers? Or will that not be supported?
fn collect_signals_driven_by_instances(module: &IrModuleInfo) -> IndexSet<IrSignal> {
    let mut signals = IndexSet::new();

    let mut visit_connection = |connection: IrPortConnection| match connection {
        IrPortConnection::Input(_) => {}
        IrPortConnection::Output(signal) => {
            if let Some(signal) = signal {
                signals.insert(signal);
            }
        }
    };

    for child in &module.children {
        match &child.inner {
            IrModuleChild::ClockedProcess(_) => {}
            IrModuleChild::CombinatorialProcess(_) => {}
            IrModuleChild::ModuleInternalInstance(inst) => {
                for connection in &inst.port_connections {
                    visit_connection(connection.inner);
                }
            }
            IrModuleChild::ModuleExternalInstance(inst) => {
                for (_, connection) in inst.port_connections.values() {
                    visit_connection(connection.inner);
                }
            }
        }
    }

    signals
}

fn reserve_module_child_names(
    diags: &Diagnostics,
    children: &[Spanned<IrModuleChild>],
    module_name_scope: &mut LoweredNameScope,
) -> DiagResult<Vec<LoweredName>> {
    children
        .iter()
        .map(|child| {
            let (base, force_index) = match &child.inner {
                IrModuleChild::ModuleInternalInstance(instance) => match &instance.name {
                    Some(name) => (name.as_str(), false),
                    None => ("instance", true),
                },
                IrModuleChild::ModuleExternalInstance(instance) => match &instance.name {
                    Some(name) => (name.as_str(), false),
                    None => ("instance", true),
                },
                IrModuleChild::CombinatorialProcess(_) => ("comb", true),
                IrModuleChild::ClockedProcess(_) => ("clocked", true),
            };
            module_name_scope.make_unique_str(diags, child.span, base, force_index)
        })
        .try_collect_vec()
}

fn lower_module_wires(
    diags: &Diagnostics,
    module_name_scope: &mut LoweredNameScope,
    signals_driven_by_child_instances: &IndexSet<IrSignal>,
    wires: &Arena<IrWire, IrWireInfo>,
    newline: &mut NewlineGenerator,
    f: &mut String,
) -> DiagResult<IndexMap<IrWire, Result<LoweredName, ZeroWidth>>> {
    let mut wire_name_map = IndexMap::new();

    newline.start_group();
    for (wire, wire_info) in wires {
        let IrWireInfo {
            ty,
            debug_info_id,
            debug_info_ty,
            debug_info_domain,
        } = &wire_info;

        let name = match VerilogType::new_from_ir(diags, debug_info_id.span, ty)? {
            Err(ZeroWidth) => {
                // skip zero-width signals
                Err(ZeroWidth)
            }
            Ok(ty_verilog) => {
                let ty_prefix = ty_verilog.prefix();

                // figure out verilog kind
                let verilog_kind = if signals_driven_by_child_instances.contains(&IrSignal::Wire(wire)) {
                    "wire"
                } else {
                    "reg"
                };

                // pick a unique name
                let debug_info_id = maybe_id_as_ref(debug_info_id);
                let name = module_name_scope.make_unique_maybe_id(diags, debug_info_id)?;

                // figure out debug info
                let debug_name = debug_info_id.inner.unwrap_or("_");

                // actually write the verilog
                newline.start_item(f);
                swriteln!(
                    f,
                    "{I}{verilog_kind} {ty_prefix}{name}; // wire {debug_name}: {debug_info_domain} {debug_info_ty}"
                );

                Ok(name)
            }
        };

        wire_name_map.insert_first(wire, name);
    }

    Ok(wire_name_map)
}

fn lower_module_statements(
    ctx: &mut LowerContext,
    module_info: &IrModuleInfo,
    module_name_scope: &mut LoweredNameScope,
    module_name_map: ModuleNameMap,
    child_names: &[LoweredName],
    newline_module: &mut NewlineGenerator,
    f: &mut String,
) -> DiagResult {
    let diags = ctx.diags;

    // TODO ensure that child labels are unique
    for (child, child_name) in zip_eq(&module_info.children, child_names) {
        newline_module.start_group_and_item(f);

        match &child.inner {
            IrModuleChild::CombinatorialProcess(process) => {
                lower_combinatorial_process(
                    f,
                    diags,
                    module_info,
                    module_name_scope,
                    module_name_map,
                    child_name,
                    child.span,
                    process,
                )?;
            }
            IrModuleChild::ClockedProcess(process) => {
                lower_clocked_process(
                    diags,
                    f,
                    module_info,
                    module_name_scope,
                    module_name_map,
                    child_name,
                    process,
                )?;
            }
            IrModuleChild::ModuleInternalInstance(instance) => {
                let &IrModuleInternalInstance {
                    name: _,
                    module,
                    ref port_connections,
                } = instance;

                let inner_module = ctx.module_map.get(&module).unwrap();
                let inner_module_info = &ctx.modules[module];

                swrite!(f, "{I}{} {child_name}", inner_module.name);

                let connections = port_connections.iter().enumerate().map(|(port_index, connection)| {
                    let (&port, port_name) = inner_module.ports.get_index(port_index).unwrap();
                    let port_name = port_name.as_ref_ok().map(LoweredName::as_ref);
                    let port_ty = &inner_module_info.signals.ports[port].ty;
                    (port_name, port_ty, connection.inner)
                });
                lower_port_connections(f, module_name_map, connections)?;
            }
            IrModuleChild::ModuleExternalInstance(instance) => {
                let IrModuleExternalInstance {
                    name: _,
                    module_name,
                    generic_args,
                    port_connections,
                } = instance;

                swrite!(f, "{I}{}", LoweredName(module_name));

                if let Some(generic_args) = generic_args {
                    if generic_args.is_empty() {
                        swrite!(f, " #()");
                    } else {
                        swriteln!(f, " #(");
                        for (arg_index, (arg_name, arg_value)) in enumerate(generic_args) {
                            let arg_name = LoweredName(arg_name);
                            let sep = separator_non_trailing(",", arg_index, generic_args.len());
                            swriteln!(f, "{I}{I}.{arg_name}({arg_value}){sep}");
                        }
                        swrite!(f, "{I})");
                    }
                }

                swrite!(f, " {child_name}");

                let connections = port_connections.iter().map(|(port_name, (port_ty, connection))| {
                    (Ok(LoweredName(port_name.as_ref())), port_ty, connection.inner)
                });
                lower_port_connections(f, module_name_map, connections)?;
            }
        }
    }

    Ok(())
}

fn lower_port_connections<'a, 'b>(
    f: &mut String,
    parent_name_map: ModuleNameMap,
    connections: impl IntoIterator<Item = (Result<LoweredName<&'a str>, ZeroWidth>, &'b IrType, IrPortConnection)>,
) -> DiagResult {
    swrite!(f, "(");

    let mut any_prev = false;

    for (port_name, port_ty, connection) in connections {
        if port_ty.size_bits().is_zero() {
            continue;
        }

        let port_name = unwrap_zero_width(port_name);
        let signal = match connection {
            IrPortConnection::Input(s) => Some(s),
            IrPortConnection::Output(s) => s,
        };
        let signal_name = signal.map(|s| unwrap_zero_width(parent_name_map.map_signal(s)));

        if any_prev {
            swrite!(f, ",");
        }
        swriteln!(f);

        swrite!(f, "{I}{I}.{port_name}(");
        if let Some(signal_name) = signal_name {
            swrite!(f, "{signal_name}");
        }
        swrite!(f, ")");

        any_prev = true;
    }

    if any_prev {
        swriteln!(f);
        swriteln!(f, "{I});");
    } else {
        swriteln!(f, ");");
    }

    Ok(())
}

fn lower_combinatorial_process(
    f_module: &mut String,
    diags: &Diagnostics,
    module_info: &IrModuleInfo,
    module_name_scope: &mut LoweredNameScope,
    module_name_map: ModuleNameMap,
    child_name: &LoweredName,
    span: Span,
    process: &IrCombinatorialProcess,
) -> DiagResult {
    let IrCombinatorialProcess { variables, block } = process;

    let indent = Indent::new(2);
    let mut f_decl = String::new();
    let mut f_init = String::new();
    let mut f_stmt = String::new();

    let mut name_scope = module_name_scope.new_child();

    // copy dummy value
    let dummy_name_internal = name_scope.make_unique_str(diags, span, SENSITIVITY_DUMMY_NAME_VAR, false)?;
    swriteln!(f_decl, "{indent}reg {dummy_name_internal};");
    swriteln!(
        f_init,
        "{indent}{dummy_name_internal} = {dummy_name};",
        dummy_name = module_name_map.dummy_name
    );

    let variable_name_map =
        declare_and_init_variables(diags, &mut f_decl, &mut f_init, indent, &mut name_scope, variables)?;

    // combinatorial processes don't have register shadowing, they can't write to any
    let process_name_map = ProcessNameMap {
        module_name_map,
        shadow_name_map: &IndexMap::default(),
        variable_name_map: &variable_name_map,
    };

    let temporaries = StableVec::new();
    let mut ctx = LowerBlockContext {
        diags,
        module: module_info,
        variables,
        is_clocked_process: false,
        name_map: process_name_map,
        name_scope: &mut name_scope,
        temporaries: &temporaries,
        indent,
        f: &mut f_stmt,
    };
    ctx.lower_block(block)?;

    // combine and write to final string
    declare_temporaries(&mut f_decl, &mut f_init, indent, temporaries);

    swriteln!(f_module, "{I}always @(*) begin: {child_name}");
    write_line_separated_strings(f_module, &[&f_decl, &f_init, &f_stmt]);
    swriteln!(f_module, "{I}end");

    Ok(())
}

fn lower_clocked_process(
    diags: &Diagnostics,
    f_module: &mut String,
    module_info: &IrModuleInfo,
    module_name_scope: &LoweredNameScope,
    module_name_map: ModuleNameMap,
    child_name: &LoweredName,
    process: &IrClockedProcess,
) -> DiagResult {
    let &IrClockedProcess {
        registers: _,
        ref variables,
        clock_signal,
        ref clock_block,
        ref async_reset,
    } = process;

    // lower edges
    let clock_edge = lower_edge(diags, module_name_map, clock_signal)?;
    let async_reset = async_reset
        .as_ref()
        .map(|info| {
            let reset_edge = lower_edge(diags, module_name_map, info.signal)?;
            Ok((reset_edge, info))
        })
        .transpose()?;

    // TODO reorder these things
    let indent_clocked = Indent::new(if async_reset.is_some() { 3 } else { 2 });
    let mut name_scope = module_name_scope.new_child();

    let mut f_decl = String::new();
    let mut f_init = String::new();
    let mut f_body = String::new();

    // declare variables and shadow registers
    let shadow_regs = collect_shadow_registers(&module_info.large, clock_block);

    let variable_name_map = declare_and_init_variables(
        diags,
        &mut f_decl,
        &mut f_init,
        Indent::new(2),
        &mut name_scope,
        variables,
    )?;
    let shadow_name_map =
        declare_shadow_signals(diags, &mut f_decl, &module_info.signals, &mut name_scope, &shadow_regs)?;

    // build new name map
    let process_name_map = ProcessNameMap {
        module_name_map,
        variable_name_map: &variable_name_map,
        shadow_name_map: &shadow_name_map,
    };

    // populate shadow signals
    for (&signal, signal_name_shadow) in &shadow_name_map {
        if shadow_regs.contains(&signal) {
            let reg_name_raw = match module_name_map.map_signal(signal) {
                Ok(orig_name) => orig_name,
                Err(ZeroWidth) => continue,
            };
            swriteln!(f_body, "{indent_clocked}{signal_name_shadow} = {reg_name_raw};");
        }
    }
    let pos_end_of_shadow_init = f_body.len();

    // lower body itself
    let temporaries = StableVec::new();
    let mut ctx = LowerBlockContext {
        diags,
        module: module_info,
        variables,
        is_clocked_process: true,
        name_map: process_name_map,
        name_scope: &mut name_scope,
        temporaries: &temporaries,
        indent: indent_clocked,
        f: &mut f_body,
    };
    ctx.lower_block(clock_block)?;

    if f_body.len() > pos_end_of_shadow_init && pos_end_of_shadow_init > 0 {
        f_body.insert(pos_end_of_shadow_init, '\n');
    }

    // async reset header if any
    match &async_reset {
        None => {}
        Some((reset_edge, reset_info)) => {
            let IrAsyncResetInfo { signal: _, resets } = reset_info;

            let mut f_if = String::new();

            swriteln!(f_if, "{I}{I}if ({}{}) begin", reset_edge.if_prefix, reset_edge.signal);
            let indent_reset = Indent::new(3);

            let mut ctx_reset = LowerBlockContext {
                diags,
                module: module_info,
                variables,
                is_clocked_process: true,
                name_map: process_name_map,
                name_scope: &mut name_scope,
                temporaries: &temporaries,
                indent: indent_reset,
                f: &mut f_if,
            };

            for reset in resets {
                let &(reg, ref value) = &reset.inner;

                // use non-shadowed name
                let reg_name_raw = match module_name_map.map_signal(reg) {
                    Ok(reg_name) => reg_name,
                    Err(ZeroWidth) => continue,
                };

                let value = unwrap_zero_width(ctx_reset.lower_expression(reset.span, value)?);

                // use non-blocking assignment to match other register writes
                swriteln!(ctx_reset.f, "{indent_reset}{reg_name_raw} <= {value};");
            }

            swriteln!(f_if, "{I}{I}end else begin");
            f_if.push_str(&f_body);
            swriteln!(f_if, "{I}{I}end");

            f_body = f_if;
        }
    };

    // combine everything
    swrite!(f_module, "{I}always @({} {}", clock_edge.edge, clock_edge.signal);
    if let Some((reset_edge, _)) = &async_reset {
        swrite!(f_module, ", {} {}", reset_edge.edge, reset_edge.signal,)
    }
    swriteln!(f_module, ") begin: {child_name}");

    declare_temporaries(&mut f_decl, &mut f_init, Indent::new(2), temporaries);
    write_line_separated_strings(f_module, &[&f_decl, &f_init, &f_body]);
    swriteln!(f_module, "{I}end");

    Ok(())
}

#[derive(Debug, Copy, Clone)]
struct ZeroWidth;

fn declare_and_init_variables(
    diags: &Diagnostics,
    f_decl: &mut String,
    f_init: &mut String,
    indent: Indent,
    name_scope: &mut LoweredNameScope,
    variables: &IrVariables,
) -> DiagResult<IndexMap<IrVariable, Result<LoweredName, ZeroWidth>>> {
    let mut result = IndexMap::new();

    for (variable, variable_info) in variables {
        let &IrVariableInfo {
            ref ty,
            debug_info_span,
            ref debug_info_id,
        } = variable_info;

        let ty_verilog = VerilogType::new_from_ir(diags, debug_info_span, ty)?;

        let name = match ty_verilog {
            Ok(ty_verilog) => {
                let debug_info_id = Spanned::new(debug_info_span, debug_info_id.as_ref().map(String::as_str));
                let name = name_scope.make_unique_maybe_id(diags, debug_info_id)?;

                declare_local(f_decl, f_init, indent, ty_verilog, &name);
                Ok(name)
            }
            Err(ZeroWidth) => Err(ZeroWidth),
        };

        result.insert_first(variable, name);
    }

    Ok(result)
}

fn declare_shadow_signals(
    diags: &Diagnostics,
    f: &mut String,
    signals: &IrSignals,
    module_name_scope: &mut LoweredNameScope,
    shadow_signals: &IndexSet<IrSignal>,
) -> DiagResult<IndexMap<IrSignal, LoweredName>> {
    let mut shadowing_reg_name_map = IndexMap::new();

    for &signal in shadow_signals {
        let (span, debug_info_id, ty) = match signal {
            IrSignal::Port(signal) => {
                let info = &signals.ports[signal];
                (info.debug_span, Some(info.name.as_str()), &info.ty)
            }
            IrSignal::Wire(wire) => {
                let info = &signals.wires[wire];
                (info.debug_info_id.span, info.debug_info_id.inner.as_deref(), &info.ty)
            }
        };

        // skip zero-width registers
        let ty_verilog = match VerilogType::new_from_ir(diags, span, ty)? {
            Ok(ty) => ty,
            Err(ZeroWidth) => continue,
        };

        let register_name = debug_info_id.unwrap_or("_");
        let shadow_name = module_name_scope.make_unique_str(diags, span, &format!("shadow_{register_name}"), false)?;

        let ty_prefix = ty_verilog.prefix();
        swriteln!(f, "{I}{I}reg {ty_prefix}{shadow_name};");

        shadowing_reg_name_map.insert_first(signal, shadow_name);
    }

    Ok(shadowing_reg_name_map)
}

fn declare_temporaries(
    f_decl: &mut String,
    f_init: &mut String,
    indent: Indent,
    temporaries: StableVec<TemporaryInfo>,
) {
    for tmp in temporaries.into_vec() {
        let TemporaryInfo { name, ty } = *tmp;
        declare_local(f_decl, f_init, indent, ty, &name);
    }
}

fn declare_local(f_decl: &mut String, f_init: &mut String, indent: Indent, ty: VerilogType, name: &LoweredName) {
    // x-initialize all variables to avoid inferring latches
    let ty_prefix = ty.prefix();
    let ty_size_bits = ty.size_bits();
    swriteln!(f_decl, "{indent}reg {ty_prefix}{name};");
    swriteln!(f_init, "{indent}{name} = {ty_size_bits}'bx;");
}

#[derive(Debug, Copy, Clone, Default)]
struct AccessInfo {
    any_read: bool,
    any_write: bool,
}

/// Collect all registers that should be shadowed.
/// Shadowed registers get a local variable in the process that at all times stores a copy of the value in the signal.
/// Writes to the register write to both the signal and the shadow variable, reads read from the shadow variable.
///
/// This ensures we implement the correct signal write behavior:
/// Reads after writes in a process should read the new value, not the old one.
/// But clocked block register writes should use non-blocking `<=` assignments, which would have the wrong behavior.
///
/// We still implement write-through on every assignment instead of only once at the end of the process,
/// to keep the generated code similar to what users would write,
/// and to hopefully better pattern match synthesis tool optimizations like clock gating.
fn collect_shadow_registers(large: &IrLargeArena, block: &IrBlock) -> IndexSet<IrSignal> {
    let mut regs: IndexMap<IrSignal, AccessInfo> = IndexMap::new();

    block.visit_values_accessed(large, &mut |value, access| match value {
        IrSignalOrVariable::Signal(signal) => {
            let entry = regs.entry(signal).or_default();
            match access {
                ValueAccess::Read => entry.any_read = true,
                ValueAccess::Write => entry.any_write = true,
            }
        }
        _ => {}
    });

    // TODO avoid reallocation here
    regs.into_iter()
        .filter(|(_, access)| access.any_write && access.any_read)
        .map(|(s, _)| s)
        .collect()
}

#[derive(Debug)]
enum Evaluated<'n> {
    Name(&'n LoweredName),
    Temporary(Temporary<'n>),
    String(String),
    Str(&'static str),

    // TODO doc (all variants, but especially this one)
    SignedString(String),
}

#[derive(Debug, Copy, Clone)]
struct Temporary<'n>(&'n LoweredName);

#[derive(Debug)]
struct TemporaryInfo {
    name: LoweredName,
    ty: VerilogType,
}

impl Display for Temporary<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'n> Evaluated<'n> {
    pub fn as_signed_maybe(&self, signed: bool) -> impl Display {
        struct S<'s, 'n> {
            inner: &'s Evaluated<'n>,
            signed: bool,
        }
        impl Display for S<'_, '_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                if self.signed {
                    match self.inner {
                        Evaluated::SignedString(s) => write!(f, "{}", s),
                        _ => write!(f, "$signed({})", self.inner),
                    }
                } else {
                    write!(f, "{}", self.inner)
                }
            }
        }
        S { inner: self, signed }
    }

    pub fn as_signed(&self) -> impl Display {
        self.as_signed_maybe(true)
    }

    pub fn is_named(&self) -> bool {
        match self {
            Evaluated::Name(_) | Evaluated::Temporary(_) => true,
            Evaluated::String(_) | Evaluated::Str(_) | Evaluated::SignedString(_) => false,
        }
    }
}

impl Display for Evaluated<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Evaluated::Name(n) => write!(f, "{}", n),
            Evaluated::Temporary(tmp) => write!(f, "{}", tmp),
            Evaluated::String(s) => write!(f, "{}", s),
            Evaluated::Str(s) => write!(f, "{}", s),
            Evaluated::SignedString(s) => write!(f, "$unsigned({})", s),
        }
    }
}

struct LowerBlockContext<'a, 'n> {
    diags: &'a Diagnostics,
    module: &'a IrModuleInfo,
    variables: &'a IrVariables,

    is_clocked_process: bool,
    name_map: ProcessNameMap<'n>,
    name_scope: &'a mut LoweredNameScope<'n>,
    temporaries: &'n StableVec<TemporaryInfo>,

    indent: Indent,
    f: &'a mut String,
}

impl<'a, 'n> LowerBlockContext<'a, 'n> {
    fn indent(&mut self, f: impl FnOnce(&mut Self) -> DiagResult) -> DiagResult {
        let old_indent = self.indent;
        self.indent = self.indent.nest();
        let result = f(self);
        self.indent = old_indent;
        result
    }

    fn lower_block_indented(&mut self, block: &IrBlock) -> DiagResult {
        self.indent(|s| s.lower_block(block))
    }

    fn lower_block(&mut self, block: &IrBlock) -> DiagResult {
        let IrBlock { statements } = block;
        for stmt in statements {
            self.lower_statement(stmt.as_ref())?;
        }
        Ok(())
    }

    fn lower_statement(&mut self, stmt: Spanned<&IrStatement>) -> DiagResult {
        let indent = self.indent;
        let diags = self.diags;

        match stmt.inner {
            IrStatement::Assign(target, source) => {
                let source = match self.lower_expression(stmt.span, source)? {
                    Ok(source) => source,
                    Err(ZeroWidth) => return Ok(()),
                };
                self.lower_assignment(stmt.span, target, source)?;
            }
            IrStatement::Block(inner) => {
                swriteln!(self.f, "{indent}begin");
                self.lower_block_indented(inner)?;
                swriteln!(self.f, "{indent}end");
            }
            IrStatement::If(IrIfStatement {
                condition,
                then_block,
                else_block,
            }) => {
                // TODO re-merge else-if chains to reduce indentation if there are no other statements in the else block?
                let cond = self.lower_expression_non_zero_width(stmt.span, condition, "condition")?;
                swriteln!(self.f, "{indent}if ({cond}) begin");
                self.lower_block_indented(then_block)?;
                swrite!(self.f, "{indent}end");

                if let Some(else_block) = else_block {
                    swriteln!(self.f, " else begin");
                    self.lower_block_indented(else_block)?;
                    swrite!(self.f, "{indent}end");
                }

                swriteln!(self.f);
            }
            &IrStatement::For(IrForStatement {
                index,
                ref range,
                ref block,
            }) => {
                // we will need to form an inclusive range, which will give weird results for empty ranges,
                //   so just skip empty ranges
                if range.is_empty() {
                    return Ok(());
                }

                // base range is non-empty => range_inc contains multiple values => cannot be zero-width
                let range_inc = ClosedNonEmptyRange {
                    start: range.start.clone(),
                    end: &range.end + 1,
                };
                let range_inc = NonZeroWidthRange::new(range_inc).unwrap();

                // create/map variables
                let index = match self.name_map.map_var(index) {
                    Ok(index) => index,
                    Err(ZeroWidth) => {
                        return Err(diags.report_error_internal(stmt.span, "index var zero-width"));
                    }
                };
                let index_tmp =
                    self.new_temporary(stmt.span, VerilogType::new_from_range(diags, stmt.span, &range_inc)?)?;

                // lower range
                let start_eval = lower_int_constant(&range_inc, &range.start);
                let end_eval = lower_int_constant(&range_inc, &range.end);

                // use signed comparison if necessary
                let range_can_be_neg = range.start.is_negative();
                let cond = if range_can_be_neg {
                    format!(
                        "{} < {}",
                        Evaluated::Temporary(index_tmp).as_signed(),
                        end_eval.as_signed()
                    )
                } else {
                    format!("{index_tmp} < {end_eval}")
                };

                // lower loop
                swriteln!(
                    self.f,
                    "{indent}for({index_tmp} = {start_eval}; {cond}; {index_tmp} = {index_tmp} + 1) begin"
                );
                swriteln!(self.f, "{indent}{I}{index} = {index_tmp};");
                self.lower_block_indented(block)?;
                swriteln!(self.f, "{indent}end");
            }
            IrStatement::Print(string) => {
                self.lower_print(stmt.span, string)?;
            }
            IrStatement::AssertFailed => {
                // TODO if targeting SystemVerilog, use $fatal/$error
                swriteln!(self.f, "{indent}$finish;");
            }
        }
        Ok(())
    }

    fn lower_print(&mut self, span: Span, s: &IrString) -> DiagResult {
        let mut f_str = String::new();
        let mut f_args = String::new();

        for p in s {
            match p {
                StringPiece::Literal(p) => {
                    f_str.push_str(&escape_verilog_str(p));
                }
                StringPiece::Substitute(p) => match p {
                    IrStringSubstitution::Integer(p, radix) => {
                        // TODO how does signed bin/hex behave?
                        let signed = p
                            .ty(&self.module.large, &self.module.signals, self.variables)
                            .unwrap_int()
                            .as_ref()
                            .start
                            .is_negative();
                        let p = self.lower_expression(span, p)?;

                        let radix = match radix {
                            IrIntegerRadix::Binary => "%b",
                            IrIntegerRadix::Decimal => "%d",
                            IrIntegerRadix::Hexadecimal => "%h",
                        };

                        match p {
                            Ok(p) => {
                                swrite!(f_str, "{radix}");
                                swrite!(f_args, ", {}", p.as_signed_maybe(signed));
                            }
                            Err(ZeroWidth) => {
                                swrite!(f_str, "0");
                            }
                        }
                    }
                },
            }
        }

        let indent = self.indent;
        swriteln!(self.f, "{indent}$write(\"{f_str}\"{f_args});");

        Ok(())
    }

    fn lower_expression_as_named(
        &mut self,
        span: Span,
        expr: &IrExpression,
    ) -> DiagResult<Result<Evaluated<'n>, ZeroWidth>> {
        let eval = try_inner!(self.lower_expression(span, expr)?);

        if eval.is_named() {
            Ok(Ok(eval))
        } else {
            let ty = expr.ty(&self.module.large, &self.module.signals, self.variables);
            let ty_verilog = try_inner!(VerilogType::new_from_ir(self.diags, span, &ty)?);

            let tmp = self.new_temporary_assign(span, ty_verilog, eval)?;
            Ok(Ok(Evaluated::Temporary(tmp)))
        }
    }

    fn lower_expression(&mut self, span: Span, expr: &IrExpression) -> DiagResult<Result<Evaluated<'n>, ZeroWidth>> {
        let diags = self.diags;
        let large = &self.module.large;
        let signals = &self.module.signals;
        let variables = self.variables;
        let name_map = self.name_map;

        // skip any zero-width expressions
        //   expressions are always pure, they can never have side-effects
        let result_ty = expr.ty(large, signals, variables);
        let result_ty_verilog = match VerilogType::new_from_ir(diags, span, &result_ty)? {
            Ok(ty) => ty,
            Err(ZeroWidth) => {
                return Ok(Err(ZeroWidth));
            }
        };

        let eval = match expr {
            &IrExpression::Bool(x) => {
                let s = if x { "1'b1" } else { "1'b0" };
                Evaluated::Str(s)
            }
            IrExpression::Int(x) => {
                let range = ClosedNonEmptyRange::single(x.clone());
                let range = NonZeroWidthRange::new(range).expect("already checked for zero-width earlier");
                lower_int_constant(&range, x)
            }

            &IrExpression::Signal(s) => Evaluated::Name(unwrap_zero_width(name_map.read_signal(s))),
            &IrExpression::Variable(v) => Evaluated::Name(unwrap_zero_width(name_map.map_var(v))),
            &IrExpression::Large(expr) => {
                match &large[expr] {
                    IrExpressionLarge::Undefined(_) => {
                        let size_bits = result_ty_verilog.size_bits();
                        Evaluated::String(format!("{}'bx", size_bits))
                    }
                    IrExpressionLarge::BoolNot(inner) => {
                        let inner = self.lower_expression_non_zero_width(span, inner, "boolean")?;
                        Evaluated::String(format!("(!{inner})"))
                    }
                    IrExpressionLarge::BoolBinaryScalar(op, left, right) => {
                        // logical and bitwise operators would both work,
                        //   bitwise is more consistent since it also has an xor operator
                        let op_str = bitwise_op_str(*op);
                        let left = self.lower_expression_non_zero_width(span, left, "boolean")?;
                        let right = self.lower_expression_non_zero_width(span, right, "boolean")?;
                        Evaluated::String(format!("({left} {op_str} {right})"))
                    }
                    IrExpressionLarge::BoolBinaryArray(op, left, right) => {
                        // both operands have the same width as the result, which we already checked is non-zero
                        let op_str = bitwise_op_str(*op);
                        let left = self.lower_expression_non_zero_width(span, left, "bit array")?;
                        let right = self.lower_expression_non_zero_width(span, right, "bit array")?;
                        Evaluated::String(format!("({left} {op_str} {right})"))
                    }
                    IrExpressionLarge::BoolFill(len, inner) => {
                        let inner = self.lower_expression_non_zero_width(span, inner, "boolean")?;
                        Evaluated::String(format!("{{{len}{{{inner}}}}}"))
                    }
                    IrExpressionLarge::BoolReduce(op, inner) => match self.lower_expression(span, inner)? {
                        Ok(inner) => Evaluated::String(format!("({}{inner})", bitwise_op_str(*op))),
                        Err(ZeroWidth) => Evaluated::String(format!("1'b{}", u8::from(op.identity_bool()))),
                    },
                    IrExpressionLarge::BoolCompareScalar(op, left, right) => {
                        let op_str = compare_op_str(*op);
                        let left = self.lower_expression_non_zero_width(span, left, "boolean")?;
                        let right = self.lower_expression_non_zero_width(span, right, "boolean")?;
                        Evaluated::String(format!("({left} {op_str} {right})"))
                    }
                    IrExpressionLarge::BoolCompareArray(op, left, right) => {
                        // both operands have the same type, so they are either both zero-width or neither is
                        let left = self.lower_expression(span, left)?;
                        let right = self.lower_expression(span, right)?;
                        match (left, right) {
                            (Ok(left), Ok(right)) => {
                                Evaluated::String(format!("({left} {} {right})", compare_op_str(*op)))
                            }
                            (Err(ZeroWidth), Err(ZeroWidth)) => {
                                // zero-width arrays are always equal
                                Evaluated::String(format!("1'b{}", u8::from(op.eval(true, true))))
                            }
                            _ => {
                                return Err(self
                                    .diags
                                    .report_error_internal(span, "bool array comparison width mismatch"));
                            }
                        }
                    }
                    &IrExpressionLarge::IntArithmetic(op, ref result_range, ref left, ref right) => {
                        let result_range = NonZeroWidthRange::new(result_range.clone())
                            .expect("already checked for zero-width earlier");
                        self.lower_arithmetic_expression(span, &result_range, result_ty_verilog, op, left, right)?
                    }
                    IrExpressionLarge::IntCompare(op, left, right) => {
                        // find common range that contains all operands
                        let left_range = left.ty(large, signals, variables).unwrap_int();
                        let right_range = right.ty(large, signals, variables).unwrap_int();
                        let combined_range = left_range.union(right_range);
                        let combined_range =
                            NonZeroWidthRange::new(combined_range).unwrap_or(NonZeroWidthRange::ZERO_ONE);

                        // lower both operands to that range
                        let left_raw = self.lower_expression_int_expanded(span, &combined_range, left)?;
                        let right_raw = self.lower_expression_int_expanded(span, &combined_range, right)?;

                        let signed = combined_range.range().start.is_negative();
                        let left = left_raw.as_signed_maybe(signed);
                        let right = right_raw.as_signed_maybe(signed);

                        // build the final expression
                        let op_str = match op {
                            IrIntCompareOp::Eq => "==",
                            IrIntCompareOp::Neq => "!=",
                            IrIntCompareOp::Lt => "<",
                            IrIntCompareOp::Lte => "<=",
                            IrIntCompareOp::Gt => ">",
                            IrIntCompareOp::Gte => ">=",
                        };
                        Evaluated::String(format!("({left} {op_str} {right})"))
                    }

                    IrExpressionLarge::TupleLiteral(elements) => self.lower_concatenation(span, elements)?,
                    IrExpressionLarge::ArrayLiteral(_inner_ty, _len, elements) => {
                        // verilog just flattens everything to bits, so the spread operator happens automatically
                        let elements = elements.iter().map(|e| match e {
                            IrArrayLiteralElement::Spread(e) => e,
                            IrArrayLiteralElement::Single(e) => e,
                        });
                        self.lower_concatenation(span, elements)?
                    }
                    IrExpressionLarge::StructLiteral(_ty, fields) => self.lower_concatenation(span, fields)?,
                    &IrExpressionLarge::EnumLiteral(ref ty, variant, ref payload) => {
                        let mut elements = vec![];

                        // tag
                        let tag_range = ty.tag_range();
                        match NonZeroWidthRange::new(tag_range) {
                            Ok(tag_range) => {
                                let tag_value = lower_int_constant(&tag_range, &BigInt::from(variant));
                                elements.push(tag_value);
                            }
                            Err(ZeroWidth) => {}
                        };

                        // payload
                        if let Some(payload) = payload {
                            match self.lower_expression(span, payload)? {
                                Ok(payload) => {
                                    elements.push(payload);
                                }
                                Err(ZeroWidth) => {}
                            }
                        }

                        // padding, which is always zero
                        let payload_size = ty.variants[variant].as_ref().map_or(BigUint::ZERO, |v| v.size_bits());
                        let delta = ty.max_payload_size_bits() - payload_size;
                        if delta > BigInt::ZERO {
                            elements.push(Evaluated::String(format!("{}'b0", delta)));
                        }

                        // concatenation
                        assert!(!elements.is_empty(), "already checked for zero width earlier");
                        match elements.single() {
                            Ok(element) => element,
                            Err(elements) => {
                                Evaluated::String(format!("{{{}}}", elements.into_iter().rev().join(", ")))
                            }
                        }
                    }

                    IrExpressionLarge::Steps { base, steps } => {
                        let base_ty = base.ty(large, signals, variables);

                        let base = try_inner!(self.lower_expression_as_named(span, base)?);

                        if steps.is_empty() {
                            // avoid throwing away evaluated kind info
                            base
                        } else {
                            let steps = self.lower_target_steps(span, base_ty.clone(), steps)?;
                            Evaluated::String(format!("{base}{steps}"))
                        }
                    }
                    IrExpressionLarge::EnumTag { base } => {
                        let base_ty = base.ty(large, signals, variables).unwrap_enum();
                        let size_bits = base_ty.tag_size_bits();

                        let base = try_inner!(self.lower_expression_as_named(span, base)?);
                        evaluate_bit_slice(base, BigUint::ZERO, &BigUint::ONE, &size_bits)
                    }
                    &IrExpressionLarge::EnumPayload { ref base, variant } => {
                        let base_ty = base.ty(large, signals, variables).unwrap_enum();

                        let offset = base_ty.tag_size_bits();
                        let size_bits = base_ty.variants[variant]
                            .as_ref()
                            .expect("cannot get payload of non-payload variant")
                            .size_bits();

                        let base = try_inner!(self.lower_expression_as_named(span, base)?);
                        evaluate_bit_slice(base, offset, &BigUint::ONE, &size_bits)
                    }

                    IrExpressionLarge::ToBits(_ty, value) => {
                        // in verilog everything is just bits, so we don't need to do much work here
                        //   we do need to be careful when switching between bit/array representations for single bools
                        let value_ty = VerilogType::new_from_ir(diags, span, &value.ty(large, signals, variables))?
                            .expect("already checked zero-width result");
                        let value = self
                            .lower_expression(span, value)?
                            .expect("already checked zero-width result");

                        match value_ty {
                            VerilogType::Bit => {
                                // force cast to array through intermediate assignment
                                let tmp = self.new_temporary_assign(span, result_ty_verilog, value)?;
                                Evaluated::Temporary(tmp)
                            }
                            VerilogType::Array(_) => {
                                // already array, no need to do anything
                                value
                            }
                        }
                    }
                    IrExpressionLarge::FromBits(_ty, value) => {
                        // in verilog everything is just bits, so we don't need to do much work here
                        //   we do need to be careful when switching between bit/array representations for single bools
                        let value = self
                            .lower_expression(span, value)?
                            .expect("already checked zero-width result");

                        match result_ty_verilog {
                            VerilogType::Bit => {
                                // force cast to scalar through intermediate assignment
                                let tmp = self.new_temporary_assign(span, result_ty_verilog, value)?;
                                Evaluated::Temporary(tmp)
                            }
                            VerilogType::Array(_) => {
                                // already array, no need to do anything
                                value
                            }
                        }
                    }
                    IrExpressionLarge::ExpandIntRange(target, value) => {
                        let target =
                            NonZeroWidthRange::new(target.clone()).expect("already checked for zero-width earlier");
                        self.lower_expression_int_expanded(span, &target, value)?
                    }
                    IrExpressionLarge::ConstrainIntRange(range, value) => {
                        // already handled through the result type
                        let _ = range;

                        // TODO add assertions? what exactly are the semantics of this operation?
                        let value = match self.lower_expression(span, value)? {
                            Ok(value) => value,
                            Err(ZeroWidth) => return Ok(Err(ZeroWidth)),
                        };

                        // store in temporary to force truncation
                        let tmp = self.new_temporary_assign(span, result_ty_verilog, value)?;
                        Evaluated::Temporary(tmp)
                    }
                }
            }
        };
        Ok(Ok(eval))
    }

    /// Verilog does not care much about types, so many different expressions (array/struct/tuple/enum literals) all
    /// just turn into simple concatenations.
    /// The strict typing of the sub-expressions should ensure they all have the right width.
    ///
    /// We flip the concatenation order so that lower fields/indices end up at lower bit indices.
    fn lower_concatenation<'e, I: DoubleEndedIterator<Item = &'e IrExpression>>(
        &mut self,
        span: Span,
        elements: impl IntoIterator<IntoIter = I>,
    ) -> DiagResult<Evaluated<'static>> {
        let mut g = String::new();
        let mut any_prev = false;
        swrite!(g, "{{");
        for elem in elements.into_iter().rev() {
            let elem = match self.lower_expression(span, elem)? {
                Ok(elem) => elem,
                Err(ZeroWidth) => continue,
            };

            if any_prev {
                swrite!(g, ", ");
            }
            swrite!(g, "{elem}");
            any_prev = true;
        }
        swrite!(g, "}}");
        Ok(Evaluated::String(g))
    }

    fn lower_arithmetic_expression(
        &mut self,
        span: Span,
        result_range: &NonZeroWidthRange,
        result_ty_verilog: VerilogType,
        op: IrIntArithmeticOp,
        left: &IrExpression,
        right: &IrExpression,
    ) -> DiagResult<Evaluated<'n>> {
        // TODO do strength reduction to common IR optimization pass?
        // TODO strength reduction (where possible):
        //    * mul -> shift when power of 2
        //    * div/mod by power of 2 -> bit slice
        //    * div by constant -> https://llvm.org/doxygen/structllvm_1_1SignedDivisionByConstantInfo.html#details
        //    * pow of two -> shift
        //    * >, >=, ... -> ==, != if possible due to known ranges
        match op {
            IrIntArithmeticOp::Add => {
                self.lower_arithmetic_expression_simple(span, result_range, result_ty_verilog, "+", left, right)
            }
            IrIntArithmeticOp::Sub => {
                self.lower_arithmetic_expression_simple(span, result_range, result_ty_verilog, "-", left, right)
            }
            IrIntArithmeticOp::Mul => {
                // TODO replace multiplication with (constant?) power of two with shift
                self.lower_arithmetic_expression_simple(span, result_range, result_ty_verilog, "*", left, right)
            }
            IrIntArithmeticOp::FloorDiv => self.lower_arithmetic_expression_div_mod(
                span,
                result_range,
                result_ty_verilog,
                OperatorDivMod::FloorDiv,
                left,
                right,
            ),
            IrIntArithmeticOp::CeilDiv => self.lower_arithmetic_expression_div_mod(
                span,
                result_range,
                result_ty_verilog,
                OperatorDivMod::CeilDiv,
                left,
                right,
            ),
            IrIntArithmeticOp::Mod => self.lower_arithmetic_expression_div_mod(
                span,
                result_range,
                result_ty_verilog,
                OperatorDivMod::Mod,
                left,
                right,
            ),
            IrIntArithmeticOp::Pow => {
                // TODO do we actually need to expand left/right?
                self.lower_arithmetic_expression_simple(span, result_range, result_ty_verilog, "**", left, right)
            }
            IrIntArithmeticOp::Shl => {
                let left = self.lower_expression_int_expanded(span, result_range, left)?;
                let right = match self.lower_expression(span, right)? {
                    Ok(right) => right,
                    Err(ZeroWidth) => return Ok(left),
                };

                let expr = format_args!("{left} << {right}");
                let tmp = self.new_temporary_assign(span, result_ty_verilog, expr)?;
                Ok(Evaluated::Temporary(tmp))
            }
            IrIntArithmeticOp::Shr => {
                let left_can_be_neg = left
                    .ty(&self.module.large, &self.module.signals, self.variables)
                    .unwrap_int()
                    .start
                    .is_negative();

                let left = match self.lower_expression(span, left)? {
                    Ok(left) => left,
                    Err(ZeroWidth) => return Ok(lower_int_constant(result_range, &BigInt::ZERO)),
                };
                let right = match self.lower_expression(span, right)? {
                    Ok(right) => right,
                    Err(ZeroWidth) => return Ok(left),
                };

                let tmp = if left_can_be_neg {
                    // the final temporary assignment also casts away the signedness for us
                    let left_singed = left.as_signed();
                    let expr = format_args!("{left_singed} >>> {right}");
                    self.new_temporary_assign(span, result_ty_verilog, expr)?
                } else {
                    let expr = format_args!("{left} >> {right}");
                    self.new_temporary_assign(span, result_ty_verilog, expr)?
                };

                Ok(Evaluated::Temporary(tmp))
            }
        }
    }

    fn lower_arithmetic_expression_simple(
        &mut self,
        span: Span,
        result_range: &NonZeroWidthRange,
        result_ty_verilog: VerilogType,
        op_str: &str,
        left: &IrExpression,
        right: &IrExpression,
    ) -> DiagResult<Evaluated<'n>> {
        // expand operands to a common range that contains all operands and the result
        // TODO just constraining everything to the output bit representation should be correct too
        let range_left = left
            .ty(&self.module.large, &self.module.signals, self.variables)
            .unwrap_int();
        let range_right = right
            .ty(&self.module.large, &self.module.signals, self.variables)
            .unwrap_int();
        let range_all = result_range
            .range()
            .as_ref()
            .union(range_left.as_ref())
            .union(range_right.as_ref())
            .cloned();
        let range_all = NonZeroWidthRange::new(range_all).expect("result range is non-zero, so the union is too");

        // evaluate operands to that range
        let left = self.lower_expression_int_expanded(span, &range_all, left)?;
        let right = self.lower_expression_int_expanded(span, &range_all, right)?;

        // store result in a temporary to force truncation
        // TODO skip if no truncation is actually necessary?
        let expr = format_args!("{left} {op_str} {right}");
        let res_tmp = self.new_temporary_assign(span, result_ty_verilog, expr)?;

        Ok(Evaluated::Temporary(res_tmp))
    }

    fn lower_arithmetic_expression_div_mod(
        &mut self,
        span: Span,
        result_range: &NonZeroWidthRange,
        result_ty_verilog: VerilogType,
        op: OperatorDivMod,
        a: &IrExpression,
        b: &IrExpression,
    ) -> DiagResult<Evaluated<'n>> {
        // TODO replace division by constant with magic multiply + shift, EDA tools probably don't reliably do this
        // TODO warn for division by non-constant?
        let diags = self.diags;

        let range_a = a
            .ty(&self.module.large, &self.module.signals, self.variables)
            .unwrap_int();
        let range_b = b
            .ty(&self.module.large, &self.module.signals, self.variables)
            .unwrap_int();

        // TODO these ranges could be tighter in many cases
        let range_adj_one = ClosedNonEmptyRange {
            start: &BigInt::NEG_ONE,
            end: &BigInt::TWO,
        };
        let range_adj = range_binary_add(range_b.as_ref(), range_adj_one);
        let range_a_adj = match op {
            OperatorDivMod::FloorDiv | OperatorDivMod::Mod => range_binary_sub(range_a.as_ref(), range_adj.as_ref()),
            OperatorDivMod::CeilDiv => range_binary_add(range_a.as_ref(), range_adj.as_ref()),
        };
        let range_all = result_range
            .range()
            .as_ref()
            .union(range_a.as_ref())
            .union(range_b.as_ref())
            .union(range_adj_one)
            .union(range_adj.as_ref())
            .union(range_a_adj.as_ref())
            .cloned();
        let range_all = NonZeroWidthRange::new(range_all).expect("result range is non-zero, so the union is too");

        // evaluate operands to that range
        let a_raw = self.lower_expression_int_expanded(span, &range_all, a)?;
        let b_raw = self.lower_expression_int_expanded(span, &range_all, b)?;

        // cast operands to signed if necessary
        let signed = range_all.range().start.is_negative();
        let a = a_raw.as_signed_maybe(signed);
        let b = b_raw.as_signed_maybe(signed);

        // make adjustments to match IR semantics (round down or up) instead of verilog (truncate towards zero)
        let a_is_neg = MaybeBool::is_negative(&a, ClosedRange::from(range_a.as_ref()));
        let b_is_neg = MaybeBool::is_negative(&b, ClosedRange::from(range_b.as_ref()));
        let signs_differ = MaybeBool::xor(&a_is_neg, &b_is_neg);
        let res_expr = match op {
            OperatorDivMod::FloorDiv => {
                // truncation rounds up if the result is negative, adjust to round down instead
                let adj_one = b_is_neg.select("1", "-1");
                let adj = signs_differ.select(&format!("({b} + {adj_one})"), "0");
                let a_adj = format!("({a} - {adj})");
                format!("{a_adj} / {b}")
            }
            OperatorDivMod::CeilDiv => {
                // truncation rounds down if the result is positive, adjust to round up instead
                let adj_one = b_is_neg.select("1", "-1");
                let adj = signs_differ.select("0", &format!("({b} + {adj_one})"));
                let a_adj = format!("({a} + {adj})");
                format!("{a_adj} / {b}")
            }
            OperatorDivMod::Mod => {
                let ty_verilog_all = VerilogType::new_from_range(diags, span, &range_all)?;
                let expr = format_args!("{a} % {b}");
                let tmp_mod = self.new_temporary_assign(span, ty_verilog_all, expr)?;

                let should_adjust = MaybeBool::and(
                    &MaybeBool::is_not_zero(&tmp_mod, ClosedRange::from(result_range.range().as_ref())),
                    &signs_differ,
                );
                should_adjust.select(&format!("{tmp_mod} + {b}"), &tmp_mod.to_string())
            }
        };

        // store in temporary to force truncation
        let res_tmp = self.new_temporary_assign(span, result_ty_verilog, res_expr)?;
        Ok(Evaluated::Temporary(res_tmp))
    }

    // TODO doc
    fn lower_expression_non_zero_width(
        &mut self,
        span: Span,
        expr: &IrExpression,
        reason: &str,
    ) -> DiagResult<Evaluated<'n>> {
        self.lower_expression(span, expr)?.map_err(|_: ZeroWidth| {
            self.diags
                .report_error_internal(span, format!("{reason} cannot be zero-width"))
        })
    }

    fn lower_expression_int_expanded(
        &mut self,
        span: Span,
        range: &NonZeroWidthRange,
        value: &IrExpression,
    ) -> DiagResult<Evaluated<'n>> {
        // skip separate expansion step for integer constants
        if let IrExpression::Int(value) = value {
            return Ok(lower_int_constant(range, value));
        }

        // general case
        let value_ty = value.ty(&self.module.large, &self.module.signals, self.variables);
        let value_ty = value_ty.unwrap_int();

        let value = match self.lower_expression(span, value)? {
            Ok(value) => lower_expand_int_range(range.range().as_ref(), value_ty.as_ref(), value),
            Err(ZeroWidth) => {
                let value = value_ty.as_ref().as_single().unwrap();
                lower_int_constant(range, value)
            }
        };

        Ok(value)
    }

    fn lower_assignment(&mut self, span: Span, target: &IrAssignmentTarget, source: Evaluated<'n>) -> DiagResult {
        // TODO constant fold if some indices are constant?
        // TODO expose the extra knowledge we have about integer ranges to verilog?
        // TODO avoid emitting duplicate expressions due to shadowed stores
        let &IrAssignmentTarget { base, ref steps } = target;

        // evaluate indexing steps
        let base_ty = base.ty(&self.module.signals, self.variables);
        let steps = self.lower_target_steps(span, base_ty.clone(), steps)?;

        // actually do the assignment(s)
        let mut append_assign = |target: &LoweredName, assign_op: &str| {
            let indent = self.indent;
            swriteln!(self.f, "{indent}{target}{steps} {assign_op} {source};");
        };
        match base {
            IrSignalOrVariable::Variable(var) => {
                let name = unwrap_zero_width(self.name_map.map_var(var));
                append_assign(name, "=");
            }
            IrSignalOrVariable::Signal(signal) => {
                let name = unwrap_zero_width(self.name_map.module_name_map.map_signal(signal));

                if self.is_clocked_process {
                    append_assign(name, "<=");

                    let name_shadow = self.name_map.shadow_name_map.get(&signal);
                    if let Some(name_shadow) = name_shadow {
                        append_assign(name_shadow, "=");
                    }
                } else {
                    append_assign(name, "=");
                }
            }
        }

        Ok(())
    }

    fn lower_target_steps(&mut self, span: Span, base_ty: IrType, steps: &IrTargetSteps) -> DiagResult<String> {
        // if there are no steps, skip entirely
        if steps.is_empty() {
            return Ok(String::new());
        }

        // string building utils
        let mut g = String::new();
        swrite!(g, "[");

        let mut is_first_offset = true;
        let mut add_offset = |index: Evaluated, size_bits: &BigUint| {
            if !is_first_offset {
                swrite!(g, " + ");
            }
            is_first_offset = false;

            swrite!(g, "{}", index);
            if size_bits != &BigUint::ONE {
                swrite!(g, " * {}", size_bits);
            }
        };

        // handle steps
        // TODO use extra range knowledge index/start type ranges give us to generate less hardware
        let IrTargetSteps {
            steps_scalar,
            step_slice,
        } = steps;

        let bit_range = bit_index_range(&base_ty.size_bits());
        let mut curr_ty = base_ty;

        for step in steps_scalar {
            curr_ty = match step {
                IrTargetStepScalar::ArrayIndex(index) => {
                    let (element_ty, _) = curr_ty.unwrap_array();
                    let element_size_bits = element_ty.size_bits();

                    let index = self.lower_expression_int_expanded(span, &bit_range, index)?;
                    add_offset(index, &element_size_bits);

                    element_ty
                }
                &IrTargetStepScalar::TupleIndex(index) => {
                    let curr_ty = curr_ty.unwrap_tuple();
                    let start_bits = curr_ty[..index].iter().map(IrType::size_bits).sum::<BigUint>();

                    add_offset(Evaluated::String(start_bits.to_string()), &BigUint::ONE);

                    curr_ty.get_owned(index)
                }
                &IrTargetStepScalar::StructField(field) => {
                    let curr_ty = curr_ty.unwrap_struct();
                    let start_bits = curr_ty.field_offset(field);

                    add_offset(Evaluated::String(start_bits.to_string()), &BigUint::ONE);

                    curr_ty.fields.get_index_owned(field).unwrap().1
                }
            };
        }

        if let Some(step_slice) = step_slice {
            let IrTargetStepSlice { start, len } = step_slice;

            let (element_ty, _) = curr_ty.unwrap_array();
            let element_size_bits = element_ty.size_bits();

            let start = self.lower_expression_int_expanded(span, &bit_range, start)?;
            add_offset(start, &element_size_bits);

            curr_ty = IrType::Array(Box::new(element_ty), len.clone());
        }

        // correctly slice the final bit length
        let result_len_bits = curr_ty.size_bits();
        if result_len_bits != BigUint::ONE {
            swrite!(g, " +: {result_len_bits}");
        }
        swrite!(g, "]");

        Ok(g)
    }

    /// Create a new temporary and immediately assign the given value to it.
    /// This can be used to get a named expression, or to force truncation or type casts.
    fn new_temporary_assign(&mut self, span: Span, ty: VerilogType, value: impl Display) -> DiagResult<Temporary<'n>> {
        let tmp = self.new_temporary(span, ty)?;

        let indent = self.indent;
        swriteln!(self.f, "{indent}{tmp} = {value};");

        Ok(tmp)
    }

    fn new_temporary(&mut self, span: Span, ty: VerilogType) -> DiagResult<Temporary<'n>> {
        let name = self.name_scope.make_unique_str(self.diags, span, "tmp", true)?;

        let info = TemporaryInfo { name, ty };
        let info = self.temporaries.push(info);

        Ok(Temporary(&info.name))
    }
}

fn evaluate_bit_slice(
    base: Evaluated,
    start_index: impl Display,
    step_size_bits: &BigUint,
    len_bits: &BigUint,
) -> Evaluated<'static> {
    let mut g = String::new();
    swrite!(g, "({base}[{start_index}");
    if step_size_bits != &BigUint::ONE {
        swrite!(g, " * {step_size_bits}")
    };
    if len_bits != &BigUint::ONE {
        swrite!(g, " +: {len_bits}");
    }
    swrite!(g, "])");
    Evaluated::String(g)
}

/// Create a range that can be used for bit indexing, slicing and related math for the given size.
fn bit_index_range(size_bits: &BigUint) -> NonZeroWidthRange {
    let bit_index_range = ClosedNonEmptyRange {
        start: BigInt::ZERO,
        end: BigInt::from(size_bits + 1u8),
    };
    NonZeroWidthRange::new(bit_index_range).unwrap()
}

fn lower_expand_int_range<'n>(
    target_ty: ClosedNonEmptyRange<&BigInt>,
    value_ty: ClosedNonEmptyRange<&BigInt>,
    value: Evaluated<'n>,
) -> Evaluated<'n> {
    // cast the value to the right signedness
    //   and add a literal of the right sign and size to force expansion
    let target_repr = IntRepresentation::for_range(target_ty);
    let target_size = target_repr.size_bits();

    let value_repr = IntRepresentation::for_range(value_ty);
    let value_size = value_repr.size_bits();

    if target_size == value_size {
        return value;
    }

    // sign/zero-extend based on the signedness of the original value
    match value_repr.signed() {
        Signed::Signed => {
            // the result will be signed too, keep it that way for now to reduce unnecessary casts
            let value_signed = value.as_signed();
            Evaluated::SignedString(format!("({target_size}'sd0 + {value_signed})"))
        }
        Signed::Unsigned => Evaluated::String(format!("({target_size}'d0 + {value})")),
    }
}

fn lower_int_constant(ty: &NonZeroWidthRange, x: &BigInt) -> Evaluated<'static> {
    let ty = ty.range();
    assert!(ty.contains(x), "Trying to emit constant {x:?} encoded as range {ty:?}");

    let repr = IntRepresentation::for_range(ty.as_ref());
    let bits = repr.size_bits();
    assert_ne!(bits, 0);

    match repr.signed() {
        Signed::Unsigned => Evaluated::String(format!("{bits}'d{x}")),
        Signed::Signed => {
            let s = match x.sign() {
                Sign::Negative => {
                    // Verilog does not actually have negative literals, it's just the unary negation operator.
                    // This makes it tricky to expression the most negative value.
                    // The expression `max_pos_value` already overflows, becoming the most negative value,
                    //   so we should skip adding a leading negative sign.
                    let prefix_sign = if x == &repr.range().start { "" } else { "-" };
                    format!("{prefix_sign}{bits}'sd{}", x.abs())
                }
                Sign::Zero | Sign::Positive => format!("{bits}'sd{x}"),
            };
            Evaluated::SignedString(s)
        }
    }
}

#[derive(Debug)]
struct EdgeString<'n> {
    edge: &'static str,
    if_prefix: &'static str,
    signal: &'n LoweredName,
}

fn lower_edge<'n>(
    diags: &Diagnostics,
    name_map: ModuleNameMap<'n>,
    expr: Spanned<Polarized<IrSignal>>,
) -> DiagResult<EdgeString<'n>> {
    let Polarized { inverted, signal } = expr.inner;
    let (edge, if_prefix) = match inverted {
        false => ("posedge", ""),
        true => ("negedge", "!"),
    };

    match name_map.map_signal(signal) {
        Ok(signal) => Ok(EdgeString {
            edge,
            if_prefix,
            signal,
        }),
        Err(ZeroWidth) => Err(diags.report_error_internal(expr.span, "zero-width edge signal")),
    }
}

/// Range that is guaranteed to contain multiple values,
///   which means that it will be represented with at least one bit in hardware.
#[derive(Debug, Clone)]
pub struct NonZeroWidthRange(ClosedNonEmptyRange<BigInt>);

impl NonZeroWidthRange {
    const ZERO_ONE: NonZeroWidthRange = NonZeroWidthRange(ClosedNonEmptyRange {
        start: BigInt::ZERO,
        end: BigInt::TWO,
    });

    fn new(range: ClosedNonEmptyRange<BigInt>) -> Result<Self, ZeroWidth> {
        let repr = IntRepresentation::for_range(range.as_ref());
        if repr.size_bits() == 0 {
            Err(ZeroWidth)
        } else {
            Ok(NonZeroWidthRange(range))
        }
    }

    fn range(&self) -> &ClosedNonEmptyRange<BigInt> {
        &self.0
    }
}

#[derive(Debug, Copy, Clone)]
enum OperatorDivMod {
    FloorDiv,
    CeilDiv,
    Mod,
}

// TODO is this distinction actually useful?
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum VerilogType {
    /// Single bit value.
    ///
    /// This becomes `reg x;` in Verilog.
    Bit,
    /// Potentially multi-bit values. This can still happen to have width 1,
    /// The difference with [SingleBit] in that case is that this should still be represented as an array.
    ///
    /// This becomes `reg [n-1:0] x;` in Verilog.
    Array(NonZeroU32),
}

impl VerilogType {
    pub fn new_array(
        diags: &Diagnostics,
        span: Span,
        size_bits: BigUint,
    ) -> DiagResult<Result<VerilogType, ZeroWidth>> {
        let size_bits = diag_big_int_to_u32(diags, span, &size_bits.into(), "array width too large")?;
        let size_bits = try_inner!(NonZeroU32::new(size_bits).ok_or(ZeroWidth));
        Ok(Ok(VerilogType::Array(size_bits)))
    }

    pub fn new_from_ir(diags: &Diagnostics, span: Span, ty: &IrType) -> DiagResult<Result<VerilogType, ZeroWidth>> {
        match ty {
            IrType::Bool => Ok(Ok(VerilogType::Bit)),
            IrType::Int(_) | IrType::Array(_, _) | IrType::Tuple(_) | IrType::Struct(_) | IrType::Enum(_) => {
                Self::new_array(diags, span, ty.size_bits())
            }
        }
    }

    pub fn new_from_range(diags: &Diagnostics, span: Span, range: &NonZeroWidthRange) -> DiagResult<VerilogType> {
        let repr = IntRepresentation::for_range(range.range().as_ref());
        Ok(Self::new_array(diags, span, BigUint::from(repr.size_bits()))?.expect("range should be non-zero-width"))
    }

    pub fn size_bits(self) -> NonZeroU32 {
        match self {
            VerilogType::Bit => NonZeroU32::new(1).unwrap(),
            VerilogType::Array(width) => width,
        }
    }

    pub fn prefix(self) -> impl Display {
        struct P(VerilogType);

        impl Display for P {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self.0 {
                    VerilogType::Bit => Ok(()),
                    VerilogType::Array(width) => write!(f, "[{}:0] ", width.get() - 1),
                }
            }
        }

        P(self)
    }
}

#[derive(Debug, Copy, Clone)]
struct NewlineGenerator {
    any_prev_group: bool,
    any_prev_item: bool,
}

impl NewlineGenerator {
    pub fn new() -> Self {
        Self {
            any_prev_group: false,
            any_prev_item: false,
        }
    }

    pub fn start_group(&mut self) {
        self.any_prev_group |= self.any_prev_item;
        self.any_prev_item = false;
    }

    pub fn start_item(&mut self, f: &mut String) {
        if self.any_prev_group && !self.any_prev_item {
            swriteln!(f);
        }
        self.any_prev_item = true;
    }

    pub fn start_group_and_item(&mut self, f: &mut String) {
        self.start_group();
        self.start_item(f);
    }
}

fn diag_big_int_to_u32(diags: &Diagnostics, span: Span, value: &BigInt, message: &str) -> DiagResult<u32> {
    value.try_into().map_err(|_| {
        diags.report_error_simple(
            format!("{message}: overflow when converting {value} to u32"),
            span,
            "used here",
        )
    })
}

impl<S: AsRef<str>> LoweredName<S> {
    pub fn as_ref(&self) -> LoweredName<&str> {
        LoweredName(self.0.as_ref())
    }
}

impl<S: AsRef<str>> Display for LoweredName<S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let s = self.0.as_ref();
        if VERILOG_KEYWORDS.contains(s) {
            // emit escaped identifier,
            //   including extra trailing space just to be sure
            f.write_str(&format!("\\{s} "))
        } else {
            // TODO check for invalid chars and escape those, or at least throw an error
            f.write_str(s)
        }
    }
}

// Updated to "IEEE Standard for SystemVerilog", IEEE 1800-2023
// TODO also include vhdl keywords and ban both in generated output?
lazy_static! {
    static ref VERILOG_KEYWORDS: IndexSet<&'static str> = {
        include_str!("verilog_keywords.txt")
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .collect()
    };
}

fn maybe_id_as_ref(id: &Spanned<Option<String>>) -> Spanned<Option<&str>> {
    id.as_ref().map_inner(|s| s.as_ref().map(String::as_ref))
}

enum MaybeBool {
    Const(bool),
    Runtime(String),
}

impl MaybeBool {
    fn is_not_zero(v: &impl Display, r: ClosedRange<&BigInt>) -> MaybeBool {
        let can_be_zero = r.contains(&&BigInt::ZERO);
        let can_be_non_zero = r != ClosedRange::single(BigInt::ZERO).as_ref();

        if can_be_zero && can_be_non_zero {
            MaybeBool::Runtime(format!("({v} != 0)"))
        } else if can_be_zero {
            MaybeBool::Const(false)
        } else {
            MaybeBool::Const(true)
        }
    }

    fn is_negative(v: &impl Display, r: ClosedRange<&BigInt>) -> MaybeBool {
        let can_be_neg = r.start.is_negative();
        let can_be_non_neg = r.end.is_positive();

        if can_be_neg && can_be_non_neg {
            MaybeBool::Runtime(format!("({v} < 0)"))
        } else if can_be_neg {
            MaybeBool::Const(true)
        } else {
            MaybeBool::Const(false)
        }
    }

    fn select(&self, t: &str, f: &str) -> String {
        match self {
            MaybeBool::Const(true) => t.to_string(),
            MaybeBool::Const(false) => f.to_string(),
            MaybeBool::Runtime(c) => format!("({c} ? {t} : {f})"),
        }
    }

    fn xor(&self, other: &Self) -> MaybeBool {
        match (self, other) {
            (&MaybeBool::Const(a), &MaybeBool::Const(b)) => MaybeBool::Const(a ^ b),
            (MaybeBool::Const(false), MaybeBool::Runtime(other))
            | (MaybeBool::Runtime(other), MaybeBool::Const(false)) => MaybeBool::Runtime(other.to_string()),
            (MaybeBool::Const(true), MaybeBool::Runtime(other))
            | (MaybeBool::Runtime(other), MaybeBool::Const(true)) => MaybeBool::Runtime(format!("(!{})", other)),
            (MaybeBool::Runtime(a), MaybeBool::Runtime(b)) => MaybeBool::Runtime(format!("({} ^ {})", a, b)),
        }
    }

    fn and(&self, other: &Self) -> MaybeBool {
        match (self, other) {
            (&MaybeBool::Const(a), &MaybeBool::Const(b)) => MaybeBool::Const(a & b),
            (MaybeBool::Const(true), MaybeBool::Runtime(other))
            | (MaybeBool::Runtime(other), MaybeBool::Const(true)) => MaybeBool::Runtime(other.to_string()),
            (MaybeBool::Const(false), MaybeBool::Runtime(_)) | (MaybeBool::Runtime(_), MaybeBool::Const(false)) => {
                MaybeBool::Const(false)
            }
            (MaybeBool::Runtime(a), MaybeBool::Runtime(b)) => MaybeBool::Runtime(format!("({} && {})", a, b)),
        }
    }
}

fn compare_op_str(op: IrBoolCompareOp) -> &'static str {
    match op {
        IrBoolCompareOp::Eq => "==",
        IrBoolCompareOp::Neq => "!=",
    }
}

fn bitwise_op_str(op: IrBoolBinaryOp) -> &'static str {
    match op {
        IrBoolBinaryOp::And => "&",
        IrBoolBinaryOp::Or => "|",
        IrBoolBinaryOp::Xor => "^",
    }
}

fn unwrap_zero_width<T>(r: Result<T, ZeroWidth>) -> T {
    r.expect("zero width should have already been checked")
}

fn escape_verilog_str(s: &str) -> String {
    let mut f = String::new();

    for c in s.chars() {
        match c {
            '\n' => swrite!(f, "\\n"),
            '\t' => swrite!(f, "\\t"),
            '\\' => swrite!(f, "\\\\"),
            '"' => swrite!(f, "\\\""),
            '%' => swrite!(f, "%%"),
            _ => {
                if c.is_ascii() {
                    f.push(c);
                } else {
                    // verilog does not support unicode strings, so replace non-ascii with '?'
                    f.push('?');
                }
            }
        }
    }

    f
}

fn write_line_separated_strings(f: &mut String, strings: &[&str]) {
    let mut prev = false;

    for s in strings {
        if s.is_empty() {
            continue;
        }

        if prev {
            f.push('\n');
        }

        f.push_str(s);
        prev = true;
    }
}
