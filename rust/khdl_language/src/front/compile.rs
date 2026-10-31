use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::DomainSignal;
use crate::front::flow::NextFlowRootId;
use crate::front::item::{ElaboratedModule, ElaborationArenas};
use crate::front::module_header::ElaboratedModuleHeader;
use crate::front::print::PrintHandler;
use crate::front::scope::{DeclaredValueSingle, FrozenScope, ScopedEntry};
use crate::front::signal::{
    Polarized, Port, PortInfo, PortInterface, PortInterfaceInfo, Signal, Wire, WireInfo, WireInterface,
    WireInterfaceInfo,
};
use crate::front::value::{CompileValue, SimpleCompileValue, Value};
use crate::mid::ir::{IrDatabase, IrLargeArena, IrModule, IrModuleInfo, IrModules, IrSignal};
use crate::syntax::ast::{
    self, Expression, ExpressionKind, Identifier, ImportFinalKind, MaybeIdentifier, SimpleIdentifier, Visibility,
};
use crate::syntax::data_inputs::DataInputs;
use crate::syntax::hierarchy::{HierarchyNode, SourceHierarchy};
use crate::syntax::parsed::{AstRefItem, AstRefModuleInternal, ParsedDatabase};
use crate::syntax::pos::{Span, Spanned};
use crate::syntax::source::{FileId, SourceDatabase};
use crate::util::arena::Arena;
use crate::util::data::{IndexMapExt, NonEmptyVec};
use crate::util::edit_distance::hint_options_by_edit_distance;
use crate::util::intern::{Id, Interner};
use crate::util::pool::ThreadPool;
use crate::util::sync::{ComputeOnceArena, SharedQueue};
use crate::util::{ResultDoubleExt, ResultExt};
use indexmap::{IndexMap, IndexSet};
use itertools::{Itertools, zip_eq};
use khdl_util::constants::{MAX_IMPORT_SUGGESTIONS, STACK_OVERFLOW_ERROR_ENTRIES_SHOWN, STACK_OVERFLOW_STACK_LIMIT};
use rand::seq::SliceRandom;
use std::borrow::Borrow;
use std::fmt::Debug;
use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex, OnceLock};

#[derive(Debug)]
pub enum ResolveError {
    EmptyPath,
    ItemNotFound,
}

impl<'a, 's> CompileRefs<'a, 's> {
    pub fn run_compile_loop(self, pool: Option<&ThreadPool>) {
        if let Some(pool) = pool {
            let all_thread_diags = pool.broadcast(|| {
                let thread_diags = Diagnostics::new();
                let thread_refs = CompileRefs {
                    diags: &thread_diags,

                    fixed: self.fixed,
                    shared: self.shared,
                    print_handler: self.print_handler,
                    should_stop: self.should_stop,
                    interrupted_local: &OnceLock::new(),
                };
                thread_refs.run_compile_loop_inner();
                thread_diags
            });

            // collect and merge diagnostics, sorting to keep them deterministic
            // TODO some kind of topological sort "as if visited by single thread" might be nicer
            let mut all_diags: Vec<_> = all_thread_diags.into_iter().flat_map(|d| d.finish()).collect();
            all_diags.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
            for d in all_diags {
                self.diags.push(d);
            }
        } else {
            // run elaboration on the current thread
            let local_diags = Diagnostics::new();
            let local_refs = CompileRefs {
                diags: &local_diags,

                fixed: self.fixed,
                shared: self.shared,
                print_handler: self.print_handler,
                should_stop: self.should_stop,
                interrupted_local: &OnceLock::new(),
            };
            local_refs.run_compile_loop_inner();

            // sort diagnostics here too, to match threaded case
            let mut local_diags = local_diags.finish();
            local_diags.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
            for d in local_diags {
                self.diags.push(d);
            }
        }
    }

    fn run_compile_loop_inner(self) {
        while let Some(work_item) = self.shared.work_queue.pop() {
            match work_item {
                WorkItem::EvaluateItem(item) => {
                    self.shared.item_values.offer_to_compute(item, || {
                        let mut ctx = CompileItemContext::new_empty(self, Some(item), None);
                        ctx.eval_item_new(item)
                    });
                }
                WorkItem::ElaborateModuleBody(header, ir_module) => {
                    // do elaboration
                    let ir_module_info = self.elaborate_module_body_new(header);

                    // store result
                    let slot = &mut self.shared.ir_database.lock().unwrap().modules[ir_module];
                    assert!(slot.is_none());
                    *slot = Some(ir_module_info);
                }
            }
        }
    }

    pub fn check_should_stop(self, span: Span) -> DiagResult {
        if let Some(&e) = self.interrupted_local.get() {
            return Err(e);
        }
        if (self.should_stop)() {
            self.shared.work_queue.abort();
            let e = *self.interrupted_local.get_or_init(|| {
                self.diags
                    .report_error_simple("compilation interrupted", span, "while elaborating here")
            });
            let _ = self.shared.interrupted.set(e);
            return Err(e);
        }
        Ok(())
    }

    pub fn get_expr(self, expr: Expression) -> &'a ExpressionKind {
        self.fixed.parsed.get_expr(expr)
    }

    pub fn get_expr_inner(self, expr: Expression) -> &'a ExpressionKind {
        let mut curr = expr;
        loop {
            match self.get_expr(curr) {
                &ExpressionKind::Wrapped(inner) => curr = inner,
                kind => break kind,
            }
        }
    }

    /// Resolve a dot-separated path, using the same rules as imports.
    /// If `allow_private` is set, private items are accessible too.
    pub fn resolve_path(self, path: Spanned<&str>, allow_private: bool) -> DiagResult<ImportValue> {
        let diags = self.diags;

        if path.inner.is_empty() {
            return Err(diags.report_error_simple("path cannot be empty", path.span, "empty path here"));
        }

        // split path, try to preserve span info
        let path_split = {
            let exact = self.fixed.source.span_str(path.span) == path.inner;
            let mut offset = path.span.start_byte;
            path.inner
                .split(".")
                .map(|step| {
                    let span = match exact {
                        true => Span::new(path.span.file, offset, offset + step.len()),
                        false => path.span,
                    };
                    offset += step.len() + 1;
                    Spanned::new(span, step)
                })
                .collect_vec()
        };

        if path_split.iter().any(|step| step.inner.is_empty()) {
            let title = format!("path `{}` contains an empty step", path.inner);
            return Err(diags.report_error_simple(title, path.span, "path here"));
        }
        let (&final_, steps) = path_split.split_last().unwrap();

        // call into existing import machinery
        let base = resolve_import_steps(diags, self.fixed.hierarchy, steps.iter().copied())?;
        resolve_import_final(
            diags,
            &self.shared.interner,
            self.fixed.hierarchy,
            &self.shared.file_scopes,
            base,
            steps.last().map(|pre_final| steps[0].span.join(pre_final.span)),
            final_,
            allow_private,
        )
    }

    pub fn eval_item(self, item: AstRefItem) -> DiagResult<&'s CompileValue> {
        let mut ctx = CompileItemContext::new_empty(self, None, None);
        ctx.eval_item(item)
    }
}

/// globally shared, constant state
#[derive(Copy, Clone)]
pub struct CompileFixed<'a> {
    pub settings: &'a CompileSettings,
    pub source: &'a SourceDatabase,
    pub hierarchy: &'a SourceHierarchy,
    pub parsed: &'a ParsedDatabase,
    pub data_inputs: &'a DataInputs,
}

#[derive(Debug, Clone)]
pub struct CompileSettings {
    pub do_ir_cleanup: bool,
}

#[derive(Debug, Copy, Clone)]
pub enum QueueItems {
    None,
    All,
}

#[derive(Debug)]
pub enum WorkItem {
    EvaluateItem(AstRefItem),
    ElaborateModuleBody(ElaboratedModuleHeader<AstRefModuleInternal>, IrModule),
}

/// long-term shared between threads
pub struct CompileShared {
    pub file_scopes: FileScopes<Arc<FrozenScope>>,

    pub work_queue: SharedQueue<WorkItem>,

    pub interner: Interner,

    pub item_values: ComputeOnceArena<AstRefItem, DiagResult<CompileValue>, StackEntry>,
    pub elaboration_arenas: ElaborationArenas,
    // TODO make this a non-blocking collection thing, could be thread-local collection and merging or a channel
    //   or maybe just another sharded DashMap
    pub ir_database: Mutex<IrDatabasePartial>,
    pub next_flow_root_id: NextFlowRootId,
    // interrupted by any thread
    pub interrupted: OnceLock<DiagError>,
}

#[derive(Debug, Clone)]
pub struct IrDatabasePartial {
    pub modules: IrModules<Option<DiagResult<IrModuleInfo>>>,
    pub external_modules: IndexSet<String>,
}

pub type FileScopes<S> = IndexMap<FileId, DiagResult<FileScope<S>>>;

pub struct FileScope<S> {
    pub declared: IndexMap<Id, DiagResult<DeclaredItem>>,
    pub scope: S,
}

#[derive(Copy, Clone)]
pub struct DeclaredItem {
    span_id: Span,
    vis: Visibility,
    item: AstRefItem,
}

#[derive(Copy, Clone)]
pub struct CompileRefs<'a, 's> {
    pub diags: &'a Diagnostics,
    // TODO maybe inline this
    pub fixed: CompileFixed<'a>,
    pub shared: &'s CompileShared,
    // TODO is there a reasonable way to get deterministic prints?
    pub print_handler: &'a (dyn PrintHandler + Sync),
    pub should_stop: &'a (dyn Fn() -> bool + Sync),
    // interrupted by the current thread
    pub interrupted_local: &'a OnceLock<DiagError>,
}

pub type ArenaPorts = Arena<Port, PortInfo>;
pub type ArenaPortInterfaces = Arena<PortInterface, PortInterfaceInfo>;

pub struct CompileItemContext<'a, 's> {
    // TODO maybe inline this
    pub refs: CompileRefs<'a, 's>,

    // TODO all of this should really be part of some kind of CompileModuleContext, instead of CompileItemContext
    pub ports: ArenaPorts,
    pub port_interfaces: Arena<PortInterface, PortInterfaceInfo>,
    pub wires: Arena<Wire, WireInfo>,
    pub wire_interfaces: Arena<WireInterface, WireInterfaceInfo>,
    pub large: IrLargeArena,

    pub curr_module: Option<ElaboratedModule>,

    pub origin: Option<AstRefItem>,
    pub call_stack: Vec<StackEntry>,
}

#[derive(Debug, Copy, Clone)]
pub enum StackEntry {
    ItemUsage(Span),
    ItemEvaluation(Span),
    FunctionCall(Span),
    FunctionRun(Span),
}

impl StackEntry {
    pub fn into_span_message(self, depth: usize) -> (Span, String) {
        let (span, msg) = match self {
            StackEntry::ItemUsage(span) => (span, "item used here"),
            StackEntry::ItemEvaluation(span) => (span, "item declared here"),
            StackEntry::FunctionCall(span) => (span, "function call here"),
            StackEntry::FunctionRun(span) => (span, "function declared here"),
        };

        (span, format!("[{depth}] {msg}"))
    }
}

impl<'a, 's> CompileItemContext<'a, 's> {
    pub fn new_empty(
        refs: CompileRefs<'a, 's>,
        origin: Option<AstRefItem>,
        curr_module: Option<ElaboratedModule>,
    ) -> Self {
        Self::new_restore(refs, origin, curr_module, Arena::new(), Arena::new())
    }

    pub fn new_restore(
        refs: CompileRefs<'a, 's>,
        origin: Option<AstRefItem>,
        curr_module: Option<ElaboratedModule>,
        ports: ArenaPorts,
        port_interfaces: ArenaPortInterfaces,
    ) -> Self {
        CompileItemContext {
            refs,
            ports,
            port_interfaces,
            wires: Arena::new(),
            wire_interfaces: Arena::new(),
            large: IrLargeArena::new(),
            origin,
            curr_module,
            call_stack: vec![],
        }
    }

    pub fn recurse<R>(&mut self, entry: StackEntry, f: impl FnOnce(&mut Self) -> R) -> DiagResult<R> {
        if self.call_stack.len() >= STACK_OVERFLOW_STACK_LIMIT {
            return Err(stack_overflow_diagnostic(&self.call_stack).report(self.refs.diags));
        }

        self.call_stack.push(entry);
        let len = self.call_stack.len();

        let result = f(self);

        assert_eq!(self.call_stack.len(), len);
        self.call_stack.pop().unwrap();

        Ok(result)
    }

    pub fn eval_import_value(&mut self, value: ImportValue) -> DiagResult<CompileValue> {
        match value {
            ImportValue::HierarchyNode(node) => Ok(CompileValue::Simple(SimpleCompileValue::Package(node))),
            ImportValue::Item(item) => self.eval_item(item).cloned(),
        }
    }

    pub fn eval_item(&mut self, item: AstRefItem) -> DiagResult<&'s CompileValue> {
        let item_span = self.refs.fixed.parsed[item].info().span_short;
        let stack_entry = StackEntry::ItemEvaluation(item_span);

        self.recurse(stack_entry, |s| {
            let origin = s.origin.map(|origin| (origin, s.call_stack.clone()));
            let f_compute = || {
                let mut ctx = CompileItemContext::new_empty(s.refs, Some(item), None);
                ctx.eval_item_new(item)
            };
            let f_cycle = |stack: Vec<&StackEntry>| cycle_diagnostic(stack).report(s.refs.diags);
            s.refs
                .shared
                .item_values
                .get_or_compute(origin, item, f_compute, f_cycle)
                .map(ResultExt::as_ref_ok)
                .flatten_err()
        })
        .flatten_err()
    }
}

fn cycle_diagnostic(mut stack: Vec<&StackEntry>) -> DiagnosticError {
    // rotate the stack to keep error messages deterministic
    assert!(!stack.is_empty());
    let min_index = stack
        .iter()
        .position_min_by_key(|entry| entry.into_span_message(0).0)
        .unwrap();
    stack.rotate_left(min_index);
    let stack = NonEmptyVec::try_from(stack).unwrap();

    // create the diagnostic
    let mut next_index: usize = 0;
    let messages = stack.map(|entry| {
        let index = next_index;
        next_index += 1;
        entry.into_span_message(index)
    });

    DiagnosticError::new_multiple("encountered cyclic dependency", messages)
}

fn stack_overflow_diagnostic(stack: &Vec<StackEntry>) -> DiagnosticError {
    assert!(!stack.is_empty());

    let mut messages = vec![];

    let skipped = if stack.len() <= 2 * STACK_OVERFLOW_ERROR_ENTRIES_SHOWN {
        for depth in 0..stack.len() {
            messages.push(stack[depth].into_span_message(depth));
        }
        None
    } else {
        for depth in 0..STACK_OVERFLOW_ERROR_ENTRIES_SHOWN {
            messages.push(stack[depth].into_span_message(depth));
        }
        for depth in (stack.len() - STACK_OVERFLOW_ERROR_ENTRIES_SHOWN)..stack.len() {
            messages.push(stack[depth].into_span_message(depth));
        }
        Some(stack.len() - 2 * STACK_OVERFLOW_ERROR_ENTRIES_SHOWN)
    };

    let mut diag = DiagnosticError::new_multiple(
        format!("stack overflow, stack depth {}", stack.len()),
        NonEmptyVec::try_from(messages).unwrap(),
    );

    if let Some(skipped) = skipped {
        diag = diag.add_footer_info(format!("skipped showing {} stack entries in the middle", skipped))
    }

    diag
}

#[derive(Debug, Clone)]
pub enum CompileStackEntry {
    Item(AstRefItem),
    FunctionCall(Span),
    FunctionRun(AstRefItem, Vec<Value>),
}

fn populate_file_scopes(diags: &Diagnostics, fixed: CompileFixed, interner: &Interner) -> FileScopes<Arc<FrozenScope>> {
    let CompileFixed {
        settings: _,
        source,
        hierarchy,
        parsed,
        data_inputs: _,
    } = fixed;

    // pass 0: add all declared items to the file scope
    let mut file_scopes: FileScopes<FrozenScope> = IndexMap::new();
    for file in hierarchy.files() {
        let file_node = &hierarchy[hierarchy.file_node(file).unwrap()];

        let scope = parsed[file].as_ref_ok().map(|ast| {
            let mut declared = IndexMap::new();
            let mut scope = FrozenScope::new(ast.span);

            for (ast_item_ref, ast_item) in ast.items_with_ref() {
                if let Some(info) = ast_item.info().declaration {
                    // skip items with an id that we can't determine here, they are reported as errors
                    if let Ok(id) = require_maybe_simple_id(diags, info.id, "top-level item") {
                        let id = id.map_id(|id| id.spanned_str(source).map_inner(|id| interner.push(id)));
                        scope.declare(diags, interner, id, Ok(ScopedEntry::Item(ast_item_ref)));

                        // insert the item in the declared map as well,
                        //   items can't have the same name as a child node, that would make imports ambiguous
                        if let MaybeIdentifier::Identifier(id) = id {
                            let result = scope.find(diags, interner, id).and_then(|_| {
                                let id_str = id.inner.str(interner);
                                match file_node.children.get(id_str) {
                                    None => Ok(DeclaredItem {
                                        span_id: id.span,
                                        vis: info.vis,
                                        item: ast_item_ref,
                                    }),
                                    Some(_) => {
                                        let title = format!("item `{id_str}` has the same name as a child package");
                                        Err(diags.report_error_simple(title, id.span, "item declared here"))
                                    }
                                }
                            });
                            declared.insert(id.inner, result);
                        }
                    }
                }
            }

            FileScope { declared, scope }
        });

        file_scopes.insert_first(file, scope);
    }

    // pass 1: resolve all imports and collect the imported items
    // (don't immediately add them, then then would already be visible for later imports from other files)
    let mut file_imported_items: Vec<Vec<(MaybeIdentifier<Spanned<Id>>, DiagResult<ScopedEntry>)>> = vec![];
    for target_file in hierarchy.files() {
        let mut curr_imported_items = vec![];

        if let Ok(target_file_ast) = &parsed[target_file] {
            for item in &target_file_ast.items {
                if let ast::Item::Import(item) = item {
                    let ast::ItemImport { span: _, steps, final_ } = item;

                    let base_span = steps
                        .inner
                        .first()
                        .map(|first| first.span.join(steps.inner.last().unwrap().span));
                    let steps = steps.inner.iter().map(|step| step.spanned_str(source));
                    let base = resolve_import_steps(diags, hierarchy, steps);

                    let entries = match &final_.inner {
                        ImportFinalKind::Single(entry) => std::slice::from_ref(entry),
                        ImportFinalKind::Multi(entries) => entries,
                    };

                    for entry in entries {
                        let &ast::ImportEntry { span: _, id, as_ } = entry;

                        // eval ids
                        let id_str = id.spanned_str(source);
                        let id = Spanned::new(id.span, interner.push(id_str.inner));
                        let as_ =
                            as_.map(|as_| as_.map_id(|as_| Spanned::new(as_.span, interner.push(as_.str(source)))));

                        // find entry
                        let value = base.and_then(|base| {
                            resolve_import_final(
                                diags,
                                interner,
                                hierarchy,
                                &file_scopes,
                                base,
                                base_span,
                                id_str,
                                false,
                            )
                        });

                        // map to entry
                        let entry = value.map(|value| match value {
                            ImportValue::HierarchyNode(node) => {
                                ScopedEntry::Value(Value::Simple(SimpleCompileValue::Package(node)))
                            }
                            ImportValue::Item(item) => ScopedEntry::Item(item),
                        });

                        // store pair
                        let target_id = match as_ {
                            Some(as_) => as_,
                            None => MaybeIdentifier::Identifier(id),
                        };
                        curr_imported_items.push((target_id, entry));
                    }
                }
            }
        }

        file_imported_items.push(curr_imported_items);
    }

    // pass 2: actually add the imported items to the file scopes
    for (target_file, items) in zip_eq(hierarchy.files(), file_imported_items) {
        if let Ok(scope) = file_scopes.get_mut(&target_file).unwrap() {
            for (target_id, value) in items {
                scope.scope.declare(diags, interner, target_id, value);
            }
        }
    }

    // pass 3: add prelude items to all files scopes
    // TODO this silently does nothing if:
    //   * the std files are missing
    //   * std contains name collisions
    let mut prelude_imported_items = vec![];
    for std_file in ["types", "util", "math"] {
        let file = hierarchy[hierarchy.root_node()]
            .children
            .get("std")
            .and_then(|&n| hierarchy[n].children.get(std_file))
            .and_then(|&n| hierarchy[n].file);

        if let Some(file) = file {
            let scope = &file_scopes.get(&file).unwrap();
            if let Ok(scope) = scope {
                let public_items = scope.declared.iter().filter(|(_, item)| match item {
                    Ok(item) => match item.vis {
                        Visibility::Public { .. } => true,
                        Visibility::Private => false,
                    },
                    Err(_) => true,
                });
                prelude_imported_items.extend(public_items.map(|(&k, &v)| (k, v)));
            }
        }
    }
    for file in hierarchy.files() {
        if let Ok(scope) = file_scopes.get_mut(&file).unwrap() {
            for &(id, item) in &prelude_imported_items {
                if !scope.scope.has_immediate_entry(id) {
                    let value = match item {
                        Ok(item) => DeclaredValueSingle::Value {
                            span: item.span_id,
                            value: ScopedEntry::Item(item.item),
                        },
                        Err(e) => DeclaredValueSingle::Error(e),
                    };
                    scope.scope.declare_already_checked(id, value);
                }
            }
        }
    }

    file_scopes
        .into_iter()
        .map(|(k, v)| {
            let v = v.map(|v| FileScope {
                declared: v.declared,
                scope: Arc::new(v.scope),
            });
            (k, v)
        })
        .collect()
}

fn require_maybe_simple_id(
    diags: &Diagnostics,
    id: MaybeIdentifier<Identifier>,
    reason: &str,
) -> DiagResult<MaybeIdentifier<SimpleIdentifier>> {
    match id {
        MaybeIdentifier::Dummy { span } => Ok(MaybeIdentifier::Dummy { span }),
        MaybeIdentifier::Identifier(id) => match id {
            Identifier::Simple(id) => Ok(MaybeIdentifier::Identifier(id)),
            Identifier::FromString(span, _) => {
                let msg = format!("{reason} must have a simple identifier");
                Err(diags.report_error_simple(msg, span, "`ident` used here"))
            }
        },
    }
}

fn resolve_import_steps<'s>(
    diags: &Diagnostics,
    hierarchy: &SourceHierarchy,
    path: impl IntoIterator<Item = Spanned<&'s str>>,
) -> DiagResult<HierarchyNode> {
    let (node, _) = path.into_iter().try_fold(
        (hierarchy.root_node(), None),
        |(node, base_span): (_, Option<Span>), step| {
            let children = &hierarchy[node].children;
            match children.get(step.inner) {
                Some(&child_node) => {
                    let base_span = base_span.map_or(step.span, |base_span| base_span.join(step.span));
                    Ok((child_node, Some(base_span)))
                }
                None => {
                    let options = children.keys().map(String::as_str).collect_vec();
                    Err(report_import_not_found(
                        diags, hierarchy, node, base_span, step, options,
                    ))
                }
            }
        },
    )?;
    Ok(node)
}

/// Report that `step` could not be found in package `base`.
/// `base_span` is the span of the expression that evaluated to `base`, `None` for the root package.
fn report_import_not_found(
    diags: &Diagnostics,
    hierarchy: &SourceHierarchy,
    base: HierarchyNode,
    base_span: Option<Span>,
    step: Spanned<&str>,
    options: Vec<&str>,
) -> DiagError {
    let title = if base == hierarchy.root_node() {
        format!("root package has no member `{}`", step.inner)
    } else {
        format!(
            "package `{}` has no member `{}`",
            hierarchy[base].steps.join("."),
            step.inner
        )
    };
    let mut diag = DiagnosticError::new(title, step.span, "not found");
    if let Some(base_span) = base_span {
        diag = diag.add_info(
            base_span,
            format!("this is package `{}`", hierarchy[base].steps.join(".")),
        );
    }
    if let Some(hint) = hint_options_by_edit_distance(step.inner, options, MAX_IMPORT_SUGGESTIONS) {
        diag = diag.add_footer_hint(hint);
    }
    diag.report(diags)
}

#[derive(Debug, Copy, Clone)]
pub enum ImportValue {
    HierarchyNode(HierarchyNode),
    Item(AstRefItem),
}

pub fn resolve_import_final<S: Borrow<FrozenScope>>(
    diags: &Diagnostics,
    interner: &Interner,
    hierarchy: &SourceHierarchy,
    file_scopes: &FileScopes<S>,
    base: HierarchyNode,
    base_span: Option<Span>,
    final_: Spanned<&str>,
    allow_private: bool,
) -> DiagResult<ImportValue> {
    let base_info = &hierarchy[base];

    // search for both options
    let node = base_info.children.get(final_.inner).copied();
    let item = base_info
        .file
        .map(|file| {
            let Some(final_id) = interner.find(final_.inner) else {
                return Ok(None);
            };
            let scope = file_scopes.get(&file).unwrap().as_ref_ok()?;
            scope.declared.get(&final_id).map(ResultExt::as_ref_ok).transpose()
        })
        .transpose()?
        .flatten();

    // pick the result
    // if there is exactly one matching option, return it
    // if there are two, report an internal error, this should have been checked earlier already
    match (node, item) {
        (Some(node), None) => {
            // simple hierarchy node
            Ok(ImportValue::HierarchyNode(node))
        }
        (None, Some(item)) => {
            // item import
            // check visibility, but still proceed as if the import succeeded
            if !allow_private {
                match item.vis {
                    Visibility::Public { span: _ } => {}
                    Visibility::Private => {
                        let _ = DiagnosticError::new(
                            format!("cannot import private item `{}`", final_.inner),
                            final_.span,
                            "not accessible here",
                        )
                        .add_info(item.span_id, "item declared as private here")
                        .add_footer_info("private items cannot be imported")
                        .report(diags);
                    }
                }
            }
            Ok(ImportValue::Item(item.item))
        }
        (None, None) => {
            let mut options = base_info.children.keys().map(String::as_str).collect_vec();
            if let Some(file) = base_info.file
                && let Ok(scope) = file_scopes.get(&file).unwrap()
            {
                let items = scope.declared.iter().filter_map(|(id, item)| {
                    let item = item.as_ref().ok()?;
                    let visible = allow_private || matches!(item.vis, Visibility::Public { span: _ });
                    visible.then(|| id.str(interner))
                });
                options.extend(items);
            }
            Err(report_import_not_found(
                diags, hierarchy, base, base_span, final_, options,
            ))
        }
        (Some(_), Some(_)) => Err(diags.report_error_internal(
            final_.span,
            "items with the same name as a child package should have been reported already",
        )),
    }
}

impl CompileShared {
    pub fn new(diags: &Diagnostics, fixed: CompileFixed, queue_items: QueueItems, thread_count: NonZeroUsize) -> Self {
        let interner = Interner::new(thread_count);
        let file_scopes = populate_file_scopes(diags, fixed, &interner);

        // pass over all items, to:
        // * collect all non-import items for the compute arena
        // * find all external modules
        let mut items = vec![];
        let mut external_modules: IndexMap<String, Vec<Span>> = IndexMap::new();
        for file in fixed.hierarchy.files() {
            if let Ok(file_ast) = &fixed.parsed[file] {
                for (item_ref, item) in file_ast.items_with_ref() {
                    if !matches!(item, ast::Item::Import(_)) {
                        items.push(item_ref);
                    }
                    if let ast::Item::ModuleExternal(module) = item {
                        external_modules
                            .entry(module.id.str(fixed.source).to_owned())
                            .or_default()
                            .push(module.id.span);
                    }
                }
            }
        }

        // check for duplicate external modules
        for (name, spans) in &external_modules {
            if spans.len() > 1 {
                let messages = spans
                    .iter()
                    .map(|&span| (span, "defined here".to_owned()))
                    .collect_vec();
                let messages = NonEmptyVec::try_from(messages).unwrap();

                let _ = DiagnosticError::new_multiple(
                    format!("external module with name `{name}` declared twice"),
                    messages,
                )
                .report(diags);
            }
        }
        let external_modules = external_modules.into_keys().collect();

        let item_values = ComputeOnceArena::new(thread_count);

        // populate work queue
        // TODO shuffle or not?
        //   * which is actually faster? (for mutex contention)
        //   * do we want to shuffle anyway to test that the compiler is deterministic?
        let work_queue = SharedQueue::new(thread_count);
        match queue_items {
            QueueItems::None => {}
            QueueItems::All => {
                items.shuffle(&mut rand::thread_rng());
                work_queue.push_batch(items.into_iter().map(WorkItem::EvaluateItem));
            }
        }

        CompileShared {
            file_scopes,
            work_queue,
            item_values,
            elaboration_arenas: ElaborationArenas::new(),
            interner,
            ir_database: Mutex::new(IrDatabasePartial {
                modules: Arena::new(),
                external_modules,
            }),
            next_flow_root_id: NextFlowRootId::default(),
            interrupted: OnceLock::new(),
        }
    }

    pub fn file_scope(&self, file: FileId) -> DiagResult<&FileScope<Arc<FrozenScope>>> {
        self.file_scopes.get(&file).unwrap().as_ref_ok()
    }

    pub fn finish_ir_database(self, diags: &Diagnostics, dummy_span: Span) -> DiagResult<IrDatabase> {
        finish_ir_database_impl(
            diags,
            dummy_span,
            &self.work_queue,
            &self.interrupted,
            self.ir_database.into_inner().unwrap(),
        )
    }

    pub fn finish_ir_database_ref(&self, diags: &Diagnostics, dummy_span: Span) -> DiagResult<IrDatabase> {
        let ir_database = self.ir_database.lock().unwrap().clone();
        finish_ir_database_impl(diags, dummy_span, &self.work_queue, &self.interrupted, ir_database)
    }
}

fn finish_ir_database_impl(
    diags: &Diagnostics,
    dummy_span: Span,
    work_queue: &SharedQueue<WorkItem>,
    interrupted: &OnceLock<DiagError>,
    ir_database: IrDatabasePartial,
) -> DiagResult<IrDatabase> {
    if let Some(&e) = interrupted.get() {
        return Err(e);
    }

    // check that work queue is empty
    if work_queue.pop().is_some() {
        return Err(diags.report_error_internal(dummy_span, "not all work items have been processed"));
    }

    // check that all modules have been elaborated
    let IrDatabasePartial {
        modules,
        external_modules,
    } = ir_database;
    let modules = modules.try_map_values(|_, v| match v {
        Some(Ok(v)) => Ok(v),
        Some(Err(e)) => Err(e),
        None => Err(diags.report_error_internal(dummy_span, "not all modules were elaborated")),
    })?;

    // check that there are no cycles
    IrDatabase::new_check_cycles(diags, modules, external_modules)
}

// TODO move somewhere else
impl CompileItemContext<'_, '_> {
    pub fn domain_signal_to_ir(&mut self, signal: Spanned<DomainSignal>) -> DiagResult<Polarized<IrSignal>> {
        let signal_span = signal.span;
        signal.inner.try_map_inner(|signal| {
            let signal_ir = match signal {
                Signal::Port(port) => IrSignal::Port(self.ports[port].ir),
                Signal::Wire(wire) => {
                    let typed = self.wires[wire].expect_typed(self.refs, &self.wire_interfaces, signal_span)?;
                    IrSignal::Wire(typed.ir)
                }
            };
            Ok(signal_ir)
        })
    }
}
