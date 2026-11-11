use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::{DomainSignal, ValueDomain};
use crate::front::implication::{
    BoolImplications, HardwareValueWithImplications, Implication, ImplicationKind, ValueWithImplications,
};
use crate::front::scope::CaptureFailed;
use crate::front::signal::{Signal, SignalOrVariable};
use crate::front::steps::TargetSteps;
use crate::front::types::{HardwareType, NonHardwareType, Type, Typed};
use crate::front::value::{
    BoundMethod, CompileValue, EnumValue, HardwareInt, HardwareValue, MaybeCompile, MaybeUndefined, MixedCompoundValue,
    MixedString, MixedValue, NotCompile, RangeValue, SimpleCompileValue, StructValue, Value, ValueCommon,
};
use crate::mid::ir::{
    IrAssignmentTarget, IrBlock, IrExpression, IrExpressionLarge, IrLargeArena, IrSignal, IrSignals, IrStatement,
    IrVariable, IrVariableInfo, IrVariables, IrWires,
};
use crate::syntax::ast::{MaybeIdentifier, StringPiece, SyncDomain};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::try_inner;
use crate::util::arena::RandomCheck;
use crate::util::big_int::BigInt;
use crate::util::data::IndexMapExt;
use crate::util::debug::DebugOnly;
use crate::util::intern::{Id, MaybeId};
use crate::util::iter::IterExt;
use crate::util::lattice::{Lattice, LatticeMerge};
use crate::util::range::{Range, RangeEmpty};
use crate::util::range_multi::{ClosedMultiRange, ClosedNonEmptyMultiRange, MultiRange};
use crate::util::{NON_ZERO_USIZE_ONE, Never, ResultExt, ResultNeverExt};
use indexmap::{IndexMap, IndexSet};
use itertools::{Itertools, zip_eq};
use khdl_util::swrite;
use std::cell::Cell;
use std::fmt::Display;
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub enum FlowKind<C, H> {
    Compile(C),
    Hardware(H),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FlowRootId(usize);

#[derive(Debug, Default)]
pub struct NextFlowRootId(AtomicUsize);

#[derive(Debug)]
pub struct FlowRoot<'d> {
    // TODO maybe this should be refs, instead having an extra parameter for a couple of functions
    diags: &'d Diagnostics,

    id: FlowRootId,
    check: RandomCheck,

    next_var_index: Cell<NonZeroUsize>,
    next_version_index: Cell<NonZeroUsize>,
}

#[derive(Debug)]
pub struct FlowRootContent {
    id: FlowRootId,
    check: RandomCheck,

    next_var_index: Cell<NonZeroUsize>,
    next_version: Cell<NonZeroUsize>,
}

pub struct FlowCompile<'p> {
    root: &'p FlowRoot<'p>,

    compile_span: Span,
    compile_reason: &'static str,

    parent: FlowCompileKind<'p>,
    variables: IndexMap<VariableIndex, VariableSlot>,
}

pub enum FlowCompileKind<'p> {
    /// Top level flow, created for each elaborated item.
    Root,
    /// A scoped block within another compile parent.
    /// Cannot modify parent variables.
    IsolatedCompile(&'p FlowCompile<'p>),
    /// A scoped block within another compile parent.
    /// Can modify parent variables,
    ///   but also declare new variables locally which are then dropped at the end of the scope.
    ScopedCompile(&'p mut FlowCompile<'p>),
    /// A compile flow within a hardware parent.
    ///   Can still modify parent variables (by setting them to constant variables),
    ///   and also declare new variables locally which are then dropped at the end of the scope.
    ScopedHardware(&'p mut FlowHardware<'p>),
}

#[derive(Debug)]
pub struct FlowCompileContent {
    check: RandomCheck,

    compile_span: Span,
    compile_reason: &'static str,

    variables: IndexMap<VariableIndex, VariableSlot>,
}

pub struct FlowHardware<'p> {
    root: &'p FlowRoot<'p>,
    enable_domain_checks: bool,
    kind: FlowHardwareKind<'p>,
}

enum FlowHardwareKind<'p> {
    /// Top level hardware flow, created for each process.
    /// Cannot modify parent variables.
    Root(&'p mut FlowHardwareRoot<'p>),
    /// A conditional branch within a hardware flow.
    /// Wires to signals and variables should not propagate to the parent immediately,
    ///   they will be merged when all branches have ended.
    Branch(&'p mut FlowHardwareBranch<'p>),
    /// A scoped block within a hardware parent.
    /// Can modify parent variables,
    ///   and also declare new variables locally which are then dropped at the end of the scope
    Scoped(FlowHardwareScoped<'p>),
}

pub struct FlowHardwareRoot<'p> {
    root: &'p FlowRoot<'p>,
    parent: &'p FlowCompile<'p>,

    #[allow(dead_code)]
    span: Span,
    process_kind: HardwareProcessKind<'p>,

    ir_signals: &'p mut IrSignals,
    ir_variables: IrVariables,

    common: FlowHardwareCommon,
}

pub enum HardwareProcessKind<'e> {
    CombinatorialProcessBody {
        span_keyword: Span,
    },
    ClockedProcessBody {
        span_keyword: Span,
        domain: Spanned<SyncDomain<DomainSignal>>,
        registers: &'e mut IndexMap<Signal, RegisterInfo>,
    },
    WireExpression {
        span_keyword: Span,
        span_init: Span,
    },
    InstancePortConnection {
        span_connection: Span,
    },
}

pub struct RegisterInfo {
    pub span: Span,
    pub ir: IrSignal,
    pub reset: Spanned<MaybeUndefined<IrExpression>>,
}

pub struct FlowHardwareBranch<'p> {
    root: &'p FlowRoot<'p>,
    parent: &'p mut FlowHardware<'p>,

    cond_domain: Spanned<ValueDomain>,
    common: FlowHardwareCommon,
}

pub struct FlowHardwareBranchContent {
    check: RandomCheck,
    // TODO think about how this should be propagated, eg. if two branches break and the third one doesn't,
    //   the value of all merged values and even implications might depend on the condition domain
    cond_domain: Spanned<ValueDomain>,
    common: FlowHardwareCommon,
}

struct FlowHardwareScoped<'p> {
    parent: &'p mut FlowHardware<'p>,
    variables: IndexMap<VariableIndex, VariableSlot>,
}

struct FlowHardwareCommon {
    // TODO document why single map
    variables: IndexMap<VariableIndex, VariableSlotOption>,
    signals: IndexMap<Signal, SignalContent>,
    implied: IndexMap<ValueVersion, Implied>,
    statements: Vec<Spanned<IrStatement>>,
}

#[derive(Debug)]
struct VariableSlot {
    info: VariableInfo,
    content: VariableContent,
}

#[derive(Default)]
struct VariableSlotOption {
    info: Option<VariableInfo>,
    content: Option<VariableContent>,
}

#[derive(Debug, Copy, Clone)]
pub struct ImplicationContradiction;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Variable {
    check: RandomCheck,
    index: VariableIndex,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
struct VariableIndex(NonZeroUsize);

#[derive(Debug)]
pub struct VariableInfo {
    pub span_decl: Span,
    pub id: MaybeId,
    pub mutable: bool,
    pub ty: Option<Spanned<Type>>,

    /// If set, branch joining will always use this IR variable as the result.
    /// This only works if all values are guaranteed to have the exact right type for this variable,
    ///   and nothing else will use this variable at any point.
    pub join_ir_variable: Option<IrVariable>,
}

// TODO remove error branch, this actually doesn't really make sense
#[derive(Debug, Clone)]
enum VariableContent {
    Assigned(Spanned<VariableValue>),
    NotFullyAssigned(VariableNotFullyAssigned),
    Error(DiagError),
}

#[derive(Debug, Copy, Clone)]
enum VariableNotFullyAssigned {
    NotYetAssigned,
    PartiallyAssigned,

    /// Undefined means no value has been assigned yet, but merging should act like there was an assigned value.
    /// This is useful when there is some external mechanism to enforce that by the time the variable is read it will
    /// actually have a value, but Flow does not understand that.
    /// This is used for function return values.
    Undefined,
}

type VariableValue = Value<SimpleCompileValue, MixedCompoundValue<IrVariable>, VariableValueHardware>;

#[derive(Debug, Clone)]
struct VariableValueHardware {
    /// The version of the currently stored value.
    version: ValueVersion,
    /// The stored value. Its type does not have any implications applied yet.
    value_raw: HardwareValue<HardwareType, IrVariable>,
    /// The implications that hold if this value is true/false.
    implications: BoolImplications,
}

pub type VarSetValue =
    Value<SimpleCompileValue, MixedCompoundValue, HardwareValueWithImplications<HardwareType, IrVariable>>;

#[derive(Debug, Clone)]
enum SignalContent {
    Compile(CompileValue),
    Hardware(SignalContentHardware),
}

#[derive(Debug, Clone)]
struct SignalContentHardware {
    /// The version of the currently stored value.
    version: ValueVersion,
    /// The implications that hold if this value is true/false.
    implications: BoolImplications,
}

#[derive(Debug, Clone)]
enum Implied {
    BoolConst(bool),
    IntRange(ClosedNonEmptyMultiRange<BigInt>),
}

/// The version of a value stored in a signal or variable.
///
/// Multiple values with the same version are guaranteed to actually be the same value.
/// These are fully unique within a given flow hierarchy.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ValueVersion {
    id: DebugOnly<FlowRootId>,
    kind: ValueVersionKind,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
enum ValueVersionKind {
    // Dedicated version for initial signal versions, so we don't have to awkwardly pre-define them.
    SignalInitial(Signal),
    Index(NonZeroUsize),
}

trait FlowPrivate: Sized {
    fn root(&self) -> &FlowRoot<'_>;

    fn var_info_option(&self, var: VariableIndex) -> Option<&VariableInfo>;
    fn var_set_content(&mut self, var: Variable, assignment_span: Span, content: VariableContent) -> DiagResult;
    fn var_get_content(&self, var: Spanned<Variable>) -> DiagResult<&VariableContent>;

    // TODO avoid clone?
    fn signal_get_content(&self, signal: Signal) -> SignalContent;

    fn get_implied(&self, version: ValueVersion) -> Option<&Implied>;
}

const VAR_EVAL_HW_REASON: &str = "accessing a hardware variable";

#[allow(private_bounds)]
pub trait Flow: FlowPrivate {
    fn root_id(&self) -> FlowRootId {
        self.root().id
    }

    #[allow(clippy::needless_lifetimes)]
    fn new_child_compile<'s>(&'s mut self, span: Span, reason: &'static str) -> FlowCompile<'s>;

    fn require_hardware(&mut self, span: Span, reason: &str) -> DiagResult<&mut FlowHardware<'_>>;

    fn kind(&self) -> FlowKind<&FlowCompile<'_>, &FlowHardware<'_>>;
    fn kind_mut(&mut self) -> FlowKind<&mut FlowCompile<'_>, &mut FlowHardware<'_>>;

    fn var_new(&mut self, info: VariableInfo) -> Variable;

    fn var_still_exists(&self, var: Variable) -> bool {
        let root = self.root();
        assert_eq!(var.check, root.check);
        assert!(var.index.0 < root.next_var_index.get());
        self.var_info_option(var.index).is_some()
    }

    fn var_info(&self, var: Spanned<Variable>) -> DiagResult<&VariableInfo> {
        assert_eq!(var.inner.check, self.root().check);
        self.var_info_option(var.inner.index).ok_or_else(|| {
            self.root()
                .diags
                .report_error_internal(var.span, "hit root before finding variable info")
        })
    }

    fn var_set(
        &mut self,
        refs: CompileRefs,
        var: Variable,
        assignment_span: Span,
        value: DiagResult<ValueWithImplications>,
    ) -> DiagResult {
        let content = match value {
            Ok(value) => {
                let value = match value {
                    Value::Simple(value) => VariableValue::Simple(value),
                    Value::Compound(value) => {
                        let var_info = self.var_info(Spanned::new(assignment_span, var))?;
                        let mut name = Some(var_info.id.str(&refs.shared.interner).unwrap_or("").to_owned());

                        let result = map_compound_hardware(refs, &value, &mut name, &mut |e, name| {
                            let flow = self.require_hardware(assignment_span, "assigning hardware value")?;
                            let value = flow.store_hardware_value_in_new_ir_variable(
                                refs,
                                assignment_span,
                                name.map(str::to_owned),
                                &e.ty,
                                e.expr.clone(),
                            );
                            Ok(value)
                        })?;
                        VariableValue::Compound(result)
                    }
                    Value::Hardware(value) => {
                        let HardwareValueWithImplications {
                            value,
                            version,
                            implications,
                        } = value;
                        if let Some(version) = version {
                            assert_eq!(version.id, DebugOnly::new(|| self.root_id()));
                        }

                        let var_info = self.var_info(Spanned::new(assignment_span, var))?;
                        let debug_info_id = var_info.id.str(&refs.shared.interner).map(str::to_owned);
                        let flow = self.require_hardware(assignment_span, "assigning hardware value")?;
                        let var_ir = flow.store_hardware_value_in_new_ir_variable(
                            refs,
                            assignment_span,
                            debug_info_id,
                            &value.ty,
                            value.expr,
                        );

                        let version = version.unwrap_or_else(|| self.root().next_version());

                        VariableValue::Hardware(VariableValueHardware {
                            version,
                            value_raw: HardwareValue {
                                ty: value.ty,
                                domain: value.domain,
                                expr: var_ir,
                            },
                            implications,
                        })
                    }
                };

                VariableContent::Assigned(Spanned::new(assignment_span, value))
            }
            Err(e) => VariableContent::Error(e),
        };

        self.var_set_content(var, assignment_span, content)
    }

    /// More specific form of [var_set] if the value is already in an IR variable,
    ///   and transferring the ownership of that variable can be transferred to the flow.
    // TODO maybe just delete this once we IR passes that clean up redundant variables
    fn var_set_to_ir_variable(
        &mut self,
        var: Variable,
        assignment_span: Span,
        value: HardwareValueWithImplications<HardwareType, IrVariable>,
    ) -> DiagResult {
        let HardwareValueWithImplications {
            value,
            version,
            implications,
        } = value;

        // keep or pick version
        let version = version.unwrap_or_else(|| self.root().next_version());

        // wrap value
        let value = VariableValueHardware {
            version,
            value_raw: value,
            implications,
        };
        let content = VariableContent::Assigned(Spanned::new(assignment_span, VariableValue::Hardware(value)));

        self.var_set_content(var, assignment_span, content)
    }

    fn var_set_undefined(&mut self, var: Variable, span: Span) -> DiagResult {
        let content = VariableContent::NotFullyAssigned(VariableNotFullyAssigned::Undefined);
        self.var_set_content(var, span, content)
    }

    /// Evaluate the given variable.
    ///
    /// The [IrVariable] in the hardware case is already a defensive copy, and can be used by the caller freely.
    /// The flow will not modify it later.
    fn var_eval(
        &mut self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        var: Spanned<Variable>,
    ) -> DiagResult<ValueWithImplications> {
        let diags = refs.diags;

        let value = match self.var_get_content(var)? {
            VariableContent::Assigned(value) => match &value.inner {
                Value::Simple(v) => Value::Simple(v.clone()),
                Value::Compound(v) => {
                    let result = map_compound_hardware::<_, _, Never>(refs, v, &mut None, &mut |e, _| {
                        Ok(IrExpression::Variable(e.expr))
                    });
                    Value::Compound(result.remove_never())
                }
                Value::Hardware(v) => {
                    let version = v.version;
                    let implied = self.get_implied(version);

                    v.as_value_without_copy(large, implied)
                }
            },
            VariableContent::NotFullyAssigned(kind) => {
                let var_info = self.var_info(var)?;
                return Err(kind.report_diag(diags, var.span, var_info));
            }
            &VariableContent::Error(e) => return Err(e),
        };

        // check that we're not returning a hardware value in a compile context
        //   (this check also catches compound values with hardware parts)
        match self.kind() {
            FlowKind::Hardware(_) => {}
            FlowKind::Compile(slf) => {
                if CompileValue::try_from(&value).is_err() {
                    return Err(slf.err_not_hardware(var.span, VAR_EVAL_HW_REASON));
                }
            }
        }

        Ok(value)
    }

    /// Get the type of the given value without actually evaluating it.
    /// This does not require that the value can be evaluated in the current flow,
    ///   for example asking the type of a hardware value in a compile-time flow is allowed.
    /// This takes into account any active implications.
    fn type_of(&self, ctx: &mut CompileItemContext, value: Spanned<SignalOrVariable>) -> DiagResult<Type> {
        match value.inner {
            SignalOrVariable::Signal(signal) => match self.signal_get_content(signal) {
                SignalContent::Compile(content) => Ok(content.ty()),
                SignalContent::Hardware(content) => match self.get_implied(content.version) {
                    None => signal
                        .expect_ty(ctx, value.span)
                        .as_ref_ok()
                        .map(|ty| ty.inner.as_type()),
                    Some(implied) => Ok(implied.ty_hw().as_type()),
                },
            },
            SignalOrVariable::Variable(var) => {
                let content = self.var_get_content(Spanned::new(value.span, var))?;

                match content {
                    VariableContent::Assigned(value) => match &value.inner {
                        VariableValue::Simple(value) => Ok(value.ty()),
                        VariableValue::Compound(value) => Ok(value.ty()),
                        VariableValue::Hardware(value) => {
                            let version = value.version;
                            match self.get_implied(version) {
                                None => Ok(value.value_raw.ty.as_type()),
                                Some(implied) => Ok(implied.ty_hw().as_type()),
                            }
                        }
                    },
                    VariableContent::NotFullyAssigned(kind) => {
                        let var_info = self.var_info(Spanned::new(value.span, var))?;
                        Err(kind.report_diag(ctx.refs.diags, value.span, var_info))
                    }
                    &VariableContent::Error(e) => Err(e),
                }
            }
        }
    }

    fn var_new_immutable_init(
        &mut self,
        refs: CompileRefs,
        id: MaybeIdentifier<Spanned<Id>>,
        assign_span: Span,
        value: DiagResult<ValueWithImplications>,
    ) -> DiagResult<Variable> {
        let info = VariableInfo {
            span_decl: id.span(),
            id: id.map_id(|id| id.inner),
            mutable: false,
            ty: None,
            join_ir_variable: None,
        };
        let var = self.var_new(info);
        self.var_set(refs, var, assign_span, value)?;
        Ok(var)
    }

    fn var_new_immutable_init_value(
        &mut self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        id: &str,
        value: Spanned<ValueWithImplications>,
    ) -> DiagResult<Spanned<ValueWithImplications>> {
        let span = value.span;
        let id = MaybeIdentifier::Identifier(Spanned::new(span, refs.shared.interner.push(id)));
        let var = self.var_new_immutable_init(refs, id, span, Ok(value.inner))?;
        let stored = self.var_eval(refs, large, Spanned::new(span, var))?;
        Ok(Spanned::new(span, stored))
    }

    fn var_capture(&self, var: Spanned<Variable>) -> DiagResult<Result<CompileValue, CaptureFailed>> {
        match self.var_get_content(var)? {
            VariableContent::Assigned(value) => match CompileValue::try_from(&value.inner) {
                Ok(v) => Ok(Ok(v)),
                Err(NotCompile) => Ok(Err(CaptureFailed::NotCompile)),
            },
            VariableContent::NotFullyAssigned(_) => Ok(Err(CaptureFailed::NotFullyInitialized)),
            &VariableContent::Error(e) => Err(e),
        }
    }

    fn var_is_not_yet_assigned(&self, var: Spanned<Variable>) -> DiagResult<bool> {
        match self.var_get_content(var)? {
            VariableContent::NotFullyAssigned(kind) => match kind {
                VariableNotFullyAssigned::NotYetAssigned => Ok(true),
                VariableNotFullyAssigned::PartiallyAssigned => Ok(false),
                VariableNotFullyAssigned::Undefined => Ok(true),
            },
            VariableContent::Assigned(_) => Ok(false),
            &VariableContent::Error(e) => Err(e),
        }
    }

    fn signal_eval_if_compile(&mut self, signal: Spanned<Signal>) -> Option<CompileValue> {
        match self.signal_get_content(signal.inner) {
            SignalContent::Compile(value) => Some(value),
            SignalContent::Hardware(_) => None,
        }
    }

    fn signal_eval(
        &mut self,
        ctx: &mut CompileItemContext,
        signal: Spanned<Signal>,
        steps: &TargetSteps,
    ) -> DiagResult<ValueWithImplications> {
        match self.signal_get_content(signal.inner) {
            SignalContent::Compile(value) => {
                // compile-time evaluation can skip any hardware checking
                let value = Spanned::new(signal.span, ValueWithImplications::from(value.clone()));
                steps.apply_to_value(ctx, &Type::Any, value)
            }
            SignalContent::Hardware(content) => {
                let SignalContentHardware { version, implications } = content;

                // get implied info, immediately return if compile-time
                let implied = self.get_implied(version);
                let implied_int_range = match implied {
                    None => None,
                    Some(implied) => match implied {
                        &Implied::BoolConst(value) => {
                            let value = Spanned::new(signal.span, Value::new_bool(value));
                            return steps.apply_to_value(ctx, &Type::Any, value);
                        }
                        Implied::IntRange(range) => Some(range),
                    },
                };

                // check that we're in a hardware flow
                let slf = match self.kind() {
                    FlowKind::Hardware(slf) => slf,
                    FlowKind::Compile(slf) => {
                        return Err(slf.err_not_hardware(signal.span, "signal evaluation"));
                    }
                };

                // evaluate without copy
                let value_full_raw_without_copy = signal.inner.as_hardware_value(ctx, signal.span)?;

                // check that we can access the domain in the current block
                // TODO this probably disables too many things, eg. nested blocks
                if slf.enable_domain_checks {
                    match &slf.root_hw().process_kind {
                        &HardwareProcessKind::ClockedProcessBody { domain, .. } => {
                            ctx.check_valid_domain_crossing(
                                signal.span,
                                Spanned::new(signal.span, value_full_raw_without_copy.domain()),
                                domain.map_inner(ValueDomain::Sync),
                                "signal read in clocked block",
                            )?;
                        }
                        HardwareProcessKind::CombinatorialProcessBody { .. }
                        | HardwareProcessKind::WireExpression { .. }
                        | HardwareProcessKind::InstancePortConnection { .. } => {}
                    }
                }

                // constrain
                let value_full_without_copy = match implied_int_range {
                    None => value_full_raw_without_copy,
                    Some(range) => HardwareValue {
                        ty: HardwareType::Int(range.clone()),
                        domain: value_full_raw_without_copy.domain,
                        expr: ctx.large.push_expr(IrExpressionLarge::ConstrainIntRange(
                            range.enclosing().cloned(),
                            value_full_raw_without_copy.expr,
                        )),
                    },
                };

                // apply steps
                let value_without_copy = {
                    let base = HardwareValueWithImplications {
                        value: value_full_without_copy,
                        version: Some(version),
                        implications,
                    };
                    let base = Spanned::new(signal.span, ValueWithImplications::Hardware(base));
                    let result = steps.apply_to_value(ctx, &Type::Any, base)?;
                    match result {
                        ValueWithImplications::Simple(value) => {
                            // we got a compile-time value, just return it
                            return Ok(Value::Simple(value));
                        }
                        ValueWithImplications::Compound(x) => {
                            // we don't need to take a copy, this value is already not a raw signal
                            return Ok(Value::Compound(x));
                        }
                        ValueWithImplications::Hardware(value_without_copy) => {
                            // we might not always need a copy (in case this is an already shadowed value),
                            //   but it doesn't hurt either
                            value_without_copy
                        }
                    }
                };

                // copy the value into a temporary variable to avoid later writes from leaking through
                let slf = match self.kind_mut() {
                    FlowKind::Compile(_) => unreachable!("already checked this earlier"),
                    FlowKind::Hardware(slf) => slf,
                };

                let debug_info_id = signal.inner.diagnostic_string(ctx).to_owned();
                let value_var = slf.store_hardware_value_in_new_ir_variable(
                    ctx.refs,
                    signal.span,
                    Some(debug_info_id),
                    &value_without_copy.value.ty,
                    value_without_copy.value.expr,
                );

                // add self-implications
                let mut implications = value_without_copy.implications;
                if value_without_copy.value.ty == HardwareType::Bool
                    && let Some(version) = value_without_copy.version
                {
                    implications.add_bool_self_implications(version);
                }

                // wrap result
                let value = HardwareValueWithImplications {
                    value: HardwareValue {
                        ty: value_without_copy.value.ty,
                        domain: value_without_copy.value.domain,
                        expr: IrExpression::Variable(value_var),
                    },
                    version: value_without_copy.version,
                    implications,
                };
                Ok(Value::Hardware(value))
            }
        }
    }

    fn signal_or_var_eval(
        &mut self,
        ctx: &mut CompileItemContext,
        base: Spanned<SignalOrVariable>,
        steps: &TargetSteps,
    ) -> DiagResult<ValueWithImplications> {
        match base.inner {
            SignalOrVariable::Signal(signal) => self.signal_eval(ctx, Spanned::new(base.span, signal), steps),
            SignalOrVariable::Variable(var) => {
                let left_base_value = self.var_eval(ctx.refs, &mut ctx.large, Spanned::new(base.span, var))?;
                steps.apply_to_value(ctx, &Type::Any, Spanned::new(base.span, left_base_value))
            }
        }
    }
}

impl<'d> FlowRoot<'d> {
    pub fn new(diags: &'d Diagnostics, next: &NextFlowRootId) -> FlowRoot<'d> {
        FlowRoot {
            diags,
            id: FlowRootId(next.0.fetch_add(1, Ordering::Relaxed)),
            check: RandomCheck::new(),
            next_var_index: Cell::new(NON_ZERO_USIZE_ONE),
            next_version_index: Cell::new(NON_ZERO_USIZE_ONE),
        }
    }

    pub fn into_content(self) -> FlowRootContent {
        FlowRootContent {
            id: self.id,
            check: self.check,
            next_var_index: self.next_var_index,
            next_version: self.next_version_index,
        }
    }

    pub fn restore(diags: &Diagnostics, content: FlowRootContent) -> FlowRoot<'_> {
        FlowRoot {
            diags,
            id: content.id,
            check: content.check,
            next_var_index: content.next_var_index,
            next_version_index: content.next_version,
        }
    }

    fn next_variable(&self) -> Variable {
        let index = self.next_var_index.get();
        self.next_var_index.set(index.checked_add(1).expect("overflow"));
        Variable {
            check: self.check,
            index: VariableIndex(index),
        }
    }

    fn next_version(&self) -> ValueVersion {
        let index = self.next_version_index.get();
        self.next_version_index.set(index.checked_add(1).expect("overflow"));
        ValueVersion {
            id: DebugOnly::new(|| self.id),
            kind: ValueVersionKind::Index(index),
        }
    }

    fn initial_signal_version(&self, signal: Signal) -> ValueVersion {
        ValueVersion {
            id: DebugOnly::new(|| self.id),
            kind: ValueVersionKind::SignalInitial(signal),
        }
    }

    fn initial_signal_content(&self, signal: Signal) -> SignalContent {
        SignalContent::Hardware(SignalContentHardware {
            version: self.initial_signal_version(signal),
            implications: BoolImplications::NONE,
        })
    }
}

impl FlowPrivate for FlowCompile<'_> {
    fn root(&self) -> &FlowRoot<'_> {
        self.root
    }

    fn var_info_option(&self, var: VariableIndex) -> Option<&VariableInfo> {
        let mut curr = self;
        loop {
            if let Some(slot) = curr.variables.get(&var) {
                return Some(&slot.info);
            }
            curr = match &curr.parent {
                FlowCompileKind::Root => return None,
                FlowCompileKind::IsolatedCompile(parent) => parent,
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => return parent.var_info_option(var),
            }
        }
    }

    fn var_set_content(&mut self, var: Variable, assignment_span: Span, content: VariableContent) -> DiagResult {
        // checks
        assert_eq!(self.root.check, var.check);
        let diags = self.root.diags;

        // TODO maybe only store unwrapped compile values in compile flows?
        let value = if let VariableContent::Assigned(assigned) = &content
            && CompileValue::try_from(&assigned.inner).is_err()
        {
            let e = diags.report_error_internal(
                assignment_span,
                "cannot assign hardware value to variable in compile context",
            );
            VariableContent::Error(e)
        } else {
            content
        };

        // find which slot to store the value in
        let mut curr = self;
        let slot = loop {
            if let Some(slot) = curr.variables.get_mut(&var.index) {
                break slot;
            }
            curr = match &mut curr.parent {
                FlowCompileKind::Root => {
                    let e = diags.report_error_internal(assignment_span, "hit root before finding variable slot");
                    return Err(e);
                }
                FlowCompileKind::IsolatedCompile(_) => {
                    let e = diags
                        .report_error_internal(assignment_span, "hit isolated parent before finding variable slot");
                    return Err(e);
                }
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => {
                    return parent.var_set_content(var, assignment_span, value);
                }
            }
        };

        slot.content = value;
        Ok(())
    }

    fn var_get_content(&self, var: Spanned<Variable>) -> DiagResult<&VariableContent> {
        assert_eq!(self.root.check, var.inner.check);
        let diags = self.root.diags;

        let mut curr = self;
        loop {
            if let Some(entry) = curr.variables.get(&var.inner.index) {
                return Ok(&entry.content);
            }
            curr = match &curr.parent {
                FlowCompileKind::Root => {
                    let e = diags.report_error_internal(var.span, "hit root before finding variable slot");
                    return Ok(VariableContent::err_ref(e));
                }
                FlowCompileKind::IsolatedCompile(parent) => parent,
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => {
                    return parent.var_get_content(var);
                }
            }
        }
    }

    fn signal_get_content(&self, signal: Signal) -> SignalContent {
        let mut curr = self;
        loop {
            curr = match &curr.parent {
                FlowCompileKind::Root => {
                    break curr.root.initial_signal_content(signal);
                }
                FlowCompileKind::IsolatedCompile(parent) => parent,
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => break parent.signal_get_content(signal),
            }
        }
    }

    fn get_implied(&self, version: ValueVersion) -> Option<&Implied> {
        let mut curr = self;
        loop {
            curr = match &curr.parent {
                FlowCompileKind::Root => return None,
                FlowCompileKind::IsolatedCompile(parent) => parent,
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => {
                    return parent.get_implied(version);
                }
            }
        }
    }
}

impl Flow for FlowCompile<'_> {
    fn new_child_compile(&mut self, span: Span, reason: &'static str) -> FlowCompile<'_> {
        let root = self.root;
        let slf = unsafe { lifetime_cast::compile_mut(self) };
        FlowCompile {
            root,
            compile_span: span,
            compile_reason: reason,
            parent: FlowCompileKind::ScopedCompile(slf),
            variables: IndexMap::new(),
        }
    }

    fn require_hardware(&mut self, span: Span, reason: &str) -> DiagResult<&mut FlowHardware<'_>> {
        Err(self.err_not_hardware(span, reason))
    }

    fn kind(&self) -> FlowKind<&FlowCompile<'_>, &FlowHardware<'_>> {
        FlowKind::Compile(unsafe { lifetime_cast::compile_ref(self) })
    }

    fn kind_mut(&mut self) -> FlowKind<&mut FlowCompile<'_>, &mut FlowHardware<'_>> {
        FlowKind::Compile(unsafe { lifetime_cast::compile_mut(self) })
    }

    fn var_new(&mut self, info: VariableInfo) -> Variable {
        let var = self.root.next_variable();

        let slot = VariableSlot {
            info,
            content: VariableContent::NotFullyAssigned(VariableNotFullyAssigned::NotYetAssigned),
        };
        self.variables.insert_first(var.index, slot);

        var
    }

    fn signal_eval(
        &mut self,
        ctx: &mut CompileItemContext,
        signal: Spanned<Signal>,
        steps: &TargetSteps,
    ) -> DiagResult<ValueWithImplications> {
        // This is a compile-time flow, so normally signals can't be evaluated.
        // They might have an implied compile-time value through, so check that first.

        // walk up until we hit a hardware parent
        let mut curr = &*self;
        let parent_hw = loop {
            curr = match &curr.parent {
                FlowCompileKind::Root => break None,
                FlowCompileKind::IsolatedCompile(parent) => parent,
                FlowCompileKind::ScopedCompile(parent) => parent,
                FlowCompileKind::ScopedHardware(parent) => break Some(parent),
            }
        };

        // walk up through the chain of hardware parents
        let mut curr = parent_hw;
        loop {
            curr = match curr {
                None => break,
                Some(curr) => {
                    let (common, parent) = match &curr.kind {
                        FlowHardwareKind::Root(curr) => (Some(&curr.common), None),
                        FlowHardwareKind::Branch(curr) => (Some(&curr.common), Some(&curr.parent)),
                        FlowHardwareKind::Scoped(curr) => (None, Some(&curr.parent)),
                    };

                    // check if this hardware flow has some information about the signal
                    if let Some(common) = common {
                        if let Some(signal_content) = common.signals.get(&signal.inner) {
                            match signal_content {
                                SignalContent::Compile(value) => {
                                    // we've found a compile-time value, we can return that
                                    let value = Spanned::new(signal.span, ValueWithImplications::from(value.clone()));
                                    let result = steps.apply_to_value(ctx, &Type::Any, value)?;
                                    return Ok(result);
                                }
                                SignalContent::Hardware(_) => {
                                    // we've found proof that the signal is hardware, so we need to stop
                                    // (this is important to allow children to override the parent)
                                    break;
                                }
                            }
                        }
                    }

                    parent
                }
            };
        }

        // otherwise
        Err(self.err_not_hardware(signal.span, "signal evaluation"))
    }
}

impl<'p> FlowCompile<'p> {
    pub fn new_root(root: &'p FlowRoot, span: Span, reason: &'static str) -> FlowCompile<'p> {
        FlowCompile {
            root,
            compile_span: span,
            compile_reason: reason,
            parent: FlowCompileKind::Root,
            variables: IndexMap::new(),
        }
    }

    // TODO think about a better name
    pub fn new_child_isolated(&self) -> FlowCompile<'_> {
        let slf = unsafe { lifetime_cast::compile_ref(self) };
        FlowCompile {
            root: self.root,
            compile_span: self.compile_span,
            compile_reason: self.compile_reason,
            parent: FlowCompileKind::IsolatedCompile(slf),
            variables: IndexMap::default(),
        }
    }

    pub fn new_child_scoped(&mut self) -> FlowCompile<'_> {
        let root = self.root;
        let compile_span = self.compile_span;
        let compile_reason = self.compile_reason;
        let slf = unsafe { lifetime_cast::compile_mut(self) };
        FlowCompile {
            root,
            compile_span,
            compile_reason,
            parent: FlowCompileKind::ScopedCompile(slf),
            variables: IndexMap::default(),
        }
    }

    pub fn into_content(self) -> FlowCompileContent {
        let FlowCompile {
            root,
            compile_span,
            compile_reason,
            parent: _,
            variables: variable_slots,
        } = self;
        FlowCompileContent {
            check: root.check,
            compile_span,
            compile_reason,
            variables: variable_slots,
        }
    }

    pub fn restore_root(root: &'p FlowRoot, content: FlowCompileContent) -> FlowCompile<'p> {
        let FlowCompileContent {
            check,
            compile_span,
            compile_reason,
            variables: variable_slots,
        } = content;
        assert_eq!(check, root.check);

        FlowCompile {
            root,
            compile_span,
            compile_reason,
            parent: FlowCompileKind::Root,
            variables: variable_slots,
        }
    }

    pub fn restore_child_isolated<'s>(parent: &'s FlowCompile, content: FlowCompileContent) -> FlowCompile<'s> {
        let FlowCompileContent {
            check,
            compile_span,
            compile_reason,
            variables: variable_slots,
        } = content;
        assert_eq!(parent.root.check, check);

        let parent = unsafe { lifetime_cast::compile_ref(parent) };
        FlowCompile {
            root: parent.root,
            compile_span,
            compile_reason,
            parent: FlowCompileKind::IsolatedCompile(parent),
            variables: variable_slots,
        }
    }

    fn err_not_hardware(&self, span: Span, reason: &str) -> DiagError {
        DiagnosticError::new(
            format!("{reason} is only allowed in a hardware context"),
            span,
            format!("{reason} here"),
        )
        .add_info(
            self.compile_span,
            format!("context is compile-time because of this {}", self.compile_reason),
        )
        .report(self.root.diags)
    }
}

impl<'p> FlowHardware<'p> {
    fn root_hw<'s>(&'s self) -> &'s FlowHardwareRoot<'p> {
        let mut curr = self;
        loop {
            curr = match &curr.kind {
                FlowHardwareKind::Root(root) => return root,
                FlowHardwareKind::Branch(branch) => branch.parent,
                FlowHardwareKind::Scoped(scoped) => scoped.parent,
            }
        }
    }

    fn root_hw_mut<'s>(&'s mut self) -> &'s mut FlowHardwareRoot<'p> {
        let mut curr = self;
        loop {
            curr = match &mut curr.kind {
                FlowHardwareKind::Root(root) => return root,
                FlowHardwareKind::Branch(branch) => branch.parent,
                FlowHardwareKind::Scoped(scoped) => scoped.parent,
            }
        }
    }

    pub fn new_child_branch(
        &mut self,
        span: Span,
        cond_domain: Spanned<ValueDomain>,
        cond_implications: Vec<Implication>,
    ) -> DiagResult<Result<FlowHardwareBranch<'_>, ImplicationContradiction>> {
        // build new flow
        let root = self.root;
        let slf = unsafe { lifetime_cast::hardware_mut(self) };

        let mut result = FlowHardwareBranch {
            root,
            parent: slf,
            cond_domain,
            common: FlowHardwareCommon::new(),
        };

        // apply implications
        let mut result_hw = result.as_flow();
        for implication in cond_implications {
            try_inner!(result_hw.add_implication(span, implication)?);
        }

        Ok(Ok(result))
    }

    pub fn add_implication(
        &mut self,
        span: Span,
        implication: Implication,
    ) -> DiagResult<Result<(), ImplicationContradiction>> {
        let diags = self.root.diags;

        let Implication {
            version,
            kind: impl_kind,
        } = implication;

        // combine new implication with previous implication if any
        let prev_implied = self.get_implied(version);
        let new_implied = match impl_kind {
            ImplicationKind::BoolEq(impl_value) => match prev_implied {
                None => Some(Implied::BoolConst(impl_value)),
                Some(prev_implied) => match prev_implied {
                    &Implied::BoolConst(prev_value) => {
                        if prev_value == impl_value {
                            None
                        } else {
                            return Ok(Err(ImplicationContradiction));
                        }
                    }
                    Implied::IntRange(_) => {
                        return Err(diags.report_error_internal(span, "combining bool and int implication"));
                    }
                },
            },
            ImplicationKind::IntIn(impl_range) => {
                let new_range = match prev_implied {
                    None => impl_range,
                    Some(prev_implied) => match prev_implied {
                        Implied::BoolConst(_) => {
                            return Err(diags.report_error_internal(span, "combining bool and int implication"));
                        }
                        Implied::IntRange(prev_range) => {
                            ClosedMultiRange::from(prev_range.clone()).intersect(&MultiRange::from(impl_range))
                        }
                    },
                };
                let new_range = match ClosedNonEmptyMultiRange::try_from(new_range) {
                    Ok(new_range) => new_range,
                    Err(RangeEmpty) => return Ok(Err(ImplicationContradiction)),
                };

                Some(Implied::IntRange(new_range))
            }
        };

        // set new implication
        if let Some(new_implied) = new_implied {
            self.first_common_mut().implied.insert(version, new_implied);
        }

        Ok(Ok(()))
    }

    pub fn new_child_scoped(&mut self) -> FlowHardware<'_> {
        let root = self.root;
        let slf = unsafe { lifetime_cast::hardware_mut(self) };
        FlowHardware {
            root,
            enable_domain_checks: true,
            kind: FlowHardwareKind::Scoped(FlowHardwareScoped {
                parent: slf,
                variables: IndexMap::new(),
            }),
        }
    }

    pub fn new_child_scoped_without_domain_checks(&mut self) -> FlowHardware<'_> {
        let mut result = self.new_child_scoped();
        result.enable_domain_checks = false;
        result
    }

    pub fn join_child_branches_pair(
        &mut self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span_merge: Span,
        branches: (FlowHardwareBranchContent, FlowHardwareBranchContent),
    ) -> DiagResult<(IrBlock, IrBlock)> {
        let (branch_0, branch_1) = branches;
        let branches = vec![branch_0, branch_1];

        let result = self.join_child_branches(refs, large, span_merge, branches)?;

        assert_eq!(result.len(), 2);
        let mut result = result.into_iter();
        let block_0 = result.next().unwrap();
        let block_1 = result.next().unwrap();
        Ok((block_0, block_1))
    }

    pub fn join_child_branches(
        &mut self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span_merge: Span,
        mut branches: Vec<FlowHardwareBranchContent>,
    ) -> DiagResult<Vec<IrBlock>> {
        // TODO do something else if children are empty, eg. push an instruction for `assert(false)`
        //    or maybe even compile-time error?

        // collect the interesting vars and signals
        // things we can skip:
        //   * items that are not in any child, they didn't change
        //   * items that don't exist in the parent, they won't be alive afterwards
        let mut merged_vars = IndexSet::new();
        let mut merged_signals = IndexSet::new();
        for branch in &branches {
            assert_eq!(self.root.check, branch.check);
            for &var in branch.common.variables.keys() {
                if self.var_info_option(var).is_some() {
                    merged_vars.insert(var);
                }
            }
            for &signal in branch.common.signals.keys() {
                merged_signals.insert(signal);
            }
        }

        // merge variables
        for var in merged_vars {
            let var = Variable {
                check: self.root.check,
                index: var,
            };

            let (merged_content, merged_implied) =
                merge_branch_variable(refs, large, self, span_merge, var, &mut branches)?;

            self.var_set_content(var, span_merge, merged_content)?;
            if let Some((version, implied)) = merged_implied {
                self.first_common_mut().implied.insert(version, implied);
            }
        }

        // merge signals
        for signal in merged_signals {
            let (merged_content, merged_implied) = merge_branch_signal(self, signal, &mut branches)?;

            self.signal_set_content(signal, merged_content);
            if let Some((version, implied)) = merged_implied {
                self.first_common_mut().implied.insert(version, implied);
            }
        }

        // extract blocks
        let branch_blocks = branches
            .into_iter()
            .map(|branch| {
                let FlowHardwareBranchContent {
                    check: _,
                    cond_domain: _,
                    common,
                } = branch;
                let FlowHardwareCommon {
                    variables: _,
                    signals: _,
                    implied: _,
                    statements,
                } = common;
                IrBlock { statements }
            })
            .collect_vec();

        // TODO merge condition domains too?
        // TODO merge implied too?

        Ok(branch_blocks)
    }

    pub fn get_ir_variables(&self) -> &IrVariables {
        &self.root_hw().ir_variables
    }

    pub fn get_ir_signals(&self) -> &IrSignals {
        self.root_hw().ir_signals
    }

    pub fn get_ir_wires_mut(&mut self) -> &mut IrWires {
        &mut self.root_hw_mut().ir_signals.wires
    }

    fn first_common_mut(&mut self) -> &mut FlowHardwareCommon {
        let mut curr = self;
        loop {
            curr = match &mut curr.kind {
                FlowHardwareKind::Root(root) => return &mut root.common,
                FlowHardwareKind::Branch(branch) => return &mut branch.common,
                FlowHardwareKind::Scoped(scoped) => scoped.parent,
            }
        }
    }

    pub fn push_ir_statement(&mut self, statement: Spanned<IrStatement>) {
        self.first_common_mut().statements.push(statement);
    }

    pub fn new_ir_variable(&mut self, info: IrVariableInfo) -> IrVariable {
        self.root_hw_mut().ir_variables.push(info)
    }

    pub fn process_kind(&mut self) -> &mut HardwareProcessKind<'p> {
        &mut self.root_hw_mut().process_kind
    }

    pub fn condition_domains(&self) -> impl Iterator<Item = Spanned<ValueDomain>> + use<'_, 'p> {
        std::iter::successors(Some(self), |curr| match &curr.kind {
            FlowHardwareKind::Root(_) => None,
            FlowHardwareKind::Branch(branch) => Some(branch.parent),
            FlowHardwareKind::Scoped(scoped) => Some(scoped.parent),
        })
        .filter_map(|curr| match &curr.kind {
            FlowHardwareKind::Root(_) => None,
            FlowHardwareKind::Scoped(_) => None,
            FlowHardwareKind::Branch(branch) => Some(branch.cond_domain),
        })
    }

    fn signal_set_content(&mut self, signal: Signal, content: SignalContent) {
        self.first_common_mut().signals.insert(signal, content);
    }

    /// Report that `signal` has been assigned a new value.
    ///
    /// The caller is still responsible for actually emitting the assignment IR,
    /// this function just handles version and implication tracking.
    ///
    /// `value` contains the new value of the entire signal if known, can be `None` if unknown.
    pub fn signal_report_assignment(&mut self, signal: Spanned<Signal>, value: Option<ValueWithImplications>) {
        // TODO track partial drivers to avoid clashes and to generate extra concat blocks
        // TODO comb blocks: check that all written signals are _always_ written
        // TODO ban signal assignments in wire expressions and port connections

        let mut hardware_content = |implied, implications| {
            let version = self.root.next_version();

            if let Some(implied) = implied {
                self.first_common_mut().implied.insert(version, implied);
            }

            SignalContent::Hardware(SignalContentHardware { version, implications })
        };

        let content = match value {
            Some(value) => match CompileValue::try_from(&value) {
                Ok(value) => SignalContent::Compile(value),
                Err(NotCompile) => match value {
                    ValueWithImplications::Simple(_) | ValueWithImplications::Compound(_) => {
                        hardware_content(None, BoolImplications::NONE)
                    }
                    ValueWithImplications::Hardware(value) => {
                        let HardwareValueWithImplications {
                            value,
                            version: _,
                            implications,
                        } = value;

                        let implied = if let HardwareType::Int(implied_int_range) = value.ty {
                            Some(Implied::IntRange(implied_int_range))
                        } else {
                            None
                        };

                        hardware_content(implied, implications)
                    }
                },
            },
            None => hardware_content(None, BoolImplications::NONE),
        };
        self.signal_set_content(signal.inner, content);
    }

    pub fn store_hardware_value_in_new_ir_variable(
        &mut self,
        refs: CompileRefs,
        span: Span,
        debug_info_id: Option<String>,
        ty: &HardwareType,
        expr: IrExpression,
    ) -> IrVariable {
        let var_ir_info = IrVariableInfo {
            ty: ty.as_ir(refs),
            debug_info_span: span,
            debug_info_id,
        };

        let var_ir = self.new_ir_variable(var_ir_info);

        let target = IrAssignmentTarget::simple(var_ir);
        let stmt_store = IrStatement::Assign(target, expr);
        self.push_ir_statement(Spanned::new(span, stmt_store));

        var_ir
    }
}

impl FlowPrivate for FlowHardware<'_> {
    fn root(&self) -> &FlowRoot<'_> {
        self.root
    }

    fn var_info_option(&self, var: VariableIndex) -> Option<&VariableInfo> {
        let mut curr = self;
        loop {
            curr = match &curr.kind {
                FlowHardwareKind::Root(root) => {
                    if let Some(slot) = root.common.variables.get(&var) {
                        if let Some(info) = &slot.info {
                            return Some(info);
                        }
                    }
                    return root.parent.var_info_option(var);
                }
                FlowHardwareKind::Branch(branch) => {
                    if let Some(slot) = branch.common.variables.get(&var) {
                        if let Some(info) = &slot.info {
                            return Some(info);
                        }
                    }
                    branch.parent
                }
                FlowHardwareKind::Scoped(scoped) => {
                    if let Some(slot) = scoped.variables.get(&var) {
                        return Some(&slot.info);
                    }
                    scoped.parent
                }
            };
        }
    }

    fn var_set_content(&mut self, var: Variable, _: Span, content: VariableContent) -> DiagResult {
        assert_eq!(self.root.check, var.check);

        // find the right flow to declare this variable in
        let mut curr = self;
        let variables = loop {
            curr = match &mut curr.kind {
                FlowHardwareKind::Root(root) => break &mut root.common.variables,
                FlowHardwareKind::Branch(branch) => break &mut branch.common.variables,
                FlowHardwareKind::Scoped(scoped) => {
                    // if the value was declared in this scope we can store it here,
                    //   otherwise fallthrough to the parent
                    if let Some(entry) = scoped.variables.get_mut(&var.index) {
                        entry.content = content;
                        return Ok(());
                    }

                    scoped.parent
                }
            }
        };

        variables.entry(var.index).or_default().content = Some(content);
        Ok(())
    }

    fn var_get_content(&self, var: Spanned<Variable>) -> DiagResult<&VariableContent> {
        assert_eq!(self.root.check, var.inner.check);

        let mut curr = self;
        loop {
            curr = match &curr.kind {
                FlowHardwareKind::Root(root) => {
                    if let Some(slot) = root.common.variables.get(&var.inner.index) {
                        if let Some(content) = &slot.content {
                            return Ok(content);
                        }
                    }
                    return root.parent.var_get_content(var);
                }
                FlowHardwareKind::Branch(branch) => {
                    if let Some(slot) = branch.common.variables.get(&var.inner.index) {
                        if let Some(content) = &slot.content {
                            return Ok(content);
                        }
                    }
                    branch.parent
                }
                FlowHardwareKind::Scoped(scoped) => {
                    if let Some(slot) = scoped.variables.get(&var.inner.index) {
                        return Ok(&slot.content);
                    }
                    scoped.parent
                }
            };
        }
    }

    fn signal_get_content(&self, signal: Signal) -> SignalContent {
        let mut curr = self;
        loop {
            curr = match &curr.kind {
                FlowHardwareKind::Root(root) => {
                    let content = root
                        .common
                        .signals
                        .get(&signal)
                        .cloned()
                        .unwrap_or_else(|| self.root.initial_signal_content(signal));
                    return content;
                }
                FlowHardwareKind::Branch(branch) => {
                    if let Some(content) = branch.common.signals.get(&signal) {
                        return content.clone();
                    }
                    branch.parent
                }
                FlowHardwareKind::Scoped(scoped) => scoped.parent,
            };
        }
    }

    fn get_implied(&self, version: ValueVersion) -> Option<&Implied> {
        let mut curr = self;
        loop {
            curr = match &curr.kind {
                FlowHardwareKind::Root(root) => {
                    if let Some(implied) = root.common.implied.get(&version) {
                        return Some(implied);
                    }
                    return None;
                }
                FlowHardwareKind::Branch(branch) => {
                    if let Some(implied) = branch.common.implied.get(&version) {
                        return Some(implied);
                    }
                    branch.parent
                }
                FlowHardwareKind::Scoped(scoped) => scoped.parent,
            };
        }
    }
}

impl Flow for FlowHardware<'_> {
    fn new_child_compile(&mut self, span: Span, reason: &'static str) -> FlowCompile<'_> {
        let root = self.root;
        let slf = unsafe { lifetime_cast::hardware_mut(self) };
        FlowCompile {
            root,
            compile_span: span,
            compile_reason: reason,
            parent: FlowCompileKind::ScopedHardware(slf),
            variables: IndexMap::new(),
        }
    }

    fn require_hardware(&mut self, _: Span, _: &str) -> DiagResult<&mut FlowHardware<'_>> {
        let slf = unsafe { lifetime_cast::hardware_mut(self) };
        Ok(slf)
    }

    fn kind(&self) -> FlowKind<&FlowCompile<'_>, &FlowHardware<'_>> {
        FlowKind::Hardware(unsafe { lifetime_cast::hardware_ref(self) })
    }

    fn kind_mut(&mut self) -> FlowKind<&mut FlowCompile<'_>, &mut FlowHardware<'_>> {
        FlowKind::Hardware(unsafe { lifetime_cast::hardware_mut(self) })
    }

    fn var_new(&mut self, info: VariableInfo) -> Variable {
        let var = self.root.next_variable();
        let content = VariableContent::NotFullyAssigned(VariableNotFullyAssigned::NotYetAssigned);

        match &mut self.kind {
            FlowHardwareKind::Root(root) => {
                let slot = VariableSlotOption {
                    info: Some(info),
                    content: Some(content),
                };
                root.common.variables.insert(var.index, slot);
            }
            FlowHardwareKind::Branch(branch) => {
                let slot = VariableSlotOption {
                    info: Some(info),
                    content: Some(content),
                };
                branch.common.variables.insert(var.index, slot);
            }
            FlowHardwareKind::Scoped(scoped) => {
                let slot = VariableSlot { info, content };
                scoped.variables.insert(var.index, slot);
            }
        }

        var
    }
}

impl<'p> FlowHardwareRoot<'p> {
    pub fn new(
        parent: &'p FlowCompile,
        span: Span,
        kind: HardwareProcessKind<'p>,
        ir_signals: &'p mut IrSignals,
    ) -> FlowHardwareRoot<'p> {
        let parent = unsafe { lifetime_cast::compile_ref(parent) };
        FlowHardwareRoot {
            root: parent.root,
            parent,
            span,
            process_kind: kind,
            ir_signals,
            ir_variables: IrVariables::new(),
            common: FlowHardwareCommon::new(),
        }
    }

    pub fn as_flow(&mut self) -> FlowHardware<'_> {
        let slf = unsafe { lifetime_cast::hardware_root_mut(self) };
        FlowHardware {
            root: slf.root,
            enable_domain_checks: true,
            kind: FlowHardwareKind::Root(slf),
        }
    }

    pub fn finish(self) -> (IrVariables, IrBlock) {
        // TODO for combinatorial blocks, check that signals are _fully_ driven
        let FlowHardwareRoot {
            root: _,
            parent: _,
            span: _,
            process_kind: _,
            ir_signals: _,
            ir_variables,
            common,
        } = self;
        let FlowHardwareCommon {
            variables: _,
            signals: _,
            implied: _,
            statements,
        } = common;

        let block = IrBlock { statements };
        (ir_variables, block)
    }
}

impl FlowHardwareBranch<'_> {
    pub fn as_flow(&mut self) -> FlowHardware<'_> {
        let root = self.root;
        let slf = unsafe { lifetime_cast::hardware_branch_mut(self) };
        FlowHardware {
            root,
            enable_domain_checks: true,
            kind: FlowHardwareKind::Branch(slf),
        }
    }

    pub fn finish(self) -> FlowHardwareBranchContent {
        let FlowHardwareBranch {
            root,
            parent: _,
            cond_domain,
            common,
        } = self;
        FlowHardwareBranchContent {
            check: root.check,
            cond_domain,
            common,
        }
    }
}

fn merge_branch_variable(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    parent_flow: &mut FlowHardware,
    span_merge: Span,
    var: Variable,
    branches: &mut [FlowHardwareBranchContent],
) -> DiagResult<(VariableContent, Option<(ValueVersion, Implied)>)> {
    let diags = refs.diags;
    let elab = &refs.shared.elaboration_arenas;

    let var_spanned = Spanned::new(span_merge, var);
    let var_info = parent_flow.var_info(var_spanned)?;
    let parent_content = parent_flow.var_get_content(var_spanned)?;

    // visit all branch values to check if we need to do a hardware merge
    let mut used_parent_value = false;
    let mut any_defined_branch = false;
    let mut merged_compile: Lattice<CompileValue> = Lattice::Undefined;
    let mut merged_version: Lattice<ValueVersion> = Lattice::Undefined;
    let mut merged_implications: Lattice<BoolImplications> = Lattice::Undefined;
    let mut merged_implied: Lattice<Implied> = Lattice::Undefined;

    for branch in &mut *branches {
        let branch_content = match branch.common.variables.get(&var.index) {
            Some(branch_slot) => {
                // we can assert/unwrap here:
                // * we know merged variables must exist in the parent, so they cannot be declared in branches
                // * slots cannot be fully empty, so if there's no info there must be content
                assert!(branch_slot.info.is_none());
                branch_slot.content.as_ref().unwrap()
            }
            None => {
                used_parent_value = true;
                parent_content
            }
        };

        let value = match branch_content {
            VariableContent::Assigned(value) => value,
            VariableContent::NotFullyAssigned(kind) => match kind {
                VariableNotFullyAssigned::NotYetAssigned | VariableNotFullyAssigned::PartiallyAssigned => {
                    let content = VariableContent::NotFullyAssigned(VariableNotFullyAssigned::PartiallyAssigned);
                    return Ok((content, None));
                }
                VariableNotFullyAssigned::Undefined => continue,
            },
            &VariableContent::Error(e) => return Err(e),
        };
        any_defined_branch = true;

        let branch_compile = CompileValue::try_from(&value.inner)
            .map(Lattice::Defined)
            .unwrap_or(Lattice::Different);
        let (branch_version, branch_implications) = match &value.inner {
            VariableValue::Hardware(value) => (
                Lattice::Defined(value.version),
                Lattice::Defined(value.implications.clone()),
            ),
            _ => (Lattice::Different, Lattice::Different),
        };
        let branch_implied = match &value.inner {
            VariableValue::Simple(value) => match value {
                &SimpleCompileValue::Bool(value) => Lattice::Defined(Implied::BoolConst(value)),
                SimpleCompileValue::Int(value) => {
                    Lattice::Defined(Implied::IntRange(ClosedNonEmptyMultiRange::single(value.clone())))
                }
                _ => Lattice::Different,
            },
            VariableValue::Compound(_) => Lattice::Different,
            VariableValue::Hardware(value) => {
                // try getting implication for version
                let version = value.version;
                let branch_implied = branch
                    .common
                    .implied
                    .get(&version)
                    .or_else(|| parent_flow.get_implied(version));

                if let Some(branch_implied) = branch_implied {
                    Lattice::Defined(branch_implied.clone())
                } else {
                    // try getting implication from specific value
                    if let HardwareType::Int(range) = &value.value_raw.ty {
                        Lattice::Defined(Implied::IntRange(range.clone()))
                    } else {
                        Lattice::Different
                    }
                }
            }
        };

        merged_compile = merged_compile.merge_eq(branch_compile);
        merged_version = merged_version.merge_eq(branch_version);
        merged_implications = merged_implications.merge(branch_implications, |a, b| LatticeMerge::Defined(a.join(&b)));
        merged_implied = merged_implied.merge(branch_implied, Implied::lattice_merge);
    }

    // handle simple result cases:
    // * undefined
    if !any_defined_branch {
        let content = VariableContent::NotFullyAssigned(VariableNotFullyAssigned::Undefined);
        return Ok((content, None));
    }

    // * compile
    if let Some(merged_compile) = merged_compile.defined() {
        let content = VariableContent::Assigned(Spanned::new(span_merge, VariableValue::from(merged_compile)));
        return Ok((content, None));
    }

    // all simple cases have been handled, we need a hardware merge
    // we know by now that all branches assign a value or are undefined
    fn unwrap_branch_value(v: &VariableContent) -> MaybeUndefined<Spanned<&VariableValue>> {
        match v {
            VariableContent::Assigned(v) => MaybeUndefined::Defined(v.as_ref()),
            VariableContent::NotFullyAssigned(kind) => match kind {
                VariableNotFullyAssigned::NotYetAssigned | VariableNotFullyAssigned::PartiallyAssigned => {
                    unreachable!("expected variable content")
                }
                VariableNotFullyAssigned::Undefined => MaybeUndefined::Undefined,
            },
            VariableContent::Error(_) => unreachable!("expected variable content"),
        }
    }
    fn unwrap_branch_slot(slot: &VariableSlotOption) -> &VariableContent {
        assert!(slot.info.is_none());
        slot.content.as_ref().unwrap()
    }

    // check that all types are hardware
    // (we do this before finding the common type to get nicer error messages)
    let mut branch_errors = IndexMap::new();
    let branch_tys = branches
        .iter()
        .map(|branch| {
            let (branch_content, branch_implied) = match branch.common.variables.get(&var.index) {
                Some(branch_slot) => (unwrap_branch_slot(branch_slot), Some(&branch.common.implied)),
                None => (parent_content, None),
            };
            let branch_value = unwrap_branch_value(branch_content);

            let branch_value = match branch_value {
                MaybeUndefined::Undefined => return Ok(HardwareType::Undefined),
                MaybeUndefined::Defined(branch_value) => branch_value,
            };
            let branch_ty = match branch_value.inner {
                VariableValue::Simple(v) => v.ty(),
                VariableValue::Compound(v) => v.ty(),
                VariableValue::Hardware(v) => {
                    let version = v.version;
                    let implied = branch_implied
                        .and_then(|implied| implied.get(&version))
                        .or_else(|| parent_flow.get_implied(version));
                    match implied {
                        None => v.value_raw.ty.as_type(),
                        Some(implied) => implied.ty_hw().as_type(),
                    }
                }
            };

            match branch_ty.as_hardware_type(elab) {
                Ok(ty) => Ok(ty),
                Err(NonHardwareType) => {
                    let ty_str = branch_ty.value_string(refs);
                    branch_errors.entry(branch_value.span).or_insert(ty_str);
                    Err(NonHardwareType)
                }
            }
        })
        .try_collect_all_vec();

    if !branch_errors.is_empty() {
        let mut diag = DiagnosticError::new(
            "branch assignment merging only works for hardware types",
            span_merge,
            "merging due to this branch",
        )
        .add_info(var_info.span_decl, "for this variable");

        for (value_span, ty_str) in branch_errors {
            let msg = format!("value assigned here has type `{ty_str}` which cannot be represented in hardware");
            diag = diag.add_info(value_span, msg);
        }

        let e = diag
            .add_footer_hint("avoid assigning different non-hardware values to the same variable in different branches")
            .report(diags);
        return Err(e);
    }
    let branch_tys = branch_tys.unwrap();

    // find common type
    let ty = branch_tys.iter().fold(Type::Undefined, |a, t| a.union(&t.as_type()));

    // convert common to hardware too
    let ty = ty.as_hardware_type(elab).map_err(|_| {
        let ty_str = ty.value_string(refs);

        let mut diag = DiagnosticError::new(
            "branch assignment merging needs hardware type",
            span_merge,
            format!("merging due to this branch, combined type `{ty_str}` cannot be represented in hardware"),
        )
        .add_info(var_info.span_decl, "for this variable");

        for (branch, ty) in zip_eq(&*branches, branch_tys) {
            if let Some(branch_slot) = branch.common.variables.get(&var.index) {
                let branch_content = unwrap_branch_slot(branch_slot);
                let branch_value = unwrap_branch_value(branch_content);

                match branch_value {
                    MaybeUndefined::Undefined => {}
                    MaybeUndefined::Defined(branch_value) => {
                        diag = diag.add_info(
                            branch_value.span,
                            format!("value in branch assigned here has type `{}`", ty.value_string(refs)),
                        )
                    }
                }
            }
        }
        if used_parent_value {
            let parent_value = unwrap_branch_value(parent_content);

            match parent_value {
                MaybeUndefined::Undefined => {}
                MaybeUndefined::Defined(parent_value) => {
                    diag = diag.add_info(
                        parent_value.span,
                        format!("value before branch assigned here has type `{}`", ty.value_string(refs)),
                    );
                }
            }
        }
        diag.report(diags)
    })?;

    // create result variable
    let var_ir = match var_info.join_ir_variable {
        None => {
            let var_ir_info = IrVariableInfo {
                ty: ty.as_ir(refs),
                debug_info_span: var_info.span_decl,
                debug_info_id: var_info.id.str(&refs.shared.interner).map(str::to_owned),
            };
            parent_flow.new_ir_variable(var_ir_info)
        }
        Some(var_ir) => var_ir,
    };

    // store values into that variable
    let mut domain = ValueDomain::CompileTime;
    let mut domain_cond = ValueDomain::CompileTime;

    let mut build_store = |value: MaybeUndefined<Spanned<&VariableValue>>,
                           implied: Option<&IndexMap<ValueVersion, Implied>>| {
        match value {
            MaybeUndefined::Undefined => {
                // undefined, skip store
                Ok(None)
            }
            MaybeUndefined::Defined(assigned) => {
                let (assigned_domain, assigned_expr) = match &assigned.inner {
                    Value::Simple(v) => (
                        v.domain(),
                        v.as_ir_expression_unchecked(refs, large, assigned.span, &ty)?,
                    ),
                    Value::Compound(v) => (
                        v.domain(),
                        v.as_ir_expression_unchecked(refs, large, assigned.span, &ty)?,
                    ),
                    Value::Hardware(v) => {
                        // get implied info
                        let version = v.version;
                        let implied = implied
                            .and_then(|implied| implied.get(&version))
                            .or_else(|| parent_flow.get_implied(version));

                        // no need to take a copy here,
                        //   we're immediately using this value in a store operation and then discarding it
                        let value = v.as_value_without_copy(large, implied);

                        // expand value to result type
                        let expr = value.as_ir_expression_unchecked(refs, large, assigned.span, &ty)?;

                        (value.domain(), expr)
                    }
                };

                domain = domain.join(assigned_domain);

                if matches!(assigned_expr, IrExpression::Variable(value_var) if value_var == var_ir) {
                    // copy from variable to itself, skip store
                    Ok(None)
                } else {
                    let store = IrStatement::Assign(IrAssignmentTarget::simple(var_ir), assigned_expr);
                    Ok(Some(Spanned::new(span_merge, store)))
                }
            }
        }
    };

    // store the values assigned in the branches
    for branch in branches {
        if let Some(branch_slot) = branch.common.variables.get(&var.index) {
            let branch_value = unwrap_branch_value(unwrap_branch_slot(branch_slot));
            if let Some(store) = build_store(branch_value, Some(&branch.common.implied))? {
                branch.common.statements.push(store);
            }
        }

        domain_cond = domain_cond.join(branch.cond_domain.inner);
    }

    // store the parent value once before the branches (if it's actually used)
    if used_parent_value {
        let parent_content = parent_flow.var_get_content(var_spanned)?;
        if let Some(parent_store) = build_store(unwrap_branch_value(parent_content), None)? {
            parent_flow.push_ir_statement(parent_store);
        }
    }

    domain = domain.join(domain_cond);

    // wrap result
    // (we don't need to set an implied range here, we've just created a new variable with the right type)
    let result_value = HardwareValue {
        ty,
        domain,
        expr: var_ir,
    };
    let version = merged_version
        .defined()
        .unwrap_or_else(|| parent_flow.root.next_version());
    let implications = merged_implications.defined().unwrap_or(BoolImplications::NONE);
    let result_var_value = VariableValueHardware {
        value_raw: result_value,
        version,
        implications,
    };
    let content = VariableContent::Assigned(Spanned::new(span_merge, VariableValue::Hardware(result_var_value)));

    let implied = merged_implied.defined().map(|implied| (version, implied));

    Ok((content, implied))
}

fn merge_branch_signal(
    parent_flow: &mut FlowHardware,
    signal: Signal,
    branches: &mut [FlowHardwareBranchContent],
) -> DiagResult<(SignalContent, Option<(ValueVersion, Implied)>)> {
    let mut merged_compile: Lattice<&CompileValue> = Lattice::Undefined;
    let mut merged_version: Lattice<ValueVersion> = Lattice::Undefined;
    let mut merged_implied: Lattice<Implied> = Lattice::Undefined;

    let parent_content = parent_flow.signal_get_content(signal);

    for branch in branches {
        let branch_content = branch.common.signals.get(&signal).unwrap_or(&parent_content);

        match branch_content {
            SignalContent::Compile(branch_value) => {
                let branch_implied = match branch_value {
                    Value::Simple(branch_value) => match branch_value {
                        &SimpleCompileValue::Bool(branch_value) => Lattice::Defined(Implied::BoolConst(branch_value)),
                        SimpleCompileValue::Int(branch_value) => Lattice::Defined(Implied::IntRange(
                            ClosedNonEmptyMultiRange::single(branch_value.clone()),
                        )),
                        _ => Lattice::Different,
                    },
                    _ => Lattice::Different,
                };

                merged_compile = merged_compile.merge_eq(Lattice::Defined(branch_value));
                merged_version = Lattice::Different;
                merged_implied = merged_implied.merge(branch_implied, Implied::lattice_merge);
            }
            SignalContent::Hardware(branch_content) => {
                let &SignalContentHardware {
                    version,
                    implications: _,
                } = branch_content;

                let branch_implied = branch
                    .common
                    .implied
                    .get(&version)
                    .or_else(|| parent_flow.get_implied(version))
                    .cloned();

                let branch_compile = match &branch_implied {
                    None => None,
                    Some(implied) => match implied {
                        &Implied::BoolConst(value) => Some(CompileValue::new_bool_ref(value)),
                        Implied::IntRange(_) => None,
                    },
                };

                let branch_compile = branch_compile.map(Lattice::Defined).unwrap_or(Lattice::Different);
                let branch_implied = branch_implied.map(Lattice::Defined).unwrap_or(Lattice::Different);

                merged_compile = merged_compile.merge_eq(branch_compile);
                merged_version = merged_version.merge_eq(Lattice::Defined(version));
                merged_implied = merged_implied.merge(branch_implied, Implied::lattice_merge);
            }
        }
    }

    // check if compile
    if let Some(merged_compile) = merged_compile.defined() {
        let content = SignalContent::Compile(merged_compile.clone());
        return Ok((content, None));
    }

    // not compile, figure out the version and implications
    let (version, implications) = match merged_version.defined() {
        None => {
            let version = parent_flow.root.next_version();
            (version, BoolImplications::NONE)
        }
        Some(version) => {
            let parent_implications = match parent_content {
                SignalContent::Compile(_) => BoolImplications::NONE,
                SignalContent::Hardware(parent_content) => parent_content.implications.clone(),
            };
            (version, parent_implications)
        }
    };

    let content = SignalContent::Hardware(SignalContentHardware { version, implications });
    let implied = merged_implied.defined().map(|implied| (version, implied));

    Ok((content, implied))
}

/// Map every hardware value (recursively) contained in a compound value through `f`,
///   keeping the compile-time parts unchanged.
fn map_compound_hardware<E: Clone, U, V>(
    refs: CompileRefs,
    value: &MixedCompoundValue<E>,
    name: &mut Option<String>,
    f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
) -> Result<MixedCompoundValue<U>, V> {
    fn with_child_name<R>(
        name: &mut Option<String>,
        suffix: impl Display,
        f: impl FnOnce(&mut Option<String>) -> R,
    ) -> R {
        let len = name.as_ref().map(String::len);
        if let Some(name) = name {
            swrite!(name, "_{suffix}");
        }
        let result = f(name);
        if let (Some(name), Some(len)) = (name, len) {
            name.truncate(len);
        }
        result
    }

    fn map_value<E: Clone, U, V>(
        refs: CompileRefs,
        value: &MixedValue<E>,
        name: &mut Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<MixedValue<U>, V> {
        match value {
            Value::Simple(v) => Ok(Value::Simple(v.clone())),
            Value::Compound(v) => Ok(Value::Compound(map_compound_hardware(refs, v, name, f)?)),
            Value::Hardware(v) => Ok(Value::Hardware(map_hardware(v, name, f)?)),
        }
    }

    fn map_hardware<E: Clone, U, V>(
        value: &HardwareValue<HardwareType, E>,
        name: &Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<HardwareValue<HardwareType, U>, V> {
        Ok(HardwareValue {
            ty: value.ty.clone(),
            domain: value.domain,
            expr: f(value, name.as_deref())?,
        })
    }

    fn map_int<E: Clone, U, V>(
        value: &HardwareInt<E>,
        name: &Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<HardwareInt<U>, V> {
        let value_hw: HardwareValue<HardwareType, E> = value.clone().into();
        Ok(HardwareValue {
            ty: value.ty.clone(),
            domain: value.domain,
            expr: f(&value_hw, name.as_deref())?,
        })
    }

    fn map_bound<E: Clone, U, V>(
        bound: &Option<MaybeCompile<BigInt, HardwareInt<E>>>,
        name: &Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<Option<MaybeCompile<BigInt, HardwareInt<U>>>, V> {
        Ok(match bound {
            None => None,
            Some(MaybeCompile::Compile(b)) => Some(MaybeCompile::Compile(b.clone())),
            Some(MaybeCompile::Hardware(b)) => Some(MaybeCompile::Hardware(map_int(b, name, f)?)),
        })
    }

    let result = match value {
        MixedCompoundValue::String(s) => {
            // name substitutions by their index among the substitutions
            let mut sub_index = 0;
            let pieces = s
                .pieces
                .iter()
                .map(|p| {
                    Ok(match p {
                        StringPiece::Literal(l) => StringPiece::Literal(l.clone()),
                        StringPiece::Substitute(v) => {
                            let suffix = format_args!("sub{sub_index}");
                            let v = with_child_name(name, suffix, |name| map_hardware(v, name, f))?;
                            sub_index += 1;
                            StringPiece::Substitute(v)
                        }
                    })
                })
                .try_collect_vec()?;
            MixedCompoundValue::String(Arc::new(MixedString { pieces }))
        }
        MixedCompoundValue::Range(r) => MixedCompoundValue::Range(match r {
            RangeValue::Compile(r) => RangeValue::Compile(r.clone()),
            RangeValue::HardwareBounds(r) => RangeValue::from_range(Range {
                start: with_child_name(name, "start", |name| map_bound(&r.range().start, name, f))?,
                end: with_child_name(name, "end", |name| map_bound(&r.range().end, name, f))?,
            }),
            RangeValue::HardwareStartLength { start, length } => RangeValue::HardwareStartLength {
                start: with_child_name(name, "start", |name| map_int(start, name, f))?,
                length: length.clone(),
            },
        }),
        MixedCompoundValue::Tuple(values) => MixedCompoundValue::Tuple(
            values
                .iter()
                .enumerate()
                .map(|(i, v)| with_child_name(name, i, |name| map_value(refs, v, name, f)))
                .try_collect_vec()?,
        ),
        MixedCompoundValue::Struct(v) => {
            let ty_info = refs.shared.elaboration_arenas.struct_info(v.ty);
            MixedCompoundValue::Struct(StructValue {
                ty: v.ty,
                fields: zip_eq(ty_info.fields.keys(), &v.fields)
                    .map(|(field_id, v)| {
                        let suffix = field_id.str(&refs.shared.interner);
                        with_child_name(name, suffix, |name| map_value(refs, v, name, f))
                    })
                    .try_collect_vec()?,
            })
        }
        MixedCompoundValue::Enum(v) => MixedCompoundValue::Enum(EnumValue {
            ty: v.ty,
            variant: v.variant,
            payload: match &v.payload {
                None => None,
                Some(p) => {
                    let ty_info = refs.shared.elaboration_arenas.enum_info(v.ty);
                    let (variant_id, _) = ty_info.variants.get_index(v.variant).unwrap();
                    let suffix = variant_id.str(&refs.shared.interner);
                    let p = with_child_name(name, suffix, |name| map_value(refs, p, name, f))?;
                    Some(Box::new(p))
                }
            },
        }),
        MixedCompoundValue::BoundMethod(m) => MixedCompoundValue::BoundMethod(BoundMethod {
            self_type: m.self_type.clone(),
            self_value: Box::new(with_child_name(name, "self", |name| {
                map_value(refs, &m.self_value, name, f)
            })?),
            method: Arc::clone(&m.method),
        }),
    };
    Ok(result)
}

impl VariableContent {
    fn err_ref(e: DiagError) -> &'static VariableContent {
        let _ = e;
        static ERR: VariableContent = VariableContent::Error(DiagError::promise_error_has_been_reported());
        &ERR
    }
}

impl VariableValueHardware {
    pub fn as_value_without_copy(&self, large: &mut IrLargeArena, implied: Option<&Implied>) -> ValueWithImplications {
        let &VariableValueHardware {
            version,
            ref value_raw,
            ref implications,
        } = self;

        // constrain type/variable if applicable
        let value = match implied {
            None => Value::Hardware(value_raw.clone().map_expression(IrExpression::Variable)),
            Some(implied) => match implied {
                &Implied::BoolConst(value) => Value::new_bool(value),
                Implied::IntRange(range) => {
                    let expr = large.push_expr(IrExpressionLarge::ConstrainIntRange(
                        range.enclosing().cloned(),
                        IrExpression::Variable(value_raw.expr),
                    ));
                    Value::Hardware(HardwareValue {
                        ty: HardwareType::Int(range.clone()),
                        domain: value_raw.domain,
                        expr,
                    })
                }
            },
        };

        // add version and implications, including self-implications
        value.map_hardware(|value| {
            let mut implications = implications.clone();
            if value.ty == HardwareType::Bool {
                implications.add_bool_self_implications(version);
            }

            HardwareValueWithImplications {
                value,
                version: Some(version),
                implications,
            }
        })
    }
}

impl Implied {
    fn ty_hw(&self) -> HardwareType {
        match self {
            Implied::BoolConst(_) => HardwareType::Bool,
            Implied::IntRange(range) => HardwareType::Int(range.clone()),
        }
    }

    fn lattice_merge(self, other: Implied) -> LatticeMerge<Implied> {
        match (self, other) {
            (Implied::BoolConst(a), Implied::BoolConst(b)) => {
                if a == b {
                    LatticeMerge::Defined(Implied::BoolConst(a))
                } else {
                    LatticeMerge::Different
                }
            }
            (Implied::IntRange(a), Implied::IntRange(b)) => {
                LatticeMerge::Defined(Implied::IntRange(a.union(&ClosedMultiRange::from(b))))
            }
            _ => LatticeMerge::Different,
        }
    }
}

impl VariableNotFullyAssigned {
    pub fn report_diag(&self, diags: &Diagnostics, span: Span, var_info: &VariableInfo) -> DiagError {
        match self {
            VariableNotFullyAssigned::NotYetAssigned => {
                DiagnosticError::new("variable has not yet been assigned a value", span, "variable used here")
                    .add_info(var_info.span_decl, "variable declared here")
                    .report(diags)
            }
            VariableNotFullyAssigned::PartiallyAssigned => DiagnosticError::new(
                "variable has not yet been assigned a value in all preceding branches",
                span,
                "variable used here",
            )
            .add_info(var_info.span_decl, "variable declared here")
            .report(diags),
            VariableNotFullyAssigned::Undefined => diags.report_error_internal(span, "evaluating undefined variable"),
        }
    }
}

impl FlowHardwareCommon {
    pub fn new() -> Self {
        FlowHardwareCommon {
            variables: IndexMap::new(),
            signals: IndexMap::new(),
            implied: IndexMap::new(),
            statements: vec![],
        }
    }
}

/// The borrow checking has trouble with nested chains of parent references,
/// but they're not actually unsafe in the way we want to use them.
// Suppress false positive https://github.com/rust-lang/rust-clippy/issues/12860.
#[allow(clippy::unnecessary_cast)]
mod lifetime_cast {
    use crate::front::flow::{FlowCompile, FlowHardware, FlowHardwareBranch, FlowHardwareRoot};

    pub unsafe fn compile_ref<'s>(flow: &'s FlowCompile) -> &'s FlowCompile<'s> {
        unsafe { &*(flow as *const FlowCompile<'_> as *const FlowCompile<'s>) }
    }
    pub unsafe fn compile_mut<'s>(flow: &'s mut FlowCompile) -> &'s mut FlowCompile<'s> {
        unsafe { &mut *(flow as *mut FlowCompile<'_> as *mut FlowCompile<'s>) }
    }
    pub unsafe fn hardware_ref<'s>(flow: &'s FlowHardware) -> &'s FlowHardware<'s> {
        unsafe { &*(flow as *const FlowHardware<'_> as *const FlowHardware<'s>) }
    }
    pub unsafe fn hardware_mut<'s>(flow: &'s mut FlowHardware) -> &'s mut FlowHardware<'s> {
        unsafe { &mut *(flow as *mut FlowHardware<'_> as *mut FlowHardware<'s>) }
    }
    pub unsafe fn hardware_root_mut<'s>(flow: &'s mut FlowHardwareRoot) -> &'s mut FlowHardwareRoot<'s> {
        unsafe { &mut *(flow as *mut FlowHardwareRoot<'_> as *mut FlowHardwareRoot<'s>) }
    }
    pub unsafe fn hardware_branch_mut<'s>(flow: &'s mut FlowHardwareBranch) -> &'s mut FlowHardwareBranch<'s> {
        unsafe { &mut *(flow as *mut FlowHardwareBranch<'_> as *mut FlowHardwareBranch<'s>) }
    }
}
