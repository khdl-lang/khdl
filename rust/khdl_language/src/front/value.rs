use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::{DiagResult, DiagnosticError};
use crate::front::domain::ValueDomain;
use crate::front::expression::LeftInterfaceInfo;
use crate::front::flow::{Flow, FlowRootId, Variable};
use crate::front::function::FunctionValue;
use crate::front::item::{
    ElaboratedEnum, ElaboratedInterface, ElaboratedInterfaceView, ElaboratedModule, ElaboratedStruct,
};
use crate::front::scope::FrozenScope;
use crate::front::signal::Signal;
use crate::front::types::{HardwareType, Type, TypeBool, Typed};
use crate::mid::ir::{IrArrayLiteralElement, IrExpression, IrExpressionLarge, IrLargeArena};
use crate::mid::steps::{IrTargetStepScalar, IrTargetSteps};
use crate::syntax::ast::{FunctionDeclaration, ParameterSelf, StringPiece};
use crate::syntax::hierarchy::HierarchyNode;
use crate::syntax::pos::Span;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::data::VecExt;
use crate::util::intern::Id;
use crate::util::iter::IterExt;
use crate::util::range::Range;
use crate::util::range_multi::{AnyMultiRange, ClosedNonEmptyMultiRange, MultiRange};
use crate::util::{Never, ResultNeverExt};
use itertools::{Itertools, zip_eq};
use khdl_util::swrite;
use std::fmt::Display;
use std::hash::Hash;
use std::sync::Arc;

pub type CompileValue = Value<SimpleCompileValue, CompileCompoundValue, Never>;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Value<S = SimpleCompileValue, C = MixedCompoundValue, H = HardwareValue> {
    // TODO should simple and hardware share one branch?
    // TODO rename simple to SimpleCompile?
    Simple(S),
    Compound(C),
    Hardware(H),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SimpleCompileValue {
    Type(Type),
    Bool(bool),
    Int(BigInt),
    Array(Arc<Vec<CompileValue>>),
    Function(FunctionValue),
    Module(ElaboratedModule),
    Interface(ElaboratedInterface),
    InterfaceArray(Vec<BigUint>, ElaboratedInterface),
    InterfaceView(ElaboratedInterfaceView),
    InterfaceViewArray(Vec<BigUint>, ElaboratedInterfaceView),
    Reference(ReferenceWrapper),
    Package(HierarchyNode),
}

// TODO rework, for vars only store FlowRootId, for signal/interface only store module
/// Wrapper around [Reference] that checks that the reference is actually valid in the current context.
///
/// This should never fail, because items elaboration already checks that references never cross between items.
/// This additional check only exists because [Variable], [Signal] and [Interface] are all newtyped indices
///   that are only unique within their original context, and accidentally using them in different contexts
///   would result in hard to debug issues.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ReferenceWrapper {
    pub span_decl: Span,
    pub span_ref: Span,
    inner: ReferenceWrapperInner,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum ReferenceWrapperInner {
    Variable {
        flow_id: FlowRootId,
        var: Variable,
        ty: Arc<Type>,
    },
    Signal {
        module: ElaboratedModule,
        signal: Signal,
        ty: Arc<Type>,
        ty_hw: Arc<HardwareType>,
    },
    Interface {
        module: ElaboratedModule,
        info: LeftInterfaceInfo,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ReferenceInner<'a> {
    Variable {
        var: Variable,
        ty: &'a Arc<Type>,
    },
    Signal {
        signal: Signal,
        ty: &'a Arc<Type>,
        ty_hw: &'a Arc<HardwareType>,
    },
    Interface(&'a LeftInterfaceInfo),
}

impl ReferenceWrapper {
    pub fn new_variable(flow: FlowRootId, var: Variable, ty: Arc<Type>, span_decl: Span, span_ref: Span) -> Self {
        let inner = ReferenceWrapperInner::Variable { flow_id: flow, var, ty };
        ReferenceWrapper {
            span_decl,
            span_ref,
            inner,
        }
    }

    pub fn new_signal(
        module: ElaboratedModule,
        signal: Signal,
        ty_hw: Arc<HardwareType>,
        span_decl: Span,
        span_ref: Span,
    ) -> Self {
        let ty = Arc::new(ty_hw.as_type());
        let inner = ReferenceWrapperInner::Signal {
            module,
            signal,
            ty,
            ty_hw,
        };
        ReferenceWrapper {
            span_decl,
            span_ref,
            inner,
        }
    }

    pub fn new_interface(module: ElaboratedModule, info: LeftInterfaceInfo, span_ref: Span) -> Self {
        let span_decl = info.span_id;
        let inner = ReferenceWrapperInner::Interface { module, info };
        ReferenceWrapper {
            span_decl,
            span_ref,
            inner,
        }
    }

    pub fn get(&self, ctx: &CompileItemContext, flow: &impl Flow, span: Span) -> DiagResult<ReferenceInner<'_>> {
        // check validness
        let build_error = |kind: &str, outside: &str| {
            DiagnosticError::new(
                format!("attempt to use {kind} reference outside its declaring {outside}"),
                span,
                "using reference here",
            )
            .add_info(self.span_decl, format!("{kind} declared here"))
            .add_info(self.span_ref, "reference taken here")
            .report(ctx.refs.diags)
        };
        match self.inner {
            ReferenceWrapperInner::Variable { flow_id, var: _, ty: _ } => {
                if flow_id != flow.root_id() {
                    return Err(build_error("variable", "context"));
                }
            }
            ReferenceWrapperInner::Signal {
                module,
                signal: _,
                ty: _,
                ty_hw: _,
            } => {
                if ctx.curr_module != Some(module) {
                    return Err(build_error("signal", "module"));
                }
            }
            ReferenceWrapperInner::Interface { module, info: _ } => {
                if ctx.curr_module != Some(module) {
                    return Err(build_error("interface", "module"));
                }
            }
        }

        // actually get inner
        Ok(self.get_unchecked())
    }

    pub fn get_unchecked(&self) -> ReferenceInner<'_> {
        match self.inner {
            ReferenceWrapperInner::Variable {
                flow_id: _,
                var,
                ref ty,
            } => ReferenceInner::Variable { var, ty },
            ReferenceWrapperInner::Signal {
                module: _,
                signal,
                ref ty,
                ref ty_hw,
            } => ReferenceInner::Signal { signal, ty, ty_hw },
            ReferenceWrapperInner::Interface { module: _, ref info } => ReferenceInner::Interface(info),
        }
    }
}

pub type MixedValue<E = IrExpression> =
    Value<SimpleCompileValue, MixedCompoundValue<E>, HardwareValue<HardwareType, E>>;

#[derive(Debug, Clone)]
pub enum MixedCompoundValue<E = IrExpression> {
    String(Arc<MixedString<E>>),
    Range(RangeValue<E>),
    Tuple(Vec<MixedValue<E>>),
    Struct(StructValue<MixedValue<E>>),
    Enum(EnumValue<Box<MixedValue<E>>>),
    BoundMethod(BoundMethod<MixedValue<E>>),
}

#[derive(Debug, Clone)]
pub struct MixedString<E = IrExpression> {
    pub pieces: Vec<StringPiece<Arc<String>, HardwareValue<HardwareType, E>>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum CompileCompoundValue {
    String(Arc<String>),
    Range(MultiRange<BigInt>),
    Tuple(Vec<CompileValue>),
    Struct(StructValue<CompileValue>),
    Enum(EnumValue<Box<CompileValue>>),
    BoundMethod(BoundMethod<CompileValue>),
}

/// This type intentionally does not implement Eq/PartialEq, comparing hardware values only makes sense at runtime,
/// not during compilation.
#[derive(Debug, Clone)]
pub struct HardwareValue<T = HardwareType, E = IrExpression> {
    pub ty: T,
    pub domain: ValueDomain,
    pub expr: E,
}

pub type HardwareInt<E = IrExpression> = HardwareValue<ClosedNonEmptyMultiRange<BigInt>, E>;
pub type HardwareUInt<E = IrExpression> = HardwareValue<ClosedNonEmptyMultiRange<BigUint>, E>;
pub type HardwareBool<E = IrExpression> = HardwareValue<TypeBool, E>;

#[derive(Debug, Clone)]
pub enum RangeValue<E = IrExpression> {
    Compile(MultiRange<BigInt>),
    HardwareBounds(HardwareBoundsRange<E>),
    // TODO allow hardware length, really only useful for "in" expressions
    HardwareStartLength { start: HardwareInt<E>, length: BigUint },
}

/// Range where at least one of the bounds is a hardware value.
/// Do not construct directly, use [RangeValue::from_range] instead.
#[derive(Debug, Clone)]
pub struct HardwareBoundsRange<E = IrExpression> {
    range: Range<MaybeCompile<BigInt, HardwareInt<E>>>,
}

impl<E> HardwareBoundsRange<E> {
    pub fn range(&self) -> &Range<MaybeCompile<BigInt, HardwareInt<E>>> {
        &self.range
    }
}

impl<E> RangeValue<E> {
    pub fn from_range(range: Range<MaybeCompile<BigInt, HardwareInt<E>>>) -> Self {
        fn as_compile<H>(bound: &Option<MaybeCompile<BigInt, H>>) -> Option<Option<&BigInt>> {
            match bound {
                None => Some(None),
                Some(MaybeCompile::Compile(bound)) => Some(Some(bound)),
                Some(MaybeCompile::Hardware(_)) => None,
            }
        }

        match (as_compile(&range.start), as_compile(&range.end)) {
            (Some(start), Some(end)) => RangeValue::Compile(MultiRange::from(Range {
                start: start.cloned(),
                end: end.cloned(),
            })),
            (None, _) | (_, None) => RangeValue::HardwareBounds(HardwareBoundsRange { range }),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct StructValue<V> {
    pub ty: ElaboratedStruct,
    pub fields: Vec<V>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct EnumValue<V> {
    pub ty: ElaboratedEnum,
    pub variant: usize,
    pub payload: Option<V>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct BoundMethod<V> {
    pub self_type: Type,
    pub self_value: Box<V>,
    pub method: Arc<MethodInfo>,
}

#[derive(Debug)]
pub struct MethodInfo {
    pub scope: Arc<FrozenScope>,
    pub name: Id,
    // TODO replace with AstRef
    pub func_decl: FunctionDeclaration<ParameterSelf>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum MaybeCompile<C, H> {
    Compile(C),
    Hardware(H),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum MaybeUndefined<T> {
    Undefined,
    Defined(T),
}

#[derive(Debug, Copy, Clone)]
pub struct NotCompile;

pub trait ValueCommon: Typed {
    /// Convert this value to a hardware value with the exact type `ty`.
    ///
    /// This fails if the value cannot be represented as a hardware value of the given type.
    /// The caller should have checked for type compatibility already, a type mismatch will result in an internal error.
    fn as_hardware_value_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: HardwareType,
    ) -> DiagResult<HardwareValue> {
        if cfg!(debug_assertions) {
            debug_assert!(ty.as_type().contains_type(&self.ty()));
        }

        // TODO avoid walking the hierarchy twice?
        let domain = self.domain();
        let expr = self.as_ir_expression_unchecked(refs, large, span, &ty)?;
        Ok(HardwareValue { ty, domain, expr })
    }

    fn domain(&self) -> ValueDomain;

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression>;
}

impl ValueCommon for Never {
    fn domain(&self) -> ValueDomain {
        self.unreachable()
    }
    fn as_ir_expression_unchecked(
        &self,
        _: CompileRefs,
        _: &mut IrLargeArena,
        _: Span,
        _: &HardwareType,
    ) -> DiagResult<IrExpression> {
        self.unreachable()
    }
}

impl<S: ValueCommon, C: ValueCommon, H: ValueCommon> ValueCommon for Value<S, C, H> {
    fn domain(&self) -> ValueDomain {
        match self {
            Value::Simple(v) => v.domain(),
            Value::Compound(v) => v.domain(),
            Value::Hardware(v) => v.domain(),
        }
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        match self {
            Value::Simple(v) => v.as_ir_expression_unchecked(refs, large, span, ty),
            Value::Compound(v) => v.as_ir_expression_unchecked(refs, large, span, ty),
            Value::Hardware(v) => v.as_ir_expression_unchecked(refs, large, span, ty),
        }
    }
}

impl ValueCommon for SimpleCompileValue {
    fn domain(&self) -> ValueDomain {
        ValueDomain::CompileTime
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        let err_type = || internal_err_hw_type_mismatch(refs, span, self, ty).report(refs.diags);

        match self {
            SimpleCompileValue::Type(_) => Err(err_type()),
            &SimpleCompileValue::Bool(v) => match ty {
                HardwareType::Bool => Ok(IrExpression::Bool(v)),
                _ => Err(err_type()),
            },
            SimpleCompileValue::Int(v) => match &ty {
                HardwareType::Int(ty) if ty.contains(v) => {
                    let expr = IrExpressionLarge::ExpandIntRange(ty.enclosing().cloned(), IrExpression::Int(v.clone()));
                    Ok(large.push_expr(expr))
                }
                _ => Err(err_type()),
            },
            SimpleCompileValue::Array(v) => match &ty {
                HardwareType::Array(e_ty, len) if &BigUint::from(v.len()) == len => {
                    // TODO if all values are the same, replace with repeat?
                    let result = v
                        .iter()
                        .map(|e| {
                            e.as_ir_expression_unchecked(refs, large, span, e_ty)
                                .map(IrArrayLiteralElement::Single)
                        })
                        .try_collect_vec()?;
                    let expr = large.push_expr(IrExpressionLarge::ArrayLiteral(e_ty.as_ir(refs), len.clone(), result));
                    Ok(expr)
                }
                _ => Err(err_type()),
            },
            SimpleCompileValue::Function(_)
            | SimpleCompileValue::Module(_)
            | SimpleCompileValue::Interface(_)
            | SimpleCompileValue::InterfaceArray(_, _)
            | SimpleCompileValue::InterfaceViewArray(_, _)
            | SimpleCompileValue::InterfaceView(_)
            | SimpleCompileValue::Reference(_)
            | SimpleCompileValue::Package(_) => Err(err_type()),
        }
    }
}

impl<E: Clone + Into<IrExpression>> ValueCommon for MixedCompoundValue<E> {
    fn domain(&self) -> ValueDomain {
        match self {
            MixedCompoundValue::String(v) => v.domain(),
            MixedCompoundValue::Range(v) => {
                fn opt_domain<C, H, E>(x: Option<&MaybeCompile<C, HardwareValue<H, E>>>) -> ValueDomain {
                    match x {
                        None => ValueDomain::CompileTime,
                        Some(start) => match start {
                            MaybeCompile::Compile(_) => ValueDomain::CompileTime,
                            MaybeCompile::Hardware(x) => x.domain,
                        },
                    }
                }

                match v {
                    RangeValue::Compile(_) => ValueDomain::CompileTime,
                    RangeValue::HardwareBounds(value) => {
                        let Range { start, end } = value.range();
                        ValueDomain::join(opt_domain(start.as_ref()), opt_domain(end.as_ref()))
                    }
                    RangeValue::HardwareStartLength { start, length } => {
                        let _: &BigUint = length;
                        start.domain
                    }
                }
            }
            MixedCompoundValue::Tuple(v) => ValueDomain::fold(v.iter().map(Value::domain)),
            MixedCompoundValue::Struct(v) => {
                let StructValue { ty: _, fields } = v;
                ValueDomain::fold(fields.iter().map(Value::domain))
            }
            MixedCompoundValue::Enum(v) => {
                let EnumValue {
                    ty: _,
                    variant: _,
                    payload,
                } = v;
                match payload {
                    None => ValueDomain::CompileTime,
                    Some(payload) => payload.domain(),
                }
            }
            MixedCompoundValue::BoundMethod(method) => {
                let BoundMethod {
                    self_type: _,
                    self_value,
                    method: _,
                } = method;
                self_value.domain()
            }
        }
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        let err_type = || internal_err_hw_type_mismatch(refs, span, self, ty).report(refs.diags);

        match self {
            MixedCompoundValue::Tuple(v) => match &ty {
                HardwareType::Tuple(ty) if v.len() == ty.len() => {
                    let result = zip_eq(v.iter(), ty.iter())
                        .map(|(e, e_ty)| e.as_ir_expression_unchecked(refs, large, span, e_ty))
                        .try_collect_vec()?;
                    Ok(large.push_expr(IrExpressionLarge::TupleLiteral(result)))
                }
                _ => Err(err_type()),
            },
            MixedCompoundValue::Struct(v) => match &ty {
                HardwareType::Struct(ty_hw) if ty_hw.inner() == v.ty => {
                    let info = refs.shared.elaboration_arenas.struct_info(ty_hw.inner());
                    let info_hw = info.hw.as_ref().unwrap();

                    let fields_ir = zip_eq(v.fields.iter(), info_hw.fields.iter())
                        .map(|(e, e_ty)| e.as_ir_expression_unchecked(refs, large, span, e_ty))
                        .try_collect_vec()?;

                    let result = IrExpressionLarge::StructLiteral(info_hw.ty_ir.clone(), fields_ir);
                    Ok(large.push_expr(result))
                }
                _ => Err(err_type()),
            },
            MixedCompoundValue::Enum(v) => match &ty {
                HardwareType::Enum(ty_hw) if ty_hw.inner() == v.ty => {
                    let &EnumValue {
                        ty: _,
                        variant,
                        ref payload,
                    } = v;
                    let info = refs.shared.elaboration_arenas.enum_info(ty_hw.inner());
                    let info_hw = info.hw.as_ref().unwrap();

                    let payload_ir = payload
                        .as_ref()
                        .map(|payload| {
                            let (payload_ty, _) = info_hw.payload_types[variant].as_ref().unwrap();
                            payload.as_ir_expression_unchecked(refs, large, span, payload_ty)
                        })
                        .transpose()?;

                    let result = IrExpressionLarge::EnumLiteral(info_hw.ty_ir.clone(), variant, payload_ir);
                    Ok(large.push_expr(result))
                }
                _ => Err(err_type()),
            },

            MixedCompoundValue::String(_) | MixedCompoundValue::Range(_) | MixedCompoundValue::BoundMethod(_) => {
                Err(err_type())
            }
        }
    }
}

impl<E> MixedString<E> {
    pub fn try_as_compile(&self) -> Result<Arc<String>, NotCompile> {
        // TODO simplify this by banning consecutive literals?
        let MixedString { pieces } = self;

        // check all compile
        let mut literals = Vec::with_capacity(pieces.len());
        for piece in pieces {
            match piece {
                StringPiece::Literal(s) => literals.push(s),
                StringPiece::Substitute(v) => {
                    let _: &HardwareValue<HardwareType, E> = v;
                    return Err(NotCompile);
                }
            }
        }

        // convert to single string
        if let Some(&s) = literals.single_ref() {
            Ok(Arc::clone(s))
        } else {
            let mut result = String::new();
            for s in literals {
                result.push_str(s.as_str());
            }
            Ok(Arc::new(result))
        }
    }

    pub fn domain(&self) -> ValueDomain {
        let MixedString { pieces } = self;
        ValueDomain::fold(pieces.iter().map(|p| match p {
            StringPiece::Literal(_) => ValueDomain::CompileTime,
            StringPiece::Substitute(v) => v.domain,
        }))
    }
}

impl ValueCommon for CompileCompoundValue {
    fn domain(&self) -> ValueDomain {
        ValueDomain::CompileTime
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        MixedCompoundValue::<IrExpression>::from(self.clone()).as_ir_expression_unchecked(refs, large, span, ty)
    }
}

impl<E: Clone + Into<IrExpression>> ValueCommon for HardwareValue<HardwareType, E> {
    fn domain(&self) -> ValueDomain {
        self.domain
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        let err_type = || internal_err_hw_type_mismatch(refs, span, self, ty).report(refs.diags);
        let expr: IrExpression = self.expr.clone().into();

        if &self.ty == ty {
            return Ok(expr.clone());
        }

        match (&self.ty, &ty) {
            (HardwareType::Bool, HardwareType::Bool) => Ok(expr.clone()),
            (HardwareType::Int(ty_curr), HardwareType::Int(ty)) => {
                if ty.contains_multi_range(ty_curr) {
                    Ok(large.push_expr(IrExpressionLarge::ExpandIntRange(ty.enclosing().cloned(), expr.clone())))
                } else {
                    Err(err_type())
                }
            }
            (HardwareType::Array(ty_inner_curr, len_curr), HardwareType::Array(ty_inner, len)) => {
                if len_curr != len {
                    return Err(err_type());
                }

                // TODO express this as a for loop in hardware? this can result in a lot of generated code
                // TODO clean this up once we have non-exclusive integer range
                let mut next = BigUint::ZERO;
                let iter = std::iter::from_fn(|| {
                    if &next < len {
                        let curr = next.clone();
                        next += 1u8;
                        Some(curr)
                    } else {
                        None
                    }
                });
                let result = iter
                    .map(|index| {
                        let step = IrTargetStepScalar::ArrayIndex(IrExpression::Int(index.into()));
                        let curr_elem_expr = large.push_expr(IrExpressionLarge::Steps {
                            base: expr.clone(),
                            steps: IrTargetSteps::single(step),
                        });
                        let curr_elem_hw = HardwareValue {
                            ty: ty_inner_curr.as_ref().clone(),
                            domain: self.domain,
                            expr: curr_elem_expr,
                        };
                        let elem_expr = curr_elem_hw.as_ir_expression_unchecked(refs, large, span, ty_inner)?;
                        Ok(IrArrayLiteralElement::Single(elem_expr))
                    })
                    .try_collect_vec()?;

                Ok(large.push_expr(IrExpressionLarge::ArrayLiteral(
                    ty_inner.as_ir(refs),
                    len.clone(),
                    result,
                )))
            }
            (HardwareType::Tuple(ty_curr), HardwareType::Tuple(ty)) => {
                if ty_curr.len() != ty.len() {
                    return Err(err_type());
                }

                let result = (0..ty.len())
                    .map(|i| {
                        let step = IrTargetStepScalar::TupleIndex(i);
                        let curr_elem_expr = large.push_expr(IrExpressionLarge::Steps {
                            base: expr.clone(),
                            steps: IrTargetSteps::single(step),
                        });
                        let curr_elem_hw = HardwareValue {
                            ty: ty_curr[i].clone(),
                            domain: self.domain,
                            expr: curr_elem_expr,
                        };
                        curr_elem_hw.as_ir_expression_unchecked(refs, large, span, &ty[i])
                    })
                    .try_collect_vec()?;

                Ok(large.push_expr(IrExpressionLarge::TupleLiteral(result)))
            }
            (HardwareType::Struct(_), HardwareType::Struct(_)) | (HardwareType::Enum(_), HardwareType::Enum(_)) => {
                // there's no struct or enum subtyping yet, so this is always an error for now
                Err(err_type())
            }
            (
                HardwareType::Undefined
                | HardwareType::Bool
                | HardwareType::Int(_)
                | HardwareType::Array(_, _)
                | HardwareType::Tuple(_)
                | HardwareType::Struct(_)
                | HardwareType::Enum(_),
                _,
            ) => Err(err_type()),
        }
    }
}

impl CompileValue {
    /// Check whether this value contains a reference.
    ///
    /// This is not watertight, it is still possible for captured references to be stored inside the captured scope
    /// for functions. This check just exists to get earlier error messages for common cases.
    pub fn definitely_contains_reference(&self) -> bool {
        match self {
            CompileValue::Simple(v) => match v {
                SimpleCompileValue::Reference(_) => true,
                SimpleCompileValue::Array(v) => v.iter().any(CompileValue::definitely_contains_reference),
                SimpleCompileValue::Type(_)
                | SimpleCompileValue::Bool(_)
                | SimpleCompileValue::Int(_)
                | SimpleCompileValue::Function(_)
                | SimpleCompileValue::Module(_)
                | SimpleCompileValue::Interface(_)
                | SimpleCompileValue::InterfaceArray(_, _)
                | SimpleCompileValue::InterfaceView(_)
                | SimpleCompileValue::InterfaceViewArray(_, _)
                | SimpleCompileValue::Package(_) => false,
            },
            CompileValue::Compound(v) => match v {
                CompileCompoundValue::Tuple(v) => v.iter().any(CompileValue::definitely_contains_reference),
                CompileCompoundValue::Struct(v) => v.fields.iter().any(CompileValue::definitely_contains_reference),
                CompileCompoundValue::Enum(v) => v.payload.as_ref().is_some_and(|p| p.definitely_contains_reference()),
                CompileCompoundValue::BoundMethod(v) => v.self_value.definitely_contains_reference(),
                CompileCompoundValue::String(_) | CompileCompoundValue::Range(_) => false,
            },
            CompileValue::Hardware(never) => never.unreachable(),
        }
    }
}

fn internal_err_hw_type_mismatch(
    refs: CompileRefs,
    span: Span,
    value: &impl Typed,
    target_ty: &HardwareType,
) -> DiagnosticError {
    let title = format!(
        "wrong type when converting value with type {} to hardware value with type {}",
        value.ty().value_string(refs),
        target_ty.value_string(refs)
    );
    DiagnosticError::new_internal_compiler_error(title, span)
}

impl<C, H> Value<SimpleCompileValue, C, H> {
    pub fn new_ty(ty: Type) -> Self {
        Value::Simple(SimpleCompileValue::Type(ty))
    }

    pub fn new_bool(v: bool) -> Self {
        Value::Simple(SimpleCompileValue::Bool(v))
    }

    pub fn new_bool_ref(v: bool) -> &'static Self {
        match v {
            true => &Value::Simple(SimpleCompileValue::Bool(true)),
            false => &Value::Simple(SimpleCompileValue::Bool(false)),
        }
    }

    // TODO accept Into<BigInt>
    pub fn new_int(v: BigInt) -> Self {
        Value::Simple(SimpleCompileValue::Int(v))
    }
}

impl<S, C: From<CompileCompoundValue>, H> Value<S, C, H> {
    pub fn unit() -> Self {
        Value::Compound(C::from(CompileCompoundValue::Tuple(vec![])))
    }
}

impl<T, E> HardwareValue<T, E> {
    pub fn map_type<U>(self, f: impl FnOnce(T) -> U) -> HardwareValue<U, E> {
        HardwareValue {
            ty: f(self.ty),
            domain: self.domain,
            expr: self.expr,
        }
    }

    pub fn map_expression<U>(self, f: impl FnOnce(E) -> U) -> HardwareValue<T, U> {
        self.try_map_expression::<U, Never>(|e| Ok(f(e))).remove_never()
    }

    pub fn try_map_expression<U, V>(self, f: impl FnOnce(E) -> Result<U, V>) -> Result<HardwareValue<T, U>, V> {
        Ok(HardwareValue {
            ty: self.ty,
            domain: self.domain,
            expr: f(self.expr)?,
        })
    }
}

impl<E, H> From<CompileValue> for Value<SimpleCompileValue, MixedCompoundValue<E>, H> {
    fn from(v: CompileValue) -> Self {
        match v {
            CompileValue::Simple(v) => Value::Simple(v),
            CompileValue::Compound(v) => Value::Compound(MixedCompoundValue::from(v)),
            CompileValue::Hardware(never) => never.unreachable(),
        }
    }
}
impl<E> From<CompileCompoundValue> for MixedCompoundValue<E> {
    fn from(v: CompileCompoundValue) -> Self {
        match v {
            CompileCompoundValue::String(v) => {
                let pieces = if v.as_str().is_empty() {
                    vec![]
                } else {
                    vec![StringPiece::Literal(v.clone())]
                };
                MixedCompoundValue::String(Arc::new(MixedString { pieces }))
            }
            CompileCompoundValue::Range(v) => MixedCompoundValue::Range(RangeValue::Compile(v)),
            CompileCompoundValue::Tuple(v) => MixedCompoundValue::Tuple(v.into_iter().map(Value::from).collect_vec()),
            CompileCompoundValue::Struct(StructValue { ty, fields }) => {
                let fields = fields.into_iter().map(Value::from).collect();
                MixedCompoundValue::Struct(StructValue { ty, fields })
            }
            CompileCompoundValue::Enum(EnumValue { ty, variant, payload }) => {
                let payload = payload.map(|e| Box::new(Value::from(*e)));
                MixedCompoundValue::Enum(EnumValue { ty, variant, payload })
            }
            CompileCompoundValue::BoundMethod(m) => {
                let BoundMethod {
                    self_type,
                    self_value,
                    method,
                } = m;
                let self_value = Box::new(Value::from(*self_value));
                MixedCompoundValue::BoundMethod(BoundMethod {
                    self_type,
                    self_value,
                    method,
                })
            }
        }
    }
}

impl<E> From<HardwareInt<E>> for HardwareValue<HardwareType, E> {
    fn from(value: HardwareInt<E>) -> Self {
        value.map_type(HardwareType::Int)
    }
}
impl<E> From<HardwareUInt<E>> for HardwareValue<HardwareType, E> {
    fn from(value: HardwareUInt<E>) -> Self {
        value.map_type(|range| HardwareType::Int(range.map(BigInt::from)))
    }
}
impl<E> From<HardwareBool<E>> for HardwareValue<HardwareType, E> {
    fn from(value: HardwareBool<E>) -> Self {
        value.map_type(|_: TypeBool| HardwareType::Bool)
    }
}

impl<E> From<HardwareUInt<E>> for HardwareInt<E> {
    fn from(value: HardwareUInt<E>) -> Self {
        value.map_type(|range| range.map(BigInt::from))
    }
}
impl<E> TryFrom<HardwareInt<E>> for HardwareUInt<E> {
    type Error = HardwareInt<E>;

    fn try_from(value: HardwareInt<E>) -> Result<Self, Self::Error> {
        if value.ty.enclosing().start.is_negative() {
            Err(value)
        } else {
            let HardwareValue { ty, domain, expr } = value;
            let ty = ty.map(|x| BigUint::try_from(x).expect("already checked start"));
            Ok(HardwareValue { ty, domain, expr })
        }
    }
}

impl<C, E, H: Into<HardwareValue<HardwareType, E>>> From<MaybeCompile<BigInt, H>>
    for Value<SimpleCompileValue, C, HardwareValue<HardwareType, E>>
{
    fn from(value: MaybeCompile<BigInt, H>) -> Self {
        match value {
            MaybeCompile::Compile(v) => Value::Simple(SimpleCompileValue::Int(v)),
            MaybeCompile::Hardware(v) => Value::Hardware(v.into()),
        }
    }
}

impl<E, H> TryFrom<&Value<SimpleCompileValue, MixedCompoundValue<E>, H>> for CompileValue {
    type Error = NotCompile;
    fn try_from(v: &Value<SimpleCompileValue, MixedCompoundValue<E>, H>) -> Result<Self, Self::Error> {
        match v {
            Value::Simple(v) => Ok(CompileValue::Simple(v.clone())),
            Value::Compound(v) => Ok(CompileValue::Compound(CompileCompoundValue::try_from(v)?)),
            Value::Hardware(_) => Err(NotCompile),
        }
    }
}
impl<E> TryFrom<&MixedCompoundValue<E>> for CompileCompoundValue {
    type Error = NotCompile;
    fn try_from(v: &MixedCompoundValue<E>) -> Result<Self, Self::Error> {
        match v {
            MixedCompoundValue::String(v) => v.try_as_compile().map(CompileCompoundValue::String),
            MixedCompoundValue::Range(v) => match v {
                RangeValue::Compile(v) => Ok(CompileCompoundValue::Range(v.clone())),
                RangeValue::HardwareBounds(_) | RangeValue::HardwareStartLength { start: _, length: _ } => {
                    Err(NotCompile)
                }
            },
            MixedCompoundValue::Tuple(v) => {
                let v = v.iter().map(CompileValue::try_from).try_collect_vec()?;
                Ok(CompileCompoundValue::Tuple(v))
            }
            MixedCompoundValue::Struct(v) => {
                let fields = v.fields.iter().map(CompileValue::try_from).try_collect_vec()?;
                Ok(CompileCompoundValue::Struct(StructValue { ty: v.ty, fields }))
            }
            MixedCompoundValue::Enum(v) => {
                let payload = v
                    .payload
                    .as_ref()
                    .map(|e| CompileValue::try_from(&**e).map(Box::new))
                    .transpose()?;
                Ok(CompileCompoundValue::Enum(EnumValue {
                    ty: v.ty,
                    variant: v.variant,
                    payload,
                }))
            }
            MixedCompoundValue::BoundMethod(m) => {
                let self_value = Box::new(CompileValue::try_from(&*m.self_value)?);
                Ok(CompileCompoundValue::BoundMethod(BoundMethod {
                    self_type: m.self_type.clone(),
                    self_value,
                    method: Arc::clone(&m.method),
                }))
            }
        }
    }
}

impl<S, C, H> Value<S, C, H> {
    // TODO these should probably always be recursive?
    pub fn map_hardware<U>(self, f: impl FnOnce(H) -> U) -> Value<S, C, U> {
        self.try_map_hardware::<U, Never>(|v| Ok(f(v))).remove_never()
    }

    pub fn try_map_hardware<T, E>(self, f: impl FnOnce(H) -> Result<T, E>) -> Result<Value<S, C, T>, E> {
        match self {
            Value::Simple(v) => Ok(Value::Simple(v)),
            Value::Compound(v) => Ok(Value::Compound(v)),
            Value::Hardware(v) => Ok(Value::Hardware(f(v)?)),
        }
    }
}

impl<E: Clone> MixedValue<E> {
    /// Map every hardware value contained in this value (recursively) through `f`,
    /// keeping the compile-time parts unchanged.
    pub fn map_hardware_recursive<U>(
        &self,
        refs: CompileRefs,
        name: Option<&str>,
        mut f: impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> U,
    ) -> MixedValue<U> {
        let mut name = name.map(str::to_owned);
        self.map_hardware_recursive_impl::<U, Never>(refs, &mut name, &mut |v, name| Ok(f(v, name)))
            .remove_never()
    }

    /// Fallible version of [Self::map_hardware_recursive].
    pub fn try_map_hardware_recursive<U, V>(
        &self,
        refs: CompileRefs,
        name: Option<&str>,
        mut f: impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<MixedValue<U>, V> {
        let mut name = name.map(str::to_owned);
        self.map_hardware_recursive_impl(refs, &mut name, &mut f)
    }

    fn map_hardware_recursive_impl<U, V>(
        &self,
        refs: CompileRefs,
        name: &mut Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<MixedValue<U>, V> {
        let result = match self {
            Value::Simple(v) => Value::Simple(v.clone()),
            Value::Compound(v) => Value::Compound(v.map_hardware_recursive_impl(refs, name, f)?),
            Value::Hardware(v) => Value::Hardware(HardwareValue {
                ty: v.ty.clone(),
                domain: v.domain,
                expr: f(v, name.as_deref())?,
            }),
        };
        Ok(result)
    }
}

impl<E: Clone> MixedCompoundValue<E> {
    /// See [MixedValue::map_hardware_recursive].
    pub fn map_hardware_recursive<U>(
        &self,
        refs: CompileRefs,
        name: Option<&str>,
        mut f: impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> U,
    ) -> MixedCompoundValue<U> {
        let mut name = name.map(str::to_owned);
        self.map_hardware_recursive_impl::<U, Never>(refs, &mut name, &mut |v, name| Ok(f(v, name)))
            .remove_never()
    }

    /// See [MixedValue::try_map_hardware_recursive].
    pub fn try_map_hardware_recursive<U, V>(
        &self,
        refs: CompileRefs,
        name: Option<&str>,
        mut f: impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<MixedCompoundValue<U>, V> {
        let mut name = name.map(str::to_owned);
        self.map_hardware_recursive_impl(refs, &mut name, &mut f)
    }

    fn map_hardware_recursive_impl<U, V>(
        &self,
        refs: CompileRefs,
        name: &mut Option<String>,
        f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
    ) -> Result<MixedCompoundValue<U>, V> {
        /// run `f` with `name` temporarily extended by `_{suffix}`.
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

        fn map_int<E: Clone, U, V>(
            value: &HardwareInt<E>,
            name: &Option<String>,
            f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
        ) -> Result<HardwareInt<U>, V> {
            Ok(HardwareValue {
                ty: value.ty.clone(),
                domain: value.domain,
                expr: f(&value.clone().into(), name.as_deref())?,
            })
        }

        fn map_bound<E: Clone, U, V>(
            bound: &Option<MaybeCompile<BigInt, HardwareInt<E>>>,
            name: &Option<String>,
            f: &mut impl FnMut(&HardwareValue<HardwareType, E>, Option<&str>) -> Result<U, V>,
        ) -> Result<Option<MaybeCompile<BigInt, HardwareInt<U>>>, V> {
            bound
                .as_ref()
                .map(|bound| match bound {
                    MaybeCompile::Compile(b) => Ok(MaybeCompile::Compile(b.clone())),
                    MaybeCompile::Hardware(b) => Ok(MaybeCompile::Hardware(map_int(b, name, f)?)),
                })
                .transpose()
        }

        let result = match self {
            MixedCompoundValue::String(s) => {
                let mut sub_index = 0;
                let pieces = s
                    .pieces
                    .iter()
                    .map(|p| match p {
                        StringPiece::Literal(l) => Ok(StringPiece::Literal(l.clone())),
                        StringPiece::Substitute(v) => {
                            let suffix = format_args!("sub{sub_index}");
                            let expr = with_child_name(name, suffix, |name| f(v, name.as_deref()))?;
                            sub_index += 1;
                            Ok(StringPiece::Substitute(HardwareValue {
                                ty: v.ty.clone(),
                                domain: v.domain,
                                expr,
                            }))
                        }
                    })
                    .try_collect_vec()?;
                MixedCompoundValue::String(Arc::new(MixedString { pieces }))
            }
            MixedCompoundValue::Range(r) => {
                let r = match r {
                    RangeValue::Compile(r) => RangeValue::Compile(r.clone()),
                    RangeValue::HardwareBounds(r) => RangeValue::from_range(Range {
                        start: with_child_name(name, "start", |name| map_bound(&r.range().start, name, f))?,
                        end: with_child_name(name, "end", |name| map_bound(&r.range().end, name, f))?,
                    }),
                    RangeValue::HardwareStartLength { start, length } => RangeValue::HardwareStartLength {
                        start: with_child_name(name, "start", |name| map_int(start, name, f))?,
                        length: length.clone(),
                    },
                };
                MixedCompoundValue::Range(r)
            }
            MixedCompoundValue::Tuple(values) => MixedCompoundValue::Tuple(
                values
                    .iter()
                    .enumerate()
                    .map(|(i, v)| with_child_name(name, i, |name| v.map_hardware_recursive_impl(refs, name, f)))
                    .try_collect_vec()?,
            ),
            MixedCompoundValue::Struct(v) => {
                let ty_info = refs.shared.elaboration_arenas.struct_info(v.ty);
                let fields = zip_eq(ty_info.fields.keys(), &v.fields)
                    .map(|(field_id, v)| {
                        let suffix = field_id.str(&refs.shared.interner);
                        with_child_name(name, suffix, |name| v.map_hardware_recursive_impl(refs, name, f))
                    })
                    .try_collect_vec()?;
                MixedCompoundValue::Struct(StructValue { ty: v.ty, fields })
            }
            MixedCompoundValue::Enum(v) => {
                let payload = v
                    .payload
                    .as_ref()
                    .map(|payload| {
                        let ty_info = refs.shared.elaboration_arenas.enum_info(v.ty);
                        let (variant_id, _) = ty_info.variants.get_index(v.variant).unwrap();
                        let suffix = variant_id.str(&refs.shared.interner);
                        let p =
                            with_child_name(name, suffix, |name| payload.map_hardware_recursive_impl(refs, name, f))?;
                        Ok(Box::new(p))
                    })
                    .transpose()?;

                MixedCompoundValue::Enum(EnumValue {
                    ty: v.ty,
                    variant: v.variant,
                    payload,
                })
            }
            MixedCompoundValue::BoundMethod(m) => {
                let self_value = with_child_name(name, "self", |name| {
                    m.self_value.map_hardware_recursive_impl(refs, name, f)
                })?;
                MixedCompoundValue::BoundMethod(BoundMethod {
                    self_type: m.self_type.clone(),
                    self_value: Box::new(self_value),
                    method: Arc::clone(&m.method),
                })
            }
        };
        Ok(result)
    }
}

impl<S: Typed, C: Typed, H: Typed> Typed for Value<S, C, H> {
    fn ty(&self) -> Type {
        match self {
            Value::Simple(v) => v.ty(),
            Value::Compound(v) => v.ty(),
            Value::Hardware(v) => v.ty(),
        }
    }
}
impl<E> Typed for MixedCompoundValue<E> {
    fn ty(&self) -> Type {
        match self {
            MixedCompoundValue::String(_) => Type::String,
            MixedCompoundValue::Range(_) => Type::Range,
            MixedCompoundValue::Tuple(values) => Type::Tuple(Some(Arc::new(values.iter().map(Value::ty).collect()))),
            MixedCompoundValue::Struct(value) => Type::Struct(value.ty),
            MixedCompoundValue::Enum(value) => Type::Enum(value.ty),
            MixedCompoundValue::BoundMethod(_) => Type::Function,
        }
    }
}
impl Typed for CompileCompoundValue {
    fn ty(&self) -> Type {
        match self {
            CompileCompoundValue::String(_) => Type::String,
            CompileCompoundValue::Range(_) => Type::Range,
            CompileCompoundValue::Tuple(values) => Type::Tuple(Some(Arc::new(values.iter().map(Value::ty).collect()))),
            CompileCompoundValue::Struct(value) => Type::Struct(value.ty),
            CompileCompoundValue::Enum(value) => Type::Enum(value.ty),
            CompileCompoundValue::BoundMethod(_) => Type::Function,
        }
    }
}
impl Typed for SimpleCompileValue {
    fn ty(&self) -> Type {
        match self {
            SimpleCompileValue::Type(_) => Type::Type,
            SimpleCompileValue::Bool(_) => Type::Bool,
            SimpleCompileValue::Int(v) => Type::Int(MultiRange::single(v.clone())),
            SimpleCompileValue::Array(values) => {
                // TODO precompute this once? this can get slow for large arrays
                let ty_inner = Type::union_all(values.iter().map(CompileValue::ty));
                Type::Array(Arc::new(ty_inner), Some(BigUint::from(values.len())))
            }
            SimpleCompileValue::Function(_) => Type::Function,
            SimpleCompileValue::Module(_) => Type::Module,
            SimpleCompileValue::Interface(_) => Type::Interface,
            SimpleCompileValue::InterfaceArray(lengths, _) => Type::InterfaceArray(lengths.clone()),
            SimpleCompileValue::InterfaceView(_) => Type::InterfaceView,
            SimpleCompileValue::InterfaceViewArray(lengths, _) => Type::InterfaceViewArray(lengths.clone()),
            SimpleCompileValue::Reference(rf) => match rf.get_unchecked() {
                ReferenceInner::Variable { var: _, ty } => Type::Ref(Arc::clone(ty)),
                ReferenceInner::Signal {
                    signal: _,
                    ty,
                    ty_hw: _,
                } => Type::Ref(Arc::clone(ty)),
                ReferenceInner::Interface(info) => Type::RefInterface(info.intf.shape().to_vec(), info.elab.inner),
            },
            SimpleCompileValue::Package(_) => Type::HierarchyNode,
        }
    }
}

impl<E> Typed for HardwareValue<HardwareType, E> {
    fn ty(&self) -> Type {
        self.ty.as_type()
    }
}
impl<D: Typed> Typed for MaybeUndefined<D> {
    fn ty(&self) -> Type {
        match self {
            MaybeUndefined::Undefined => Type::Undefined,
            MaybeUndefined::Defined(v) => v.ty(),
        }
    }
}

impl<T> MaybeUndefined<T> {
    pub fn map_defined<U>(self, f: impl FnOnce(T) -> U) -> MaybeUndefined<U> {
        match self {
            MaybeUndefined::Undefined => MaybeUndefined::Undefined,
            MaybeUndefined::Defined(v) => MaybeUndefined::Defined(f(v)),
        }
    }

    pub fn as_ref(&self) -> MaybeUndefined<&T> {
        match self {
            MaybeUndefined::Undefined => MaybeUndefined::Undefined,
            MaybeUndefined::Defined(v) => MaybeUndefined::Defined(v),
        }
    }
}

impl<T: Clone> MaybeUndefined<&T> {
    pub fn cloned(self) -> MaybeUndefined<T> {
        match self {
            MaybeUndefined::Undefined => MaybeUndefined::Undefined,
            MaybeUndefined::Defined(v) => MaybeUndefined::Defined(v.clone()),
        }
    }
}

impl<C, H> MaybeCompile<C, H> {
    pub fn map_compile<U>(self, f: impl FnOnce(C) -> U) -> MaybeCompile<U, H> {
        match self {
            MaybeCompile::Compile(v) => MaybeCompile::Compile(f(v)),
            MaybeCompile::Hardware(v) => MaybeCompile::Hardware(v),
        }
    }

    pub fn map_hardware<U>(self, f: impl FnOnce(H) -> U) -> MaybeCompile<C, U> {
        match self {
            MaybeCompile::Compile(v) => MaybeCompile::Compile(v),
            MaybeCompile::Hardware(v) => MaybeCompile::Hardware(f(v)),
        }
    }

    pub fn unwrap_compile(self) -> Result<C, NotCompile> {
        match self {
            MaybeCompile::Compile(v) => Ok(v),
            MaybeCompile::Hardware(_) => Err(NotCompile),
        }
    }
}

impl<E> MaybeCompile<BigInt, HardwareInt<E>> {
    pub fn range(&self) -> ClosedNonEmptyMultiRange<BigInt> {
        match self {
            MaybeCompile::Compile(value) => ClosedNonEmptyMultiRange::single(value.clone()),
            MaybeCompile::Hardware(value) => value.ty.clone(),
        }
    }
}

impl<E> MaybeCompile<BigUint, HardwareUInt<E>> {
    pub fn range(&self) -> ClosedNonEmptyMultiRange<BigUint> {
        match self {
            MaybeCompile::Compile(value) => ClosedNonEmptyMultiRange::single(value.clone()),
            MaybeCompile::Hardware(value) => value.ty.clone(),
        }
    }
}

impl MethodInfo {
    fn eq_key(&self) -> impl Eq + Hash {
        let MethodInfo {
            scope,
            name: _,
            func_decl,
        } = self;
        (Arc::as_ptr(scope), func_decl.span)
    }
}

impl Eq for MethodInfo {}
impl PartialEq for MethodInfo {
    fn eq(&self, other: &Self) -> bool {
        self.eq_key() == other.eq_key()
    }
}
impl Hash for MethodInfo {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.eq_key().hash(state)
    }
}
