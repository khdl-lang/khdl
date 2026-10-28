use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::ValueDomain;
use crate::front::implication::{HardwareValueWithImplications, ValueWithImplications};
use crate::front::signal::PortInfo;
use crate::front::types::{HardwareType, Type, TypeBool, Typed};
use crate::front::value::{
    CompileCompoundValue, CompileValue, HardwareInt, HardwareUInt, HardwareValue, MaybeCompile, MixedCompoundValue,
    MixedString, RangeValue, SimpleCompileValue, Value,
};
use crate::syntax::ast::{PortDirection, SyncDomain};
use crate::syntax::pos::{Span, Spanned};
use crate::syntax::token::TOKEN_STR_UNSAFE_VALUE_WITH_DOMAIN;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::iter::IterExt;
use crate::util::range::Range;
use crate::util::range_multi::MultiRange;
use std::fmt::Debug;
use std::sync::Arc;

impl CompileItemContext<'_, '_> {
    pub fn check_valid_domain_crossing(
        &self,
        crossing_span: Span,
        source: Spanned<ValueDomain>,
        target: Spanned<ValueDomain>,
        required_reason: &str,
    ) -> DiagResult {
        let diags = self.refs.diags;

        let valid = match (target.inner, source.inner) {
            (ValueDomain::Clock, ValueDomain::Clock) => Ok(()),
            (ValueDomain::Clock, _) => Err("non-clock to clock"),
            (ValueDomain::Sync(_), ValueDomain::Clock) => Err("clock to sync"),
            (ValueDomain::Sync(_), ValueDomain::Async) => Err("async to sync"),

            // compile-time from nothing else and to everything
            (_, ValueDomain::CompileTime) => Ok(()),
            (ValueDomain::CompileTime, _) => Err("non compile to compile"),

            // const only from const and to everything
            (_, ValueDomain::Const) => Ok(()),
            (ValueDomain::Const, _) => Err("non-const to const"),

            // async from everything
            (ValueDomain::Async, _) => Ok(()),

            // sync only if matching
            // TODO expand this to look though wires without logic
            (ValueDomain::Sync(target_inner), ValueDomain::Sync(source_inner)) => {
                let SyncDomain {
                    clock: target_clock,
                    reset: target_reset,
                } = target_inner;
                let SyncDomain {
                    clock: source_clock,
                    reset: source_reset,
                } = source_inner;

                // protect again clock domain crossings
                let clock_match = target_clock == source_clock;
                // protect against the source resetting while the target is not
                let reset_match = match (target_reset, source_reset) {
                    (_, None) => true,
                    (None, Some(_)) => false,
                    (Some(target_reset), Some(source_reset)) => target_reset == source_reset,
                };

                match (clock_match, reset_match) {
                    (true, true) => Ok(()),
                    (false, true) => Err("different clock"),
                    (true, false) => Err("different reset"),
                    (false, false) => Err("different clock and reset"),
                }
            }
        };

        valid.map_err(|invalid_reason| {
            let target_str = target.inner.diagnostic_string(self);
            let source_str = source.inner.diagnostic_string(self);
            DiagnosticError::new(
                format!("invalid domain crossing: {invalid_reason}"),
                crossing_span,
                "invalid domain crossing here",
            )
            .add_info(target.span, format!("target domain is {target_str}"))
            .add_info(source.span, format!("source domain is {source_str}"))
            .add_footer_info(format!("crossing due to {required_reason}"))
            .add_footer_hint(format!(
                "to intentionally cross domains, use `{}` or `unsafe_bool_to_clock`",
                TOKEN_STR_UNSAFE_VALUE_WITH_DOMAIN
            ))
            .report(diags)
        })
    }
}

#[derive(Debug, Copy, Clone)]
pub enum TypeContainsReason {
    Assignment {
        span_target: Span,
        span_target_ty: Span,
    },
    SpreadOperator(Span),
    Operator(Span),
    InstanceModule(Span),
    InstancePortInput {
        span_connection_port_id: Span,
        span_port_ty: Span,
    },
    InstancePortOutput {
        span_target: Span,
        span_target_ty: Span,
        span_port_ty: Span,
    },
    Return {
        span_keyword: Span,
        span_return_ty: Span,
    },
    ForIndexType(Span),
    IfCondition(Span),
    MatchPattern(Span),
    WhileCondition(Span),
    ArrayLen {
        span_len: Span,
    },
    Parameter {
        param_ty: Span,
    },
    Internal(Span),
}

impl TypeContainsReason {
    pub fn add_diag_info(self, refs: CompileRefs, diag: DiagnosticError, target_ty: &Type) -> DiagnosticError {
        let target_ty_str = target_ty.value_string(refs);
        match self {
            // TODO improve assignment error message
            TypeContainsReason::Assignment {
                span_target,
                span_target_ty,
            } => diag
                .add_info(span_target, format!("target requires type `{target_ty_str}`"))
                .add_info(span_target_ty, "target type set here"),
            TypeContainsReason::SpreadOperator(span) => diag.add_info(span, "spread operator requires an array"),
            TypeContainsReason::Operator(span) => {
                diag.add_info(span, format!("operator requires type `{target_ty_str}`"))
            }
            TypeContainsReason::InstanceModule(span) => {
                diag.add_info(span, format!("module instance requires type `{target_ty_str}`"))
            }
            TypeContainsReason::InstancePortInput {
                span_connection_port_id,
                span_port_ty,
            } => diag
                .add_info(
                    span_connection_port_id,
                    format!("input port has type `{target_ty_str}`"),
                )
                .add_info(span_port_ty, "input port type set here"),
            TypeContainsReason::InstancePortOutput {
                span_target,
                span_target_ty,
                span_port_ty,
            } => diag
                .add_info(span_target, format!("target has type `{target_ty_str}`"))
                .add_info(span_target_ty, "target type set here")
                .add_info(span_port_ty, "output port type set here"),
            TypeContainsReason::Return {
                span_keyword,
                span_return_ty,
            } => diag
                .add_info(span_keyword, format!("return requires type `{target_ty_str}`"))
                .add_info(span_return_ty, format!("return type `{target_ty_str}` set here")),
            TypeContainsReason::ForIndexType(span_ty) => diag.add_info(
                span_ty,
                format!("for loop iteration variable type `{target_ty_str}` set here"),
            ),
            TypeContainsReason::IfCondition(span) => {
                diag.add_info(span, format!("if condition requires type `{target_ty_str}`"))
            }
            TypeContainsReason::MatchPattern(span) => {
                diag.add_info(span, format!("match pattern against value with type `{target_ty_str}`"))
            }
            TypeContainsReason::WhileCondition(span) => {
                diag.add_info(span, format!("while condition requires type `{target_ty_str}`"))
            }
            TypeContainsReason::ArrayLen { span_len } => {
                diag.add_info(span_len, format!("array length requires type `{target_ty_str}`"))
            }
            TypeContainsReason::Parameter { param_ty } => {
                diag.add_info(param_ty, format!("parameter requires type `{target_ty_str}`"))
            }
            TypeContainsReason::Internal(span) => DiagnosticError::new_internal_compiler_error(
                "type check failed, should have been checked already",
                span,
            ),
        }
    }
}

pub fn check_type_contains_value<V: Typed + Debug>(
    refs: CompileRefs,
    reason: TypeContainsReason,
    target_ty: &Type,
    value: Spanned<&V>,
) -> DiagResult {
    // TODO if constant value, use value in message?
    let value_ty = value.map_inner(|v| v.ty());
    check_type_contains_type(refs, reason, target_ty, value_ty.as_ref())
}

pub fn check_type_contains_type(
    refs: CompileRefs,
    reason: TypeContainsReason,
    target_ty: &Type,
    value_ty: Spanned<&Type>,
) -> DiagResult {
    let diags = refs.diags;
    if target_ty.contains_type(value_ty.inner) {
        Ok(())
    } else {
        // TODO simpler error message for very simply values, eg. ints, bools, short tuples/arrays
        // TODO for assignments, error should point at the assignment operator, not the value
        let mut diag = DiagnosticError::new(
            "type mismatch",
            value_ty.span,
            format!(
                "source value with type `{}` does not fit",
                value_ty.inner.value_string(refs)
            ),
        );
        diag = reason.add_diag_info(refs, diag, target_ty);
        Err(diag.report(diags))
    }
}

pub fn check_type_is_int(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<Value>,
) -> DiagResult<MaybeCompile<BigInt, HardwareInt>> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::Int(MultiRange::open()), value.as_ref())?;

    let err = || diags.report_error_internal(value.span, "unexpected value kind for int type");
    match value.inner {
        Value::Simple(v) => match v {
            SimpleCompileValue::Int(v) => Ok(MaybeCompile::Compile(v)),
            _ => Err(err()),
        },
        Value::Hardware(v) => match v.ty {
            HardwareType::Int(ty) => Ok(MaybeCompile::Hardware(HardwareValue {
                ty,
                domain: v.domain,
                expr: v.expr,
            })),
            _ => Err(err()),
        },
        Value::Compound(_) => Err(err()),
    }
}

pub fn check_type_is_uint(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<Value>,
) -> DiagResult<MaybeCompile<BigUint, HardwareUInt>> {
    let diags = refs.diags;
    let ty_uint = Type::Int(MultiRange::from(Range {
        start: Some(BigInt::ZERO),
        end: None,
    }));
    check_type_contains_value(refs, reason, &ty_uint, value.as_ref())?;

    let err = || diags.report_error_internal(value.span, "unexpected value kind for uint type");
    match value.inner {
        Value::Simple(v) => match v {
            SimpleCompileValue::Int(v) => Ok(MaybeCompile::Compile(BigUint::try_from(v).unwrap())),
            _ => Err(err()),
        },
        Value::Hardware(v) => match v.ty {
            HardwareType::Int(ty) => Ok(MaybeCompile::Hardware(HardwareValue {
                ty: ty.map(|x| BigUint::try_from(x).unwrap()),
                domain: v.domain,
                expr: v.expr,
            })),
            _ => Err(err()),
        },
        Value::Compound(_) => Err(err()),
    }
}

pub fn check_type_is_int_hardware(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<HardwareValue>,
) -> DiagResult<HardwareInt> {
    let diags = refs.diags;
    let value_ty = value.as_ref().map_inner(|value| value.ty.as_type());
    check_type_contains_type(refs, reason, &Type::Int(MultiRange::open()), value_ty.as_ref())?;

    match value.inner.ty {
        HardwareType::Int(ty) => Ok(HardwareValue {
            ty,
            domain: value.inner.domain,
            expr: value.inner.expr,
        }),
        _ => Err(diags.report_error_internal(value.span, "expected int type")),
    }
}

pub fn check_type_is_uint_compile(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<CompileValue>,
) -> DiagResult<BigUint> {
    let diags = refs.diags;
    let ty_uint = Type::Int(MultiRange::from(Range {
        start: Some(BigInt::ZERO),
        end: None,
    }));
    check_type_contains_value(refs, reason, &ty_uint, value.as_ref())?;

    let err = || diags.report_error_internal(value.span, "expected uint value");
    match value.inner {
        CompileValue::Simple(v) => match v {
            SimpleCompileValue::Int(v) => Ok(BigUint::try_from(v).unwrap()),
            _ => Err(err()),
        },
        CompileValue::Compound(_) => Err(err()),
        CompileValue::Hardware(never) => never.unreachable(),
    }
}

pub fn check_type_is_bool(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<ValueWithImplications>,
) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::Bool, value.as_ref())?;

    let err = || diags.report_error_internal(value.span, "unexpected value kind for bool type");
    match value.inner {
        Value::Simple(v) => match v {
            SimpleCompileValue::Bool(v) => Ok(MaybeCompile::Compile(v)),
            _ => Err(err()),
        },
        Value::Compound(_) => Err(err()),
        Value::Hardware(v) => match v.value.ty {
            HardwareType::Bool => Ok(MaybeCompile::Hardware(v.map_type(|_| TypeBool))),
            _ => Err(diags.report_error_internal(value.span, "expected bool type")),
        },
    }
}

pub fn check_type_is_bool_compile(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<CompileValue>,
) -> DiagResult<bool> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::Bool, value.as_ref())?;

    let err = || diags.report_error_internal(value.span, "expected bool value");
    match value.inner {
        CompileValue::Simple(v) => match v {
            SimpleCompileValue::Bool(v) => Ok(v),
            _ => Err(err()),
        },
        CompileValue::Compound(_) => Err(err()),
        CompileValue::Hardware(never) => never.unreachable(),
    }
}

pub fn check_type_is_bool_array(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<Value>,
    expected_len: Option<BigUint>,
) -> DiagResult<MaybeCompile<Vec<bool>, HardwareValue<BigUint>>> {
    let diags = refs.diags;
    let expected_ty = Type::Array(Arc::new(Type::Bool), expected_len);
    check_type_contains_value(refs, reason, &expected_ty, value.as_ref())?;

    let err_internal = || diags.report_error_internal(value.span, "expected bool array");
    match value.inner {
        Value::Simple(v) => match v {
            SimpleCompileValue::Array(v) => {
                let result = v
                    .iter()
                    .map(|e| match e {
                        &Value::Simple(SimpleCompileValue::Bool(b)) => Ok(b),
                        _ => Err(err_internal()),
                    })
                    .try_collect_vec()?;
                Ok(MaybeCompile::Compile(result))
            }
            _ => Err(err_internal()),
        },
        Value::Hardware(c) => {
            let len = match c.ty {
                HardwareType::Array(_, len) => len,
                _ => return Err(err_internal()),
            };
            Ok(MaybeCompile::Hardware(HardwareValue {
                ty: len,
                domain: c.domain,
                expr: c.expr,
            }))
        }
        Value::Compound(_) => Err(err_internal()),
    }
}

pub fn check_type_is_string(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<Value>,
) -> DiagResult<Arc<MixedString>> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::String, value.as_ref())?;

    match value.inner {
        Value::Compound(MixedCompoundValue::String(v)) => Ok(v),
        _ => Err(diags.report_error_internal(value.span, "expected string value")),
    }
}

pub fn check_type_is_string_compile(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<CompileValue>,
) -> DiagResult<Arc<String>> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::String, value.as_ref())?;

    match value.inner {
        Value::Compound(CompileCompoundValue::String(v)) => Ok(v),
        _ => Err(diags.report_error_internal(value.span, "expected string value")),
    }
}

pub fn check_hardware_type_for_bit_operation(refs: CompileRefs, ty: Spanned<&Type>) -> DiagResult<HardwareType> {
    let diags = refs.diags;
    let shared = &refs.shared;
    ty.inner.as_hardware_type(&shared.elaboration_arenas).map_err(|_| {
        let ty_str = ty.inner.value_string(refs);
        DiagnosticError::new(
            "converting to/from bits is only possible for hardware types",
            ty.span,
            format!("actual type `{}`", ty_str),
        )
        .report(diags)
    })
}

pub fn check_type_is_range(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<Value>,
) -> DiagResult<RangeValue> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::Range, value.as_ref())?;

    match value.inner {
        Value::Compound(MixedCompoundValue::Range(range)) => Ok(range),
        _ => Err(diags.report_error_internal(value.span, "expected range value")),
    }
}

pub fn check_type_is_range_compile(
    refs: CompileRefs,
    reason: TypeContainsReason,
    value: Spanned<CompileValue>,
) -> DiagResult<MultiRange<BigInt>> {
    let diags = refs.diags;
    check_type_contains_value(refs, reason, &Type::Range, value.as_ref())?;

    match value.inner {
        CompileValue::Compound(CompileCompoundValue::Range(range)) => Ok(range),
        CompileValue::Compound(_) | CompileValue::Simple(_) => {
            Err(diags.report_error_internal(value.span, "expected range value"))
        }
        CompileValue::Hardware(never) => never.unreachable(),
    }
}

pub fn check_port_is_output(
    diags: &Diagnostics,
    port_info: &PortInfo,
    span: Span,
    title: &str,
    msg: &str,
) -> DiagResult {
    match port_info.direction.inner {
        PortDirection::Input => {
            let diag = DiagnosticError::new(title, span, msg)
                .add_info(port_info.span, "port declared here")
                .add_info(port_info.direction.span, "port direction set here")
                .report(diags);
            Err(diag)
        }
        PortDirection::Output => Ok(()),
    }
}

pub fn check_range_is_compile_for_member(
    refs: CompileRefs,
    member_span: Span,
    value: Spanned<Value>,
) -> DiagResult<MultiRange<BigInt>> {
    let diags = refs.diags;
    let range_span = value.span;

    let range = check_type_is_range(refs, TypeContainsReason::Operator(member_span), value)?;
    match range {
        RangeValue::Compile(range) => Ok(range),
        RangeValue::HardwareBounds(_) | RangeValue::HardwareStartLength { start: _, length: _ } => {
            let diag = DiagnosticError::new(
                "range attributes and methods require compile-time ranges",
                range_span,
                "range with hardware bounds here",
            )
            .add_info(member_span, "for attribute or method here")
            .report(diags);
            Err(diag)
        }
    }
}
