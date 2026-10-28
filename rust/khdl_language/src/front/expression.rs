use crate::front::assignment::AssignmentTarget;
use crate::front::check::{
    TypeContainsReason, check_type_contains_value, check_type_is_bool, check_type_is_bool_array, check_type_is_int,
    check_type_is_range, check_type_is_string_compile, check_type_is_uint, check_type_is_uint_compile,
};
use crate::front::compile::{CompileItemContext, CompileRefs, StackEntry};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::{DomainSignal, ValueDomain};
use crate::front::flow::ValueVersion;
use crate::front::function::{AstArgs, CallArgs, Param, require_compile_arg};
use crate::front::implication::{BoolImplications, HardwareValueWithImplications, Implication, ValueWithImplications};
use crate::front::item::{ElaboratedInterface, ElaboratedInterfaceView, ElaboratedModule};
use crate::front::scope::{CapturedValue, NamedValue, Scope, ScopeKey, ScopedEntry};
use crate::front::signal::{Interface, Polarized, Port, Signal, SignalOrVariable};
use crate::front::steps::{
    SliceInfo, SpannedStep, TargetStep, TargetStepCompile, TargetStepHardware, TargetSteps, check_range_index_compile,
    check_range_slice_compile,
};
use crate::front::types::{HardwareType, NonHardwareType, Type, TypeBool, Typed};
use crate::front::value::{
    BoundMethod, CompileCompoundValue, CompileValue, HardwareInt, HardwareUInt, HardwareValue, MaybeCompile,
    MixedCompoundValue, NotCompile, RangeValue, ReferenceInner, ReferenceWrapper, SimpleCompileValue, Value,
    ValueCommon,
};
use crate::mid::ir::{
    IrArrayLiteralElement, IrBoolBinaryOp, IrBoolCompareOp, IrExpression, IrExpressionLarge, IrIntArithmeticOp,
    IrIntCompareOp, IrLargeArena, IrType,
};
use crate::syntax::ast::{
    Args, ArrayComprehension, ArrayLiteralElement, BinaryOp, BlockExpression, DomainKind, DotIndexKind, Expression,
    ExpressionKind, Identifier, IntLiteral, MaybeIdentifier, RangeLiteral, SimpleIdentifier, SyncDomain, UnaryOp,
};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::big_int::{AnyInt, BigInt, BigUint, IsZero};
use crate::util::data::{VecExt, vec_concat};
use std::collections::VecDeque;

use crate::front::exit::ExitStack;
use crate::front::extra::{ExtraCursor, ExtraScope};
use crate::front::flow::Flow;
use crate::front::range_arithmetic::{
    multi_range_binary_add, multi_range_binary_bitwise, multi_range_binary_div_ceil, multi_range_binary_div_floor,
    multi_range_binary_mod, multi_range_binary_mul, multi_range_binary_pow, multi_range_binary_sub,
    multi_range_unary_bitwise_not, multi_range_unary_neg,
};
use crate::mid::steps::{IrTargetStepScalar, IrTargetSteps};
use crate::syntax::token::{
    parse_token_int_literal_binary, parse_token_int_literal_decimal, parse_token_int_literal_hexadecimal,
};
use crate::util::ResultDoubleExt;
use crate::util::int::IntRepresentation;
use crate::util::intern::Id;
use crate::util::iter::IterExt;
use crate::util::nd_array::NdArray;
use crate::util::range::{ClosedNonEmptyRange, NonEmptyRange, Range, RangeEmpty, RangeOpen};
use crate::util::range_multi::{AnyMultiRange, ClosedNonEmptyMultiRange, MultiRange};
use itertools::{Either, zip_eq};
use std::sync::Arc;
use unwrap_match::unwrap_match;

#[derive(Debug)]
pub enum NamedOrValue {
    Named(NamedValue),
    Value(Value),
}

#[derive(Debug)]
pub enum LrValue {
    LeftTarget(AssignmentTarget),
    LeftInterface(LeftInterfaceInfo),
    Right(ValueWithImplications),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct LeftInterfaceInfo {
    pub span_id: Span,
    /// The interface.
    pub elab: Spanned<ElaboratedInterface>,
    /// The view, only set if this is a port.
    pub port_view: Option<Spanned<ElaboratedInterfaceView>>,

    /// The actual interface instances.
    pub intf: NdArray<Interface>,
}

impl LrValue {
    pub fn from_named(span: Span, named: NamedValue) -> LrValue {
        match named {
            NamedValue::Variable(var) => LrValue::LeftTarget(AssignmentTarget::simple(Spanned::new(span, var.into()))),
            NamedValue::Signal(sig) => LrValue::LeftTarget(AssignmentTarget::simple(Spanned::new(span, sig.into()))),
            NamedValue::Interface(intf) => LrValue::LeftInterface(intf),
        }
    }

    /// Evaluate as a value.
    pub fn read_value(
        self,
        ctx: &mut CompileItemContext,
        flow: &mut impl Flow,
        span: Span,
    ) -> DiagResult<ValueWithImplications> {
        let refs = ctx.refs;
        let diags = refs.diags;

        match self {
            LrValue::LeftTarget(v) => {
                // eval base
                let AssignmentTarget { base, steps } = v;
                flow.signal_or_var_eval(ctx, base, &steps)
            }
            LrValue::LeftInterface(info) => {
                let e = if info.intf.as_single().is_some() {
                    DiagnosticError::new("cannot evaluate interface as value", span, "evaluating interface here")
                        .add_info(info.span_id, "interface declared here")
                        .add_footer_hint("to access individual signals, use dot indexing: `<intf>.<signal>`")
                        .add_footer_hint("to get a reference to the whole interface, use `ref(<intf>)`")
                } else {
                    DiagnosticError::new(
                        "cannot evaluate interface array as value",
                        span,
                        "evaluating interface array here",
                    )
                    .add_info(info.span_id, "interface array declared here")
                    .add_footer_hint("to access individual interfaces, use array indexing: `<array>[<index>]`")
                };
                Err(e.report(diags))
            }
            LrValue::Right(v) => Ok(v),
        }
    }

    /// Evaluate as an assignment target.
    pub fn into_target(self, ctx: &mut CompileItemContext, span: Span) -> DiagResult<AssignmentTarget> {
        let diags = ctx.refs.diags;

        match self {
            LrValue::LeftTarget(t) => Ok(t),
            LrValue::LeftInterface(info) => {
                let e = DiagnosticError::new("cannot use interface as target", span, "interface used as target here")
                    .add_info(info.span_id, "interface declared here")
                    .report(diags);
                Err(e)
            }
            LrValue::Right(_) => {
                Err(diags.report_error_simple("cannot use value as target", span, "value used as target here"))
            }
        }
    }
}

impl<'a> CompileItemContext<'a, '_> {
    pub fn eval_simple_id(&self, id: SimpleIdentifier) -> Spanned<Id> {
        let span = id.span;
        let s = id.str(self.refs.fixed.source);
        let id = self.refs.shared.interner.push(s);
        Spanned::new(span, id)
    }

    pub fn eval_id(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        id: impl Into<Identifier>,
    ) -> DiagResult<Spanned<Id>> {
        let refs = self.refs;

        let id = id.into();

        match id {
            Identifier::Simple(id) => Ok(self.eval_simple_id(id)),
            Identifier::FromString(span, expr) => {
                let value =
                    self.eval_expression_as_compile(scope, flow, &Type::String, expr, Spanned::new(span, "id string"))?;
                let value = check_type_is_string_compile(refs, TypeContainsReason::Operator(span), value)?;
                let id = self.refs.shared.interner.push(&value);
                Ok(Spanned::new(span, id))
            }
        }
    }

    pub fn eval_maybe_id(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        id: MaybeIdentifier<Identifier>,
    ) -> DiagResult<MaybeIdentifier<Spanned<Id>>> {
        id.map_id(|id| self.eval_id(scope, flow, id)).transpose()
    }

    pub fn eval_scoped_as_lr(
        &mut self,
        scope: &Scope,
        key: impl Into<ScopeKey<Spanned<Id>, Span>>,
    ) -> DiagResult<LrValue> {
        let key = key.into();
        let key_span = key.span();

        let named = self.eval_scoped_as_named(scope, key)?;
        let result = match named {
            NamedOrValue::Named(named_inner) => LrValue::from_named(key_span, named_inner),
            NamedOrValue::Value(value) => LrValue::Right(ValueWithImplications::simple(value)),
        };
        Ok(result)
    }

    pub fn eval_scoped_as_named(
        &mut self,
        scope: &Scope,
        key: impl Into<ScopeKey<Spanned<Id>, Span>>,
    ) -> DiagResult<NamedOrValue> {
        let refs = self.refs;
        let diags = refs.diags;

        let key = key.into();
        let key_span = key.span();

        let found = scope.find(refs, key)?;

        let result = match found.value {
            ScopedEntry::Named(value) => NamedOrValue::Named(value),
            ScopedEntry::Item(item) => {
                let entry = StackEntry::ItemUsage(key.span());
                let value = self.recurse(entry, |s| Ok(s.eval_item(item)?.clone())).flatten_err()?;
                NamedOrValue::Value(Value::from(value))
            }
            ScopedEntry::Captured(value) => {
                let CapturedValue { span_capture, value } = value;
                match value {
                    Ok(value) => NamedOrValue::Value(Value::from(Arc::unwrap_or_clone(value))),
                    Err(e) => return Err(e.to_diag_error(found.span_decl, span_capture, key_span).report(diags)),
                }
            }
            ScopedEntry::Value(value) => NamedOrValue::Value(value),
        };
        Ok(result)
    }

    pub fn eval_expression(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr: Expression,
    ) -> DiagResult<Spanned<Value>> {
        Ok(self
            .eval_expression_with_implications(scope, flow, expected_ty, expr)?
            .map_inner(ValueWithImplications::into_value))
    }

    pub fn eval_expression_with_implications(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr: Expression,
    ) -> DiagResult<Spanned<ValueWithImplications>> {
        let value = self
            .eval_expression_as_lr(scope, flow, expected_ty, expr)?
            .read_value(self, flow, expr.span)?;
        Ok(Spanned::new(expr.span, value))
    }

    pub fn eval_expression_as_assign_target(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr: Expression,
    ) -> DiagResult<AssignmentTarget> {
        self.eval_expression_as_lr(scope, flow, &Type::Any, expr)?
            .into_target(self, expr.span)
    }

    pub fn eval_expression_as_lr(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr: Expression,
    ) -> DiagResult<LrValue> {
        let refs = self.refs;
        let diags = refs.diags;
        let source = refs.fixed.source;
        let elab = &refs.shared.elaboration_arenas;

        let result: LrValue = match refs.get_expr(expr) {
            &ExpressionKind::ParseError(_) => {
                return Err(diags.report_error_internal(expr.span, "encountered parse error"));
            }
            ExpressionKind::Dummy => {
                // if dummy expressions were allowed, the caller would have checked for them already
                return Err(diags.report_error_simple(
                    "dummy expression not allowed in this context",
                    expr.span,
                    "dummy expression used here",
                ));
            }
            ExpressionKind::Undefined => {
                flow.require_hardware(expr.span, "undefined expression")?;

                let expected_ty_hw = expected_ty.as_hardware_type(elab).map_err(|_: NonHardwareType| {
                    diags.report_error_simple(
                        "undefined expression requires hardware type",
                        expr.span,
                        format!("inferred type is `{}`", expected_ty.value_string(refs)),
                    )
                })?;

                let result = self
                    .large
                    .push_expr(IrExpressionLarge::Undefined(expected_ty_hw.as_ir(refs)));
                let result = HardwareValue {
                    ty: expected_ty_hw,
                    domain: ValueDomain::CompileTime,
                    expr: result,
                };
                LrValue::Right(ValueWithImplications::simple(Value::Hardware(result)))
            }
            ExpressionKind::Type => LrValue::Right(Value::new_ty(Type::Type)),
            ExpressionKind::Slf => self.eval_scoped_as_lr(scope, ScopeKey::Slf(expr.span))?,
            &ExpressionKind::Builtin { span_keyword, ref args } => {
                let result = self.eval_builtin(scope, flow, expr.span, span_keyword, args)?;
                LrValue::Right(ValueWithImplications::simple(result))
            }
            &ExpressionKind::Wrapped(operand) => {
                // intentionally discard LR-state, force evaluation
                let result = self.eval_expression_with_implications(scope, flow, expected_ty, operand)?;
                LrValue::Right(result.inner)
            }
            ExpressionKind::Block(block_expr) => {
                let &BlockExpression {
                    ref statements,
                    expression,
                } = block_expr;

                // run statements in new block scope
                let mut scope_inner = scope.new_child(expr.span);
                let mut stack = ExitStack::new_in_block_expression(expr.span);
                let end = self.elaborate_block_statements(&mut scope_inner, flow, &mut stack, statements)?;
                end.unwrap_normal(diags, expr.span)?;

                // intentionally discard LR-state, force evaluation
                let result = self.eval_expression_with_implications(&scope_inner, flow, expected_ty, expression)?;
                LrValue::Right(result.inner)
            }
            &ExpressionKind::Id(id) => {
                let id = self.eval_id(scope, flow, id)?;
                self.eval_scoped_as_lr(scope, id)?
            }
            ExpressionKind::IntLiteral(pattern) => {
                let parsed = match *pattern {
                    IntLiteral::Binary { span } => parse_token_int_literal_binary(source.span_str(span)),
                    IntLiteral::Decimal { span } => parse_token_int_literal_decimal(source.span_str(span)),
                    IntLiteral::Hexadecimal { span } => parse_token_int_literal_hexadecimal(source.span_str(span)),
                };
                let value = parsed.map_err(|_| diags.report_error_internal(expr.span, "failed to parse int"))?;

                let value = Value::new_int(BigInt::from(value));
                LrValue::Right(ValueWithImplications::simple(value))
            }
            &ExpressionKind::BoolLiteral(literal) => LrValue::Right(Value::new_bool(literal)),
            ExpressionKind::StringLiteral(pieces) => {
                let result = self.eval_string_literal(scope, flow, pieces)?;
                LrValue::Right(ValueWithImplications::simple(result))
            }
            ExpressionKind::ArrayLiteral(elements) => {
                let result = self.eval_array_literal(scope, flow, expected_ty, expr.span, elements)?;
                LrValue::Right(ValueWithImplications::simple(result))
            }
            ExpressionKind::TupleLiteral(elements) => {
                let result = self.eval_tuple_literal(scope, flow, expected_ty, elements)?;
                LrValue::Right(ValueWithImplications::simple(result))
            }
            &ExpressionKind::RangeLiteral(literal) => {
                let mut eval_bound = |bound: Expression, op_span: Span| {
                    let bound_span = bound.span;
                    let bound = self.eval_expression(scope, flow, &Type::Int(MultiRange::open()), bound)?;

                    let reason = TypeContainsReason::Operator(op_span);
                    let bound = check_type_is_int(refs, reason, bound)?;

                    Ok(Spanned::new(bound_span, bound))
                };

                let result = match literal {
                    RangeLiteral::ExclusiveEnd {
                        op_span,
                        ref start,
                        ref end,
                    } => {
                        let start = start.map(|start| eval_bound(start, op_span)).transpose();
                        let end = end.map(|end| eval_bound(end, op_span)).transpose();

                        let start = start?;
                        let end = end?;

                        // check validness
                        if let (Some(start), Some(end)) = (&start, &end) {
                            let start_range = start.inner.range();
                            let end_range = end.inner.range();

                            #[allow(clippy::nonminimal_bool)]
                            if !(start_range.enclosing_range().end - 1 <= *end_range.enclosing_range().start) {
                                let msg_start = message_range_or_single("start", &start_range, None);
                                let msg_end = message_range_or_single("end", &end_range, None);
                                let diag = DiagnosticError::new(
                                    "invalid range: open range requires that `start <= end`",
                                    op_span,
                                    "range constructed here",
                                )
                                .add_info(start.span, msg_start)
                                .add_info(end.span, msg_end)
                                .add_footer_hint(HINT_RANGE_USE_START_LENGTH)
                                .report(diags);
                                return Err(diag);
                            }
                        }

                        let start = start.map(|s| s.inner);
                        let end = end.map(|e| e.inner);
                        RangeValue::Normal(Range { start, end })
                    }
                    RangeLiteral::InclusiveEnd {
                        op_span,
                        start,
                        end_inc,
                    } => {
                        // eval bounds
                        let start = start.map(|start| eval_bound(start, op_span)).transpose();
                        let end_inc = eval_bound(end_inc, op_span);

                        let start = start?;
                        let end_inc = end_inc?;

                        // check validness
                        if let Some(start) = &start {
                            let start_range = start.inner.range();
                            let end_inc_range = end_inc.inner.range();

                            #[allow(clippy::nonminimal_bool)]
                            if !(start_range.enclosing_range().end - 1 <= end_inc_range.enclosing_range().start + 1) {
                                let msg_start = message_range_or_single("start", &start_range, None);
                                let msg_end = message_range_or_single("end", &end_inc_range, None);
                                let diag = DiagnosticError::new(
                                    "invalid range: closed range requires that `start <= end_inc + 1`",
                                    op_span,
                                    "inclusive range constructed here",
                                )
                                .add_info(start.span, msg_start)
                                .add_info(end_inc.span, msg_end)
                                .add_footer_hint(HINT_RANGE_USE_START_LENGTH)
                                .report(diags);
                                return Err(diag);
                            }
                        }

                        // map end to exclusive
                        let end = match end_inc.inner {
                            MaybeCompile::Compile(end_inc) => MaybeCompile::Compile(end_inc + 1),
                            MaybeCompile::Hardware(end_inc) => {
                                let end_range = end_inc.ty.map(|x| x + 1);

                                let end_expr = IrExpressionLarge::IntArithmetic(
                                    IrIntArithmeticOp::Add,
                                    end_range.enclosing_range().cloned(),
                                    end_inc.expr,
                                    IrExpression::Int(BigInt::ONE),
                                );
                                MaybeCompile::Hardware(HardwareInt {
                                    ty: end_range,
                                    domain: end_inc.domain,
                                    expr: self.large.push_expr(end_expr),
                                })
                            }
                        };

                        let start = start.map(|s| s.inner);
                        RangeValue::Normal(Range { start, end: Some(end) })
                    }
                    RangeLiteral::Length { op_span, start, length } => {
                        let start = eval_bound(start, op_span);

                        let range_uint = MultiRange::from(Range {
                            start: Some(BigInt::ZERO),
                            end: None,
                        });
                        let length = self
                            .eval_expression(scope, flow, &Type::Int(range_uint), length)
                            .and_then(|length| {
                                let reason = TypeContainsReason::Operator(op_span);
                                check_type_is_uint(refs, reason, length)
                            });

                        let start = start?;
                        let length = length?;

                        match (start.inner, length) {
                            (MaybeCompile::Hardware(start), MaybeCompile::Compile(length)) => {
                                // preserve full information to allow for hardware slicing
                                RangeValue::HardwareStartLength { start, length }
                            }
                            (start, length) => {
                                // decay to normal range by calculating `end = start + length`
                                let length = match length {
                                    MaybeCompile::Compile(length) => MaybeCompile::Compile(BigInt::from(length)),
                                    MaybeCompile::Hardware(length) => MaybeCompile::Hardware(HardwareInt {
                                        ty: length.ty.map(BigInt::from),
                                        domain: length.domain,
                                        expr: length.expr,
                                    }),
                                };
                                let end = match pair_compile_int(start.clone(), length) {
                                    MaybeCompile::Compile((start, length)) => MaybeCompile::Compile(start + length),
                                    MaybeCompile::Hardware((start, length)) => {
                                        let range = multi_range_binary_add(&start.ty, &length.ty);
                                        let result = build_binary_int_arithmetic_op(
                                            IrIntArithmeticOp::Add,
                                            &mut self.large,
                                            range,
                                            start,
                                            length,
                                        );
                                        MaybeCompile::Hardware(result)
                                    }
                                };

                                // length is unsigned, so end >= start always holds
                                RangeValue::Normal(Range {
                                    start: Some(start),
                                    end: Some(end),
                                })
                            }
                        }
                    }
                };

                let result = Value::Compound(MixedCompoundValue::Range(result));
                LrValue::Right(ValueWithImplications::simple(result))
            }
            ExpressionKind::ArrayComprehension(array_comprehension) => {
                let &ArrayComprehension {
                    body,
                    index,
                    span_keyword,
                    iter,
                } = array_comprehension;

                let expected_ty_inner = match expected_ty {
                    Type::Array(inner, _) => inner,
                    _ => &Type::Any,
                };

                // evaluate operands
                let index = self.eval_maybe_id(scope, flow, index)?;

                let iter_span = iter.span;
                let iter = self.eval_expression_as_for_iterator(scope, flow, iter)?;

                // this is only a lower bound,
                //   there might be spread elements in the literal which expand to multiple values
                let len_lower_bound = match iter.len() {
                    None => {
                        return Err(diags.report_error_simple(
                            "array comprehension over infinite iterator would never finish",
                            iter_span,
                            "this iterator is infinite",
                        ));
                    }
                    Some(len) => usize::try_from(len).unwrap_or(usize::MAX),
                };

                let mut values = try_vec_with_capacity(diags, expr.span, len_lower_bound)?;

                for index_value in iter {
                    self.refs.check_should_stop(expr.span)?;

                    let index_value = index_value.map_hardware(|h| h.map_expression(|h| h.into_expr(&mut self.large)));
                    let index_var =
                        flow.var_new_immutable_init(refs, index, span_keyword, Ok(Value::simple(index_value)))?;

                    let scope_span = body.span().join(index.span());
                    let mut scope_body = scope.new_child(scope_span);
                    scope_body.declare(refs, index, Ok(ScopedEntry::Named(NamedValue::Variable(index_var))));

                    let value = body
                        .map_inner(|body_expr| self.eval_expression(&scope_body, flow, expected_ty_inner, body_expr))
                        .transpose()?;
                    values.push(value);
                }

                let result = array_literal_combine_values(refs, flow, &mut self.large, expr.span, values)?;
                LrValue::Right(ValueWithImplications::simple(result))
            }

            &ExpressionKind::UnaryOp(op, operand) => match op.inner {
                UnaryOp::Plus => {
                    let operand = self.eval_expression_with_implications(scope, flow, &Type::Any, operand)?;
                    let _ = check_type_is_int(
                        refs,
                        TypeContainsReason::Operator(op.span),
                        operand.clone().map_inner(ValueWithImplications::into_value),
                    )?;
                    LrValue::Right(operand.inner)
                }
                UnaryOp::Neg => {
                    let operand = self.eval_expression(scope, flow, &Type::Any, operand)?;
                    let operand_int = check_type_is_int(refs, TypeContainsReason::Operator(op.span), operand)?;

                    let result = match operand_int {
                        MaybeCompile::Compile(c) => Value::new_int(-c),
                        MaybeCompile::Hardware(v) => {
                            Value::Hardware(HardwareValue::from(build_unary_int_neg(&mut self.large, v)))
                        }
                    };
                    LrValue::Right(ValueWithImplications::simple(result))
                }
                UnaryOp::Not => {
                    let operand = self.eval_expression_with_implications(scope, flow, &Type::Any, operand)?;
                    LrValue::Right(eval_unary_not(refs, &mut self.large, op.span, operand)?)
                }
            },
            &ExpressionKind::BinaryOp(op, left, right) => {
                let left = self.eval_expression_with_implications(scope, flow, &Type::Any, left);
                let right = self.eval_expression_with_implications(scope, flow, &Type::Any, right);
                let result = eval_binary_expression(refs, &mut self.large, expr.span, op, left?, right?)?;
                LrValue::Right(result)
            }
            &ExpressionKind::ArrayType {
                span_brackets: _,
                ref lengths,
                element,
            } => {
                // TODO support nd arrays
                // evaluate length
                let length = lengths
                    .single_ref()
                    .ok_or_else(|| diags.report_error_todo(expr.span, "multidimensional arrays"))?;
                let length = match length {
                    &ArrayLiteralElement::Single(length) => length,
                    ArrayLiteralElement::Spread(_, _) => {
                        return Err(diags.report_error_todo(length.span(), "multidimensional arrays"));
                    }
                };

                let length = match refs.get_expr(length) {
                    ExpressionKind::Dummy => None,
                    _ => {
                        let ty_uint = Type::Int(MultiRange::from(Range {
                            start: Some(BigInt::ZERO),
                            end: None,
                        }));
                        let length = self.eval_expression_as_compile(
                            scope,
                            flow,
                            &ty_uint,
                            length,
                            Spanned::new(expr.span, "array type length"),
                        )?;
                        let reason = TypeContainsReason::ArrayLen { span_len: length.span };
                        let length = check_type_is_uint_compile(refs, reason, length)?;
                        Some(length)
                    }
                };

                // eval inner type or interface view
                let inner = self.eval_expression_as_compile(
                    scope,
                    flow,
                    &Type::Any,
                    element,
                    Spanned::new(expr.span, "array type element"),
                )?;

                let length_for_interface = |length: Option<BigUint>| {
                    length.ok_or_else(|| {
                        diags.report_error_simple(
                            "interface arrays must have a known length",
                            expr.span,
                            "missing length here",
                        )
                    })
                };
                let prepend_length = |length: BigUint, mut prev_lengths: Vec<BigUint>| {
                    prev_lengths.insert(0, length);
                    prev_lengths
                };

                let result = match inner.inner {
                    // array type
                    CompileValue::Simple(SimpleCompileValue::Type(element_ty)) => {
                        Value::new_ty(Type::Array(Arc::new(element_ty), length))
                    }

                    // array interfaces and views
                    CompileValue::Simple(SimpleCompileValue::Interface(intf)) => {
                        let length = length_for_interface(length)?;
                        Value::Simple(SimpleCompileValue::InterfaceArray(vec![length], intf))
                    }
                    CompileValue::Simple(SimpleCompileValue::InterfaceArray(prev_lengths, intf)) => {
                        let lengths = prepend_length(length_for_interface(length)?, prev_lengths);
                        Value::Simple(SimpleCompileValue::InterfaceArray(lengths, intf))
                    }
                    CompileValue::Simple(SimpleCompileValue::InterfaceView(view)) => {
                        let length = length_for_interface(length)?;
                        Value::Simple(SimpleCompileValue::InterfaceViewArray(vec![length], view))
                    }
                    CompileValue::Simple(SimpleCompileValue::InterfaceViewArray(prev_lengths, view)) => {
                        let lengths = prepend_length(length_for_interface(length)?, prev_lengths);
                        Value::Simple(SimpleCompileValue::InterfaceViewArray(lengths, view))
                    }

                    // error, invalid element
                    value => {
                        let mut diag = DiagnosticError::new(
                            "array element must be a type, interface or interface view",
                            inner.span,
                            format!("got value with type `{}`", value.ty().value_string(refs)),
                        );
                        if let ExpressionKind::TupleLiteral(_) = refs.get_expr(element) {
                            diag = diag.add_footer_hint("tuple types are written `Tuple(...)`, not `(...)`")
                        }
                        return Err(diag.report(diags));
                    }
                };

                LrValue::Right(ValueWithImplications::simple(result))
            }
            &ExpressionKind::ArrayIndex {
                span_brackets: _,
                base,
                ref indices,
            } => {
                // eval base
                let base_span = base.span;
                let base = self.eval_expression_as_lr(scope, flow, &Type::Any, base)?;

                // TODO support nd arrays
                // evaluate index
                let index = indices
                    .single_ref()
                    .ok_or_else(|| diags.report_error_todo(expr.span, "multidimensional array indexing"))?;
                let index = match index {
                    &ArrayLiteralElement::Single(index) => index,
                    ArrayLiteralElement::Spread(_, _) => {
                        return Err(diags.report_error_todo(index.span(), "multidimensional array indexing"));
                    }
                };

                // apply step to value
                let step = self.eval_expression_as_array_step(scope, flow, index)?;
                let step = SpannedStep {
                    span_full: expr.span,
                    span_step: index.span,
                    step,
                };

                match base {
                    LrValue::LeftTarget(base) => {
                        let mut result = base;
                        result.steps.push(step);
                        LrValue::LeftTarget(result)
                    }
                    LrValue::LeftInterface(info) => {
                        let Some(array_len) = info.intf.first_len() else {
                            let e = DiagnosticError::new(
                                "cannot index into interface",
                                expr.span,
                                "trying to index into interface here",
                            )
                            .add_info(base_span, "base evaluates to an interface")
                            .add_info(info.span_id, "interface declared here")
                            .report(diags);
                            return Err(e);
                        };
                        let array_len = Spanned::new(base_span, array_len);

                        let intf = match step.step {
                            // index
                            TargetStep::Compile(TargetStepCompile::ArrayIndex(index)) => {
                                let index =
                                    check_range_index_compile(diags, Spanned::new(step.span_step, &index), array_len)?;
                                info.intf.step_index(index).expect("already checked range")
                            }
                            // slice
                            TargetStep::Compile(TargetStepCompile::ArraySlice { start, length }) => {
                                let SliceInfo { start, length } = check_range_slice_compile(
                                    diags,
                                    Spanned::new(step.span_step, &start),
                                    length.as_ref().map(|length| Spanned::new(step.span_step, length)),
                                    array_len,
                                )?;
                                info.intf.step_slice(start, length).expect("already checked range")
                            }
                            // hardware index/slice not yet supported
                            TargetStep::Hardware(TargetStepHardware::ArrayIndex(_)) => {
                                let msg = "indexing interface arrays with a hardware value";
                                return Err(diags.report_error_todo(step.span_step, msg));
                            }
                            TargetStep::Hardware(TargetStepHardware::ArraySlice { .. }) => {
                                let msg = "slicing interface arrays with a hardware start";
                                return Err(diags.report_error_todo(step.span_step, msg));
                            }
                            // impossible case
                            TargetStep::Compile(
                                TargetStepCompile::DotIndexInt(_) | TargetStepCompile::DotIndexId(_),
                            ) => {
                                let msg = "dot index step from array index expression";
                                return Err(diags.report_error_internal(step.span_step, msg));
                            }
                        };
                        LrValue::LeftInterface(LeftInterfaceInfo { intf, ..info })
                    }
                    LrValue::Right(base) => {
                        let steps = TargetSteps::single(step);
                        let result = steps.apply_to_value(self, expected_ty, Spanned::new(base_span, base))?;
                        LrValue::Right(result)
                    }
                }
            }
            &ExpressionKind::DotIndex(base, index) => {
                let base_span = base.span;
                let base = self.eval_expression_as_lr(scope, flow, &Type::Any, base)?;

                let index_span = index.span();
                let index = match index {
                    DotIndexKind::Id(index) => Either::Left(self.eval_id(scope, flow, index)?.inner),
                    DotIndexKind::Int { span } => Either::Right(
                        parse_token_int_literal_decimal(refs.fixed.source.span_str(span))
                            .map_err(|_| diags.report_error_internal(expr.span, "failed to parse int"))?,
                    ),
                };

                let index_to_step = |index: Either<Id, BigUint>| {
                    let step = match index {
                        Either::Left(index) => TargetStepCompile::DotIndexId(index),
                        Either::Right(index) => TargetStepCompile::DotIndexInt(index),
                    };
                    SpannedStep {
                        span_full: expr.span,
                        span_step: index_span,
                        step: TargetStep::Compile(step),
                    }
                };

                match base {
                    LrValue::LeftTarget(base) => {
                        let mut result = base;
                        result.steps.push(index_to_step(index));
                        LrValue::LeftTarget(result)
                    }
                    LrValue::LeftInterface(info) => {
                        let &base = info.intf.as_single().ok_or_else(|| {
                            DiagnosticError::new(
                                "cannot access signal of interface array",
                                index_span,
                                "attempt to access signal here",
                            )
                            .add_info(base_span, "base evaluates to an interface array")
                            .add_info(info.span_id, "interface array declared here")
                            .add_footer_hint("to access individual interfaces, use array indexing: `<array>[<index>]`")
                            .report(diags)
                        })?;
                        let index = index.left().ok_or_else(|| {
                            DiagnosticError::new(
                                "cannot tuple index into interface",
                                expr.span,
                                "trying to tuple index here",
                            )
                            .add_info(base_span, "base evaluates to an interface")
                            .add_info(info.span_id, "interface declared here")
                            .report(diags)
                        })?;

                        let signal = base.get_signal(self, base_span, Spanned::new(index_span, index))?;
                        LrValue::LeftTarget(AssignmentTarget::simple(Spanned::new(expr.span, signal.into())))
                    }
                    LrValue::Right(base) => {
                        let steps = TargetSteps::new(vec![index_to_step(index)]);
                        LrValue::Right(steps.apply_to_value(self, expected_ty, Spanned::new(base_span, base))?)
                    }
                }
            }
            &ExpressionKind::Call(target, ref args) => {
                // eval target
                let target = self.eval_expression(scope, flow, &Type::Any, target)?;

                // prepare args
                let &Args {
                    span: span_args,
                    items: ref items_args,
                } = args;
                let mut args_scope = scope.new_child(span_args);
                let args_scope = ExtraScope::new(None, &mut args_scope);
                let args_cursor = ExtraCursor::new(args_scope, items_args, false);
                let args = CallArgs::Ast(AstArgs {
                    span: span_args,
                    cursor: args_cursor,
                });

                // eval call
                let result = self.eval_call(flow, expected_ty, expr.span, target.as_ref(), args)?;

                LrValue::Right(ValueWithImplications::simple(result))
            }
            &ExpressionKind::UnsafeValueWithDomain(value, domain) => {
                // evaluate value
                let flow_hw = flow.require_hardware(expr.span, "domain cast")?;
                let value = {
                    // evaluate the value with disabled domain checks
                    // (the whole point of this operation is to bypass domain checking)
                    // TODO is this not accidentally disabling eg. writes to unrelated signals too?
                    let mut flow_hw_inner = flow_hw.new_child_scoped_without_domain_checks();
                    self.eval_expression(scope, &mut flow_hw_inner, expected_ty, value)?
                };

                // evaluate domain
                let domain = {
                    let mut flow_domain = flow.new_child_compile(domain.span, "domain");
                    self.eval_domain(scope, &mut flow_domain, domain)?
                };

                // convert value to hardware
                let ty = match value.inner.ty().as_hardware_type(elab) {
                    Ok(ty) => ty,
                    Err(NonHardwareType) => {
                        let diag = DiagnosticError::new(
                            "value must be representable in hardware for domain cast",
                            value.span,
                            format!("got non-hardware type `{}`", value.inner.ty().value_string(refs)),
                        )
                        .report(diags);
                        return Err(diag);
                    }
                };
                let value_expr = value
                    .inner
                    .as_ir_expression_unchecked(refs, &mut self.large, value.span, &ty)?;

                // override domain
                let result = Value::Hardware(HardwareValue {
                    ty,
                    domain: ValueDomain::from_domain_kind(domain.inner),
                    expr: value_expr,
                });
                LrValue::Right(ValueWithImplications::simple(result))
            }
            &ExpressionKind::Ref(span_keyword, operand) => {
                let expected_ty_inner = match expected_ty {
                    Type::Ref(expected_ty_inner) => expected_ty_inner,
                    Type::RefInterface(_, _) => &Type::Interface,
                    _ => &Type::Any,
                };

                let operand_span = operand.span;
                let operand = self.eval_expression_as_lr(scope, flow, expected_ty_inner, operand)?;

                let result = match operand {
                    LrValue::LeftTarget(operand) => {
                        let AssignmentTarget { base, steps } = operand;
                        if !steps.is_empty() {
                            return Err(diags.report_error_todo(operand_span, "reference to target with steps"));
                        }

                        match base.inner {
                            SignalOrVariable::Signal(signal) => {
                                let curr_module = self.curr_module.ok_or_else(|| {
                                    diags.report_error_internal(expr.span, "reference to signal outside module")
                                })?;
                                let signal_ty = signal.expect_ty(self, base.span)?;
                                ReferenceWrapper::new_signal(
                                    curr_module,
                                    signal,
                                    Arc::new(signal_ty.inner.clone()),
                                    signal.span_decl(self),
                                    span_keyword,
                                )
                            }
                            SignalOrVariable::Variable(var) => {
                                // Reference types are invariant, since they can be read and written to.
                                // Variables without any type can contain and accept any type,
                                //   so their type as a reference must be `Ref(any)` too.
                                let var_info = flow.var_info(Spanned::new(base.span, var))?;
                                let var_ty = var_info.ty.as_ref().map_or(Type::Any, |ty| ty.inner.clone());
                                ReferenceWrapper::new_variable(
                                    flow.root_id(),
                                    var,
                                    Arc::new(var_ty),
                                    var_info.span_decl,
                                    span_keyword,
                                )
                            }
                        }
                    }
                    LrValue::LeftInterface(info) => {
                        let curr_module = self.curr_module.ok_or_else(|| {
                            diags.report_error_internal(expr.span, "reference to interface outside module")
                        })?;
                        ReferenceWrapper::new_interface(curr_module, info, span_keyword)
                    }
                    LrValue::Right(_) => {
                        let e = DiagnosticError::new(
                            "cannot take reference to value",
                            span_keyword,
                            "trying to take reference here",
                        )
                        .add_info(operand_span, "this expression evaluates to a value")
                        .report(diags);
                        return Err(e);
                    }
                };

                LrValue::Right(Value::Simple(SimpleCompileValue::Reference(result)))
            }
            &ExpressionKind::Deref(span_keyword, operand) => {
                let reason = Spanned::new(span_keyword, "dereference operand");
                let operand = self.eval_expression_as_compile(scope, flow, &Type::Any, operand, reason)?;

                if let Value::Simple(SimpleCompileValue::Reference(rf)) = operand.inner {
                    match rf.get(self, flow, operand.span)? {
                        ReferenceInner::Variable { var, ty: _ } => {
                            if !flow.var_still_exists(var) {
                                let err = DiagnosticError::new(
                                    "cannot access variable after its scope has ended",
                                    span_keyword,
                                    "trying to dereference here",
                                )
                                .add_info(rf.span_decl, "variable declared here")
                                .add_info(rf.span_ref, "reference taken here")
                                .report(diags);
                                return Err(err);
                            }
                            LrValue::LeftTarget(AssignmentTarget::simple(Spanned::new(expr.span, var.into())))
                        }
                        ReferenceInner::Signal {
                            signal,
                            ty: _,
                            ty_hw: _,
                        } => LrValue::LeftTarget(AssignmentTarget::simple(Spanned::new(expr.span, signal.into()))),
                        ReferenceInner::Interface(info) => LrValue::LeftInterface(info.clone()),
                    }
                } else {
                    let diag = DiagnosticError::new(
                        "cannot dereference non-reference value",
                        span_keyword,
                        "trying to dereference non-reference here",
                    )
                    .add_info(
                        operand.span,
                        format!("operand has type `{}`", operand.inner.ty().value_string(refs)),
                    )
                    .report(diags);
                    return Err(diag);
                }
            }
        };
        Ok(result)
    }

    pub fn eval_call(
        &mut self,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr_span: Span,
        target: Spanned<&Value>,
        args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let diags = refs.diags;

        match target.inner {
            // typeof operator
            Value::Simple(SimpleCompileValue::Type(Type::Type)) => {
                let ty = self.eval_type_of(flow, target.span, args)?;
                Ok(Value::new_ty(ty))
            }

            // normal function
            Value::Simple(SimpleCompileValue::Function(target_function)) => {
                self.call_function(flow, expected_ty, target.span, expr_span, target_function, args)
            }
            // bound method
            Value::Compound(MixedCompoundValue::BoundMethod(bound)) => {
                self.call_bound_method(flow, expr_span, bound, args)
            }

            // constrain int type
            Value::Simple(SimpleCompileValue::Type(Type::Int(range))) => {
                let result = self.eval_int_ty_call(flow, expr_span, Spanned::new(target.span, range), args)?;
                Ok(Value::new_ty(result))
            }
            // constraint tuple type
            Value::Simple(SimpleCompileValue::Type(Type::Tuple(None))) => {
                let result = self.eval_tuple_ty_call(flow, target.span, args)?;
                Ok(Value::new_ty(result))
            }

            // not a valid call target
            _ => Err(diags.report_error_simple(
                "call target must be function",
                expr_span,
                format!("got value with type `{}`", target.inner.ty().value_string(refs)),
            )),
        }
    }

    /// Evaluate a call to `int` or `uint`, which is how integer range constraints are expressed.
    /// The arguments must be compile time, and either:
    /// * a single int, the bitwidth
    /// * a list of ranges which together form the multi-range
    fn eval_int_ty_call(
        &mut self,
        flow: &mut impl Flow,
        span_call: Span,
        target: Spanned<&MultiRange<BigInt>>,
        mut args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Type> {
        let refs = self.refs;
        let diags = refs.diags;
        let args_span = args.span();

        // int calls should only work for `int` and `uint`, detect which of these it is here
        let target_signed = match target.inner.as_single_range() {
            Some(NonEmptyRange { start: None, end: None }) => true,
            Some(NonEmptyRange {
                start: Some(BigInt::ZERO),
                end: None,
            }) => false,
            _ => {
                let diag = DiagnosticError::new(
                    "only `int` and `uint` can be constrained",
                    span_call,
                    "attempt to constrain type here",
                )
                .add_info(
                    target.span,
                    format!("base type is `{}`", Type::Int(target.inner.clone()).value_string(refs)),
                )
                .report(diags);
                return Err(diag);
            }
        };

        // evaluate args, they must be compile-time
        let param = Param::Positional { span: target.span };
        let mut values = vec![];
        while let Some(value) = args.next_value(self, flow, param, Spanned::new(target.span, &Type::Any))? {
            let value_compile = require_compile_arg(refs, "int type arguments", value.as_ref())?;
            values.push(Spanned::new(value.span, value_compile));
        }

        // if single integer arg, interpret as bitwidth
        if let Some(value) = values.single_ref()
            && let CompileValue::Simple(SimpleCompileValue::Int(width)) = &value.inner
        {
            let width = BigUint::try_from(width.clone()).map_err(|width| {
                diags.report_error_simple(
                    format!("the bitwidth of an integer type cannot be negative, got `{width}`"),
                    value.span,
                    "got negative bitwidth here",
                )
            })?;

            let range = if target_signed {
                let width_m1 = width.sub_1().map_err(|_: IsZero| {
                    diags.report_error_simple(
                        "zero-width signed integers are not allowed",
                        value.span,
                        "got width zero here",
                    )
                })?;

                let pow = BigUint::pow_2_to(&width_m1);
                Range {
                    start: Some(-&pow),
                    end: Some(BigInt::from(pow)),
                }
            } else {
                Range {
                    start: Some(BigInt::ZERO),
                    end: Some(BigInt::from(BigUint::pow_2_to(&width))),
                }
            };
            return Ok(Type::Int(MultiRange::from(range)));
        }

        // all args must be ranges, union them together
        let mut result = MultiRange::EMPTY;
        for value in values {
            let range = match value.inner {
                CompileValue::Compound(CompileCompoundValue::Range(range)) => range,
                _ => {
                    return Err(diags.report_error_simple(
                        "int type constraint must be a single int or one or more ranges",
                        value.span,
                        format!("got value with type `{}` here", value.inner.ty().value_string(refs)),
                    ));
                }
            };
            result = result.union(&MultiRange::from(range));
        }

        // check that the new range is a subrange of the base type
        let base_ty_name = match target_signed {
            true => "int",
            false => "uint",
        };
        if let Some(enclosing_range) = result.enclosing_range()
            && !target.inner.contains_range(enclosing_range)
        {
            let diag = DiagnosticError::new(
                "int range must be a subrange of the base type",
                args_span,
                format!("new range `{result}` is not a subrange"),
            )
            .add_info(target.span, format!("base type is `{base_ty_name}`"))
            .report(diags);
            return Err(diag);
        }

        Ok(Type::Int(result))
    }

    fn eval_tuple_ty_call(
        &mut self,
        flow: &mut impl Flow,
        span_target: Span,
        mut args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Type> {
        let diags = self.refs.diags;

        let param = Param::Positional { span: span_target };
        let mut tys = vec![];
        while let Some(value) = args.next_value(self, flow, param, Spanned::new(span_target, &Type::Type))? {
            match value.inner {
                Value::Simple(SimpleCompileValue::Type(ty)) => tys.push(ty),
                _ => return Err(diags.report_error_internal(value.span, "expected type, should have been checked")),
            }
        }

        Ok(Type::Tuple(Some(Arc::new(tys))))
    }

    fn eval_array_literal(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr_span: Span,
        values: &[ArrayLiteralElement<Expression>],
    ) -> DiagResult<Value> {
        // intentionally ignore the length, the caller can pass "0" when they have no opinion on it
        // TODO if we stop ignoring the length at some point, then we can infer lengths in eg. `[false] * _`
        let expected_ty_inner = match expected_ty {
            Type::Array(inner, _len) => &**inner,
            _ => &Type::Any,
        };

        // evaluate
        let values = values
            .iter()
            .map(|v| {
                let expected_ty_curr = match v {
                    ArrayLiteralElement::Single(_) => expected_ty_inner,
                    ArrayLiteralElement::Spread(_, _) => &Type::Array(Arc::new(expected_ty_inner.clone()), None),
                };

                v.map_inner(|value_inner| self.eval_expression(scope, flow, expected_ty_curr, value_inner))
                    .transpose()
            })
            .try_collect_all_vec()?;

        // combine into compile or non-compile value
        array_literal_combine_values(self.refs, flow, &mut self.large, expr_span, values)
    }

    fn eval_tuple_literal(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        values: &Vec<Expression>,
    ) -> DiagResult<Value> {
        let expected_tys_inner = if let Type::Tuple(Some(tys)) = expected_ty
            && tys.len() == values.len()
        {
            Some(tys)
        } else {
            None
        };

        let values = values
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                let expected_ty_i = expected_tys_inner.map_or(&Type::Any, |tys| &tys[i]);
                Ok(self.eval_expression(scope, flow, expected_ty_i, v)?.inner)
            })
            .try_collect_all_vec()?;

        Ok(Value::Compound(MixedCompoundValue::Tuple(values)))
    }

    fn eval_expression_as_array_step(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        index: Expression,
    ) -> DiagResult<TargetStep> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let index = self.eval_expression(scope, flow, &Type::Any, index)?;
        let index_span = index.span;

        let index_ty = index.inner.ty();
        let err_wrong_type = || {
            diags.report_error_simple(
                "array index must be integer or range",
                index.span,
                format!("got type `{}`", index_ty.value_string(refs)),
            )
        };
        let err_hardware_not_len = || {
            DiagnosticError::new(
                "hardware slicing only supports `start+..length` ranges",
                index.span,
                "got non-length slice",
            )
            .report(diags)
        };

        let step = match index.inner {
            Value::Simple(index) => match index {
                SimpleCompileValue::Int(index) => {
                    // check non-negative
                    let index = BigUint::try_from(index).map_err(|index| {
                        diags.report_error_simple(
                            "array index out of bounds",
                            index_span,
                            format!("array index cannot be negative, got {index}"),
                        )
                    })?;

                    TargetStep::Compile(TargetStepCompile::ArrayIndex(index))
                }
                _ => return Err(err_wrong_type()),
            },
            Value::Compound(index) => match index {
                MixedCompoundValue::Range(range) => match range {
                    RangeValue::Normal(Range { start, end }) => {
                        let start = match start {
                            None => BigUint::ZERO,
                            Some(start) => match start {
                                MaybeCompile::Compile(start) => {
                                    // check non-negative
                                    BigUint::try_from(&start).map_err(|_| {
                                        diags.report_error_simple(
                                            "array slice start out of bounds",
                                            index_span,
                                            format!("slice start cannot be negative, got {start}"),
                                        )
                                    })?
                                }
                                MaybeCompile::Hardware(_) => return Err(err_hardware_not_len()),
                            },
                        };

                        let length = match end {
                            None => None,
                            Some(end) => match end {
                                MaybeCompile::Compile(end) => {
                                    let length = &end - &start;
                                    let length = BigUint::try_from(length).map_err(|_| {
                                        diags.report_error_simple(
                                            "array slice end out of bounds",
                                            index_span,
                                            format!("slice end (got {end}) must be >= start (got {start})"),
                                        )
                                    })?;
                                    Some(length)
                                }
                                MaybeCompile::Hardware(_) => return Err(err_hardware_not_len()),
                            },
                        };

                        TargetStep::Compile(TargetStepCompile::ArraySlice { start, length })
                    }
                    RangeValue::HardwareStartLength { start, length } => {
                        let start = HardwareUInt::try_from(start).map_err(|start| {
                            diags.report_error_simple(
                                "array slice start out of bounds",
                                index_span,
                                format!("array slice start cannot be negative, got range {}", start.ty),
                            )
                        })?;
                        TargetStep::Hardware(TargetStepHardware::ArraySlice { start, length })
                    }
                },
                _ => return Err(err_wrong_type()),
            },
            Value::Hardware(index) => {
                // check int
                let index_ty = match index.ty {
                    HardwareType::Int(ty) => ty,
                    _ => return Err(err_wrong_type()),
                };
                let index = HardwareInt {
                    ty: index_ty,
                    domain: index.domain,
                    expr: index.expr,
                };

                // check non-negative
                let index = HardwareUInt::try_from(index).map_err(|index| {
                    diags.report_error_simple(
                        "array index out of bounds",
                        index_span,
                        format!("array index cannot be negative, got range {}", index.ty),
                    )
                })?;
                TargetStep::Hardware(TargetStepHardware::ArrayIndex(index))
            }
        };

        Ok(step)
    }

    pub fn eval_expression_as_compile(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expected_ty: &Type,
        expr: Expression,
        reason: Spanned<&'static str>,
    ) -> DiagResult<Spanned<CompileValue>> {
        // TODO should we allow compile-time writes to the outside?
        //   right now we intentionally don't because that might be confusing in eg. function params or types
        let mut flow_inner = flow.new_child_compile(reason.span, reason.inner);
        let value = self.eval_expression(scope, &mut flow_inner, expected_ty, expr)?.inner;

        let value = CompileValue::try_from(&value).map_err(|_: NotCompile| {
            self.refs.diags.report_error_simple(
                format!("{} must be a compile-time value", reason.inner),
                expr.span,
                "got hardware value",
            )
        })?;
        Ok(Spanned {
            span: expr.span,
            inner: value,
        })
    }

    pub fn eval_expression_as_ty(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr: Expression,
    ) -> DiagResult<Spanned<Type>> {
        let refs = self.refs;
        let diags = self.refs.diags;

        // TODO unify this message with the one when a normal type-check fails
        match self
            .eval_expression_as_compile(scope, flow, &Type::Type, expr, Spanned::new(expr.span, "type"))?
            .inner
        {
            CompileValue::Simple(SimpleCompileValue::Type(ty)) => Ok(Spanned {
                span: expr.span,
                inner: ty,
            }),
            value => {
                let mut diag = DiagnosticError::new(
                    "expected type, got value",
                    expr.span,
                    format!("got value with type `{}`", value.ty().value_string(refs)),
                );

                if let ExpressionKind::TupleLiteral(_) = self.refs.get_expr(expr) {
                    diag = diag.add_footer_hint("tuple types are written `Tuple(...)`, not `(...)`")
                }

                Err(diag.report(diags))
            }
        }
    }

    pub fn eval_expression_as_ty_hardware(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr: Expression,
        reason: &str,
    ) -> DiagResult<Spanned<HardwareType>> {
        let refs = self.refs;
        let diags = self.refs.diags;
        let elab = &self.refs.shared.elaboration_arenas;

        let ty = self.eval_expression_as_ty(scope, flow, expr)?.inner;
        let ty_hw = ty.as_hardware_type(elab).map_err(|_| {
            diags.report_error_simple(
                format!("{reason} type must be representable in hardware"),
                expr.span,
                format!("got type `{}`", ty.value_string(refs)),
            )
        })?;
        Ok(Spanned {
            span: expr.span,
            inner: ty_hw,
        })
    }

    pub fn eval_expression_as_domain_signal(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr: Expression,
    ) -> DiagResult<Spanned<DomainSignal>> {
        let diags = self.refs.diags;
        let build_err =
            |actual: &str| diags.report_error_simple("expected domain signal", expr.span, format!("got {actual}"));
        self.try_eval_expression_as_domain_signal(scope, flow, expr, build_err)
            .map_err(|e| e.into_inner())
    }

    pub fn try_eval_expression_as_domain_signal<E>(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr: Expression,
        build_err: impl Fn(&str) -> E,
    ) -> Result<Spanned<DomainSignal>, Either<E, DiagError>> {
        // TODO expand to allow general expressions again (which then probably create implicit signals)?
        let result = match *self.refs.get_expr_inner(expr) {
            ExpressionKind::UnaryOp(
                Spanned {
                    span: _,
                    inner: UnaryOp::Not,
                },
                inner,
            ) => {
                let inner = self
                    .try_eval_expression_as_domain_signal(scope, flow, inner, build_err)?
                    .inner;
                Ok(inner.invert())
            }
            ExpressionKind::Id(id) => {
                let id = self.eval_id(scope, flow, id).map_err(Either::Right)?;
                let named = self.eval_scoped_as_named(scope, id).map_err(|e| Either::Right(e))?;

                match named {
                    NamedOrValue::Value(_) => Err(build_err("a value")),
                    NamedOrValue::Named(s) => match s {
                        NamedValue::Signal(s) => Ok(Polarized::new(s)),
                        NamedValue::Variable(_) => Err(build_err("a variable")),
                        NamedValue::Interface(_) => Err(build_err("an interface instance")),
                    },
                }
            }
            _ => Err(build_err("a general expression")),
        };

        let result = result.map_err(|e| Either::Left(e))?;
        Ok(Spanned {
            span: expr.span,
            inner: result,
        })
    }

    pub fn eval_domain_sync(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        domain: SyncDomain<Expression>,
    ) -> DiagResult<SyncDomain<DomainSignal>> {
        let SyncDomain { clock, reset } = domain;
        let clock = self.eval_expression_as_domain_signal(scope, flow, clock);
        let reset = reset.map(|reset| self.eval_expression_as_domain_signal(scope, flow, reset));
        Ok(SyncDomain {
            clock: clock?.inner,
            reset: reset.transpose()?.map(|r| r.inner),
        })
    }

    pub fn eval_domain(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        domain: Spanned<DomainKind<Expression>>,
    ) -> DiagResult<Spanned<DomainKind<DomainSignal>>> {
        let result = match domain.inner {
            DomainKind::Const => Ok(DomainKind::Const),
            DomainKind::Async => Ok(DomainKind::Async),
            DomainKind::Sync(domain) => self.eval_domain_sync(scope, flow, domain).map(DomainKind::Sync),
        };

        Ok(Spanned {
            span: domain.span,
            inner: result?,
        })
    }

    pub fn eval_port_domain(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        domain: Spanned<DomainKind<Expression>>,
    ) -> DiagResult<Spanned<DomainKind<Polarized<Port>>>> {
        let diags = self.refs.diags;
        let result = self.eval_domain(scope, flow, domain)?;

        Ok(Spanned {
            span: result.span,
            inner: match result.inner {
                DomainKind::Const => DomainKind::Const,
                DomainKind::Async => DomainKind::Async,
                DomainKind::Sync(sync) => DomainKind::Sync(sync.try_map_signal(|signal| {
                    signal.try_map_inner(|signal| match signal {
                        Signal::Port(port) => Ok(port),
                        Signal::Wire(_) => Err(diags.report_error_internal(domain.span, "expected port, got wire")),
                    })
                })?),
            },
        })
    }

    pub fn eval_expression_as_for_iterator(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        iter: Expression,
    ) -> DiagResult<ForIterator> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let iter = self.eval_expression(scope, flow, &Type::Any, iter)?;
        let iter_span = iter.span;

        let result = match iter.inner {
            // range
            Value::Compound(MixedCompoundValue::Range(iter)) => {
                // TODO allow hardware-length range?
                fn expect_compile<C, H>(diags: &Diagnostics, iter_span: Span, v: MaybeCompile<C, H>) -> DiagResult<C> {
                    match v {
                        MaybeCompile::Compile(v) => Ok(v),
                        MaybeCompile::Hardware(_) => Err(diags.report_error_simple(
                            "iterator range must be compile-time value",
                            iter_span,
                            "got hardware value here",
                        )),
                    }
                }

                match iter {
                    RangeValue::Normal(Range { start, end }) => {
                        // check compile
                        let start = start.map(|start| expect_compile(diags, iter_span, start)).transpose()?;
                        let end = end.map(|end| expect_compile(diags, iter_span, end)).transpose()?;

                        // check start
                        let start = start.ok_or_else(|| {
                            let range = Range {
                                start: None,
                                end: end.clone(),
                            };
                            diags.report_error_simple(
                                "iterator range must have start value",
                                iter_span,
                                format!("got range `{}`", range),
                            )
                        })?;

                        ForIterator::Range { next: start, end }
                    }
                    RangeValue::HardwareStartLength { start, length: _ } => {
                        let _: HardwareInt = start;
                        return Err(diags.report_error_simple(
                            "iterator range must be compile-time value",
                            iter_span,
                            "got hardware value here",
                        ));
                    }
                }
            }

            // tuple
            Value::Compound(MixedCompoundValue::Tuple(values)) => ForIterator::MixedTuple {
                left: VecDeque::from(values),
            },

            Value::Hardware(HardwareValue {
                ty: HardwareType::Tuple(ty_elements),
                domain,
                expr: tuple_expr,
            }) => ForIterator::HardwareTuple {
                next: 0,
                base: HardwareValue {
                    ty: ty_elements,
                    domain,
                    expr: tuple_expr,
                },
            },

            // array
            Value::Simple(SimpleCompileValue::Array(array)) => ForIterator::CompileArray { next: 0, array },
            Value::Hardware(HardwareValue {
                ty: HardwareType::Array(ty_inner, len),
                domain,
                expr: array_expr,
            }) => {
                let base = HardwareValue {
                    ty: (Arc::unwrap_or_clone(ty_inner), len),
                    domain,
                    expr: array_expr,
                };
                ForIterator::HardwareArray {
                    next: BigUint::ZERO,
                    base,
                }
            }
            _ => {
                return Err(diags.report_error_simple(
                    "invalid for loop iterator type, must be range, tuple or array",
                    iter.span,
                    format!("iterator has type `{}`", iter.inner.ty().value_string(refs)),
                ));
            }
        };

        Ok(result)
    }

    pub fn eval_expression_as_module(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        span_keyword: Span,
        expr: Expression,
    ) -> DiagResult<ElaboratedModule> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let eval =
            self.eval_expression_as_compile(scope, flow, &Type::Module, expr, Spanned::new(expr.span, "module"))?;

        let reason = TypeContainsReason::InstanceModule(span_keyword);
        check_type_contains_value(refs, reason, &Type::Module, eval.as_ref())?;

        match eval.inner {
            CompileValue::Simple(SimpleCompileValue::Module(elab)) => Ok(elab),
            _ => Err(diags.report_error_internal(eval.span, "expected module, should have already been checked")),
        }
    }
}

pub enum ForIterator {
    Range {
        next: BigInt,
        // exclusive
        end: Option<BigInt>,
    },
    MixedTuple {
        left: VecDeque<Value>,
    },
    HardwareTuple {
        next: usize,
        base: HardwareValue<Arc<Vec<HardwareType>>>,
    },
    CompileArray {
        next: usize,
        array: Arc<Vec<CompileValue>>,
    },
    HardwareArray {
        next: BigUint,
        base: HardwareValue<(HardwareType, BigUint)>,
    },
}

impl ForIterator {
    pub fn len(&self) -> Option<BigUint> {
        match self {
            ForIterator::Range { next, end } => end.as_ref().map(|end| BigUint::try_from(end - next).unwrap()),
            ForIterator::MixedTuple { left } => Some(left.len().into()),
            ForIterator::HardwareTuple { next, base } => Some(BigUint::from(base.ty.len() - *next)),
            ForIterator::CompileArray { next, array } => Some(BigUint::from(array.len() - *next)),
            ForIterator::HardwareArray { next, base } => {
                let (_, len) = &base.ty;
                Some(BigUint::try_from(len - next).unwrap())
            }
        }
    }
}

/// Temporary type to allow delaying construction of the large expression,
/// because we don't have access to [IrLargeArena] in the iterator.
pub enum ForIteratorIrExpression {
    Ir(IrExpression),
    Large(IrExpressionLarge),
}

impl ForIteratorIrExpression {
    pub fn into_expr(self, large: &mut IrLargeArena) -> IrExpression {
        match self {
            ForIteratorIrExpression::Ir(expr) => expr,
            ForIteratorIrExpression::Large(expr) => large.push_expr(expr),
        }
    }
}

impl Iterator for ForIterator {
    type Item = Value<SimpleCompileValue, MixedCompoundValue, HardwareValue<HardwareType, ForIteratorIrExpression>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ForIterator::Range { next, end } => {
                if end.as_ref().is_none_or(|end| &*next < end) {
                    let curr = Value::new_int(next.clone());
                    *next += 1;
                    Some(curr)
                } else {
                    None
                }
            }
            ForIterator::MixedTuple { left } => left
                .pop_front()
                .map(|v| v.map_hardware(|v| v.map_expression(ForIteratorIrExpression::Ir))),
            ForIterator::HardwareTuple { next, base } => {
                let index = *next;
                let ty_element = base.ty.get(index)?;
                *next += 1;

                let step = IrTargetStepScalar::TupleIndex(index);
                let element_expr = IrExpressionLarge::Steps {
                    base: base.expr.clone(),
                    steps: IrTargetSteps::single(step),
                };
                Some(Value::Hardware(HardwareValue {
                    ty: ty_element.clone(),
                    domain: base.domain,
                    expr: ForIteratorIrExpression::Large(element_expr),
                }))
            }
            ForIterator::CompileArray { next, array } => {
                if *next < array.len() {
                    let curr = array[*next].clone();
                    *next += 1;
                    Some(Value::from(curr))
                } else {
                    None
                }
            }
            ForIterator::HardwareArray { next, base } => {
                let HardwareValue {
                    ty: (ty_inner, ty_len),
                    domain,
                    expr: base_expr,
                } = &*base;

                if &*next < ty_len {
                    let index_expr = IrExpression::Int(BigInt::from(next.clone()));
                    *next += 1u8;

                    let step = IrTargetStepScalar::ArrayIndex(index_expr);
                    let element_expr = IrExpressionLarge::Steps {
                        base: base_expr.clone(),
                        steps: IrTargetSteps::single(step),
                    };
                    Some(Value::Hardware(HardwareValue {
                        ty: (*ty_inner).clone(),
                        domain: *domain,
                        expr: ForIteratorIrExpression::Large(element_expr),
                    }))
                } else {
                    None
                }
            }
        }
    }
}

fn pair_compile_int<L: AnyInt, R: AnyInt>(
    left: MaybeCompile<L, HardwareValue<ClosedNonEmptyMultiRange<L>>>,
    right: MaybeCompile<R, HardwareValue<ClosedNonEmptyMultiRange<R>>>,
) -> MaybeCompile<
    (L, R),
    (
        HardwareValue<ClosedNonEmptyMultiRange<L>>,
        HardwareValue<ClosedNonEmptyMultiRange<R>>,
    ),
> {
    fn f<T: AnyInt>(x: T) -> HardwareValue<ClosedNonEmptyMultiRange<T>> {
        HardwareValue {
            ty: ClosedNonEmptyMultiRange::single(x.clone()),
            domain: ValueDomain::Const,
            expr: IrExpression::Int(x.into()),
        }
    }

    pair_compile(left, right, |x: L| f(x), |x: R| f(x))
}

fn pair_compile<LC, LH, RC, RH>(
    left: MaybeCompile<LC, LH>,
    right: MaybeCompile<RC, RH>,
    f_left: impl FnOnce(LC) -> LH,
    f_right: impl FnOnce(RC) -> RH,
) -> MaybeCompile<(LC, RC), (LH, RH)> {
    match (left, right) {
        (MaybeCompile::Compile(left), MaybeCompile::Compile(right)) => MaybeCompile::Compile((left, right)),
        (left, right) => {
            let left = match left {
                MaybeCompile::Compile(left) => f_left(left),
                MaybeCompile::Hardware(left) => left,
            };
            let right = match right {
                MaybeCompile::Compile(right) => f_right(right),
                MaybeCompile::Hardware(right) => right,
            };
            MaybeCompile::Hardware((left, right))
        }
    }
}

pub fn eval_binary_expression(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    expr_span: Span,
    op: Spanned<BinaryOp>,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
) -> DiagResult<ValueWithImplications> {
    let diags = refs.diags;

    let op_reason = TypeContainsReason::Operator(op.span);
    let op_span = op.span;

    // common utility functions
    let eval_arithmetic =
        |large, left, right, op| eval_binary_arithmetic(refs, large, expr_span, Spanned::new(op_span, op), left, right);
    let eval_bool = |large, left, right, op| eval_binary_bool(refs, large, op_reason, left, right, op);
    let eval_eq = |large, left, right, eq| eval_binary_eq(refs, large, op_reason, op_span, left, right, eq);
    let eval_compare = |large, left, right, op| {
        eval_binary_int_compare(refs, large, op_reason, left, right, op).map(ValueWithImplications::from)
    };
    let eval_bitwise = |large, left, right, op| eval_binary_bitwise(refs, large, op_reason, op_span, left, right, op);

    // handle operation
    let result_simple: Value<_> = match op.inner {
        // arithmetic:
        //   (int, int), (range, range)
        BinaryOp::Add => eval_arithmetic(large, left, right, IrIntArithmeticOp::Add)?,
        BinaryOp::Sub => eval_arithmetic(large, left, right, IrIntArithmeticOp::Sub)?,
        BinaryOp::Mul => match left.inner.ty() {
            Type::Array(_, _) => eval_array_repeat(refs, large, expr_span, op_reason, left, right)?,
            _ => eval_arithmetic(large, left, right, IrIntArithmeticOp::Mul)?,
        },
        BinaryOp::FloorDiv => eval_arithmetic(large, left, right, IrIntArithmeticOp::FloorDiv)?,
        BinaryOp::CeilDiv => eval_arithmetic(large, left, right, IrIntArithmeticOp::CeilDiv)?,
        BinaryOp::Mod => eval_arithmetic(large, left, right, IrIntArithmeticOp::Mod)?,
        BinaryOp::Pow => eval_arithmetic(large, left, right, IrIntArithmeticOp::Pow)?,
        BinaryOp::Shl => eval_arithmetic(large, left, right, IrIntArithmeticOp::Shl)?,
        BinaryOp::Shr => eval_arithmetic(large, left, right, IrIntArithmeticOp::Shr)?,

        // boolean:
        //   (bool, bool)
        // TODO these should short-circuit, so delay evaluation of right
        BinaryOp::BoolAnd => return eval_bool(large, left, right, IrBoolBinaryOp::And),
        BinaryOp::BoolOr => return eval_bool(large, left, right, IrBoolBinaryOp::Or),
        BinaryOp::BoolXor => return eval_bool(large, left, right, IrBoolBinaryOp::Xor),

        // bitwise:
        //   (bool, bool), (int, int), (bool, []bool), ([]bool, bool), ([]bool, []bool)
        BinaryOp::BitAnd => return eval_bitwise(large, left, right, IrBoolBinaryOp::And),
        BinaryOp::BitOr => return eval_bitwise(large, left, right, IrBoolBinaryOp::Or),
        BinaryOp::BitXor => return eval_bitwise(large, left, right, IrBoolBinaryOp::Xor),

        // comparison
        //   (T, T)
        BinaryOp::CmpEq => return eval_eq(large, left, right, true),
        BinaryOp::CmpNeq => return eval_eq(large, left, right, false),
        BinaryOp::CmpLt => return eval_compare(large, left, right, IrIntCompareOp::Lt),
        BinaryOp::CmpLte => return eval_compare(large, left, right, IrIntCompareOp::Lte),
        BinaryOp::CmpGt => return eval_compare(large, left, right, IrIntCompareOp::Gt),
        BinaryOp::CmpGte => return eval_compare(large, left, right, IrIntCompareOp::Gte),

        // contains
        //   (int, range) or (T:Eq, array)
        // TODO share code with match "in" pattern
        // TODO for hardware ranges, also check if start <(=) end, otherwise this might have false positives
        BinaryOp::In => return Err(diags.report_error_todo(expr_span, "binary op In")),
    };

    Ok(Value::simple(result_simple))
}

fn eval_binary_arithmetic(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    expr_span: Span,
    op: Spanned<IrIntArithmeticOp>,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
) -> DiagResult<Value> {
    let diags = refs.diags;
    let left_span = left.span;
    let right_span = right.span;
    let op_reason = TypeContainsReason::Operator(op.span);

    match (left.inner.ty(), right.inner.ty()) {
        (Type::Int(_), Type::Int(_)) => {
            // type cast
            let left = check_type_is_int(refs, op_reason, left.map_inner(|e| e.into_value()))
                .map_err(|_| diags.report_error_internal(left_span, "expected int"))?;
            let right = check_type_is_int(refs, op_reason, right.map_inner(|e| e.into_value()))
                .map_err(|_| diags.report_error_internal(right_span, "expected int"))?;

            // check operands valid for operator and compute result range
            let range = arithmetic_result_range(
                diags,
                expr_span,
                op,
                Spanned::new(left_span, &left.range()),
                Spanned::new(right_span, &right.range()),
            )?;

            // handle compile/hardware
            match pair_compile_int(left, right) {
                MaybeCompile::Compile((left, right)) => {
                    Ok(Value::new_int(arithmetic_result_compile(op.inner, left, right)))
                }
                MaybeCompile::Hardware((left, right)) => {
                    let result = build_binary_int_arithmetic_op(op.inner, large, range, left, right);
                    Ok(Value::Hardware(HardwareValue::from(result)))
                }
            }
        }
        (Type::Range, Type::Range) => {
            let left = check_arithmetic_range_operand(refs, op.span, left);
            let right = check_arithmetic_range_operand(refs, op.span, right);
            let (left, right) = (left?, right?);

            let result = arithmetic_result_range(
                diags,
                expr_span,
                op,
                Spanned::new(left_span, &left),
                Spanned::new(right_span, &right),
            )?;

            Ok(range_arithmetic_result_value(result))
        }
        (left_ty, right_ty) => {
            let diag = DiagnosticError::new(
                "arithmetic operators require either two ints or two ranges",
                op.span,
                "for operator here",
            )
            .add_info(
                left_span,
                format!("left operand has type `{}`", left_ty.value_string(refs)),
            )
            .add_info(
                right_span,
                format!("right operand has type `{}`", right_ty.value_string(refs)),
            )
            .report(diags);
            Err(diag)
        }
    }
}

fn check_arithmetic_range_operand(
    refs: CompileRefs,
    op_span: Span,
    value: Spanned<ValueWithImplications>,
) -> DiagResult<ClosedNonEmptyMultiRange<BigInt>> {
    let diags = refs.diags;
    let range_span = value.span;

    // type cast
    let op_reason = TypeContainsReason::Operator(op_span);
    let range = check_type_is_range(refs, op_reason, value.map_inner(|e| e.into_value()))
        .map_err(|_| diags.report_error_internal(range_span, "expected range"))?;
    let range = Spanned::new(range_span, range);

    // check compile
    let range = Range::<BigInt>::try_from(&range.inner).map_err(|e| {
        let _: NotCompile = e;
        DiagnosticError::new(
            "range arithmetic requires compile-time ranges",
            range_span,
            "range with hardware bounds here",
        )
        .add_info(op_span, "for operator here")
        .report(diags)
    })?;

    // check closed
    match ClosedNonEmptyRange::try_from(range.clone()) {
        Ok(range) => Ok(ClosedNonEmptyMultiRange::from(range)),
        Err(e) => {
            let reason = match e {
                Either::Left(RangeEmpty) => "empty",
                Either::Right(RangeOpen) => "open",
            };
            let diag = DiagnosticError::new(
                format!("range arithmetic requires non-empty closed ranges, got {reason} range"),
                range_span,
                format!("got range `{range}` here"),
            )
            .add_info(op_span, "for operator here")
            .report(diags);
            Err(diag)
        }
    }
}

fn range_arithmetic_result_value(result: ClosedNonEmptyMultiRange<BigInt>) -> Value {
    // TODO preserve multi-range
    let result = Range::from(result.enclosing_range().cloned());
    Value::from(CompileValue::Compound(CompileCompoundValue::Range(result)))
}

/// Evaluate an arithmetic operation on compile-time ints, the operands must have been checked already.
fn arithmetic_result_compile(op: IrIntArithmeticOp, left: BigInt, right: BigInt) -> BigInt {
    let right_uint = || BigUint::try_from(right.clone()).expect("already checked non-negative");
    match op {
        IrIntArithmeticOp::Add => &left + &right,
        IrIntArithmeticOp::Sub => &left - &right,
        IrIntArithmeticOp::Mul => &left * &right,
        IrIntArithmeticOp::FloorDiv => left.div_floor(&right).expect("already checked non-zero"),
        IrIntArithmeticOp::CeilDiv => left.div_ceil(&right).expect("already checked non-zero"),
        IrIntArithmeticOp::Mod => left.mod_floor(&right).expect("already checked non-zero"),
        IrIntArithmeticOp::Pow => left.pow(&right_uint()),
        IrIntArithmeticOp::Shl => left * BigUint::pow_2_to(&right_uint()),
        IrIntArithmeticOp::Shr => left
            .div_floor(&BigInt::from(BigUint::pow_2_to(&right_uint())))
            .expect("known nonzero"),
    }
}

/// Check that the operation is valid for all values in the operand ranges,
/// and compute the range of the result.
fn arithmetic_result_range(
    diags: &Diagnostics,
    expr_span: Span,
    op: Spanned<IrIntArithmeticOp>,
    left: Spanned<&ClosedNonEmptyMultiRange<BigInt>>,
    right: Spanned<&ClosedNonEmptyMultiRange<BigInt>>,
) -> DiagResult<ClosedNonEmptyMultiRange<BigInt>> {
    // utilities
    let check_right_nonzero = |op_name: &str| {
        if right.inner.contains(&BigInt::ZERO) {
            let msg_right = message_range_or_single("right", right.inner, Some("which contains zero"));
            let diag = DiagnosticError::new(format!("{op_name} by zero is not allowed"), right.span, msg_right)
                .add_info(op.span, "for operator here")
                .report(diags);
            return Err(diag);
        }
        Ok(())
    };
    let check_right_shift_factor = || {
        if right.inner.enclosing_range().start.is_negative() {
            let diag = DiagnosticError::new(
                "shift amount must be non-negative",
                right.span,
                message_range_or_single("right", right.inner, None),
            )
            .add_info(op.span, "for operator here")
            .report(diags);
            return Err(diag);
        }

        let right_uint = right.inner.clone().map(|x| BigUint::try_from(x).unwrap());
        let factor =
            multi_range_binary_pow(&ClosedNonEmptyMultiRange::single(BigInt::TWO), &right_uint).expect("non-zero base");
        Ok(factor)
    };

    let result = match op.inner {
        IrIntArithmeticOp::Add => multi_range_binary_add(left.inner, right.inner),
        IrIntArithmeticOp::Sub => multi_range_binary_sub(left.inner, right.inner),
        IrIntArithmeticOp::Mul => multi_range_binary_mul(left.inner, right.inner),
        IrIntArithmeticOp::FloorDiv => {
            check_right_nonzero("division")?;
            multi_range_binary_div_floor(left.inner, right.inner).expect("already checked for zero")
        }
        IrIntArithmeticOp::CeilDiv => {
            check_right_nonzero("division")?;
            multi_range_binary_div_ceil(left.inner, right.inner).expect("already checked for zero")
        }
        IrIntArithmeticOp::Mod => {
            check_right_nonzero("modulo")?;
            multi_range_binary_mod(left.inner, right.inner).expect("already checked for zero")
        }
        IrIntArithmeticOp::Pow => {
            let (base, exp) = (left, right);

            // check exp >= 0
            if exp.inner.enclosing_range().start.is_negative() {
                let diag = DiagnosticError::new("invalid power operation", expr_span, "exponent must be non-negative")
                    .add_info(exp.span, message_range_or_single("exponent", exp.inner, None))
                    .report(diags);
                return Err(diag);
            }

            // check not 0 ** 0
            // TODO is there actually a reason to ban this? `1` makes sense as the answer
            if base.inner.contains(&BigInt::ZERO) && exp.inner.contains(&BigInt::ZERO) {
                let msg_base = message_range_or_single("base", base.inner, Some("which contains zero"));
                let msg_exp = message_range_or_single("exponent", exp.inner, Some("which contains zero"));
                let diag = DiagnosticError::new(
                    "invalid power operation `0 ** 0`",
                    expr_span,
                    "base and exponent could both be zero",
                )
                .add_info(base.span, msg_base)
                .add_info(exp.span, msg_exp)
                .report(diags);
                return Err(diag);
            }

            let exp_uint = exp.inner.clone().map(|x| BigUint::try_from(x).unwrap());
            multi_range_binary_pow(base.inner, &exp_uint).expect("already checked for 0**0")
        }
        IrIntArithmeticOp::Shl => multi_range_binary_mul(left.inner, &check_right_shift_factor()?),
        IrIntArithmeticOp::Shr => {
            multi_range_binary_div_floor(left.inner, &check_right_shift_factor()?).expect("non-zero divisor")
        }
    };
    Ok(result)
}

fn eval_array_repeat(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    expr_span: Span,
    op_reason: TypeContainsReason,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
) -> DiagResult<Value> {
    // TODO do we want to keep using multiplication as the "array repeat" syntax?
    //   if so, maybe allow tuples on the right side for multidimensional repeating
    // TODO maybe put a general cap on array sizes,
    //   to avoid memory overflows and different behavior between compile and hardware values?
    let diags = refs.diags;
    let elab = &refs.shared.elaboration_arenas;

    let (left_ty_inner, left_len) = unwrap_match!(left.inner.ty(), Type::Array(inner, len) => (inner, len));
    let left_len = left_len.expect("array value has known length");

    let right_span = right.span;
    let right = check_type_is_int(refs, op_reason, right.map_inner(|e| e.into_value()))?;
    let right_inner = match right {
        MaybeCompile::Compile(right_inner) => right_inner,
        MaybeCompile::Hardware(_) => {
            return Err(diags.report_error_simple(
                "array repeat right hand side must be compile-time value",
                right_span,
                "got non-compile-time value here",
            ));
        }
    };
    let right_inner = BigUint::try_from(right_inner).map_err(|right_inner| {
        diags.report_error_simple(
            "array repeat right hand side cannot be negative",
            right_span,
            format!("got value `{right_inner}`"),
        )
    })?;
    let right_inner = usize::try_from(right_inner).map_err(|right_inner| {
        diags.report_error_simple(
            "array repeat right hand side too large",
            right_span,
            format!("got value `{right_inner}`"),
        )
    })?;

    let result = match left.inner.into_value() {
        Value::Simple(SimpleCompileValue::Array(left_inner)) => {
            // do the repetition at compile-time
            let result_len = usize::try_from(BigUint::from(left_inner.len()) * right_inner).map_err(|result_len| {
                diags.report_error_simple(
                    "array repeat result size too large",
                    right_span,
                    format!("got value `{result_len}`"),
                )
            })?;

            let mut result = try_vec_with_capacity(diags, expr_span, result_len)?;
            for _ in 0..right_inner {
                result.extend_from_slice(&left_inner);
            }
            Value::Simple(SimpleCompileValue::Array(Arc::new(result)))
        }
        Value::Hardware(value) => {
            // implement runtime repetition through spread array literal
            let element = IrArrayLiteralElement::Spread(value.expr);
            let mut elements = try_vec_with_capacity(diags, expr_span, right_inner)?;
            elements.resize(right_inner, element);

            let left_ty_inner_hw = left_ty_inner.as_hardware_type(elab).unwrap();
            let result_len = left_len * right_inner;
            let result_expr =
                IrExpressionLarge::ArrayLiteral(left_ty_inner_hw.as_ir(refs), result_len.clone(), elements);
            Value::Hardware(HardwareValue {
                ty: HardwareType::Array(Arc::new(left_ty_inner_hw.clone()), result_len),
                domain: value.domain,
                expr: large.push_expr(result_expr),
            })
        }
        Value::Simple(_) | Value::Compound(_) => {
            return Err(
                diags.report_error_internal(left.span, "compile-time value with type array is not actually an array")
            );
        }
    };

    Ok(result)
}

/// Logical not for bools, bitwise not for ints and bool arrays.
fn eval_unary_not(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_span: Span,
    operand: Spanned<ValueWithImplications>,
) -> DiagResult<ValueWithImplications> {
    let op_reason = TypeContainsReason::Operator(op_span);
    let operand_ty = operand.inner.ty();

    match &operand_ty {
        Type::Bool => {
            let operand_bool = check_type_is_bool(refs, op_reason, operand)?;
            let result = match operand_bool {
                MaybeCompile::Compile(c) => MaybeCompile::Compile(!c),
                MaybeCompile::Hardware(v) => build_unary_bool_gate(large, v, |b| !b),
            };
            return Ok(result.into());
        }
        Type::Int(_) => {
            let operand_int = check_type_is_int(refs, op_reason, operand.map_inner(|v| v.into_value()))?;
            let result = match operand_int {
                MaybeCompile::Compile(c) => Value::new_int(!c),
                MaybeCompile::Hardware(v) => {
                    // `!x == -1 - x`
                    let range = multi_range_unary_bitwise_not(&v.ty);
                    let expr = IrExpressionLarge::IntArithmetic(
                        IrIntArithmeticOp::Sub,
                        range.enclosing_range().cloned(),
                        IrExpression::Int(BigInt::NEG_ONE),
                        v.expr,
                    );
                    Value::Hardware(HardwareValue {
                        ty: HardwareType::Int(range),
                        domain: v.domain,
                        expr: large.push_expr(expr),
                    })
                }
            };
            return Ok(ValueWithImplications::simple(result));
        }
        Type::Array(ty_inner, _) => {
            if matches!(**ty_inner, Type::Bool) {
                let operand_array =
                    check_type_is_bool_array(refs, op_reason, operand.map_inner(|v| v.into_value()), None)?;
                let result = match operand_array {
                    MaybeCompile::Compile(c) => {
                        let result = c.into_iter().map(|b| CompileValue::new_bool(!b)).collect();
                        Value::Simple(SimpleCompileValue::Array(Arc::new(result)))
                    }
                    MaybeCompile::Hardware(v) => {
                        // `!x == x ^ true`
                        let ones = large.push_expr(IrExpressionLarge::BoolFill(v.ty.clone(), IrExpression::Bool(true)));
                        Value::Hardware(HardwareValue {
                            ty: HardwareType::Array(Arc::new(HardwareType::Bool), v.ty),
                            domain: v.domain,
                            expr: large.push_expr(IrExpressionLarge::BoolBinaryArray(
                                IrBoolBinaryOp::Xor,
                                v.expr,
                                ones,
                            )),
                        })
                    }
                };
                return Ok(ValueWithImplications::simple(result));
            }
        }
        _ => {
            // fallthrough
        }
    }

    // report type error
    let diag = DiagnosticError::new("invalid operand type for not operator", op_span, "for operator here")
        .add_info(
            operand.span,
            format!("operand has type `{}`", operand_ty.value_string(refs)),
        )
        .add_footer_hint("the not operator supports `bool`, `int` and `[_]bool`")
        .report(refs.diags);
    Err(diag)
}

fn eval_binary_bitwise(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    op_span: Span,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
    op: IrBoolBinaryOp,
) -> DiagResult<ValueWithImplications> {
    #[derive(Debug, Copy, Clone)]
    enum Kind {
        Bool,
        Int,
        Range,
        BoolArray,
    }
    let kind_of = |ty: &Type| match ty {
        Type::Bool => Some(Kind::Bool),
        Type::Int(_) => Some(Kind::Int),
        Type::Range => Some(Kind::Range),
        Type::Array(inner, _) if matches!(**inner, Type::Bool) => Some(Kind::BoolArray),
        _ => None,
    };

    let left_ty = left.inner.ty();
    let right_ty = right.inner.ty();

    match (kind_of(&left_ty), kind_of(&right_ty)) {
        (Some(Kind::Bool), Some(Kind::Bool)) => eval_binary_bool(refs, large, op_reason, left, right, op),
        (Some(Kind::Int), Some(Kind::Int)) => {
            let left = check_type_is_int(refs, op_reason, left.map_inner(|e| e.into_value()))?;
            let right = check_type_is_int(refs, op_reason, right.map_inner(|e| e.into_value()))?;

            let result = match pair_compile_int(left, right) {
                MaybeCompile::Compile((left, right)) => Value::new_int(op.eval_int(&left, &right)),
                MaybeCompile::Hardware((left, right)) => {
                    Value::Hardware(HardwareValue::from(build_binary_int_bitwise_op(large, op, left, right)))
                }
            };
            Ok(ValueWithImplications::simple(result))
        }
        (Some(Kind::Range), Some(Kind::Range)) => {
            let left = check_arithmetic_range_operand(refs, op_span, left);
            let right = check_arithmetic_range_operand(refs, op_span, right);
            let (left, right) = (left?, right?);

            let result = multi_range_binary_bitwise(op, &left, &right);
            Ok(ValueWithImplications::simple(range_arithmetic_result_value(result)))
        }
        (Some(Kind::Bool | Kind::BoolArray), Some(Kind::Bool | Kind::BoolArray)) => {
            let left = check_bit_operand(refs, op_reason, left)?;
            let right = check_bit_operand(refs, op_reason, right)?;
            let result = eval_binary_bitwise_array(refs, large, op_span, op, left, right)?;
            Ok(ValueWithImplications::simple(result))
        }
        _ => {
            let diag = DiagnosticError::new(
                "invalid operand types for bitwise operator",
                op_span,
                "for operator here",
            )
            .add_info(left.span, format!("left operand has type `{}`", left_ty.value_string(refs)))
            .add_info(right.span, format!("right operand has type `{}`", right_ty.value_string(refs)))
            .add_footer_hint("bitwise operators support `(bool, bool)`, `(int, int)`, `(Range, Range)`, `([_]bool, [_]bool)`, `(bool, [_]bool)` and `([_]bool, bool)`")
            .report(refs.diags);
            Err(diag)
        }
    }
}

/// Bitwise operation on integers, using the infinitely sign-extended two's complement representation.
///
/// This is lowered to the IR by expanding both operands to a common representation, converting them to bits,
/// applying the operation on the bits and converting back to an integer.
fn build_binary_int_bitwise_op(
    large: &mut IrLargeArena,
    op: IrBoolBinaryOp,
    left: HardwareInt,
    right: HardwareInt,
) -> HardwareInt {
    let result_range = multi_range_binary_bitwise(op, &left.ty, &right.ty);

    // the result of a bitwise operation always fits in the representation of the operands
    let combined_range = left
        .ty
        .enclosing_range()
        .cloned()
        .union(right.ty.enclosing_range().cloned());
    let repr_range = IntRepresentation::for_range(combined_range.as_ref()).range();
    let repr_ty = IrType::Int(repr_range.clone());

    let mut to_bits = |value: HardwareInt| {
        let value_range = value.ty.enclosing_range().cloned();
        let value_expanded = if value_range == repr_range {
            value.expr
        } else {
            large.push_expr(IrExpressionLarge::ExpandIntRange(repr_range.clone(), value.expr))
        };
        large.push_expr(IrExpressionLarge::ToBits(repr_ty.clone(), value_expanded))
    };
    let domain = left.domain.join(right.domain);
    let left_bits = to_bits(left);
    let right_bits = to_bits(right);

    let result_bits = large.push_expr(IrExpressionLarge::BoolBinaryArray(op, left_bits, right_bits));
    let result_repr = large.push_expr(IrExpressionLarge::FromBits(repr_ty, result_bits));
    let result_expr = large.push_expr(IrExpressionLarge::ConstrainIntRange(
        result_range.enclosing_range().cloned(),
        result_repr,
    ));

    HardwareInt {
        ty: result_range,
        domain,
        expr: result_expr,
    }
}

enum BitOperand {
    Scalar(MaybeCompile<bool, HardwareValue<TypeBool>>),
    Array(MaybeCompile<Vec<bool>, HardwareValue<BigUint>>),
}

fn check_bit_operand(
    refs: CompileRefs,
    op_reason: TypeContainsReason,
    value: Spanned<ValueWithImplications>,
) -> DiagResult<Spanned<BitOperand>> {
    let value_span = value.span;
    let operand = if matches!(value.inner.ty(), Type::Bool) {
        BitOperand::Scalar(check_type_is_bool(refs, op_reason, value)?.map_hardware(|v| v.value))
    } else {
        BitOperand::Array(check_type_is_bool_array(
            refs,
            op_reason,
            value.map_inner(|v| v.into_value()),
            None,
        )?)
    };
    Ok(Spanned::new(value_span, operand))
}

/// Bitwise operation where at least one of the operands is a bool array, scalar operands are broadcast.
fn eval_binary_bitwise_array(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_span: Span,
    op: IrBoolBinaryOp,
    left: Spanned<BitOperand>,
    right: Spanned<BitOperand>,
) -> DiagResult<Value> {
    let operand_len = |operand: &BitOperand| match operand {
        BitOperand::Scalar(_) => None,
        BitOperand::Array(MaybeCompile::Compile(v)) => Some(BigUint::from(v.len())),
        BitOperand::Array(MaybeCompile::Hardware(v)) => Some(v.ty.clone()),
    };

    // determine the result length
    let len = match (operand_len(&left.inner), operand_len(&right.inner)) {
        (None, None) => {
            return Err(refs
                .diags
                .report_error_internal(op_span, "expected at least one array operand"));
        }
        (Some(len), None) | (None, Some(len)) => len,
        (Some(left_len), Some(right_len)) => {
            if left_len != right_len {
                let diag = DiagnosticError::new(
                    "bitwise operator on arrays with different lengths",
                    op_span,
                    "for operator here",
                )
                .add_info(left.span, format!("left operand has length `{left_len}`"))
                .add_info(right.span, format!("right operand has length `{right_len}`"))
                .report(refs.diags);
                return Err(diag);
            }
            left_len
        }
    };

    // full compile-time evaluation
    let result_compile: Option<Vec<bool>> = match (&left.inner, &right.inner) {
        (BitOperand::Array(MaybeCompile::Compile(left)), BitOperand::Array(MaybeCompile::Compile(right))) => {
            Some(left.iter().zip(right).map(|(&l, &r)| op.eval_bool(l, r)).collect())
        }
        (&BitOperand::Scalar(MaybeCompile::Compile(left)), BitOperand::Array(MaybeCompile::Compile(right))) => {
            Some(right.iter().map(|&r| op.eval_bool(left, r)).collect())
        }
        (BitOperand::Array(MaybeCompile::Compile(left)), &BitOperand::Scalar(MaybeCompile::Compile(right))) => {
            Some(left.iter().map(|&l| op.eval_bool(l, right)).collect())
        }
        _ => None,
    };
    if let Some(result) = result_compile {
        let result = result.into_iter().map(CompileValue::new_bool).collect();
        return Ok(Value::Simple(SimpleCompileValue::Array(Arc::new(result))));
    }

    // hardware evaluation
    let mut to_hardware = |operand: BitOperand| -> (ValueDomain, IrExpression) {
        match operand {
            BitOperand::Scalar(MaybeCompile::Compile(v)) => (
                ValueDomain::CompileTime,
                large.push_expr(IrExpressionLarge::BoolFill(len.clone(), IrExpression::Bool(v))),
            ),
            BitOperand::Scalar(MaybeCompile::Hardware(v)) => (
                v.domain,
                large.push_expr(IrExpressionLarge::BoolFill(len.clone(), v.expr)),
            ),
            BitOperand::Array(MaybeCompile::Compile(v)) => {
                let elements = v
                    .into_iter()
                    .map(|b| IrArrayLiteralElement::Single(IrExpression::Bool(b)))
                    .collect();
                (
                    ValueDomain::CompileTime,
                    large.push_expr(IrExpressionLarge::ArrayLiteral(IrType::Bool, len.clone(), elements)),
                )
            }
            BitOperand::Array(MaybeCompile::Hardware(v)) => (v.domain, v.expr),
        }
    };
    let (left_domain, left_expr) = to_hardware(left.inner);
    let (right_domain, right_expr) = to_hardware(right.inner);

    Ok(Value::Hardware(HardwareValue {
        ty: HardwareType::Array(Arc::new(HardwareType::Bool), len),
        domain: left_domain.join(right_domain),
        expr: large.push_expr(IrExpressionLarge::BoolBinaryArray(op, left_expr, right_expr)),
    }))
}

fn eval_binary_bool(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
    op: IrBoolBinaryOp,
) -> DiagResult<ValueWithImplications> {
    let left = check_type_is_bool(refs, op_reason, left);
    let right = check_type_is_bool(refs, op_reason, right);
    let (left, right) = (left?, right?);

    Ok(eval_binary_bool_typed(large, op, left, right).into())
}

pub fn eval_binary_bool_typed(
    large: &mut IrLargeArena,
    op: IrBoolBinaryOp,
    left: MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>,
    right: MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>,
) -> MaybeCompile<bool, HardwareValueWithImplications<TypeBool>> {
    match (left, right) {
        // full compile-time eval
        (MaybeCompile::Compile(left), MaybeCompile::Compile(right)) => MaybeCompile::Compile(op.eval_bool(left, right)),

        // partial compile-time eval
        (MaybeCompile::Compile(left), MaybeCompile::Hardware(right)) => {
            build_unary_bool_gate(large, right, |b| op.eval_bool(left, b))
        }
        (MaybeCompile::Hardware(left), MaybeCompile::Compile(right)) => {
            build_unary_bool_gate(large, left, |b| op.eval_bool(b, right))
        }

        // full hardware
        // TODO these could be improved for multi-integer ranges,
        //   we actually need to join/intersect allowed ranges per version
        (MaybeCompile::Hardware(left), MaybeCompile::Hardware(right)) => {
            let expr = HardwareValue {
                ty: TypeBool,
                domain: left.value.domain.join(right.value.domain),
                expr: large.push_expr(IrExpressionLarge::BoolBinaryScalar(
                    op,
                    left.value.expr,
                    right.value.expr,
                )),
            };

            let implications = match op {
                IrBoolBinaryOp::And => BoolImplications {
                    if_true: vec_concat([left.implications.if_true, right.implications.if_true]),
                    if_false: vec![],
                },
                IrBoolBinaryOp::Or => BoolImplications {
                    if_true: vec![],
                    if_false: vec_concat([left.implications.if_false, right.implications.if_false]),
                },
                IrBoolBinaryOp::Xor => BoolImplications::new(None),
            };

            MaybeCompile::Hardware(HardwareValueWithImplications {
                value: expr,
                version: None,
                implications,
            })
        }
    }
}

fn build_unary_bool_gate(
    large: &mut IrLargeArena,
    value: HardwareValueWithImplications<TypeBool>,
    op: impl Fn(bool) -> bool,
) -> MaybeCompile<bool, HardwareValueWithImplications<TypeBool>> {
    match (op(false), op(true)) {
        // constants
        (false, false) => MaybeCompile::Compile(false),
        (true, true) => MaybeCompile::Compile(true),
        // pass gate
        (false, true) => MaybeCompile::Hardware(value),
        // not gate
        (true, false) => MaybeCompile::Hardware(HardwareValueWithImplications {
            value: HardwareValue {
                ty: TypeBool,
                domain: value.value.domain,
                expr: large.push_expr(IrExpressionLarge::BoolNot(value.value.expr)),
            },
            version: None,
            implications: value.implications.invert(),
        }),
    }
}

fn eval_binary_eq(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    op_span: Span,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
    eq: bool,
) -> DiagResult<ValueWithImplications> {
    let left_ty = left.inner.ty();
    let right_ty = right.inner.ty();

    // check that both operand types are individually valid
    let mut operands_valid = Ok(());
    for (operand_span, operand_ty) in [(left.span, &left_ty), (right.span, &right_ty)] {
        if !valid_type_for_eq(refs, operand_ty) {
            let diag = DiagnosticError::new(
                "invalid operand type for equality operator",
                operand_span,
                format!("operand has type `{}`", operand_ty.value_string(refs)),
            )
            .add_info(op_span, "for operator here")
            .report(refs.diags);
            operands_valid = Err(diag);
        }
    }
    operands_valid?;

    // check that the common type is still valid
    let common_ty = left_ty.union(&right_ty);
    if !valid_type_for_eq(refs, &common_ty) {
        let diag = DiagnosticError::new(
            "mismatched operand types for equality operator",
            op_span,
            "for operator here",
        )
        .add_info(
            left.span,
            format!("left operand has type `{}`", left_ty.value_string(refs)),
        )
        .add_info(
            right.span,
            format!("right operand has type `{}`", right_ty.value_string(refs)),
        )
        .add_footer_hint("both operands of an equality operator must have compatible types")
        .report(refs.diags);
        return Err(diag);
    }

    // recursively compare the values
    let result = eval_binary_eq_recurse(refs, large, op_reason, op_span, left, right, eq)?;
    Ok(result.into())
}

/// Whether values of the given type can be compared for equality.
fn valid_type_for_eq(refs: CompileRefs, ty: &Type) -> bool {
    let elab = &refs.shared.elaboration_arenas;
    match ty {
        // basic types are valid
        Type::Type
        | Type::Bool
        | Type::String
        | Type::Int(_)
        | Type::Range
        | Type::Function
        | Type::Module
        | Type::Interface
        | Type::InterfaceArray(_)
        | Type::InterfaceView
        | Type::InterfaceViewArray(_)
        | Type::HierarchyNode => true,

        // this comes up for empty arrays and for values that are undefined after merging flows, allow it
        Type::Undefined => true,

        // these could maybe be compared but are sketchy, so don't allow them for now
        Type::Any | Type::Ref(_) | Type::RefInterface(_, _) => false,

        // compound types are valid iff their subtypes are
        Type::Array(inner, len) => len.is_some() && valid_type_for_eq(refs, inner),
        Type::Tuple(inner) => inner
            .as_ref()
            .is_some_and(|inner| inner.iter().all(|ty| valid_type_for_eq(refs, ty))),
        &Type::Struct(ty_struct) => elab
            .struct_info(ty_struct)
            .fields
            .values()
            .all(|(_, field_ty)| valid_type_for_eq(refs, &field_ty.inner)),
        &Type::Enum(ty_enum) => elab.enum_info(ty_enum).variants.values().all(|variant| {
            variant
                .payload_ty
                .as_ref()
                .is_none_or(|payload_ty| valid_type_for_eq(refs, &payload_ty.inner))
        }),
    }
}

/// Check whether two values with valid and matching types are equal (`eq = true`) or not equal (`eq = false`).
///
/// Compile-time values are compared at compile time, compound values are compared recursively
///   and the remaining values are converted to a common hardware type and compared in hardware.
fn eval_binary_eq_recurse(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    op_span: Span,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
    eq: bool,
) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
    // special cases for bool and int to track implications
    match (&left.inner.ty(), &right.inner.ty()) {
        (Type::Bool, Type::Bool) => {
            let left = check_type_is_bool(refs, op_reason, left)?;
            let right = check_type_is_bool(refs, op_reason, right)?;

            let result = match (left, right) {
                (MaybeCompile::Compile(left), MaybeCompile::Compile(right)) => {
                    MaybeCompile::Compile((left == right) == eq)
                }
                (MaybeCompile::Compile(c), MaybeCompile::Hardware(v))
                | (MaybeCompile::Hardware(v), MaybeCompile::Compile(c)) => {
                    build_unary_bool_gate(large, v, |b| (b == c) == eq)
                }
                (MaybeCompile::Hardware(left), MaybeCompile::Hardware(right)) => {
                    let op = if eq { IrBoolCompareOp::Eq } else { IrBoolCompareOp::Neq };
                    let expr = IrExpressionLarge::BoolCompareScalar(op, left.value.expr, right.value.expr);
                    let value = HardwareValue {
                        ty: TypeBool,
                        domain: left.value.domain.join(right.value.domain),
                        expr: large.push_expr(expr),
                    };
                    MaybeCompile::Hardware(HardwareValueWithImplications::simple(value))
                }
            };
            return Ok(result);
        }
        (Type::Int(_), Type::Int(_)) => {
            let op = if eq { IrIntCompareOp::Eq } else { IrIntCompareOp::Neq };
            return eval_binary_int_compare(refs, large, op_reason, left, right, op);
        }
        _ => {
            // fallthrough into general comparison
        }
    }

    // try full compile-time evaluation
    let left = left.map_inner(ValueWithImplications::into_value);
    let right = right.map_inner(ValueWithImplications::into_value);
    if let (Ok(left), Ok(right)) = (
        CompileValue::try_from(&left.inner),
        CompileValue::try_from(&right.inner),
    ) {
        return Ok(MaybeCompile::Compile((left == right) == eq));
    }

    // handle hardware and compound values
    let err_internal = |msg: &str| refs.diags.report_error_internal(op_span, msg);
    match (&left.inner, &right.inner) {
        // at least one side is hardware, compare in hardware
        (Value::Hardware(_), _) | (_, Value::Hardware(_)) => {
            eval_binary_eq_hardware(refs, large, op_span, left.as_ref(), right.as_ref(), eq)
        }

        // compound values, recurse into their elements
        (Value::Compound(left_inner), Value::Compound(right_inner)) => match (left_inner, right_inner) {
            (MixedCompoundValue::Tuple(left_inner), MixedCompoundValue::Tuple(right_inner)) => {
                if left_inner.len() != right_inner.len() {
                    return Err(err_internal("tuple equality with mismatched lengths"));
                }
                eval_binary_eq_recurse_all(
                    refs,
                    large,
                    op_reason,
                    op_span,
                    left.span,
                    right.span,
                    zip_eq(left_inner, right_inner),
                    eq,
                )
            }
            (MixedCompoundValue::Struct(left_inner), MixedCompoundValue::Struct(right_inner)) => {
                if left_inner.ty != right_inner.ty || left_inner.fields.len() != right_inner.fields.len() {
                    return Err(err_internal("struct equality with mismatched types"));
                }
                eval_binary_eq_recurse_all(
                    refs,
                    large,
                    op_reason,
                    op_span,
                    left.span,
                    right.span,
                    zip_eq(&left_inner.fields, &right_inner.fields),
                    eq,
                )
            }
            (MixedCompoundValue::Enum(left_inner), MixedCompoundValue::Enum(right_inner)) => {
                if left_inner.ty != right_inner.ty {
                    return Err(err_internal("enum equality with mismatched types"));
                }
                if left_inner.variant != right_inner.variant {
                    return Ok(MaybeCompile::Compile(!eq));
                }
                match (&left_inner.payload, &right_inner.payload) {
                    (None, None) => Ok(MaybeCompile::Compile(eq)),
                    (Some(left_payload), Some(right_payload)) => eval_binary_eq_recurse_all(
                        refs,
                        large,
                        op_reason,
                        op_span,
                        left.span,
                        right.span,
                        std::iter::once((&**left_payload, &**right_payload)),
                        eq,
                    ),
                    (None, Some(_)) | (Some(_), None) => Err(err_internal("payload presence mismatch")),
                }
            }

            // these only support compile-time equality, which was already handled
            (MixedCompoundValue::String(_), MixedCompoundValue::String(_))
            | (MixedCompoundValue::Range(_), MixedCompoundValue::Range(_)) => {
                let diag = DiagnosticError::new(
                    "equality between strings or ranges is only supported for compile-time values",
                    op_span,
                    "for comparison here",
                )
                .report(refs.diags);
                Err(diag)
            }
            (MixedCompoundValue::BoundMethod(left_inner), MixedCompoundValue::BoundMethod(right_inner)) => {
                let BoundMethod {
                    self_type: left_self_type,
                    self_value: left_self_value,
                    method: left_method,
                } = left_inner;
                let BoundMethod {
                    self_type: right_self_type,
                    self_value: right_self_value,
                    method: right_method,
                } = right_inner;

                if left_self_type != right_self_type || left_method != right_method {
                    return Ok(MaybeCompile::Compile(!eq));
                }
                eval_binary_eq_recurse_all(
                    refs,
                    large,
                    op_reason,
                    op_span,
                    left.span,
                    right.span,
                    std::iter::once((&**left_self_value, &**right_self_value)),
                    eq,
                )
            }

            // mismatches, these should have been rejected by the type check
            (
                MixedCompoundValue::String(_)
                | MixedCompoundValue::Range(_)
                | MixedCompoundValue::Tuple(_)
                | MixedCompoundValue::Struct(_)
                | MixedCompoundValue::Enum(_)
                | MixedCompoundValue::BoundMethod(_),
                _,
            ) => Err(err_internal("equality between mismatched compound values")),
        },

        // simple values are always compile-time, so this was already handled
        (Value::Simple(_), Value::Simple(_)) => Err(err_internal("equality between simple values not handled")),

        // mismatches, these should have been rejected by the type check
        (Value::Simple(_), Value::Compound(_)) | (Value::Compound(_), Value::Simple(_)) => {
            Err(err_internal("equality between mismatched simple and compound values"))
        }
    }
}

/// Compare multiple pairs of values, combining the results.
/// The values are equal if all pairs are equal, and not equal if any pair is not equal.
fn eval_binary_eq_recurse_all<'v>(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    op_span: Span,
    left_span: Span,
    right_span: Span,
    pairs: impl Iterator<Item = (&'v Value, &'v Value)>,
    eq: bool,
) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
    let combine_op = if eq { IrBoolBinaryOp::And } else { IrBoolBinaryOp::Or };

    let mut result = MaybeCompile::Compile(eq);
    for (left, right) in pairs {
        let left = Spanned::new(left_span, ValueWithImplications::simple(left.clone()));
        let right = Spanned::new(right_span, ValueWithImplications::simple(right.clone()));
        let inner = eval_binary_eq_recurse(refs, large, op_reason, op_span, left, right, eq)?;
        result = eval_binary_bool_typed(large, combine_op, result, inner);
    }
    Ok(result)
}

/// Compare two values in hardware, by converting them to a common hardware type and comparing their bits.
fn eval_binary_eq_hardware(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_span: Span,
    left: Spanned<&Value>,
    right: Spanned<&Value>,
    eq: bool,
) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
    let left_ty = left.inner.ty();
    let right_ty = right.inner.ty();
    let ty_hw = left_ty
        .union(&right_ty)
        .as_hardware_type(&refs.shared.elaboration_arenas)
        .map_err(|_: NonHardwareType| {
            DiagnosticError::new(
                "equality on non-compile-time values requires hardware types",
                op_span,
                "for operator here",
            )
            .add_info(
                left.span,
                format!("left value has type `{}`", left_ty.value_string(refs)),
            )
            .add_info(
                right.span,
                format!("right value has type `{}`", right_ty.value_string(refs)),
            )
            .report(refs.diags)
        })?;

    // zero-width types only have a single possible value
    let ty_ir = ty_hw.as_ir(refs);
    if ty_ir.size_bits() == BigUint::ZERO {
        return Ok(MaybeCompile::Compile(eq));
    }

    let left = left
        .inner
        .as_hardware_value_unchecked(refs, large, left.span, ty_hw.clone())?;
    let right = right
        .inner
        .as_hardware_value_unchecked(refs, large, right.span, ty_hw)?;

    // compare the bit representations
    let op = if eq { IrBoolCompareOp::Eq } else { IrBoolCompareOp::Neq };
    let left_bits = large.push_expr(IrExpressionLarge::ToBits(ty_ir.clone(), left.expr));
    let right_bits = large.push_expr(IrExpressionLarge::ToBits(ty_ir, right.expr));
    let expr = large.push_expr(IrExpressionLarge::BoolCompareArray(op, left_bits, right_bits));

    let value = HardwareValue {
        ty: TypeBool,
        domain: left.domain.join(right.domain),
        expr,
    };
    Ok(MaybeCompile::Hardware(HardwareValueWithImplications::simple(value)))
}

fn eval_binary_int_compare(
    refs: CompileRefs,
    large: &mut IrLargeArena,
    op_reason: TypeContainsReason,
    left: Spanned<ValueWithImplications>,
    right: Spanned<ValueWithImplications>,
    op: IrIntCompareOp,
) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
    let left_int = check_type_is_int(
        refs,
        op_reason,
        left.clone().map_inner(ValueWithImplications::into_value),
    );
    let right_int = check_type_is_int(
        refs,
        op_reason,
        right.clone().map_inner(ValueWithImplications::into_value),
    );
    let left_int = left_int?;
    let right_int = right_int?;

    // TODO spans are getting unnecessarily complicated, eg. why does this try to propagate spans?
    match pair_compile_int(left_int, right_int) {
        MaybeCompile::Compile((left, right)) => Ok(MaybeCompile::Compile(op.eval(&left, &right))),
        MaybeCompile::Hardware((left_int, right_int)) => {
            let lv = match left.inner {
                ValueWithImplications::Simple(_) | ValueWithImplications::Compound(_) => None,
                ValueWithImplications::Hardware(v) => v.version,
            };
            let rv = match right.inner {
                ValueWithImplications::Simple(_) | ValueWithImplications::Compound(_) => None,
                ValueWithImplications::Hardware(v) => v.version,
            };

            // TODO warning if the result is always true/false (depending on the ranges)
            //   or maybe just return a compile-time value again?
            // build implications
            let lr = left_int.ty.enclosing_range();
            let rr = right_int.ty.enclosing_range();
            let implications = match op {
                IrIntCompareOp::Lt => implications_lt(false, lv, lr, rv, rr),
                IrIntCompareOp::Lte => implications_lt(true, lv, lr, rv, rr),
                IrIntCompareOp::Gt => implications_lt(false, rv, rr, lv, lr),
                IrIntCompareOp::Gte => implications_lt(true, rv, rr, lv, lr),
                IrIntCompareOp::Eq => implications_eq(lv, lr, rv, rr),
                IrIntCompareOp::Neq => implications_eq(lv, lr, rv, rr).invert(),
            };

            // build the resulting expression
            let result = HardwareValue {
                ty: TypeBool,
                domain: left_int.domain.join(right_int.domain),
                expr: large.push_expr(IrExpressionLarge::IntCompare(op, left_int.expr, right_int.expr)),
            };
            Ok(MaybeCompile::Hardware(HardwareValueWithImplications {
                value: result,
                version: None,
                implications,
            }))
        }
    }
}

fn build_unary_int_neg(large: &mut IrLargeArena, value: HardwareInt) -> HardwareInt {
    let range = multi_range_unary_neg(&value.ty);
    let result_expr = IrExpressionLarge::IntArithmetic(
        IrIntArithmeticOp::Sub,
        range.enclosing_range().cloned(),
        IrExpression::Int(BigInt::ZERO),
        value.expr,
    );
    HardwareInt {
        ty: range,
        domain: value.domain,
        expr: large.push_expr(result_expr),
    }
}

fn build_binary_int_arithmetic_op(
    op: IrIntArithmeticOp,
    large: &mut IrLargeArena,
    range: ClosedNonEmptyMultiRange<BigInt>,
    left: HardwareInt,
    right: HardwareInt,
) -> HardwareInt {
    let result_expr = IrExpressionLarge::IntArithmetic(op, range.enclosing_range().cloned(), left.expr, right.expr);
    HardwareInt {
        ty: range,
        domain: left.domain.join(right.domain),
        expr: large.push_expr(result_expr),
    }
}

// TODO move these to the implications module
// TODO rework implications entirely first
fn implications_lt(
    eq: bool,
    left: Option<ValueVersion>,
    left_range: ClosedNonEmptyRange<&BigInt>,
    right: Option<ValueVersion>,
    right_range: ClosedNonEmptyRange<&BigInt>,
) -> BoolImplications {
    let mut if_true = vec![];
    let mut if_false = vec![];

    if let Some(left) = left {
        if_true.push(implication_lt_is(true, eq, left, right_range));
        if_false.push(implication_lt_is(false, eq, left, right_range));
    }

    #[allow(clippy::nonminimal_bool)]
    if let Some(right) = right {
        // flip left/right by inverting the eval and eq flags
        if_true.push(implication_lt_is(!true, !eq, right, left_range));
        if_false.push(implication_lt_is(!false, !eq, right, left_range));
    }

    BoolImplications { if_true, if_false }
}

/// Construct the implication for `left <(=) right == eval`. `eq` indicates whether the comparison is `<` or `<=`.
fn implication_lt_is(eval: bool, eq: bool, left: ValueVersion, right: ClosedNonEmptyRange<&BigInt>) -> Implication {
    let range = match (eval, eq) {
        // left <= right
        (true, true) => Range {
            start: None,
            end: Some(right.end.clone()),
        },
        // left < right
        (true, false) => Range {
            start: None,
            end: Some(right.end - 1),
        },
        // left > right
        (false, true) => Range {
            start: Some(right.start + 1),
            end: None,
        },
        // left >= right
        (false, false) => Range {
            start: Some(right.start.clone()),
            end: None,
        },
    };
    Implication::new_int(left, MultiRange::from(range))
}

fn implications_eq(
    left: Option<ValueVersion>,
    left_range: ClosedNonEmptyRange<&BigInt>,
    right: Option<ValueVersion>,
    right_range: ClosedNonEmptyRange<&BigInt>,
) -> BoolImplications {
    let mut if_true = vec![];
    let mut if_false = vec![];

    if let Some(left) = left {
        if_true.push(Implication::new_int(
            left,
            MultiRange::from(Range::from(right_range.cloned())),
        ));

        if let Some(right_single) = right_range.as_single() {
            if_false.push(Implication::new_int(
                left,
                MultiRange::from(Range::single(right_single.clone())).complement(),
            ));
        }
    }

    if let Some(right) = right {
        if_true.push(Implication::new_int(
            right,
            MultiRange::from(Range::from(left_range.cloned())),
        ));

        if let Some(left_single) = left_range.as_single() {
            if_false.push(Implication::new_int(
                right,
                MultiRange::from(Range::single(left_single.clone())).complement(),
            ));
        }
    }

    BoolImplications { if_true, if_false }
}

fn array_literal_combine_values(
    refs: CompileRefs,
    flow: &mut impl Flow,
    large: &mut IrLargeArena,
    expr_span: Span,
    values: Vec<ArrayLiteralElement<Spanned<Value>>>,
) -> DiagResult<Value> {
    let diags = refs.diags;
    let elab = &refs.shared.elaboration_arenas;

    // check that spread operator only deals with arrays
    let mut any_err = Ok(());
    for v in &values {
        match v {
            ArrayLiteralElement::Single(_) => {}
            &ArrayLiteralElement::Spread(span_op, ref v) => {
                let reason = TypeContainsReason::SpreadOperator(span_op);
                let res = check_type_contains_value(refs, reason, &Type::Array(Arc::new(Type::Any), None), v.as_ref());
                any_err = any_err.and(res);
            }
        }
    }
    any_err?;

    // figure out if there are any non-compile values
    let first_non_compile = values
        .iter()
        .find(|v| CompileValue::try_from(&v.value().inner).is_err())
        .map(|v| v.value());

    if let Some(first_non_compile) = first_non_compile {
        // at least one non-compile, turn everything into IR
        let ty_inner = values
            .iter()
            .map(|v| match v {
                ArrayLiteralElement::Single(v) => Ok(v.inner.ty()),
                &ArrayLiteralElement::Spread(span_spread, ref v) => {
                    let v_ty = v.inner.ty();
                    match v_ty {
                        Type::Array(ty_inner, _len) => Ok(Arc::unwrap_or_clone(ty_inner)),
                        _ => Err(diags.report_error_internal(span_spread, "spread operator expected array")),
                    }
                }
            })
            .try_fold(Type::Undefined, |a, t| Ok(a.union(&t?)))?;

        // TODO improve error message:
        //   * if mix of types that cases result type any, report pair
        //   * if any element non-hardware, report that element
        let ty_inner_hw = ty_inner.as_hardware_type(elab).map_err(|_| {
            let message = format!(
                "hardware array literal has inner type `{}` which is not representable in hardware",
                ty_inner.value_string(refs)
            );
            DiagnosticError::new(
                "hardware array type needs to be representable in hardware",
                expr_span,
                message,
            )
            .add_info(
                first_non_compile.span,
                format!(
                    "first non-compile value with type `{}`",
                    first_non_compile.inner.ty().value_string(refs)
                ),
            )
            .report(diags)
        })?;
        let ty_inner_hw = Arc::new(ty_inner_hw);

        let mut result_domain = ValueDomain::CompileTime;
        let mut result_len = BigUint::ZERO;
        let mut result_exprs = Vec::with_capacity(values.len());

        for elem in values {
            let (elem_len, elem_domain, elem_expr) = match elem {
                ArrayLiteralElement::Single(elem_inner) => {
                    let elem_domain = elem_inner.inner.domain();
                    let elem_expr =
                        elem_inner
                            .inner
                            .as_ir_expression_unchecked(refs, large, elem_inner.span, &ty_inner_hw)?;

                    (BigUint::ONE, elem_domain, IrArrayLiteralElement::Single(elem_expr))
                }
                ArrayLiteralElement::Spread(_, elem_inner) => {
                    let elem_len = unwrap_match!(elem_inner.inner.ty(), Type::Array(_, len) => len)
                        .expect("array value has known length");
                    let elem_domain = elem_inner.inner.domain();
                    let elem_expr = elem_inner.inner.as_ir_expression_unchecked(
                        refs,
                        large,
                        elem_inner.span,
                        &HardwareType::Array(ty_inner_hw.clone(), elem_len.clone()),
                    )?;

                    (elem_len, elem_domain, IrArrayLiteralElement::Spread(elem_expr))
                }
            };

            result_len += elem_len;
            result_domain = result_domain.join(elem_domain);
            result_exprs.push(elem_expr);
        }

        let result_expr = IrExpressionLarge::ArrayLiteral(ty_inner_hw.as_ir(refs), result_len.clone(), result_exprs);
        let result_value = HardwareValue {
            ty: HardwareType::Array(ty_inner_hw, result_len),
            domain: result_domain,
            expr: large.push_expr(result_expr),
        };

        // store result in variable to prevent large duplicate expressions
        let flow = flow.require_hardware(expr_span, "array literal containing hardware values")?;
        let result_value = flow.store_hardware_value_in_new_ir_variable(refs, expr_span, None, result_value);

        Ok(Value::Hardware(result_value.map_expression(IrExpression::Variable)))
    } else {
        // all compile, create compile value
        let mut result = Vec::with_capacity(values.len());
        for elem in values {
            match elem {
                ArrayLiteralElement::Single(elem_inner) => {
                    let elem_inner = CompileValue::try_from(&elem_inner.inner).unwrap();
                    result.push(elem_inner);
                }
                ArrayLiteralElement::Spread(span_spread, elem_inner) => {
                    let elem_inner = CompileValue::try_from(&elem_inner.inner).unwrap();
                    let elem_inner_array = match elem_inner {
                        CompileValue::Simple(SimpleCompileValue::Array(elem_inner)) => elem_inner,
                        _ => return Err(diags.report_error_internal(span_spread, "spread operator expected array")),
                    };
                    result.extend(elem_inner_array.iter().cloned())
                }
            }
        }
        Ok(Value::Simple(SimpleCompileValue::Array(Arc::new(result))))
    }
}

fn message_range_or_single(name: &str, range: &impl AnyMultiRange<BigInt>, suffix_if_multiple: Option<&str>) -> String {
    let (suffix_sep, suffix) = match suffix_if_multiple {
        None => ("", ""),
        Some(suffix) => (" ", suffix),
    };

    let range = range.as_multi_range();
    match range.as_single() {
        None => format!("{name} has range {range}{suffix_sep}{suffix}"),
        Some(single) => format!("{name} is {single}"),
    }
}

const HINT_RANGE_USE_START_LENGTH: &str = "to construct ranges that are valid by design, use the `start+..len` syntax";

fn try_vec_with_capacity<T>(diags: &Diagnostics, span: Span, capacity: usize) -> DiagResult<Vec<T>> {
    let mut result = Vec::new();
    result.try_reserve_exact(capacity).map_err(|_| {
        diags.report_error_simple(
            "array too large",
            span,
            format!("array with length `{capacity}` cannot be allocated"),
        )
    })?;
    Ok(result)
}
