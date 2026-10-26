use crate::front::check::{TypeContainsReason, check_hardware_type_for_bit_operation, check_type_contains_value};
use crate::front::compile::{CompileItemContext, CompileRefs, resolve_import_final};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::ValueDomain;
use crate::front::function::{
    FunctionBits, FunctionBitsKind, FunctionBody, FunctionValue, error_cannot_infer_generic_params,
    error_unique_mismatch,
};
use crate::front::implication::{HardwareValueWithImplications, ValueWithImplications};
use crate::front::item::{ElaboratedInterfaceView, FunctionItemBody};
use crate::front::types::{HardwareType, Type, Typed};
use crate::front::value::{
    BoundMethod, CompileCompoundValue, CompileValue, EnumValue, HardwareUInt, HardwareValue, MaybeCompile,
    MixedCompoundValue, NotCompile, SimpleCompileValue, Value, ValueCommon,
};
use crate::mid::ir::{IrExpression, IrExpressionLarge, IrLargeArena, IrSignals, IrVariables};
use crate::mid::steps::{InvalidScalarAfterSlice, IrTargetStep, IrTargetStepScalar, IrTargetStepSlice, IrTargetSteps};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::ResultExt;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::data::VecExt;
use crate::util::intern::Id;
use crate::util::iter::IterExt;
use crate::util::range::ClosedNonEmptyRange;
use crate::util::range_multi::{AnyMultiRange, ClosedNonEmptyMultiRange};
use itertools::{Either, Itertools, zip_eq};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct TargetSteps<S = TargetStep> {
    pub steps: Vec<SpannedStep<S>>,
}

#[derive(Debug, Clone)]
pub struct SpannedStep<S> {
    /// Span of the entire expression, base and step included.
    pub span_full: Span,
    /// Span of the step part of the expression.
    pub span_step: Span,
    /// The step itself.
    pub step: S,
}

pub type TargetStep = MaybeCompile<TargetStepCompile, TargetStepHardware>;

#[derive(Debug, Clone)]
pub enum TargetStepCompile {
    ArrayIndex(BigUint),
    ArraySlice { start: BigUint, length: Option<BigUint> },
    DotIndexInt(BigUint),
    DotIndexId(Id),
}

#[derive(Debug, Clone)]
pub enum TargetStepHardware {
    ArrayIndex(HardwareUInt),
    ArraySlice { start: HardwareUInt, length: BigUint },
}

impl<S> TargetSteps<S> {
    pub fn new(steps: Vec<SpannedStep<S>>) -> Self {
        Self { steps }
    }

    pub fn single(step: SpannedStep<S>) -> Self {
        Self::new(vec![step])
    }

    pub fn push(&mut self, step: SpannedStep<S>) {
        self.steps.push(step);
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

#[derive(Debug, Copy, Clone)]
struct EncounteredAny;

#[derive(Debug, Copy, Clone)]
struct EncounteredUnknown;

trait IrStepsBuilder {
    fn push(&mut self, step: IrTargetStep) -> Result<(), InvalidScalarAfterSlice>;
}

struct IrTargetStepsBuilder<'a> {
    large: &'a mut IrLargeArena,
    signals: &'a IrSignals,
    variables: &'a IrVariables,

    steps: IrTargetSteps,
}

impl IrStepsBuilder for IrTargetStepsBuilder<'_> {
    fn push(&mut self, step: IrTargetStep) -> Result<(), InvalidScalarAfterSlice> {
        self.steps.push(self.large, self.signals, self.variables, step)
    }
}

struct IgnoreBuilder;

impl IrStepsBuilder for IgnoreBuilder {
    fn push(&mut self, step: IrTargetStep) -> Result<(), InvalidScalarAfterSlice> {
        let _ = step;
        Ok(())
    }
}

impl TargetSteps<TargetStep> {
    /// A suggestion for RHS evaluation, not a write constraint. Inspect declarations only:
    /// the receiver need not have a value yet, and its contents can change on the RHS.
    pub fn assignment_expected_type(&self, refs: CompileRefs, mut ty: Type) -> Type {
        for step in &self.steps {
            ty = match (&step.step, ty) {
                (
                    TargetStep::Compile(TargetStepCompile::ArrayIndex(_))
                    | TargetStep::Hardware(TargetStepHardware::ArrayIndex(_)),
                    Type::Array(inner, _),
                ) => (*inner).clone(),
                (TargetStep::Compile(TargetStepCompile::ArraySlice { start, length }), Type::Array(inner, len)) => {
                    let len = length
                        .clone()
                        .or_else(|| len.and_then(|len| BigUint::try_from(len - start).ok()));
                    Type::Array(inner, len)
                }
                (TargetStep::Hardware(TargetStepHardware::ArraySlice { length, .. }), Type::Array(inner, _)) => {
                    Type::Array(inner, Some(length.clone()))
                }
                (TargetStep::Compile(TargetStepCompile::DotIndexInt(index)), Type::Tuple(Some(fields))) => index
                    .as_usize_if_lt(fields.len())
                    .map_or(Type::Any, |index| fields[index].clone()),
                (TargetStep::Compile(TargetStepCompile::DotIndexId(id)), Type::Struct(elab)) => {
                    let info = refs.shared.elaboration_arenas.struct_info(elab);
                    match info.fields.get(id) {
                        Some(field) if field.ref_.is_some() => match &field.ty.inner {
                            Type::Ref(inner) => (**inner).clone(),
                            _ => Type::Any,
                        },
                        Some(field) => field.ty.inner.clone(),
                        None => Type::Any,
                    }
                }
                _ => Type::Any,
            };
        }
        ty
    }

    pub fn try_as_compile(&self) -> Result<TargetSteps<&TargetStepCompile>, NotCompile> {
        let steps = self
            .steps
            .iter()
            .map(|s| match &s.step {
                MaybeCompile::Compile(s_compile) => Ok(SpannedStep {
                    span_full: s.span_full,
                    span_step: s.span_step,
                    step: s_compile,
                }),
                MaybeCompile::Hardware(_) => Err(NotCompile),
            })
            .try_collect_vec()?;
        Ok(TargetSteps { steps })
    }

    pub fn apply_to_expected_type(&self, refs: CompileRefs, ty: Spanned<Type>) -> DiagResult<Type> {
        let (ty, _) = self.apply_to_type_impl(refs, ty, IgnoreBuilder)?;
        Ok(ty)
    }

    pub fn apply_to_hardware_type(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        signals: &IrSignals,
        variables: &IrVariables,
        ty: Spanned<&HardwareType>,
    ) -> DiagResult<(HardwareType, IrTargetSteps)> {
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        // call common utility
        let builder = IrTargetStepsBuilder {
            large,
            signals,
            variables,
            steps: IrTargetSteps::new(),
        };
        let (result_ty, builder) = self.apply_to_type_impl(refs, ty.map_inner(HardwareType::as_type), builder)?;

        // map type back
        let result_ty_hw = result_ty.as_hardware_type(elab).map_err(|_| {
            diags.report_error_internal(
                ty.span,
                "applying access steps to hardware type should result in hardware type again",
            )
        })?;

        // extract steps
        let builder = builder.map_err(|e: Either<EncounteredAny, EncounteredUnknown>| {
            diags.report_error_internal(ty.span, format!("applying steps to hardware type failed: {e:?}"))
        })?;
        let steps = builder.steps;

        Ok((result_ty_hw, steps))
    }

    pub fn for_each_domain(&self, mut f: impl FnMut(Spanned<ValueDomain>)) {
        for step in &self.steps {
            let &d = match &step.step {
                TargetStep::Compile(_) => &ValueDomain::CompileTime,
                TargetStep::Hardware(step) => match step {
                    TargetStepHardware::ArrayIndex(index) => &index.domain,
                    TargetStepHardware::ArraySlice { start, length: _ } => &start.domain,
                },
            };
            f(Spanned::new(step.span_step, d));
        }
    }

    /// Return the result type after applying the steps to the given type.
    /// This can be used to get the type of step expressions but also the target type for an assignment with steps.
    ///
    /// This function also checks index and slice ranges for validity,
    /// reporting proper diagnostics if they are out of bounds.
    ///
    /// Applying any step to [Type::Any] will return [Type::Any] and [EncounteredAny]. This is
    /// useful to get the inferred type for assignments, once we encounter Any the result type is also Any.
    fn apply_to_type_impl<B: IrStepsBuilder>(
        &self,
        refs: CompileRefs,
        ty: Spanned<Type>,
        builder: B,
    ) -> DiagResult<(Type, Result<B, Either<EncounteredAny, EncounteredUnknown>>)> {
        let diags = refs.diags;
        let TargetSteps { steps } = self;

        let mut steps_builder = Ok(builder);
        let mut curr_ty = ty;

        for step in steps {
            // stop once we encounter Type::Any
            if matches!(curr_ty.inner, Type::Any) {
                return Ok((Type::Any, Err(Either::Left(EncounteredAny))));
            }

            // map step to IR and get the next type
            let step_span = step.span_step;
            let check_type_is_array = |step_is_slice: bool| {
                let (inner, len) = check_type_is_array(refs, curr_ty.as_ref(), step_span, step_is_slice)?;
                let len = Spanned::new(curr_ty.span, len);
                Ok((inner, len))
            };

            let (step_ir, next_ty) = match &step.step {
                TargetStep::Compile(step) => match step {
                    TargetStepCompile::ArrayIndex(index) => {
                        let (array_inner, array_len) = check_type_is_array(false)?;
                        check_range_index(
                            diags,
                            Spanned::new(step_span, &ClosedNonEmptyMultiRange::single(index.clone())),
                            array_len,
                        )?;

                        let step_ir = array_len
                            .inner
                            .map(|_| {
                                IrTargetStep::Scalar(IrTargetStepScalar::ArrayIndex(IrExpression::Int(index.into())))
                            })
                            .ok_or(EncounteredUnknown);

                        (step_ir, array_inner.as_ref().clone())
                    }
                    TargetStepCompile::ArraySlice {
                        start: slice_start,
                        length: slice_length,
                    } => {
                        let (array_inner, array_len) = check_type_is_array(true)?;

                        let slice_len = check_range_slice(
                            diags,
                            Spanned::new(step_span, &ClosedNonEmptyMultiRange::single(slice_start.clone())),
                            slice_length
                                .as_ref()
                                .map(|slice_length| Spanned::new(step_span, slice_length)),
                            array_len,
                        )?;

                        match slice_len {
                            None => (Err(EncounteredUnknown), Type::Array(Arc::clone(array_inner), None)),
                            Some(slice_len) => {
                                let step_ir = IrTargetStep::Slice(IrTargetStepSlice {
                                    start: IrExpression::Int(slice_start.into()),
                                    len: slice_len.clone(),
                                });
                                let next_ty = Type::Array(Arc::clone(array_inner), Some(slice_len));
                                (Ok(step_ir), next_ty)
                            }
                        }
                    }
                    TargetStepCompile::DotIndexInt(index) => {
                        let fields = match &curr_ty.inner {
                            Type::Tuple(fields) => fields,
                            _ => return Err(err_expected_tuple(refs, curr_ty.as_ref(), step_span)),
                        };

                        match fields {
                            None => (Err(EncounteredUnknown), Type::Any),
                            Some(fields) => {
                                let index = check_tuple_index(diags, fields.len(), index, curr_ty.span, step_span)?;
                                let step_ir = IrTargetStep::Scalar(IrTargetStepScalar::TupleIndex(index));
                                (Ok(step_ir), fields[index].clone())
                            }
                        }
                    }
                    TargetStepCompile::DotIndexId(field) => {
                        let ty = match curr_ty.inner {
                            Type::Struct(ty) => ty,
                            _ => return Err(err_expected_struct(refs, curr_ty.as_ref(), step_span)),
                        };
                        let ty_info = refs.shared.elaboration_arenas.struct_info(ty);

                        let field_index = ty_info.field_index(refs, curr_ty.span, Spanned::new(step_span, *field))?;

                        let step_ir = IrTargetStep::Scalar(IrTargetStepScalar::StructField(field_index));
                        let field_ty = ty_info.fields[field_index].ty.inner.clone();
                        (Ok(step_ir), field_ty)
                    }
                },
                TargetStep::Hardware(step) => match step {
                    TargetStepHardware::ArrayIndex(index) => {
                        let (array_inner, array_len) = check_type_is_array(false)?;
                        check_range_index(diags, Spanned::new(step_span, &index.ty), array_len)?;

                        let step_ir = array_len
                            .inner
                            .map(|_| IrTargetStep::Scalar(IrTargetStepScalar::ArrayIndex(index.expr.clone())))
                            .ok_or(EncounteredUnknown);

                        (step_ir, array_inner.as_ref().clone())
                    }
                    TargetStepHardware::ArraySlice {
                        start: slice_start,
                        length: slice_len,
                    } => {
                        let (array_inner, array_len) = check_type_is_array(true)?;
                        check_range_slice(
                            diags,
                            Spanned::new(step_span, &slice_start.ty),
                            Some(Spanned::new(step_span, slice_len)),
                            array_len,
                        )?;

                        let step_ir = IrTargetStep::Slice(IrTargetStepSlice {
                            start: slice_start.expr.clone(),
                            len: slice_len.clone(),
                        });

                        let next_ty = Type::Array(Arc::clone(array_inner), Some(slice_len.clone()));

                        (Ok(step_ir), next_ty)
                    }
                },
            };

            // append IR step
            match step_ir {
                Ok(step_ir) => {
                    if let Ok(steps_builder) = &mut steps_builder {
                        steps_builder
                            .push(step_ir)
                            .map_err(|_| diags.report_error_internal(step_span, "invalid step sequence"))?;
                    }
                }
                Err(e) => {
                    steps_builder = Err(e);
                }
            }

            // move on to the next type
            curr_ty = Spanned::new(step.span_full, next_ty);
        }

        let steps_ir = steps_builder.map_err(Either::Right);
        Ok((curr_ty.inner, steps_ir))
    }

    pub fn apply_to_value(
        &self,
        ctx: &mut CompileItemContext,
        expected_ty: &Type,
        value: Spanned<ValueWithImplications>,
    ) -> DiagResult<ValueWithImplications> {
        let refs = ctx.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let TargetSteps { steps } = self;

        let mut curr_expected_ty = expected_ty;
        let mut curr_value = value;

        // TODO fuse IR steps?
        for step in steps {
            let curr_span = curr_value.span;
            let expr_span = step.span_full;
            let step_span = step.span_step;

            let next_value: ValueWithImplications = match &step.step {
                TargetStep::Compile(step) => match step {
                    TargetStepCompile::ArrayIndex(index) => {
                        let index_range = ClosedNonEmptyMultiRange::single(index.clone());
                        let index_spanned = Spanned::new(step_span, &index_range);

                        match curr_value.inner {
                            Value::Simple(SimpleCompileValue::Array(curr_value)) => {
                                let index = check_range_index_compile(
                                    diags,
                                    Spanned::new(step_span, index),
                                    Spanned::new(curr_span, curr_value.len()),
                                )?;

                                match Arc::try_unwrap(curr_value) {
                                    Ok(curr) => Value::from(curr.get_owned(index)),
                                    Err(curr) => Value::from(curr[index].clone()),
                                }
                            }
                            Value::Hardware(ref curr_value)
                                if let HardwareType::Array(curr_inner, curr_len) = &curr_value.value.ty =>
                            {
                                check_range_index(diags, index_spanned, Spanned::new(curr_span, Some(curr_len)))?;

                                let step = IrTargetStepScalar::ArrayIndex(IrExpression::Int(index.into()));
                                let result = IrExpressionLarge::Steps {
                                    base: curr_value.value.expr.clone(),
                                    steps: IrTargetSteps::single(step),
                                };
                                let result = HardwareValue {
                                    ty: (**curr_inner).clone(),
                                    domain: curr_value.value.domain,
                                    expr: ctx.large.push_expr(result),
                                };
                                Value::Hardware(HardwareValueWithImplications::simple(result))
                            }
                            _ => {
                                let err = err_expected_array(
                                    refs,
                                    curr_value.as_ref().map_inner(Value::ty).as_ref(),
                                    step_span,
                                    false,
                                );
                                return Err(err);
                            }
                        }
                    }
                    TargetStepCompile::ArraySlice {
                        start: slice_start,
                        length: slice_length,
                    } => {
                        let slice_length = slice_length
                            .as_ref()
                            .map(|slice_length| Spanned::new(step_span, slice_length));

                        match curr_value.inner {
                            Value::Simple(SimpleCompileValue::Array(curr_value)) => {
                                let slice_start = Spanned::new(step_span, slice_start);
                                let slice_range = check_range_slice_compile(
                                    diags,
                                    slice_start,
                                    slice_length,
                                    Spanned::new(curr_span, curr_value.len()),
                                )?
                                .as_range();

                                let result = match Arc::try_unwrap(curr_value) {
                                    Ok(curr_value) => curr_value.slice_owned(slice_range),
                                    Err(curr_value) => curr_value[slice_range].to_vec(),
                                };

                                Value::Simple(SimpleCompileValue::Array(Arc::new(result)))
                            }
                            Value::Hardware(ref curr_value)
                                if let HardwareType::Array(array_inner, array_len) = &curr_value.value.ty =>
                            {
                                let slice_len = check_range_slice_known(
                                    diags,
                                    Spanned::new(step_span, &ClosedNonEmptyMultiRange::single(slice_start.clone())),
                                    slice_length,
                                    Spanned::new(curr_span, array_len),
                                )?;

                                let step = IrTargetStepSlice {
                                    start: IrExpression::Int(slice_start.into()),
                                    len: slice_len.clone(),
                                };
                                let result = IrExpressionLarge::Steps {
                                    base: curr_value.value.expr.clone(),
                                    steps: IrTargetSteps::single(step),
                                };

                                let result = HardwareValue {
                                    ty: HardwareType::Array(Arc::clone(array_inner), slice_len),
                                    domain: curr_value.value.domain,
                                    expr: ctx.large.push_expr(result),
                                };
                                Value::Hardware(HardwareValueWithImplications::simple(result))
                            }
                            _ => {
                                let curr_ty = curr_value.as_ref().map_inner(Value::ty);
                                return Err(err_expected_array(refs, curr_ty.as_ref(), step_span, true));
                            }
                        }
                    }
                    TargetStepCompile::DotIndexInt(index) => match curr_value.inner {
                        Value::Simple(SimpleCompileValue::Type(Type::Tuple(fields))) => {
                            let fields = fields.ok_or_else(|| {
                                DiagnosticError::new(
                                    "cannot index into tuple type with unknown field types",
                                    step_span,
                                    "trying to index here",
                                )
                                .add_info(
                                    curr_span,
                                    format!("target resolved to type `{}`", Type::Tuple(None).value_string(refs)),
                                )
                                .report(diags)
                            })?;
                            let index = check_tuple_index(diags, fields.len(), index, curr_span, step_span)?;

                            let result = match Arc::try_unwrap(fields) {
                                Ok(fields) => fields.get_owned(index),
                                Err(fields) => fields[index].clone(),
                            };
                            Value::new_ty(result)
                        }
                        Value::Compound(MixedCompoundValue::Tuple(fields)) => {
                            let index = check_tuple_index(diags, fields.len(), index, curr_span, step_span)?;
                            ValueWithImplications::simple(fields.get_owned(index))
                        }
                        Value::Hardware(ref curr_value) if let HardwareType::Tuple(fields) = &curr_value.value.ty => {
                            let index = check_tuple_index(diags, fields.len(), index, curr_span, step_span)?;

                            let step = IrTargetStepScalar::TupleIndex(index);
                            let result = IrExpressionLarge::Steps {
                                base: curr_value.value.expr.clone(),
                                steps: IrTargetSteps::single(step),
                            };
                            let result = HardwareValue {
                                ty: fields[index].clone(),
                                domain: curr_value.value.domain,
                                expr: ctx.large.push_expr(result),
                            };
                            Value::Hardware(HardwareValueWithImplications::simple(result))
                        }
                        _ => {
                            let curr_ty = curr_value.as_ref().map_inner(Value::ty);
                            return Err(err_expected_tuple(refs, curr_ty.as_ref(), step_span));
                        }
                    },
                    TargetStepCompile::DotIndexId(field) => eval_dot_index_id(
                        ctx,
                        curr_expected_ty,
                        expr_span,
                        curr_value,
                        Spanned::new(step_span, *field),
                    )?,
                },
                TargetStep::Hardware(step) => {
                    // check type
                    let curr_ty = curr_value.inner.ty();
                    let step_is_slice = match step {
                        TargetStepHardware::ArrayIndex(_) => false,
                        TargetStepHardware::ArraySlice { .. } => true,
                    };
                    check_type_is_array(refs, Spanned::new(curr_span, &curr_ty), step_span, step_is_slice)?;

                    // convert value to hardware
                    let curr_ty = curr_ty.as_hardware_type(elab).map_err(|_| {
                        DiagnosticError::new(
                            "hardware array indexing target needs to have hardware type",
                            curr_span,
                            format!(
                                "this array target needs to have a hardware type, has type `{}`",
                                curr_ty.value_string(refs)
                            ),
                        )
                        .add_info(step_span, "for this hardware array access operation")
                        .report(diags)
                    })?;

                    let curr_value = curr_value.inner.as_hardware_value_unchecked(
                        refs,
                        &mut ctx.large,
                        curr_span,
                        curr_ty.clone(),
                    )?;
                    let (array_inner, array_len) = match curr_value.ty {
                        HardwareType::Array(array_inner, array_len) => (array_inner, array_len),
                        _ => {
                            let diag = diags.report_error_internal(step_span, "should still be array after conversion");
                            return Err(diag);
                        }
                    };
                    let array_len = Spanned::new(curr_span, &array_len);

                    // apply step
                    match step {
                        TargetStepHardware::ArrayIndex(index) => {
                            check_range_index(diags, Spanned::new(step_span, &index.ty), array_len.map_inner(Some))?;

                            let step = IrTargetStepScalar::ArrayIndex(index.expr.clone());
                            let result = IrExpressionLarge::Steps {
                                base: curr_value.expr,
                                steps: IrTargetSteps::single(step),
                            };
                            let result = HardwareValue {
                                ty: Arc::unwrap_or_clone(array_inner),
                                domain: curr_value.domain.join(index.domain),
                                expr: ctx.large.push_expr(result),
                            };
                            Value::Hardware(HardwareValueWithImplications::simple(result))
                        }
                        TargetStepHardware::ArraySlice {
                            start: slice_start,
                            length: slice_length,
                        } => {
                            check_range_slice(
                                diags,
                                Spanned::new(step_span, &slice_start.ty),
                                Some(Spanned::new(step_span, slice_length)),
                                array_len.map_inner(Some),
                            )?;

                            let step = IrTargetStepSlice {
                                start: slice_start.expr.clone(),
                                len: slice_length.clone(),
                            };
                            let result = IrExpressionLarge::Steps {
                                base: curr_value.expr,
                                steps: IrTargetSteps::single(step),
                            };
                            let result = HardwareValue {
                                ty: HardwareType::Array(array_inner, slice_length.clone()),
                                domain: curr_value.domain.join(slice_start.domain),
                                expr: ctx.large.push_expr(result),
                            };
                            Value::Hardware(HardwareValueWithImplications::simple(result))
                        }
                    }
                }
            };

            // we lose expected type info after any step
            curr_expected_ty = &Type::Any;
            curr_value = Spanned::new(step.span_full, next_value);
        }

        Ok(curr_value.inner)
    }
}

impl TargetSteps<&TargetStepCompile> {
    /// Evaluate the operation `target[steps] = value`, where all operands are compile-time constants.
    pub fn set_compile_value(
        &self,
        refs: CompileRefs,
        target: Spanned<&mut CompileValue>,
        assign_op_span: Span,
        source: Spanned<CompileValue>,
    ) -> DiagResult {
        let target_span = target.span;
        let target = Spanned::new(target_span, SetCompileTarget::Scalar(target.inner));
        set_compile_value_impl(refs, target, &self.steps, assign_op_span, source, None)
    }

    /// Evaluate the expression `value[steps]`
    pub fn apply_to_compile_value(
        &self,
        ctx: &mut CompileItemContext,
        base: Spanned<CompileValue>,
    ) -> DiagResult<CompileValue> {
        let refs = ctx.refs;
        let diags = refs.diags;

        // TODO avoid clones
        let self_mapped = TargetSteps {
            steps: self
                .steps
                .iter()
                .map(|s| SpannedStep {
                    span_full: s.span_full,
                    span_step: s.span_step,
                    step: TargetStep::Compile(s.step.clone()),
                })
                .collect_vec(),
        };

        let base_span = base.span;
        let result = self_mapped.apply_to_value(ctx, &Type::Type, base.map_inner(Value::from))?;

        CompileValue::try_from(&result).map_err(|_: NotCompile| {
            let msg = "applying compile-time steps to compile-time value should result in compile-time value again, got hardware";
            diags.report_error_internal(base_span, msg)
        })
    }
}

pub const POSSIBLE_BUILTIN_TYPE_MEMBERS: &[&str] = &["size_bits", "to_bits", "from_bits", "from_bits_unsafe", "new"];

fn eval_dot_index_id(
    ctx: &mut CompileItemContext,
    expected_ty: &Type,
    expr_span: Span,
    base: Spanned<ValueWithImplications>,
    index: Spanned<Id>,
) -> DiagResult<ValueWithImplications> {
    // TODO add type.int_start, type.int_end, type.int_ranges, type.tuple_items, type.struct_fields?
    let refs = ctx.refs;
    let diags = refs.diags;

    let index_str = index.inner.str(&refs.shared.interner);

    // interface views
    if let &Value::Simple(SimpleCompileValue::Interface(base_interface)) = &base.inner {
        let info = ctx.refs.shared.elaboration_arenas.interface_info(base_interface);
        let (view_index, _) = info.get_view(diags, &refs.shared.interner, index)?;

        let interface_view = ElaboratedInterfaceView {
            interface: base_interface,
            view_index,
        };
        return Ok(Value::Simple(SimpleCompileValue::InterfaceView(interface_view)));
    }

    // hierarchy indexing, similar to import
    if let &Value::Simple(SimpleCompileValue::Package(node)) = &base.inner {
        let value = resolve_import_final(
            diags,
            &refs.shared.interner,
            refs.fixed.hierarchy,
            &refs.shared.file_scopes,
            node,
            Some(base.span),
            Spanned::new(index.span, index_str),
            false,
        )?;

        return Ok(Value::from(ctx.eval_import_value(value)?));
    }

    // common type attributes
    if let Value::Simple(SimpleCompileValue::Type(ty)) = &base.inner {
        match index_str {
            "size_bits" => {
                let ty_hw = check_hardware_type_for_bit_operation(refs, Spanned::new(base.span, ty))?;
                let width = ty_hw.size_bits(refs);
                return Ok(Value::new_int(width.into()));
            }
            "to_bits" => {
                let ty_hw = check_hardware_type_for_bit_operation(refs, Spanned::new(base.span, ty))?;
                let func = FunctionBits {
                    ty_hw,
                    kind: FunctionBitsKind::ToBits,
                };
                return Ok(Value::Simple(SimpleCompileValue::Function(FunctionValue::Bits(func))));
            }
            "from_bits" => {
                let ty_hw = check_hardware_type_for_bit_operation(refs, Spanned::new(base.span, ty))?;

                if !ty_hw.every_bit_pattern_is_valid(refs) {
                    let diag = DiagnosticError::new(
                        "from_bits is only allowed for types where every bit pattern is valid",
                        base.span,
                        format!("got type `{}` with invalid bit patterns", ty_hw.value_string(refs)),
                    )
                    .add_footer_hint("consider using a target type where every bit pattern is valid")
                    .add_footer_hint("if you know the bits are valid for this type, use `from_bits_unsafe` instead")
                    .report(diags);
                    return Err(diag);
                }

                let func = FunctionBits {
                    ty_hw,
                    kind: FunctionBitsKind::FromBits { is_unsafe: false },
                };
                return Ok(Value::Simple(SimpleCompileValue::Function(FunctionValue::Bits(func))));
            }
            "from_bits_unsafe" => {
                let ty_hw = check_hardware_type_for_bit_operation(refs, Spanned::new(base.span, ty))?;
                let func = FunctionBits {
                    ty_hw,
                    kind: FunctionBitsKind::FromBits { is_unsafe: true },
                };
                return Ok(Value::Simple(SimpleCompileValue::Function(FunctionValue::Bits(func))));
            }
            _ => {}
        }

        // array type attributes
        if let Type::Array(ty_inner, ty_len) = ty {
            match index_str {
                "inner" => {
                    return Ok(Value::new_ty((**ty_inner).clone()));
                }
                "len" => {
                    return if let Some(ty_len) = ty_len {
                        Ok(Value::new_int(BigInt::from(ty_len)))
                    } else {
                        let diag = DiagnosticError::new(
                            "cannot get length of array type with unknown length",
                            index.span,
                            "trying to get length here",
                        )
                        .add_info(base.span, format!("array type is `{}`", ty.value_string(refs)))
                        .report(diags);
                        Err(diag)
                    };
                }
                _ => {}
            }
        }

        // tuple type attributes
        if let Type::Tuple(ty_elements) = ty {
            let err_unknown_elements = |get: &str| {
                DiagnosticError::new(
                    format!("cannot get {get} of tuple type with unknown elements"),
                    index.span,
                    format!("trying to get {get} here"),
                )
                .add_info(base.span, format!("tuple type is `{}`", ty.value_string(refs)))
                .report(diags)
            };

            match index_str {
                "elements" => {
                    let ty_elements = ty_elements
                        .as_ref()
                        .ok_or_else(|| err_unknown_elements("element types"))?;
                    let ty_elements = ty_elements.iter().cloned().map(Value::new_ty).collect_vec();
                    return Ok(Value::Compound(MixedCompoundValue::Tuple(ty_elements)));
                }
                "len" => {
                    let ty_elements = ty_elements.as_ref().ok_or_else(|| err_unknown_elements("length"))?;
                    return Ok(Value::new_int(BigInt::from(ty_elements.len())));
                }
                _ => {}
            }
        }
    }

    // struct new, struct static members
    if let &Value::Simple(SimpleCompileValue::Type(Type::Struct(elab))) = &base.inner {
        if index_str == "new" {
            let func = FunctionValue::StructNew(elab);
            return Ok(Value::Simple(SimpleCompileValue::Function(func)));
        }

        let info = refs.shared.elaboration_arenas.struct_info(elab);
        if let Some(value) = info.members_static.get(&index.inner) {
            return Ok(Value::from(value.as_ref_ok()?.clone()));
        }
    }

    // struct new for not yet inferred struct types
    let base_item_function = match &base.inner {
        Value::Simple(SimpleCompileValue::Function(FunctionValue::User(func))) => match &func.body.inner {
            FunctionBody::ItemBody(body) => Some(body),
            _ => None,
        },
        _ => None,
    };
    if let Some(FunctionItemBody::Struct(unique, _)) = base_item_function
        && index_str == "new"
    {
        let func = FunctionValue::StructNewInfer(*unique);
        return Ok(Value::Simple(SimpleCompileValue::Function(func)));
    }

    // enum variants
    let eval_enum = |elab| {
        let info = refs.shared.elaboration_arenas.enum_info(elab);
        let variant_index = info.variant_index(refs, index)?;
        let variant_info = &info.variants[variant_index];

        let result = match &variant_info.payload_ty {
            None => Value::Compound(MixedCompoundValue::Enum(EnumValue {
                ty: elab,
                variant: variant_index,
                payload: None,
            })),
            Some(_) => Value::Simple(SimpleCompileValue::Function(FunctionValue::EnumNew(
                elab,
                variant_index,
            ))),
        };
        Ok(result)
    };

    if let &Value::Simple(SimpleCompileValue::Type(Type::Enum(elab))) = &base.inner {
        // enum members
        let info = refs.shared.elaboration_arenas.enum_info(elab);
        if let Some(value) = info.members_static.get(&index.inner) {
            return Ok(Value::from(value.as_ref_ok()?.clone()));
        }

        // enum variants
        return eval_enum(elab);
    }
    if let Some(FunctionItemBody::Enum(unique, generic_info)) = base_item_function {
        return if let &Type::Enum(expected) = expected_ty {
            let expected_info = refs.shared.elaboration_arenas.enum_info(expected);
            if expected_info.unique == *unique {
                eval_enum(expected)
            } else {
                Err(
                    error_unique_mismatch("enum", base.span, expected_info.unique.id().span(), unique.id().span())
                        .report(diags),
                )
            }
        } else {
            let generic_variant = generic_info.find_variant(refs, index)?;
            if generic_variant.has_payload {
                // delay type inference until payload construction/call time
                let func = FunctionValue::EnumNewInfer(*unique, index.inner);
                Ok(Value::Simple(SimpleCompileValue::Function(func)))
            } else {
                // non-payload variant, we need to know the type now
                let expected_ty_str = match expected_ty {
                    Type::Any => None,
                    _ => Some(expected_ty.value_string(refs)),
                };
                let err = error_cannot_infer_generic_params(
                    "enum",
                    base.span,
                    expr_span,
                    unique.id().span(),
                    expected_ty_str,
                );
                return Err(err.report(diags));
            }
        };
    }

    // struct fields and methods
    let base_ty = base.inner.ty();
    if let Type::Struct(base_ty_struct) = base_ty {
        let info = refs.shared.elaboration_arenas.struct_info(base_ty_struct);

        // try method
        if let Some(method) = info.methods_self.get(&index.inner) {
            let bound = BoundMethod {
                self_type: base_ty,
                self_value: Box::new(base.inner.into_value()),
                method: Arc::clone(method),
            };
            return Ok(Value::Compound(MixedCompoundValue::BoundMethod(bound)));
        }

        // try field
        let field_index = info.field_index(refs, base.span, index)?;
        let result = match base.inner {
            ValueWithImplications::Compound(MixedCompoundValue::Struct(base_inner)) => {
                base_inner.fields.get_owned(field_index)
            }
            ValueWithImplications::Hardware(base_inner) => {
                let info_hw = info.hw.as_ref_ok().map_err(|_| {
                    diags.report_error_internal(expr_span, "hardware value with non-hardware struct type")
                })?;

                let step = IrTargetStepScalar::StructField(field_index);
                let result = IrExpressionLarge::Steps {
                    base: base_inner.value.expr,
                    steps: IrTargetSteps::single(step),
                };
                let result = HardwareValue {
                    ty: info_hw.fields[field_index].clone(),
                    domain: base_inner.value.domain,
                    expr: ctx.large.push_expr(result),
                };

                Value::Hardware(result)
            }
            _ => return Err(diags.report_error_internal(expr_span, "struct type but not a struct value")),
        };
        return Ok(ValueWithImplications::simple(result));
    }

    // enum methods
    if let Type::Enum(base_ty_enum) = base_ty {
        let info = refs.shared.elaboration_arenas.enum_info(base_ty_enum);

        // try method
        if let Some(method) = info.methods_self.get(&index.inner) {
            let bound = BoundMethod {
                self_type: base_ty,
                self_value: Box::new(base.inner.into_value()),
                method: Arc::clone(method),
            };
            return Ok(Value::Compound(MixedCompoundValue::BoundMethod(bound)));
        }
    }

    // array length
    if let Type::Array(_, value_len) = &base_ty
        && index_str == "len"
    {
        return if let Some(value_len) = value_len {
            Ok(Value::new_int(BigInt::from(value_len)))
        } else {
            Err(diags.report_error_internal(expr_span, "value has type with unknown array length"))
        };
    }

    // tuple length
    if let Type::Tuple(value_elements) = &base_ty
        && index_str == "len"
    {
        return if let Some(value_elements) = value_elements {
            Ok(Value::new_int(BigInt::from(value_elements.len())))
        } else {
            Err(diags.report_error_internal(expr_span, "value has tuple type with unknown elements"))
        };
    }

    // fallthrough into error
    let diag = DiagnosticError::new(
        "invalid dot index expression",
        index.span,
        format!("no attribute found with name `{index_str}`"),
    )
    .add_info(base.span, format!("base has type `{}`", base_ty.value_string(refs)))
    .report(diags);
    Err(diag)
}

enum SetCompileTarget<'a> {
    Scalar(&'a mut CompileValue),
    Slice(&'a mut [CompileValue]),
}

impl SetCompileTarget<'_> {
    pub fn ty(&self) -> Type {
        match self {
            SetCompileTarget::Scalar(v) => v.ty(),
            SetCompileTarget::Slice(slice) => {
                let v = SimpleCompileValue::Array(Arc::new(slice.to_vec()));
                v.ty()
            }
        }
    }
}

fn set_compile_value_impl(
    refs: CompileRefs,
    target: Spanned<SetCompileTarget<'_>>,
    steps: &[SpannedStep<&TargetStepCompile>],
    assign_op_span: Span,
    source: Spanned<CompileValue>,
    expected_ty: Option<Spanned<Type>>,
) -> DiagResult {
    let diags = refs.diags;
    let elab = &refs.shared.elaboration_arenas;

    // if done just do the final assignment, otherwise get the next step
    let Some((step, steps)) = steps.split_first() else {
        if let Some(expected_ty) = expected_ty {
            let reason = TypeContainsReason::Assignment {
                span_target: target.span,
                span_target_ty: expected_ty.span,
            };
            check_type_contains_value(refs, reason, &expected_ty.inner, source.as_ref())?;
        }

        match target.inner {
            SetCompileTarget::Scalar(target) => {
                // scalar assignment target, just replace the entire value
                *target = source.inner;
            }
            SetCompileTarget::Slice(target_slice) => {
                // slice assignment target, assign all elements in the selected subrange
                let source_span = source.span;
                match source.inner {
                    CompileValue::Simple(SimpleCompileValue::Array(source)) => {
                        if source.len() != target_slice.len() {
                            return Err(DiagnosticError::new(
                                "slice assignment length mismatch",
                                assign_op_span,
                                "length mismatch on this assignment",
                            )
                            .add_info(target.span, format!("target slice has length `{}`", target_slice.len()))
                            .add_info(source_span, format!("source array has length `{}`", source.len()))
                            .report(diags));
                        }

                        match Arc::try_unwrap(source) {
                            Ok(source) => {
                                for (t, v) in zip_eq(target_slice, source) {
                                    *t = v;
                                }
                            }
                            Err(source) => {
                                for (t, v) in zip_eq(target_slice, source.as_ref()) {
                                    *t = v.clone();
                                }
                            }
                        }
                    }
                    _ => {
                        return Err(DiagnosticError::new(
                            "expected array value for slice assignment",
                            assign_op_span,
                            "value assigned to slice here",
                        )
                        .add_info(
                            source.span,
                            format!(
                                "non-array value with type `{}` here",
                                source.inner.ty().value_string(refs)
                            ),
                        )
                        .add_info(target.span, "target is a slice assignment")
                        .report(diags));
                    }
                }
            }
        }
        return Ok(());
    };

    let target_span = target.span;
    let step_span = step.span_step;
    let (new_target, field_ty) = match step.step {
        TargetStepCompile::ArrayIndex(index) => {
            let target_inner = check_target_is_array(refs, target, step_span, false)?;

            let index = check_range_index_compile(
                diags,
                Spanned::new(step_span, index),
                Spanned::new(target_span, target_inner.len()),
            )?;

            let new_target = SetCompileTarget::Scalar(&mut target_inner[index]);
            (new_target, None)
        }
        TargetStepCompile::ArraySlice {
            start: slice_start,
            length: slice_len,
        } => {
            let target_inner = check_target_is_array(refs, target, step_span, true)?;

            let SliceInfo {
                start: slice_start,
                length: slice_len,
            } = check_range_slice_compile(
                diags,
                Spanned::new(step_span, slice_start),
                slice_len.as_ref().map(|len| Spanned::new(step_span, len)),
                Spanned::new(target_span, target_inner.len()),
            )?;

            let new_target = SetCompileTarget::Slice(&mut target_inner[slice_start..][..slice_len]);
            (new_target, None)
        }
        TargetStepCompile::DotIndexInt(index) => {
            // check target is tuple
            let target_inner = match target.inner {
                SetCompileTarget::Scalar(target_inner) => match target_inner {
                    CompileValue::Compound(CompileCompoundValue::Tuple(target_inner)) => target_inner,
                    CompileValue::Hardware(never) => never.unreachable(),
                    _ => {
                        let curr_ty = Spanned::new(target_span, target_inner.ty());
                        return Err(err_expected_tuple(refs, curr_ty.as_ref(), step_span));
                    }
                },
                SetCompileTarget::Slice(_) => {
                    let curr_ty = Spanned::new(target_span, target.inner.ty());
                    return Err(err_expected_tuple(refs, curr_ty.as_ref(), step_span));
                }
            };

            // check index in bounds
            let index = check_tuple_index(diags, target_inner.len(), index, target_span, step_span)?;

            // build new target
            let new_target = SetCompileTarget::Scalar(&mut target_inner[index]);
            (new_target, None)
        }
        TargetStepCompile::DotIndexId(field) => {
            // check target is struct
            let target_inner = match target.inner {
                SetCompileTarget::Scalar(target_inner) => match target_inner {
                    CompileValue::Compound(CompileCompoundValue::Struct(target_inner)) => target_inner,
                    CompileValue::Hardware(never) => never.unreachable(),
                    _ => {
                        let curr_ty = Spanned::new(target_span, target_inner.ty());
                        return Err(err_expected_struct(refs, curr_ty.as_ref(), step_span));
                    }
                },
                SetCompileTarget::Slice(_) => {
                    let curr_ty = Spanned::new(target_span, target.inner.ty());
                    return Err(err_expected_struct(refs, curr_ty.as_ref(), step_span));
                }
            };

            // get field index
            let ty_info = elab.struct_info(target_inner.ty);
            let field_index = ty_info.field_index(refs, target_span, Spanned::new(step_span, *field))?;
            let field_ty = ty_info.fields[field_index].ty.clone();

            // build new target
            let new_target = SetCompileTarget::Scalar(&mut target_inner.fields[field_index]);
            (new_target, Some(field_ty))
        }
    };

    // Preserve extra type constraints we encounter along the way. These can only come from struct fields.
    // * if this was a struct field, set the new expected type to the type of that field
    // * otherwise, just apply the step to the current expected type if there is one
    let next_expected_ty = match field_ty {
        Some(field_ty) => Some(field_ty),
        None => expected_ty
            .map(|ty| {
                let span = ty.span;
                let step = SpannedStep {
                    span_full: step.span_full,
                    span_step: step.span_step,
                    step: TargetStep::Compile(step.step.clone()),
                };
                let new_ty = TargetSteps::single(step).apply_to_expected_type(refs, ty)?;
                Ok(Spanned::new(span, new_ty))
            })
            .transpose()?,
    };

    let new_target = Spanned::new(step.span_full, new_target);
    set_compile_value_impl(refs, new_target, steps, assign_op_span, source, next_expected_ty)
}

fn check_target_is_array<'a>(
    refs: CompileRefs,
    target: Spanned<SetCompileTarget<'a>>,
    step_span: Span,
    op_is_slice: bool,
) -> DiagResult<&'a mut [CompileValue]> {
    match target.inner {
        SetCompileTarget::Scalar(target_inner) => match target_inner {
            CompileValue::Simple(SimpleCompileValue::Array(target_inner)) => {
                Ok(Arc::make_mut(target_inner).as_mut_slice())
            }
            _ => Err(err_expected_array(
                refs,
                Spanned::new(target.span, &target_inner.ty()),
                step_span,
                op_is_slice,
            )),
        },
        SetCompileTarget::Slice(array) => Ok(array),
    }
}

pub fn check_range_index(
    diags: &Diagnostics,
    index: Spanned<&ClosedNonEmptyMultiRange<BigUint>>,
    array_len: Spanned<Option<&BigUint>>,
) -> DiagResult {
    let ClosedNonEmptyRange {
        start: _,
        end: index_end,
    } = index.inner.enclosing_range();

    if array_len.inner.is_none_or(|array_len| index_end <= array_len) {
        Ok(())
    } else {
        let index_str = if let Some(index) = index.inner.as_single() {
            format!("`{index}`")
        } else {
            format!("with range `{}`", index.inner)
        };

        Err(DiagnosticError::new(
            "array index out of bounds",
            index.span,
            format!("index {index_str} is out of bounds"),
        )
        .add_info(array_len.span, info_array_length(array_len.inner))
        .report(diags))
    }
}

pub fn check_range_index_compile(
    diags: &Diagnostics,
    index: Spanned<&BigUint>,
    array_len: Spanned<usize>,
) -> DiagResult<usize> {
    let index_range = index.cloned().map_inner(ClosedNonEmptyMultiRange::single);

    let array_len = array_len.map_inner(BigUint::from);
    let array_len = array_len.as_ref().map_inner(Some);
    check_range_index(diags, index_range.as_ref(), array_len)?;

    Ok(usize::try_from(index.inner).unwrap())
}

pub fn check_range_slice_known(
    diags: &Diagnostics,
    slice_start: Spanned<&ClosedNonEmptyMultiRange<BigUint>>,
    slice_len: Option<Spanned<&BigUint>>,
    array_len: Spanned<&BigUint>,
) -> DiagResult<BigUint> {
    Ok(check_range_slice(diags, slice_start, slice_len, array_len.map_inner(Some))?.unwrap())
}

pub fn check_range_slice(
    diags: &Diagnostics,
    slice_start: Spanned<&ClosedNonEmptyMultiRange<BigUint>>,
    slice_len: Option<Spanned<&BigUint>>,
    array_len: Spanned<Option<&BigUint>>,
) -> DiagResult<Option<BigUint>> {
    #[derive(Copy, Clone)]
    enum SliceLen<T, U> {
        NoneButStartSingle(U),
        Some(T),
    }
    let slice_len = match slice_len {
        Some(slice_len) => SliceLen::Some(slice_len),
        None => match slice_start.inner.as_single() {
            None => {
                return Err(diags.report_error_internal(
                    slice_start.span,
                    "start with non-single range and no length doesn't make sense",
                ));
            }
            Some(slice_start_single) => SliceLen::NoneButStartSingle(slice_start_single),
        },
    };

    let slice_str = || {
        let start = if let Some(slice_start_single) = slice_start.inner.as_single() {
            format!("{slice_start_single}")
        } else {
            format!("({})", slice_start.inner)
        };

        match slice_len {
            SliceLen::NoneButStartSingle(_) => format!("{start}.."),
            SliceLen::Some(slice_len) => format!("{}+..{}", start, slice_len.inner),
        }
    };

    // check start
    let ClosedNonEmptyRange {
        start: _,
        end: slice_start_end,
    } = slice_start.inner.enclosing_range();

    if array_len
        .inner
        .is_some_and(|array_len| slice_start_end - 1 > BigInt::from(array_len.clone()))
    {
        return Err(DiagnosticError::new(
            "array slice start out of bounds",
            slice_start.span,
            format!("slice start of `{}` is out of bounds", slice_str()),
        )
        .add_info(array_len.span, info_array_length(array_len.inner))
        .report(diags));
    }

    // check array length compared to slice length (if we have enough info)
    match slice_len {
        SliceLen::Some(slice_len) => {
            if let Some(array_len_inner) = array_len.inner {
                let slice_end_max = slice_start_end + BigInt::from(slice_len.inner.clone());

                #[allow(clippy::nonminimal_bool)]
                if !(slice_end_max - 1 <= BigInt::from(array_len_inner)) {
                    return Err(DiagnosticError::new(
                        "array slice end out of bounds",
                        slice_len.span,
                        format!("slice end of `{}` is out of bounds", slice_str()),
                    )
                    .add_info(array_len.span, info_array_length(Some(array_len_inner)))
                    .report(diags));
                }
            }

            Ok(Some(slice_len.inner.clone()))
        }
        SliceLen::NoneButStartSingle(slice_start) => Ok(array_len
            .inner
            .map(|array_len| BigUint::try_from(array_len - slice_start).unwrap())),
    }
}

fn info_array_length(array_len: Option<&BigUint>) -> String {
    match array_len {
        Some(len) => format!("for this array with length `{}`", len),
        None => "for this array".to_string(),
    }
}

#[derive(Copy, Clone)]
pub struct SliceInfo {
    pub start: usize,
    pub length: usize,
}

impl SliceInfo {
    fn as_range(self) -> std::ops::Range<usize> {
        let SliceInfo { start, length } = self;
        start..start + length
    }
}

pub fn check_range_slice_compile(
    diags: &Diagnostics,
    slice_start: Spanned<&BigUint>,
    slice_len: Option<Spanned<&BigUint>>,
    array_len: Spanned<usize>,
) -> DiagResult<SliceInfo> {
    let start_range = slice_start.cloned().map_inner(ClosedNonEmptyMultiRange::single);
    check_range_slice_known(
        diags,
        start_range.as_ref(),
        slice_len,
        array_len.map_inner(BigUint::from).as_ref(),
    )?;
    let start = usize::try_from(slice_start.inner).unwrap();
    let len = slice_len
        .map(|len| usize::try_from(len.inner).unwrap())
        .unwrap_or(array_len.inner - start);
    Ok(SliceInfo { start, length: len })
}

fn check_tuple_index(
    diags: &Diagnostics,
    tuple_len: usize,
    index: &BigUint,
    base_span: Span,
    step_span: Span,
) -> DiagResult<usize> {
    index.as_usize_if_lt(tuple_len).ok_or_else(|| {
        DiagnosticError::new(
            "tuple index out of bounds",
            step_span,
            format!("index `{index}` is out of bounds"),
        )
        .add_info(base_span, format!("base is tuple with length `{}`", tuple_len))
        .report(diags)
    })
}

fn check_type_is_array<'t>(
    refs: CompileRefs,
    ty: Spanned<&'t Type>,
    step_span: Span,
    step_is_slice: bool,
) -> DiagResult<(&'t Arc<Type>, Option<&'t BigUint>)> {
    match &ty.inner {
        Type::Array(ty_inner, len) => Ok((ty_inner, len.as_ref())),
        _ => Err(err_expected_array(refs, ty, step_span, step_is_slice)),
    }
}

fn err_expected_array(refs: CompileRefs, ty: Spanned<&Type>, step_span: Span, step_is_slice: bool) -> DiagError {
    let op_name = if step_is_slice { "slice" } else { "index" };

    DiagnosticError::new(
        format!("cannot {op_name} non-array type"),
        step_span,
        format!("array {op_name} here"),
    )
    .add_info(
        ty.span,
        format!("on non-array value with type `{}` here", ty.inner.value_string(refs)),
    )
    .report(refs.diags)
}

pub fn err_expected_tuple(refs: CompileRefs, ty: Spanned<&Type>, step_span: Span) -> DiagError {
    DiagnosticError::new("cannot tuple index non-tuple type", step_span, "tuple index here")
        .add_info(
            ty.span,
            format!("on non-tuple value with type `{}` here", ty.inner.value_string(refs)),
        )
        .report(refs.diags)
}

pub fn err_expected_struct(refs: CompileRefs, ty: Spanned<&Type>, step_span: Span) -> DiagError {
    DiagnosticError::new("cannot struct index non-struct type", step_span, "struct index here")
        .add_info(
            ty.span,
            format!("on non-struct value with type `{}` here", ty.inner.value_string(refs)),
        )
        .report(refs.diags)
}
