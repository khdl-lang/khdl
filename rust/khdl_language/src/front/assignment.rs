use crate::front::check::{TypeContainsReason, check_port_is_output, check_type_contains_value};
use crate::front::compile::CompileItemContext;
use crate::front::diagnostic::{DiagResult, DiagnosticError};
use crate::front::domain::{DomainSignal, ValueDomain};
use crate::front::expression::{LrValue, eval_binary_expression};
use crate::front::flow::{Flow, FlowHardware, HardwareProcessKind, VarSetValue};
use crate::front::implication::{HardwareValueWithImplications, ValueWithImplications};
use crate::front::scope::Scope;
use crate::front::signal::{Signal, SignalOrVariable};
use crate::front::steps::TargetSteps;
use crate::front::types::{HardwareType, NonHardwareType, Type, Typed};
use crate::front::value::{CompileValue, HardwareValue, Value, ValueCommon};
use crate::mid::ir::{IrAssignmentTarget, IrExpression, IrSignalOrVariable, IrStatement};
use crate::syntax::ast::{Assignment, SyncDomain};
use crate::syntax::pos::{Span, Spanned};

#[derive(Debug, Clone)]
pub struct AssignmentTarget {
    pub base: Spanned<SignalOrVariable>,
    pub steps: TargetSteps,
}

impl AssignmentTarget {
    pub fn simple(base: Spanned<SignalOrVariable>) -> Self {
        Self {
            base,
            steps: TargetSteps::new(vec![]),
        }
    }
}

enum BlockKind {
    Combinatorial,
    Clocked(Spanned<SyncDomain<DomainSignal>>),
}

impl CompileItemContext<'_, '_> {
    // TODO this probably needs yet another refactor, there's a lot of semi-duplicate code here
    pub fn elaborate_assignment(&mut self, scope: &Scope, flow: &mut impl Flow, stmt: &Assignment) -> DiagResult {
        let refs = self.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let &Assignment {
            span: _,
            op,
            target: target_expr,
            value: right_expr,
        } = stmt;

        // evaluate target
        let target = self.eval_expression_as_lr(scope, flow, &Type::Any, target_expr)?;

        // compute source, by evaluating right but also left if needed
        let (target, source_value) = match op.inner {
            None => {
                // figure out the expected type
                // (the expected type still being unknown if fine for now, we can suggest one later)
                let target_base_ty = match &target {
                    LrValue::LeftTarget(target) => match target.base.inner {
                        SignalOrVariable::Signal(target_base) => match target_base {
                            Signal::Port(port) => Some(self.ports[port].ty.as_ref().map_inner(HardwareType::as_type)),
                            Signal::Wire(wire) => self.wires[wire]
                                .typed_maybe(refs, &self.wire_interfaces)?
                                .map(|info| info.ty.map_inner(HardwareType::as_type)),
                        },
                        SignalOrVariable::Variable(var) => flow.var_info(target.base.map_inner(|_| var))?.ty.clone(),
                    },
                    _ => None,
                };

                let right_expected_ty = match (&target, target_base_ty) {
                    (LrValue::LeftTarget(target), Some(ty)) => target.steps.assignment_expected_type(refs, ty.inner),
                    _ => Type::Any,
                };

                // Ordinary targets are deferred until the RHS has run. This also
                // determines which transparent binding a plain assignment uses.
                let source = self.eval_expression_with_implications(scope, flow, &right_expected_ty, right_expr)?;
                (target.into_target(self, flow, target_expr.span)?, source)
            }
            Some(op_inner) => {
                // Capture reference crossings before reading the compound LHS,
                // and keep those target identities across RHS side effects.
                let target = target.into_target(self, flow, target_expr.span)?;
                let target_base = target.base;
                let target_steps = &target.steps;
                // evaluate left, including steps
                let left_value = flow.signal_or_var_eval(self, target_base, target_steps)?;
                let left_value = Spanned::new(target_expr.span, left_value);

                // evaluate right
                let right_value = self.eval_expression_with_implications(scope, flow, &Type::Any, right_expr)?;

                // evaluate operation
                let source_value = eval_binary_expression(
                    refs,
                    &mut self.large,
                    stmt.span,
                    Spanned::new(op.span, op_inner.to_binary_op()),
                    left_value,
                    right_value,
                )?;
                (target, Spanned::new(stmt.span, source_value))
            }
        };

        let &AssignmentTarget {
            base: target_base,
            steps: ref target_steps,
        } = &target;

        // store result
        match target_base.inner {
            SignalOrVariable::Signal(target_base_signal) => {
                let target_base = Spanned::new(target_base.span, target_base_signal);
                let flow = flow.require_hardware(stmt.span, "signal assignment")?;

                // check direction
                match target_base.inner {
                    Signal::Port(port) => {
                        let port_info = &self.ports[port];
                        check_port_is_output(
                            diags,
                            port_info,
                            target_base.span,
                            "cannot assign to input port",
                            "assigning to input port here",
                        )?;
                    }
                    Signal::Wire(_) => {}
                }

                // suggest domain
                let flow_block_kind = self.check_block_kind_and_driver_type(flow, target_base)?;
                let suggested_domain = match flow_block_kind {
                    BlockKind::Clocked(domain) => domain.map_inner(ValueDomain::Sync),
                    BlockKind::Combinatorial => Spanned::new(source_value.span, source_value.inner.domain()),
                };
                let target_base_domain = target_base_signal.suggest_domain(self, suggested_domain)?;

                // check domain
                self.check_assignment_domains(
                    flow_block_kind,
                    flow.condition_domains(),
                    op.span,
                    target_base_domain,
                    target_steps,
                    Spanned::new(source_value.span, source_value.inner.domain()),
                )?;

                // suggest type
                if target_steps.is_empty() {
                    if let Ok(source_ty) = source_value.inner.ty().as_hardware_type(elab) {
                        target_base_signal.suggest_ty(
                            self,
                            flow.get_ir_wires_mut(),
                            Spanned::new(source_value.span, &source_ty),
                        )?;
                    }
                }

                // check type
                let (target_base_ty, target_base_ir) = target_base_signal.expect_ty_and_ir(self, target_base.span)?;
                let target_base_ty = target_base_ty.cloned();
                let (target_ty, target_steps_ir) = target_steps.apply_to_hardware_type(
                    refs,
                    &mut self.large,
                    flow.get_ir_signals(),
                    flow.get_ir_variables(),
                    target_base_ty.as_ref(),
                )?;
                let reason = TypeContainsReason::Assignment {
                    span_target: target_expr.span,
                    span_target_ty: target_base_ty.span,
                };
                check_type_contains_value(refs, reason, &target_ty.as_type(), source_value.as_ref())?;

                // convert source to hardware type and value
                //   (don't expand to the target type yet, then flow could not see the more specific type)
                let source_ty_hw = source_value
                    .inner
                    .ty()
                    .as_hardware_type(elab)
                    .map_err(|_: NonHardwareType| {
                        diags.report_error_internal(stmt.span, "source type subtype not somehow non-hardware")
                    })?;
                let source_value_hw = source_value.inner.as_hardware_value_unchecked(
                    refs,
                    &mut self.large,
                    source_value.span,
                    source_ty_hw,
                )?;

                // append store statement
                let value_hardware_expanded =
                    source_value_hw.as_hardware_value_unchecked(refs, &mut self.large, source_value.span, target_ty)?;
                let ir_target = IrAssignmentTarget {
                    base: IrSignalOrVariable::Signal(target_base_ir),
                    steps: target_steps_ir,
                };
                let ir_stmt = IrStatement::Assign(ir_target, value_hardware_expanded.expr);
                flow.push_ir_statement(Spanned::new(stmt.span, ir_stmt));

                // report assignment to flow
                let result_value = if target_steps.is_empty() {
                    Some(source_value.inner)
                } else if let Ok(source_value_compile) = CompileValue::try_from(&source_value.inner)
                    && let Some(target_base_value) = flow.signal_eval_if_compile(target_base)?
                    && let Ok(target_steps) = target_steps.try_as_compile()
                {
                    let mut result_value = target_base_value.clone();
                    target_steps.set_compile_value(
                        refs,
                        Spanned::new(target_base.span, &mut result_value),
                        op.span,
                        Spanned::new(source_value.span, source_value_compile),
                    )?;
                    Some(ValueWithImplications::simple(Value::from(result_value)))
                } else {
                    None
                };
                flow.signal_report_assignment(target_base, result_value);
            }
            SignalOrVariable::Variable(target_base_var) => {
                let target_base = Spanned::new(target_base.span, target_base_var);

                // check mutable or first assignment
                let var_info = flow.var_info(target_base)?;
                if !(var_info.mutable || (target_steps.is_empty() && flow.var_is_not_yet_assigned(target_base)?)) {
                    return Err(DiagnosticError::new(
                        "cannot assign to immutable variable",
                        target_base.span,
                        "variable assigned to here",
                    )
                    .add_info(var_info.span_decl, "variable declared as immutable here")
                    .report(diags));
                }

                // check type
                let target_base_ty = var_info.ty.clone();
                if let Some(target_base_ty) = &target_base_ty {
                    let source_expected_ty = target_steps.apply_to_expected_type(refs, target_base_ty.clone())?;
                    let reason = TypeContainsReason::Assignment {
                        span_target: target_expr.span,
                        span_target_ty: target_base_ty.span,
                    };
                    check_type_contains_value(refs, reason, &source_expected_ty, source_value.as_ref())?;
                }

                if target_steps.is_empty() {
                    // simple step-less assignment, just do it
                    // (this is a separate case to avoid evaluating the current value)
                    flow.var_set(refs, target_base_var, stmt.span, Ok(source_value.inner))?;
                } else {
                    let target_base_value = flow.var_eval_without_copy(&mut self.large, target_base)?;

                    // check if we can do this assignment at compile-time
                    if let Ok(target_base_value_compile) = CompileValue::try_from(&target_base_value)
                        && let Ok(source_value_compile) = CompileValue::try_from(&source_value.inner)
                        && let Ok(target_steps_compile) = target_steps.try_as_compile()
                    {
                        let mut result_value = target_base_value_compile.clone();
                        target_steps_compile.set_compile_value(
                            refs,
                            Spanned::new(target_base.span, &mut result_value),
                            op.span,
                            Spanned::new(source_value.span, source_value_compile),
                        )?;

                        flow.var_set_compile(target_base_var, stmt.span, Ok(result_value))?;
                    } else {
                        // we need to do a hardware assignment
                        let flow = flow.require_hardware(stmt.span, "hardware variable assignment")?;

                        // decide on a target (hardware) type
                        //   if the var has a type hint use that, otherwise use the current type of the value
                        let (target_base_ty, target_base_ty_origin) = match target_base_ty {
                            Some(target_base_ty) => (target_base_ty, "type from this type hint"),
                            None => (
                                Spanned::new(target_base.span, target_base_value.ty()),
                                "type based on the current value",
                            ),
                        };
                        let target_base_ty_hw =
                            target_base_ty
                                .inner
                                .as_hardware_type(elab)
                                .map_err(|_: NonHardwareType| {
                                    DiagnosticError::new(
                                        "failed to determine hardware type for variable",
                                        target_base.span,
                                        format!(
                                            "type `{}` is not representable in hardware",
                                            target_base_ty.inner.value_string(refs)
                                        ),
                                    )
                                    .add_info(target_base_ty.span, target_base_ty_origin)
                                    .add_info(op.span, "necessary because of this hardware partial assignment")
                                    .report(diags)
                                })?;

                        // convert target value to hardware
                        let target_base_value = target_base_value.into_value().as_hardware_value_unchecked(
                            refs,
                            &mut self.large,
                            target_base.span,
                            target_base_ty_hw.clone(),
                        )?;

                        // decide the source value type
                        let (source_ty_hw, target_steps_ir) = target_steps.apply_to_hardware_type(
                            refs,
                            &mut self.large,
                            flow.get_ir_signals(),
                            flow.get_ir_variables(),
                            Spanned::new(target_base.span, &target_base_ty_hw),
                        )?;

                        // convert source value to hardware
                        let reason = TypeContainsReason::Assignment {
                            span_target: target_expr.span,
                            span_target_ty: target_base_ty.span,
                        };
                        check_type_contains_value(refs, reason, &source_ty_hw.as_type(), source_value.as_ref())?;
                        let source_value_hw = source_value.inner.as_hardware_value_unchecked(
                            refs,
                            &mut self.large,
                            source_value.span,
                            source_ty_hw,
                        )?;

                        // determine the result domain
                        let mut result_domain = target_base_value.domain().join(source_value_hw.domain);
                        target_steps.for_each_domain(|d| {
                            result_domain = result_domain.join(d.inner);
                        });

                        // make sure the target is an ir variable, reusing the existing variable if possible
                        let target_base_var_ir = match &target_base_value.expr {
                            &IrExpression::Variable(var) => var,
                            _ => {
                                let debug_info_id = flow
                                    .var_info(target_base)?
                                    .id
                                    .str(&refs.shared.interner)
                                    .map(str::to_owned);
                                flow.store_hardware_value_in_new_ir_variable(
                                    refs,
                                    target_base.span,
                                    debug_info_id,
                                    target_base_value,
                                )
                                .expr
                            }
                        };

                        // actually do the assignment
                        let ir_target = IrAssignmentTarget {
                            base: IrSignalOrVariable::Variable(target_base_var_ir),
                            steps: target_steps_ir,
                        };
                        let ir_stmt = IrStatement::Assign(ir_target, source_value_hw.expr);
                        flow.push_ir_statement(Spanned::new(stmt.span, ir_stmt));

                        // report the assignment to flow
                        //   (this is a stepped assignment, so there are no implications)
                        let result_value = HardwareValue {
                            ty: target_base_ty_hw,
                            domain: result_domain,
                            expr: target_base_var_ir,
                        };
                        let result_value = HardwareValueWithImplications::simple(result_value);
                        flow.var_set_without_copy(target_base_var, stmt.span, Ok(VarSetValue::Hardware(result_value)))?;
                    }
                }
            }
        }

        Ok(())
    }

    fn check_block_kind_and_driver_type(
        &self,
        flow: &mut FlowHardware,
        target_base_signal: Spanned<Signal>,
    ) -> DiagResult<BlockKind> {
        let diags = self.refs.diags;

        let block_kind = match flow.process_kind() {
            HardwareProcessKind::CombinatorialProcessBody { span_keyword: _ } => BlockKind::Combinatorial,
            HardwareProcessKind::ClockedProcessBody {
                span_keyword: _,
                domain,
                registers,
            } => {
                if !registers.contains_key(&target_base_signal.inner) {
                    let signal_kind = target_base_signal.inner.kind_str();
                    let signal_decl_span = match target_base_signal.inner {
                        Signal::Port(signal) => self.ports[signal].span,
                        Signal::Wire(signal) => self.wires[signal].span_decl(),
                    };

                    return Err(DiagnosticError::new(
                        format!("clocked process cannot drive {signal_kind} without marking it as a register"),
                        target_base_signal.span,
                        "driven incorrectly here",
                    )
                        .add_info(signal_decl_span, format!("{signal_kind} declared here"))
                        .add_footer_hint(
                            format!("to mark the {signal_kind} as a register, add `reg wire <name> = <reset>;` to the body of the process"),
                        )
                        .add_footer_hint(
                            format!("to drive the {signal_kind} combinatorially, use a combinatorial process or an instance port"),
                        )
                        .report(diags));
                }

                BlockKind::Clocked(*domain)
            }
            HardwareProcessKind::WireExpression {
                span_keyword: _,
                span_init,
            } => {
                return Err(DiagnosticError::new(
                    "assigning to signals is only allowed in processes",
                    target_base_signal.span,
                    "assigning to signal here",
                )
                .add_info(*span_init, "the current context is a wire expression")
                .report(diags));
            }
            HardwareProcessKind::InstancePortConnection { span_connection } => {
                return Err(DiagnosticError::new(
                    "assigning to signals is only allowed in processes",
                    target_base_signal.span,
                    "assigning to signal here",
                )
                .add_info(*span_connection, "the current context is an instance connection")
                .report(diags));
            }
        };
        Ok(block_kind)
    }

    fn check_assignment_domains(
        &self,
        block_kind: BlockKind,
        condition_domains: impl Iterator<Item = Spanned<ValueDomain>>,
        op_span: Span,
        target_base_domain: Spanned<ValueDomain>,
        steps: &TargetSteps,
        value_domain: Spanned<ValueDomain>,
    ) -> DiagResult {
        match block_kind {
            BlockKind::Combinatorial => {
                let mut check = self.check_valid_domain_crossing(
                    op_span,
                    value_domain,
                    target_base_domain,
                    "value to target in combinatorial block",
                );

                steps.for_each_domain(|d| {
                    let c = self.check_valid_domain_crossing(
                        op_span,
                        d,
                        target_base_domain,
                        "step to target in combinatorial block",
                    );
                    check = check.and(c);
                });

                for condition_domain in condition_domains {
                    let c = self.check_valid_domain_crossing(
                        op_span,
                        condition_domain,
                        target_base_domain,
                        "condition to target in combinatorial block",
                    );
                    check = check.and(c);
                }

                check
            }
            BlockKind::Clocked(block_domain) => {
                let block_domain = block_domain.map_inner(ValueDomain::Sync);
                let mut check = self.check_valid_domain_crossing(
                    op_span,
                    block_domain,
                    target_base_domain,
                    "clocked block to target",
                );

                steps.for_each_domain(|d| {
                    let c = self.check_valid_domain_crossing(op_span, d, block_domain, "step to clocked block");
                    check = check.and(c);
                });

                let c = self.check_valid_domain_crossing(op_span, value_domain, block_domain, "value to clocked block");
                check = check.and(c);

                check
            }
        }
    }
}
