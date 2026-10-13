use crate::front::check::{TypeContainsReason, check_type_is_bool, check_type_is_string, check_type_is_string_compile};
use crate::front::compile::CompileItemContext;
use crate::front::diagnostic::{DiagResult, DiagnosticError};
use crate::front::domain::ValueDomain;
use crate::front::expression::NamedOrValue;
use crate::front::flow::{Flow, FlowKind, ImplicationContradiction};
use crate::front::implication::ValueWithImplications;
use crate::front::scope::{NamedValue, Scope};
use crate::front::signal::SignalOrVariable;
use crate::front::string::hardware_print_string;
use crate::front::types::{HardwareType, Type, Typed};
use crate::front::value::{CompileValue, HardwareValue, MaybeCompile, NotCompile, SimpleCompileValue, Value};
use crate::mid::ir::{IrExpression, IrStatement};
use crate::syntax::ast::{Arg, Args, Expression, ExpressionKind, StringPiece};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::syntax::token::TOKEN_STR_BUILTIN;
use crate::util::range_multi::MultiRange;
use std::sync::Arc;

impl CompileItemContext<'_, '_> {
    pub fn eval_type_of(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr_span: Span,
        args: &Args,
    ) -> DiagResult<Type> {
        let diags = self.refs.diags;

        // check single unnamed arg
        // TODO extract common code, there are probably other users of this pattern
        const ARG_DIAG_TITLE: &str = "`type(...)` only takes a single unnamed argument";

        let mut arg_expr = None;
        let mut scope_args = scope.new_child(args.span());
        self.elaborate_extra_list(&mut scope_args, flow, args, false, &mut |_, _, _, arg| {
            let &Arg { span: _, name, value } = arg;

            if let Some(name) = name {
                return Err(diags.report_error_simple(
                    ARG_DIAG_TITLE,
                    name.span(),
                    "tried to pass named argument here",
                ));
            }
            if arg_expr.is_some() {
                return Err(diags.report_error_simple(ARG_DIAG_TITLE, args.span(), "too many arguments passed here"));
            }

            arg_expr = Some(value);
            Ok(())
        })?;

        let Some(arg_expr) = arg_expr else {
            return Err(diags.report_error_simple(ARG_DIAG_TITLE, args.span(), "no arguments passed here"));
        };

        // eval id
        let &ExpressionKind::Id(id) = self.refs.get_expr(arg_expr) else {
            return Err(diags.report_error_simple(
                "`type(...)` only works on identifiers, not general expressions",
                arg_expr.span,
                "tried to pass non-identifier here",
            ));
        };
        let id = self.eval_id(scope, flow, id)?;

        // eval named
        let named = self.eval_scoped_as_named(scope, flow, id)?;

        // get type
        let ty = match named {
            NamedOrValue::Value(value) => value.ty(),
            NamedOrValue::Named(value) => match value {
                NamedValue::Variable(var) => {
                    flow.type_of(self, Spanned::new(id.span, SignalOrVariable::Variable(var)))?
                }
                NamedValue::Signal(signal) => {
                    flow.type_of(self, Spanned::new(id.span, SignalOrVariable::Signal(signal)))?
                }
                NamedValue::Interface(_) => return Err(diags.report_error_todo(expr_span, "typeof for interfaces")),
            },
        };
        Ok(ty)
    }

    pub fn eval_builtin(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        expr_span: Span,
        target_span: Span,
        args: &Spanned<Vec<Expression>>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let diags = self.refs.diags;

        // evaluate the first two arguments as string literals
        if args.inner.len() < 2 {
            return Err(diags.report_error_internal(
                args.span,
                format!("{TOKEN_STR_BUILTIN} requires at least two arguments"),
            ));
        }
        let arg_0 = self.eval_expression_as_compile(
            scope,
            flow,
            &Type::String,
            args.inner[0],
            Spanned::new(target_span, "builtin arg"),
        )?;
        let arg_1 = self.eval_expression_as_compile(
            scope,
            flow,
            &Type::String,
            args.inner[1],
            Spanned::new(target_span, "builtin arg"),
        )?;
        let args_rest = &args.inner[2..];

        let type_reason = TypeContainsReason::Operator(target_span);
        let arg_0 = check_type_is_string_compile(refs, type_reason, arg_0)?;
        let arg_1 = check_type_is_string_compile(refs, type_reason, arg_1)?;

        // handle the different builtins
        match (arg_0.as_str(), arg_1.as_str(), args_rest) {
            // types
            ("type", "any", &[]) => Ok(Value::new_ty(Type::Any)),
            ("type", "bool", &[]) => Ok(Value::new_ty(Type::Bool)),
            ("type", "str", &[]) => Ok(Value::new_ty(Type::String)),
            ("type", "int", &[]) => Ok(Value::new_ty(Type::Int(MultiRange::open()))),
            ("type", "Tuple", &[]) => Ok(Value::new_ty(Type::Tuple(None))),
            ("type", "Range", &[]) => Ok(Value::new_ty(Type::Range)),
            ("type", "Function", &[]) => Ok(Value::new_ty(Type::Function)),
            ("type", "Module", &[]) => Ok(Value::new_ty(Type::Module)),
            ("type", "Interface", &[]) => Ok(Value::new_ty(Type::Interface)),
            ("type", "InterfaceView", &[]) => Ok(Value::new_ty(Type::InterfaceView)),
            ("type", "Package", &[]) => Ok(Value::new_ty(Type::HierarchyNode)),
            ("type", "Ref", &[ty]) => {
                let ty_inner = self.eval_expression_as_ty(scope, flow, ty)?;
                let ty = Type::Ref(Arc::new(ty_inner.inner));
                Ok(Value::new_ty(ty))
            }
            ("type", "RefInterface", &[intf]) => {
                let reason = Spanned::new(expr_span, "interface reference inner type");
                let intf = self.eval_expression_as_compile(scope, flow, &Type::Interface, intf, reason)?;

                if let CompileValue::Simple(SimpleCompileValue::Interface(intf)) = intf.inner {
                    let ty = Type::RefInterface(intf);
                    Ok(Value::new_ty(ty))
                } else {
                    Err(diags.report_error_internal(intf.span, "expected interface"))
                }
            }

            // print
            ("fn", "print", &[msg]) => {
                let msg = self.eval_expression(scope, flow, &Type::String, msg)?;

                let reason_str = TypeContainsReason::Internal(expr_span);
                let msg = check_type_is_string(refs, reason_str, msg)?;

                match flow.kind_mut() {
                    FlowKind::Compile(_) => {
                        let msg = msg.try_as_compile().map_err(|_: NotCompile| {
                            diags.report_error_internal(expr_span, "non-compile message in compile flow")
                        })?;
                        self.refs.print_handler.print(&msg);
                    }
                    FlowKind::Hardware(flow) => {
                        hardware_print_string(self.refs, flow, &mut self.large, expr_span, &msg);
                    }
                }

                Ok(Value::unit())
            }

            // assert
            ("fn", "assert_fail", &[msg]) => {
                // TODO for compile-time, include entire stack trace (handled by diagnostics)
                //      for hardware, include the source location of the caller (enough levels up, maybe with a marker per function?)
                let msg = self.eval_expression(scope, flow, &Type::String, msg)?;

                let reason_str = TypeContainsReason::Internal(expr_span);
                let msg = check_type_is_string(refs, reason_str, msg)?;

                const ASSERT_PREFIX: &str = "assertion failed";
                match flow.kind_mut() {
                    FlowKind::Compile(_) => {
                        let msg = msg.try_as_compile().map_err(|_: NotCompile| {
                            diags.report_error_internal(expr_span, "non-compile message in compile flow")
                        })?;

                        let msg = if msg.is_empty() {
                            ASSERT_PREFIX.to_string()
                        } else {
                            format!("{ASSERT_PREFIX}: `{}`", msg.as_str())
                        };

                        Err(DiagnosticError::new(msg, expr_span, "assertion failed here").report(diags))
                    }
                    FlowKind::Hardware(flow) => {
                        let mut msg = Arc::unwrap_or_clone(msg);

                        if msg.pieces.is_empty() {
                            msg.pieces
                                .push(StringPiece::Literal(Arc::new(ASSERT_PREFIX.to_string())));
                        } else {
                            msg.pieces
                                .insert(0, StringPiece::Literal(Arc::new(format!("{ASSERT_PREFIX}: `"))));
                            msg.pieces.push(StringPiece::Literal(Arc::new("`".to_string())));
                        };

                        // TODO keep the message and assert failure connected, so backends can use them properly
                        hardware_print_string(self.refs, flow, &mut self.large, expr_span, &msg);
                        flow.push_ir_statement(Spanned::new(expr_span, IrStatement::AssertFailed));

                        Ok(Value::unit())
                    }
                }
            }
            ("fn", "assume", &[cond]) => {
                let cond = self.eval_expression_with_implications(scope, flow, &Type::Bool, cond)?;

                let reason_bool = TypeContainsReason::Internal(expr_span);
                let cond = check_type_is_bool(refs, reason_bool, cond)?;

                // check constant cases
                let cond = match cond {
                    MaybeCompile::Compile(cond) => {
                        return if !cond {
                            // should have been caught by the preceding assert
                            Err(diags.report_error_internal(expr_span, "assuming false condition"))
                        } else {
                            // maybe emit a warning?
                            Ok(Value::unit())
                        };
                    }
                    MaybeCompile::Hardware(cond) => cond,
                };

                // check hardware flow
                let flow = match flow.kind_mut() {
                    FlowKind::Compile(_) => {
                        // assuming does nothing at compile time
                        return Ok(Value::unit());
                    }
                    FlowKind::Hardware(flow) => flow,
                };

                // add implications
                for implication in cond.implications.if_true {
                    match flow.add_implication(self, expr_span, implication)? {
                        Ok(()) => {}
                        Err(ImplicationContradiction) => {
                            return Err(diags.report_error_simple(
                                "contradiction due to assume",
                                expr_span,
                                "assumption here",
                            ));
                        }
                    }
                }

                Ok(Value::unit())
            }

            // casting
            ("fn", "unsafe_bool_to_clock", &[value]) => {
                let value = self.eval_expression(scope, flow, &Type::Bool, value)?;
                let value = check_type_is_bool(
                    refs,
                    TypeContainsReason::Internal(expr_span),
                    value.map_inner(ValueWithImplications::simple),
                )?;

                let expr = match value {
                    MaybeCompile::Compile(v) => IrExpression::Bool(v),
                    MaybeCompile::Hardware(v) => v.value.expr,
                };
                Ok(Value::Hardware(HardwareValue {
                    ty: HardwareType::Bool,
                    domain: ValueDomain::Clock,
                    expr,
                }))
            }
            _ => Err(diags.report_error_internal(expr_span, "invalid builtin arguments")),
        }
    }
}
