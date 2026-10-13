use crate::front::block::{BlockEnd, EarlyExitKind};
use crate::front::check::{TypeContainsReason, check_type_contains_value, check_type_is_bool_array};
use crate::front::compile::{CompileItemContext, CompileRefs, StackEntry};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError};
use crate::front::exit::{ExitFlag, ExitStack, ReturnEntry, ReturnEntryHardware, ReturnEntryKind};
use crate::front::extra::{ExtraCursor, ExtraScope};
use crate::front::flow::{Flow, FlowKind, VariableInfo};
use crate::front::implication::ValueWithImplications;
use crate::front::item::{
    ElaboratedEnum, ElaboratedEnumVariantInfo, ElaboratedStruct, ElaboratedStructInfo, FunctionItemBody,
    UniqueDeclaration,
};
use crate::front::scope::{FrozenScope, NamedValue, Scope, ScopeKey, ScopedEntry};
use crate::front::types::{HardwareType, Type};
use crate::front::value::{
    BoundMethod, CompileValue, EnumValue, HardwareValue, MaybeCompile, MethodInfo, MixedCompoundValue, NotCompile,
    SimpleCompileValue, StructValue, Value, ValueCommon,
};
use crate::mid::bits::{FromBitsInvalidValue, FromBitsWrongLength, ToBitsWrongType};
use crate::mid::ir::{IrExpressionLarge, IrLargeArena};
use crate::syntax::ast::{
    Arg, Block, BlockStatement, Expression, ExtraList, FunctionDeclaration, MaybeIdentifier, Parameter, Parameters,
};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::ResultDoubleExt;
use crate::util::intern::Id;
use itertools::{Either, Itertools};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub enum FunctionValue {
    User(Arc<UserFunctionValue>),
    Bits(FunctionBits),
    StructNew(ElaboratedStruct),
    StructNewInfer(UniqueDeclaration),
    EnumNew(ElaboratedEnum, usize),
    EnumNewInfer(UniqueDeclaration, Id),
}

#[derive(Debug, Clone)]
pub struct FunctionBits {
    pub ty_hw: HardwareType,
    pub kind: FunctionBitsKind,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum FunctionBitsKind {
    ToBits,
    FromBits { is_unsafe: bool },
}

// TODO find a better name for this
#[derive(Debug, Clone)]
pub struct UserFunctionValue {
    // only used for uniqueness
    // TODO switch to newer UniqueDeclaration?
    pub span_decl: Span,
    pub scope_captured: Arc<FrozenScope>,

    // TODO point into ast instead of storing a clone here
    pub params: Arc<ExtraList<Parameter>>,
    pub body: Spanned<FunctionBody<'static>>,
}

// TODO this is a weird struct, rework this
#[derive(Debug, Clone)]
pub enum FunctionBody<'a> {
    ItemBody(FunctionItemBody),
    FunctionBodyBlockOwned {
        // TODO avoid ast clones, just refer to the ast item here
        body: Arc<Block<BlockStatement>>,
        ret_ty: Option<Expression>,
    },
    FunctionBodyBlockRef {
        body: &'a Block<BlockStatement>,
        ret_ty: Option<Expression>,
    },
}

/// Parameter specification.
#[derive(Debug, Copy, Clone)]
pub enum Param {
    /// Only accept positional.
    Positional { span: Span },
    /// Only accept named with the given name.
    Named(Spanned<Id>),
    /// Accept either positional or named with the given name.
    PositionalOrNamed(Spanned<Id>),
}

/// The different kinds of call arguments possible.
pub enum CallArgs<'a, 's, 'p> {
    /// Not yet evaluated AST arguments.
    Ast(AstArgs<'a, 's, 'p>),
    /// Already fully evaluated args.
    Evaluated(EvaluatedArgs),
}

pub struct AstArgs<'a, 's, 'p> {
    pub span: Span,
    pub cursor: ExtraCursor<'a, 's, 'p, Arg>,
}

pub struct EvaluatedArgs {
    pub span: Span,
    pub inner: std::vec::IntoIter<EvaluatedArg>,
}

pub type EvaluatedArg = Arg<Option<Spanned<Id>>, Spanned<ValueWithImplications>>;

impl Param {
    fn span(self) -> Span {
        match self {
            Param::Positional { span } => span,
            Param::Named(id) | Param::PositionalOrNamed(id) => id.span,
        }
    }
}

impl<'a, 's, 'p> AstArgs<'a, 's, 'p> {
    /// Pop the next argument if any, and check that it matches `param`.
    pub fn next_arg<F: Flow, R>(
        &mut self,
        ctx: &mut CompileItemContext,
        flow: &mut F,
        param: Param,
        f: impl FnOnce(&mut CompileItemContext, &Scope, &mut F, Expression) -> DiagResult<R>,
    ) -> DiagResult<Option<R>> {
        let Some(mut arg) = self.cursor.next(ctx, flow)? else {
            return Ok(None);
        };

        arg.with_scope(|scope, arg| {
            let &Arg { span, id, value } = arg;

            let scope = scope.as_scope();
            let id = id.map(|id| ctx.eval_id(scope, flow, id)).transpose()?;
            check_arg_name(ctx.refs, param, span, id)?;

            f(ctx, scope, flow, value)
        })
        .map(Some)
    }
}

impl CallArgs<'_, '_, '_> {
    pub fn span(&self) -> Span {
        match self {
            CallArgs::Ast(args) => args.span,
            CallArgs::Evaluated(args) => args.span,
        }
    }

    /// Pop and evaluate the next argument, and heck that it matches `param` and `ty`.
    pub fn next_value(
        &mut self,
        ctx: &mut CompileItemContext,
        flow: &mut impl Flow,
        param: Param,
        ty: Spanned<&Type>,
    ) -> DiagResult<Option<Spanned<ValueWithImplications>>> {
        // eval value
        let value = match self {
            CallArgs::Ast(args) => args.next_arg(ctx, flow, param, |ctx, scope, flow, expr| {
                ctx.eval_expression_with_implications(scope, flow, ty.inner, expr)
            })?,
            CallArgs::Evaluated(args) => args
                .inner
                .next()
                .map(|arg| {
                    check_arg_name(ctx.refs, param, arg.span, arg.id)?;
                    Ok(arg.value)
                })
                .transpose()?,
        };

        // check type
        let value = match value {
            None => None,
            Some(value) => {
                let reason = TypeContainsReason::Parameter { param_ty: ty.span };
                check_type_contains_value(ctx.refs, reason, ty.inner, value.as_ref())?;
                Some(value)
            }
        };

        Ok(value)
    }

    /// The same as [Self::next_value] but reports an error if there are no remaining arguments.
    pub fn require_value(
        &mut self,
        ctx: &mut CompileItemContext,
        flow: &mut impl Flow,
        param: Param,
        ty: Spanned<&Type>,
    ) -> DiagResult<Spanned<ValueWithImplications>> {
        match self.next_value(ctx, flow, param, ty)? {
            Some(value) => Ok(value),
            None => Err(error_missing_argument(ctx.refs, self.span(), param)),
        }
    }

    /// Check that all args have been used.
    pub fn finish(self, ctx: &mut CompileItemContext, flow: &mut impl Flow, span_params: Span) -> DiagResult {
        let span_leftover = match self {
            CallArgs::Ast(mut args) => args.cursor.next(ctx, flow)?.map(|arg| arg.item().span),
            CallArgs::Evaluated(mut args) => args.inner.next().map(|arg| arg.span),
        };

        match span_leftover {
            None => Ok(()),
            Some(span_leftover) => Err(DiagnosticError::new(
                "argument does not match any parameter",
                span_leftover,
                "argument passed here",
            )
            .add_info(span_params, "parameters declared here")
            .report(ctx.refs.diags)),
        }
    }
}

/// Check the `arg_id` matches `param`.
fn check_arg_name(refs: CompileRefs, param: Param, span_arg: Span, arg_id: Option<Spanned<Id>>) -> DiagResult {
    let diags = refs.diags;
    let interner = &refs.shared.interner;

    match (param, arg_id) {
        (Param::Positional { .. } | Param::PositionalOrNamed(_), None) => {
            // positional accepts no id
            Ok(())
        }
        (Param::Positional { span }, Some(arg_id)) => {
            // positional-only rejects id
            Err(DiagnosticError::new(
                "named arguments are not allowed for this call target",
                arg_id.span,
                "named argument passed here",
            )
            .add_info(span, "parameter declared here")
            .report(diags))
        }
        (Param::Named(param_id) | Param::PositionalOrNamed(param_id), Some(arg_id)) => {
            // named accepts matching id
            if param_id.inner == arg_id.inner {
                Ok(())
            } else {
                let param_str = param_id.inner.str(interner);
                let arg_str = arg_id.inner.str(interner);
                Err(DiagnosticError::new(
                    "argument name does not match the parameter at this position",
                    arg_id.span,
                    format!("argument `{arg_str}` passed here, expected `{param_str}`"),
                )
                .add_info(param_id.span, "parameter declared here")
                .add_footer_hint("arguments must be passed in parameter order")
                .report(diags))
            }
        }
        (Param::Named(param_id), None) => {
            // named-only rejects no id
            let param_str = param_id.inner.str(interner);
            Err(DiagnosticError::new(
                "positional arguments are not allowed for this call target",
                span_arg,
                "positional argument passed here",
            )
            .add_info(param_id.span, "parameter declared here")
            .add_footer_hint(format!("pass the argument by name using `{param_str}=`"))
            .report(diags))
        }
    }
}

pub fn error_missing_argument(refs: CompileRefs, span_args: Span, param: Param) -> DiagError {
    let title = match param {
        Param::Positional { .. } => "missing argument".to_owned(),
        Param::Named(id) | Param::PositionalOrNamed(id) => {
            format!(
                "missing argument for parameter `{}`",
                id.inner.str(&refs.shared.interner)
            )
        }
    };
    DiagnosticError::new(title, Span::empty_at(span_args.end()), "missing argument here")
        .add_info(param.span(), "parameter declared here")
        .report(refs.diags)
}

pub fn require_compile_arg(
    refs: CompileRefs,
    what: &str,
    value: Spanned<&ValueWithImplications>,
) -> DiagResult<CompileValue> {
    CompileValue::try_from(value.inner).map_err(|_: NotCompile| {
        refs.diags.report_error_simple(
            format!("{what} must be compile-time"),
            value.span,
            "hardware value passed here",
        )
    })
}

impl CompileItemContext<'_, '_> {
    pub fn call_function(
        &mut self,
        flow: &mut impl Flow,
        expected_ty: &Type,
        span_target: Span,
        span_call: Span,
        function: &FunctionValue,
        args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let err_infer_any = |kind: &str, span_decl: Span| {
            error_cannot_infer_generic_params(kind, span_target, span_call, span_decl, None).report(diags)
        };
        let err_infer_mismatch = |kind: &str, actual_span: Span| {
            DiagnosticError::new(
                "mismatching expected type",
                actual_span,
                format!("{kind} type set here"),
            )
            .add_info(
                span_call,
                format!(
                    "expected type `{}` does not match this {kind}",
                    expected_ty.value_string(refs)
                ),
            )
            .report(self.refs.diags)
        };

        match function {
            FunctionValue::User(function) => {
                let UserFunctionValue {
                    span_decl,
                    scope_captured,
                    params,
                    body,
                } = &**function;
                self.call_user_function(flow, *span_decl, scope_captured, params, body, span_call, None, args)
            }
            FunctionValue::Bits(function) => self.call_bits_function(flow, span_call, span_target, function, args),
            &FunctionValue::StructNew(struct_elab) => self.call_struct_new(flow, struct_elab, args),
            &FunctionValue::StructNewInfer(func_unique) => match *expected_ty {
                Type::Struct(expected_elab) => {
                    let expected_info = self.refs.shared.elaboration_arenas.struct_info(expected_elab);
                    if expected_info.unique == func_unique {
                        self.call_struct_new(flow, expected_elab, args)
                    } else {
                        Err(error_unique_mismatch(
                            "struct",
                            span_target,
                            expected_info.unique.id().span(),
                            func_unique.id().span(),
                        )
                        .report(diags))
                    }
                }
                Type::Any => Err(err_infer_any("struct", func_unique.id().span())),
                _ => Err(err_infer_mismatch("struct", func_unique.id().span())),
            },
            &FunctionValue::EnumNew(enum_elab, variant_index) => {
                self.call_enum_new(flow, span_call, enum_elab, variant_index, args)
            }
            &FunctionValue::EnumNewInfer(func_unique, variant_id) => match expected_ty {
                &Type::Enum(expected_elab) => {
                    let expected_info = self.refs.shared.elaboration_arenas.enum_info(expected_elab);

                    if expected_info.unique == func_unique {
                        let variant_index = expected_info.variant_index(refs, Spanned::new(span_target, variant_id))?;
                        self.call_enum_new(flow, span_call, expected_elab, variant_index, args)
                    } else {
                        Err(error_unique_mismatch(
                            "enum",
                            span_target,
                            expected_info.unique.id().span(),
                            func_unique.id().span(),
                        )
                        .report(diags))
                    }
                }
                Type::Any => Err(err_infer_any("enum", func_unique.id().span())),
                _ => Err(err_infer_mismatch("enum", func_unique.id().span())),
            },
        }
    }

    pub fn call_bound_method(
        &mut self,
        flow: &mut impl Flow,
        span_call: Span,
        method: &BoundMethod<Value>,
        args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        // TODO propagate self type too
        let BoundMethod {
            self_type: _,
            self_value,
            method,
        } = method;
        let MethodInfo {
            scope,
            name: _,
            func_decl,
        } = &**method;
        let &FunctionDeclaration {
            span: span_decl,
            id: _,
            ref params,
            ret_ty,
            ref body,
        } = func_decl;
        let Parameters {
            span: _,
            slf: self_param,
            items: param_items,
        } = params;

        let self_value = Spanned::new(self_param.span, self_value.as_ref().clone());
        let func_body = FunctionBody::FunctionBodyBlockRef { body, ret_ty };

        self.call_user_function(
            flow,
            span_decl,
            scope,
            param_items,
            &Spanned::new(span_decl, func_body),
            span_call,
            Some(self_value),
            args,
        )
    }

    fn call_struct_new(
        &mut self,
        flow: &mut impl Flow,
        elab: ElaboratedStruct,
        mut args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let &ElaboratedStructInfo {
            unique: _,
            debug_info_name: _,
            span_body,
            ref fields,
            hw: _,
            members_static: _,
            methods_self: _,
        } = refs.shared.elaboration_arenas.struct_info(elab);

        let mut field_values = vec![];
        for field in fields.values() {
            let value = args.require_value(self, flow, Param::Named(field.id), field.ty.as_ref())?;
            field_values.push(value.inner.into_value());
        }
        args.finish(self, flow, span_body)?;

        let result = StructValue {
            ty: elab,
            fields: field_values,
        };
        Ok(Value::Compound(MixedCompoundValue::Struct(result)))
    }

    fn call_enum_new(
        &mut self,
        flow: &mut impl Flow,
        span_call: Span,
        elab: ElaboratedEnum,
        variant_index: usize,
        mut args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let enum_info = refs.shared.elaboration_arenas.enum_info(elab);
        let &ElaboratedEnumVariantInfo {
            id: variant_id,
            ref payload_ty,
        } = &enum_info.variants[variant_index];

        let payload_ty = payload_ty.as_ref().ok_or_else(|| {
            DiagnosticError::new(
                "trying to call enum variant without payload",
                span_call,
                "calling enum variant here",
            )
            .add_info(variant_id.span(), "enum variant declared without payload here")
            .report(refs.diags)
        })?;

        let param = Param::Positional { span: payload_ty.span };
        let payload = args.require_value(self, flow, param, payload_ty.as_ref())?;
        args.finish(self, flow, payload_ty.span)?;

        let result = EnumValue {
            ty: elab,
            variant: variant_index,
            payload: Some(Box::new(payload.inner.into_value())),
        };
        Ok(Value::Compound(MixedCompoundValue::Enum(result)))
    }

    fn call_user_function(
        &mut self,
        flow: &mut impl Flow,
        // function
        span_decl: Span,
        scope_captured: &Arc<FrozenScope>,
        params: &ExtraList<Parameter>,
        body: &Spanned<FunctionBody>,
        // args
        span_call: Span,
        arg_self: Option<Spanned<Value>>,
        args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let entry = StackEntry::FunctionCall(span_call);
        self.recurse(entry, |s| {
            s.call_user_function_inner(flow, span_decl, scope_captured, params, body, arg_self, args)
        })
        .flatten_err()
    }

    fn call_user_function_inner(
        &mut self,
        flow: &mut impl Flow,
        // function
        span_decl: Span,
        scope_captured: &Arc<FrozenScope>,
        params: &ExtraList<Parameter>,
        body: &Spanned<FunctionBody>,
        // args
        arg_self: Option<Spanned<Value>>,
        args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        self.refs.check_should_stop(span_decl)?;

        // decide whether to allow hardware/reference values
        let args_must_be_compile_without_ref = match body.inner {
            FunctionBody::ItemBody(_) => true,
            FunctionBody::FunctionBodyBlockOwned { .. } | FunctionBody::FunctionBodyBlockRef { .. } => false,
        };

        // create parameter scope
        let scope_captured = Arc::clone(scope_captured).as_scope();
        let params_scope_span = params.span.join(body.span);
        let mut params_scope = scope_captured.new_child(params_scope_span);

        // declare self
        if let Some(arg_self) = arg_self {
            params_scope.declare(
                self.refs,
                ScopeKey::Slf(arg_self.span),
                Ok(ScopedEntry::Value(arg_self.inner)),
            );
        };

        // create parameter cursor
        let params_scope = ExtraScope::new(None, &mut params_scope);
        let mut params_cursor = ExtraCursor::new(params_scope, &params.items, true);

        // walk over parameters and arguments in lockstep
        let mut args = args;
        let mut param_values_flat = vec![];
        while let Some(mut param_leaf) = params_cursor.next(self, flow)? {
            let &Parameter {
                span: _,
                id: param_id,
                ty: param_ty,
                default: param_default,
            } = param_leaf.item();

            // eval param
            let (param_id, param_ty) = param_leaf.with_scope(|scope, _| -> DiagResult<_> {
                let scope = scope.as_scope();
                let param_id = self.eval_id(scope, flow, param_id)?;
                let param_ty = self.eval_expression_as_ty(scope, flow, param_ty)?;
                Ok((param_id, param_ty))
            })?;

            // eval arg
            let param_match = Param::PositionalOrNamed(param_id);
            let arg_value = args.next_value(self, flow, param_match, param_ty.as_ref())?;

            // use arg or fallback to param default
            let value = match (arg_value, param_default) {
                (Some(arg_value), _) => arg_value,
                (None, Some(param_default)) => {
                    let value = param_leaf.with_scope(|scope, _| {
                        self.eval_expression_with_implications(scope.as_scope(), flow, &param_ty.inner, param_default)
                    })?;

                    let reason = TypeContainsReason::Parameter {
                        param_ty: param_ty.span,
                    };
                    check_type_contains_value(self.refs, reason, &param_ty.inner, value.as_ref())?;

                    value
                }
                (None, None) => return Err(error_missing_argument(self.refs, args.span(), param_match)),
            };

            // check compile
            if args_must_be_compile_without_ref {
                let value_compile = require_compile_arg(self.refs, "item parameters", value.as_ref())?;
                if value_compile.definitely_contains_reference() {
                    let diag = DiagnosticError::new(
                        "item parameters cannot contain references",
                        value.span,
                        "argument containing reference passed here",
                    )
                    .add_footer_info(
                        "references must stay inside the module they belong to, they cannot escape into other items",
                    )
                    .report(self.refs.diags);
                    return Err(diag);
                }
            }

            // record value into vec
            param_values_flat.push((param_id, value.inner.clone()));

            // declare param in scope
            let param_var = flow.var_new_immutable_init(
                self.refs,
                MaybeIdentifier::Identifier(param_id),
                param_id.span(),
                Ok(value.inner),
            )?;
            let entry = ScopedEntry::Named(NamedValue::Variable(param_var));
            param_leaf
                .with_scope(|scope, _| scope.declare_root(self.refs, MaybeIdentifier::Identifier(param_id), Ok(entry)));
        }
        args.finish(self, flow, params.span)?;

        // we're done with the cursor, convert back to scope
        let scope_params = &*params_cursor.root_scope().as_scope();

        // run the function
        let entry = StackEntry::FunctionRun(span_decl);
        self.recurse(entry, |slf| {
            match &body.inner {
                FunctionBody::ItemBody(item_body) => {
                    // unwrap compile, we checked that these values are compile-time during argument matching
                    let param_values = param_values_flat
                        .into_iter()
                        .map(|(id, v)| (id, CompileValue::try_from(&v).unwrap()))
                        .collect_vec();

                    let mut flow_inner = flow.new_child_compile(body.span, "item body");
                    let value = slf.eval_item_function_body(
                        scope_params,
                        &mut flow_inner,
                        Some(param_values),
                        Spanned::new(body.span, item_body),
                    )?;
                    Ok(Value::from(value))
                }
                &FunctionBody::FunctionBodyBlockOwned { ref body, ret_ty } => {
                    slf.run_function_body_block(flow, scope_params, span_decl, ret_ty, body)
                }
                &FunctionBody::FunctionBodyBlockRef { body, ret_ty } => {
                    slf.run_function_body_block(flow, scope_params, span_decl, ret_ty, body)
                }
            }
        })
        .flatten_err()
    }

    fn run_function_body_block(
        &mut self,
        flow: &mut impl Flow,
        scope: &Scope,
        span_decl: Span,
        ret_ty: Option<Expression>,
        body: &Block<BlockStatement>,
    ) -> DiagResult<Value> {
        // evaluate return type
        let return_type = ret_ty
            .map(|ret_ty| self.eval_expression_as_ty(scope, flow, ret_ty))
            .transpose()?;

        // set up the stack
        let return_entry_kind = match flow.kind_mut() {
            FlowKind::Compile(_) => ReturnEntryKind::Compile,
            FlowKind::Hardware(flow) => {
                let return_flag = ExitFlag::new(self.refs, flow, span_decl, EarlyExitKind::Return)?;
                ReturnEntryKind::Hardware(ReturnEntryHardware { return_flag })
            }
        };
        let return_var = if let Some(return_type) = &return_type
            && !return_type.inner.is_unit()
        {
            let id_return_value = self.refs.shared.interner.push("return_value");
            let return_var_info = VariableInfo {
                span_decl,
                id: MaybeIdentifier::Identifier(id_return_value),
                mutable: false,
                ty: None,
                join_ir_variable: None,
            };
            let return_var = flow.var_new(return_var_info);

            // As far as the flow is concerned,
            //   it might look like not all branches are guaranteed to initialize the return value.
            // To avoid wrong error messages and skipped merging, we always start with an initial value.
            flow.var_set_undefined(return_var, span_decl)?;

            Some(return_var)
        } else {
            None
        };
        let return_entry = ReturnEntry {
            span_function_decl: span_decl,
            return_type: return_type.as_ref().map(Spanned::as_ref),
            return_var,
            kind: return_entry_kind,
        };
        let mut stack = ExitStack::new_in_function(return_entry);

        // evaluate block
        let end = self.elaborate_block(scope, flow, &mut stack, body)?;

        // check end and extract return value
        let return_entry = stack.return_info_option().unwrap();
        check_function_end(self.refs, flow, &mut self.large, body.span, return_entry, end)
    }

    fn call_bits_function(
        &mut self,
        flow: &mut impl Flow,
        span_call: Span,
        span_target: Span,
        function: &FunctionBits,
        mut args: CallArgs<'_, '_, '_>,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let FunctionBits { ty_hw, kind } = function;
        let ty_ir = ty_hw.as_ir(refs);
        let ty_bits = HardwareType::Array(Arc::new(HardwareType::Bool), ty_ir.size_bits());

        // get the single argument
        let expected_ty = match kind {
            FunctionBitsKind::ToBits => ty_hw.as_type(),
            FunctionBitsKind::FromBits { .. } => ty_bits.as_type(),
        };
        let param = Param::Positional { span: span_target };
        let value = args.require_value(self, flow, param, Spanned::new(span_target, &expected_ty))?;
        args.finish(self, flow, span_target)?;
        let span_value = value.span;

        // actual implementation
        match *kind {
            FunctionBitsKind::ToBits => {
                // try as compile-time first so we get compile-time bits back
                match CompileValue::try_from(&value.inner) {
                    Ok(value) => {
                        let bits = ty_hw.value_to_bits(refs, &value).map_err(|_: ToBitsWrongType| {
                            diags.report_error_internal(span_call, "value_to_bits wrong type")
                        })?;
                        let bits_wrapped = bits.into_iter().map(CompileValue::new_bool).collect_vec();
                        Ok(Value::Simple(SimpleCompileValue::Array(Arc::new(bits_wrapped))))
                    }
                    Err(NotCompile) => {
                        let value =
                            value
                                .inner
                                .as_hardware_value_unchecked(refs, &mut self.large, span_call, ty_hw.clone())?;
                        let value_bits = HardwareValue {
                            ty: ty_bits,
                            domain: value.domain,
                            expr: self.large.push_expr(IrExpressionLarge::ToBits(ty_ir, value.expr)),
                        };
                        Ok(Value::Hardware(value_bits))
                    }
                }
            }
            FunctionBitsKind::FromBits { is_unsafe } => {
                let value = check_type_is_bool_array(
                    refs,
                    TypeContainsReason::Operator(span_call),
                    value.map_inner(|v| v.into_value()),
                    Some(ty_ir.size_bits()),
                )?;

                let result = match value {
                    MaybeCompile::Compile(v) => {
                        let result = ty_hw.value_from_bits(refs, &v).map_err(|e| match e {
                            Either::Left(FromBitsInvalidValue) => {
                                if is_unsafe {
                                    DiagnosticError::new(
                                        "invalid bit pattern for type",
                                        span_value,
                                        format!("got bits `{v:?}`"),
                                    )
                                    .add_info(span_target, format!("target type `{}`", ty_hw.value_string(refs)))
                                    .report(diags)
                                } else {
                                    diags.report_error_internal(
                                        span_call,
                                        "value_from_bits invalid value but not unsafe",
                                    )
                                }
                            }
                            Either::Right(FromBitsWrongLength) => {
                                diags.report_error_internal(span_call, "value_from_bits wrong length")
                            }
                        })?;
                        Value::from(result)
                    }
                    MaybeCompile::Hardware(v) => {
                        let expr = self.large.push_expr(IrExpressionLarge::FromBits(ty_ir, v.expr));
                        Value::Hardware(HardwareValue {
                            ty: ty_hw.clone(),
                            domain: v.domain,
                            expr,
                        })
                    }
                };
                Ok(result)
            }
        }
    }
}

pub fn check_function_return_type_and_set_value(
    refs: CompileRefs,
    flow: &mut impl Flow,
    entry: &ReturnEntry,
    span_stmt: Span,
    span_keyword: Span,
    value: Option<Spanned<ValueWithImplications>>,
) -> DiagResult {
    let diags = refs.diags;

    let ty = entry.return_type;

    match (ty, value) {
        (None, None) => {}
        (Some(ty), Some(value)) => {
            let reason = TypeContainsReason::Return {
                span_keyword,
                span_return_ty: ty.span,
            };
            let result_ty = check_type_contains_value(refs, reason, ty.inner, value.as_ref());

            if let Some(return_var) = entry.return_var {
                flow.var_set(refs, return_var, span_stmt, result_ty.map(|()| value.inner))?;
            }

            result_ty?;
        }
        (Some(ty), None) => {
            let diag = DiagnosticError::new(
                "missing return value in function with return type",
                span_keyword,
                "return without value here",
            )
            .add_info(
                ty.span,
                format!("function return type `{}` declared here", ty.inner.value_string(refs)),
            )
            .add_footer_hint("either return a value or remove the return type")
            .report(diags);
            return Err(diag);
        }
        (None, Some(value)) => {
            let diag = DiagnosticError::new(
                "return value in function without return type",
                value.span,
                "return value here",
            )
            .add_info(entry.span_function_decl, "function declared without return type here")
            .add_footer_hint(
                "either remove the returned value or add a return type using `-> <type>` after the parameter list",
            )
            .report(diags);
            return Err(diag);
        }
    }

    Ok(())
}

fn check_function_end(
    refs: CompileRefs,
    flow: &mut impl Flow,
    large: &mut IrLargeArena,
    body_span: Span,
    return_entry: &ReturnEntry,
    end: BlockEnd,
) -> DiagResult<Value> {
    let diags = refs.diags;

    // some of these should be impossible, but checking again here is redundant
    let is_certain_return = match end {
        BlockEnd::Unreachable => true,
        BlockEnd::CompileExit(end) => match end {
            EarlyExitKind::Return => true,
            EarlyExitKind::Break => false,
            EarlyExitKind::Continue => false,
        },
        BlockEnd::Normal => false,
        BlockEnd::HardwareExit(_) => false,
        BlockEnd::HardwareMaybeExit(_) => false,
    };

    let value = if is_certain_return {
        if let Some(var) = return_entry.return_var {
            // normal return, get the value
            flow.var_eval(refs, large, Spanned::new(body_span, var))
                .map_err(|_: DiagError| diags.report_error_internal(body_span, "failed to evaluate return value"))?
        } else {
            // normal return with unit return type, return unit
            Value::unit()
        }
    } else {
        // the end of the body might be reachable, this is only okay for functions without a return type
        match return_entry.return_type {
            None => Value::unit(),
            Some(return_type) => {
                let diag = DiagnosticError::new(
                    "missing return in function",
                    Span::empty_at(body_span.end()),
                    "end of function is reached here",
                )
                .add_info(
                    return_type.span,
                    format!("return type `{}` declared here", return_type.inner.value_string(refs)),
                )
                .report(diags);
                return Err(diag);
            }
        }
    };
    Ok(value.into_value())
}

impl Eq for FunctionValue {}

impl FunctionValue {
    fn equality_key(&self) -> impl Eq + Hash + '_ {
        #[derive(Eq, PartialEq, Hash)]
        enum Key<'a> {
            User(Span, *const FrozenScope),
            Bits(&'a HardwareType, FunctionBitsKind),
            StructNew(ElaboratedStruct),
            StructNewInfer(UniqueDeclaration),
            EnumNew(ElaboratedEnum, usize),
            EnumNewInfer(UniqueDeclaration, Id),
        }

        match self {
            FunctionValue::User(func) => {
                let &UserFunctionValue {
                    span_decl,
                    ref scope_captured,
                    ref params,
                    ref body,
                } = &**func;

                // these are both derivable from the span_decl, so redundant
                let _ = (params, body);

                // deduplicate based on captured scope equality (by pointer)
                //   we could compare by full contents equality, but that is more expensive and complicated
                Key::User(span_decl, Arc::as_ptr(scope_captured))
            }
            FunctionValue::Bits(FunctionBits { ty_hw: ty, kind }) => Key::Bits(ty, *kind),
            FunctionValue::StructNew(elab) => Key::StructNew(*elab),
            &FunctionValue::StructNewInfer(ref_struct) => Key::StructNewInfer(ref_struct),
            FunctionValue::EnumNew(elab, index) => Key::EnumNew(*elab, *index),
            &FunctionValue::EnumNewInfer(ref_struct, variant) => Key::EnumNewInfer(ref_struct, variant),
        }
    }
}

impl PartialEq for FunctionValue {
    fn eq(&self, other: &Self) -> bool {
        self.equality_key() == other.equality_key()
    }
}

impl Hash for FunctionValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.equality_key().hash(state);
    }
}

pub fn error_unique_mismatch(kind: &str, target_span: Span, expected_span: Span, actual_span: Span) -> DiagnosticError {
    DiagnosticError::new(
        format!("{kind} expected type mismatch"),
        target_span,
        format!("this {kind} is different from the expected {kind}"),
    )
    .add_info(expected_span, format!("expected {kind} declared here"))
    .add_info(actual_span, format!("actual {kind} declared here"))
}

pub fn error_cannot_infer_generic_params(
    kind: &str,
    span_target: Span,
    span_call: Span,
    span_decl: Span,
    expected_ty: Option<String>,
) -> DiagnosticError {
    let expected_info = match expected_ty {
        None => "no expected type".to_owned(),
        Some(expected_ty) => format!("expected type `{expected_ty}` does not match this {kind}"),
    };
    DiagnosticError::new(
        format!("cannot infer {kind} parameters"),
        span_target,
        format!("this {kind} has unbound generic parameters"),
    )
    .add_info(span_call, expected_info)
    .add_info(span_decl, format!("{kind} declared with generic parameters here"))
    .add_footer_hint("either set an expected type or use the full type")
}
