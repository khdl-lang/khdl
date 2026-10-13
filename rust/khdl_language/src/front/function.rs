use crate::front::block::{BlockEnd, EarlyExitKind};
use crate::front::check::{TypeContainsReason, check_type_contains_value, check_type_is_bool_array};
use crate::front::compile::{CompileItemContext, CompileRefs, StackEntry};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError};
use crate::front::exit::{ExitFlag, ExitStack, ReturnEntry, ReturnEntryHardware, ReturnEntryKind};
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
    ReferenceWrapper, SimpleCompileValue, StructValue, Value, ValueCommon,
};
use crate::mid::bits::{FromBitsInvalidValue, FromBitsWrongLength, ToBitsWrongType};
use crate::mid::ir::{IrExpressionLarge, IrLargeArena};
use crate::syntax::ast::{
    Arg, Block, BlockStatement, Expression, ExtraList, FunctionDeclaration, MaybeIdentifier, Parameter,
    ParameterSelfKind, Parameters,
};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::ResultDoubleExt;
use crate::util::data::VecExt;
use crate::util::intern::Id;
use indexmap::IndexMap;
use indexmap::map::Entry;
use itertools::{Either, Itertools, enumerate};
use std::hash::Hash;
use std::sync::Arc;

/// How the selected method binds self inside its body.
enum MethodSelf {
    Value(Value),
    Reference(ReferenceWrapper),
}

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

#[must_use]
pub struct ParamArgMacher<'a> {
    // constant initial values
    refs: CompileRefs<'a, 'a>,
    args: &'a EvaluatedArgs,
    arg_name_to_index: IndexMap<Id, usize>,
    positional_count: usize,
    params_span: Span,

    // mutable state
    next_param_index: usize,
    arg_used: Vec<bool>,
    param_names: IndexMap<Id, Span>,

    any_err: DiagResult,
}

pub struct EvaluatedArgs {
    pub span: Span,
    pub inner: Vec<Arg<Option<Spanned<Id>>, Spanned<ValueWithImplications>>>,
}

#[derive(Debug, Copy, Clone)]
enum NamedRule {
    OnlyNamed,
    OnlyPositional,
    PositionalAndNamed,
}

// TODO make generic over the "value", this should be reused for instance connections in the future
impl<'a> ParamArgMacher<'a> {
    fn new(
        refs: CompileRefs<'a, 'a>,
        params_span: Span,
        args: &'a EvaluatedArgs,
        args_must_be_compile_without_ref: bool,
        args_must_be_named: NamedRule,
    ) -> DiagResult<Self> {
        let diags = refs.diags;

        // check for duplicate arg names and check that positional args are before named args
        let mut arg_name_to_index: IndexMap<Id, usize> = IndexMap::new();
        let mut first_named_span = None;
        let mut positional_count: usize = 0;
        let mut any_err_args = Ok(());
        for (arg_index, arg) in enumerate(&args.inner) {
            if args_must_be_compile_without_ref {
                match CompileValue::try_from(&arg.value.inner) {
                    Ok(arg_compile) => {
                        if arg_compile.definitely_contains_reference() {
                            let diag = DiagnosticError::new(
                                "item parameters cannot contain references",
                                arg.value.span,
                                "argument containing reference passed here",
                            ).add_footer_info("references must stay inside the module they belong to, they cannot escape into other items")
                                .report(diags);
                            any_err_args = Err(diag);
                        }
                    }
                    Err(NotCompile) => {
                        let diag = DiagnosticError::new(
                            "call target only supports compile-time parameters",
                            arg.value.span,
                            "argument containing hardware value passed here",
                        )
                        .add_info(params_span, "parameters defined here")
                        .report(diags);
                        any_err_args = Err(diag);
                    }
                }
            }

            match (&arg.name, args_must_be_named) {
                (None, NamedRule::OnlyNamed) => {
                    let diag = DiagnosticError::new(
                        "positional arguments are not allowed for this call target",
                        arg.span,
                        "positional argument passed here",
                    )
                    .add_info(params_span, "parameters defined here")
                    .report(diags);
                    any_err_args = Err(diag);
                }
                (Some(_), NamedRule::OnlyPositional) => {
                    let diag = DiagnosticError::new(
                        "named arguments are not allowed for this call target",
                        arg.span,
                        "named argument passed here",
                    )
                    .add_info(params_span, "parameters defined here")
                    .report(diags);
                    any_err_args = Err(diag);
                }

                (None, NamedRule::OnlyPositional) => {}
                (Some(_), NamedRule::OnlyNamed) => {}
                (_, NamedRule::PositionalAndNamed) => {}
            }

            match &arg.name {
                Some(id) => {
                    match arg_name_to_index.entry(id.inner) {
                        Entry::Occupied(entry) => {
                            let prev_index = *entry.get();
                            let diag = DiagnosticError::new("duplicate named parameter", id.span, "passed again here")
                                .add_info(args.inner[prev_index].span, "previously passed here")
                                .report(diags);
                            any_err_args = Err(diag);
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(arg_index);
                        }
                    }

                    if first_named_span.is_none() {
                        first_named_span = Some(id.span);
                    }
                }
                None => {
                    if let Some(first_named_span) = first_named_span {
                        let diag = DiagnosticError::new(
                            "positional arguments after named arguments are not allowed",
                            arg.span,
                            "later positional argument here".to_string(),
                        )
                        .add_info(first_named_span, "first named argument here")
                        .report(diags);
                        any_err_args = Err(diag);
                    }

                    positional_count += 1;
                }
            }
        }
        any_err_args?;

        Ok(Self {
            refs,
            args,
            positional_count,
            arg_name_to_index,
            params_span,
            next_param_index: 0,
            arg_used: vec![false; args.inner.len()],
            param_names: IndexMap::new(),
            any_err: Ok(()),
        })
    }

    pub fn resolve_param(
        &mut self,
        id: Spanned<Id>,
        ty: Spanned<&Type>,
        default: Option<Spanned<ValueWithImplications>>,
    ) -> DiagResult<Spanned<ValueWithImplications>> {
        let refs = self.refs;
        let diags = self.refs.diags;

        let param_index = self.next_param_index;
        self.next_param_index += 1;

        if let Some(prev_span) = self.param_names.insert(id.inner, id.span) {
            let e = DiagnosticError::new("duplicate parameter name", id.span, "defined again here")
                .add_info(prev_span, "previously defined here")
                .report(diags);
            self.any_err = Err(e);
            return Err(e);
        }

        let value = if param_index < self.positional_count {
            // positional match
            let arg_index = param_index;
            let arg = &self.args.inner[arg_index];
            assert!(arg.name.is_none());
            assert!(!self.arg_used[arg_index]);

            // check if there's also a named match to get better error messages
            if let Some(&other_arg_index) = self.arg_name_to_index.get(&id.inner) {
                let e = DiagnosticError::new(
                    "argument matches positionally but is also passed as named",
                    self.args.inner[other_arg_index].span,
                    "named match here",
                )
                .add_info(id.span, "parameter defined here")
                .add_info(arg.span, "positional match here")
                .report(diags);
                self.any_err = Err(e);
                self.arg_used[other_arg_index] = true;
            }

            self.arg_used[arg_index] = true;
            Ok(arg.value.clone())
        } else {
            match self.arg_name_to_index.get(&id.inner) {
                Some(&arg_index) => {
                    // named match
                    let arg = &self.args.inner[arg_index];
                    assert!(arg.name.is_some());
                    assert!(!self.arg_used[arg_index]);
                    self.arg_used[arg_index] = true;
                    Ok(arg.value.clone())
                }
                None => {
                    if let Some(default) = default {
                        // default value
                        Ok(default)
                    } else {
                        // nothing matched, report error
                        let id_str = id.inner.str(&self.refs.shared.interner);
                        let e = DiagnosticError::new(
                            format!("missing argument for parameter `{id_str}`"),
                            self.args.span,
                            "missing argument here",
                        )
                        .add_info(id.span, "parameter defined without default value here")
                        .report(diags);
                        self.any_err = Err(e);
                        Err(e)
                    }
                }
            }
        };

        // check type match
        let value = value.and_then(|value| {
            let reason = TypeContainsReason::Parameter { param_ty: ty.span };
            check_type_contains_value(refs, reason, ty.inner, value.as_ref())?;
            Ok(value)
        });

        if let Err(e) = value {
            self.any_err = Err(e);
        }

        value
    }

    pub fn finish(self) -> DiagResult {
        let diags = self.refs.diags;
        self.any_err?;

        let mut any_err_used = Ok(());
        for (i, arg_used) in enumerate(self.arg_used) {
            if !arg_used {
                let e = DiagnosticError::new(
                    "argument does not match any parameter",
                    self.args.inner[i].span,
                    "argument passed here",
                )
                .add_info(self.params_span, "parameters defined here")
                .report(diags);
                any_err_used = Err(e);
            }
        }

        any_err_used?;
        Ok(())
    }
}

impl CompileItemContext<'_, '_> {
    pub fn call_function(
        &mut self,
        flow: &mut impl Flow,
        expected_ty: &Type,
        span_target: Span,
        span_call: Span,
        function: &FunctionValue,
        args: EvaluatedArgs,
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
            FunctionValue::Bits(function) => self.call_bits_function(span_call, span_target, function, args),
            &FunctionValue::StructNew(struct_elab) => self.call_struct_new(span_call, struct_elab, args),
            &FunctionValue::StructNewInfer(func_unique) => match *expected_ty {
                Type::Struct(expected_elab) => {
                    let expected_info = self.refs.shared.elaboration_arenas.struct_info(expected_elab);
                    if expected_info.unique == func_unique {
                        self.call_struct_new(span_call, expected_elab, args)
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
                self.call_enum_new(span_call, enum_elab, variant_index, &args)
            }
            &FunctionValue::EnumNewInfer(func_unique, variant_id) => match expected_ty {
                &Type::Enum(expected_elab) => {
                    let expected_info = self.refs.shared.elaboration_arenas.enum_info(expected_elab);

                    if expected_info.unique == func_unique {
                        let variant_index = expected_info.variant_index(refs, Spanned::new(span_target, variant_id))?;
                        self.call_enum_new(span_call, expected_elab, variant_index, &args)
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
        args: EvaluatedArgs,
    ) -> DiagResult<Value> {
        // TODO propagate self type too
        let BoundMethod {
            self_type,
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

        let self_value = match self_param.inner {
            ParameterSelfKind::Slf => MethodSelf::Value(self_value.as_ref().clone()),
            ParameterSelfKind::RefSlf => {
                let Value::Simple(SimpleCompileValue::Reference(rf)) = self_value.as_ref() else {
                    return Err(self
                        .refs
                        .diags
                        .report_error_internal(span_call, "reference receiver binding is not a reference"));
                };
                self.check_reference_receiver(flow, span_call, rf, self_type)?;
                MethodSelf::Reference(rf.clone())
            }
        };
        let self_value = Spanned::new(self_param.span, self_value);
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

    // TODO ensure the expected type for fields is correctly propagated to the args
    //   (this might need a major re-think, currently args are always evaluated in advance)
    fn call_struct_new(&mut self, span_call: Span, elab: ElaboratedStruct, args: EvaluatedArgs) -> DiagResult<Value> {
        let _ = span_call;
        let &ElaboratedStructInfo {
            unique: _,
            debug_info_name: _,
            span_body,
            ref fields,
            hw: _,
            members_static: _,
            methods_self: _,
        } = self.refs.shared.elaboration_arenas.struct_info(elab);

        let mut matcher = ParamArgMacher::new(self.refs, span_body, &args, false, NamedRule::OnlyNamed)?;

        let mut field_values = vec![];
        for field in fields.values() {
            if let Ok(v) = matcher.resolve_param(field.id, field.ty.as_ref(), None) {
                field_values.push(v.inner.into_value());
            }
        }
        matcher.finish()?;

        let result = StructValue {
            ty: elab,
            fields: field_values,
        };
        Ok(Value::Compound(MixedCompoundValue::Struct(result)))
    }

    fn call_enum_new(
        &mut self,
        span_call: Span,
        elab: ElaboratedEnum,
        variant_index: usize,
        args: &EvaluatedArgs,
    ) -> DiagResult<Value> {
        let enum_info = self.refs.shared.elaboration_arenas.enum_info(elab);
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
            .report(self.refs.diags)
        })?;

        let mut matcher = ParamArgMacher::new(self.refs, span_call, args, false, NamedRule::OnlyPositional)?;
        let payload = matcher
            .resolve_param(
                Spanned::new(variant_id.span(), variant_id.inner),
                payload_ty.as_ref(),
                None,
            )?
            .inner
            .into_value();
        matcher.finish()?;

        let result = EnumValue {
            ty: elab,
            variant: variant_index,
            payload: Some(Box::new(payload)),
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
        arg_self: Option<Spanned<MethodSelf>>,
        args: EvaluatedArgs,
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
        arg_self: Option<Spanned<MethodSelf>>,
        args: EvaluatedArgs,
    ) -> DiagResult<Value> {
        self.refs.check_should_stop(span_decl)?;

        // recreate captured scope
        let span_scope = params.span.join(body.span);
        let scope_captured = Arc::clone(scope_captured).as_scope();

        // map params into scope
        let mut scope = scope_captured.new_child(span_scope);
        let mut param_values = vec![];

        if let Some(arg_self) = arg_self {
            scope.declare(
                self.refs,
                ScopeKey::Slf(arg_self.span),
                Ok(match arg_self.inner {
                    MethodSelf::Value(value) => ScopedEntry::Value(value),
                    MethodSelf::Reference(rf) => ScopedEntry::Alias(rf),
                }),
            );
        }

        let args_must_be_compile_without_ref = match body.inner {
            FunctionBody::ItemBody(_) => true,
            FunctionBody::FunctionBodyBlockOwned { .. } | FunctionBody::FunctionBodyBlockRef { .. } => false,
        };
        let mut matcher = ParamArgMacher::new(
            self.refs,
            params.span,
            &args,
            args_must_be_compile_without_ref,
            NamedRule::PositionalAndNamed,
        )?;

        self.elaborate_extra_list(&mut scope, flow, params, true, &mut |slf, scope, flow, param| {
            let &Parameter {
                span: _,
                id,
                ty,
                default,
            } = param;

            let id_eval = slf.eval_id(scope.as_scope(), flow, id)?;

            let ty = slf.eval_expression_as_ty(scope.as_scope(), flow, ty)?;
            let default = default
                .as_ref()
                .map(|&default| {
                    let value = slf.eval_expression_as_compile(
                        scope.as_scope(),
                        flow,
                        &ty.inner,
                        default,
                        Spanned::new(param.span, "parameter default value"),
                    )?;
                    Ok(value.map_inner(Value::from))
                })
                .transpose()?;

            let value = matcher.resolve_param(id_eval, ty.as_ref(), default);

            // record value into vec
            if let Ok(value) = &value {
                param_values.push((id_eval, value.inner.clone()));
            }

            // declare param in scope
            let param_var = flow.var_new_immutable_init(
                slf.refs,
                MaybeIdentifier::Identifier(id_eval),
                param.id.span(),
                value.map(|v| v.inner),
            )?;
            let entry = ScopedEntry::Named(NamedValue::Variable(param_var));

            scope.declare_root(slf.refs, MaybeIdentifier::Identifier(id_eval), Ok(entry));

            Ok(())
        })?;
        matcher.finish()?;

        // run the body
        let entry = StackEntry::FunctionRun(span_decl);
        self.recurse(entry, |slf| {
            match &body.inner {
                FunctionBody::ItemBody(item_body) => {
                    // unwrap compile, we checked that these values are compile-time during argument matching
                    let param_values = param_values
                        .into_iter()
                        .map(|(id, v)| (id, CompileValue::try_from(&v).unwrap()))
                        .collect_vec();

                    let mut flow_inner = flow.new_child_compile(body.span, "item body");
                    let value = slf.eval_item_function_body(
                        &scope,
                        &mut flow_inner,
                        Some(param_values),
                        Spanned::new(body.span, item_body),
                    )?;
                    Ok(Value::from(value))
                }
                &FunctionBody::FunctionBodyBlockOwned { ref body, ret_ty } => {
                    slf.run_function_body_block(flow, &scope, span_decl, ret_ty, body)
                }
                &FunctionBody::FunctionBodyBlockRef { body, ret_ty } => {
                    slf.run_function_body_block(flow, &scope, span_decl, ret_ty, body)
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
        span_call: Span,
        span_target: Span,
        function: &FunctionBits,
        args: EvaluatedArgs,
    ) -> DiagResult<Value> {
        let refs = self.refs;
        let diags = self.refs.diags;

        // check arg is single non-named value
        // TODO use new common arg-matching machinery
        let value = match args.inner.single() {
            Ok(Arg { span: _, name, value }) => {
                if let Some(name) = name {
                    return Err(diags.report_error_simple(
                        "this function expects a single unnamed parameter",
                        name.span,
                        "got named argument here",
                    ));
                }
                value
            }
            Err(_) => {
                return Err(diags.report_error_simple(
                    "this function expects a single parameter",
                    args.span,
                    "incorrect arguments here",
                ));
            }
        };
        let span_value = value.span;

        // actual implementation
        let FunctionBits { ty_hw, kind } = function;
        match kind {
            FunctionBitsKind::ToBits => {
                check_type_contains_value(
                    refs,
                    TypeContainsReason::Operator(span_call),
                    &ty_hw.as_type(),
                    value.as_ref(),
                )?;

                // try as compile-time first so we get compile-time bits back
                match CompileValue::try_from(&value.inner) {
                    Ok(value) => {
                        let bits = ty_hw.value_to_bits(self.refs, &value).map_err(|_: ToBitsWrongType| {
                            diags.report_error_internal(span_call, "value_to_bits wrong type")
                        })?;
                        let bits_wrapped = bits.into_iter().map(CompileValue::new_bool).collect_vec();
                        Ok(Value::Simple(SimpleCompileValue::Array(Arc::new(bits_wrapped))))
                    }
                    Err(NotCompile) => {
                        let value = value.inner.as_hardware_value_unchecked(
                            self.refs,
                            &mut self.large,
                            span_call,
                            ty_hw.clone(),
                        )?;

                        let ty_ir = ty_hw.as_ir(self.refs);
                        let ty_bits = HardwareType::Array(Arc::new(HardwareType::Bool), ty_ir.size_bits());
                        let value_bits = HardwareValue {
                            ty: ty_bits,
                            domain: value.domain,
                            expr: self.large.push_expr(IrExpressionLarge::ToBits(ty_ir, value.expr)),
                        };
                        Ok(Value::Hardware(value_bits))
                    }
                }
            }
            &FunctionBitsKind::FromBits { is_unsafe } => {
                let ty_ir = ty_hw.as_ir(self.refs);
                let width = ty_ir.size_bits();

                let value = check_type_is_bool_array(
                    refs,
                    TypeContainsReason::Operator(span_call),
                    value.map_inner(|v| v.into_value()),
                    Some(width),
                )?;

                let result = match value {
                    MaybeCompile::Compile(v) => {
                        let result = ty_hw.value_from_bits(self.refs, &v).map_err(|e| match e {
                            Either::Left(FromBitsInvalidValue) => {
                                if is_unsafe {
                                    DiagnosticError::new(
                                        "invalid bit pattern for type",
                                        span_value,
                                        format!("got bits `{:?}`", v),
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
                        let expr = self.large.push_expr(IrExpressionLarge::FromBits(ty_ir, v.expr.clone()));
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
