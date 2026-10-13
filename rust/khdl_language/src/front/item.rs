use crate::front::check::{TypeContainsReason, check_type_contains_value};
use crate::front::compile::{CompileItemContext, CompileRefs, WorkItem};
use crate::front::diagnostic::{DiagResult, DiagnosticError};
use crate::front::extra::ExtraScope;
use crate::front::flow::{Flow, FlowCompile, FlowRoot};
use crate::front::function::{FunctionBody, FunctionValue, UserFunctionValue};
use crate::front::interface::ElaboratedInterfaceInfo;
use crate::front::module_header::{ElaboratedModuleExternalInfo, ElaboratedModuleInternalInfo};
use crate::front::scope::{CaptureFailed, DeclaredValueSingle, NamedValue, Scope, ScopeKey, ScopedEntry};
use crate::front::steps::POSSIBLE_BUILTIN_TYPE_MEMBERS;
use crate::front::types::{HardwareType, Type};
use crate::front::value::{CompileValue, MethodInfo, SimpleCompileValue, Value};
use crate::mid::ir::{IrEnumType, IrStructType, IrType};
use crate::syntax::ast::{
    CommonDeclaration, CommonDeclarationNamed, CommonDeclarationNamedKind, ConstDeclaration, EnumBodyItem,
    EnumDeclaration, EnumVariant, Expression, ExtraList, FunctionDeclaration, Item, ItemDefInterface,
    ItemDefModuleExternal, ItemDefModuleInternal, MaybeIdentifier, ParameterSelfKind, Parameters, StructBodyItem,
    StructDeclaration, StructField, TypeDeclaration,
};
use crate::syntax::parsed::{AstRefInterface, AstRefItem, AstRefModuleExternal, AstRefModuleInternal};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::ResultExt;
use crate::util::big_int::BigInt;
use crate::util::intern::Id;
use crate::util::iter::IterExt;
use crate::util::range::ClosedNonEmptyRange;
use crate::util::sync::ComputeOnceMap;
use indexmap::IndexMap;
use itertools::zip_eq;
use khdl_util::swrite;
use std::hash::Hash;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ElaboratedModule<I = ElaboratedModuleInternal, E = ElaboratedModuleExternal> {
    Internal(I),
    External(E),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedModuleInternal(usize);
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedModuleExternal(usize);
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedInterface(usize);
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedStruct(usize);
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedEnum(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedInterfaceView {
    pub interface: ElaboratedInterface,
    pub view_index: usize,
}

pub struct ElaborationArenas {
    elaborated_modules_internal: ElaborateItemArena<ElaboratedModuleInternal, ElaboratedModuleInternalInfo>,
    elaborated_modules_external: ElaborateItemArena<ElaboratedModuleExternal, ElaboratedModuleExternalInfo>,
    elaborated_interfaces: ElaborateItemArena<ElaboratedInterface, ElaboratedInterfaceInfo>,
    elaborated_structs: ElaborateItemArena<ElaboratedStruct, ElaboratedStructInfo>,
    elaborated_enums: ElaborateItemArena<ElaboratedEnum, ElaboratedEnumInfo>,
    next_unique_declaration: AtomicUsize,
}

// TODO rework this, this should really _only_ store a unique index, no other metadata
#[derive(Debug, Copy, Clone)]
pub struct UniqueDeclaration {
    index: usize,
    id: MaybeIdentifier<Spanned<Id>>,
}

impl UniqueDeclaration {
    pub fn id(&self) -> MaybeIdentifier<Spanned<Id>> {
        self.id
    }
}

impl Eq for UniqueDeclaration {}
impl PartialEq for UniqueDeclaration {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}
impl Hash for UniqueDeclaration {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl ElaborationArenas {
    pub fn new() -> Self {
        ElaborationArenas {
            elaborated_modules_internal: ElaborateItemArena::new(),
            elaborated_modules_external: ElaborateItemArena::new(),
            elaborated_interfaces: ElaborateItemArena::new(),
            elaborated_structs: ElaborateItemArena::new(),
            elaborated_enums: ElaborateItemArena::new(),
            next_unique_declaration: AtomicUsize::new(0),
        }
    }

    pub fn module_internal_info(&self, elab: ElaboratedModuleInternal) -> &ElaboratedModuleInternalInfo {
        self.elaborated_modules_internal.get(elab)
    }

    pub fn module_external_info(&self, elab: ElaboratedModuleExternal) -> &ElaboratedModuleExternalInfo {
        self.elaborated_modules_external.get(elab)
    }

    pub fn interface_info(&self, elab: ElaboratedInterface) -> &ElaboratedInterfaceInfo {
        self.elaborated_interfaces.get(elab)
    }

    pub fn struct_info(&self, elab: ElaboratedStruct) -> &ElaboratedStructInfo {
        self.elaborated_structs.get(elab)
    }

    pub fn enum_info(&self, elab: ElaboratedEnum) -> &ElaboratedEnumInfo {
        self.elaborated_enums.get(elab)
    }

    fn next_unique_declaration(&self, id: MaybeIdentifier<Spanned<Id>>) -> UniqueDeclaration {
        let index = self.next_unique_declaration.fetch_add(1, Ordering::Relaxed);
        assert!(index < usize::MAX / 2, "(close to) overflowing");
        UniqueDeclaration { index, id }
    }
}

pub struct ElaborateItemArena<E, F> {
    next_id: AtomicUsize,
    key_to_id: ComputeOnceMap<ElaboratedItemKey, E>,
    id_to_info: ComputeOnceMap<E, DiagResult<F>>,
}

impl<E: Copy + Eq + Hash, F> ElaborateItemArena<E, F> {
    pub fn new() -> Self {
        ElaborateItemArena {
            next_id: AtomicUsize::new(0),
            key_to_id: ComputeOnceMap::new(),
            id_to_info: ComputeOnceMap::new(),
        }
    }

    pub fn get(&self, id: E) -> &F {
        // The key only gets out if the computation was successful,
        //   so we can safely unwrap here (twice).
        self.id_to_info.get(&id).unwrap().as_ref_ok().unwrap()
    }

    /// Elaborate a given item if necessary, or return the existing result if it exists.
    ///
    /// The function `f` gets the resulting id already, but it not not yet valid,
    /// so it should only be used as an equality key, not for looking up elaborated results.
    pub fn elaborate(
        &self,
        params: ElaboratedItemParams,
        e: impl FnOnce(usize) -> E,
        f: impl FnOnce(E, ElaboratedItemParams) -> DiagResult<F>,
    ) -> DiagResult<(E, &F)> {
        let key = params.cache_key();

        let &id = self.key_to_id.get_or_compute(key, |_| {
            let index = self.next_id.fetch_add(1, Ordering::Relaxed);
            let id = e(index);

            let info = f(id, params);

            self.id_to_info.set(id, info).unwrap();
            id
        });

        let info = self.id_to_info.get(&id).unwrap().as_ref_ok()?;
        Ok((id, info))
    }
}

pub struct ElaboratedItemParams {
    // TODO maybe remove this field?
    pub unique: UniqueDeclaration,
    pub params: Option<Vec<(Spanned<Id>, CompileValue)>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ElaboratedItemKey {
    unique: UniqueDeclaration,
    params: Option<Vec<CompileValue>>,
}

impl ElaboratedItemParams {
    pub fn cache_key(&self) -> ElaboratedItemKey {
        let unique = self.unique;
        let param_values = self
            .params
            .as_ref()
            .map(|params| params.iter().map(|(_, v)| v.clone()).collect());
        ElaboratedItemKey {
            unique,
            params: param_values,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FunctionItemBody {
    // TODO change this to be a type alias, or maybe change the others to be ast references too?
    TypeAliasExpr(Expression),
    ModuleInternal(UniqueDeclaration, AstRefModuleInternal),
    ModuleExternal(UniqueDeclaration, AstRefModuleExternal),
    Interface(UniqueDeclaration, AstRefInterface),
    Struct(UniqueDeclaration, Arc<GenericStructInfo>),
    Enum(UniqueDeclaration, Arc<GenericEnumInfo>),
}

/// Newtype wrapper that promises that the fields are representable in hardware.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct HardwareChecked<T> {
    inner: T,
}

impl<T: Copy> HardwareChecked<T> {
    pub fn new_unchecked(inner: T) -> Self {
        HardwareChecked { inner }
    }

    pub fn inner(self) -> T {
        self.inner
    }
}

#[derive(Debug)]
pub struct GenericStructInfo {
    // TODO replace with AstRef
    items: ExtraList<StructBodyItem>,
}

#[derive(Debug)]
pub struct ElaboratedStructInfo {
    pub unique: UniqueDeclaration,
    pub debug_info_name: String,
    pub span_body: Span,

    pub fields: IndexMap<Id, ElaboratedStructField>,
    pub hw: Result<HardwareStructInfo, NonHardwareStruct>,

    pub members_static: IndexMap<Id, DiagResult<CompileValue>>,
    pub methods_self: IndexMap<Id, Arc<MethodInfo>>,
}

#[derive(Debug)]
pub struct ElaboratedStructField {
    pub id: Spanned<Id>,
    /// The constructor/storage type, including the reference wrapper.
    pub ty: Spanned<Type>,
    /// Reference fields project to their target; ordinary reference-valued fields do not.
    pub ref_: Option<Span>,
}

#[derive(Debug)]
pub struct HardwareStructInfo {
    pub ty_ir: IrStructType,
    pub fields: Vec<HardwareType>,
}

#[derive(Debug, Copy, Clone)]
pub struct NonHardwareStruct {
    pub first_non_hardware_field: usize,
}

/// Information that can be collected about an enum declaration before filling in generic parameters.
#[derive(Debug)]
pub struct GenericEnumInfo {
    pub span_body: Span,
    // TODO replace with AstRef
    pub items: ExtraList<EnumBodyItem>,
    pub generic_variants: IndexMap<Id, GenericVariantInfo>,
}

#[derive(Debug, Copy, Clone)]
pub struct GenericVariantInfo {
    pub span_first_decl: Span,
    pub has_payload: bool,
}

#[derive(Debug)]
pub struct ElaboratedEnumInfo {
    pub unique: UniqueDeclaration,
    pub debug_info_name: String,
    pub span_body: Span,
    pub variants: IndexMap<Id, ElaboratedEnumVariantInfo>,
    pub hw: Result<HardwareEnumInfo, NonHardwareEnum>,

    pub members_static: IndexMap<Id, DiagResult<CompileValue>>,
    pub methods_self: IndexMap<Id, Arc<MethodInfo>>,
}

#[derive(Debug)]
pub struct ElaboratedEnumVariantInfo {
    pub id: Spanned<Id>,
    pub payload_ty: Option<Spanned<Type>>,
}

#[derive(Debug, Clone)]
pub enum NonHardwareEnum {
    NoVariants,
    FirstNonHardwareVariant(usize),
}

#[derive(Debug)]
pub struct HardwareEnumInfo {
    pub ty_ir: IrEnumType,
    pub tag_range: ClosedNonEmptyRange<BigInt>,
    pub payload_types: Vec<Option<(HardwareType, IrType)>>,
}

impl GenericEnumInfo {
    pub fn find_variant(&self, refs: CompileRefs, variant: Spanned<Id>) -> DiagResult<&GenericVariantInfo> {
        self.generic_variants.get(&variant.inner).ok_or_else(|| {
            let variant_str = variant.inner.str(&refs.shared.interner);
            DiagnosticError::new(
                format!("enum variant `{variant_str}` not found"),
                variant.span,
                "attempt to access variant here",
            )
            .add_info(self.span_body, "enum variants declared here")
            .report(refs.diags)
        })
    }
}

impl ElaboratedStructInfo {
    pub fn field_index(&self, refs: CompileRefs, base_span: Span, field: Spanned<Id>) -> DiagResult<usize> {
        self.fields.get_index_of(&field.inner).ok_or_else(|| {
            let field_str = field.inner.str(&refs.shared.interner);
            DiagnosticError::new(
                format!("struct member `{field_str}` not found"),
                field.span,
                "attempt to access non-existing member here",
            )
            .add_info(base_span, format!("base has type `{}`", self.value_string()))
            .add_info(self.span_body, "struct body declared here")
            .report(refs.diags)
        })
    }
}

impl ElaboratedEnumInfo {
    pub fn variant_index(&self, refs: CompileRefs, variant: Spanned<Id>) -> DiagResult<usize> {
        self.variants.get_index_of(&variant.inner).ok_or_else(|| {
            let variant_str = variant.inner.str(&refs.shared.interner);
            DiagnosticError::new(
                format!("enum variant `{variant_str}` not found"),
                variant.span,
                "attempt to access variant here",
            )
            .add_info(self.span_body, "enum variants declared here")
            .report(refs.diags)
        })
    }
}

pub struct EvaluatedDeclaration {
    pub span: Span,
    pub id: MaybeIdentifier<Spanned<Id>>,
    pub value: CompileValue,
}

impl EvaluatedDeclaration {
    pub fn value_into_entry(self, refs: CompileRefs, flow: &mut impl Flow) -> DiagResult<ScopedEntry> {
        let var = flow.var_new_immutable_init(refs, self.id, self.span, Ok(Value::from(self.value)))?;
        Ok(ScopedEntry::Named(NamedValue::Variable(var)))
    }
}

impl CompileItemContext<'_, '_> {
    pub fn eval_item_new(&mut self, item: AstRefItem) -> DiagResult<CompileValue> {
        let diags = self.refs.diags;

        let item_ast = &self.refs.fixed.parsed[item];
        self.refs.check_should_stop(item_ast.info().span_short)?;

        let file_scope = self.refs.shared.file_scope(item.file())?;
        let file_scope = Arc::clone(&file_scope.scope).as_scope();

        match item_ast {
            Item::Import(item_inner) => {
                let reason = "import items should have been resolved in a separate pass already";
                Err(diags.report_error_internal(item_inner.span, reason))
            }
            Item::CommonDeclaration(decl) => {
                let flow_root = FlowRoot::new(diags, &self.refs.shared.next_flow_root_id);
                let mut flow = FlowCompile::new_root(&flow_root, decl.span, "item declaration");

                let eval = self.eval_declaration(&file_scope, &mut flow, &decl.inner)?;

                let value = match eval {
                    None => CompileValue::unit(),
                    Some(value) => value.value,
                };
                Ok(value)
            }
            Item::ModuleInternal(module) => {
                let &ItemDefModuleInternal {
                    span: _,
                    vis: _,
                    id,
                    ref params,
                    ref ports,
                    ref body,
                } = module;
                let item = AstRefModuleInternal::new_unchecked(item, module);
                let body_span = ports.span.join(body.span);

                let flow_root = FlowRoot::new(diags, &self.refs.shared.next_flow_root_id);
                let mut flow = FlowCompile::new_root(&flow_root, module.span, "item declaration");
                let id_eval = self.eval_maybe_id(&file_scope, &mut flow, id)?;

                let unique = self.refs.shared.elaboration_arenas.next_unique_declaration(id_eval);
                let body = FunctionItemBody::ModuleInternal(unique, item);

                self.eval_maybe_generic_item(id.span(), body_span, &file_scope, &mut flow, params, body)
            }
            Item::ModuleExternal(module) => {
                let &ItemDefModuleExternal {
                    span: _,
                    span_ext: _,
                    vis: _,
                    id,
                    ref params,
                    ref ports,
                } = module;
                let item = AstRefModuleExternal::new_unchecked(item, module);
                let body_span = ports.span;

                let id = self.eval_simple_id(id);
                let unique = self
                    .refs
                    .shared
                    .elaboration_arenas
                    .next_unique_declaration(MaybeIdentifier::Identifier(id));
                let body = FunctionItemBody::ModuleExternal(unique, item);

                let flow_root = FlowRoot::new(diags, &self.refs.shared.next_flow_root_id);
                let mut flow = FlowCompile::new_root(&flow_root, module.span, "item declaration");
                self.eval_maybe_generic_item(id.span, body_span, &file_scope, &mut flow, params, body)
            }

            Item::Interface(interface) => {
                let &ItemDefInterface {
                    span: _,
                    vis: _,
                    id,
                    ref params,
                    ref span_body,
                    body: _,
                } = interface;
                let item = AstRefInterface::new_unchecked(item, interface);

                let flow_root = FlowRoot::new(diags, &self.refs.shared.next_flow_root_id);
                let mut flow = FlowCompile::new_root(&flow_root, interface.span, "item declaration");
                let id_eval = self.eval_maybe_id(&file_scope, &mut flow, id)?;

                let unique = self.refs.shared.elaboration_arenas.next_unique_declaration(id_eval);
                let body = FunctionItemBody::Interface(unique, item);

                self.eval_maybe_generic_item(id.span(), *span_body, &file_scope, &mut flow, params, body)
            }
        }
    }

    pub fn eval_declaration<V>(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        decl: &CommonDeclaration<V>,
    ) -> DiagResult<Option<EvaluatedDeclaration>> {
        match decl {
            CommonDeclaration::Named(decl) => {
                let CommonDeclarationNamed { vis: _, kind } = decl;
                self.eval_declaration_named(scope, flow, kind).map(Some)
            }
            CommonDeclaration::ConstBlock(decl) => {
                self.elaborate_const_block(scope, flow, decl)?;
                Ok(None)
            }
        }
    }

    pub fn eval_declaration_named(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        decl: &CommonDeclarationNamedKind,
    ) -> DiagResult<EvaluatedDeclaration> {
        let refs = self.refs;
        let diags = self.refs.diags;

        match decl {
            CommonDeclarationNamedKind::Type(decl) => {
                let &TypeDeclaration {
                    span,
                    id,
                    ref params,
                    body,
                } = decl;
                let body_span = body.span;
                let id_eval = self.eval_maybe_id(scope, flow, id)?;

                let body = FunctionItemBody::TypeAliasExpr(body);
                let value = self.eval_maybe_generic_item(id.span(), body_span, scope, flow, params, body)?;
                Ok(EvaluatedDeclaration {
                    span,
                    id: id_eval,
                    value,
                })
            }
            CommonDeclarationNamedKind::Const(decl) => {
                let &ConstDeclaration { span, id, ty, value } = decl;
                let id_eval = self.eval_maybe_id(scope, flow, id)?;

                let ty = ty.map(|ty| self.eval_expression_as_ty(scope, flow, ty)).transpose()?;

                let expected_ty = ty.as_ref().map_or(&Type::Any, |ty| &ty.inner);
                let value = self.eval_expression_as_compile(
                    scope,
                    flow,
                    expected_ty,
                    value,
                    Spanned::new(span, "const declaration"),
                )?;

                // check type
                if let Some(ty) = ty {
                    let reason = TypeContainsReason::Assignment {
                        span_target: id.span(),
                        span_target_ty: ty.span,
                    };
                    check_type_contains_value(refs, reason, &ty.inner, value.as_ref())?;
                };

                Ok(EvaluatedDeclaration {
                    span,
                    id: id_eval,
                    value: value.inner,
                })
            }
            CommonDeclarationNamedKind::Struct(decl) => {
                let &StructDeclaration {
                    span,
                    span_body,
                    id,
                    ref params,
                    ref items,
                } = decl;

                let id_eval = self.eval_maybe_id(scope, flow, id)?;
                let unique = self.refs.shared.elaboration_arenas.next_unique_declaration(id_eval);
                let generic_info = GenericStructInfo { items: items.clone() };
                let body = FunctionItemBody::Struct(unique, Arc::new(generic_info));

                let value = self.eval_maybe_generic_item(id.span(), span_body, scope, flow, params, body)?;
                Ok(EvaluatedDeclaration {
                    span,
                    id: id_eval,
                    value,
                })
            }
            CommonDeclarationNamedKind::Enum(decl) => {
                let &EnumDeclaration {
                    span,
                    id,
                    ref params,
                    ref items,
                } = decl;

                // check variant payload consistency
                // this is necessary to avoid confusing type inference situations later
                let decl_id_eval = self.eval_maybe_id(scope, flow, id)?;
                let mut generic_variants: IndexMap<Id, GenericVariantInfo> = IndexMap::new();
                let mut any_err = Ok(());
                items.for_each_leaf(&mut |item| {
                    let variant = match item {
                        EnumBodyItem::Variant(variant) => variant,
                        EnumBodyItem::Method(_) => return,
                    };

                    let &EnumVariant {
                        span: variant_span,
                        id,
                        payload,
                    } = variant;
                    let id_eval = refs.shared.interner.push(id.str(refs.fixed.source));

                    match generic_variants.get(&id_eval) {
                        None => {
                            generic_variants.insert(
                                id_eval,
                                GenericVariantInfo {
                                    span_first_decl: variant_span,
                                    has_payload: payload.is_some(),
                                },
                            );
                        }
                        Some(&GenericVariantInfo {
                            span_first_decl,
                            has_payload,
                        }) => {
                            let kind_str = |has_payload: bool| if has_payload { "with" } else { "without" };
                            if has_payload != payload.is_some() {
                                let diag = DiagnosticError::new(
                                    "enum variant payload must be consistent between generic instantiations",
                                    variant_span,
                                    format!("redeclared here {} payload", kind_str(payload.is_some())),
                                )
                                .add_info(
                                    span_first_decl,
                                    format!("previously declared here {} payload", kind_str(has_payload)),
                                )
                                .add_footer_info("this would make type inference for enum variants too difficult")
                                .report(diags);
                                any_err = Err(diag);
                            }
                        }
                    }
                });
                any_err?;

                let unique = self
                    .refs
                    .shared
                    .elaboration_arenas
                    .next_unique_declaration(decl_id_eval);
                let generic_info = GenericEnumInfo {
                    span_body: items.span,
                    items: items.clone(),
                    generic_variants,
                };
                let body = FunctionItemBody::Enum(unique, Arc::new(generic_info));

                let value = self.eval_maybe_generic_item(id.span(), span, scope, flow, params, body)?;
                Ok(EvaluatedDeclaration {
                    span,
                    id: decl_id_eval,
                    value,
                })
            }
            CommonDeclarationNamedKind::Function(decl) => {
                let &FunctionDeclaration {
                    span,
                    id,
                    ref params,
                    ret_ty,
                    ref body,
                } = decl;
                let Parameters {
                    span: _,
                    slf: (),
                    items: param_items,
                } = params;

                let id_eval = self.eval_maybe_id(scope, flow, id)?;

                let body_inner = FunctionBody::FunctionBodyBlockOwned {
                    body: Arc::new(body.clone()),
                    ret_ty,
                };
                let function = UserFunctionValue {
                    span_decl: id.span(),
                    scope_captured: Arc::new(scope.capture(flow, id.span())),
                    params: Arc::new(param_items.clone()),
                    body: Spanned {
                        span: body.span,
                        inner: body_inner,
                    },
                };
                let value = CompileValue::Simple(SimpleCompileValue::Function(FunctionValue::User(Arc::new(function))));
                Ok(EvaluatedDeclaration {
                    span,
                    id: id_eval,
                    value,
                })
            }
        }
    }

    pub fn eval_and_declare_declaration(
        &mut self,
        scope: &mut Scope,
        flow: &mut impl Flow,
        decl: &CommonDeclaration<()>,
    ) -> DiagResult {
        let eval = self.eval_declaration(scope, flow, decl)?;

        if let Some(eval) = eval {
            let id = eval.id;
            let entry = eval.value_into_entry(self.refs, flow)?;
            scope.declare(self.refs, id, Ok(entry));
        }

        Ok(())
    }

    fn eval_maybe_generic_item(
        &mut self,
        span_decl: Span,
        span_body: Span,
        scope: &Scope,
        flow: &mut impl Flow,
        params: &Option<Parameters>,
        body: FunctionItemBody,
    ) -> DiagResult<CompileValue> {
        match params {
            None => {
                // eval immediately
                let body = Spanned::new(span_body, &body);
                let mut flow = flow.new_child_compile(span_decl, "item body");
                self.eval_item_function_body(scope, &mut flow, None, body)
            }
            Some(params) => {
                // build function
                let Parameters {
                    span: _,
                    slf: (),
                    items: param_items,
                } = params;
                let func = UserFunctionValue {
                    span_decl,
                    scope_captured: Arc::new(scope.capture(flow, span_decl)),
                    params: Arc::new(param_items.clone()),
                    body: Spanned {
                        span: span_body,
                        inner: FunctionBody::ItemBody(body),
                    },
                };
                Ok(CompileValue::Simple(SimpleCompileValue::Function(FunctionValue::User(
                    Arc::new(func),
                ))))
            }
        }
    }

    pub fn eval_item_function_body(
        &mut self,
        scope_params: &Scope,
        flow: &mut FlowCompile,
        params: Option<Vec<(Spanned<Id>, CompileValue)>>,
        body: Spanned<&FunctionItemBody>,
    ) -> DiagResult<CompileValue> {
        let diags = self.refs.diags;
        let source = self.refs.fixed.source;

        match *body.inner {
            FunctionItemBody::TypeAliasExpr(expr) => {
                let result_ty = self.eval_expression_as_ty(scope_params, flow, expr)?.inner;
                Ok(CompileValue::new_ty(result_ty))
            }
            FunctionItemBody::ModuleInternal(ref unique, ast_ref) => {
                let unique = *unique;
                let item_params = ElaboratedItemParams { unique, params };
                let refs = self.refs;

                // TODO make module elaboration more similar to other items,
                //   where the flow is not created by the inner elaboration function but top-level.
                //   This is trickier than usual (since we delay module body elaboration) but might still be possible.
                let (result_id, _) = refs.shared.elaboration_arenas.elaborated_modules_internal.elaborate(
                    item_params,
                    ElaboratedModuleInternal,
                    |result_id, item_params| {
                        // capture scope to ensure full separation
                        let scope_params = scope_params.capture(flow, body.span);

                        // elaborate ports
                        let ast = &refs.fixed.parsed[ast_ref];
                        let (connectors, header) = refs.elaborate_module_ports_new(
                            ast_ref,
                            ast.span,
                            ElaboratedModule::Internal(result_id),
                            item_params,
                            Arc::new(scope_params),
                            &ast.ports,
                        )?;

                        // reserve ir module key, will be filled in later during body elaboration
                        let ir_module = { refs.shared.ir_database.lock().unwrap().modules.push(None) };

                        // queue body elaboration for later
                        refs.shared
                            .work_queue
                            .push(WorkItem::ElaborateModuleBody(header, ir_module));

                        Ok(ElaboratedModuleInternalInfo {
                            unique,
                            ast_ref,
                            module_ir: ir_module,
                            connectors,
                        })
                    },
                )?;

                Ok(CompileValue::Simple(SimpleCompileValue::Module(
                    ElaboratedModule::Internal(result_id),
                )))
            }
            FunctionItemBody::ModuleExternal(ref unique, ast_ref) => {
                let item_params = ElaboratedItemParams {
                    unique: *unique,
                    params,
                };
                let refs = self.refs;
                let ast = &refs.fixed.parsed[ast_ref];

                let (result_id, _) = refs.shared.elaboration_arenas.elaborated_modules_external.elaborate(
                    item_params,
                    ElaboratedModuleExternal,
                    |result_id, item_params| {
                        // save generic args for later
                        let generic_args = item_params
                            .params
                            .as_ref()
                            .map(|item_params| {
                                item_params
                                    .iter()
                                    .map(|(id, value)| {
                                        let value = match value {
                                            &CompileValue::Simple(SimpleCompileValue::Bool(value)) => {
                                                if value {
                                                    BigInt::ONE
                                                } else {
                                                    BigInt::ZERO
                                                }
                                            }
                                            CompileValue::Simple(SimpleCompileValue::Int(value)) => value.clone(),
                                            _ => {
                                                return Err(diags.report_error_todo(
                                                    ast.params.as_ref().map_or(ast.span, |p| p.span),
                                                    "external module generic parameters that are not bool or int",
                                                ));
                                            }
                                        };

                                        Ok((id.inner.str(&refs.shared.interner).to_owned(), value))
                                    })
                                    .try_collect_all_vec()
                            })
                            .transpose()?;

                        // capture scope to ensure full separation
                        let scope_params = scope_params.capture(flow, body.span);

                        // elaborate ports
                        let (connectors, header) = refs.elaborate_module_ports_new(
                            ast_ref,
                            ast.span,
                            ElaboratedModule::External(result_id),
                            item_params,
                            Arc::new(scope_params),
                            &ast.ports,
                        )?;

                        // collect result
                        let ports = header
                            .ports
                            .values()
                            .map(|info| (header.ir_ports[info.ir].name.clone(), info.ty.inner.clone()))
                            .collect();
                        Ok(ElaboratedModuleExternalInfo {
                            ast_ref,
                            module_name: ast.id.str(source).to_owned(),
                            generic_args,
                            ports,
                            connectors,
                        })
                    },
                )?;

                Ok(CompileValue::Simple(SimpleCompileValue::Module(
                    ElaboratedModule::External(result_id),
                )))
            }
            FunctionItemBody::Interface(ref unique, ast_ref) => {
                let unique = *unique;
                let item_params = ElaboratedItemParams { unique, params };

                let refs = self.refs;
                let (result_id, _) = refs.shared.elaboration_arenas.elaborated_interfaces.elaborate(
                    item_params,
                    ElaboratedInterface,
                    |_, item_params| {
                        self.elaborate_interface_new(scope_params, flow, unique, &item_params.params, ast_ref)
                    },
                )?;

                Ok(CompileValue::Simple(SimpleCompileValue::Interface(result_id)))
            }
            FunctionItemBody::Struct(ref unique, ref generic_info) => {
                let unique = *unique;
                let item_params = ElaboratedItemParams { unique, params };

                let (result_id, _) = self.refs.shared.elaboration_arenas.elaborated_structs.elaborate(
                    item_params,
                    ElaboratedStruct,
                    |new_elab, item_params| {
                        self.elaborate_struct_new(
                            scope_params,
                            flow,
                            unique,
                            &item_params.params,
                            body.span,
                            generic_info,
                            new_elab,
                        )
                    },
                )?;
                Ok(CompileValue::new_ty(Type::Struct(result_id)))
            }
            FunctionItemBody::Enum(ref unique, ref variants) => {
                let unique = *unique;
                let item_params = ElaboratedItemParams { unique, params };

                let (result_id, _) = self.refs.shared.elaboration_arenas.elaborated_enums.elaborate(
                    item_params,
                    ElaboratedEnum,
                    |new_elab, item_params| {
                        self.elaborate_enum_new(
                            scope_params,
                            flow,
                            unique,
                            &item_params.params,
                            body.span,
                            variants,
                            new_elab,
                        )
                    },
                )?;

                Ok(CompileValue::new_ty(Type::Enum(result_id)))
            }
        }
    }

    fn elaborate_struct_new<'a>(
        &mut self,
        scope_params: &Scope,
        flow: &mut FlowCompile,
        unique: UniqueDeclaration,
        params: &Option<Vec<(Spanned<Id>, CompileValue)>>,
        span_body: Span,
        generic_info: &'a GenericStructInfo,
        new_elab: ElaboratedStruct,
    ) -> DiagResult<ElaboratedStructInfo> {
        let diags = self.refs.diags;
        let elab = &self.refs.shared.elaboration_arenas;
        let GenericStructInfo { items } = generic_info;

        // capture scope for possible member functions
        let scope_params_captured = Arc::new(scope_params.capture(flow, span_body));

        // elaborate extra list containing fields and members
        let mut fields_eval: IndexMap<Id, ElaboratedStructField> = IndexMap::new();
        let mut methods_self: IndexMap<Id, Arc<MethodInfo>> = IndexMap::new();
        let mut any_item_err = Ok(());

        let mut err_member_duplicate = |prev_span, prev_kind, curr_span, curr_kind| {
            let e = err_member_duplicate("struct", prev_span, prev_kind, curr_span, curr_kind).report(diags);
            any_item_err = Err(e);
        };

        let mut visit_item =
            |s: &mut Self, scope: &mut ExtraScope, flow: &mut FlowCompile, item: &'a StructBodyItem| {
                match item {
                    StructBodyItem::Field(field) => {
                        let &StructField { span: _, ref_, id, ty } = field;

                        let id_eval = s.eval_id(scope.as_scope(), flow, id)?;
                        let ty = if let Some(span_ref) = ref_ {
                            let value = s.eval_expression_as_compile(
                                scope.as_scope(),
                                flow,
                                &Type::Any,
                                ty,
                                Spanned::new(span_ref, "reference field annotation"),
                            )?;
                            let stored_ty = match value.inner {
                                CompileValue::Simple(SimpleCompileValue::Type(ty)) => Type::Ref(Arc::new(ty)),
                                CompileValue::Simple(SimpleCompileValue::Interface(intf)) => {
                                    Type::RefInterface(vec![], intf)
                                }
                                _ => {
                                    return Err(DiagnosticError::new(
                                        "reference field annotation must be a type or interface",
                                        value.span,
                                        "interface views and other values are not supported here",
                                    )
                                    .report(diags));
                                }
                            };
                            Spanned::new(value.span, stored_ty)
                        } else {
                            s.eval_expression_as_ty(scope.as_scope(), flow, ty)?
                        };

                        if let Some(prev) = fields_eval.get(&id_eval.inner) {
                            let prev_id = prev.id;
                            err_member_duplicate(prev_id.span(), "field", id_eval.span(), "field");
                            return Ok(());
                        }
                        if let Some(prev_info) = methods_self.get(&id_eval.inner) {
                            err_member_duplicate(prev_info.func_decl.id.span(), "method", id_eval.span(), "field");
                            return Ok(());
                        }

                        fields_eval.insert(id_eval.inner, ElaboratedStructField { id: id_eval, ty, ref_ });
                    }
                    StructBodyItem::Method(method) => match method.params.slf.inner {
                        ParameterSelfKind::Slf => {
                            let id = match method.id {
                                MaybeIdentifier::Dummy { .. } => return Ok(()),
                                MaybeIdentifier::Identifier(id) => id,
                            };
                            let id_eval = s.eval_id(scope.as_scope(), flow, id)?.inner;

                            if let Some(prev) = fields_eval.get(&id_eval) {
                                let prev_id = prev.id;
                                err_member_duplicate(prev_id.span(), "field", id.span(), "method");
                                return Ok(());
                            }
                            if let Some(prev_info) = methods_self.get(&id_eval) {
                                err_member_duplicate(prev_info.func_decl.id.span(), "method", id.span(), "method");
                                return Ok(());
                            }

                            let info = MethodInfo {
                                scope: Arc::clone(&scope_params_captured),
                                name: id_eval,
                                func_decl: method.clone(),
                            };
                            methods_self.insert(id_eval, Arc::new(info));
                        }
                    },
                }
                Ok(())
            };

        let mut scope = scope_params.new_child(span_body);
        self.elaborate_extra_list(&mut scope, flow, items, true, &mut visit_item)?;
        any_item_err?;

        let members_static = collect_static_members_from_body(self.refs, &scope, flow, "struct", |name| {
            if let Some(prev) = fields_eval.get(&name) {
                Some((prev.id.span(), "field"))
            } else if let Some(prev_info) = methods_self.get(&name) {
                Some((prev_info.func_decl.id.span(), "method"))
            } else {
                None
            }
        });

        let debug_info_name = debug_info_name_including_params(self.refs, &unique, params);

        // check if this struct can be represented in hardware
        //   we do this once now instead of each time we need to know this
        let fields_hw = fields_eval
            .iter()
            .enumerate()
            .map(|(i, (_, field))| {
                field.ty.inner.as_hardware_type(elab).map_err(|_| NonHardwareStruct {
                    first_non_hardware_field: i,
                })
            })
            .try_collect_vec();
        let hw = fields_hw.map(|fields_hw| {
            let fields_ir = zip_eq(fields_eval.keys(), &fields_hw)
                .map(|(name, ty)| (name.str(&self.refs.shared.interner).to_owned(), ty.as_ir(self.refs)))
                .collect();
            HardwareStructInfo {
                ty_ir: IrStructType {
                    ty: HardwareChecked::new_unchecked(new_elab),
                    debug_info_name: debug_info_name.clone(),
                    fields: fields_ir,
                },
                fields: fields_hw,
            }
        });

        Ok(ElaboratedStructInfo {
            unique,
            debug_info_name,
            span_body,
            fields: fields_eval,
            hw,
            members_static,
            methods_self,
        })
    }

    fn elaborate_enum_new(
        &mut self,
        scope_params: &Scope,
        flow: &mut FlowCompile,
        unique: UniqueDeclaration,
        params: &Option<Vec<(Spanned<Id>, CompileValue)>>,
        span_body: Span,
        generic_info: &GenericEnumInfo,
        new_elab: ElaboratedEnum,
    ) -> DiagResult<ElaboratedEnumInfo> {
        let diags = self.refs.diags;
        let GenericEnumInfo {
            span_body: _,
            items,
            generic_variants: _,
        } = generic_info;

        // capture scope for possible member functions
        let scope_params_captured = Arc::new(scope_params.capture(flow, span_body));

        // elaborate extra list containing variants and members
        let mut variants_eval: IndexMap<Id, ElaboratedEnumVariantInfo> = IndexMap::new();
        let mut methods_self: IndexMap<Id, Arc<MethodInfo>> = IndexMap::new();
        let mut any_item_err = Ok(());

        let mut err_member_duplicate = |prev_span, prev_kind, curr_span, curr_kind| {
            let e = err_member_duplicate("enum", prev_span, prev_kind, curr_span, curr_kind).report(diags);
            any_item_err = Err(e);
        };

        let mut visit_item = |s: &mut Self, scope: &mut ExtraScope, flow: &mut FlowCompile, item: &EnumBodyItem| {
            match item {
                EnumBodyItem::Variant(variant) => {
                    let &EnumVariant {
                        span: _,
                        id,
                        payload: content,
                    } = variant;

                    let id = s.eval_simple_id(id);

                    let payload_ty = content
                        .map(|content| s.eval_expression_as_ty(scope.as_scope(), flow, content))
                        .transpose()?;
                    let variant_info = ElaboratedEnumVariantInfo { id, payload_ty };

                    if let Some(prev_info) = variants_eval.get(&id.inner) {
                        err_member_duplicate(prev_info.id.span(), "variant", id.span(), "variant");
                        return Ok(());
                    }
                    if let Some(prev_info) = methods_self.get(&id.inner) {
                        err_member_duplicate(prev_info.func_decl.id.span(), "method", id.span(), "variant");
                        return Ok(());
                    }

                    variants_eval.insert(id.inner, variant_info);
                }
                EnumBodyItem::Method(method) => {
                    let id = match method.id {
                        MaybeIdentifier::Dummy { .. } => return Ok(()),
                        MaybeIdentifier::Identifier(id) => id,
                    };
                    let id_eval = s.eval_id(scope.as_scope(), flow, id)?.inner;

                    if let Some(prev_info) = methods_self.get(&id_eval) {
                        err_member_duplicate(prev_info.func_decl.id.span(), "method", id.span(), "method");
                        return Ok(());
                    }
                    if let Some(prev_info) = variants_eval.get(&id_eval) {
                        err_member_duplicate(prev_info.id.span(), "variant", id.span(), "method");
                        return Ok(());
                    }

                    let info = MethodInfo {
                        scope: Arc::clone(&scope_params_captured),
                        name: id_eval,
                        func_decl: method.clone(),
                    };
                    methods_self.insert(id_eval, Arc::new(info));
                }
            }

            Ok(())
        };

        let mut scope = scope_params.new_child(span_body);
        self.elaborate_extra_list(&mut scope, flow, items, true, &mut visit_item)?;
        any_item_err?;

        let members = collect_static_members_from_body(self.refs, &scope, flow, "enum", |name| {
            if let Some(variant_info) = variants_eval.get(&name) {
                Some((variant_info.id.span(), "variant"))
            } else {
                None
            }
        });

        let debug_info_name = debug_info_name_including_params(self.refs, &unique, params);

        // check if this enum can be represented in hardware
        //   we do this once now instead of each time we need to know this for performance reasons
        let hw = try_enum_as_hardware(self.refs, &variants_eval, &debug_info_name, new_elab)?;

        Ok(ElaboratedEnumInfo {
            unique,
            debug_info_name,
            span_body,
            variants: variants_eval,
            hw,
            members_static: members,
            methods_self,
        })
    }
}

fn collect_static_members_from_body(
    refs: CompileRefs,
    scope: &Scope,
    flow: &impl Flow,
    ty_kind: &str,
    prev_span_kind: impl Fn(Id) -> Option<(Span, &'static str)>,
) -> IndexMap<Id, DiagResult<CompileValue>> {
    let diags = refs.diags;
    let interner = &refs.shared.interner;
    let mut members = IndexMap::new();
    scope.for_each_immediate_entry(|name, entry| {
        let name = match name {
            ScopeKey::Id(name) => name,
            ScopeKey::Slf(_) => return,
        };

        let member = match entry {
            DeclaredValueSingle::Value { span, value } => {
                let name_str = name.str(interner);
                if POSSIBLE_BUILTIN_TYPE_MEMBERS.contains(&name_str) {
                    Err(DiagnosticError::new(
                        format!("{ty_kind} member name collides with builtin type member"),
                        span,
                        format!("trying to declare member with name `{name_str}` here"),
                    )
                    .report(diags))
                } else if let Some((prev_span, prev_kind)) = prev_span_kind(name) {
                    Err(err_member_duplicate(ty_kind, prev_span, prev_kind, span, "member").report(diags))
                } else {
                    match value {
                        ScopedEntry::Named(value) => match value {
                            &NamedValue::Variable(var) => flow.var_capture(Spanned::new(span, var)).and_then(|value| {
                                value.map_err(|e: CaptureFailed| {
                                    diags.report_error_internal(span, format!("failed to capture member: {e:?}"))
                                })
                            }),
                            NamedValue::Signal(_) | NamedValue::Interface(_) => {
                                Err(diags.report_error_internal(span, "unexpected member named value kind"))
                            }
                        },
                        ScopedEntry::Item(_) | ScopedEntry::Captured(_) | ScopedEntry::Value(_) => {
                            Err(diags.report_error_internal(span, "unexpected member scoped entry kind"))
                        }
                    }
                }
            }
            DeclaredValueSingle::Error(e) => Err(e),
        };

        members.insert(name, member);
    });
    members
}

fn err_member_duplicate(
    ty_kind: &str,
    prev_span: Span,
    prev_kind: &str,
    curr_span: Span,
    curr_kind: &str,
) -> DiagnosticError {
    DiagnosticError::new(
        format!("conflicting definitions of {ty_kind} member"),
        curr_span,
        format!("{curr_kind} declared here"),
    )
    .add_info(prev_span, format!("{prev_kind} previously declared here"))
}

pub fn debug_info_name_including_params(
    refs: CompileRefs,
    unique: &UniqueDeclaration,
    params: &Option<Vec<(Spanned<Id>, CompileValue)>>,
) -> String {
    let interner = &refs.shared.interner;

    let mut f = unique.id.diagnostic_str(interner).to_owned();
    if let Some(params) = params {
        swrite!(f, "(");
        for ((param_id, param_value), last) in params.iter().with_last() {
            swrite!(f, "{}={}", param_id.inner.str(interner), param_value.value_string(refs));
            if !last {
                swrite!(f, ", ");
            }
        }
        swrite!(f, ")");
    }
    f
}

fn try_enum_as_hardware(
    refs: CompileRefs,
    variants_eval: &IndexMap<Id, ElaboratedEnumVariantInfo>,
    debug_info_name: &str,
    new_elab: ElaboratedEnum,
) -> DiagResult<Result<HardwareEnumInfo, NonHardwareEnum>> {
    let elab = &refs.shared.elaboration_arenas;
    let interner = &refs.shared.interner;

    if variants_eval.is_empty() {
        // no variants, cannot be represented in hardware
        return Ok(Err(NonHardwareEnum::NoVariants));
    }

    // try to map fields to hardware
    let mut payload_types = vec![];
    for (i, (_, info)) in variants_eval.iter().enumerate() {
        let ty_hw = match &info.payload_ty {
            None => None,
            Some(ty) => match ty.inner.as_hardware_type(elab) {
                Ok(ty_hw) => {
                    let ty_ir = ty_hw.as_ir(refs);
                    Some((ty_hw, ty_ir))
                }
                Err(_) => return Ok(Err(NonHardwareEnum::FirstNonHardwareVariant(i))),
            },
        };
        payload_types.push(ty_hw);
    }

    // wrap result
    let tag_range = ClosedNonEmptyRange {
        start: BigInt::ZERO,
        end: BigInt::from(variants_eval.len()),
    };
    let variants_ir = zip_eq(variants_eval.keys(), &payload_types)
        .map(|(name, payload_ty)| {
            (
                name.str(interner).to_owned(),
                payload_ty.as_ref().map(|(_, ty_ir)| ty_ir.clone()),
            )
        })
        .collect();
    let ty_ir = IrEnumType {
        ty: HardwareChecked::new_unchecked(new_elab),
        debug_info_name: debug_info_name.to_owned(),
        variants: variants_ir,
    };
    let info = HardwareEnumInfo {
        ty_ir,
        tag_range,
        payload_types,
    };
    Ok(Ok(info))
}
