use crate::syntax::ast::{
    ArenaExpressions, Arg, ArrayComprehension, ArrayLiteralElement, Assignment, Block, BlockExpression, BlockStatement,
    BlockStatementKind, ClockedProcess, ClockedProcessReset, CombinatorialProcess, CommonDeclaration,
    CommonDeclarationNamed, CommonDeclarationNamedKind, ConnectEntry, ConnectStatement, ConstBlock, ConstDeclaration,
    DomainKind, EnumBodyItem, EnumDeclaration, EnumVariant, Expression, ExpressionKind, ExtraList, ExtraListBlock,
    ExtraListItem, FileContent, ForStatement, FunctionDeclaration, Identifier, IfCondBlockPair, IfStatement,
    ImportEntry, ImportFinalKind, InterfaceListItem, InterfaceSignal, InterfaceView, Item, ItemDefInterface,
    ItemDefModuleExternal, ItemDefModuleInternal, MatchBranch, MatchPattern, MatchStatement, MaybeIdentifier,
    MaybeParameterSelf, ModuleInstance, ModulePortDomainBlock, ModulePortInBlock, ModulePortInBlockKind,
    ModulePortItem, ModulePortSingle, ModulePortSingleKind, ModuleStatement, ModuleStatementKind, Parameter,
    ParameterSelf, ParameterSelfKind, Parameters, PortConnection, PortSingleKindInner, RangeLiteral,
    RegisterDeclaration, RegisterDeclarationKind, RegisterDeclarationNew, RegisterDeclarationWire, ReturnStatement,
    StringPiece, StructBodyItem, StructDeclaration, StructField, SyncDomain, TypeDeclaration, VariableDeclaration,
    Visibility, WhileStatement, WireDeclaration, WireDeclarationDomainTyKind, WireDeclarationKind,
};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::syntax::source::SourceDatabase;
use crate::syntax::token::parse_token_string_middle;
use crate::util::regex::RegexDfa;
use indexmap::IndexMap;
use itertools::Either;
use std::borrow::Cow;
use std::cell::RefCell;
use std::ops::ControlFlow;

pub fn syntax_visit<V: SyntaxVisitor>(
    source: &SourceDatabase,
    file: &FileContent,
    visitor: &mut V,
) -> ControlFlow<V::Break> {
    let FileContent {
        span: _,
        items,
        arena_expressions,
    } = file;
    let mut ctx = VisitContext {
        source,
        arena_expressions,
        visitor,
    };
    ctx.visit_file(items)
}

pub enum FoldRangeKind {
    Comment,
    Imports,
    Region,
}

// TODO document all of this
pub trait SyntaxVisitor {
    type Break;
    const SCOPE_DECLARE: bool;

    // TODO think about and document what exactly this means,
    //   eg. for declarations it's not that straightforward
    fn should_visit_span(&self, span: Span) -> bool;

    fn report_id_declare(&mut self, id: Either<Identifier, ParameterSelf>) -> ControlFlow<Self::Break, ()> {
        let _ = id;
        ControlFlow::Continue(())
    }

    fn report_id_use(
        &mut self,
        id: Either<Identifier, Spanned<SelfExpression>>,
        scope_find_id: impl Fn() -> Vec<Span>,
    ) -> ControlFlow<Self::Break, ()> {
        let _ = (id, scope_find_id);
        ControlFlow::Continue(())
    }

    fn report_range(&mut self, range: Span, fold: Option<FoldRangeKind>) {
        let _ = (range, fold);
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Conditional {
    No,
    Yes,
}

#[derive(Debug)]
pub struct DeclScope<'p> {
    parent: Option<&'p DeclScope<'p>>,
    content: RefCell<DeclScopeContent>,
}

#[derive(Debug, Default)]
struct DeclScopeContent {
    slf: Vec<(Span, Conditional)>,
    simple: IndexMap<String, Vec<(Span, Conditional)>>,
    pattern: Vec<(RegexDfa, Span, Conditional)>,
}

#[derive(Debug)]
pub enum EvaluatedId<S> {
    Simple(S),
    Pattern(RegexDfa),
}

impl EvaluatedId<&str> {
    pub fn into_owned(self) -> EvaluatedId<String> {
        match self {
            EvaluatedId::Simple(s) => EvaluatedId::Simple(s.to_owned()),
            EvaluatedId::Pattern(regex) => EvaluatedId::Pattern(regex),
        }
    }
}

struct VisitContext<'a, 'v, V> {
    source: &'a SourceDatabase,
    arena_expressions: &'a ArenaExpressions,
    visitor: &'v mut V,
}

#[derive(Debug, Copy, Clone)]
pub struct SelfExpression;

impl<'p> DeclScope<'p> {
    fn new_root() -> Self {
        Self {
            parent: None,
            content: RefCell::new(DeclScopeContent::default()),
        }
    }

    fn new_child(&'p self) -> Self {
        Self {
            parent: Some(self),
            content: RefCell::new(DeclScopeContent::default()),
        }
    }

    fn merge_conditional_child(&mut self, child: DeclScopeContent) {
        let DeclScopeContent { slf, simple, pattern } = child;
        let mut parent = self.content.borrow_mut();

        for (span, _) in slf {
            parent.slf.push((span, Conditional::Yes));
        }
        for (k, v) in simple {
            for (span, _) in v {
                parent
                    .simple
                    .entry(k.clone())
                    .or_default()
                    .push((span, Conditional::Yes));
            }
        }
        for (k, span, _) in pattern {
            parent.pattern.push((k, span, Conditional::Yes));
        }
    }

    fn find(&self, id: &Either<EvaluatedId<&str>, SelfExpression>) -> Vec<Span> {
        let mut curr = self;
        let mut result = vec![];

        loop {
            let content = curr.content.borrow();
            let mut any_certain = false;

            match id {
                Either::Left(id) => {
                    // check simple
                    match id {
                        &EvaluatedId::Simple(id) => {
                            if let Some(entries) = content.simple.get(id) {
                                for &(span, cond) in entries {
                                    result.push(span);
                                    match cond {
                                        Conditional::Yes => {}
                                        Conditional::No => any_certain = true,
                                    }
                                }
                            }
                        }
                        EvaluatedId::Pattern(id) => {
                            for (key, entries) in &content.simple {
                                if id.could_match_str(key) {
                                    for &(span, cond) in entries {
                                        result.push(span);
                                        // pattern matches are never certain
                                        let _ = cond;
                                    }
                                }
                            }
                        }
                    }

                    // check patterns
                    for &(ref pattern, span, c) in &content.pattern {
                        let could_match = match id {
                            EvaluatedId::Simple(id) => pattern.could_match_str(id),
                            EvaluatedId::Pattern(id) => pattern.could_match_pattern(id),
                        };
                        if could_match {
                            result.push(span);
                            // pattern matches are never certain
                            let _ = c;
                        }
                    }
                }
                Either::Right(_) => {
                    for &(span, cond) in &content.slf {
                        result.push(span);
                        match cond {
                            Conditional::Yes => {}
                            Conditional::No => any_certain = true,
                        }
                    }
                }
            }

            if any_certain {
                break;
            }

            curr = match &curr.parent {
                Some(parent) => parent,
                None => break,
            }
        }

        result
    }
}

impl DeclScopeContent {
    fn declare(&mut self, cond: Conditional, span: Span, id: Either<EvaluatedId<&str>, ParameterSelfKind>) {
        match id {
            Either::Left(id) => match id {
                EvaluatedId::Simple(id_inner) => {
                    self.simple.entry(id_inner.to_owned()).or_default().push((span, cond));
                }
                EvaluatedId::Pattern(pattern) => self.pattern.push((pattern, span, cond)),
            },
            Either::Right(_) => {
                self.slf.push((span, cond));
            }
        }
    }
}

macro_rules! check_skip {
    ($ctx: expr, $span: expr) => {
        if !$ctx.visitor.should_visit_span($span) {
            return ControlFlow::Continue(());
        }
    };
}

impl<V: SyntaxVisitor> VisitContext<'_, '_, V> {
    fn visit_file(&mut self, items: &[Item]) -> ControlFlow<V::Break> {
        // first pass: declare all items in scope
        // TODO should we filter based on span here or not? maybe make an enum for how declarations should behave
        //   at least document this properly
        let mut scope = DeclScope::new_root();
        for item in items {
            if let Some(info) = item.info().declaration {
                self.scope_declare(&mut scope, Conditional::No, info.id)?;
            }

            if let Item::Import(item) = item {
                let mut visit_entry = |slf: &mut VisitContext<V>, entry: &ImportEntry| {
                    let &ImportEntry { span, id, as_ } = entry;
                    slf.visitor.report_range(span, None);
                    let final_id = as_.unwrap_or(MaybeIdentifier::Identifier(id));
                    slf.scope_declare(&mut scope, Conditional::Yes, final_id.into())
                };
                self.visitor.report_range(item.final_.span, None);
                match &item.final_.inner {
                    ImportFinalKind::Single(entry) => {
                        visit_entry(self, entry)?;
                    }
                    ImportFinalKind::Multi(entries) => {
                        if let (Some(first), Some(last)) = (entries.first(), entries.last()) {
                            self.visitor.report_range(first.span.join(last.span), None);
                        }

                        for entry in entries {
                            visit_entry(self, entry)?;
                        }
                    }
                }
            }
        }

        // second pass: visit the items themselves
        for item in items {
            self.visit_file_item(&scope, item)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_file_item(&mut self, scope_file: &DeclScope, item: &Item) -> ControlFlow<V::Break> {
        let item_span = item.info().span_full;
        check_skip!(self, item_span);

        // TODO report single fold range for consecutive imports
        // TODO report single fold range for multi-line comments? that's really more of a token thing, not really AST
        let fold = if let Item::Import(_) = item {
            FoldRangeKind::Imports
        } else {
            FoldRangeKind::Region
        };
        self.visitor.report_range(item_span, Some(fold));

        match item {
            Item::Import(_) => {
                // TODO implement "go to definition" for paths, entries, ...
                ControlFlow::Continue(())
            }
            Item::CommonDeclaration(decl) => {
                // we don't need a real scope here, the declaration would already have happened in the first pass
                let mut scope_dummy = scope_file.new_child();
                self.visit_common_declaration(&mut scope_dummy, &decl.inner)
            }
            Item::ModuleInternal(decl) => {
                let ItemDefModuleInternal {
                    span: _,
                    vis: _,
                    id: _,
                    params,
                    ports,
                    body,
                } = decl;

                let mut scope_params = scope_file.new_child();
                if let Some(params) = params {
                    self.visit_parameters(&mut scope_params, params)?;
                }

                let mut scope_ports = scope_params.new_child();
                self.visitor.report_range(ports.span, None);
                self.visit_extra_list(&mut scope_ports, &ports.inner, &mut |slf, scope_ports, port| {
                    slf.visit_port_item(scope_ports, port)
                })?;

                self.visitor.report_range(body.span, Some(FoldRangeKind::Region));
                let scope_body = scope_ports.new_child();
                let mut scope_body_inner = DeclScope::new_child(&scope_body);
                self.visit_extra_list(&mut scope_body_inner, &body.inner, &mut |slf, scope, stmt| {
                    slf.visit_module_statement(&scope_body, scope, stmt)
                })?;

                ControlFlow::Continue(())
            }
            Item::ModuleExternal(decl) => {
                let ItemDefModuleExternal {
                    span: _,
                    span_ext: _,
                    vis: _,
                    id: _,
                    params,
                    ports,
                } = decl;

                let mut scope_params = scope_file.new_child();
                if let Some(params) = params {
                    self.visit_parameters(&mut scope_params, params)?;
                }

                let mut scope_ports = scope_params.new_child();
                self.visitor.report_range(ports.span, None);
                self.visit_extra_list(&mut scope_ports, &ports.inner, &mut |slf, scope_ports, port| {
                    slf.visit_port_item(scope_ports, port)
                })?;

                ControlFlow::Continue(())
            }
            Item::Interface(decl) => {
                let ItemDefInterface {
                    span: _,
                    vis: _,
                    id: _,
                    params,
                    span_body: _,
                    body,
                } = decl;

                let mut scope_params = scope_file.new_child();
                if let Some(params) = params {
                    self.visit_parameters(&mut scope_params, params)?;
                }

                // match two-pass system from real elaboration
                let mut scope_body = scope_params.new_child();
                let mut scope_ports = DeclScope::new_root();
                let mut scope_views = DeclScope::new_root();

                let mut all_view_ports = vec![];

                self.visit_extra_list(&mut scope_body, body, &mut |slf, scope_body, item| {
                    match item {
                        &InterfaceListItem::Signal(signal) => {
                            let InterfaceSignal {
                                id: signal_id,
                                ty: signal_ty,
                            } = signal;
                            slf.visitor.report_range(signal_id.span().join(signal_ty.span), None);
                            slf.visit_expression(scope_body, signal_ty)?;
                            slf.scope_declare(&mut scope_ports, Conditional::No, signal_id.into())?;
                        }
                        InterfaceListItem::View(view) => {
                            let &InterfaceView {
                                span,
                                id,
                                ref port_dirs,
                            } = view;

                            slf.visitor.report_range(span, Some(FoldRangeKind::Region));

                            slf.visit_extra_list(scope_body, port_dirs, &mut |slf, _, port| {
                                let (port_name, _) = port.inner;
                                slf.visitor.report_range(port.span, None);
                                all_view_ports.push(port_name);
                                ControlFlow::Continue(())
                            })?;
                            slf.scope_declare(&mut scope_views, Conditional::No, id)?;
                        }
                    }

                    ControlFlow::Continue(())
                })?;

                for port_id in all_view_ports {
                    self.visit_id_usage(&scope_ports, Either::Left(port_id.into()))?;
                }

                ControlFlow::Continue(())
            }
        }
    }

    fn visit_port_item(&mut self, scope_ports: &mut DeclScope, port: &ModulePortItem) -> ControlFlow<V::Break> {
        self.visitor.report_range(port.span(), None);

        match port {
            ModulePortItem::Single(port) => {
                let &ModulePortSingle { span: _, id, ref kind } = port;
                match kind {
                    ModulePortSingleKind::Port { direction: _, kind } => match kind {
                        PortSingleKindInner::Clock { span_clock: _ } => {}
                        &PortSingleKindInner::Normal { domain, ty } => {
                            self.visit_domain(scope_ports, domain)?;
                            self.visit_expression(scope_ports, ty)?;
                        }
                    },
                    &ModulePortSingleKind::Interface {
                        span_keyword: _,
                        domain,
                        interface,
                    } => {
                        self.visit_domain(scope_ports, domain)?;
                        self.visit_expression(scope_ports, interface)?;
                    }
                }
                self.scope_declare(scope_ports, Conditional::No, id.into())?;
                ControlFlow::Continue(())
            }
            ModulePortItem::DomainBlock(block) => {
                let &ModulePortDomainBlock {
                    span,
                    domain,
                    ref ports,
                } = block;

                self.visitor.report_range(span, Some(FoldRangeKind::Region));

                self.visit_domain(scope_ports, domain)?;
                self.visit_extra_list_block(scope_ports, ports, &mut |slf, scope_ports, port| {
                    let &ModulePortInBlock { span, id, ref kind } = port;
                    slf.visitor.report_range(span, None);

                    match *kind {
                        ModulePortInBlockKind::Port { direction: _, ty } => {
                            slf.visit_expression(scope_ports, ty)?;
                        }
                        ModulePortInBlockKind::Interface {
                            span_keyword: _,
                            interface,
                        } => {
                            slf.visit_expression(scope_ports, interface)?;
                        }
                    }
                    slf.scope_declare(scope_ports, Conditional::No, id.into())?;
                    ControlFlow::Continue(())
                })?;

                ControlFlow::Continue(())
            }
        }
    }

    fn visit_domain(&mut self, scope: &DeclScope, domain: Spanned<DomainKind<Expression>>) -> ControlFlow<V::Break> {
        self.visitor.report_range(domain.span, None);

        match domain.inner {
            DomainKind::Const => ControlFlow::Continue(()),
            DomainKind::Async => ControlFlow::Continue(()),
            DomainKind::Sync(domain) => self.visit_domain_sync(scope, domain),
        }
    }

    fn visit_domain_sync(&mut self, scope: &DeclScope, domain: SyncDomain<Expression>) -> ControlFlow<V::Break> {
        self.visitor.report_range(domain.span(), None);

        let SyncDomain { clock, reset } = domain;
        self.visit_expression(scope, clock)?;
        if let Some(reset) = reset {
            self.visit_expression(scope, reset)?;
        }
        ControlFlow::Continue(())
    }

    fn visit_common_declaration<S>(
        &mut self,
        scope_parent: &mut DeclScope,
        decl: &CommonDeclaration<S>,
    ) -> ControlFlow<V::Break> {
        self.visitor.report_range(decl.span(), Some(FoldRangeKind::Region));

        match decl {
            CommonDeclaration::Named(decl) => {
                let CommonDeclarationNamed { vis: _, kind } = decl;
                let id = match kind {
                    CommonDeclarationNamedKind::Type(decl) => {
                        let &TypeDeclaration {
                            span: _,
                            id,
                            ref params,
                            body,
                        } = decl;

                        let mut scope_params = scope_parent.new_child();
                        if let Some(params) = params {
                            self.visit_parameters(&mut scope_params, params)?;
                        }
                        self.visit_expression(&scope_params, body)?;

                        id
                    }
                    CommonDeclarationNamedKind::Const(decl) => {
                        let &ConstDeclaration { span: _, id, ty, value } = decl;

                        if let Some(ty) = ty {
                            self.visit_expression(scope_parent, ty)?;
                        }
                        self.visit_expression(scope_parent, value)?;

                        id
                    }
                    CommonDeclarationNamedKind::Struct(decl) => {
                        let &StructDeclaration {
                            span: _,
                            span_body: _,
                            id,
                            ref params,
                            ref items,
                        } = decl;

                        let mut scope_params = scope_parent.new_child();
                        if let Some(params) = params {
                            self.visit_parameters(&mut scope_params, params)?;
                        }
                        self.visit_extra_list(&mut scope_params, items, &mut |slf, scope, item| {
                            match item {
                                StructBodyItem::Field(field) => {
                                    let &StructField {
                                        span,
                                        ref_: _,
                                        id: _,
                                        ty,
                                    } = field;
                                    slf.visitor.report_range(span, None);
                                    slf.visit_expression(scope, ty)?;
                                }
                                StructBodyItem::Method(decl) => {
                                    slf.visit_function_declaration(scope, decl)?;
                                }
                            }

                            ControlFlow::Continue(())
                        })?;

                        id
                    }
                    CommonDeclarationNamedKind::Enum(decl) => {
                        let &EnumDeclaration {
                            span: _,
                            id,
                            ref params,
                            ref items,
                        } = decl;

                        let mut scope_params = scope_parent.new_child();
                        if let Some(params) = params {
                            self.visit_parameters(&mut scope_params, params)?;
                        }

                        self.visit_extra_list(&mut scope_params, items, &mut |slf, scope_params, item| {
                            match item {
                                EnumBodyItem::Variant(variant) => {
                                    let &EnumVariant {
                                        span,
                                        id: _,
                                        payload: content,
                                    } = variant;
                                    slf.visitor.report_range(span, None);

                                    // TODO declare variant name
                                    if let Some(content) = content {
                                        slf.visit_expression(scope_params, content)?;
                                    }
                                }
                                EnumBodyItem::Method(decl) => {
                                    slf.visit_function_declaration(scope_parent, decl)?;
                                }
                            }

                            ControlFlow::Continue(())
                        })?;

                        id
                    }
                    CommonDeclarationNamedKind::Function(decl) => {
                        self.visit_function_declaration(scope_parent, decl)?
                    }
                };

                self.scope_declare(scope_parent, Conditional::No, id)?;
            }
            CommonDeclaration::ConstBlock(block) => {
                let ConstBlock { span_keyword: _, block } = block;
                self.visit_block_statements(scope_parent, block)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_function_declaration<S: MaybeParameterSelf>(
        &mut self,
        scope_parent: &DeclScope,
        decl: &FunctionDeclaration<S>,
    ) -> ControlFlow<V::Break, MaybeIdentifier> {
        let &FunctionDeclaration {
            span: _,
            id,
            ref params,
            ret_ty,
            ref body,
        } = decl;

        let mut scope_params = scope_parent.new_child();
        self.visit_parameters(&mut scope_params, params)?;
        if let Some(ret_ty) = ret_ty {
            self.visit_expression(&scope_params, ret_ty)?;
        }
        self.visit_block_statements(&scope_params, body)?;

        ControlFlow::Continue(id)
    }

    fn visit_parameters<S: MaybeParameterSelf>(
        &mut self,
        scope: &mut DeclScope,
        params: &Parameters<S>,
    ) -> ControlFlow<V::Break> {
        let &Parameters { span, slf, ref items } = params;
        self.visitor.report_range(span, Some(FoldRangeKind::Region));

        if let Some(slf) = slf.as_parameter_self() {
            self.scope_declare_impl(scope, Conditional::No, Either::Right(slf))?;
        }

        self.visit_extra_list(scope, items, &mut |slf, scope, param| {
            let &Parameter { span, id, ty, default } = param;

            slf.visitor.report_range(span, None);

            slf.visit_expression(scope, ty)?;
            if let Some(default) = default {
                slf.visit_expression(scope, default)?;
            }
            slf.scope_declare(scope, Conditional::No, id.into())?;
            ControlFlow::Continue(())
        })
    }

    fn visit_extra_list<T>(
        &mut self,
        scope_parent: &mut DeclScope,
        list: &ExtraList<T>,
        f: &mut impl FnMut(&mut Self, &mut DeclScope, &T) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        let &ExtraList { span, ref items } = list;
        self.visitor.report_range(span, None);
        self.visit_extra_list_items(scope_parent, items, f)
    }

    fn visit_extra_list_block<T>(
        &mut self,
        scope_parent: &mut DeclScope,
        block: &ExtraListBlock<T>,
        f: &mut impl FnMut(&mut Self, &mut DeclScope, &T) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        let &ExtraListBlock { span, ref items } = block;
        self.visitor.report_range(span, Some(FoldRangeKind::Region));
        self.visit_extra_list_items(scope_parent, items, f)
    }

    fn visit_extra_list_items<T>(
        &mut self,
        scope_parent: &mut DeclScope,
        items: &[ExtraListItem<T>],
        f: &mut impl FnMut(&mut Self, &mut DeclScope, &T) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        // TODO this is overly pessimistic, if/else combo can become non-conditional,
        //   which we don't model correctly
        // TODO this is not right, not all declarations leak out into the parent scope,
        //   only public ones or in special ExtraList cases (eg. parameters, ports, ...)
        // TODO leaking and non-leaking of declarations is wrongly implemented in general,
        //   we should probably split extra if/for out from statement if/for
        for item in items {
            match item {
                ExtraListItem::Leaf(leaf) => f(self, scope_parent, leaf)?,
                ExtraListItem::Declaration(decl) => self.visit_common_declaration(scope_parent, decl)?,
                ExtraListItem::If(stmt) => {
                    let mut scope_cond = scope_parent.new_child();
                    self.visit_if_stmt(&mut scope_cond, stmt, &mut |slf, s: &mut DeclScope, b| {
                        slf.visit_extra_list_block(s, b, f)
                    })?;

                    scope_parent.merge_conditional_child(scope_cond.content.into_inner());
                }
                ExtraListItem::Match(stmt) => {
                    let mut scope_cond = scope_parent.new_child();

                    self.visit_match_stmt(&mut scope_cond, stmt, &mut |slf, s: &mut DeclScope, b| {
                        slf.visit_extra_list_block(s, b, f)
                    })?;

                    scope_parent.merge_conditional_child(scope_cond.content.into_inner());
                }
                ExtraListItem::For(stmt) => {
                    let scope_cond = scope_parent.new_child();
                    self.visit_for_stmt(scope_parent, stmt, |slf, s, b| slf.visit_extra_list_block(s, b, f))?;

                    scope_parent.merge_conditional_child(scope_cond.content.into_inner());
                }
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_if_stmt<'a, B: 'a>(
        &mut self,
        scope: &mut DeclScope,
        if_stmt: &'a IfStatement<B>,
        f: &mut impl FnMut(&mut Self, &mut DeclScope, &'a B) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        let &IfStatement {
            span,
            ref initial_if,
            ref else_ifs,
            ref final_else,
        } = if_stmt;

        self.visitor.report_range(span, None);

        let mut visit_pair = |slf: &mut Self, pair: &'a IfCondBlockPair<B>| {
            let &IfCondBlockPair {
                span,
                span_if: _,
                cond,
                ref block,
            } = pair;

            slf.visitor.report_range(span, None);

            slf.visit_expression(scope, cond)?;
            f(slf, scope, block)?;

            ControlFlow::Continue(())
        };

        visit_pair(self, initial_if)?;
        for else_if in else_ifs {
            visit_pair(self, else_if)?;
        }
        if let Some(final_else) = final_else {
            f(self, scope, final_else)?;
        }
        ControlFlow::Continue(())
    }

    fn visit_match_stmt<'a, B: HasSpan>(
        &mut self,
        scope: &mut DeclScope,
        match_stmt: &'a MatchStatement<B>,
        f: &mut impl FnMut(&mut Self, &mut DeclScope, &'a B) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        let &MatchStatement {
            span_keyword: _,
            target,
            ref branches,
            pos_end: _,
        } = match_stmt;

        self.visitor.report_range(match_stmt.span(), None);

        self.visit_expression(scope, target)?;

        for branch in branches {
            let MatchBranch { pattern, block } = branch;

            self.visitor.report_range(branch.span(), None);
            self.visitor.report_range(pattern.span, None);

            let mut scope_inner = scope.new_child();
            match &pattern.inner {
                MatchPattern::Wildcard => {}
                &MatchPattern::WildcardVal(id) => {
                    self.scope_declare(&mut scope_inner, Conditional::No, id)?;
                }
                &MatchPattern::EqualTo(expr) => {
                    self.visit_expression(scope, expr)?;
                }
                &MatchPattern::InRange { span_in: _, range } => {
                    self.visit_expression(scope, range)?;
                }
                &MatchPattern::IsEnumVariant {
                    variant: _,
                    payload_id: payload,
                } => {
                    if let Some(payload) = payload {
                        self.scope_declare(&mut scope_inner, Conditional::No, payload)?;
                    }
                }
            }

            f(self, &mut scope_inner, block)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_for_stmt<'a, B: HasSpan>(
        &mut self,
        scope: &DeclScope,
        stmt: &'a ForStatement<B>,
        f: impl FnOnce(&mut Self, &mut DeclScope, &'a B) -> ControlFlow<V::Break>,
    ) -> ControlFlow<V::Break> {
        let &ForStatement {
            span_keyword: _,
            index,
            index_ty,
            iter,
            ref body,
        } = stmt;

        self.visitor.report_range(stmt.span(), None);

        self.visit_expression(scope, iter)?;

        if let Some(index_ty) = index_ty {
            self.visit_expression(scope, index_ty)?;
        }

        let mut scope_inner = scope.new_child();
        self.scope_declare(&mut scope_inner, Conditional::No, index)?;

        f(self, &mut scope_inner, body)?;

        ControlFlow::Continue(())
    }

    fn visit_block_statements(
        &mut self,
        scope_parents: &DeclScope,
        block: &Block<BlockStatement>,
    ) -> ControlFlow<V::Break> {
        let &Block { span, ref statements } = block;

        // declarations inside a block can't leak outside, so we can skip here
        check_skip!(self, span);

        self.visitor.report_range(span, Some(FoldRangeKind::Region));

        let mut scope = scope_parents.new_child();
        for stmt in statements {
            self.visit_statement(&mut scope, stmt)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_statement(&mut self, scope: &mut DeclScope, stmt: &BlockStatement) -> ControlFlow<V::Break> {
        let stmt_span = stmt.span;

        self.visitor.report_range(stmt_span, None);

        match &stmt.inner {
            BlockStatementKind::CommonDeclaration(decl) => {
                self.visit_common_declaration(scope, decl)?;
            }
            BlockStatementKind::VariableDeclaration(decl) => {
                let &VariableDeclaration {
                    span: _,
                    mutable: _,
                    id,
                    ty,
                    init,
                } = decl;
                if let Some(ty) = ty {
                    self.visit_expression(scope, ty)?;
                }
                if let Some(init) = init {
                    self.visit_expression(scope, init)?;
                }
                self.scope_declare(scope, Conditional::No, id)?;
            }
            BlockStatementKind::RegisterDeclaration(decl) => {
                let &RegisterDeclaration {
                    span_keyword: _,
                    kind,
                    reset,
                } = decl;

                match kind {
                    RegisterDeclarationKind::Wire(RegisterDeclarationWire {
                        span_keyword_wire: _,
                        target,
                    }) => {
                        self.visit_expression(scope, target)?;
                        self.visit_expression(scope, reset)?;
                    }
                    RegisterDeclarationKind::New(RegisterDeclarationNew { id, ty }) => {
                        self.visit_id_decl(scope, MaybeIdentifier::Identifier(id))?;
                        if let Some(ty) = ty {
                            self.visit_expression(scope, ty)?;
                        }
                        self.visit_expression(scope, reset)?;
                        self.scope_declare(scope, Conditional::No, id.into())?;
                    }
                }
            }
            BlockStatementKind::Assignment(stmt) => {
                let &Assignment {
                    span: _,
                    op: _,
                    target,
                    value,
                } = stmt;
                self.visit_expression(scope, target)?;
                self.visit_expression(scope, value)?;
            }
            &BlockStatementKind::Expression(expr) => {
                self.visit_expression(scope, expr)?;
            }
            BlockStatementKind::Block(block) => {
                self.visit_block_statements(scope, block)?;
            }
            BlockStatementKind::If(stmt) => {
                check_skip!(self, stmt_span);
                self.visit_if_stmt(scope, stmt, &mut |slf, s, b| slf.visit_block_statements(s, b))?;
            }
            BlockStatementKind::Match(stmt) => {
                check_skip!(self, stmt_span);
                self.visit_match_stmt(scope, stmt, &mut |slf, s, b| slf.visit_block_statements(s, b))?;
            }
            BlockStatementKind::For(stmt) => {
                check_skip!(self, stmt_span);
                self.visit_for_stmt(scope, stmt, |slf, s, b| slf.visit_block_statements(s, b))?;
            }
            BlockStatementKind::While(stmt) => {
                check_skip!(self, stmt_span);
                let &WhileStatement {
                    span_keyword: _,
                    cond,
                    ref body,
                } = stmt;
                self.visit_expression(scope, cond)?;
                self.visit_block_statements(scope, body)?;
            }
            BlockStatementKind::Return(stmt) => {
                let &ReturnStatement { span_return: _, value } = stmt;
                if let Some(value) = value {
                    self.visit_expression(scope, value)?;
                }
            }
            BlockStatementKind::Break { span: _ } | BlockStatementKind::Continue { span: _ } => {}
        }

        ControlFlow::Continue(())
    }

    fn visit_module_statement(
        &mut self,
        module_scope: &DeclScope,
        scope: &mut DeclScope,
        stmt: &ModuleStatement,
    ) -> ControlFlow<V::Break> {
        self.visitor.report_range(stmt.span, None);
        match &stmt.inner {
            ModuleStatementKind::ParseError(_) => {
                // do nothing
            }
            ModuleStatementKind::WireDeclaration(decl) => {
                let &WireDeclaration {
                    vis,
                    span_keyword: _,
                    id,
                    kind,
                } = decl;

                self.visit_id_decl(scope, id)?;

                match kind {
                    WireDeclarationKind::Normal {
                        domain_ty,
                        assign_span_and_value,
                    } => {
                        match domain_ty {
                            WireDeclarationDomainTyKind::Clock { span_clock: _ } => {}
                            WireDeclarationDomainTyKind::Normal { domain, ty } => {
                                if let Some(domain) = domain {
                                    self.visit_domain(scope, domain)?;
                                }
                                if let Some(ty) = ty {
                                    self.visit_expression(scope, ty)?;
                                }
                            }
                        }

                        if let Some((_, value)) = assign_span_and_value {
                            self.visit_expression(scope, value)?;
                        }
                    }
                    WireDeclarationKind::Interface {
                        domain,
                        span_keyword: _,
                        interface,
                    } => {
                        if let Some(domain) = domain {
                            self.visit_domain(scope, domain)?;
                        }
                        self.visit_expression(scope, interface)?;
                    }
                }

                match vis {
                    Visibility::Public { span: _ } => {
                        self.scope_declare_impl(module_scope, Conditional::No, Either::Left(id))?
                    }
                    Visibility::Private => self.scope_declare(scope, Conditional::No, id)?,
                }
            }
            ModuleStatementKind::CombinatorialProcess(stmt) => {
                let CombinatorialProcess { span_keyword: _, block } = stmt;
                self.visit_block_statements(scope, block)?;
            }
            ModuleStatementKind::ClockedProcess(stmt) => {
                let &ClockedProcess {
                    span_keyword: _,
                    span_domain,
                    clock,
                    reset,
                    ref block,
                } = stmt;
                self.visitor.report_range(span_domain, None);
                self.visit_expression(scope, clock)?;
                if let Some(reset) = reset {
                    self.visitor.report_range(reset.span, None);
                    let ClockedProcessReset { kind: _, signal } = reset.inner;
                    self.visit_expression(scope, signal)?;
                }
                self.visit_block_statements(scope, block)?;
            }
            ModuleStatementKind::Instance(stmt) => {
                let &ModuleInstance {
                    name: _,
                    span_keyword: _,
                    module,
                    ref port_connections,
                } = stmt;

                self.visit_expression(scope, module)?;

                self.visitor.report_range(port_connections.span, None);

                let mut scope_connections = DeclScope::new_child(scope);
                self.visit_extra_list(
                    &mut scope_connections,
                    &port_connections.inner,
                    &mut |slf, scope_connections, connection| {
                        slf.visitor.report_range(connection.span(), None);

                        let &PortConnection { id, expr } = connection;
                        // TODO try resolving port name, needs type info
                        let _ = id;
                        slf.visit_expression(scope_connections, expr.expr())?;

                        ControlFlow::Continue(())
                    },
                )?;
            }
            ModuleStatementKind::Connect(stmt) => {
                let ConnectStatement {
                    span_keyword: _,
                    entries,
                } = stmt;

                self.visitor.report_range(entries.span, None);

                let mut scope_entries = DeclScope::new_child(scope);
                self.visit_extra_list(&mut scope_entries, entries, &mut |slf, scope_entries, entry| {
                    slf.visitor.report_range(entry.span, None);

                    let &ConnectEntry { span: _, expr, view } = entry;
                    // TODO try resolving view name, needs type info
                    let _ = view;
                    slf.visit_expression(scope_entries, expr)?;

                    ControlFlow::Continue(())
                })?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_array_literal_element(
        &mut self,
        scope: &DeclScope,
        elem: ArrayLiteralElement<Expression>,
    ) -> ControlFlow<V::Break> {
        self.visitor.report_range(elem.span(), None);

        match elem {
            ArrayLiteralElement::Single(elem) => self.visit_expression(scope, elem),
            ArrayLiteralElement::Spread(_, elem) => self.visit_expression(scope, elem),
        }
    }

    fn visit_expression(&mut self, scope: &DeclScope, expr: Expression) -> ControlFlow<V::Break> {
        // expressions can't contain declarations that leak outside, so we can skip here
        check_skip!(self, expr.span);

        self.visitor.report_range(expr.span, None);

        match &self.arena_expressions[expr.inner] {
            &ExpressionKind::ParseError(_) => {
                // do nothing
            }
            &ExpressionKind::Builtin { span_keyword, ref args } => {
                self.visitor.report_range(span_keyword, None);
                self.visitor.report_range(args.span, Some(FoldRangeKind::Region));
                for &arg in &args.inner {
                    self.visit_expression(scope, arg)?;
                }
            }
            &ExpressionKind::Wrapped(inner) => {
                self.visit_expression(scope, inner)?;
            }
            ExpressionKind::Block(block) => {
                let &BlockExpression {
                    ref statements,
                    expression,
                } = block;
                let mut scope_inner = scope.new_child();
                for stmt in statements {
                    self.visit_statement(&mut scope_inner, stmt)?
                }
                self.visit_expression(&scope_inner, expression)?;
            }
            &ExpressionKind::Id(id) => {
                self.visit_id_usage(scope, Either::Left(id.into()))?;
            }
            ExpressionKind::Slf => {
                self.visit_id_usage(scope, Either::Right(Spanned::new(expr.span, SelfExpression)))?;
            }
            ExpressionKind::StringLiteral(pieces) => {
                for &piece in pieces {
                    match piece {
                        StringPiece::Literal(span) => {
                            self.visitor.report_range(span, None);
                        }
                        StringPiece::Substitute(expr) => {
                            self.visit_expression(scope, expr)?;
                        }
                    }
                }
            }
            ExpressionKind::ArrayLiteral(elems) => {
                // report extra selection range covering only the inside of the literal
                if let (Some(first), Some(last)) = (elems.first(), elems.last()) {
                    self.visitor.report_range(first.span().join(last.span()), None);
                }

                for &elem in elems {
                    self.visit_array_literal_element(scope, elem)?;
                }
            }
            ExpressionKind::TupleLiteral(elems) => {
                // report extra selection range covering only the inside of the literal
                if let (Some(first), Some(last)) = (elems.first(), elems.last()) {
                    self.visitor.report_range(first.span().join(last.span()), None);
                }

                for &elem in elems {
                    self.visit_expression(scope, elem)?;
                }
            }
            ExpressionKind::RangeLiteral(expr) => match *expr {
                RangeLiteral::ExclusiveEnd { op_span: _, start, end } => {
                    if let Some(start) = start {
                        self.visit_expression(scope, start)?;
                    }
                    if let Some(end) = end {
                        self.visit_expression(scope, end)?;
                    }
                }
                RangeLiteral::InclusiveEnd {
                    op_span: _,
                    start,
                    end_inc,
                } => {
                    if let Some(start) = start {
                        self.visit_expression(scope, start)?;
                    }
                    self.visit_expression(scope, end_inc)?;
                }
                RangeLiteral::Length {
                    op_span: _,
                    start,
                    length,
                } => {
                    self.visit_expression(scope, start)?;
                    self.visit_expression(scope, length)?;
                }
            },
            ExpressionKind::ArrayComprehension(expr) => {
                let &ArrayComprehension {
                    body,
                    index,
                    span_keyword: _,
                    iter,
                } = expr;

                self.visitor.report_range(body.span().join(iter.span), None);

                self.visit_expression(scope, iter)?;

                let mut scope_inner = scope.new_child();
                self.scope_declare(&mut scope_inner, Conditional::No, index)?;

                self.visit_array_literal_element(&scope_inner, body)?;
            }
            &ExpressionKind::UnaryOp(_, inner) => {
                self.visit_expression(scope, inner)?;
            }
            &ExpressionKind::BinaryOp(_, left, right) => {
                self.visit_expression(scope, left)?;
                self.visit_expression(scope, right)?;
            }
            &ExpressionKind::ArrayType {
                span_brackets,
                ref lengths,
                element,
            } => {
                self.visitor.report_range(span_brackets, None);
                for &len in lengths {
                    self.visit_array_literal_element(scope, len)?;
                }
                self.visit_expression(scope, element)?;
            }
            &ExpressionKind::ArrayIndex {
                span_brackets,
                base,
                ref indices,
            } => {
                self.visit_expression(scope, base)?;
                self.visitor.report_range(span_brackets, None);
                for &index in indices {
                    self.visit_array_literal_element(scope, index)?;
                }
            }
            &ExpressionKind::DotIndex(base, index) => {
                // TODO try resolving index, needs type info
                self.visit_expression(scope, base)?;
                self.visitor.report_range(index.span(), None);
            }
            &ExpressionKind::Call(target, ref args) => {
                self.visit_expression(scope, target)?;

                self.visitor.report_range(args.span(), None);

                let mut scope_dummy = DeclScope::new_child(scope);
                self.visit_extra_list(&mut scope_dummy, args, &mut |slf, scope, arg| {
                    let &Arg { span, ref id, value } = arg;
                    slf.visitor.report_range(span, None);
                    // TODO try resolving id, needs type info
                    let _ = id;
                    slf.visit_expression(scope, value)?;
                    ControlFlow::Continue(())
                })?;
            }
            &ExpressionKind::UnsafeValueWithDomain(value, domain) => {
                self.visit_expression(scope, value)?;
                self.visit_domain(scope, domain)?;
            }
            &ExpressionKind::Ref(_, inner) | &ExpressionKind::Deref(_, inner) => {
                self.visit_expression(scope, inner)?;
            }
            ExpressionKind::Dummy
            | ExpressionKind::Undefined
            | ExpressionKind::Type
            | ExpressionKind::IntLiteral(_)
            | ExpressionKind::BoolLiteral(_) => {}
        }

        ControlFlow::Continue(())
    }

    // TODO what is the difference between this and visit_id_usage?
    // TODO refactor all id visiting functions, we have a bunch of partially overlapping ones
    fn visit_id_decl(&mut self, scope: &DeclScope, id: MaybeIdentifier) -> ControlFlow<V::Break> {
        self.visitor.report_range(id.span(), None);

        match id {
            MaybeIdentifier::Dummy { span: _ } => {}
            MaybeIdentifier::Identifier(id) => match id {
                Identifier::Simple(_id) => {}
                Identifier::FromString(_span, expr) => {
                    self.visit_expression(scope, expr)?;
                }
            },
        }

        ControlFlow::Continue(())
    }

    fn visit_id_usage(
        &mut self,
        scope: &DeclScope,
        id: Either<MaybeIdentifier, Spanned<SelfExpression>>,
    ) -> ControlFlow<V::Break> {
        let span = id.span();

        check_skip!(self, span);
        self.visitor.report_range(span, None);

        let report_id = match id {
            Either::Left(id) => {
                match id {
                    MaybeIdentifier::Dummy { .. } => None,
                    MaybeIdentifier::Identifier(id) => {
                        // first visit the inner expressions if any
                        match id {
                            Identifier::Simple(_id) => {}
                            Identifier::FromString(_span, expr) => {
                                self.visit_expression(scope, expr)?;
                            }
                        }

                        Some(Either::Left(id))
                    }
                }
            }
            Either::Right(slf) => Some(Either::Right(slf)),
        };

        // report the id usage itself
        if let Some(report_id) = report_id {
            self.visitor.report_id_use(report_id, || {
                let id_eval = match report_id {
                    Either::Left(report_id) => {
                        let eval_id = eval_id(self.source, self.arena_expressions, report_id);
                        Either::Left(eval_id)
                    }
                    Either::Right(slf) => Either::Right(slf.inner),
                };
                scope.find(&id_eval)
            })?;
        }

        ControlFlow::Continue(())
    }

    fn scope_declare(
        &mut self,
        scope: &mut DeclScope,
        cond: Conditional,
        id: MaybeIdentifier,
    ) -> ControlFlow<V::Break> {
        self.scope_declare_impl(scope, cond, Either::Left(id))
    }

    fn scope_declare_impl(
        &mut self,
        scope: &DeclScope,
        cond: Conditional,
        id: Either<MaybeIdentifier, ParameterSelf>,
    ) -> ControlFlow<V::Break> {
        match id {
            Either::Left(id) => match id {
                MaybeIdentifier::Dummy { .. } => {}
                MaybeIdentifier::Identifier(id) => {
                    self.visitor.report_id_declare(Either::Left(id))?;

                    if V::SCOPE_DECLARE {
                        let id_eval = eval_id(self.source, self.arena_expressions, id);
                        scope
                            .content
                            .borrow_mut()
                            .declare(cond, id.span(), Either::Left(id_eval));
                    }
                }
            },
            Either::Right(slf) => {
                self.visitor.report_id_declare(Either::Right(slf))?;

                if V::SCOPE_DECLARE {
                    scope
                        .content
                        .borrow_mut()
                        .declare(cond, slf.span, Either::Right(slf.inner));
                }
            }
        }

        ControlFlow::Continue(())
    }
}

fn eval_id<'s>(source: &'s SourceDatabase, arena: &ArenaExpressions, id: Identifier) -> EvaluatedId<&'s str> {
    match id {
        Identifier::Simple(id) => EvaluatedId::Simple(id.str(source)),
        Identifier::FromString(_, expr) => {
            // TODO look even further through eg. constants, values, ...
            match &arena[expr.inner] {
                ExpressionKind::StringLiteral(pieces) => {
                    // build a pattern that matches all possible substitutions
                    let mut pattern = String::new();
                    pattern.push('^');

                    for piece in pieces {
                        match piece {
                            &StringPiece::Literal(literal_span) => {
                                // this should never fail, but reporting an error here or panicking would be bad,
                                //   so just ignore the error if any
                                let literal = parse_token_string_middle(source.span_str(literal_span))
                                    .unwrap_or(Cow::Borrowed("?"));
                                pattern.push_str(&regex::escape(literal.as_ref()));
                            }
                            StringPiece::Substitute(_expr) => {
                                pattern.push_str(".*");
                            }
                        }
                    }

                    pattern.push('$');
                    EvaluatedId::Pattern(RegexDfa::new(&pattern).unwrap())
                }
                _ => {
                    // default to a regex that matches everything
                    // TODO maybe it's even faster to have a separate enum branch for this case
                    EvaluatedId::Pattern(RegexDfa::new(".*").unwrap())
                }
            }
        }
    }
}
