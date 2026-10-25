use crate::syntax::ast::{
    ArenaExpressions, Arg, ArrayComprehension, ArrayLiteralElement, AssignBinaryOp, Assignment, BinaryOp,
    BinaryOpLevel, Block, BlockExpression, BlockStatement, BlockStatementKind, ClockedProcess, ClockedProcessReset,
    CombinatorialProcess, CommonDeclaration, CommonDeclarationNamed, CommonDeclarationNamedKind, ConnectEntry,
    ConnectEntryView, ConnectStatement, ConstBlock, ConstDeclaration, DomainKind, DotIndexKind, EnumBodyItem,
    EnumDeclaration, EnumVariant, Expression, ExpressionKind, ExtraList, ExtraListBlock, ExtraListItem, FileContent,
    ForStatement, FunctionDeclaration, Identifier, IfCondBlockPair, IfStatement, ImportEntry, ImportFinalKind,
    IntLiteral, InterfaceListItem, InterfaceSignal, InterfaceView, Item, ItemDefInterface, ItemDefModuleExternal,
    ItemDefModuleInternal, ItemImport, MatchBranch, MatchPattern, MatchStatement, MaybeIdentifier, MaybeParameterSelf,
    MaybeVisibility, ModuleInstance, ModulePortDomainBlock, ModulePortInBlock, ModulePortInBlockKind, ModulePortItem,
    ModulePortSingle, ModulePortSingleKind, ModuleStatement, ModuleStatementKind, Parameter, ParameterSelfKind,
    Parameters, PortConnection, PortConnectionExpression, PortSingleKindInner, RangeLiteral, RegisterDeclaration,
    RegisterDeclarationKind, RegisterDeclarationNew, RegisterDeclarationWire, ReturnStatement, StringPiece,
    StructBodyItem, StructDeclaration, StructField, SyncDomain, TypeDeclaration, VariableDeclaration, Visibility,
    WhileStatement, WireDeclaration, WireDeclarationDomainTyKind, WireDeclarationKind,
};
use crate::syntax::format::high::{HNode, PreserveKind};
use crate::syntax::parser::RecoveredParseError;
use crate::syntax::pos::{HasSpan, Span};
use crate::syntax::token::TokenType as TT;
use crate::util::iter::IterExt;
use itertools::Either;
use std::cell::Cell;

pub fn ast_to_node(file: &FileContent) -> Result<HNode, RecoveredParseError> {
    let FileContent {
        span: _,
        items,
        arena_expressions,
    } = file;

    let mut ctx = Context {
        arena_expressions,
        any_parse_error: Cell::new(None),
    };
    let result = ctx.fmt_file_items(items);

    if let Some(e) = ctx.any_parse_error.into_inner() {
        Err(e)
    } else {
        Ok(result)
    }
}

struct Context<'a> {
    arena_expressions: &'a ArenaExpressions,
    any_parse_error: Cell<Option<RecoveredParseError>>,
}

impl Context<'_> {
    fn report_parse_error(&self, e: RecoveredParseError) -> HNode {
        self.any_parse_error.set(Some(e));
        HNode::EMPTY
    }

    fn fmt_file_items(&mut self, items: &[Item]) -> HNode {
        // special case to deal with empty files
        let mut nodes = vec![HNode::PreserveBlankLines(PreserveKind::Always)];

        for item in items {
            let item_node = match item {
                Item::Import(import) => self.fmt_import(import),
                Item::CommonDeclaration(decl) => self.fmt_common_decl(&decl.inner),
                Item::ModuleInternal(decl) => {
                    let &ItemDefModuleInternal {
                        span: _,
                        vis,
                        id,
                        ref params,
                        ref ports,
                        ref body,
                    } = decl;
                    self.fmt_module_decl(vis, false, id, params.as_ref(), &ports.inner, Some(&body.inner))
                }
                Item::ModuleExternal(decl) => {
                    let &ItemDefModuleExternal {
                        span: _,
                        vis,
                        span_ext: _,
                        id,
                        ref params,
                        ref ports,
                    } = decl;
                    self.fmt_module_decl(vis, true, id.into(), params.as_ref(), &ports.inner, None)
                }
                Item::Interface(decl) => self.fmt_interface_decl(decl),
            };
            nodes.push(skippable(item.info().span_full, item_node));

            nodes.push(HNode::PreserveBlankLines(PreserveKind::Always))
        }

        HNode::Sequence(nodes)
    }

    fn fmt_import(&self, import: &ItemImport) -> HNode {
        let ItemImport { span: _, steps, final_ } = import;

        let mut nodes = vec![];
        nodes.push(token(TT::Import));
        nodes.push(HNode::Space);

        for &step in &steps.inner {
            nodes.push(self.fmt_id(step));
            nodes.push(token(TT::Dot));
        }

        match &final_.inner {
            ImportFinalKind::Single(entry) => {
                nodes.push(self.fmt_import_entry(entry));
            }
            ImportFinalKind::Multi(entries) => {
                let mut seq = vec![];

                for (entry, last) in entries.iter().with_last() {
                    seq.push(self.fmt_import_entry(entry));
                    seq.push(comma_nodes(last));

                    // We want to express a "fill" construct, where after each item we can independently decide to wrap.
                    //   This can be built by adding a mini-group around each WrapNewLine.
                    if !last {
                        seq.push(HNode::Group(Box::new(HNode::WrapNewline)));
                    }
                }

                nodes.push(surrounded_group_indent(SurroundKind::Square, HNode::Sequence(seq)));
            }
        }

        nodes.push(token(TT::Semi));
        nodes.push(HNode::AlwaysNewline);
        HNode::Sequence(nodes)
    }

    fn fmt_import_entry(&self, entry: &ImportEntry) -> HNode {
        let &ImportEntry { span: _, id, as_ } = entry;
        let mut nodes = vec![];
        nodes.push(self.fmt_id(id));
        if let Some(as_) = as_ {
            // TODO allow wrapping here?
            nodes.push(HNode::Space);
            nodes.push(token(TT::As));
            nodes.push(HNode::Space);
            nodes.push(self.fmt_id(as_));
        }
        HNode::Sequence(nodes)
    }

    fn fmt_extra_list<T: HasSpan>(
        &self,
        surround: SurroundKind,
        force_wrap: bool,
        list: &ExtraList<T>,
        f: &impl Fn(&T) -> HNodeAndComma,
    ) -> HNode {
        let ExtraList { span: _, items } = list;
        self.fmt_extra_list_items(surround, force_wrap, None, items, f)
    }

    fn fmt_extra_list_block<T: HasSpan>(
        &self,
        force_wrap: bool,
        block: &ExtraListBlock<T>,
        f: &impl Fn(&T) -> HNodeAndComma,
    ) -> HNode {
        let ExtraListBlock { span: _, items } = block;
        self.fmt_extra_list_items(SurroundKind::Curly, force_wrap, None, items, f)
    }

    fn fmt_extra_list_items<T: HasSpan>(
        &self,
        surround: SurroundKind,
        force_wrap: bool,
        first: Option<(Span, HNodeAndComma)>,
        items: &[ExtraListItem<T>],
        f: &impl Fn(&T) -> HNodeAndComma,
    ) -> HNode {
        let mut seq = vec![];

        if first.is_some() || !items.is_empty() {
            if force_wrap {
                seq.push(HNode::ForceWrap);
            }
            seq.push(HNode::PreserveBlankLines(PreserveKind::AfterComment));
        }

        let push_leaf = |seq: &mut Vec<HNode>, span: Span, leaf: HNodeAndComma, last: bool| {
            let HNodeAndComma { node, comma } = leaf;

            seq.push(skippable(span, node));
            if comma {
                seq.push(comma_nodes(last));
            } else {
                seq.push(HNode::ForceWrap);
            }
            if !last {
                seq.push(HNode::WrapNewline);
            }
        };

        if let Some((first_span, first)) = first {
            let last = items.is_empty();
            push_leaf(&mut seq, first_span, first, last);
            seq.push(preserve_blank_lines_after_item(last));
        }

        for (item, last) in items.iter().with_last() {
            match item {
                ExtraListItem::Leaf(leaf) => {
                    push_leaf(&mut seq, leaf.span(), f(leaf), last);
                }
                ExtraListItem::Declaration(decl) => {
                    seq.push(skippable(decl.span(), self.fmt_common_decl(decl)));
                }
                ExtraListItem::If(stmt) => {
                    let node = self.fmt_if(stmt, |inner| self.fmt_extra_list_block(force_wrap, inner, f));
                    seq.push(skippable(stmt.span(), node));
                }
                ExtraListItem::Match(stmt) => {
                    let node = self.fmt_match(stmt, |inner| self.fmt_extra_list_block(force_wrap, inner, f));
                    seq.push(skippable(stmt.span(), node));
                }
                ExtraListItem::For(stmt) => {
                    let node = self.fmt_for(stmt, |inner| self.fmt_extra_list_block(force_wrap, inner, f));
                    seq.push(skippable(stmt.span(), node));
                }
            }

            seq.push(preserve_blank_lines_after_item(last));
        }

        surrounded_group_indent(surround, HNode::Sequence(seq))
    }

    fn fmt_common_decl<V: MaybeVisibility>(&self, decl: &CommonDeclaration<V>) -> HNode {
        match decl {
            CommonDeclaration::Named(decl) => {
                let &CommonDeclarationNamed { vis, ref kind } = decl;
                let node_kind = match kind {
                    CommonDeclarationNamedKind::Type(decl) => {
                        let &TypeDeclaration {
                            span: _,
                            id,
                            ref params,
                            body,
                        } = decl;
                        let mut seq = vec![token(TT::Type), HNode::Space, self.fmt_id(id)];
                        if let Some(params) = params {
                            seq.push(self.fmt_parameters(params));
                        }
                        seq.push(wrapping_assign(self.fmt_expr(body)));

                        seq.push(token(TT::Semi));
                        seq.push(HNode::AlwaysNewline);
                        HNode::Sequence(seq)
                    }
                    CommonDeclarationNamedKind::Const(decl) => {
                        let &ConstDeclaration { span: _, id, ty, value } = decl;
                        self.fmt_variable_decl(token(TT::Const), self.fmt_id(id), ty, Some(value))
                    }
                    CommonDeclarationNamedKind::Struct(decl) => {
                        let &StructDeclaration {
                            span: _,
                            span_body: _,
                            id,
                            ref params,
                            ref items,
                        } = decl;

                        let mut seq = vec![token(TT::Struct), HNode::Space, self.fmt_id(id)];
                        if let Some(params) = params {
                            seq.push(self.fmt_parameters(params));
                        }
                        seq.push(HNode::Space);
                        seq.push(
                            self.fmt_extra_list(SurroundKind::Curly, true, items, &|item| match item {
                                StructBodyItem::Field(field) => {
                                    let &StructField { span: _, id, ty } = field;
                                    let node = HNode::Sequence(vec![self.fmt_id(id), wrapping_type(self.fmt_expr(ty))]);
                                    HNodeAndComma { node, comma: true }
                                }
                                StructBodyItem::Method(method) => {
                                    let node = self.fmt_function_decl(method);
                                    HNodeAndComma { node, comma: false }
                                }
                            }),
                        );
                        seq.push(HNode::AlwaysNewline);
                        HNode::Sequence(seq)
                    }
                    CommonDeclarationNamedKind::Enum(decl) => {
                        let &EnumDeclaration {
                            span: _,
                            id,
                            ref params,
                            ref items,
                        } = decl;

                        let mut seq = vec![token(TT::Enum), HNode::Space, self.fmt_id(id)];
                        if let Some(params) = params {
                            seq.push(self.fmt_parameters(params));
                        }
                        seq.push(HNode::Space);
                        seq.push(
                            self.fmt_extra_list(SurroundKind::Curly, true, items, &|item| match item {
                                EnumBodyItem::Variant(variant) => {
                                    let &EnumVariant {
                                        span: _,
                                        id,
                                        payload: content,
                                    } = variant;

                                    let node_id = self.fmt_id(id);
                                    let node = match content {
                                        None => node_id,
                                        Some(content) => HNode::Sequence(vec![
                                            node_id,
                                            surrounded_group_indent(SurroundKind::Round, self.fmt_expr(content)),
                                        ]),
                                    };
                                    HNodeAndComma { node, comma: true }
                                }
                                EnumBodyItem::Method(method) => {
                                    let node = self.fmt_function_decl(method);
                                    HNodeAndComma { node, comma: false }
                                }
                            }),
                        );
                        seq.push(HNode::AlwaysNewline);
                        HNode::Sequence(seq)
                    }
                    CommonDeclarationNamedKind::Function(decl) => self.fmt_function_decl(decl),
                };

                let mut seq = vec![];
                fmt_visibility(&mut seq, vis);
                seq.push(node_kind);
                HNode::Sequence(seq)
            }
            CommonDeclaration::ConstBlock(block) => {
                let ConstBlock { span_keyword: _, block } = block;
                HNode::Sequence(vec![
                    token(TT::Const),
                    HNode::Space,
                    self.fmt_block(block),
                    HNode::AlwaysNewline,
                ])
            }
        }
    }

    fn fmt_module_decl(
        &self,
        vis: Visibility,
        external: bool,
        id: MaybeIdentifier,
        params: Option<&Parameters>,
        ports: &ExtraList<ModulePortItem>,
        body: Option<&ExtraList<ModuleStatement>>,
    ) -> HNode {
        let mut seq = vec![];
        fmt_visibility(&mut seq, vis);

        if external {
            seq.push(token(TT::External));
            seq.push(HNode::Space);
        }

        seq.push(token(TT::Module));
        seq.push(HNode::Space);
        seq.push(self.fmt_id(id));

        if let Some(params) = params {
            seq.push(self.fmt_parameters(params));
        }

        seq.push(HNode::Space);
        seq.push(token(TT::Ports));
        seq.push(self.fmt_extra_list(SurroundKind::Round, true, ports, &|port| {
            self.fmt_module_port_item(port)
        }));

        if let Some(body) = body {
            let node_body = self.fmt_extra_list(SurroundKind::Curly, false, body, &|stmt| HNodeAndComma {
                node: self.fmt_module_statement(stmt),
                comma: false,
            });

            seq.push(HNode::Space);
            seq.push(node_body);
        }

        seq.push(HNode::AlwaysNewline);
        HNode::Sequence(seq)
    }

    fn fmt_interface_decl(&self, decl: &ItemDefInterface) -> HNode {
        let &ItemDefInterface {
            span: _,
            vis,
            id,
            ref params,
            span_body: _,
            ref body,
        } = decl;

        let mut seq = vec![];
        fmt_visibility(&mut seq, vis);
        seq.push(token(TT::Interface));
        seq.push(HNode::Space);
        seq.push(self.fmt_id(id));

        if let Some(params) = params {
            seq.push(self.fmt_parameters(params));
        }

        // TODO force newline between items of different kinds?
        let body_node = self.fmt_extra_list(SurroundKind::Curly, true, body, &|item| match item {
            &InterfaceListItem::Signal(signal) => {
                let InterfaceSignal {
                    id: signal_id,
                    ty: port_id,
                } = signal;
                let node = HNode::Sequence(vec![self.fmt_id(signal_id), wrapping_type(self.fmt_expr(port_id))]);
                HNodeAndComma { node, comma: true }
            }
            InterfaceListItem::View(view) => {
                let node = self.fmt_interface_view_decl(view);
                HNodeAndComma { node, comma: false }
            }
        });
        seq.push(HNode::Space);
        seq.push(body_node);
        seq.push(HNode::AlwaysNewline);

        HNode::Sequence(seq)
    }

    fn fmt_interface_view_decl(&self, view: &InterfaceView) -> HNode {
        let &InterfaceView {
            span: _,
            id: view_id,
            ref port_dirs,
        } = view;

        let surround = if port_dirs.is_empty() {
            SurroundKind::Curly
        } else {
            SurroundKind::CurlySpace
        };

        let token_ports = self.fmt_extra_list(surround, false, port_dirs, &|port| {
            let (port_id, port_dir) = port.inner;
            let node = HNode::Sequence(vec![
                self.fmt_id(port_id),
                token(TT::Colon),
                HNode::Space,
                token(port_dir.inner.token()),
            ]);
            HNodeAndComma { node, comma: true }
        });

        HNode::Sequence(vec![
            HNode::ForceWrap,
            token(TT::View),
            HNode::Space,
            self.fmt_id(view_id),
            HNode::Space,
            token_ports,
            HNode::AlwaysNewline,
        ])
    }

    fn fmt_function_decl<S: MaybeParameterSelf>(&self, decl: &FunctionDeclaration<S>) -> HNode {
        let &FunctionDeclaration {
            span: _,
            id,
            ref params,
            ret_ty,
            ref body,
        } = decl;

        let mut nodes = vec![
            token(TT::Fn),
            HNode::Space,
            self.fmt_id(id),
            self.fmt_parameters(params),
        ];

        if let Some(ret_ty) = ret_ty {
            nodes.push(HNode::Space);
            nodes.push(token(TT::Arrow));
            nodes.push(HNode::Space);
            nodes.push(self.fmt_expr(ret_ty));
        }

        nodes.push(HNode::Space);
        nodes.push(self.fmt_block(body));
        nodes.push(HNode::AlwaysNewline);

        HNode::Sequence(nodes)
    }

    fn fmt_parameters<S: MaybeParameterSelf>(&self, params: &Parameters<S>) -> HNode {
        let Parameters { span: _, slf, items } = params;

        let first = slf.as_parameter_self().map(|slf| {
            let node = match slf.inner {
                ParameterSelfKind::Slf => token(TT::Slf),
            };
            (slf.span, HNodeAndComma { node, comma: true })
        });
        let ExtraList { span: _, items } = items;

        self.fmt_extra_list_items(SurroundKind::Round, false, first, items, &|p| {
            let node = self.fmt_parameter(p);
            HNodeAndComma { node, comma: true }
        })
    }

    fn fmt_parameter(&self, param: &Parameter) -> HNode {
        let &Parameter {
            span: _,
            id,
            ty,
            default,
        } = param;

        let mut seq = vec![self.fmt_id(id)];
        seq.push(wrapping_type(self.fmt_expr(ty)));
        if let Some(default) = default {
            seq.push(wrapping_assign(self.fmt_expr(default)));
        }
        HNode::Sequence(seq)
    }

    fn fmt_module_port_item(&self, item: &ModulePortItem) -> HNodeAndComma {
        match item {
            ModulePortItem::Single(single) => {
                let &ModulePortSingle { span: _, id, ref kind } = single;

                let node_kind = match kind {
                    ModulePortSingleKind::Port {
                        direction,
                        kind: kind_inner,
                    } => {
                        let node_kind_inner = match kind_inner {
                            PortSingleKindInner::Clock { span_clock: _ } => token(TT::Clock),
                            &PortSingleKindInner::Normal { domain, ty } => {
                                HNode::Sequence(vec![self.fmt_domain(domain.inner), HNode::Space, self.fmt_expr(ty)])
                            }
                        };
                        HNode::Sequence(vec![token(direction.inner.token()), HNode::Space, node_kind_inner])
                    }
                    &ModulePortSingleKind::Interface {
                        span_keyword: _,
                        domain,
                        interface,
                    } => HNode::Sequence(vec![
                        token(TT::Interface),
                        HNode::Space,
                        self.fmt_domain(domain.inner),
                        HNode::Space,
                        self.fmt_expr(interface),
                    ]),
                };

                let node = HNode::Sequence(vec![self.fmt_id(id), wrapping_type(node_kind)]);
                HNodeAndComma { node, comma: true }
            }
            ModulePortItem::DomainBlock(block) => {
                let ModulePortDomainBlock { span: _, domain, ports } = block;

                let node_domain = self.fmt_domain(domain.inner);

                let node_ports = self.fmt_extra_list_block(true, ports, &|port| {
                    let &ModulePortInBlock { span: _, id, kind } = port;
                    let node_kind = match kind {
                        ModulePortInBlockKind::Port { direction, ty } => {
                            HNode::Sequence(vec![token(direction.inner.token()), HNode::Space, self.fmt_expr(ty)])
                        }
                        ModulePortInBlockKind::Interface {
                            span_keyword: _,
                            interface,
                        } => HNode::Sequence(vec![token(TT::Interface), HNode::Space, self.fmt_expr(interface)]),
                    };
                    let node_port = HNode::Sequence(vec![self.fmt_id(id), wrapping_type(node_kind)]);
                    HNodeAndComma {
                        node: node_port,
                        comma: true,
                    }
                });

                let node = HNode::Sequence(vec![node_domain, HNode::Space, node_ports]);
                HNodeAndComma { node, comma: false }
            }
        }
    }

    fn fmt_block(&self, block: &Block<BlockStatement>) -> HNode {
        let Block { span: _, statements } = block;
        self.fmt_block_ext(statements, None)
    }

    fn fmt_block_ext(&self, statements: &[BlockStatement], final_expression: Option<Expression>) -> HNode {
        let node_final_expression = final_expression.map(|expr| self.fmt_expr(expr));
        let f = |stmt: &BlockStatement| skippable(stmt.span, self.fmt_block_statement(stmt));
        fmt_block_impl(statements, node_final_expression, f)
    }

    fn fmt_module_statement(&self, stmt: &ModuleStatement) -> HNode {
        match &stmt.inner {
            &ModuleStatementKind::ParseError(e) => self.report_parse_error(e),
            ModuleStatementKind::WireDeclaration(decl) => {
                let &WireDeclaration {
                    vis,
                    span_keyword: _,
                    id,
                    kind,
                } = decl;

                let mut seq = vec![];
                fmt_visibility(&mut seq, vis);

                seq.push(token(TT::Wire));
                seq.push(HNode::Space);
                seq.push(self.fmt_id(id));

                match kind {
                    WireDeclarationKind::Normal {
                        domain_ty,
                        assign_span_and_value,
                    } => {
                        let domain_ty_node = match domain_ty {
                            WireDeclarationDomainTyKind::Clock { span_clock: _ } => Some(token(TT::Clock)),
                            WireDeclarationDomainTyKind::Normal { domain, ty } => {
                                if domain.is_some() || ty.is_some() {
                                    let mut domain_ty_seq = vec![];
                                    if let Some(domain) = domain {
                                        domain_ty_seq.push(HNode::Space);
                                        domain_ty_seq.push(self.fmt_domain(domain.inner));
                                    }
                                    if let Some(ty) = ty {
                                        domain_ty_seq.push(HNode::Space);
                                        domain_ty_seq.push(self.fmt_expr(ty));
                                    }
                                    Some(HNode::Sequence(domain_ty_seq))
                                } else {
                                    None
                                }
                            }
                        };

                        if let Some(domain_ty_node) = domain_ty_node {
                            seq.push(wrapping_type(domain_ty_node));
                        }
                        if let Some((_span, value)) = assign_span_and_value {
                            seq.push(wrapping_assign(self.fmt_expr(value)));
                        }
                    }
                    WireDeclarationKind::Interface {
                        domain,
                        span_keyword: _,
                        interface,
                    } => {
                        let mut domain_interface_seq = vec![];
                        if let Some(domain) = domain {
                            domain_interface_seq.push(self.fmt_domain(domain.inner));
                            domain_interface_seq.push(HNode::Space);
                        }
                        domain_interface_seq.push(token(TT::Interface));
                        domain_interface_seq.push(HNode::Space);
                        domain_interface_seq.push(self.fmt_expr(interface));

                        seq.push(wrapping_type(HNode::Sequence(domain_interface_seq)))
                    }
                };

                seq.push(token(TT::Semi));
                seq.push(HNode::AlwaysNewline);
                HNode::Sequence(seq)
            }
            ModuleStatementKind::CombinatorialProcess(block) => {
                let CombinatorialProcess { span_keyword: _, block } = block;
                HNode::Sequence(vec![
                    token(TT::Comb),
                    HNode::Space,
                    self.fmt_block(block),
                    HNode::AlwaysNewline,
                ])
            }
            ModuleStatementKind::ClockedProcess(block) => {
                let &ClockedProcess {
                    span_keyword: _,
                    span_domain: _,
                    clock,
                    reset,
                    ref block,
                } = block;

                let args: &[_] = match reset {
                    None => &[Either::Left(clock)],
                    Some(reset) => &[Either::Left(clock), Either::Right(reset)],
                };
                let node_domain = fmt_call_like(token(TT::Clocked), args, |&arg| match arg {
                    Either::Left(clock) => self.fmt_expr(clock),
                    Either::Right(reset) => {
                        let ClockedProcessReset { kind, signal } = reset.inner;
                        HNode::Sequence(vec![token(kind.inner.token()), HNode::Space, self.fmt_expr(signal)])
                    }
                });

                HNode::Sequence(vec![
                    node_domain,
                    HNode::Space,
                    self.fmt_block(block),
                    HNode::AlwaysNewline,
                ])
            }
            ModuleStatementKind::Instance(instance) => {
                let &ModuleInstance {
                    name,
                    span_keyword: _,
                    module,
                    ref port_connections,
                } = instance;

                let mut seq = vec![token(TT::Instance)];
                if let Some(name) = name {
                    seq.push(HNode::Space);
                    seq.push(self.fmt_id(name));
                    seq.push(HNode::Space);
                    seq.push(token(TT::Eq));
                }

                seq.push(HNode::Space);
                seq.push(self.fmt_expr(module));

                seq.push(HNode::Space);
                seq.push(token(TT::Ports));

                let node_connections =
                    self.fmt_extra_list(SurroundKind::Round, false, &port_connections.inner, &|connection| {
                        // TODO if id and expression match, collapse them automatically
                        let &PortConnection { id, expr } = connection;

                        let node_id = self.fmt_id(id);
                        let node_connection = match expr {
                            PortConnectionExpression::FakeId(_) => node_id,
                            PortConnectionExpression::Real(expr) => {
                                HNode::Sequence(vec![node_id, token(TT::Eq), self.fmt_expr(expr)])
                            }
                        };

                        HNodeAndComma {
                            node: node_connection,
                            comma: true,
                        }
                    });
                seq.push(node_connections);

                seq.push(token(TT::Semi));
                seq.push(HNode::AlwaysNewline);
                HNode::Sequence(seq)
            }
            ModuleStatementKind::Connect(connect) => {
                let ConnectStatement {
                    span_keyword: _,
                    entries,
                } = connect;

                let node_entries = self.fmt_extra_list(SurroundKind::Round, false, entries, &|entry| {
                    let &ConnectEntry { span: _, expr, view } = entry;
                    let mut seq = vec![self.fmt_expr(expr)];
                    if let Some(view) = view {
                        let ConnectEntryView { span_keyword: _, id } = view;
                        seq.extend([HNode::Space, token(TT::View), HNode::Space, self.fmt_id(id)]);
                    }
                    HNodeAndComma {
                        node: HNode::Sequence(seq),
                        comma: true,
                    }
                });

                HNode::Sequence(vec![
                    token(TT::Connect),
                    node_entries,
                    token(TT::Semi),
                    HNode::AlwaysNewline,
                ])
            }
        }
    }

    fn fmt_block_statement(&self, stmt: &BlockStatement) -> HNode {
        match &stmt.inner {
            BlockStatementKind::CommonDeclaration(decl) => self.fmt_common_decl(decl),
            BlockStatementKind::VariableDeclaration(decl) => {
                let &VariableDeclaration {
                    span: _,
                    mutable,
                    id,
                    ty,
                    init,
                } = decl;
                let kind = if mutable { TT::Var } else { TT::Val };
                self.fmt_variable_decl(token(kind), self.fmt_id(id), ty, init)
            }
            BlockStatementKind::RegisterDeclaration(decl) => {
                let &RegisterDeclaration {
                    span_keyword: _,
                    kind,
                    reset,
                } = decl;

                let (kind, target, ty) = match kind {
                    RegisterDeclarationKind::Wire(kind) => {
                        let RegisterDeclarationWire {
                            span_keyword_wire: _,
                            target,
                        } = kind;
                        (
                            HNode::Sequence(vec![token(TT::Reg), HNode::Space, token(TT::Wire)]),
                            self.fmt_expr(target),
                            None,
                        )
                    }
                    RegisterDeclarationKind::New(kind) => {
                        let RegisterDeclarationNew { id, ty } = kind;
                        (token(TT::Reg), self.fmt_id(id), ty)
                    }
                };

                self.fmt_variable_decl(kind, target, ty, Some(reset))
            }
            BlockStatementKind::Assignment(stmt) => {
                let &Assignment {
                    span: _,
                    op,
                    target,
                    value,
                } = stmt;

                let op_token = op.inner.map_or(TT::Eq, AssignBinaryOp::token);
                HNode::Sequence(vec![
                    self.fmt_expr(target),
                    wrapping_assign_op(op_token, self.fmt_expr(value)),
                    token(TT::Semi),
                    HNode::AlwaysNewline,
                ])
            }
            &BlockStatementKind::Expression(expr) => {
                HNode::Sequence(vec![self.fmt_expr(expr), token(TT::Semi), HNode::AlwaysNewline])
            }
            BlockStatementKind::Block(block) => HNode::Sequence(vec![self.fmt_block(block), HNode::AlwaysNewline]),
            BlockStatementKind::If(stmt) => self.fmt_if(stmt, |block| self.fmt_block(block)),
            BlockStatementKind::Match(stmt) => self.fmt_match(stmt, |block| self.fmt_block(block)),
            BlockStatementKind::For(stmt) => self.fmt_for(stmt, |block| self.fmt_block(block)),
            BlockStatementKind::While(stmt) => self.fmt_while(stmt),
            BlockStatementKind::Return(stmt) => {
                let &ReturnStatement { span_return: _, value } = stmt;
                let mut seq = vec![token(TT::Return)];
                if let Some(value) = value {
                    seq.push(HNode::Space);
                    seq.push(self.fmt_expr(value));
                }
                seq.push(token(TT::Semi));
                seq.push(HNode::AlwaysNewline);
                HNode::Sequence(seq)
            }
            BlockStatementKind::Break { span: _ } => {
                HNode::Sequence(vec![token(TT::Break), token(TT::Semi), HNode::AlwaysNewline])
            }
            BlockStatementKind::Continue { span: _ } => {
                HNode::Sequence(vec![token(TT::Continue), token(TT::Semi), HNode::AlwaysNewline])
            }
        }
    }

    fn fmt_variable_decl(&self, kind: HNode, id: HNode, ty: Option<Expression>, value: Option<Expression>) -> HNode {
        let mut seq = vec![];
        seq.push(kind);
        seq.push(HNode::Space);
        seq.push(id);
        if let Some(ty) = ty {
            seq.push(wrapping_type(self.fmt_expr(ty)));
        }
        if let Some(value) = value {
            seq.push(wrapping_assign(self.fmt_expr(value)));
        }
        seq.push(token(TT::Semi));
        seq.push(HNode::AlwaysNewline);
        HNode::Sequence(seq)
    }

    fn fmt_if<B>(&self, stmt: &IfStatement<B>, mut f: impl FnMut(&B) -> HNode) -> HNode {
        fn fmt_else(seq: &mut Vec<HNode>) {
            seq.push(HNode::Space);
            seq.push(token(TT::Else));
            seq.push(HNode::Space);
        }

        fn fmt_pair<B>(slf: &Context, mut f: impl FnMut(&B) -> HNode, seq: &mut Vec<HNode>, pair: &IfCondBlockPair<B>) {
            let &IfCondBlockPair {
                span: _,
                span_if: _,
                cond,
                ref block,
            } = pair;
            seq.push(token(TT::If));
            seq.push(HNode::Space);
            seq.push(surrounded_group_indent(SurroundKind::Round, slf.fmt_expr(cond)));
            seq.push(HNode::Space);
            seq.push(f(block));
        }

        let IfStatement {
            span: _,
            initial_if,
            else_ifs,
            final_else,
        } = stmt;

        let mut seq = vec![];
        fmt_pair(self, &mut f, &mut seq, initial_if);
        for else_if in else_ifs {
            fmt_else(&mut seq);
            fmt_pair(self, &mut f, &mut seq, else_if);
        }
        if let Some(final_else) = final_else {
            fmt_else(&mut seq);
            seq.push(f(final_else));
        }

        seq.push(HNode::AlwaysNewline);
        HNode::Sequence(seq)
    }

    fn fmt_match<B>(&self, stmt: &MatchStatement<B>, f: impl Fn(&B) -> HNode) -> HNode {
        let &MatchStatement {
            span_keyword: _,
            target,
            pos_end: _,
            ref branches,
        } = stmt;

        let mut seq_branches = vec![];

        if !branches.is_empty() {
            seq_branches.push(HNode::PreserveBlankLines(PreserveKind::AfterComment));
        }

        for (branch, last) in branches.iter().with_last() {
            let MatchBranch { pattern, block } = branch;

            let pattern_node = match pattern.inner {
                MatchPattern::Wildcard => token(TT::Underscore),
                MatchPattern::WildcardVal(id) => HNode::Sequence(vec![token(TT::Val), HNode::Space, self.fmt_id(id)]),
                MatchPattern::EqualTo(value) => self.fmt_expr(value),
                MatchPattern::InRange { span_in: _, range } => {
                    HNode::Sequence(vec![token(TT::In), HNode::Space, self.fmt_expr(range)])
                }
                MatchPattern::IsEnumVariant {
                    variant,
                    payload_id: payload,
                } => {
                    let node_variant = HNode::Sequence(vec![token(TT::Dot), self.fmt_id(variant)]);
                    match payload {
                        None => node_variant,
                        Some(payload) => {
                            let node_payload = match payload {
                                MaybeIdentifier::Dummy { span: _ } => token(TT::Underscore),
                                MaybeIdentifier::Identifier(id) => {
                                    HNode::Sequence(vec![token(TT::Val), HNode::Space, self.fmt_id(id)])
                                }
                            };
                            HNode::Sequence(vec![
                                node_variant,
                                surrounded_group_indent(SurroundKind::Round, node_payload),
                            ])
                        }
                    }
                }
            };

            seq_branches.push(pattern_node);
            seq_branches.push(HNode::Space);
            seq_branches.push(token(TT::DoubleArrow));
            seq_branches.push(HNode::Space);
            seq_branches.push(f(block));
            seq_branches.push(HNode::AlwaysNewline);
            seq_branches.push(preserve_blank_lines_after_item(last));
        }

        HNode::Sequence(vec![
            token(TT::Match),
            HNode::Space,
            surrounded_group_indent(SurroundKind::Round, self.fmt_expr(target)),
            HNode::Space,
            surrounded_group_indent(SurroundKind::Curly, HNode::Sequence(seq_branches)),
            HNode::AlwaysNewline,
        ])
    }

    fn fmt_for<B>(&self, stmt: &ForStatement<B>, f: impl Fn(&B) -> HNode) -> HNode {
        let &ForStatement {
            span_keyword: _,
            index,
            index_ty,
            iter,
            ref body,
        } = stmt;

        let mut seq = vec![self.fmt_id(index)];
        if let Some(index_ty) = index_ty {
            seq.push(wrapping_type(self.fmt_expr(index_ty)));
        }

        seq.push(group_indent_seq(vec![
            HNode::WrapNewline,
            HNode::Space,
            token(TT::In),
            HNode::Space,
            self.fmt_expr(iter),
        ]));

        HNode::Sequence(vec![
            token(TT::For),
            HNode::Space,
            surrounded_group_indent(SurroundKind::Round, HNode::Sequence(seq)),
            HNode::Space,
            f(body),
            HNode::AlwaysNewline,
        ])
    }

    fn fmt_while(&self, stmt: &WhileStatement) -> HNode {
        let &WhileStatement {
            span_keyword: _,
            cond,
            ref body,
        } = stmt;

        HNode::Sequence(vec![
            token(TT::While),
            HNode::Space,
            surrounded_group_indent(SurroundKind::Round, self.fmt_expr(cond)),
            HNode::Space,
            self.fmt_block(body),
            HNode::AlwaysNewline,
        ])
    }

    fn fmt_domain(&self, domain: DomainKind<Expression>) -> HNode {
        match domain {
            DomainKind::Const => token(TT::Const),
            DomainKind::Async => token(TT::Async),
            DomainKind::Sync(domain) => {
                let SyncDomain { clock, reset } = domain;
                let args: &[_] = match reset {
                    None => &[Either::Left(clock)],
                    Some(reset) => &[Either::Left(clock), Either::Right(reset)],
                };
                fmt_call_like(token(TT::Sync), args, |&arg| match arg {
                    Either::Left(clock) => self.fmt_expr(clock),
                    Either::Right(reset) => HNode::Sequence(vec![token(TT::Async), HNode::Space, self.fmt_expr(reset)]),
                })
            }
        }
    }

    fn fmt_expr(&self, expr: Expression) -> HNode {
        skippable(expr.span, self.fmt_expr_inner(expr))
    }

    fn fmt_expr_inner(&self, expr: Expression) -> HNode {
        match &self.arena_expressions[expr.inner] {
            &ExpressionKind::ParseError(e) => self.report_parse_error(e),
            ExpressionKind::Dummy => token(TT::Underscore),
            ExpressionKind::Undefined => token(TT::Undef),
            ExpressionKind::Type => token(TT::Type),
            ExpressionKind::Slf => token(TT::Slf),
            ExpressionKind::Builtin { span_keyword: _, args } => {
                fmt_call_like(token(TT::Builtin), &args.inner, |&arg| self.fmt_expr(arg))
            }
            &ExpressionKind::Wrapped(inner) => surrounded_group_indent(SurroundKind::Round, self.fmt_expr(inner)),
            ExpressionKind::Block(expr) => {
                let &BlockExpression {
                    ref statements,
                    expression,
                } = expr;
                self.fmt_block_ext(statements, Some(expression))
            }
            &ExpressionKind::Id(id) => self.fmt_id(id),
            ExpressionKind::IntLiteral(literal) => {
                let tt = match literal {
                    IntLiteral::Binary { span: _ } => TT::IntLiteralBinary,
                    IntLiteral::Decimal { span: _ } => TT::IntLiteralDecimal,
                    IntLiteral::Hexadecimal { span: _ } => TT::IntLiteralHexadecimal,
                };
                token(tt)
            }
            &ExpressionKind::BoolLiteral(value) => {
                let tt = if value { TT::True } else { TT::False };
                token(tt)
            }
            ExpressionKind::StringLiteral(pieces) => {
                // dedent all nodes that could follow StringMiddle to avoid any indentation sneaking into the string
                let mut seq = vec![token(TT::StringStart)];
                for piece in pieces {
                    match piece {
                        StringPiece::Literal(_span) => {
                            seq.push(HNode::Dedent(Box::new(token(TT::StringMiddle))));
                        }
                        &StringPiece::Substitute(expr) => {
                            seq.push(group_seq(vec![
                                HNode::Dedent(Box::new(token(TT::StringSubStart))),
                                HNode::WrapNewline,
                                HNode::Indent(Box::new(self.fmt_expr(expr))),
                                HNode::WrapNewline,
                                token(TT::StringSubEnd),
                            ]));
                        }
                    }
                }
                seq.push(HNode::Dedent(Box::new(token(TT::StringEnd))));
                HNode::Sequence(seq)
            }
            ExpressionKind::ArrayLiteral(elements) => fmt_comma_list(SurroundKind::Square, elements, |&elem| {
                self.fmt_array_literal_element(elem)
            }),
            ExpressionKind::TupleLiteral(elements) => {
                match elements.as_slice() {
                    // don't allow breaking for empty tuple
                    [] => HNode::Sequence(vec![token(TT::OpenR), token(TT::CloseR)]),
                    // force trailing comma for single-element tuple
                    &[element] => surrounded_group_indent(
                        SurroundKind::Round,
                        HNode::Sequence(vec![self.fmt_expr(element), token(TT::Comma)]),
                    ),
                    // general case
                    elements => fmt_comma_list(SurroundKind::Round, elements, |&elem| self.fmt_expr(elem)),
                }
            }
            &ExpressionKind::RangeLiteral(expr) => match expr {
                RangeLiteral::ExclusiveEnd { op_span: _, start, end } => wrapping_binary_op(
                    token(TT::DotDot),
                    start.map(|e| self.fmt_expr(e)),
                    end.map(|e| self.fmt_expr(e)),
                ),
                RangeLiteral::InclusiveEnd {
                    op_span: _,
                    start,
                    end_inc,
                } => wrapping_binary_op(
                    token(TT::DotDotEq),
                    start.map(|e| self.fmt_expr(e)),
                    Some(self.fmt_expr(end_inc)),
                ),
                RangeLiteral::Length {
                    op_span: _,
                    start,
                    length: len,
                } => wrapping_binary_op(
                    token(TT::PlusDotDot),
                    Some(self.fmt_expr(start)),
                    Some(self.fmt_expr(len)),
                ),
            },
            ExpressionKind::ArrayComprehension(expr) => {
                let &ArrayComprehension {
                    body,
                    index,
                    span_keyword: _,
                    iter,
                } = expr;

                let seq = vec![
                    self.fmt_array_literal_element(body),
                    HNode::WrapNewline,
                    HNode::Space,
                    token(TT::For),
                    HNode::Space,
                    self.fmt_id(index),
                    HNode::Space,
                    token(TT::In),
                    HNode::Space,
                    self.fmt_expr(iter),
                ];

                surrounded_group_indent(SurroundKind::Square, HNode::Sequence(seq))
            }
            &ExpressionKind::UnaryOp(op, inner) => HNode::Sequence(vec![token(op.inner.token()), self.fmt_expr(inner)]),
            &ExpressionKind::BinaryOp(op, _, _) => {
                let mut seq = vec![];
                let leftmost = self.collect_binary_expr::<LeftmostYes>(&mut seq, op.inner.level(), expr);
                binary_indent_seq(leftmost, seq)
            }
            &ExpressionKind::ArrayType {
                span_brackets: _,
                ref lengths,
                element,
            } => {
                let node_lengths = fmt_comma_list(SurroundKind::Square, lengths, |&len| {
                    self.fmt_array_literal_element(len)
                });
                HNode::Sequence(vec![node_lengths, self.fmt_expr(element)])
            }
            &ExpressionKind::ArrayIndex {
                span_brackets: _,
                base,
                ref indices,
            } => {
                let node_indices = fmt_comma_list(SurroundKind::Square, indices, |&index| {
                    self.fmt_array_literal_element(index)
                });
                HNode::Sequence(vec![self.fmt_expr(base), node_indices])
            }
            ExpressionKind::DotIndex(_, _) => {
                // repeated dot indices should wrap together
                let mut base = expr;
                let mut indices_rev = vec![];
                while let &ExpressionKind::DotIndex(curr_base, curr_index) = &self.arena_expressions[base.inner] {
                    base = curr_base;
                    indices_rev.push(curr_index);
                }

                let node_base = self.fmt_expr(base);

                let mut seq = vec![];
                for (index, last) in indices_rev.into_iter().rev().with_last() {
                    let node_index = match index {
                        DotIndexKind::Id(id) => self.fmt_id(id),
                        DotIndexKind::Int { span: _ } => token(TT::IntLiteralDecimal),
                    };

                    seq.push(token(TT::Dot));
                    seq.push(node_index);

                    if !last {
                        seq.push(HNode::WrapNewline);
                    }
                }
                let node_indices = HNode::Sequence(seq);

                wrapping_binary_op(HNode::EMPTY, Some(node_base), Some(node_indices))
            }
            &ExpressionKind::Call(target, ref args) => {
                let node_target = self.fmt_expr(target);

                let node_args = self.fmt_extra_list(SurroundKind::Round, false, args, &|arg| {
                    let &Arg { span: _, id, value } = arg;
                    let node_value = self.fmt_expr(value);
                    let node_arg = if let Some(id) = id {
                        // TODO allow wrapping before/after "="?
                        HNode::Sequence(vec![self.fmt_id(id), token(TT::Eq), node_value])
                    } else {
                        node_value
                    };
                    HNodeAndComma {
                        node: node_arg,
                        comma: true,
                    }
                });

                HNode::Sequence(vec![node_target, node_args])
            }
            &ExpressionKind::UnsafeValueWithDomain(value, domain) => fmt_call_like(
                token(TT::UnsafeValueWithDomain),
                &[Either::Left(value), Either::Right(domain)],
                |&either| match either {
                    Either::Left(value) => self.fmt_expr(value),
                    Either::Right(domain) => self.fmt_domain(domain.inner),
                },
            ),
            &ExpressionKind::Ref(_span, inner) => {
                fmt_call_like(token(TT::Ref), &[inner], |&inner| self.fmt_expr(inner))
            }
            &ExpressionKind::Deref(_span, inner) => {
                fmt_call_like(token(TT::Deref), &[inner], |&inner| self.fmt_expr(inner))
            }
        }
    }

    fn collect_binary_expr<L: LeftmostMaybe>(
        &self,
        seq: &mut Vec<HNode>,
        level: BinaryOpLevel,
        expr: Expression,
    ) -> L::R {
        if let &ExpressionKind::BinaryOp(op, left, right) = &self.arena_expressions[expr.inner]
            && op.inner.level() == level
        {
            let leftmost = self.collect_binary_expr::<L>(seq, level, left);

            seq.push(HNode::WrapNewline);
            let op_node = token(op.inner.token());
            match op.inner {
                BinaryOp::Pow => {
                    // TODO should this really be the one edge case?
                    seq.push(op_node);
                }
                _ => {
                    seq.push(HNode::Space);
                    seq.push(op_node);
                    seq.push(HNode::Space);
                }
            };

            self.collect_binary_expr::<LeftmostNo>(seq, level, right);

            leftmost
        } else {
            let expr_node = self.fmt_expr(expr);
            L::push_or_return(seq, expr_node)
        }
    }

    fn fmt_array_literal_element(&self, elem: ArrayLiteralElement<Expression>) -> HNode {
        match elem {
            ArrayLiteralElement::Single(elem) => self.fmt_expr(elem),
            ArrayLiteralElement::Spread(_span, elem) => HNode::Sequence(vec![token(TT::Star), self.fmt_expr(elem)]),
        }
    }

    fn fmt_id(&self, id: impl Into<MaybeIdentifier>) -> HNode {
        match id.into() {
            MaybeIdentifier::Dummy { span: _ } => token(TT::Underscore),
            MaybeIdentifier::Identifier(id) => match id {
                Identifier::Simple(_id) => token(TT::Identifier),
                Identifier::FromString(_span, expr) => {
                    fmt_call_like(token(TT::Ident), &[expr], |&expr| self.fmt_expr(expr))
                }
            },
        }
    }
}

fn skippable(span: Span, node: HNode) -> HNode {
    HNode::Skippable(span, Box::new(node))
}

fn fmt_block_impl<T>(statements: &[T], final_expression: Option<HNode>, f: impl Fn(&T) -> HNode) -> HNode {
    let mut seq = vec![];

    if !statements.is_empty() || final_expression.is_some() {
        seq.push(HNode::PreserveBlankLines(PreserveKind::AfterComment));
    }

    for (stmt, last_stmt) in statements.iter().with_last() {
        seq.push(f(stmt));
        seq.push(preserve_blank_lines_after_item(last_stmt && final_expression.is_none()));
    }

    if let Some(final_expression) = final_expression {
        seq.push(HNode::Space);
        seq.push(final_expression);
        seq.push(HNode::WrapNewline);
        seq.push(HNode::PreserveBlankLines(PreserveKind::BeforeComment));
        seq.push(HNode::Space);
    }

    surrounded_group_indent(SurroundKind::Curly, HNode::Sequence(seq))
}

fn fmt_call_like<T>(target: HNode, args: &[T], f: impl Fn(&T) -> HNode) -> HNode {
    HNode::Sequence(vec![target, fmt_comma_list(SurroundKind::Round, args, f)])
}

fn fmt_comma_list<T>(surround: SurroundKind, items: &[T], f: impl Fn(&T) -> HNode) -> HNode {
    let mut seq = vec![];

    if !items.is_empty() {
        seq.push(HNode::PreserveBlankLines(PreserveKind::AfterComment));
    }

    for (item, last) in items.iter().with_last() {
        seq.push(f(item));
        seq.push(comma_nodes(last));
        seq.push(HNode::WrapNewline);
        seq.push(preserve_blank_lines_after_item(last));
    }

    surrounded_group_indent(surround, HNode::Sequence(seq))
}

fn fmt_visibility<V: MaybeVisibility>(seq: &mut Vec<HNode>, v: V) {
    if let Some(vis) = v.as_visibility() {
        match vis {
            Visibility::Public { span: _ } => {
                seq.push(token(TT::Pub));
                seq.push(HNode::Space);
            }
            Visibility::Private => {
                // emit nothing, private is the default
            }
        }
    }
}

fn preserve_blank_lines_after_item(last: bool) -> HNode {
    if !last {
        HNode::PreserveBlankLines(PreserveKind::Always)
    } else {
        HNode::PreserveBlankLines(PreserveKind::BeforeComment)
    }
}

fn comma_nodes(last: bool) -> HNode {
    if !last {
        HNode::Sequence(vec![token(TT::Comma), HNode::Space])
    } else {
        HNode::WrapComma
    }
}

fn wrapping_type(ty: HNode) -> HNode {
    HNode::Sequence(vec![
        group_indent_seq(vec![HNode::WrapNewline, token(TT::Colon), HNode::Space]),
        ty,
    ])
}

fn wrapping_assign(value: HNode) -> HNode {
    wrapping_assign_op(TT::Eq, value)
}

fn wrapping_assign_op(op: TT, value: HNode) -> HNode {
    HNode::Sequence(vec![
        group_indent_seq(vec![HNode::WrapNewline, HNode::Space, token(op), HNode::Space]),
        value,
    ])
}

fn wrapping_binary_op(op: HNode, left: Option<HNode>, right: Option<HNode>) -> HNode {
    match (left, right) {
        (Some(left), Some(right)) => {
            // both left and right hand side, provide some wrapping opportunities
            binary_indent_seq(left, vec![HNode::WrapNewline, op, right])
        }
        (left, right) => {
            // only an operator and one side, just flatten to a sequence without wrapping
            let mut seq = vec![];
            if let Some(left) = left {
                seq.push(left);
            }
            seq.push(op);
            if let Some(right) = right {
                seq.push(right);
            }
            HNode::Sequence(seq)
        }
    }
}

fn group_seq(nodes: Vec<HNode>) -> HNode {
    HNode::Group(Box::new(HNode::Sequence(nodes)))
}

fn group_indent_seq(nodes: Vec<HNode>) -> HNode {
    HNode::Group(Box::new(HNode::Indent(Box::new(HNode::Sequence(nodes)))))
}

fn binary_indent_seq(leftmost: HNode, rest: Vec<HNode>) -> HNode {
    group_seq(vec![leftmost, HNode::Indent(Box::new(HNode::Sequence(rest)))])
}

fn surrounded_group_indent(surround: SurroundKind, inner: HNode) -> HNode {
    let (before, after) = surround.before_after();
    group_seq(vec![
        before,
        HNode::WrapNewline,
        HNode::Indent(Box::new(inner)),
        HNode::WrapNewline,
        after,
    ])
}

fn token(tt: TT) -> HNode {
    HNode::AlwaysToken(tt)
}

enum SurroundKind {
    Round,
    Square,
    Curly,
    CurlySpace,
}

impl SurroundKind {
    pub fn before_after(self) -> (HNode, HNode) {
        match self {
            SurroundKind::Round => (token(TT::OpenR), token(TT::CloseR)),
            SurroundKind::Square => (token(TT::OpenS), token(TT::CloseS)),
            SurroundKind::Curly => (token(TT::OpenC), token(TT::CloseC)),
            SurroundKind::CurlySpace => (
                HNode::Sequence(vec![token(TT::OpenC), HNode::Space]),
                HNode::Sequence(vec![HNode::Space, token(TT::CloseC)]),
            ),
        }
    }
}

struct HNodeAndComma {
    node: HNode,
    comma: bool,
}

trait LeftmostMaybe {
    type R;
    fn push_or_return(seq: &mut Vec<HNode>, v: HNode) -> Self::R;
}

struct LeftmostYes;
struct LeftmostNo;
impl LeftmostMaybe for LeftmostYes {
    type R = HNode;
    fn push_or_return(_: &mut Vec<HNode>, v: HNode) -> Self::R {
        v
    }
}
impl LeftmostMaybe for LeftmostNo {
    type R = ();
    fn push_or_return(seq: &mut Vec<HNode>, v: HNode) -> Self::R {
        seq.push(v);
    }
}
