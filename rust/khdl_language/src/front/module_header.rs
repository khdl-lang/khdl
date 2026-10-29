use crate::front::compile::{ArenaPortInterfaces, ArenaPorts, CompileItemContext, CompileRefs};
use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::front::domain::PortDomain;
use crate::front::expression::LeftInterfaceInfo;
use crate::front::extra::ExtraScope;
use crate::front::flow::{FlowCompile, FlowCompileContent, FlowRoot, FlowRootContent};
use crate::front::item::{ElaboratedInterfaceView, ElaboratedItemParams, ElaboratedModule, UniqueDeclaration};
use crate::front::scope::{FrozenScope, NamedValue, Scope, ScopeContent, ScopedEntry};
use crate::front::signal::{Interface, Polarized, Port, PortInfo, PortInterfaceInfo, Signal};
use crate::front::string::shape_string;
use crate::front::types::{HardwareType, Type, Typed};
use crate::front::value::{CompileValue, SimpleCompileValue};
use crate::mid::ir::{IrModule, IrPort, IrPortDeclared, IrPortInfo, IrPorts};
use crate::new_index_type;
use crate::syntax::ast::{
    DomainKind, Expression, ExtraList, ModulePortDomainBlock, ModulePortInBlock, ModulePortInBlockKind, ModulePortItem,
    ModulePortSingle, ModulePortSingleKind, PortDirection, PortSingleKindInner,
};
use crate::syntax::parsed::{AstRefItemKind, AstRefModuleExternal, AstRefModuleInternal};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::arena::Arena;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::data::NonEmptyVec;
use crate::util::intern::Id;
use crate::util::nd_array::{NdArray, try_for_each_nd_index};
use crate::util::{ResultExt, result_pair, result_pair_split};
use indexmap::IndexMap;
use itertools::{Either, Itertools, enumerate};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;

new_index_type!(pub Connector);

pub type ArenaConnectors = Arena<Connector, ConnectorInfo>;

pub struct ModuleConnectors {
    pub arena: ArenaConnectors,
    pub id_to_connector: IndexMap<Id, Connector>,
}

pub struct ConnectorInfo {
    pub id: Spanned<Id>,
    pub kind: DiagResult<ConnectorKind>,
}

pub enum ConnectorKind {
    Port {
        direction: Spanned<PortDirection>,
        domain: Spanned<PortDomain<ConnectorSingle>>,
        ty: Spanned<HardwareType>,
        single: ConnectorSingle,
    },
    Interface {
        domain: Spanned<DomainKind<Polarized<ConnectorSingle>>>,
        view: Spanned<ElaboratedInterfaceView>,
        singles: NdArray<Vec<ConnectorSingle>>,
    },
}

impl ConnectorKind {
    pub fn singles(&self) -> impl Iterator<Item = ConnectorSingle> {
        match self {
            &ConnectorKind::Port { single, .. } => Either::Left(std::iter::once(single)),
            ConnectorKind::Interface { singles, .. } => Either::Right(singles.flat_values().iter().flatten().copied()),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ConnectorSingle(usize);

#[derive(Debug)]
pub struct ElaboratedModuleHeader<A> {
    pub ast_ref: A,
    pub elab_module: ElaboratedModule,
    pub unique: UniqueDeclaration,
    pub debug_info_params: Option<Vec<(String, String)>>,

    pub ports: ArenaPorts,
    pub port_interfaces: ArenaPortInterfaces,
    pub ir_ports: IrPorts,
    pub ir_ports_named: IndexMap<String, IrPort>,
    pub ir_ports_declared: IndexMap<String, IrPortDeclared>,

    pub scope_params: Arc<FrozenScope>,
    pub scope_ports: ScopeContent,
    pub flow_root: FlowRootContent,
    pub flow: FlowCompileContent,
}

pub struct ElaboratedModuleInternalInfo {
    pub ast_ref: AstRefModuleInternal,
    pub unique: UniqueDeclaration,

    pub module_ir: IrModule,
    pub connectors: ModuleConnectors,
}

pub struct ElaboratedModuleExternalInfo {
    pub ast_ref: AstRefModuleExternal,
    pub module_name: String,
    pub generic_args: Option<Vec<(String, BigInt)>>,
    pub ports: Vec<(String, HardwareType)>,
    pub connectors: ModuleConnectors,
}

impl CompileRefs<'_, '_> {
    pub fn elaborate_module_ports_new<A: AstRefItemKind>(
        self,
        ast_ref: A,
        def_span: Span,
        elab_module: ElaboratedModule,
        params: ElaboratedItemParams,
        scope_params: Arc<FrozenScope>,
        ports: &Spanned<ExtraList<ModulePortItem>>,
    ) -> DiagResult<(ModuleConnectors, ElaboratedModuleHeader<A>)> {
        let ElaboratedItemParams {
            unique,
            params: debug_info_params,
        } = params;

        // reconstruct header scope
        let mut ctx = CompileItemContext::new_empty(self, None, Some(elab_module));
        let flow_root = FlowRoot::new(self.diags, &self.shared.next_flow_root_id);
        let mut flow = FlowCompile::new_root(&flow_root, def_span, "item declaration");

        // elaborate ports
        let scope_params_tmp = &Arc::clone(&scope_params).as_scope();
        let (connectors, scope_ports, ir_ports, ir_ports_named, ir_ports_declared) =
            self.elaborate_module_ports_impl(&mut ctx, scope_params_tmp, &mut flow, ports, def_span)?;

        // create params debug info string
        let debug_info_params = debug_info_params.map(|p| {
            p.into_iter()
                .map(|(k, v)| (k.inner.str(&self.shared.interner).to_owned(), v.value_string(self)))
                .collect_vec()
        });

        // save scope and flow
        //   the body will be elaborated with different diagnostics, so diag ids can't be kept
        let scope_ports = scope_ports.into_content(false);
        let flow = flow.into_content();

        // collect results
        let header = ElaboratedModuleHeader {
            elab_module,
            ast_ref,
            unique,
            debug_info_params,
            ports: ctx.ports,
            port_interfaces: ctx.port_interfaces,
            ir_ports,
            ir_ports_named,
            ir_ports_declared,

            scope_params,
            scope_ports,
            flow_root: flow_root.into_content(),
            flow,
        };
        let id_to_connector = connectors
            .into_iter()
            .map(|(connector, info)| (info.id.inner, connector))
            .collect();
        let connectors = ModuleConnectors {
            arena: connectors,
            id_to_connector,
        };

        Ok((connectors, header))
    }

    fn elaborate_module_ports_impl<'p>(
        &self,
        ctx: &mut CompileItemContext,
        scope_params: &'p Scope<'p>,
        flow: &mut FlowCompile,
        ports: &Spanned<ExtraList<ModulePortItem>>,
        module_def_span: Span,
    ) -> DiagResult<(
        ArenaConnectors,
        Scope<'p>,
        IrPorts,
        IndexMap<String, IrPort>,
        IndexMap<String, IrPortDeclared>,
    )> {
        let diags = self.diags;

        // build context
        let mut connectors: ArenaConnectors = Arena::new();
        let mut ir_ports = Arena::new();
        let mut ir_ports_declared = IndexMap::new();
        let mut ctx_ports = ModulePortsContext {
            connectors: &mut connectors,
            ir_ports: &mut ir_ports,
            ir_ports_declared: &mut ir_ports_declared,
            any_err: Ok(()),
            port_to_single: IndexMap::new(),
            ir_ports_names_used: IndexMap::new(),
            next_single_index: 0,
        };

        // visit port extra list
        let mut scope_ports = scope_params.new_child(ports.span.join(Span::empty_at(module_def_span.end())));
        ctx.elaborate_extra_list(
            &mut scope_ports,
            flow,
            &ports.inner,
            true,
            &mut |ctx, scope, flow, port_item| ctx_ports.visit_port_item(ctx, scope, flow, port_item),
        )?;

        // stop elaboration if any port or name errors happened
        ctx_ports.any_err?;
        scope_ports.any_declare_key_error()?;
        ctx_ports.check_unique_ir_port_names(diags)?;

        // we've checked that port names are unique, create the mapping that proves that
        let mut ir_ports_named = IndexMap::new();
        for (port, port_info) in &ir_ports {
            let prev = ir_ports_named.insert(port_info.name.clone(), port);
            if prev.is_some() {
                return Err(diags.report_error_internal(module_def_span, "duplicate ir port name"));
            }
        }

        Ok((connectors, scope_ports, ir_ports, ir_ports_named, ir_ports_declared))
    }
}

pub struct ModulePortsContext<'a> {
    // results
    connectors: &'a mut ArenaConnectors,
    ir_ports: &'a mut IrPorts,
    ir_ports_declared: &'a mut IndexMap<String, IrPortDeclared>,
    any_err: DiagResult,

    // intermediate state
    port_to_single: IndexMap<Port, ConnectorSingle>,
    ir_ports_names_used: IndexMap<String, Vec<(Span, bool)>>,
    next_single_index: usize,
}

impl ModulePortsContext<'_> {
    fn visit_port_item(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &mut ExtraScope,
        flow: &mut FlowCompile,
        port_item: &ModulePortItem,
    ) -> DiagResult<()> {
        let refs = ctx.refs;

        match port_item {
            ModulePortItem::Single(port_item) => {
                let &ModulePortSingle { span: _, id, ref kind } = port_item;

                // eval id
                let id = ctx.eval_id(scope.as_scope(), flow, id)?;

                match *kind {
                    ModulePortSingleKind::Port { direction, ref kind } => {
                        // eval domain and type
                        let (domain, ty) = match *kind {
                            PortSingleKindInner::Clock { span_clock } => (
                                Ok(Spanned::new(span_clock, PortDomain::Clock)),
                                Ok(Spanned::new(span_clock, HardwareType::Bool)),
                            ),
                            PortSingleKindInner::Normal { domain, ty } => (
                                ctx.eval_port_domain(scope.as_scope(), flow, domain)
                                    .map(|d| d.map_inner(PortDomain::Kind)),
                                ctx.eval_expression_as_ty_hardware(scope.as_scope(), flow, ty, "port"),
                            ),
                        };

                        // record
                        let entry = self.push_connector_single(ctx, id, direction, domain, ty);
                        self.report_any_err(&entry);
                        scope.declare_root(refs, id, entry);
                    }
                    ModulePortSingleKind::Interface {
                        span_keyword,
                        domain,
                        interface,
                    } => {
                        // eval domain
                        let domain = ctx.eval_port_domain(scope.as_scope(), flow, domain);

                        // eval interface view
                        let interface_view = eval_port_interface_view(ctx, scope, flow, span_keyword, interface);

                        // record
                        let entry = self.push_connector_interface(ctx, id, domain, interface_view);
                        self.report_any_err(&entry);
                        scope.declare_root(refs, id, entry);
                    }
                }
            }
            ModulePortItem::DomainBlock(port_item) => {
                let &ModulePortDomainBlock {
                    span: _,
                    domain,
                    ref ports,
                } = port_item;

                // eval domain (shared between all inner ports)
                let domain = ctx.eval_port_domain(scope.as_scope(), flow, domain);

                // visit inner ports
                ctx.elaborate_extra_list_block(
                    scope,
                    flow,
                    ports,
                    true,
                    &mut |ctx, scope, flow, port_item_in_block| {
                        self.visit_port_item_in_block(ctx, scope, flow, domain, port_item_in_block)?;
                        Ok(())
                    },
                )?;
            }
        }

        Ok(())
    }

    fn visit_port_item_in_block(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &mut ExtraScope,
        flow: &mut FlowCompile,
        domain: DiagResult<Spanned<DomainKind<Polarized<Port>>>>,
        port_item_in_block: &ModulePortInBlock,
    ) -> DiagResult<()> {
        let refs = ctx.refs;

        let &ModulePortInBlock { span: _, id, ref kind } = port_item_in_block;

        // eval id
        let id = ctx.eval_id(scope.as_scope(), flow, id)?;

        match *kind {
            ModulePortInBlockKind::Port { direction, ty } => {
                // map domain
                let domain = domain.map(|d| d.map_inner(PortDomain::Kind));

                // eval type
                let ty = ctx.eval_expression_as_ty_hardware(scope.as_scope(), flow, ty, "port");

                // record
                let entry = self.push_connector_single(ctx, id, direction, domain, ty);
                self.report_any_err(&entry);
                scope.declare_root(refs, id, entry);
            }
            ModulePortInBlockKind::Interface {
                span_keyword,
                interface,
            } => {
                // eval interface view
                let interface_view = eval_port_interface_view(ctx, scope, flow, span_keyword, interface);

                // record
                let entry = self.push_connector_interface(ctx, id, domain, interface_view);
                self.report_any_err(&entry);
                scope.declare_root(refs, id, entry);
            }
        }

        Ok(())
    }

    fn push_connector_single(
        &mut self,
        ctx: &mut CompileItemContext,
        id: Spanned<Id>,
        direction: Spanned<PortDirection>,
        domain: DiagResult<Spanned<PortDomain<Port>>>,
        ty: DiagResult<Spanned<HardwareType>>,
    ) -> DiagResult<ScopedEntry> {
        let id_str = id.inner.str(&ctx.refs.shared.interner);
        self.record_ir_port_name(id_str.to_owned(), id.span(), false);

        let kind_and_entry = result_pair(domain, ty).map(|(domain, ty)| {
            let ir_port_info = IrPortInfo {
                name: id_str.to_owned(),
                direction: direction.inner,
                ty: ty.inner.as_ir(ctx.refs),
                debug_span: id.span(),
                debug_info_ty: ty.as_ref().map_inner(|inner| inner.value_string(ctx.refs)),
                debug_info_domain: domain.inner.diagnostic_string(ctx),
            };
            let ir_port = self.ir_ports.push(ir_port_info);
            self.ir_ports_declared
                .insert(id_str.to_owned(), IrPortDeclared::Single(ir_port));

            let port = ctx.ports.push(PortInfo {
                span: id.span(),
                name: id.inner.str(&ctx.refs.shared.interner).to_owned(),
                direction,
                domain,
                ty: ty.clone(),
                ir: ir_port,
            });

            let single = self.create_port_single(port);

            let connector_domain = domain.map_inner(|d| d.map_inner(|p| self.get_port_single(p)));
            let kind = ConnectorKind::Port {
                direction,
                domain: connector_domain,
                ty,
                single,
            };

            let entry = ScopedEntry::Named(NamedValue::Signal(Signal::Port(port)));
            (kind, entry)
        });

        let (kind, entry) = result_pair_split(kind_and_entry);
        self.connectors.push(ConnectorInfo { id, kind });
        entry
    }

    fn push_connector_interface(
        &mut self,
        ctx: &mut CompileItemContext,
        id: Spanned<Id>,
        domain: DiagResult<Spanned<DomainKind<Polarized<Port>>>>,
        view: DiagResult<(Vec<BigUint>, Spanned<ElaboratedInterfaceView>)>,
    ) -> DiagResult<ScopedEntry> {
        let kind_and_entry = result_pair(domain, view).and_then(|(domain, (lengths, view))| {
            let shape = interface_array_shape(ctx.refs.diags, view.span, &lengths)?;
            let id_str = id.inner.str(&ctx.refs.shared.interner).to_owned();

            let mut intfs = vec![];
            let mut singles = vec![];
            let mut ir_ports = vec![];
            try_for_each_nd_index(&shape, |index| {
                let (name, ir_name) = interface_array_element_names(&id_str, index);
                let (intf, element_singles, element_ir_ports) =
                    self.push_port_interface(ctx, id, &name, &ir_name, domain, view)?;
                intfs.push(intf);
                singles.push(element_singles);
                ir_ports.push(element_ir_ports);
                Ok(())
            })?;
            let intf = NdArray::new(shape.clone(), intfs);
            let singles = NdArray::new(shape.clone(), singles);
            let ir_ports = NdArray::new(shape, ir_ports);
            self.ir_ports_declared
                .insert(id_str, IrPortDeclared::Interface(ir_ports));

            let kind = ConnectorKind::Interface {
                domain: self.map_connector_domain(domain),
                view,
                singles,
            };
            let entry = ScopedEntry::Named(NamedValue::Interface(LeftInterfaceInfo {
                span_id: id.span,
                elab: view.map_inner(|v| v.interface),
                port_view: Some(view),
                intf,
            }));
            Ok((kind, entry))
        });

        let (kind, entry) = result_pair_split(kind_and_entry);
        self.connectors.push(ConnectorInfo { id, kind });
        entry
    }

    fn push_port_interface(
        &mut self,
        ctx: &mut CompileItemContext,
        id: Spanned<Id>,
        name: &str,
        ir_name: &str,
        domain: Spanned<DomainKind<Polarized<Port>>>,
        view: Spanned<ElaboratedInterfaceView>,
    ) -> DiagResult<(Interface, Vec<ConnectorSingle>, IndexMap<String, IrPort>)> {
        let ElaboratedInterfaceView { interface, view_index } = view.inner;
        let interface = ctx.refs.shared.elaboration_arenas.interface_info(interface);
        let view_info = &interface.views[view_index];

        let port_dirs = view_info.port_dirs.as_ref_ok()?;

        let mut declared_ports = vec![];
        let mut singles = vec![];
        let mut ir_ports = IndexMap::new();

        // TODO rework interface port names, to ensure unique but still readable names
        for (port_index, (_, port)) in enumerate(&interface.signals) {
            let port_id_str = port.id.inner.str(&ctx.refs.shared.interner);
            let port_name = format!("{name}.{port_id_str}");
            let port_ir_name = format!("{ir_name}_{port_id_str}");

            self.record_ir_port_name(port_ir_name.clone(), id.span(), true);

            let direction = port_dirs[port_index].1;
            let ty = port.ty.as_ref_ok()?;

            let ir_port_info = IrPortInfo {
                name: port_ir_name,
                direction: direction.inner,
                ty: ty.inner.as_ir(ctx.refs),
                debug_span: id.span(),
                debug_info_ty: ty.as_ref().map_inner(|ty| ty.value_string(ctx.refs)),
                debug_info_domain: domain.inner.diagnostic_string(ctx),
            };
            let ir_port = self.ir_ports.push(ir_port_info);
            ir_ports.insert(port_id_str.to_owned(), ir_port);

            let port = ctx.ports.push(PortInfo {
                span: id.span(),
                name: port_name,
                direction,
                domain: domain.map_inner(PortDomain::Kind),
                ty: ty.clone(),
                ir: ir_port,
            });

            declared_ports.push(port);

            let single = self.create_port_single(port);
            singles.push(single);
        }

        let port_interface = ctx.port_interfaces.push(PortInterfaceInfo {
            id,
            view,
            domain,
            ports: declared_ports,
        });
        Ok((Interface::Port(port_interface), singles, ir_ports))
    }

    fn map_connector_domain(
        &self,
        domain: Spanned<DomainKind<Polarized<Port>>>,
    ) -> Spanned<DomainKind<Polarized<ConnectorSingle>>> {
        domain.map_inner(|d| d.map_signal(|p| p.map_inner(|p| self.get_port_single(p))))
    }

    fn create_port_single(&mut self, port: Port) -> ConnectorSingle {
        let index = self.next_single_index;
        self.next_single_index += 1;

        let single = ConnectorSingle(index);
        self.port_to_single.insert(port, single);
        single
    }

    fn get_port_single(&self, port: Port) -> ConnectorSingle {
        self.port_to_single.get(&port).copied().unwrap()
    }

    fn report_any_err<T>(&mut self, res: &DiagResult<T>) {
        if let &Err(e) = res {
            self.any_err = Err(e);
        }
    }

    fn record_ir_port_name(&mut self, name: String, span: Span, intf: bool) {
        self.ir_ports_names_used.entry(name).or_default().push((span, intf));
    }

    fn check_unique_ir_port_names(&self, diags: &Diagnostics) -> DiagResult {
        let mut any_err = Ok(());

        for (name, sites) in &self.ir_ports_names_used {
            if sites.len() > 1 {
                let title = format!("port name conflict: `{name}`");

                let messages = sites
                    .iter()
                    .map(|&(span, intf)| {
                        let msg = match intf {
                            false => "declared here",
                            true => "declared as part of interface here",
                        };
                        (span, msg.to_owned())
                    })
                    .collect_vec();
                let messages = NonEmptyVec::try_from(messages).unwrap();

                any_err = Err(DiagnosticError::new_multiple(title, messages).report(diags));
            }
        }

        any_err
    }
}

fn eval_port_interface_view(
    ctx: &mut CompileItemContext,
    scope: &mut ExtraScope,
    flow: &mut FlowCompile,
    span_keyword: Span,
    interface: Expression,
) -> DiagResult<(Vec<BigUint>, Spanned<ElaboratedInterfaceView>)> {
    let refs = ctx.refs;

    let view = ctx.eval_expression_as_compile(
        scope.as_scope(),
        flow,
        &Type::Any,
        interface,
        Spanned::new(interface.span, "interface view"),
    )?;

    match view.inner {
        CompileValue::Simple(SimpleCompileValue::InterfaceView(inner)) => Ok((vec![], Spanned::new(view.span, inner))),
        CompileValue::Simple(SimpleCompileValue::InterfaceViewArray(lengths, inner)) => {
            Ok((lengths, Spanned::new(view.span, inner)))
        }
        value => {
            let diag = DiagnosticError::new(
                "expected interface view",
                view.span,
                format!("got value with type `{}`", value.ty().value_string(refs)),
            )
            .add_info(span_keyword, "interface port requires interface view")
            .report(refs.diags);
            Err(diag)
        }
    }
}

/// Convert the lengths of an interface array to a shape, checking that the total element count does not overflow.
pub fn interface_array_shape(diags: &Diagnostics, span: Span, lengths: &[BigUint]) -> DiagResult<Vec<usize>> {
    let err_too_large = || diags.report_error_simple("interface array too large", span, "array declared here");

    let shape = lengths
        .iter()
        .map(|len| len.as_usize_if_lt(usize::MAX).ok_or_else(err_too_large))
        .collect::<DiagResult<Vec<usize>>>()?;
    shape
        .iter()
        .try_fold(1usize, |total, &len| total.checked_mul(len))
        .ok_or_else(err_too_large)?;
    Ok(shape)
}

/// The diagnostic name (`id[i][j]`) and IR name (`id_i_j`) of an element of an interface array.
pub fn interface_array_element_names(id_str: &str, index: &[usize]) -> (String, String) {
    let name = format!("{id_str}{}", shape_string(index));
    let ir_name = format!("{id_str}{}", index.iter().map(|i| format!("_{i}")).join(""));
    (name, ir_name)
}
