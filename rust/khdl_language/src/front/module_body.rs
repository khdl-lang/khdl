use crate::front::assignment::AssignmentTarget;
use crate::front::check::{TypeContainsReason, check_type_contains_type, check_type_contains_value};
use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError};
use crate::front::domain::{DomainSignal, PortDomain, ValueDomain};
use crate::front::exit::ExitStack;
use crate::front::expression::{LeftInterfaceInfo, LrValue};
use crate::front::extra::ExtraScope;
use crate::front::flow::{Flow, FlowCompile, FlowHardwareRoot, FlowRoot, HardwareProcessKind, RegisterInfo};
use crate::front::interface::ElaboratedInterfaceSignalInfo;
use crate::front::item::{ElaboratedInterface, ElaboratedModule};
use crate::front::module_header::{
    ArenaConnectors, Connector, ConnectorInfo, ConnectorKind, ConnectorSingle, ElaboratedModuleExternalInfo,
    ElaboratedModuleHeader, ElaboratedModuleInternalInfo, ModuleConnectors, interface_array_element_names,
    interface_array_shape,
};
use crate::front::scope::{NamedValue, Scope, ScopeParent, ScopedEntry};
use crate::front::signal::{
    Interface, Polarized, Signal, SignalOrVariable, WireInfo, WireInfoInInterface, WireInfoSingle, WireInterfaceInfo,
};
use crate::front::steps::TargetStep;
use crate::front::string::shape_string;
use crate::front::types::{HardwareType, NonHardwareType, Type, Typed};
use crate::front::value::{CompileValue, HardwareValue, MaybeUndefined, SimpleCompileValue, ValueCommon};
use crate::mid::cleanup::cleanup_module;
use crate::mid::cones::compute_and_check_module_cones;
use crate::mid::ir::{
    IrAssignmentTarget, IrAsyncResetInfo, IrBlock, IrClockedProcess, IrCombinatorialProcess, IrExpression,
    IrIfStatement, IrModuleChild, IrModuleExternalInstance, IrModuleInfo, IrModuleInternalInstance, IrPortConnection,
    IrSignal, IrSignalOrVariable, IrSignals, IrStatement, IrVariables, IrWireInfo,
};
use crate::mid::steps::IrTargetSteps;
use crate::syntax::ast;
use crate::syntax::ast::{
    ClockedProcess, ClockedProcessReset, CombinatorialProcess, ConnectEntry, ConnectStatement, DomainKind,
    ExpressionKind, ModuleInstance, ModuleStatement, ModuleStatementKind, PortConnection, PortDirection, ResetKind,
    SyncDomain, Visibility, WireDeclaration, WireDeclarationDomainTyKind, WireDeclarationKind,
};
use crate::syntax::parsed::AstRefModuleInternal;
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::arena::Arena;
use crate::util::data::{IndexMapExt, NonEmptyVec, VecExt};
use crate::util::intern::Id;
use crate::util::nd_array::{NdArray, NdArrayShape, try_for_each_nd_index};
use crate::util::{ResultExt, result_pair};
use indexmap::{IndexMap, IndexSet};
use itertools::{Either, Itertools, enumerate, zip_eq};
use std::convert::identity;
use std::sync::Arc;

impl CompileRefs<'_, '_> {
    pub fn elaborate_module_body_new(
        self,
        ports: ElaboratedModuleHeader<AstRefModuleInternal>,
    ) -> DiagResult<IrModuleInfo> {
        let ElaboratedModuleHeader {
            elab_module: elab,
            ast_ref,
            unique,
            debug_info_params,
            ports,
            port_interfaces,
            ir_ports,
            ir_ports_named,
            ir_ports_declared,
            scope_params,
            scope_ports,
            flow_root,
            flow,
        } = ports;
        let &ast::ItemDefModuleInternal {
            span: _,
            vis: _,
            id: def_id,
            params: _,
            ports: _,
            ref body,
        } = &self.fixed.parsed[ast_ref];

        self.check_should_stop(def_id.span())?;
        let diags = self.diags;

        // rebuild scopes
        let mut ctx = CompileItemContext::new_restore(self, None, Some(elab), ports, port_interfaces);
        let flow_root = FlowRoot::restore(diags, flow_root);
        let mut flow = FlowCompile::restore_root(&flow_root, flow);
        let scope_ports = Scope::restore_from_content(ScopeParent::Frozen(scope_params), scope_ports);

        // elaborate the body
        let mut ctx_body = BodyContext {
            ir_signals: IrSignals {
                ports: ir_ports,
                ports_named: ir_ports_named,
                ports_declared: ir_ports_declared,
                wires: Arena::new(),
            },
            children: vec![],
            delayed_err: Ok(()),
        };
        let mut scope_body = scope_ports.new_child(body.span);
        ctx.elaborate_extra_list(
            &mut scope_body,
            &mut flow,
            &body.inner,
            false,
            &mut |ctx, scope, flow, stmt| ctx_body.elaborate_module_statement(ctx, scope, flow, stmt),
        )?;
        ctx_body.delayed_err?;

        // infer a default type for all wires that still don't have one
        //   this causes them to actually appear in the IR output, which is useful because:
        //   * we get the "wire has no driver" warnings from the IR driver checks
        //   * they can still appear in the simulator signal list
        for (_, wire_info) in ctx.wires.iter_mut() {
            if let Ok(None) = wire_info.typed_maybe(self, &ctx.wire_interfaces) {
                wire_info.suggest_ty(
                    self,
                    &ctx.wire_interfaces,
                    &mut ctx_body.ir_signals.wires,
                    Spanned::new(wire_info.span_decl(), &HardwareType::Tuple(Arc::new(vec![]))),
                )?;
            }
        }

        // fill in debug domains for wires
        for wire_info in ctx.wires.values() {
            match wire_info {
                WireInfo::Single(wire_info) => {
                    if let Ok(Some(typed)) = &wire_info.typed {
                        let domain_str = if let Ok(Some(domain)) = &wire_info.domain {
                            domain.inner.diagnostic_string(&ctx)
                        } else {
                            "unknown".to_string()
                        };

                        ctx_body.ir_signals.wires[typed.ir].debug_info_domain = domain_str;
                    }
                }
                WireInfo::Interface(_) => {
                    // handled during interface loop
                }
            }
        }
        for intf_info in ctx.wire_interfaces.values() {
            let domain_str = if let Ok(Some(domain)) = intf_info.domain {
                domain.inner.diagnostic_string(&ctx)
            } else {
                "unknown".to_string()
            };
            for &wire_ir in &intf_info.ir_wires {
                ctx_body.ir_signals.wires[wire_ir].debug_info_domain = domain_str.clone();
            }
        }

        // finish building the ir module
        let debug_info_def_file = match self.fixed.hierarchy.file_steps(def_id.span().file) {
            None => "unknown".to_string(),
            Some(steps) => steps.join("."),
        };
        let mut module_ir = IrModuleInfo {
            signals: ctx_body.ir_signals,
            large: ctx.large,
            children: ctx_body.children,
            debug_info_def_file,
            debug_info_id: unique.id().spanned_string(&self.shared.interner),
            debug_info_generic_args: debug_info_params,
        };

        // cleanup
        if self.fixed.settings.do_ir_cleanup {
            cleanup_module(&mut module_ir);
        }

        // TODO
        compute_and_check_module_cones(diags, &module_ir)?;

        Ok(module_ir)
    }
}

pub struct BodyContext {
    ir_signals: IrSignals,
    children: Vec<Spanned<IrModuleChild>>,
    delayed_err: DiagResult,
}

#[derive(Debug, Copy, Clone)]
enum ConnectionSignal {
    Signal(DomainSignal),
    Dummy(Span),
    Expression(Span),
    Error(DiagError),
}

/// Instance port connection that has been evaluated, but whose domain has not been checked yet.
/// Domain checking is delayed until all connections are evaluated, since port domains can refer to other ports.
struct InstanceConnectionEval {
    span_id: Span,
    info: DiagResult<InstanceConnectionInfo>,
}

struct InstanceConnectionInfo {
    span: Span,
    singles: Vec<(ConnectorSingle, ConnectionSignal)>,
    delayed: DelayedConnection,
}

enum DelayedConnection {
    PortInput {
        source_domain: Spanned<ValueDomain>,
        signal_ir: IrSignal,
    },
    PortOutputDummy,
    PortOutput {
        target_base: Signal,
        target_ir: IrSignal,
        expansion: Option<(HardwareType, IrTargetSteps)>,
    },
    Interface {
        values: Vec<Interface>,
        any_input: bool,
        any_output: bool,
        ir_connections: Vec<IrPortConnection>,
    },
}

struct ConnectEntryEval<'a> {
    span: Span,
    interface: Spanned<ElaboratedInterface>,
    port_dirs: &'a [(Spanned<Id>, Spanned<PortDirection>)],
    intf: NdArray<Interface>,
}

impl BodyContext {
    fn elaborate_module_statement(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &mut ExtraScope,
        flow: &mut FlowCompile,
        stmt: &ModuleStatement,
    ) -> DiagResult {
        match &stmt.inner {
            ModuleStatementKind::ParseError(_) => Err(ctx
                .refs
                .diags
                .report_error_internal(stmt.span, "encountered parse error")),
            ModuleStatementKind::WireDeclaration(decl) => {
                self.elaborate_wire_declaration(ctx, scope, flow, Spanned::new(stmt.span, decl))
            }
            ModuleStatementKind::CombinatorialProcess(block) => {
                self.elaborate_combinatorial_block(ctx, scope.as_scope(), flow, Spanned::new(stmt.span, block))
            }
            ModuleStatementKind::ClockedProcess(block) => {
                self.elaborate_clocked_block(ctx, scope.as_scope(), flow, Spanned::new(stmt.span, block))
            }
            ModuleStatementKind::Instance(inst) => {
                self.elaborate_instance(ctx, scope.as_scope(), flow, Spanned::new(stmt.span, inst))
            }
            ModuleStatementKind::Connect(connect) => {
                self.elaborate_connect(ctx, scope.as_scope(), flow, Spanned::new(stmt.span, connect))
            }
        }
    }

    fn elaborate_wire_declaration(
        &mut self,
        ctx: &mut CompileItemContext,
        scope_extra: &mut ExtraScope,
        flow_parent: &mut FlowCompile,
        stmt: Spanned<&WireDeclaration>,
    ) -> DiagResult {
        let &WireDeclaration {
            vis,
            span_keyword,
            id: wire_id,
            kind,
        } = stmt.inner;

        let refs = ctx.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let scope = scope_extra.as_scope();

        // evaluate id
        let wire_id = ctx.eval_maybe_id(scope, flow_parent, wire_id)?;

        // evaluate kind: ty/value
        let named_value = match kind {
            WireDeclarationKind::Normal {
                domain_ty,
                assign_span_and_value,
            } => {
                // create wire immediately, we'll fill in the domain and type later
                let wire = ctx.wires.push(WireInfo::Single(WireInfoSingle {
                    id: wire_id,
                    domain: Ok(None),
                    typed: Ok(None),
                }));

                let (domain, ty) = match domain_ty {
                    WireDeclarationDomainTyKind::Clock { span_clock } => (
                        Some(Spanned::new(span_clock, ValueDomain::Clock)),
                        Some(Spanned::new(span_clock, HardwareType::Bool)),
                    ),
                    WireDeclarationDomainTyKind::Normal { domain, ty } => {
                        let domain = domain
                            .map(|domain| {
                                let domain = ctx.eval_domain(scope, flow_parent, domain)?;
                                Ok(domain.map_inner(ValueDomain::from_domain_kind))
                            })
                            .transpose();
                        let ty = ty
                            .map(|ty| ctx.eval_expression_as_ty_hardware(scope, flow_parent, ty, "wire"))
                            .transpose();

                        let domain = domain?;
                        let ty = ty?;

                        (domain, ty)
                    }
                };

                match assign_span_and_value {
                    None => {
                        // just set the domain and type
                        if let Some(domain) = domain {
                            ctx.wires[wire].suggest_domain(&mut ctx.wire_interfaces, domain)?;
                        }
                        if let Some(ty) = ty.as_ref() {
                            ctx.wires[wire].suggest_ty(
                                refs,
                                &ctx.wire_interfaces,
                                &mut self.ir_signals.wires,
                                ty.as_ref(),
                            )?;
                        }
                    }
                    Some((assign_span, value)) => {
                        // eval value
                        let expected_ty = ty.as_ref().map_or(Type::Any, |ty| ty.inner.as_type());

                        let flow_kind = HardwareProcessKind::WireExpression {
                            span_keyword,
                            span_init: value.span,
                        };
                        let mut flow_value =
                            FlowHardwareRoot::new(flow_parent, value.span, flow_kind, &mut self.ir_signals);
                        let value = ctx.eval_expression(scope, &mut flow_value.as_flow(), &expected_ty, value)?;
                        let (ir_vars, mut ir_block) = flow_value.finish();

                        // infer or check domain
                        let value_domain = value.as_ref().map_inner(|v| v.domain());
                        let domain = match domain {
                            None => Ok(value_domain),
                            Some(domain) => ctx
                                .check_valid_domain_crossing(
                                    assign_span,
                                    value_domain,
                                    domain,
                                    "wire declaration value",
                                )
                                .map(|()| domain),
                        };

                        // infer or check type
                        let ty = match ty {
                            None => match value.inner.ty().as_hardware_type(elab) {
                                Ok(ty) => Ok(Spanned::new(value.span, ty)),
                                Err(e) => {
                                    let _: NonHardwareType = e;
                                    let err_msg = format!(
                                        "value with type `{}` cannot be represented in hardware",
                                        value.inner.ty().value_string(refs)
                                    );
                                    let diag = DiagnosticError::new(
                                        "cannot assign non-hardware value to wire",
                                        value.span,
                                        err_msg,
                                    )
                                    .add_info(assign_span, "assignment to wire here")
                                    .report(diags);
                                    Err(diag)
                                }
                            },
                            Some(ty) => {
                                let reason = TypeContainsReason::Assignment {
                                    span_target: wire_id.span(),
                                    span_target_ty: ty.span,
                                };
                                check_type_contains_value(refs, reason, &ty.inner.as_type(), value.as_ref())
                                    .map(|()| ty)
                            }
                        };

                        let domain = domain?;
                        let ty = ty?;

                        // create the wire by suggesting the domain and ty
                        let wire_info = &mut ctx.wires[wire];
                        wire_info.suggest_domain(&mut ctx.wire_interfaces, domain)?;
                        let wire_info_typed = wire_info.suggest_ty(
                            refs,
                            &ctx.wire_interfaces,
                            &mut self.ir_signals.wires,
                            ty.as_ref(),
                        )?;

                        // append final assignment to process
                        let expr_hw = value.inner.as_ir_expression_unchecked(
                            refs,
                            &mut ctx.large,
                            value.span,
                            wire_info_typed.ty.inner,
                        )?;
                        let target = IrAssignmentTarget::simple(wire_info_typed.ir);

                        ir_block
                            .statements
                            .push(Spanned::new(stmt.span, IrStatement::Assign(target, expr_hw)));

                        // record process
                        let process = IrCombinatorialProcess {
                            variables: ir_vars,
                            block: ir_block,
                        };
                        self.children
                            .push(Spanned::new(stmt.span, IrModuleChild::CombinatorialProcess(process)));
                    }
                }

                NamedValue::Signal(Signal::Wire(wire))
            }
            WireDeclarationKind::Interface {
                domain,
                span_keyword,
                interface,
            } => {
                // eval domain and interface
                let domain = domain
                    .map(|domain| {
                        let domain = ctx.eval_domain(scope, flow_parent, domain)?;
                        Ok(domain.map_inner(ValueDomain::from_domain_kind))
                    })
                    .transpose();

                let interface = ctx
                    .eval_expression_as_compile(
                        scope,
                        flow_parent,
                        &Type::Any,
                        interface,
                        Spanned::new(span_keyword, "wire interface"),
                    )
                    .and_then(|interface| match interface.inner {
                        CompileValue::Simple(SimpleCompileValue::Interface(interface_inner)) => {
                            Ok((vec![], Spanned::new(interface.span, interface_inner)))
                        }
                        CompileValue::Simple(SimpleCompileValue::InterfaceArray(lengths, interface_inner)) => {
                            let shape = interface_array_shape(diags, interface.span, &lengths)?;
                            Ok((shape, Spanned::new(interface.span, interface_inner)))
                        }
                        value => {
                            let diag = DiagnosticError::new(
                                "expected interface or interface array",
                                interface.span,
                                format!("got value with type `{}`", value.ty().value_string(refs)),
                            )
                            .add_info(span_keyword, "interface wire requires interface")
                            .report(diags);
                            Err(diag)
                        }
                    });

                let domain = domain?;
                let (shape, interface) = interface?;

                let wire_id_str = wire_id.diagnostic_str(&refs.shared.interner);
                let interface_info = elab.interface_info(interface.inner);

                let mut intfs = vec![];
                try_for_each_nd_index(&shape, |index| {
                    let (element_str, element_ir_str) = interface_array_element_names(wire_id_str, index);

                    // create interface wire
                    let wire_interface = ctx.wire_interfaces.push(WireInterfaceInfo {
                        id: wire_id,
                        domain: Ok(domain),
                        interface,
                        // these will be filled in immediately after this
                        wires: vec![],
                        ir_wires: vec![],
                    });

                    // create inner wires
                    let mut wires = vec![];
                    let mut ir_wires = vec![];

                    for (signal_index, (_, signal_info)) in enumerate(&interface_info.signals) {
                        let ElaboratedInterfaceSignalInfo {
                            id: signal_id,
                            ty: signal_ty,
                        } = signal_info;
                        let signal_ty = signal_ty.as_ref_ok()?;

                        let signal_id_str = signal_id.inner.str(&refs.shared.interner);
                        let diagnostic_str = format!("{element_str}.{signal_id_str}");
                        let ir_name = format!("{element_ir_str}_{signal_id_str}");

                        let wire_ir_info = IrWireInfo {
                            ty: signal_ty.inner.as_ir(refs),
                            debug_info_id: Spanned::new(wire_id.span(), Some(ir_name)),
                            debug_info_ty: signal_ty.inner.value_string(refs),
                            // will be filled in later during the inference checking pass
                            debug_info_domain: String::new(),
                        };
                        let wire_ir = self.ir_signals.wires.push(wire_ir_info);

                        let wire_info = WireInfoInInterface {
                            decl_span: stmt.span,
                            interface: Spanned::new(interface.span, wire_interface),
                            index: signal_index,
                            diagnostic_string: diagnostic_str,
                            ir: wire_ir,
                        };
                        let wire = ctx.wires.push(WireInfo::Interface(wire_info));

                        wires.push(wire);
                        ir_wires.push(wire_ir);
                    }

                    let wire_interface_info = &mut ctx.wire_interfaces[wire_interface];
                    wire_interface_info.wires = wires;
                    wire_interface_info.ir_wires = ir_wires;

                    intfs.push(Interface::Wire(wire_interface));
                    Ok(())
                })?;
                let intf = NdArray::new(shape, intfs);

                NamedValue::Interface(LeftInterfaceInfo {
                    span_id: wire_id.span(),
                    elab: interface,
                    port_view: None,
                    intf,
                })
            }
        };

        // declare wire in the right scope
        let entry = ScopedEntry::Named(named_value);
        match vis {
            Visibility::Public { span: _ } => scope_extra.declare_root(refs, wire_id, Ok(entry)),
            Visibility::Private => scope_extra.as_scope().declare(refs, wire_id, Ok(entry)),
        }

        Ok(())
    }

    fn elaborate_combinatorial_block(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &Scope,
        flow_parent: &mut FlowCompile,
        stmt: Spanned<&CombinatorialProcess>,
    ) -> DiagResult {
        let &CombinatorialProcess {
            span_keyword,
            ref block,
        } = stmt.inner;

        let diags = ctx.refs.diags;

        // elaborate block
        let flow_kind = HardwareProcessKind::CombinatorialProcessBody { span_keyword };
        let mut flow = FlowHardwareRoot::new(flow_parent, block.span, flow_kind, &mut self.ir_signals);

        let mut stack = ExitStack::new_root();

        let end = ctx.elaborate_block(scope, &mut flow.as_flow(), &mut stack, block)?;
        end.unwrap_normal(diags, block.span)?;
        let (ir_vars, ir_block) = flow.finish();

        // record process
        let process = IrCombinatorialProcess {
            variables: ir_vars,
            block: ir_block,
        };
        self.children
            .push(Spanned::new(span_keyword, IrModuleChild::CombinatorialProcess(process)));

        Ok(())
    }

    fn elaborate_clocked_block(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &Scope,
        flow_parent: &mut FlowCompile,
        stmt: Spanned<&ClockedProcess>,
    ) -> DiagResult {
        let &ClockedProcess {
            span_keyword,
            span_domain,
            clock,
            reset,
            ref block,
        } = stmt.inner;

        let diags = ctx.refs.diags;

        // eval domain
        let clock = ctx.eval_expression_as_domain_signal(scope, flow_parent, clock);
        let reset = reset
            .as_ref()
            .map(|reset| {
                reset
                    .as_ref()
                    .map_inner(|reset| {
                        let &ClockedProcessReset { kind, signal } = reset;
                        let signal = ctx.eval_expression_as_domain_signal(scope, flow_parent, signal)?;
                        Ok(ClockedProcessReset { kind, signal })
                    })
                    .transpose()
            })
            .transpose();
        let (clock, reset) = result_pair(clock, reset)?;

        // check reset domain
        if let Some(reset) = &reset {
            let ClockedProcessReset { kind, signal } = reset.inner;
            match kind.inner {
                // nothing to check for async resets
                // TODO check that the posedge is sync to the clock
                ResetKind::Async => {}
                // check that the reset is sync to the clock
                ResetKind::Sync => {
                    let target = clock.map_inner(|s| ValueDomain::Sync(SyncDomain { clock: s, reset: None }));

                    let source_domain = signal.inner.signal.domain(ctx, signal.span)?;
                    let source = Spanned::new(reset.span, source_domain.inner);
                    ctx.check_valid_domain_crossing(span_domain, source, target, "sync reset")?;
                }
            }
        };

        // map to domain: async reset stays, a sync reset disappears
        let domain = SyncDomain {
            clock: clock.inner,
            reset: reset.as_ref().and_then(|reset| match reset.inner.kind.inner {
                ResetKind::Async => Some(reset.inner.signal.inner),
                ResetKind::Sync => None,
            }),
        };
        let domain = Spanned::new(span_domain, domain);

        // elaborate block
        let mut registers = IndexMap::new();
        let flow_kind = HardwareProcessKind::ClockedProcessBody {
            span_keyword,
            domain,
            registers: &mut registers,
        };
        let mut flow = FlowHardwareRoot::new(flow_parent, block.span, flow_kind, &mut self.ir_signals);

        let mut stack = ExitStack::new_root();
        let end = ctx.elaborate_block(scope, &mut flow.as_flow(), &mut stack, block)?;
        end.unwrap_normal(diags, block.span)?;

        let (ir_vars, ir_block) = flow.finish();

        // record IR registers
        let registers_ir: IndexSet<IrSignal> = registers.iter().map(|(_, info)| info.ir).collect();

        // build reset structure
        let (clock_block, async_reset) = match reset {
            None => {
                // check that registers don't need reset values
                for info in registers.into_values() {
                    let RegisterInfo {
                        span: reg_span,
                        ir: _,
                        reset: reg_reset,
                    } = info;
                    match reg_reset.inner {
                        MaybeUndefined::Undefined => {
                            // no reset value is allowed
                        }
                        MaybeUndefined::Defined(_) => {
                            let diag = DiagnosticError::new(
                                "clocked block without reset cannot drive register with reset value",
                                reg_span,
                                "register with reset value declared here",
                            )
                            .add_info(clock.span, "clocked block declared without reset here")
                            .add_info(reg_reset.span, "register reset value defined here")
                            .add_footer_hint("either add a reset to the block or use `undef` as the reset value")
                            .report(diags);
                            self.delayed_err = Err(diag);
                        }
                    }
                }

                (ir_block, None)
            }
            Some(reset) => {
                let reset_ir = Spanned::new(reset.inner.signal.span, ctx.domain_signal_to_ir(reset.inner.signal)?);

                // collect resets
                let mut resets = vec![];
                for info in registers.into_values() {
                    let RegisterInfo {
                        span: reg_span,
                        ir: reg_ir,
                        reset: reg_reset,
                    } = info;
                    match reg_reset.inner {
                        MaybeUndefined::Undefined => {
                            // no reset value, do nothing
                        }
                        MaybeUndefined::Defined(reg_reset) => {
                            resets.push(Spanned::new(reg_span, (reg_ir, reg_reset)));
                        }
                    }
                }

                // build proper reset structure
                match reset.inner.kind.inner {
                    ResetKind::Async => {
                        // async reset has a dedicated structure
                        let reset_info = IrAsyncResetInfo {
                            signal: reset_ir,
                            resets,
                        };
                        (ir_block, Some(reset_info))
                    }
                    ResetKind::Sync => {
                        // sync reset just becomes assignments inside an if branch
                        let reset_statements = resets
                            .into_iter()
                            .map(|reset| {
                                let (signal, reset_value) = reset.inner;
                                let stmt = IrStatement::Assign(IrAssignmentTarget::simple(signal), reset_value);
                                Spanned::new(reset.span, stmt)
                            })
                            .collect_vec();
                        let reset_block = IrBlock {
                            statements: reset_statements,
                        };

                        let if_stmt = IrIfStatement {
                            condition: reset_ir.inner.as_expression(&mut ctx.large),
                            then_block: reset_block,
                            else_block: Some(ir_block),
                        };
                        let root_block = IrBlock {
                            statements: vec![Spanned::new(reset_ir.span, IrStatement::If(if_stmt))],
                        };
                        (root_block, None)
                    }
                }
            }
        };

        // record process
        let clock_ir = Spanned::new(clock.span, ctx.domain_signal_to_ir(clock)?);
        let process = IrClockedProcess {
            registers: registers_ir,
            variables: ir_vars,
            async_reset,
            clock_signal: clock_ir,
            clock_block,
        };
        self.children
            .push(Spanned::new(span_keyword, IrModuleChild::ClockedProcess(process)));

        Ok(())
    }

    fn elaborate_connect(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &Scope,
        flow_parent: &mut FlowCompile,
        stmt: Spanned<&ConnectStatement>,
    ) -> DiagResult {
        let refs = ctx.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;
        let interner = &refs.shared.interner;

        let &ConnectStatement {
            span_keyword,
            ref entries,
        } = stmt.inner;

        // eval entries
        let mut entries_eval: Vec<ConnectEntryEval> = vec![];
        let mut scope_entries = scope.new_child(entries.span);
        let mut any_err_entries = Ok(());
        ctx.elaborate_extra_list(
            &mut scope_entries,
            flow_parent,
            entries,
            false,
            &mut |ctx, scope, flow, entry| {
                let &ConnectEntry { span: _, expr, view } = entry;

                // eval value
                let mut flow_value = flow.new_child_isolated();
                let value = ctx.eval_expression_as_lr(scope.as_scope(), &mut flow_value, &Type::Any, expr)?
                    .resolve_reference_fields(ctx, &mut flow_value)?;
                // eval view
                let view_id = view
                    .map(|view| ctx.eval_id(scope.as_scope(), flow, view.id))
                    .transpose()?;

                // check that value is an interface
                let LrValue::LeftInterface(value) = value else {
                    return Err(
                        DiagnosticError::new("expected interface value", expr.span, "got non-interface value")
                            .add_info(span_keyword, "connect requires interface values")
                            .report(diags),
                    );
                };
                let interface_info = elab.interface_info(value.elab.inner);

                // figure out the view
                let (view_span, view_index) = if let Some(view_id) = view_id {
                    // we explicit have one here, use it
                    let (view_index, _) = interface_info.get_view(diags, interner, view_id)?;
                    (view_id.span, view_index)
                } else if let Some(port_view) = value.port_view {
                    // this is a port, which has a view, default to it
                    (port_view.span, port_view.inner.view_index)
                } else {
                    // no view info, error
                    let e = DiagnosticError::new(
                        "missing view for wire interface",
                        expr.span,
                        "wire interface used here without a view",
                    )
                        .add_footer_hint("only port interfaces have a declared view, add `view <name>` to select one")
                        .report(diags);
                    any_err_entries = Err(e);
                    return Ok(());
                };

                // for ports, check that the view directions match the declared port directions
                let view_info = &interface_info.views[view_index];
                let view_dirs = view_info.port_dirs.as_ref_ok()?;
                if let Some(port_view) = value.port_view
                    && port_view.inner.view_index != view_index
                {
                    let port_view_info = &interface_info.views[port_view.inner.view_index];
                    let port_view_dirs = port_view_info.port_dirs.as_ref_ok()?;
                    let mismatches = enumerate(zip_eq(view_dirs, port_view_dirs))
                        .filter(|(_, ((_, dir), (_, port_dir)))| dir.inner != port_dir.inner)
                        .collect_vec();

                    if !mismatches.is_empty() {
                        let view_name = &view_info.debug_info_name;
                        let port_view_name = &port_view_info.debug_info_name;

                        let mut diag = DiagnosticError::new(
                            format!("view `{view_name}` does not match the directions of the port interface"),
                            view_span,
                            format!("view `{view_name}` used here"),
                        )
                        .add_info(
                            port_view.span,
                            format!("port interface declared with view `{port_view_name}` here"),
                        );
                        for (signal_index, ((_, dir), (_, port_dir))) in mismatches {
                            let signal_id_str = interface_info.signals[signal_index].id.inner.str(interner);
                            diag = diag.add_footer_info(format!(
                                "signal `{signal_id_str}` is `{}` in view `{view_name}`, but `{}` in view `{port_view_name}`",
                                dir.inner.diagnostic_string(),
                                port_dir.inner.diagnostic_string(),
                            ));
                        }
                        any_err_entries = Err(diag.report(diags));
                    }
                }

                // store entry
                entries_eval.push(ConnectEntryEval {
                    span: entry.span,
                    interface: value.elab,
                    port_dirs: view_dirs,
                    intf: value.intf,
                });
                Ok(())
            },
        )?;
        any_err_entries?;

        // check that there are at least two entries
        let [first, rest @ ..] = entries_eval.as_slice() else {
            return Err(diags.report_error_simple(
                "connect requires at least two entries",
                entries.span,
                "got no entries here",
            ));
        };
        if rest.is_empty() {
            return Err(diags.report_error_simple(
                "connect requires at least two entries",
                entries.span,
                "got only a single entry here",
            ));
        }

        // check that all interfaces match
        let interface_mismatches = rest
            .iter()
            .filter(|other| first.interface.inner != other.interface.inner)
            .map(|other| {
                let message = format!(
                    "this entry has interface `{}`",
                    other.interface.inner.value_string(refs)
                );
                (other.span, message)
            })
            .collect_vec();
        if let Ok(interface_mismatches) = NonEmptyVec::try_from(interface_mismatches) {
            let diag = DiagnosticError::new_multiple("interface mismatch", interface_mismatches)
                .add_info(
                    first.span,
                    format!(
                        "first entry has interface `{}`",
                        first.interface.inner.value_string(refs)
                    ),
                )
                .report(diags);
            return Err(diag);
        }

        // check that all shapes match
        let shape_mismatches = rest
            .iter()
            .filter(|other| first.intf.shape() != other.intf.shape())
            .map(|other| {
                let message = format!("this entry is {}", describe_interface_shape(other.intf.shape()));
                (other.span, message)
            })
            .collect_vec();
        if let Ok(shape_mismatches) = NonEmptyVec::try_from(shape_mismatches) {
            let diag = DiagnosticError::new_multiple("interface array shape mismatch", shape_mismatches)
                .add_info(
                    first.span,
                    format!("first entry is {}", describe_interface_shape(first.intf.shape())),
                )
                .report(diags);
            return Err(diag);
        }

        // for each signal, find the single driver entry, grouping errors by the set of driving entries
        let interface_info = elab.interface_info(first.interface.inner);

        let mut signal_drivers = vec![];
        let mut signal_driver_errors: IndexMap<Vec<bool>, Vec<usize>> = IndexMap::new();
        for signal_index in 0..interface_info.signals.len() {
            let mask_input = entries_eval
                .iter()
                .map(|e| e.port_dirs[signal_index].1.inner.is_input())
                .collect_vec();

            // find single source
            let sources = mask_input.iter().copied().positions(identity).collect_vec();
            if let &[source] = sources.as_slice() {
                signal_drivers.push(source);
                continue;
            }

            // failed, collect error info
            signal_driver_errors.entry(mask_input).or_default().push(signal_index);
        }

        // report driver errors if any
        let mut any_driver_err = Ok(());
        for (entry_drives, signals) in signal_driver_errors {
            assert!(!signals.is_empty());

            let signals_str = {
                let (plural_s, plural_has) = if signals.len() > 1 { ("s", "have") } else { ("", "has") };
                let list = signals
                    .iter()
                    .map(|&s| {
                        let s = interface_info.signals[s].id.inner.str(interner);
                        format!("`{s}`")
                    })
                    .join(", ");
                format!("signal{plural_s} {list} {plural_has}")
            };

            let multiple_drivers = entry_drives.iter().copied().any(identity);
            let title = if multiple_drivers {
                "multiple drivers"
            } else {
                "no driver"
            };

            let mut diag = DiagnosticError::new(format!("{signals_str} {title}"), span_keyword, "connection here");

            if multiple_drivers {
                for (entry, &drives) in zip_eq(&entries_eval, &entry_drives) {
                    if drives {
                        diag = diag.add_info(entry.span, "driven here");
                    }
                }
            } else {
                diag = diag.add_footer_info("all entries only read");
            }

            any_driver_err = Err(diag.report(diags));
        }
        any_driver_err?;
        assert_eq!(signal_drivers.len(), interface_info.signals.len());

        // for each element of the arrays, suggest and check domains, and then emit the processes
        let mut any_err_domain = Ok(());
        for element_index in 0..first.intf.flat_values().len() {
            let element = |entry: &ConnectEntryEval| entry.intf.flat_values()[element_index];

            // suggest and check domains
            let entries = entries_eval
                .iter()
                .map(|entry| Spanned::new(entry.span, element(entry)))
                .collect_vec();
            if let Err(e) = connect_domains_suggest_and_check(ctx, span_keyword, &entries, &signal_drivers) {
                any_err_domain = Err(e);
                continue;
            }

            // build a combinatorial process for each source signal, driving all of its sinks
            for (signal_index, &source) in enumerate(&signal_drivers) {
                let source_ir = element(&entries_eval[source]).signal_ir(ctx, signal_index);
                let statements = enumerate(&entries_eval)
                    .filter(|&(sink, _)| sink != source)
                    .map(|(_, sink)| {
                        let target = IrAssignmentTarget::simple(element(sink).signal_ir(ctx, signal_index));
                        Spanned::new(sink.span, IrStatement::Assign(target, IrExpression::Signal(source_ir)))
                    })
                    .collect_vec();
                let process = IrCombinatorialProcess {
                    variables: IrVariables::new(),
                    block: IrBlock { statements },
                };
                self.children
                    .push(Spanned::new(stmt.span, IrModuleChild::CombinatorialProcess(process)));
            }
        }

        any_err_domain
    }

    fn elaborate_instance(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &Scope,
        flow_parent: &mut FlowCompile,
        stmt: Spanned<&ModuleInstance>,
    ) -> DiagResult {
        let refs = ctx.refs;
        let diags = refs.diags;
        let interner = &refs.shared.interner;

        let &ModuleInstance {
            ref name,
            span_keyword,
            module,
            ref port_connections,
        } = stmt.inner;

        // eval name
        let name = name.map(|name| ctx.eval_id(scope, flow_parent, name)).transpose()?;

        // eval module
        let elaborated_module = ctx.eval_expression_as_module(scope, flow_parent, span_keyword, module)?;

        // get module info
        let (instance_info, connectors, def_ports_span) = match elaborated_module {
            ElaboratedModule::Internal(module) => {
                let ElaboratedModuleInternalInfo {
                    ast_ref,
                    unique: _,
                    module_ir,
                    connectors,
                } = ctx.refs.shared.elaboration_arenas.module_internal_info(module);
                (
                    ElaboratedModule::Internal(*module_ir),
                    connectors,
                    refs.fixed.parsed[*ast_ref].ports.span,
                )
            }
            ElaboratedModule::External(module) => {
                let ElaboratedModuleExternalInfo {
                    ast_ref,
                    module_name,
                    generic_args,
                    ports,
                    connectors,
                } = ctx.refs.shared.elaboration_arenas.module_external_info(module);
                (
                    ElaboratedModule::External((module_name, generic_args, ports)),
                    connectors,
                    refs.fixed.parsed[*ast_ref].ports.span,
                )
            }
        };
        let ModuleConnectors {
            arena: connectors,
            id_to_connector,
        } = connectors;

        // eval port connections (in connection order, so side effects and scopes are correct)
        let mut connector_to_connections: IndexMap<Connector, Vec<InstanceConnectionEval>> =
            connectors.keys().map(|connector| (connector, vec![])).collect();
        let mut any_err = Ok(());
        {
            let mut scope_connections = scope.new_child(port_connections.span);
            ctx.elaborate_extra_list(
                &mut scope_connections,
                flow_parent,
                &port_connections.inner,
                true,
                &mut |ctx, scope, flow, connection| {
                    // eval id
                    let id = ctx.eval_id(scope.as_scope(), flow, connection.id);
                    let id = match id {
                        Ok(id) => id,
                        Err(e) => {
                            any_err = Err(e);
                            return Ok(());
                        }
                    };

                    // find corresponding connector
                    let connector = match id_to_connector.get(&id.inner) {
                        Some(&connector) => connector,
                        None => {
                            let diag = DiagnosticError::new(
                                "connection does not match any port",
                                id.span,
                                "invalid connection here",
                            )
                            .add_info(def_ports_span, "ports declared here")
                            .report(diags);

                            any_err = Err(diag);
                            return Ok(());
                        }
                    };

                    // evaluate connection
                    let info = self.eval_instance_port_connection(
                        ctx,
                        scope.as_scope(),
                        flow,
                        connectors,
                        connector,
                        connection,
                    );

                    // store connection
                    let eval = InstanceConnectionEval { span_id: id.span, info };
                    connector_to_connections.get_mut(&connector).unwrap().push(eval);

                    Ok(())
                },
            )?;
        }

        // visit connectors (in connector declaration order, so domain references work)
        let mut single_to_signal: IndexMap<ConnectorSingle, ConnectionSignal> = IndexMap::new();
        let mut ir_connections = vec![];
        for (connector, connections) in connector_to_connections {
            let connector_info = &connectors[connector];
            let connector_id_str = connector_info.id.inner.str(interner);

            // check that there is exactly one connection
            let mut connections = connections.into_iter();
            let connection = match (connections.next(), connections.next()) {
                (Some(single), None) => {
                    // great
                    single.info.map(|info| (single.span_id, info))
                }
                (None, _) => {
                    // error, missing connection
                    let diag = DiagnosticError::new(
                        format!("missing connection for port `{connector_id_str}`"),
                        Span::empty_at(port_connections.span.end()),
                        "connections here",
                    )
                    .add_info(connector_info.id.span, "port declared here")
                    .report(diags);
                    Err(diag)
                }
                (Some(first), Some(second)) => {
                    // error, multiple connections
                    let mut diag = DiagnosticError::new(
                        format!("multiple connections for port `{connector_id_str}`"),
                        second.span_id,
                        "connected again here",
                    )
                    .add_info(first.span_id, "first connected here");
                    for r in connections {
                        diag = diag.add_info(r.span_id, "connected again here");
                    }
                    Err(diag.report(diags))
                }
            };

            // record the connected signals, later ports can refer to them in their domains
            let (span_id, info) = match connection {
                Ok((span_id, info)) => {
                    for &(single, signal) in &info.singles {
                        single_to_signal.insert_first(single, signal);
                    }
                    (span_id, info)
                }
                Err(e) => {
                    if let Ok(kind) = &connector_info.kind {
                        for single in kind.singles() {
                            single_to_signal.insert_first(single, ConnectionSignal::Error(e));
                        }
                    }
                    any_err = Err(e);
                    continue;
                }
            };

            // check domains and finish the connection
            match self.finish_instance_port_connection(ctx, connectors, &single_to_signal, connector, span_id, info) {
                Ok(connections) => ir_connections.extend(connections),
                Err(e) => any_err = Err(e),
            }
        }
        any_err?;

        // build instance
        let name = name.map(|id| id.inner.str(&ctx.refs.shared.interner).to_owned());
        let ir_instance = match instance_info {
            ElaboratedModule::Internal(module_ir) => IrModuleChild::ModuleInternalInstance(IrModuleInternalInstance {
                name,
                module: module_ir,
                port_connections: ir_connections,
            }),
            ElaboratedModule::External((module_name, generic_args, ports)) => {
                let port_connections: IndexMap<_, _> = zip_eq(ports, ir_connections)
                    .map(|((port_name, port_ty), connection)| (port_name.clone(), (port_ty.as_ir(refs), connection)))
                    .collect();

                IrModuleChild::ModuleExternalInstance(IrModuleExternalInstance {
                    name,
                    module_name: module_name.clone(),
                    generic_args: generic_args.clone(),
                    port_connections,
                })
            }
        };

        // record instance
        self.children.push(Spanned::new(stmt.span, ir_instance));
        Ok(())
    }

    fn eval_instance_port_connection(
        &mut self,
        ctx: &mut CompileItemContext,
        scope: &Scope,
        flow_parent: &mut FlowCompile,
        connectors: &ArenaConnectors,
        connector: Connector,
        connection: &PortConnection,
    ) -> DiagResult<InstanceConnectionInfo> {
        let refs = ctx.refs;
        let diags = refs.diags;
        let interner = &refs.shared.interner;

        // connector, declared in the module being instantiated
        let ConnectorInfo {
            id: connector_id,
            kind: connector_kind,
        } = &connectors[connector];

        // connection, declared in the instantiation statement
        let connection_span = connection.span();
        let &PortConnection {
            id: connection_id,
            expr,
        } = &connection;
        let expr = expr.expr();

        // always try to evaluate as signal for domain replacing purposes
        let signal = match &refs.get_expr(expr) {
            ExpressionKind::Dummy => ConnectionSignal::Dummy(expr.span),
            _ => {
                let mut flow_domain = flow_parent.new_child_isolated();
                match ctx.try_eval_expression_as_domain_signal(scope, &mut flow_domain, expr, |_| ()) {
                    Ok(signal) => ConnectionSignal::Signal(signal.inner),
                    Err(Either::Left(())) => ConnectionSignal::Expression(expr.span),
                    Err(Either::Right(e)) => return Err(e),
                }
            }
        };

        // evaluate the connection differently depending on the port direction
        match connector_kind.as_ref_ok()? {
            &ConnectorKind::Port {
                direction: port_dir,
                domain: _,
                ty: ref port_ty,
                single: connector_single,
            } => {
                let delayed = match port_dir.inner {
                    PortDirection::Input => {
                        // better dummy port error message
                        if let ExpressionKind::Dummy = refs.get_expr(expr) {
                            let diag = DiagnosticError::new(
                                "dummy connections are only allowed for output ports",
                                expr.span,
                                "dummy connection used here",
                            )
                            .add_info(port_dir.span, "port declared as input here")
                            .report(diags);
                            return Err(diag);
                        }

                        // eval expr
                        let flow_kind = HardwareProcessKind::InstancePortConnection {
                            span_connection: connection_span,
                        };
                        let mut flow = FlowHardwareRoot::new(flow_parent, expr.span, flow_kind, &mut self.ir_signals);
                        let connection_value =
                            ctx.eval_expression(scope, &mut flow.as_flow(), &port_ty.inner.as_type(), expr)?;
                        let (ir_vars, mut ir_block) = flow.finish();

                        // check type
                        let reason = TypeContainsReason::InstancePortInput {
                            span_connection_port_id: connection_id.span(),
                            span_port_ty: port_ty.span,
                        };
                        check_type_contains_value(refs, reason, &port_ty.inner.as_type(), connection_value.as_ref())?;

                        // convert value to ir
                        let connection_value_ir_raw = connection_value
                            .as_ref()
                            .map_inner(|v| {
                                Ok(v.as_hardware_value_unchecked(
                                    refs,
                                    &mut ctx.large,
                                    expr.span,
                                    port_ty.inner.clone(),
                                )?
                                .expr)
                            })
                            .transpose()?;

                        // build extra wire and process if necessary
                        let connection_signal_ir = if let Some(connection_signal) =
                            try_extract_simple_port_input_signal(&ir_block, &connection_value_ir_raw.inner)
                        {
                            connection_signal
                        } else {
                            let extra_ir_wire = self.ir_signals.wires.push(IrWireInfo {
                                ty: port_ty.inner.as_ir(refs),
                                debug_info_id: connector_id.map_inner(|id| Some(id.str(interner).to_owned())),
                                debug_info_ty: port_ty.inner.clone().value_string(refs),
                                debug_info_domain: connection_value.inner.domain().diagnostic_string(ctx),
                            });

                            ir_block.statements.push(Spanned {
                                span: connection_span,
                                inner: IrStatement::Assign(
                                    IrAssignmentTarget::simple(extra_ir_wire),
                                    connection_value_ir_raw.inner,
                                ),
                            });
                            let process = IrCombinatorialProcess {
                                variables: ir_vars,
                                block: ir_block,
                            };
                            let child = IrModuleChild::CombinatorialProcess(process);
                            self.children.push(Spanned::new(connection_span, child));

                            IrSignal::Wire(extra_ir_wire)
                        };

                        DelayedConnection::PortInput {
                            source_domain: connection_value.as_ref().map_inner(|v| v.domain()),
                            signal_ir: connection_signal_ir,
                        }
                    }
                    PortDirection::Output => {
                        match refs.get_expr(expr) {
                            ExpressionKind::Dummy => DelayedConnection::PortOutputDummy,
                            _ => {
                                let mut flow = flow_parent.new_child_compile(expr.span, "output port target");
                                let AssignmentTarget {
                                    base: target_base,
                                    steps: target_steps,
                                } = ctx.eval_expression_as_assign_target(scope, &mut flow, expr)?;

                                // double-check that the steps are compile-time, dynamic steps don't make sense for output ports
                                for step in &target_steps.steps {
                                    match &step.step {
                                        TargetStep::Compile(_) => {}
                                        TargetStep::Hardware(_) => {
                                            // cannot happen, the expr was evaluated in a compile-time context
                                            let msg = "non-compile step in output port connection";
                                            return Err(diags.report_error_internal(step.span_step, msg));
                                        }
                                    }
                                }

                                // double check that the base is a signal
                                let target_base_span = target_base.span;
                                let target_base = match target_base.inner {
                                    SignalOrVariable::Signal(base) => base,
                                    SignalOrVariable::Variable(_) => {
                                        let msg = "variable in output port connection";
                                        return Err(diags.report_error_internal(expr.span, msg));
                                    }
                                };

                                // figure out base info
                                let (base_ty, base_ir) = match target_base {
                                    Signal::Port(base) => {
                                        // port has fixed info, just get it
                                        let port_info = &ctx.ports[base];
                                        (port_info.ty.clone(), IrSignal::Port(port_info.ir))
                                    }
                                    Signal::Wire(base) => {
                                        // wire info can still be suggested
                                        let wire_info = &mut ctx.wires[base];
                                        let wire_typed = if target_steps.is_empty() {
                                            wire_info.suggest_ty(
                                                refs,
                                                &ctx.wire_interfaces,
                                                &mut self.ir_signals.wires,
                                                port_ty.as_ref(),
                                            )
                                        } else {
                                            wire_info.expect_typed(refs, &ctx.wire_interfaces, target_base_span)
                                        }?;
                                        (wire_typed.ty.cloned(), IrSignal::Wire(wire_typed.ir))
                                    }
                                };

                                // check type
                                let no_vars = IrVariables::new();
                                let (target_ty, steps_ir) = target_steps.apply_to_hardware_type(
                                    refs,
                                    &mut ctx.large,
                                    &self.ir_signals,
                                    &no_vars,
                                    Spanned::new(target_base_span, &base_ty.inner),
                                )?;

                                let reason = TypeContainsReason::InstancePortOutput {
                                    span_target: expr.span,
                                    span_target_ty: base_ty.span,
                                    span_port_ty: port_ty.span,
                                };
                                check_type_contains_type(
                                    refs,
                                    reason,
                                    &target_ty.as_type(),
                                    Spanned::new(connection_id.span(), &port_ty.inner.as_type()),
                                )?;

                                // if there are any steps or if we need type expansion,
                                //   we need an intermediate combinatorial process
                                let expansion = if steps_ir.is_empty() && base_ty.inner == port_ty.inner {
                                    None
                                } else {
                                    Some((target_ty, steps_ir))
                                };

                                DelayedConnection::PortOutput {
                                    target_base,
                                    target_ir: base_ir,
                                    expansion,
                                }
                            }
                        }
                    }
                };

                Ok(InstanceConnectionInfo {
                    span: connection_span,
                    singles: vec![(connector_single, signal)],
                    delayed,
                })
            }
            ConnectorKind::Interface {
                domain: _,
                view: connector_view,
                singles: connector_singles,
            } => {
                // eval expr
                let mut flow_connection = flow_parent.new_child_isolated();
                let value_eval = ctx
                    .eval_expression_as_lr(scope, &mut flow_connection, &Type::Any, expr)?
                    .resolve_reference_fields(ctx, &mut flow_connection)?;

                // expect interface
                let value_eval = match value_eval {
                    LrValue::LeftInterface(info) => info,
                    LrValue::LeftTarget(_) | LrValue::Right(_) => {
                        let e = DiagnosticError::new("expected interface value", expr.span, "got non-interface value")
                            .add_info(connector_id.span(), "port defined as interface here")
                            .report(diags);
                        return Err(e);
                    }
                };

                // check interface (including generics) and shape match
                let connector_interface = connector_view.map_inner(|v| v.interface);
                if connector_interface.inner != value_eval.elab.inner {
                    let diag = DiagnosticError::new("interface mismatch", expr.span, "got mismatching interface")
                        .add_info(
                            connector_interface.span,
                            format!(
                                "expected interface `{}` set here",
                                connector_interface.inner.value_string(refs)
                            ),
                        )
                        .add_info(
                            value_eval.elab.span,
                            format!(
                                "actual interface `{}` set here",
                                value_eval.elab.inner.value_string(refs)
                            ),
                        )
                        .report(diags);
                    return Err(diag);
                }
                if connector_singles.shape() != value_eval.intf.shape() {
                    let diag = DiagnosticError::new(
                        "interface array shape mismatch",
                        expr.span,
                        format!("got {}", describe_interface_shape(value_eval.intf.shape())),
                    )
                    .add_info(
                        connector_id.span(),
                        format!("expected {}", describe_interface_shape(connector_singles.shape())),
                    )
                    .report(diags);
                    return Err(diag);
                }
                let elements = connector_singles
                    .zip(&value_eval.intf)
                    .map_err(|_| diags.report_error_internal(expr.span, "interface shape mismatch after check"))?;

                let interface_info = refs
                    .shared
                    .elaboration_arenas
                    .interface_info(connector_view.inner.interface);
                let view_info = &interface_info.views[connector_view.inner.view_index];

                let port_dirs = view_info.port_dirs.as_ref_ok()?;
                let any_input = port_dirs.iter().any(|(_, d)| d.inner.is_input());
                let any_output = port_dirs.iter().any(|(_, d)| d.inner.is_output());

                // check directions and build connections
                let mut singles = vec![];
                let mut ir_connections = vec![];
                for (element_singles, &element_intf) in elements {
                    for (port_index, &(_, connector_dir)) in enumerate(port_dirs.iter()) {
                        let value_ir = element_intf.signal_ir(ctx, port_index);
                        let (value_dir, value_signal) = match element_intf {
                            Interface::Port(port_interface) => {
                                let port_interface_info = &ctx.port_interfaces[port_interface];
                                let port = port_interface_info.ports[port_index];
                                let dir = (ctx.ports[port].direction, port_interface_info.view.span);
                                (Some(dir), Signal::Port(port))
                            }
                            Interface::Wire(wire_interface) => (
                                None,
                                Signal::Wire(ctx.wire_interfaces[wire_interface].wires[port_index]),
                            ),
                        };

                        // check direction
                        if let Some((value_dir, value_view_span)) = value_dir
                            && connector_dir.inner != value_dir.inner
                        {
                            let signal_id_str = interface_info.signals[port_index].id.inner.str(interner);
                            let diag = DiagnosticError::new(
                                format!("direction mismatch for interface port `{}`", signal_id_str),
                                expr.span,
                                format!("got direction `{}`", value_dir.inner.diagnostic_string()),
                            )
                            .add_info(
                                connection_id.span(),
                                format!("expected direction `{}`", connector_dir.inner.diagnostic_string()),
                            )
                            .add_info(connector_dir.span, "expected direction set here")
                            .add_info(value_dir.span, "actual direction set here")
                            .add_info(value_view_span, "port interface view set here")
                            .report(diags);
                            return Err(diag);
                        }

                        // build connection
                        let ir_connection = match connector_dir.inner {
                            PortDirection::Input => IrPortConnection::Input(value_ir),
                            PortDirection::Output => IrPortConnection::Output(Some(value_ir)),
                        };
                        let signal = ConnectionSignal::Signal(Polarized {
                            inverted: false,
                            signal: value_signal,
                        });
                        singles.push((element_singles[port_index], signal));
                        ir_connections.push(ir_connection);
                    }
                }

                Ok(InstanceConnectionInfo {
                    span: connection_span,
                    singles,
                    delayed: DelayedConnection::Interface {
                        values: value_eval.intf.flat_values().to_vec(),
                        any_input,
                        any_output,
                        ir_connections,
                    },
                })
            }
        }
    }

    fn finish_instance_port_connection(
        &mut self,
        ctx: &mut CompileItemContext,
        connectors: &ArenaConnectors,
        single_to_signal: &IndexMap<ConnectorSingle, ConnectionSignal>,
        connector: Connector,
        connection_id_span: Span,
        info: InstanceConnectionInfo,
    ) -> DiagResult<Vec<Spanned<IrPortConnection>>> {
        let refs = ctx.refs;
        let diags = refs.diags;
        let interner = &refs.shared.interner;

        let ConnectorInfo {
            id: connector_id,
            kind: connector_kind,
        } = &connectors[connector];
        let InstanceConnectionInfo {
            span: connection_span,
            singles: _,
            delayed,
        } = info;

        // replace signals that are earlier ports with their connected value
        let map_domain_kind = |domain_span: Span, domain: DomainKind<Polarized<ConnectorSingle>>| {
            Ok(match domain {
                DomainKind::Const => DomainKind::Const,
                DomainKind::Async => DomainKind::Async,
                DomainKind::Sync(sync) => DomainKind::Sync(sync.try_map_signal(|raw_port| {
                    let mapped_port = match single_to_signal.get(&raw_port.signal) {
                        None => {
                            return Err(
                                diags.report_error_internal(connection_span, "failed to get signal for previous port")
                            );
                        }
                        Some(&ConnectionSignal::Error(e)) => Err(e),
                        Some(&ConnectionSignal::Dummy(dummy_span)) => {
                            let diag = DiagnosticError::new_todo(
                                "dummy port connections used in the domain of other ports",
                                dummy_span,
                            )
                            .add_info(domain_span, "port used in a domain here")
                            .report(diags);
                            return Err(diag);
                        }
                        Some(&ConnectionSignal::Expression(expr_span)) => {
                            let diag = DiagnosticError::new_todo(
                                "general expression port connections used in the domain of other ports",
                                expr_span,
                            )
                            .add_info(domain_span, "port used in a domain here")
                            .report(diags);
                            return Err(diag);
                        }
                        Some(&ConnectionSignal::Signal(signal)) => Ok(signal),
                    }?;
                    Ok(Polarized {
                        signal: mapped_port.signal,
                        inverted: mapped_port.inverted ^ raw_port.inverted,
                    })
                })?),
            })
        };

        let connector_domain = match connector_kind.as_ref_ok()? {
            ConnectorKind::Port { domain, .. } => domain
                .map_inner(|d| match d {
                    PortDomain::Clock => Ok(ValueDomain::Clock),
                    PortDomain::Kind(kind) => Ok(ValueDomain::from_domain_kind(map_domain_kind(domain.span, kind)?)),
                })
                .transpose()?,
            ConnectorKind::Interface { domain, .. } => domain
                .map_inner(|d| Ok(ValueDomain::from_domain_kind(map_domain_kind(domain.span, d)?)))
                .transpose()?,
        };

        let result = match delayed {
            DelayedConnection::PortInput {
                source_domain,
                signal_ir,
            } => {
                let target_domain = Spanned::new(connection_id_span, connector_domain.inner);
                ctx.check_valid_domain_crossing(
                    connection_span,
                    source_domain,
                    target_domain,
                    "input port connection",
                )?;
                vec![IrPortConnection::Input(signal_ir)]
            }
            DelayedConnection::PortOutputDummy => vec![IrPortConnection::Output(None)],
            DelayedConnection::PortOutput {
                target_base,
                target_ir,
                expansion,
            } => {
                let base_domain = target_base.suggest_domain(ctx, connector_domain)?;
                ctx.check_valid_domain_crossing(
                    connection_span,
                    connector_domain,
                    base_domain,
                    "output port connection",
                )?;

                let connection_signal_ir = match expansion {
                    None => target_ir,
                    Some((target_ty, steps_ir)) => {
                        let port_ty = match connector_kind.as_ref_ok()? {
                            ConnectorKind::Port { ty, .. } => ty,
                            ConnectorKind::Interface { .. } => {
                                let msg = "expected port connector for port connection";
                                return Err(diags.report_error_internal(connection_span, msg));
                            }
                        };

                        // create intermediate wire, with the port type
                        let wire_raw = self.ir_signals.wires.push(IrWireInfo {
                            ty: port_ty.inner.as_ir(refs),
                            debug_info_id: connector_id.map_inner(|id| Some(id.str(interner).to_owned())),
                            debug_info_ty: port_ty.inner.value_string(refs),
                            debug_info_domain: connector_domain.inner.diagnostic_string(ctx).to_owned(),
                        });

                        // create type expansion expression
                        let value_raw = HardwareValue {
                            ty: port_ty.inner.clone(),
                            domain: connector_domain.inner,
                            expr: wire_raw.as_expression(),
                        };
                        let value_expanded =
                            value_raw.as_ir_expression_unchecked(refs, &mut ctx.large, connection_span, &target_ty)?;

                        // create combinatorial process that assigns the expanded value to the real target signal
                        let target_ir = IrAssignmentTarget {
                            base: target_ir.into(),
                            steps: steps_ir,
                        };
                        let stmt = IrStatement::Assign(target_ir, value_expanded);
                        let process = IrCombinatorialProcess {
                            variables: IrVariables::new(),
                            block: IrBlock {
                                statements: vec![Spanned::new(connection_span, stmt)],
                            },
                        };
                        let child = IrModuleChild::CombinatorialProcess(process);
                        self.children.push(Spanned::new(connection_span, child));

                        // connect the port to the intermediate wire
                        IrSignal::Wire(wire_raw)
                    }
                };

                vec![IrPortConnection::Output(Some(connection_signal_ir))]
            }
            DelayedConnection::Interface {
                values,
                any_input,
                any_output,
                ir_connections,
            } => {
                for element_intf in values {
                    let value_domain = element_intf.suggest_domain(ctx, connector_domain)?;

                    let mut any_err_domain = Ok(());
                    if any_input {
                        let r = ctx.check_valid_domain_crossing(
                            connection_span,
                            value_domain,
                            connector_domain,
                            "interface connection with input port",
                        );
                        any_err_domain = any_err_domain.and(r);
                    }
                    if any_output {
                        let r = ctx.check_valid_domain_crossing(
                            connection_span,
                            connector_domain,
                            value_domain,
                            "interface connection with output port",
                        );
                        any_err_domain = any_err_domain.and(r);
                    }
                    any_err_domain?;
                }

                ir_connections
            }
        };

        Ok(result.into_iter().map(|c| Spanned::new(connection_span, c)).collect())
    }
}

/// Suggest and check domains in an interface connect statement.
///
/// Implemented by repeatedly finding any driver with a known domain, and then suggesting that domain to all sinks.
/// This allows domains to propagate as much as possible.
fn connect_domains_suggest_and_check(
    ctx: &mut CompileItemContext,
    span_keyword: Span,
    entries: &[Spanned<Interface>],
    signal_drivers: &[usize],
) -> DiagResult {
    let diags = ctx.refs.diags;

    let mut any_err = Ok(());
    let mut pending = signal_drivers.iter().copied().unique().collect_vec();
    loop {
        let pending_len_before = pending.len();

        // find the next driver with a known domain
        let mut i = 0;
        while i < pending.len() {
            let source = pending[i];
            let Some(source_domain) = entries[source].inner.domain(ctx)? else {
                i += 1;
                continue;
            };

            // iterate over all sinks
            for (sink, sink_entry) in enumerate(entries) {
                if sink == source {
                    continue;
                }

                // suggest and check domain source->sink
                let sink_domain = sink_entry.inner.suggest_domain(ctx, source_domain)?;
                let curr_err = ctx.check_valid_domain_crossing(
                    sink_entry.span,
                    source_domain,
                    sink_domain,
                    "interface connection",
                );
                any_err = any_err.and(curr_err);
            }
            pending.remove(i);
        }

        // if done or not making progress
        if pending.is_empty() || pending.len() == pending_len_before {
            break;
        }
    }

    // if we're not done, report error
    if !pending.is_empty() {
        let mut diag = DiagnosticError::new(
            "cannot infer domain for connection between wires",
            span_keyword,
            "connection here",
        );
        for &driver in &pending {
            diag = diag.add_info(entries[driver].span, "driver has no known domain");
        }
        return Err(diag
            .add_footer_hint("declare the domain of the driving wires")
            .report(diags));
    }

    any_err
}

fn try_extract_simple_port_input_signal(block: &IrBlock, expr: &IrExpression) -> Option<IrSignal> {
    let IrBlock { statements } = block;

    // expr signal, block empty
    if let &IrExpression::Signal(signal) = expr
        && statements.is_empty()
    {
        return Some(signal);
    }

    // expr variable, block only contains assignment of signal to that variable
    if let &IrExpression::Variable(var_expr) = expr
        && let Some(stmt) = statements.single_ref()
        && let IrStatement::Assign(
            IrAssignmentTarget {
                base: IrSignalOrVariable::Variable(var_assign),
                ref steps,
            },
            IrExpression::Signal(signal),
        ) = stmt.inner
        && steps.is_empty()
        && var_assign == var_expr
    {
        return Some(signal);
    }

    None
}

pub fn describe_interface_shape(shape: NdArrayShape) -> String {
    match shape {
        NdArrayShape::Scalar => "a single interface".to_owned(),
        NdArrayShape::Array { .. } => {
            format!("an interface array with shape `{}`", shape_string(&shape.to_vec()))
        }
    }
}
