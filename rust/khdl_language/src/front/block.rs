use crate::front::assignment::AssignmentTarget;
use crate::front::check::{
    TypeContainsReason, check_port_is_output, check_type_contains_value, check_type_is_bool, check_type_is_bool_compile,
};
use crate::front::compile::CompileItemContext;
use crate::front::diagnostic::{DiagResult, DiagnosticError, DiagnosticWarning, Diagnostics};
use crate::front::domain::ValueDomain;
use crate::front::exit::{ExitStack, LoopEntry, ReturnEntryKind};
use crate::front::expression::ForIterator;
use crate::front::flow::{
    Flow, FlowHardware, FlowKind, HardwareProcessKind, ImplicationContradiction, RegisterInfo, VariableInfo,
};
use crate::front::function::check_function_return_type_and_set_value;
use crate::front::implication::{HardwareValueWithImplications, ValueWithImplications};
use crate::front::scope::{NamedValue, Scope, ScopedEntry};
use crate::front::signal::{Signal, SignalOrVariable, WireInfo, WireInfoSingle};
use crate::front::types::{NonHardwareType, Type, TypeBool, Typed};
use crate::front::value::{CompileValue, MaybeCompile, MaybeUndefined, SimpleCompileValue, Value, ValueCommon};
use crate::mid::ir::{IrBlock, IrExpression, IrExpressionLarge, IrIfStatement, IrLargeArena, IrStatement};
use crate::syntax::ast::{
    Block, BlockStatement, BlockStatementKind, ConstBlock, ExpressionKind, ForStatement, IfCondBlockPair, IfStatement,
    MaybeIdentifier, RegisterDeclaration, RegisterDeclarationKind, RegisterDeclarationNew, RegisterDeclarationWire,
    ReturnStatement, VariableDeclaration, WhileStatement,
};
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::data::{IndexMapExt, VecExt};
use crate::util::intern::Id;
use indexmap::IndexMap;
use itertools::{Either, enumerate};
use unwrap_match::unwrap_match;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[must_use]
pub enum BlockEnd {
    /// No early exit, proceed normally.
    Normal,

    /// This block turns out to have been unreachable. This can happen for conditions that are in hindsight always
    /// false, for `assert(false)`-like constructs or in dead code after early exits.
    /// This [BlockEnd] is the bottom value of the lattice,
    /// for branch joining it should always decay and result in the other branches.
    Unreachable,

    /// Definite early exit, known at compile time.
    CompileExit(EarlyExitKind),

    /// Definite early exit, but the kind depends on hardware conditions.
    /// The mask indicates which kinds of exits are possible.
    HardwareExit(ExitMask<2>),

    /// Maybe early exit, but the kind and whether there is actually an exit depends on hardware conditions.
    /// The mask indicates which kinds of exits are possible.
    HardwareMaybeExit(ExitMask<1>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum EarlyExitKind {
    Return,
    Break,
    Continue,
}

/// Another encoding of [BlockEnd] that's easier to use for merging and joining.
#[derive(Debug, Copy, Clone)]
pub enum BlockEndFlags {
    /// Corresponds to [BlockEnd::Unreachable]
    Unreachable,
    /// Represents other [BlockEnd] variants.
    /// `certain_exit` indicates whether the block definitely exits early,
    /// `mask` indicates which kinds of exits are possible.
    Normal { certain_exit: bool, mask: ExitMask<0> },
}

/// A set of possible exit kinds.
/// The const generic [N] indicates the minimum number of exit kinds that are set.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ExitMask<const N: u8> {
    can_return: bool,
    can_break: bool,
    can_continue: bool,
}

impl BlockEnd {
    fn from_flags(flags: BlockEndFlags) -> BlockEnd {
        #[allow(clippy::collapsible_else_if)]
        match flags {
            BlockEndFlags::Unreachable => BlockEnd::Unreachable,
            BlockEndFlags::Normal { certain_exit, mask } => {
                if certain_exit {
                    if let Some(mask) = ExitMask::<2>::from_base(mask) {
                        // at least two options, so hardware-dependant exit
                        BlockEnd::HardwareExit(mask)
                    } else {
                        // at most one option, so definite compile-known exit
                        if mask.can_return {
                            BlockEnd::CompileExit(EarlyExitKind::Return)
                        } else if mask.can_break {
                            BlockEnd::CompileExit(EarlyExitKind::Break)
                        } else if mask.can_continue {
                            BlockEnd::CompileExit(EarlyExitKind::Continue)
                        } else {
                            unreachable!("certain exit but empty mask")
                        }
                    }
                } else {
                    if let Some(mask) = ExitMask::<1>::from_base(mask) {
                        // at least one option, so maybe exit
                        BlockEnd::HardwareMaybeExit(mask)
                    } else {
                        // no exit options, so normal
                        BlockEnd::Normal
                    }
                }
            }
        }
    }

    fn into_flags(self) -> BlockEndFlags {
        match self {
            BlockEnd::Normal => BlockEndFlags::Normal {
                certain_exit: false,
                mask: ExitMask::default(),
            },
            BlockEnd::Unreachable => BlockEndFlags::Unreachable,
            BlockEnd::CompileExit(kind) => BlockEndFlags::Normal {
                certain_exit: true,
                mask: ExitMask::from_kind(kind).into_base(),
            },
            BlockEnd::HardwareExit(mask) => BlockEndFlags::Normal {
                certain_exit: true,
                mask: mask.into_base(),
            },
            BlockEnd::HardwareMaybeExit(mask) => BlockEndFlags::Normal {
                certain_exit: false,
                mask: mask.into_base(),
            },
        }
    }

    pub fn should_stop_sequence(self) -> bool {
        match self {
            BlockEnd::Unreachable | BlockEnd::CompileExit(_) | BlockEnd::HardwareExit(_) => true,
            BlockEnd::Normal | BlockEnd::HardwareMaybeExit(_) => false,
        }
    }

    pub fn should_recheck_exit_flags(self) -> bool {
        match self {
            BlockEnd::HardwareMaybeExit(_) => true,
            BlockEnd::Normal | BlockEnd::Unreachable | BlockEnd::CompileExit(_) | BlockEnd::HardwareExit(_) => false,
        }
    }

    pub fn unwrap_normal(self, diags: &Diagnostics, span: Span) -> DiagResult {
        match self {
            BlockEnd::Normal => Ok(()),
            _ => Err(diags.report_error_internal(span, "unexpected early exit")),
        }
    }

    pub fn remove(self, mask_remove: ExitMask<0>) -> BlockEnd {
        match self.into_flags() {
            BlockEndFlags::Unreachable => BlockEnd::Unreachable,
            BlockEndFlags::Normal { certain_exit, mask } => {
                let result_mask = ExitMask {
                    can_return: mask.can_return & !mask_remove.can_return,
                    can_break: mask.can_break & !mask_remove.can_break,
                    can_continue: mask.can_continue & !mask_remove.can_continue,
                };

                let any_removed = result_mask != mask;
                let result_certain_exit = certain_exit && !any_removed;

                BlockEnd::from_flags(BlockEndFlags::Normal {
                    certain_exit: result_certain_exit,
                    mask: result_mask,
                })
            }
        }
    }
}

impl<const N: u8> ExitMask<N> {
    pub fn into_base(self) -> ExitMask<0> {
        ExitMask {
            can_return: self.can_return,
            can_break: self.can_break,
            can_continue: self.can_continue,
        }
    }

    pub fn from_base(mask: ExitMask<0>) -> Option<Self> {
        let count = mask.can_return as u8 + mask.can_break as u8 + mask.can_continue as u8;
        if count >= N {
            Some(ExitMask {
                can_return: mask.can_return,
                can_break: mask.can_break,
                can_continue: mask.can_continue,
            })
        } else {
            None
        }
    }

    pub fn absorb_loop(self) -> ExitMask<0> {
        ExitMask {
            can_return: self.can_return,
            can_break: false,
            can_continue: false,
        }
    }
}

impl<const N: u8> std::ops::BitOr for ExitMask<N> {
    type Output = ExitMask<N>;
    fn bitor(self, rhs: Self) -> Self::Output {
        ExitMask {
            can_return: self.can_return || rhs.can_return,
            can_break: self.can_break || rhs.can_break,
            can_continue: self.can_continue || rhs.can_continue,
        }
    }
}

impl Default for ExitMask<0> {
    fn default() -> Self {
        ExitMask {
            can_return: false,
            can_break: false,
            can_continue: false,
        }
    }
}

impl ExitMask<1> {
    pub fn from_kind(kind: EarlyExitKind) -> Self {
        let mut res = ExitMask {
            can_return: false,
            can_break: false,
            can_continue: false,
        };
        match kind {
            EarlyExitKind::Return => res.can_return = true,
            EarlyExitKind::Break => res.can_break = true,
            EarlyExitKind::Continue => res.can_continue = true,
        }
        res
    }
}

pub struct ElaboratedForHeader {
    pub index_id: MaybeIdentifier<Spanned<Id>>,
    pub index_ty: Option<Spanned<Type>>,
    pub iter: ForIterator,
}

impl CompileItemContext<'_, '_> {
    pub fn elaborate_const_block(&mut self, scope: &Scope, flow: &mut impl Flow, block: &ConstBlock) -> DiagResult {
        let diags = self.refs.diags;
        let &ConstBlock {
            span_keyword,
            ref block,
        } = block;

        let span = span_keyword.join(block.span);
        let mut flow_inner = flow.new_child_compile(span, "const block");

        let mut stack = ExitStack::new_root();
        let block_end = self.elaborate_block(scope, &mut flow_inner, &mut stack, block)?;
        block_end.unwrap_normal(diags, block.span)?;

        Ok(())
    }

    pub fn elaborate_block(
        &mut self,
        scope_parent: &Scope,
        flow_parent: &mut impl Flow,
        stack: &mut ExitStack,
        block: &Block<BlockStatement>,
    ) -> DiagResult<BlockEnd> {
        let &Block { span, ref statements } = block;

        // Create a new scope, necessary to ensure declarations don't leak into the parent scope.
        let mut scope = scope_parent.new_child(span);

        // Create a new scoped flow, not strictly necessary for correctness,
        //   but allows dropping variables that go out of scope immediately.
        match flow_parent.kind_mut() {
            FlowKind::Compile(flow_parent) => {
                let mut flow = flow_parent.new_child_scoped();
                self.elaborate_block_statements(&mut scope, &mut flow, stack, statements)
            }
            FlowKind::Hardware(flow_parent) => {
                let mut flow = flow_parent.new_child_scoped();
                self.elaborate_block_statements(&mut scope, &mut flow, stack, statements)
            }
        }
    }

    pub fn elaborate_block_statements(
        &mut self,
        scope: &mut Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        statements: &[BlockStatement],
    ) -> DiagResult<BlockEnd> {
        let diags = self.refs.diags;
        let span = if statements.is_empty() {
            return Ok(BlockEnd::Normal);
        } else {
            statements
                .first()
                .unwrap()
                .span()
                .join(statements.last().unwrap().span())
        };

        let end = match stack.early_exit_condition(self.refs, diags, &mut self.large, flow, span)? {
            MaybeCompile::Compile(exit_cond) => {
                if exit_cond {
                    return Err(diags
                        .report_error_internal(span, "compile-time early exit condition should be handled elsewhere"));
                }
                self.elaborate_block_statements_without_immediate_exit_check(scope, flow, stack, statements)?
            }
            MaybeCompile::Hardware(exit_cond) => {
                let flow = flow.require_hardware(span, "hardware exit condition")?;

                let exit_cond = Spanned::new(span, exit_cond);

                self.elaborate_hardware_if(flow, span, exit_cond, |slf, branch_flow, branch_cond| {
                    if branch_cond {
                        // early exit, do nothing
                        //   as far as block end merging is concerned this branch is not actually reachable,
                        //   since we should have exited earlier already
                        Ok(BlockEnd::Unreachable)
                    } else {
                        // no early exit, so actually run the statements
                        slf.elaborate_block_statements_without_immediate_exit_check(
                            scope,
                            branch_flow,
                            stack,
                            statements,
                        )
                    }
                })?
            }
        };
        Ok(end)
    }

    pub fn elaborate_block_statements_without_immediate_exit_check(
        &mut self,
        scope: &mut Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        statements: &[BlockStatement],
    ) -> DiagResult<BlockEnd> {
        let mut end_joined = BlockEnd::Normal;

        for (stmt_index, stmt) in enumerate(statements) {
            let end_curr = self.elaborate_statement(scope, flow, stack, stmt)?;
            end_joined = join_block_ends_sequence(end_joined, end_curr);

            if end_joined.should_stop_sequence() {
                break;
            }

            if end_curr.should_recheck_exit_flags() {
                // recurse and return, instead of continuing the loop
                let statements_rest = &statements[stmt_index + 1..];
                let end_rest = self.elaborate_block_statements(scope, flow, stack, statements_rest)?;
                return Ok(join_block_ends_sequence(end_joined, end_rest));
            }
        }

        Ok(end_joined)
    }

    fn elaborate_statement(
        &mut self,
        scope: &mut Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        stmt: &BlockStatement,
    ) -> DiagResult<BlockEnd> {
        let refs = self.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let stmt_span = stmt.span;
        let end = match &stmt.inner {
            BlockStatementKind::CommonDeclaration(decl) => {
                self.eval_and_declare_declaration(scope, flow, decl)?;
                BlockEnd::Normal
            }
            BlockStatementKind::VariableDeclaration(decl) => {
                let &VariableDeclaration {
                    span: _,
                    mutable,
                    id,
                    ty,
                    init,
                } = decl;

                // eval id
                let id_eval = self.eval_maybe_id(scope, flow, id)?;

                // eval ty
                let ty = ty.map(|ty| self.eval_expression_as_ty(scope, flow, ty)).transpose()?;

                // eval init
                let init_expected_ty = ty.as_ref().map_or(&Type::Any, |ty| &ty.inner);
                let init = init
                    .map(|init| self.eval_expression_with_implications(scope, flow, init_expected_ty, init))
                    .transpose()?;

                // check that init fits in type
                if let Some(ty) = &ty
                    && let Some(init) = &init
                {
                    let reason = TypeContainsReason::Assignment {
                        span_target: id.span(),
                        span_target_ty: ty.span,
                    };
                    check_type_contains_value(refs, reason, &ty.inner, init.as_ref())?;
                }

                // build variable
                let info = VariableInfo {
                    span_decl: id.span(),
                    id: id_eval.map_id(|id| id.inner),
                    mutable,
                    ty,
                    join_ir_variable: None,
                };
                let var = flow.var_new(info);

                // store initial value if there is one
                if let Some(init) = init {
                    flow.var_set(refs, var, decl.span, Ok(init.inner))?;
                }

                // declare entry
                let entry = ScopedEntry::Named(NamedValue::Variable(var));
                scope.declare(refs, id_eval, Ok(entry));

                BlockEnd::Normal
            }
            BlockStatementKind::RegisterDeclaration(decl) => {
                let &RegisterDeclaration {
                    span_keyword,
                    kind,
                    reset,
                } = decl;

                // check that we're in a clocked process
                let flow = flow.require_hardware(stmt_span, "register declaration")?;
                let err_process_kind = |kind: &str, span: Span| {
                    Err(DiagnosticError::new(
                        "registers cannot be declared outside of clocked processes",
                        stmt_span,
                        "trying to declare register here",
                    )
                    .add_info(span, format!("currently inside {kind}"))
                    .report(diags))
                };
                let domain = match flow.process_kind() {
                    HardwareProcessKind::ClockedProcessBody {
                        span_keyword: _,
                        domain,
                        registers: _,
                    } => *domain,
                    &mut HardwareProcessKind::CombinatorialProcessBody { span_keyword, .. } => {
                        return err_process_kind("a combinatorial process", span_keyword);
                    }
                    &mut HardwareProcessKind::WireExpression { span_init, .. } => {
                        return err_process_kind("a wire declaration", span_init);
                    }
                    &mut HardwareProcessKind::InstancePortConnection { span_connection, .. } => {
                        return err_process_kind("an instance port connection", span_connection);
                    }
                };
                fn reborrow_registers<'a, 'p>(
                    flow: &'a mut FlowHardware<'p>,
                ) -> &'a mut &'p mut IndexMap<Signal, RegisterInfo> {
                    match flow.process_kind() {
                        HardwareProcessKind::ClockedProcessBody { registers, .. } => registers,
                        _ => unreachable!(),
                    }
                }

                let signal = match kind {
                    RegisterDeclarationKind::Wire(decl) => {
                        let RegisterDeclarationWire {
                            span_keyword_wire,
                            target: target_expr,
                        } = decl;

                        // eval target
                        let target = self.eval_expression_as_assign_target(scope, flow, target_expr)?;
                        let AssignmentTarget { base, steps } = target;

                        let signal = match base.inner {
                            SignalOrVariable::Signal(signal) => signal,
                            SignalOrVariable::Variable(var) => {
                                let var_info = flow.var_info(Spanned::new(target_expr.span, var))?;
                                return Err(DiagnosticError::new(
                                    "expected existing signal for register wire declaration",
                                    target_expr.span,
                                    "found variable",
                                )
                                .add_info(span_keyword_wire, "expecting signal because this is a wire register")
                                .add_info(var_info.span_decl, "variable declared here")
                                .add_footer_hint("to declare a new register instead, remove the `wire` keyword")
                                .report(diags));
                            }
                        };
                        if !steps.is_empty() {
                            return Err(diags.report_error_todo(target_expr.span, "partial signal registers"));
                        }

                        // check direction
                        match signal {
                            Signal::Port(port) => {
                                let port_info = &self.ports[port];
                                check_port_is_output(
                                    diags,
                                    port_info,
                                    target_expr.span,
                                    "cannot drive an input port with a register",
                                    "declaring a register for an input port here",
                                )?;
                            }
                            Signal::Wire(_) => {}
                        }

                        // check that this is the first register declaration in this block with this signal
                        if let Some(prev_info) = reborrow_registers(flow).get(&signal) {
                            let diag = DiagnosticError::new(
                                format!("{} already marked as a register in this process", signal.kind_str()),
                                stmt_span,
                                "trying to mark as register here",
                            )
                            .add_info(prev_info.span, "previous declaration here")
                            .report(diags);
                            return Err(diag);
                        }

                        Spanned::new(target_expr.span, signal)
                    }
                    RegisterDeclarationKind::New(new) => {
                        let RegisterDeclarationNew { id, ty } = new;

                        // eval id
                        let id = self.eval_id(scope, flow, id)?;

                        // warning if declaring register with same name as signal
                        // TODO improve, only warn if the entry is actually a signal?
                        if let Ok(Some(prev_span)) = scope.try_find_for_diagnostic(id.inner) {
                            let id_str = id.inner.str(&self.refs.shared.interner);
                            DiagnosticWarning::new(
                                "declaring new register with name matching an existing scope entry",
                                stmt_span,
                                format!("declaring register `{id_str}` here"),
                            )
                            .add_info(prev_span, format!("existing entry `{id_str}` declared here"))
                            .add_footer_hint("to mark an existing signal as a register, use `reg wire`/`port` instead")
                            .report(diags);
                        }

                        // eval ty
                        let ty = ty
                            .map(|ty| self.eval_expression_as_ty_hardware(scope, flow, ty, "register type"))
                            .transpose()?;

                        // create new wire
                        let wire = self.wires.push(WireInfo::Single(WireInfoSingle {
                            id: MaybeIdentifier::Identifier(id),
                            domain: Ok(None),
                            typed: Ok(None),
                        }));

                        // suggest type
                        if let Some(ty) = ty {
                            self.wires[wire].suggest_ty(
                                refs,
                                &self.wire_interfaces,
                                flow.get_ir_wires_mut(),
                                ty.as_ref(),
                            )?;
                        }

                        // declare in scope
                        let entry = ScopedEntry::Named(NamedValue::Signal(wire.into()));
                        scope.declare(refs, MaybeIdentifier::Identifier(id), Ok(entry));

                        Spanned::new(id.span, Signal::Wire(wire))
                    }
                };

                // suggest domain
                let domain = domain.map_inner(ValueDomain::Sync);
                let domain_signal = signal.inner.suggest_domain(self, domain)?;
                self.check_valid_domain_crossing(span_keyword, domain, domain_signal, "register driving signal")?;

                // eval reset value, possibly suggesting a type
                let reset_value = match self.refs.get_expr_inner(reset) {
                    ExpressionKind::Undefined => MaybeUndefined::Undefined,
                    _ => {
                        // figure out expected type
                        let signal_ty = match signal.inner {
                            Signal::Port(port) => Some(self.ports[port].ty.as_ref()),
                            Signal::Wire(wire) => self.wires[wire]
                                .typed_maybe(refs, &self.wire_interfaces)?
                                .map(|info| info.ty),
                        };
                        let expected_ty = signal_ty.map(|ty| ty.inner.as_type()).unwrap_or(Type::Any);
                        let signal_ty_is_none = signal_ty.is_none();

                        // eval expression
                        let reason = Spanned::new(stmt_span, "register reset value");
                        let reset_value = self.eval_expression_as_compile(scope, flow, &expected_ty, reset, reason)?;

                        // suggest ty
                        if signal_ty_is_none {
                            let reset_ty = reset_value.inner.ty();
                            let reset_ty = reset_ty.as_hardware_type(elab).map_err(|_: NonHardwareType| {
                                diags.report_error_simple(
                                    "register reset value must be representable in hardware",
                                    reset_value.span,
                                    format!("got type `{}`", reset_ty.value_string(refs)),
                                )
                            })?;
                            signal.inner.suggest_ty(
                                self,
                                flow.get_ir_wires_mut(),
                                Spanned::new(reset.span, &reset_ty),
                            )?;
                        }

                        // check reset value type
                        let signal_ty = signal.inner.expect_ty(self, signal.span)?.cloned();
                        let reason = TypeContainsReason::Assignment {
                            span_target: signal.span,
                            span_target_ty: signal_ty.span,
                        };
                        check_type_contains_value(refs, reason, &signal_ty.inner.as_type(), reset_value.as_ref())?;

                        // convert reset value to ir expression
                        let reset_ir = reset_value.inner.as_ir_expression_unchecked(
                            refs,
                            &mut self.large,
                            reset.span,
                            &signal_ty.inner,
                        )?;
                        MaybeUndefined::Defined(reset_ir)
                    }
                };

                // collect info
                let signal_ir = signal.inner.expect_ir(self, signal.span)?;
                let register_info = RegisterInfo {
                    span: stmt_span,
                    ir: signal_ir,
                    reset: Spanned::new(reset.span, reset_value),
                };

                // re-borrow process kind to store register info
                let registers = match flow.process_kind() {
                    HardwareProcessKind::ClockedProcessBody { registers, .. } => registers,
                    _ => unreachable!(),
                };
                registers.insert_first(signal.inner, register_info);

                BlockEnd::Normal
            }
            BlockStatementKind::Assignment(stmt) => {
                self.elaborate_assignment(scope, flow, stmt)?;
                BlockEnd::Normal
            }
            &BlockStatementKind::Expression(expr) => {
                let _: Spanned<Value> = self.eval_expression(scope, flow, &Type::Any, expr)?;
                BlockEnd::Normal
            }
            BlockStatementKind::Block(inner_block) => self.elaborate_block(scope, flow, stack, inner_block)?,
            BlockStatementKind::If(stmt) => {
                let IfStatement {
                    span: _,
                    initial_if,
                    else_ifs,
                    final_else,
                } = stmt;

                self.elaborate_if_statement(scope, flow, stack, Some((initial_if, else_ifs)), final_else)?
            }
            BlockStatementKind::Match(stmt) => {
                let stmt = Spanned::new(stmt_span, stmt);
                self.elaborate_match_statement(scope, flow, stack, stmt.inner)?
            }
            BlockStatementKind::While(stmt) => {
                let stmt = Spanned::new(stmt_span, stmt);
                self.elaborate_while_statement(scope, flow, stack, stmt)?
            }
            BlockStatementKind::For(stmt) => {
                let stmt = Spanned::new(stmt_span, stmt);
                self.elaborate_for_statement(scope, flow, stack, stmt)?
            }
            BlockStatementKind::Return(stmt) => {
                let &ReturnStatement { span_return, ref value } = stmt;

                // set flag
                let entry = stack.return_info(diags, span_return)?;
                if let ReturnEntryKind::Hardware(entry) = &mut entry.kind {
                    entry.return_flag.set(flow, span_return)?;
                }

                // check type and store value
                let type_unit = Type::unit();
                let expected_ty = entry.return_type.map_or(&type_unit, |ty| ty.inner);
                let value = value
                    .map(|value| self.eval_expression_with_implications(scope, flow, expected_ty, value))
                    .transpose()?;

                check_function_return_type_and_set_value(refs, flow, entry, stmt_span, span_return, value)?;

                BlockEnd::CompileExit(EarlyExitKind::Return)
            }
            &BlockStatementKind::Break { span } => {
                let entry = stack.innermost_loop(diags, span, "break")?;
                if let LoopEntry::Hardware(entry) = entry {
                    entry.break_flag.set(flow, span)?;
                }
                BlockEnd::CompileExit(EarlyExitKind::Break)
            }
            &BlockStatementKind::Continue { span } => {
                let entry = stack.innermost_loop(diags, span, "continue")?;
                if let LoopEntry::Hardware(entry) = entry {
                    entry.continue_flag.set(flow, span)?;
                }
                BlockEnd::CompileExit(EarlyExitKind::Continue)
            }
        };
        Ok(end)
    }

    // TODO make this non-recursive for very deep if chains?
    fn elaborate_if_statement(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        ifs: Option<(
            &IfCondBlockPair<Block<BlockStatement>>,
            &[IfCondBlockPair<Block<BlockStatement>>],
        )>,
        final_else: &Option<Block<BlockStatement>>,
    ) -> DiagResult<BlockEnd> {
        let refs = self.refs;

        let (initial_if, remaining_ifs) = match ifs {
            Some(p) => p,
            None => {
                return match final_else {
                    None => Ok(BlockEnd::Normal),
                    Some(final_else) => {
                        return self.elaborate_block(scope, flow, stack, final_else);
                    }
                };
            }
        };

        let &IfCondBlockPair {
            span: _,
            span_if,
            cond,
            ref block,
        } = initial_if;
        let cond_span = cond.span;

        let cond = self.eval_expression_with_implications(scope, flow, &Type::Bool, cond)?;

        let reason = TypeContainsReason::IfCondition(span_if);
        let cond = check_type_is_bool(refs, reason, cond)?;

        match cond {
            // evaluate the if at compile-time
            MaybeCompile::Compile(cond_eval) => {
                // only visit the selected branch
                if cond_eval {
                    self.elaborate_block(scope, flow, stack, block)
                } else {
                    self.elaborate_if_statement(scope, flow, stack, remaining_ifs.split_first(), final_else)
                }
            }
            // evaluate the if in hardware, generating IR
            MaybeCompile::Hardware(cond_value) => {
                let flow = flow.require_hardware(cond_span, "hardware value")?;

                let cond_value = Spanned::new(cond_span, cond_value);
                self.elaborate_hardware_if(flow, span_if, cond_value, |slf, branch_flow, branch_cond| {
                    if branch_cond {
                        slf.elaborate_block(scope, branch_flow, stack, block)
                    } else {
                        slf.elaborate_if_statement(scope, branch_flow, stack, remaining_ifs.split_first(), final_else)
                    }
                })
            }
        }
    }

    fn elaborate_while_statement(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        stmt: Spanned<&WhileStatement>,
    ) -> DiagResult<BlockEnd> {
        let refs = self.refs;
        let diags = refs.diags;

        let &WhileStatement {
            span_keyword,
            cond,
            ref body,
        } = stmt.inner;

        self.elaborate_loop(
            flow,
            stack,
            span_keyword,
            std::iter::repeat(()),
            |slf, flow, stack, ()| {
                // eval condition
                let cond = slf.eval_expression_as_compile(
                    scope,
                    flow,
                    &Type::Bool,
                    cond,
                    Spanned::new(span_keyword, "while loop condition"),
                )?;

                // typecheck condition
                let reason = TypeContainsReason::WhileCondition(span_keyword);
                check_type_contains_value(refs, reason, &Type::Bool, cond.as_ref())?;
                let cond = match &cond.inner {
                    &CompileValue::Simple(SimpleCompileValue::Bool(b)) => b,
                    _ => {
                        let diag =
                            diags.report_error_internal(cond.span, "expected bool, should have been checked already");
                        return Err(diag);
                    }
                };

                // check condition
                if !cond {
                    return Ok(BlockEnd::CompileExit(EarlyExitKind::Break));
                }

                // elaborate body itself
                slf.elaborate_block(scope, flow, stack, body)
            },
        )
    }

    pub fn elaborate_for_statement_header<B>(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        stmt: &ForStatement<B>,
    ) -> DiagResult<ElaboratedForHeader> {
        let &ForStatement {
            span_keyword: _,
            index,
            index_ty,
            iter,
            body: _,
        } = stmt;

        let index_id = self.eval_maybe_id(scope, flow, index)?;
        let index_ty = index_ty
            .map(|index_ty| self.eval_expression_as_ty(scope, flow, index_ty))
            .transpose()?;
        let iter = self.eval_expression_as_for_iterator(scope, flow, iter)?;

        Ok(ElaboratedForHeader {
            index_id,
            index_ty,
            iter,
        })
    }

    pub fn elaborate_for_statement_iteration<B: HasSpan>(
        &mut self,
        scope: &mut Scope,
        flow: &mut impl Flow,
        stmt: &ForStatement<B>,
        index_id: MaybeIdentifier<Spanned<Id>>,
        index_ty: &Option<Spanned<Type>>,
        index_value: <ForIterator as Iterator>::Item,
    ) -> DiagResult {
        let refs = self.refs;

        // convert index to actual value
        let index_value = index_value.map_hardware(|h| h.map_expression(|h| h.into_expr(&mut self.large)));

        // typecheck index (if specified)
        if let Some(index_ty) = &index_ty {
            let curr_spanned = Spanned {
                span: stmt.iter.span,
                inner: &index_value,
            };
            let reason = TypeContainsReason::ForIndexType(index_ty.span);
            check_type_contains_value(refs, reason, &index_ty.inner, curr_spanned)?;
        }

        // store index in variable
        let var = flow.var_new_immutable_init(
            refs,
            index_id,
            stmt.span_keyword,
            Ok(ValueWithImplications::simple(index_value)),
        )?;

        // declare variable in scope
        scope.declare(refs, index_id, Ok(ScopedEntry::Named(NamedValue::Variable(var))));

        Ok(())
    }

    fn elaborate_for_statement(
        &mut self,
        scope_parent: &Scope,
        flow: &mut impl Flow,
        stack: &mut ExitStack,
        stmt: Spanned<&ForStatement<Block<BlockStatement>>>,
    ) -> DiagResult<BlockEnd> {
        let ElaboratedForHeader {
            index_id,
            index_ty,
            iter,
        } = self.elaborate_for_statement_header(scope_parent, flow, stmt.inner)?;

        self.elaborate_loop(
            flow,
            stack,
            stmt.inner.span_keyword,
            iter,
            |slf, flow, stack, index_value| {
                let mut scope_body = scope_parent.new_child(stmt.span);
                slf.elaborate_for_statement_iteration(
                    &mut scope_body,
                    flow,
                    stmt.inner,
                    index_id,
                    &index_ty,
                    index_value,
                )?;
                slf.elaborate_block(&scope_body, flow, stack, &stmt.inner.body)
            },
        )
    }

    fn elaborate_loop<F: Flow, T>(
        &mut self,
        flow: &mut F,
        stack: &mut ExitStack,
        span_keyword: Span,
        iter: impl Iterator<Item = T>,
        mut body: impl FnMut(&mut Self, &mut F, &mut ExitStack, T) -> DiagResult<BlockEnd>,
    ) -> DiagResult<BlockEnd> {
        let entry = LoopEntry::new(self.refs, flow, span_keyword)?;
        stack.with_loop_entry(entry, |stack| {
            let mut end_joined = BlockEnd::Normal;

            for iter_item in iter {
                self.refs.check_should_stop(span_keyword)?;

                // clear continue flag
                if let FlowKind::Hardware(flow) = flow.kind_mut() {
                    let entry =
                        unwrap_match!(stack.innermost_loop_option().unwrap(), LoopEntry::Hardware(entry) => entry);
                    entry.continue_flag.clear(flow, span_keyword)?;
                }

                // elaborate body
                //   the body is responsible for checking the exit flags, that's typically handled in elaborate_block
                let end_body_raw = body(self, flow, stack, iter_item)?;

                // stop continue, it shouldn't leak into the next iteration
                let end_body = end_body_raw.remove(ExitMask::from_kind(EarlyExitKind::Continue).into_base());

                // handle end and stop elaborating if possible
                end_joined = join_block_ends_sequence(end_joined, end_body);
                if end_joined.should_stop_sequence() {
                    break;
                }
            }

            // absorb break/continue, they don't leak out of the loop
            let mask_loop = ExitMask {
                can_break: true,
                can_continue: true,
                can_return: false,
            };
            Ok(end_joined.remove(mask_loop))
        })
    }

    fn elaborate_hardware_if(
        &mut self,
        flow: &mut FlowHardware,
        span: Span,
        cond: Spanned<HardwareValueWithImplications<TypeBool>>,
        mut f: impl FnMut(&mut Self, &mut FlowHardware, bool) -> DiagResult<BlockEnd>,
    ) -> DiagResult<BlockEnd> {
        let cond_domain = Spanned::new(cond.span, cond.inner.value.domain);

        // lower then
        let then_flow_end = match flow.new_child_branch(self, span, cond_domain, cond.inner.implications.if_true)? {
            Ok(mut then_flow) => {
                let then_end = f(self, &mut then_flow.as_flow(), true)?;
                let then_flow = then_flow.finish();
                Some((then_flow, then_end))
            }
            Err(ImplicationContradiction) => None,
        };

        // lower else
        let else_flow_end = match flow.new_child_branch(self, span, cond_domain, cond.inner.implications.if_false)? {
            Ok(mut else_flow) => {
                let else_end = f(self, &mut else_flow.as_flow(), false)?;
                let else_flow = else_flow.finish();
                Some((else_flow, else_end))
            }
            Err(ImplicationContradiction) => None,
        };

        // join
        match (then_flow_end, else_flow_end) {
            (Some(then_flow_end), Some(else_flow_end)) => {
                // both branches are possible
                let (then_flow, then_end) = then_flow_end;
                let (else_flow, else_end) = else_flow_end;

                // join flows
                let (then_block, else_block) =
                    flow.join_child_branches_pair(self.refs, &mut self.large, span, (then_flow, else_flow))?;

                // build if
                let ir_if = build_ir_if_statement(
                    &mut self.large,
                    cond.inner.value.expr,
                    Some(then_block),
                    Some(else_block),
                );
                if let Some(ir_if) = ir_if {
                    let ir_if = match ir_if {
                        Either::Left(ir_if) => IrStatement::Block(ir_if),
                        Either::Right(ir_if) => IrStatement::If(ir_if),
                    };
                    flow.push_ir_statement(Spanned::new(span, ir_if));
                }

                // join ends
                Ok(join_block_ends_branches(&[then_end, else_end]))
            }
            (Some(flow_end), None) | (None, Some(flow_end)) => {
                // only one branch is possible, so no need to build an if statement
                let (case_flow, case_end) = flow_end;

                let block = flow
                    .join_child_branches(self.refs, &mut self.large, span, vec![case_flow])?
                    .single()
                    .unwrap();

                flow.push_ir_statement(Spanned::new(span, IrStatement::Block(block)));

                Ok(case_end)
            }
            (None, None) => {
                // both branches contradict, this basically means this entire flow is unreachable,
                //  no need to do anything at all
                Ok(BlockEnd::Unreachable)
            }
        }
    }

    // TODO share code with normal if statement?
    // TODO make sure this works similarly to match statements
    // TODO move all control flow stuff to a separate module
    pub fn compile_if_statement_choose_block<'a, B>(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        if_stmt: &'a IfStatement<B>,
    ) -> DiagResult<Option<&'a B>> {
        let refs = self.refs;

        let IfStatement {
            span: _,
            initial_if,
            else_ifs,
            final_else,
        } = if_stmt;

        let mut eval_pair = |pair: &'a IfCondBlockPair<B>| {
            let &IfCondBlockPair {
                span: _,
                span_if,
                cond,
                ref block,
            } = pair;

            let cond = self.eval_expression_as_compile(
                scope,
                flow,
                &Type::Bool,
                cond,
                Spanned::new(span_if, "compile-time if condition"),
            )?;

            let reason = TypeContainsReason::IfCondition(span_if);
            let cond = check_type_is_bool_compile(refs, reason, cond)?;

            if cond { Ok(Some(block)) } else { Ok(None) }
        };

        if let Some(block) = eval_pair(initial_if)? {
            return Ok(Some(block));
        }
        for else_if in else_ifs {
            if let Some(block) = eval_pair(else_if)? {
                return Ok(Some(block));
            }
        }
        Ok(final_else.as_ref())
    }
}

fn join_block_ends_sequence(first: BlockEnd, second: BlockEnd) -> BlockEnd {
    match first.into_flags() {
        BlockEndFlags::Unreachable => BlockEnd::Unreachable,
        BlockEndFlags::Normal {
            certain_exit: first_certain_exit,
            mask: first_mask,
        } => {
            if first_certain_exit {
                first
            } else {
                match second.into_flags() {
                    BlockEndFlags::Unreachable => first,
                    BlockEndFlags::Normal {
                        certain_exit: second_certain_exit,
                        mask: second_mask,
                    } => BlockEnd::from_flags(BlockEndFlags::Normal {
                        certain_exit: second_certain_exit,
                        mask: first_mask | second_mask,
                    }),
                }
            }
        }
    }
}

pub fn join_block_ends_branches(ends: &[BlockEnd]) -> BlockEnd {
    let mut all_certain = true;
    let mut any_mask = ExitMask::<0>::default();
    let mut any_non_unreachable = false;

    for &end in ends {
        match end.into_flags() {
            BlockEndFlags::Unreachable => {
                // ignore unreachable branches, it's as if they don't exist
            }
            BlockEndFlags::Normal { certain_exit, mask } => {
                all_certain &= certain_exit;
                any_mask = any_mask | mask;
                any_non_unreachable = true;
            }
        }
    }

    if any_non_unreachable {
        BlockEnd::from_flags(BlockEndFlags::Normal {
            certain_exit: all_certain,
            mask: any_mask,
        })
    } else {
        BlockEnd::Unreachable
    }
}

fn build_ir_if_statement(
    large: &mut IrLargeArena,
    condition: IrExpression,
    then_block: Option<IrBlock>,
    else_block: Option<IrBlock>,
) -> Option<Either<IrBlock, IrIfStatement>> {
    // discard empty blocks
    let then_block = then_block.filter(|b| !b.statements.is_empty());
    let else_block = else_block.filter(|b| !b.statements.is_empty());

    // simplify constant condition
    if let IrExpression::Bool(condition) = condition {
        let block = if condition { then_block } else { else_block };
        return block.map(Either::Left);
    }

    // simplify if/else setup
    let res = match (then_block, else_block) {
        // both empty, emit nothing
        (None, None) => None,
        // only then, drop else
        (Some(then_block), None) => Some(IrIfStatement {
            condition,
            then_block,
            else_block: None,
        }),
        // only else, drop then and invert condition
        (None, Some(else_block)) => {
            let inverted_cond = large.push_expr(IrExpressionLarge::BoolNot(condition));
            Some(IrIfStatement {
                condition: inverted_cond,
                then_block: else_block,
                else_block: None,
            })
        }
        // both, emit the full if
        (Some(then_block), Some(else_block)) => Some(IrIfStatement {
            condition,
            then_block,
            else_block: Some(else_block),
        }),
    };

    res.map(Either::Right)
}
