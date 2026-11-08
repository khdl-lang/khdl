use crate::front::block::EarlyExitKind;
use crate::front::compile::CompileRefs;
use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::front::expression::eval_binary_bool_typed;
use crate::front::flow::{Flow, FlowKind, Variable, VariableInfo};
use crate::front::implication::HardwareValueWithImplications;
use crate::front::types::{HardwareType, Type, TypeBool};
use crate::front::value::{MaybeCompile, SimpleCompileValue, Value};
use crate::mid::ir::{IrBoolBinaryOp, IrLargeArena, IrType, IrVariableInfo};
use crate::syntax::ast::MaybeIdentifier;
use crate::syntax::pos::{Span, Spanned};
use unwrap_match::unwrap_match;

pub struct ExitStack<'r> {
    inside_block_expression: Option<InsideBlockExpression>,
    return_info: Option<ReturnEntry<'r>>,
    stack: Vec<LoopEntry>,
}

#[derive(Debug, Copy, Clone)]
pub struct InsideBlockExpression(pub Span);

#[derive(Debug)]
pub struct ReturnEntry<'r> {
    pub span_function_decl: Span,

    pub return_type: Option<Spanned<&'r Type>>,
    pub return_var: Option<Variable>,

    pub kind: ReturnEntryKind,
}

#[derive(Debug)]
pub enum ReturnEntryKind {
    Compile,
    Hardware(ReturnEntryHardware),
}

#[derive(Debug)]
pub struct ReturnEntryHardware {
    pub return_flag: ExitFlag,
}

#[derive(Debug)]
pub enum LoopEntry {
    Compile,
    Hardware(LoopEntryHardware),
}

#[derive(Debug)]
pub struct LoopEntryHardware {
    pub break_flag: ExitFlag,
    pub continue_flag: ExitFlag,
}

#[derive(Debug)]
pub struct ExitFlag {
    var: Variable,
}

impl LoopEntry {
    // TODO use Variable instead of IrVariable to get const prop, implications and joining for free
    pub fn new(refs: CompileRefs, flow: &mut impl Flow, span_keyword: Span) -> DiagResult<LoopEntry> {
        match flow.kind_mut() {
            FlowKind::Compile(_) => Ok(LoopEntry::Compile),
            FlowKind::Hardware(flow) => {
                let entry = LoopEntryHardware {
                    break_flag: ExitFlag::new(refs, flow, span_keyword, EarlyExitKind::Break)?,
                    continue_flag: ExitFlag::new(refs, flow, span_keyword, EarlyExitKind::Continue)?,
                };

                Ok(LoopEntry::Hardware(entry))
            }
        }
    }
}

impl ExitFlag {
    pub fn new(refs: CompileRefs, flow: &mut impl Flow, span: Span, kind: EarlyExitKind) -> DiagResult<ExitFlag> {
        // crate variable
        let name = match kind {
            EarlyExitKind::Return => "flag_function_return",
            EarlyExitKind::Break => "flag_loop_break",
            EarlyExitKind::Continue => "flag_loop_continue",
        };

        let use_ir_variable = match flow.kind_mut() {
            FlowKind::Compile(_) => None,
            FlowKind::Hardware(flow) => {
                let info = IrVariableInfo {
                    ty: IrType::Bool,
                    debug_info_span: span,
                    debug_info_id: Some(name.to_owned()),
                };
                Some(flow.new_ir_variable(info))
            }
        };

        let id = MaybeIdentifier::Identifier(refs.shared.interner.push(name));
        let info = VariableInfo {
            span_decl: span,
            id,
            mutable: true,
            ty: Some(Spanned::new(span, Type::Bool)),
            join_ir_variable: use_ir_variable,
        };
        let var = flow.var_new(info);

        // initialize to false
        flow.var_set(refs, var, span, Ok(Value::new_bool(false)))?;

        Ok(Self { var })
    }

    pub fn clear(&mut self, refs: CompileRefs, flow: &mut impl Flow, span: Span) -> DiagResult {
        flow.var_set(refs, self.var, span, Ok(Value::new_bool(false)))
    }

    pub fn set(&mut self, refs: CompileRefs, flow: &mut impl Flow, span: Span) -> DiagResult {
        flow.var_set(refs, self.var, span, Ok(Value::new_bool(true)))
    }

    pub fn get(
        &self,
        refs: CompileRefs,
        diags: &Diagnostics,
        large: &mut IrLargeArena,
        flow: &mut impl Flow,
        span: Span,
    ) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
        match flow.var_eval(refs, large, Spanned::new(span, self.var)) {
            Ok(value) => {
                let value = match value {
                    Value::Simple(value) => {
                        let value = unwrap_match!(value, SimpleCompileValue::Bool(value) => value);
                        MaybeCompile::Compile(value)
                    }
                    Value::Compound(_) => panic!("unexpected compound value for exit flag"),
                    Value::Hardware(value) => {
                        assert_eq!(value.value.ty, HardwareType::Bool);
                        MaybeCompile::Hardware(value.map_type(|_| TypeBool))
                    }
                };
                Ok(value)
            }
            Err(_) => Err(diags.report_error_internal(span, "flag evaluation should never fail")),
        }
    }
}

impl<'r> ExitStack<'r> {
    pub fn new_root() -> Self {
        Self {
            inside_block_expression: None,
            return_info: None,
            stack: vec![],
        }
    }

    pub fn new_in_function(return_info: ReturnEntry<'r>) -> Self {
        Self {
            inside_block_expression: None,
            return_info: Some(return_info),
            stack: vec![],
        }
    }

    pub fn new_in_block_expression(span: Span) -> Self {
        Self {
            inside_block_expression: Some(InsideBlockExpression(span)),
            return_info: None,
            stack: vec![],
        }
    }

    pub fn early_exit_condition(
        &mut self,
        refs: CompileRefs,
        diags: &Diagnostics,
        large: &mut IrLargeArena,
        flow: &mut impl Flow,
        span: Span,
    ) -> DiagResult<MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>> {
        let mut add_flag = |c: MaybeCompile<bool, HardwareValueWithImplications<TypeBool>>, flag: &ExitFlag| {
            let flag = flag.get(refs, diags, large, flow, span)?;
            Ok(eval_binary_bool_typed(large, IrBoolBinaryOp::Or, c, flag))
        };

        let mut exit_cond = MaybeCompile::Compile(false);
        if let Some(entry) = self.return_info_option()
            && let ReturnEntryKind::Hardware(entry) = &entry.kind
        {
            exit_cond = add_flag(exit_cond, &entry.return_flag)?;
        }
        if let Some(LoopEntry::Hardware(entry)) = self.innermost_loop_option() {
            exit_cond = add_flag(exit_cond, &entry.break_flag)?;
            exit_cond = add_flag(exit_cond, &entry.continue_flag)?;
        }

        Ok(exit_cond)
    }

    pub fn with_loop_entry<R>(&mut self, entry: LoopEntry, f: impl FnOnce(&mut ExitStack) -> R) -> R {
        self.stack.push(entry);
        let result = f(self);
        self.stack.pop().unwrap();
        result
    }

    pub fn return_info_option(&mut self) -> Option<&mut ReturnEntry<'r>> {
        self.return_info.as_mut()
    }

    pub fn return_info(&mut self, diags: &Diagnostics, span_return: Span) -> DiagResult<&mut ReturnEntry<'r>> {
        match &mut self.return_info {
            None => match self.inside_block_expression {
                None => Err(diags.report_error_simple(
                    "return can only be used inside a function",
                    span_return,
                    "attempt to return here",
                )),
                Some(InsideBlockExpression(span_block)) => {
                    Err(DiagnosticError::new_todo("return inside block expression", span_return)
                        .add_info(span_block, "inside this block expression")
                        .report(diags))
                }
            },
            Some(entry) => Ok(entry),
        }
    }

    pub fn innermost_loop_option(&mut self) -> Option<&mut LoopEntry> {
        self.stack.last_mut()
    }

    pub fn innermost_loop(
        &mut self,
        diags: &Diagnostics,
        span_reason: Span,
        reason: &str,
    ) -> DiagResult<&mut LoopEntry> {
        let inside_block_expression = self.inside_block_expression;

        self.innermost_loop_option()
            .ok_or_else(|| match inside_block_expression {
                None => diags.report_error_simple(
                    format!("{} can only be used inside a loop", reason),
                    span_reason,
                    format!("attempt to {} here", reason),
                ),
                Some(InsideBlockExpression(span_block)) => {
                    DiagnosticError::new_todo(format!("{} inside block expression", reason), span_reason)
                        .add_info(span_block, "inside this block expression")
                        .report(diags)
                }
            })
    }
}
