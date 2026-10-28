use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::DiagResult;
use crate::front::flow::{Flow, FlowHardware};
use crate::front::item::{
    ElaboratedEnumInfo, ElaboratedInterface, ElaboratedInterfaceView, ElaboratedStructInfo, ElaborationArenas,
};
use crate::front::scope::Scope;
use crate::front::types::{HardwareType, Type};
use crate::front::value::{
    BoundMethod, CompileCompoundValue, CompileValue, EnumValue, HardwareValue, MixedCompoundValue, MixedString,
    RangeValue, ReferenceInner, SimpleCompileValue, StructValue, Value,
};
use crate::mid::ir::{
    IrBlock, IrExpression, IrExpressionLarge, IrForStatement, IrIfStatement, IrIntCompareOp, IrIntegerRadix,
    IrLargeArena, IrStatement, IrStringPiece, IrStringSubstitution, IrType, IrVariable, IrVariableInfo,
};
use crate::mid::steps::{IrTargetStepScalar, IrTargetSteps};
use crate::syntax::ast::{Expression, StringPiece};
use crate::syntax::hierarchy::SourceHierarchy;
use crate::syntax::pos::{Span, Spanned};
use crate::syntax::token::parse_token_string_middle;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::intern::Interner;
use crate::util::iter::IterExt;
use crate::util::range::{ClosedNonEmptyRange, ClosedRange, Range};
use crate::util::range_multi::{AnyMultiRange, MultiRange};
use itertools::{Itertools, enumerate, zip_eq};
use khdl_util::swrite;
use std::borrow::Cow;
use std::sync::Arc;

struct StringBuilder {
    pieces: Vec<StringPiece<String, HardwareValue>>,
}

impl StringBuilder {
    pub fn new() -> Self {
        Self { pieces: vec![] }
    }

    pub fn push_str<'s>(&mut self, value: impl Into<Cow<'s, str>>) {
        let value = value.into();

        if value.is_empty() {
            return;
        }

        if let Some(StringPiece::Literal(last)) = self.pieces.last_mut() {
            // concatenate adjacent literals to canonicalize
            last.push_str(&value);
        } else {
            // just push a new piece
            self.pieces.push(StringPiece::Literal(value.into_owned()))
        }
    }

    pub fn push_value(&mut self, refs: CompileRefs, value: &Value) {
        match value {
            Value::Simple(value) => self.push_str(value.value_string(refs)),
            Value::Compound(value) => match value {
                MixedCompoundValue::String(value) => {
                    let MixedString { pieces } = value.as_ref();
                    for piece in pieces {
                        match piece {
                            StringPiece::Literal(piece) => {
                                self.push_str(piece.as_str());
                            }
                            StringPiece::Substitute(piece) => {
                                self.pieces.push(StringPiece::Substitute(piece.clone()));
                            }
                        }
                    }
                }
                MixedCompoundValue::Range(value) => match value {
                    RangeValue::Compile(range) => {
                        self.push_str(range_value_string(range));
                    }
                    RangeValue::HardwareBounds(range) => {
                        let Range { start, end } = range.range();
                        self.push_str("Range(");
                        if let Some(start) = start {
                            self.push_value(refs, &Value::from(start.clone()));
                        }
                        self.push_str("..");
                        if let Some(end) = end {
                            self.push_value(refs, &Value::from(end.clone()));
                        }
                        self.push_str(")");
                    }
                    RangeValue::HardwareStartLength { start, length } => {
                        self.push_str("Range(");
                        self.push_value(refs, &Value::Hardware(start.clone().map_type(HardwareType::Int)));
                        self.push_str("+..");
                        self.push_str(length.to_string());
                        self.push_str(")");
                    }
                },
                MixedCompoundValue::Tuple(elements) => {
                    self.push_str("(");
                    for (elem, last) in elements.iter().with_last() {
                        self.push_value(refs, elem);
                        if !last {
                            self.push_str(", ");
                        }
                    }
                    if elements.len() == 1 {
                        self.push_str(",");
                    }
                    self.push_str(")");
                }
                MixedCompoundValue::Struct(value) => {
                    let &StructValue { ty, ref fields } = value;
                    let ty_info = refs.shared.elaboration_arenas.struct_info(ty);

                    self.push_str(&ty_info.debug_info_name);
                    self.push_str(".new(");
                    for ((field_name, field_value), last) in zip_eq(ty_info.fields.keys(), fields).with_last() {
                        self.push_str(field_name.str(&refs.shared.interner));
                        self.push_str("=");
                        self.push_value(refs, field_value);
                        if !last {
                            self.push_str(", ");
                        }
                    }
                    self.push_str(")");
                }
                MixedCompoundValue::Enum(value) => {
                    let &EnumValue {
                        ty,
                        variant,
                        ref payload,
                    } = value;
                    let ty_info = refs.shared.elaboration_arenas.enum_info(ty);

                    let (variant_name, _) = ty_info.variants.get_index(variant).unwrap();

                    self.push_str(&ty_info.debug_info_name);
                    self.push_str(".");
                    self.push_str(variant_name.str(&refs.shared.interner));
                    if let Some(payload) = payload {
                        self.push_str("(");
                        self.push_value(refs, payload);
                        self.push_str(")");
                    }
                }
                MixedCompoundValue::BoundMethod(bound) => {
                    let BoundMethod {
                        self_type,
                        self_value: _,
                        method,
                    } = bound;

                    self.push_str("<bound ");
                    self.push_str(self_type.value_string(refs));
                    self.push_str(".");
                    self.push_str(method.name.str(&refs.shared.interner));
                    self.push_str(">");
                }
            },
            Value::Hardware(value) => {
                self.pieces.push(StringPiece::Substitute(value.clone()));
            }
        }
    }

    pub fn finish(self) -> Vec<StringPiece<Arc<String>, HardwareValue>> {
        self.pieces
            .into_iter()
            .map(|piece| match piece {
                StringPiece::Literal(s) => StringPiece::Literal(Arc::new(s)),
                StringPiece::Substitute(v) => StringPiece::Substitute(v),
            })
            .collect_vec()
    }
}

impl CompileItemContext<'_, '_> {
    pub fn eval_string_literal(
        &mut self,
        scope: &Scope,
        flow: &mut impl Flow,
        pieces: &[StringPiece<Span, Expression>],
    ) -> DiagResult<Value> {
        let diags = self.refs.diags;

        let mut builder = StringBuilder::new();

        let mut any_err = Ok(());
        for &piece in pieces {
            match piece {
                StringPiece::Literal(piece_span) => {
                    let raw = self.refs.fixed.source.span_str(piece_span);
                    let escaped = parse_token_string_middle(raw)
                        .map_err(|_| diags.report_error_internal(piece_span, "failed to parse string token"))?;

                    if !escaped.is_empty() {
                        builder.push_str(escaped);
                    }
                }
                StringPiece::Substitute(piece_value) => {
                    let piece_value = self.eval_expression(scope, flow, &Type::Any, piece_value);
                    let piece_value = match piece_value {
                        Ok(v) => v,
                        Err(e) => {
                            any_err = Err(e);
                            continue;
                        }
                    };

                    builder.push_value(self.refs, &piece_value.inner);
                }
            }
        }

        any_err?;

        let pieces = builder.finish();
        let mixed_str = MixedString { pieces };
        Ok(Value::Compound(MixedCompoundValue::String(Arc::new(mixed_str))))
    }
}

pub fn hardware_print_string(
    refs: CompileRefs,
    flow: &mut FlowHardware,
    large: &mut IrLargeArena,
    span: Span,
    string: &MixedString,
) {
    let mut new_ir_var = |info| flow.new_ir_variable(info);
    let mut builder = IrStringBuilder { span, pieces: vec![] };
    let mut block = vec![];

    let MixedString { pieces } = string;
    for piece in pieces {
        match piece {
            StringPiece::Literal(s) => builder.push_str(s),
            StringPiece::Substitute(sub) => {
                block.extend(print_hardware_sub(refs, &mut new_ir_var, large, &mut builder, sub));
            }
        }
    }

    // flush any remaining pieces
    builder.print_and_clear(&mut block);

    // try to emit inline
    match block.len() {
        0 => {}
        1 => block.into_iter().for_each(|stmt| flow.push_ir_statement(stmt)),
        _ => flow.push_ir_statement(Spanned::new(span, IrStatement::Block(IrBlock { statements: block }))),
    }
}

struct IrStringBuilder {
    span: Span,
    pieces: Vec<IrStringPiece>,
}

impl IrStringBuilder {
    pub fn push_str(&mut self, s: &str) {
        if let Some(IrStringPiece::Literal(last)) = self.pieces.last_mut() {
            last.push_str(s);
        } else {
            self.pieces.push(IrStringPiece::Literal(s.to_owned()));
        }
    }

    pub fn push_sub(&mut self, sub: IrStringSubstitution) {
        self.pieces.push(IrStringPiece::Substitute(sub));
    }

    fn print_and_clear(&mut self, block: &mut Vec<Spanned<IrStatement>>) {
        if !self.pieces.is_empty() {
            let pieces = std::mem::take(&mut self.pieces);
            let stmt = IrStatement::Print(pieces);
            block.push(Spanned::new(self.span, stmt));
        }
    }
}

#[must_use]
fn print_hardware_sub(
    refs: CompileRefs,
    new_ir_var: &mut impl FnMut(IrVariableInfo) -> IrVariable,
    large: &mut IrLargeArena,
    builder: &mut IrStringBuilder,
    value: &HardwareValue,
) -> Vec<Spanned<IrStatement>> {
    let span = builder.span;
    let mut block_parent = vec![];

    match &value.ty {
        HardwareType::Undefined => {
            builder.push_str("undef");
        }
        HardwareType::Bool => {
            // sadly we can't directly print booleans in verilog, so we need to do a full branch
            //   we could generate some common utility function for this, but that complicates the IR
            builder.print_and_clear(&mut block_parent);

            let block_print = |s: &str| IrBlock {
                statements: vec![Spanned::new(
                    span,
                    IrStatement::Print(vec![StringPiece::Literal(s.to_owned())]),
                )],
            };
            let stmt = IrIfStatement {
                condition: value.expr.clone(),
                then_block: block_print("true"),
                else_block: Some(block_print("false")),
            };
            block_parent.push(Spanned::new(span, IrStatement::If(stmt)));
        }
        HardwareType::Int(_) => {
            let sub = IrStringSubstitution::Integer(value.expr.clone(), IrIntegerRadix::Decimal);
            builder.push_sub(sub);
        }
        HardwareType::Array(ty_inner, len) => {
            builder.push_str("[");

            let mut element_value = |index: IrExpression| {
                let step = IrTargetStepScalar::ArrayIndex(index);
                let element_expr = large.push_expr(IrExpressionLarge::Steps {
                    base: value.expr.clone(),
                    steps: IrTargetSteps::single(step),
                });
                HardwareValue {
                    ty: ty_inner.as_ref().clone(),
                    domain: value.domain,
                    expr: element_expr,
                }
            };

            if len.is_zero() {
                // empty array, don't do anything
            } else if len == &BigUint::ONE {
                // single element, just print it
                // TODO also do this for short arrays with simplem elements?
                let element_value = element_value(IrExpression::Int(BigInt::ZERO));
                block_parent.extend(print_hardware_sub(refs, new_ir_var, large, builder, &element_value));
            } else {
                // multiple elements, emit a loop
                // print any pending pieces before the loop
                builder.print_and_clear(&mut block_parent);

                // create index variable
                let range = ClosedNonEmptyRange {
                    start: BigInt::ZERO,
                    end: BigInt::from(len),
                };
                let index = new_ir_var(IrVariableInfo {
                    ty: IrType::Int(range.clone()),
                    debug_info_span: span,
                    debug_info_id: Some("i_str".to_owned()),
                });

                // print the element, clearing again immediately afterwards to force all statements into the loop
                let element_value = element_value(IrExpression::Variable(index));
                let mut element_block = print_hardware_sub(refs, new_ir_var, large, builder, &element_value);
                builder.print_and_clear(&mut element_block);

                // print comma
                let if_cond = IrExpressionLarge::IntCompare(
                    IrIntCompareOp::Lt,
                    IrExpression::Variable(index),
                    IrExpression::Int(len - 1),
                );
                let if_stmt = IrIfStatement {
                    condition: large.push_expr(if_cond),
                    then_block: IrBlock {
                        statements: vec![Spanned::new(
                            span,
                            IrStatement::Print(vec![StringPiece::Literal(", ".to_owned())]),
                        )],
                    },
                    else_block: None,
                };
                element_block.push(Spanned::new(span, IrStatement::If(if_stmt)));

                // push the loop
                let for_stmt = IrForStatement {
                    index,
                    range: ClosedRange::from(range),
                    block: IrBlock {
                        statements: element_block,
                    },
                };
                block_parent.push(Spanned::new(span, IrStatement::For(for_stmt)));
            }
            builder.push_str("]");
        }
        HardwareType::Tuple(element_types) => {
            builder.push_str("(");
            for (index, ty) in enumerate(element_types.as_ref()) {
                let step = IrTargetStepScalar::TupleIndex(index);
                let element_expr = large.push_expr(IrExpressionLarge::Steps {
                    base: value.expr.clone(),
                    steps: IrTargetSteps::single(step),
                });
                let element_value = HardwareValue {
                    ty: ty.clone(),
                    domain: value.domain,
                    expr: element_expr,
                };
                block_parent.extend(print_hardware_sub(refs, new_ir_var, large, builder, &element_value));
                if index < element_types.len() - 1 {
                    builder.push_str(", ");
                }
            }
            if element_types.len() == 1 {
                builder.push_str(",");
            }
            builder.push_str(")");
        }
        HardwareType::Struct(ty) => {
            let ty_info = refs.shared.elaboration_arenas.struct_info(ty.inner());
            let ty_fields_hw = &ty_info.hw.as_ref().unwrap().fields;

            builder.push_str(&ty_info.debug_info_name);
            builder.push_str(".new(");
            for (field_index, ((field_name, _), field_ty)) in enumerate(zip_eq(&ty_info.fields, ty_fields_hw)) {
                let step = IrTargetStepScalar::StructField(field_index);
                let field_expr = large.push_expr(IrExpressionLarge::Steps {
                    base: value.expr.clone(),
                    steps: IrTargetSteps::single(step),
                });
                let field_value = HardwareValue {
                    ty: field_ty.clone(),
                    domain: value.domain,
                    expr: field_expr,
                };

                builder.push_str(field_name.str(&refs.shared.interner));
                builder.push_str("=");
                block_parent.extend(print_hardware_sub(refs, new_ir_var, large, builder, &field_value));

                if field_index < ty_info.fields.len() - 1 {
                    builder.push_str(", ");
                }
            }
            builder.push_str(")");
        }
        HardwareType::Enum(ty) => {
            let ty_info = refs.shared.elaboration_arenas.enum_info(ty.inner());
            let ty_info_hw = ty_info.hw.as_ref().unwrap();

            builder.push_str(&ty_info.debug_info_name);
            builder.push_str(".");
            builder.print_and_clear(&mut block_parent);

            let mut rest = IrStatement::Print(vec![IrStringPiece::Literal("<unknown>".to_owned())]);
            for (variant, (variant_name, _)) in enumerate(&ty_info.variants).rev() {
                let cond = ty_info_hw.check_tag_matches(large, value.expr.clone(), variant);
                let payload = ty_info_hw.extract_payload(large, value, variant);

                let mut block_case = vec![];
                builder.push_str(variant_name.str(&refs.shared.interner));
                if let Some(payload) = payload {
                    builder.push_str("(");
                    block_case.extend(print_hardware_sub(refs, new_ir_var, large, builder, &payload));
                    builder.push_str(")");
                }
                builder.print_and_clear(&mut block_case);

                rest = IrStatement::If(IrIfStatement {
                    condition: cond,
                    then_block: IrBlock { statements: block_case },
                    else_block: Some(IrBlock::new_single(span, rest)),
                })
            }

            block_parent.push(Spanned::new(span, rest));
        }
    }

    block_parent
}

/// The minimal set of references needed to convert values and types to strings.
#[derive(Copy, Clone)]
pub struct StringRefs<'a> {
    pub hierarchy: &'a SourceHierarchy,
    pub interner: &'a Interner,
    pub elab: &'a ElaborationArenas,
}

impl<'a, 's: 'a> From<CompileRefs<'a, 's>> for StringRefs<'a> {
    fn from(refs: CompileRefs<'a, 's>) -> Self {
        StringRefs {
            hierarchy: refs.fixed.hierarchy,
            interner: &refs.shared.interner,
            elab: &refs.shared.elaboration_arenas,
        }
    }
}

impl CompileValue {
    pub fn value_string<'a>(&self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        match self {
            CompileValue::Simple(v) => v.value_string(refs),
            CompileValue::Compound(v) => v.value_string(refs),
            CompileValue::Hardware(never) => never.unreachable(),
        }
    }
}

impl SimpleCompileValue {
    pub fn value_string<'a>(&self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        match self {
            SimpleCompileValue::Type(v) => v.value_string(refs),
            SimpleCompileValue::Bool(v) => v.to_string(),
            SimpleCompileValue::Int(v) => v.to_string(),
            SimpleCompileValue::Array(v) => {
                let content = v.iter().map(|e| e.value_string(refs)).format(", ");
                format!("[{}]", content)
            }
            // TODO include names for function/module/references
            // TODO include import path for debug names?
            SimpleCompileValue::Function(_) => "<function>".to_owned(),
            SimpleCompileValue::Module(_) => "<module>".to_owned(),
            &SimpleCompileValue::Package(node) => {
                format!("<package {}>", refs.hierarchy[node].steps.join("."))
            }
            &SimpleCompileValue::Interface(v) => v.value_string(refs),
            &SimpleCompileValue::InterfaceArray(ref lens, v) => {
                format!("{}{}", shape_string(lens), v.value_string(refs))
            }
            &SimpleCompileValue::InterfaceView(v) => v.value_string(refs),
            &SimpleCompileValue::InterfaceViewArray(ref lens, v) => {
                format!("{}{}", shape_string(lens), v.value_string(refs))
            }
            SimpleCompileValue::Reference(rf) => match rf.get_unchecked() {
                ReferenceInner::Variable { var: _, ty } => {
                    format!("<ref to var with type `{}`>", ty.value_string(refs))
                }
                ReferenceInner::Signal { signal, ty, ty_hw: _ } => {
                    let kind_str = signal.kind_str();
                    format!("<ref to {kind_str} with type `{}`>", ty.value_string(refs))
                }
                ReferenceInner::Interface(info) => {
                    let intf_str = &refs.elab.interface_info(info.elab.inner).debug_info_name;
                    // all elements have the same kind, except that an empty array has no elements
                    let kind_str = match info.intf.flat_values().first() {
                        Some(intf) => format!("{} ", intf.kind_str()),
                        None => String::new(),
                    };
                    match info.intf.as_single() {
                        Some(_) => format!("<ref to {kind_str}instance of interface `{intf_str}`>"),
                        None => format!(
                            "<ref to {kind_str}array of interface `{intf_str}` with shape `{}`>",
                            shape_string(&info.intf.shape().to_vec())
                        ),
                    }
                }
            },
        }
    }
}

impl Type {
    pub fn value_string<'a>(&self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        match self {
            Type::Type => "type".to_string(),
            Type::Any => "any".to_string(),
            Type::Undefined => "undefined".to_string(),

            Type::Bool => "bool".to_string(),
            Type::String => "str".to_string(),
            Type::Int(range) => {
                let range_int = MultiRange::open();
                let range_uint = MultiRange::from(Range {
                    start: Some(BigInt::ZERO),
                    end: None,
                });
                if range == &range_int {
                    "int".to_owned()
                } else if range == &range_uint {
                    "uint".to_owned()
                } else if range.is_empty() {
                    "int(/*empty*/)".to_string()
                } else {
                    format!("int({range})")
                }
            }
            Type::Array(inner, len) => {
                let inner_str = inner.value_string(refs);
                match len {
                    None => format!("[_]{inner_str}"),
                    Some(len) => format!("[{len}]{inner_str}"),
                }
            }
            Type::Tuple(inner) => {
                let mut f = String::new();
                swrite!(f, "Tuple");
                if let Some(inner) = inner {
                    swrite!(f, "(");
                    swrite!(f, "{}", inner.iter().map(|e| e.value_string(refs)).format(", "));
                    if inner.len() == 1 {
                        swrite!(f, ",");
                    }
                    swrite!(f, ")");
                }
                f
            }
            // TODO include import path for debug names?
            &Type::Struct(ty) => refs.elab.struct_info(ty).value_string(),
            &Type::Enum(ty) => refs.elab.enum_info(ty).value_string(),
            Type::Range => "Range".to_string(),
            Type::Function => "Function".to_string(),
            Type::Module => "Module".to_string(),
            Type::Interface => "Interface".to_string(),
            Type::InterfaceArray(lens) => format!("{}Interface", shape_string(lens)),
            Type::InterfaceView => "InterfaceView".to_string(),
            Type::InterfaceViewArray(lens) => format!("{}InterfaceView", shape_string(lens)),
            Type::HierarchyNode => "Package".to_string(),
            Type::Ref(ty) => {
                format!("Ref({})", ty.value_string(refs))
            }
            Type::RefInterface(shape, intf) => {
                let shape_str = shape_string(shape);
                let intf_str = &refs.elab.interface_info(*intf).debug_info_name;
                format!("RefInterface({shape_str}{intf_str})")
            }
        }
    }
}

impl ElaboratedStructInfo {
    pub fn value_string(&self) -> String {
        format!("<struct {}>", self.debug_info_name)
    }
}

impl ElaboratedEnumInfo {
    pub fn value_string(&self) -> String {
        format!("<enum {}>", self.debug_info_name)
    }
}

impl HardwareType {
    pub fn value_string<'a>(&self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        self.as_type().value_string(refs)
    }
}

pub fn range_value_string(range: &MultiRange<BigInt>) -> String {
    format!("Range({})", range.ranges().iter().format(", "))
}

impl CompileCompoundValue {
    pub fn value_string<'a>(&self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        match self {
            CompileCompoundValue::String(v) => v.as_ref().clone(),
            CompileCompoundValue::Range(v) => range_value_string(v),
            CompileCompoundValue::Tuple(v) => {
                let mut f = String::new();
                swrite!(f, "(");
                swrite!(f, "{}", v.iter().map(|e| e.value_string(refs)).format(", "));
                if v.len() == 1 {
                    swrite!(f, ",");
                }
                swrite!(f, ")");
                f
            }
            CompileCompoundValue::Struct(v) => {
                let &StructValue { ty, ref fields } = v;
                let ty_info = refs.elab.struct_info(ty);

                let mut f = String::new();
                swrite!(f, "{}.new(", ty_info.debug_info_name);
                for ((field_name, field_value), last) in zip_eq(ty_info.fields.keys(), fields).with_last() {
                    swrite!(
                        f,
                        "{}={}",
                        field_name.str(refs.interner),
                        field_value.value_string(refs)
                    );
                    if !last {
                        swrite!(f, ", ");
                    }
                }
                swrite!(f, ")");
                f
            }
            CompileCompoundValue::Enum(v) => {
                let &EnumValue {
                    ty,
                    variant,
                    ref payload,
                } = v;
                let ty_info = refs.elab.enum_info(ty);

                let (variant_name, _) = ty_info.variants.get_index(variant).unwrap();

                let mut f = String::new();
                swrite!(f, "{}.{}", ty_info.debug_info_name, variant_name.str(refs.interner));
                if let Some(payload) = payload {
                    swrite!(f, "({})", payload.value_string(refs));
                }
                f
            }
            CompileCompoundValue::BoundMethod(bound) => {
                let BoundMethod {
                    self_type,
                    self_value: _,
                    method,
                } = bound;
                format!(
                    "<bound {}.{}>",
                    self_type.value_string(refs),
                    method.name.str(refs.interner)
                )
            }
        }
    }
}

impl ElaboratedInterface {
    pub fn value_string<'a>(self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        let intf = &refs.elab.interface_info(self).debug_info_name;
        format!("<interface {intf}>")
    }
}

impl ElaboratedInterfaceView {
    pub fn value_string<'a>(self, refs: impl Into<StringRefs<'a>>) -> String {
        let refs = refs.into();
        let ElaboratedInterfaceView { interface, view_index } = self;
        let info = refs.elab.interface_info(interface);
        let view_info = &info.views[view_index];
        format!(
            "<interface view {}.{}>",
            info.debug_info_name, view_info.debug_info_name
        )
    }
}

/// Format an array shape as `[a][b][c]`.
pub fn shape_string<T: std::fmt::Display>(shape: &[T]) -> String {
    shape.iter().map(|len| format!("[{len}]")).join("")
}
