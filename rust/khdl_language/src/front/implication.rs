use crate::front::compile::CompileRefs;
use crate::front::diagnostic::DiagResult;
use crate::front::domain::ValueDomain;
use crate::front::flow::ValueVersion;
use crate::front::types::{HardwareType, Type, TypeBool, Typed};
use crate::front::value::{HardwareValue, MaybeCompile, MixedCompoundValue, SimpleCompileValue, Value, ValueCommon};
use crate::mid::ir::{IrExpression, IrLargeArena};
use crate::syntax::pos::Span;
use crate::util::big_int::BigInt;
use crate::util::range_multi::ClosedMultiRange;
use std::fmt::Debug;

#[derive(Debug, Clone)]
pub struct BoolImplications<V = ValueVersion> {
    pub if_true: Vec<Implication<V>>,
    pub if_false: Vec<Implication<V>>,
}

// TODO rename the concept "implication" to "type narrowing" everywhere
#[derive(Debug, Clone)]
pub struct Implication<V = ValueVersion> {
    pub version: V,
    pub kind: ImplicationKind,
}

#[derive(Debug, Clone)]
pub enum ImplicationKind {
    BoolEq(bool),
    IntIn(ClosedMultiRange<BigInt>),
}

#[derive(Debug, Copy, Clone)]
pub enum ImplicationIntOp {
    Neq,
    Lt,
    Gt,
}

pub type ValueWithVersion<S = SimpleCompileValue, C = MixedCompoundValue, T = HardwareType, E = IrExpression> =
    Value<S, C, HardwareValueWithVersion<ValueVersion, T, E>>;
pub type ValueWithImplications<S = SimpleCompileValue, C = MixedCompoundValue, T = HardwareType, E = IrExpression> =
    Value<S, C, HardwareValueWithImplications<T, E>>;
pub type HardwareValueWithMaybeVersion = HardwareValueWithVersion<Option<ValueVersion>>;

#[derive(Debug, Clone)]
pub struct HardwareValueWithVersion<V = ValueVersion, T = HardwareType, E = IrExpression> {
    pub value: HardwareValue<T, E>,
    pub version: V,
}

#[derive(Debug, Clone)]
pub struct HardwareValueWithImplications<T = HardwareType, E = IrExpression, V = Option<ValueVersion>> {
    pub value: HardwareValue<T, E>,
    pub version: V,
    pub implications: BoolImplications,
}

impl<V> HardwareValueWithVersion<V> {
    pub fn map_version<F: FnOnce(V) -> U, U>(self, f: F) -> HardwareValueWithVersion<U> {
        HardwareValueWithVersion {
            value: self.value,
            version: f(self.version),
        }
    }
}

impl BoolImplications {
    pub const NONE: Self = BoolImplications {
        if_true: vec![],
        if_false: vec![],
    };

    pub fn add_bool_self_implications(&mut self, version: ValueVersion) {
        self.if_true.push(Implication::new_bool(version, true));
        self.if_false.push(Implication::new_bool(version, false));
    }

    pub fn invert(self) -> Self {
        Self {
            if_true: self.if_false,
            if_false: self.if_true,
        }
    }
}

impl Implication {
    pub fn new_bool(value: ValueVersion, equal: bool) -> Self {
        Self {
            version: value,
            kind: ImplicationKind::BoolEq(equal),
        }
    }

    pub fn new_int(value: ValueVersion, range: ClosedMultiRange<BigInt>) -> Self {
        Self {
            version: value,
            kind: ImplicationKind::IntIn(range),
        }
    }
}

impl<S, C, T, E> ValueWithVersion<S, C, T, E> {
    pub fn into_value(self) -> Value<S, C, HardwareValue<T, E>> {
        self.map_hardware(|v| v.value)
    }
}

impl<S, C, T, E> ValueWithImplications<S, C, T, E> {
    pub fn simple(value: Value<S, C, HardwareValue<T, E>>) -> Self {
        value.map_hardware(HardwareValueWithImplications::simple)
    }

    pub fn into_value(self) -> Value<S, C, HardwareValue<T, E>> {
        self.map_hardware(|v| v.value)
    }
}

impl<T, E> HardwareValueWithImplications<T, E> {
    pub fn simple(value: HardwareValue<T, E>) -> Self {
        Self {
            value,
            version: None,
            implications: BoolImplications::NONE,
        }
    }
}

impl<T, E, V> HardwareValueWithImplications<T, E, V> {
    pub fn map_type<U>(self, f: impl FnOnce(T) -> U) -> HardwareValueWithImplications<U, E, V> {
        HardwareValueWithImplications {
            value: self.value.map_type(f),
            version: self.version,
            implications: self.implications,
        }
    }

    pub fn map_version<F: FnOnce(V) -> U, U>(self, f: F) -> HardwareValueWithImplications<T, E, U> {
        HardwareValueWithImplications {
            value: self.value,
            version: f(self.version),
            implications: self.implications,
        }
    }
}

impl<E> From<HardwareValueWithImplications<TypeBool, E>> for HardwareValueWithImplications<HardwareType, E> {
    fn from(value: HardwareValueWithImplications<TypeBool, E>) -> Self {
        value.map_type(|_: TypeBool| HardwareType::Bool)
    }
}

impl<C, E> From<MaybeCompile<bool, HardwareValueWithImplications<TypeBool, E>>>
    for ValueWithImplications<SimpleCompileValue, C, HardwareType, E>
{
    fn from(value: MaybeCompile<bool, HardwareValueWithImplications<TypeBool, E>>) -> Self {
        match value {
            MaybeCompile::Compile(v) => Value::Simple(SimpleCompileValue::Bool(v)),
            MaybeCompile::Hardware(v) => Value::Hardware(v.into()),
        }
    }
}

impl<V, E> Typed for HardwareValueWithVersion<V, HardwareType, E> {
    fn ty(&self) -> Type {
        self.value.ty.as_type()
    }
}

impl<E> Typed for HardwareValueWithImplications<HardwareType, E> {
    fn ty(&self) -> Type {
        self.value.ty.as_type()
    }
}

impl<V, E: Clone + Into<IrExpression>> ValueCommon for HardwareValueWithVersion<V, HardwareType, E> {
    fn domain(&self) -> ValueDomain {
        self.value.domain()
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        self.value.as_ir_expression_unchecked(refs, large, span, ty)
    }
}

impl<E: Clone + Into<IrExpression>> ValueCommon for HardwareValueWithImplications<HardwareType, E> {
    fn domain(&self) -> ValueDomain {
        self.value.domain()
    }

    fn as_ir_expression_unchecked(
        &self,
        refs: CompileRefs,
        large: &mut IrLargeArena,
        span: Span,
        ty: &HardwareType,
    ) -> DiagResult<IrExpression> {
        self.value.as_ir_expression_unchecked(refs, large, span, ty)
    }
}
