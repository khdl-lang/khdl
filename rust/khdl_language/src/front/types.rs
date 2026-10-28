use crate::front::compile::CompileRefs;
use crate::front::item::{
    ElaboratedEnum, ElaboratedInterface, ElaboratedStruct, ElaborationArenas, HardwareChecked, HardwareEnumInfo,
};
use crate::front::value::{CompileValue, HardwareValue};
use crate::mid::bits::{FromBitsInvalidValue, FromBitsWrongLength, ToBitsWrongType};
use crate::mid::ir::{IrEnumType, IrExpression, IrExpressionLarge, IrIntCompareOp, IrLargeArena, IrStructType, IrType};
use crate::util::big_int::{BigInt, BigUint};
use crate::util::int::IntRepresentation;
use crate::util::range_multi::{ClosedNonEmptyMultiRange, MultiRange};
use crate::util::{Never, ResultExt};
use itertools::{Either, Itertools, zip_eq};
use std::sync::Arc;

// TODO add an arena for types?
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Type {
    // Lattice top type (including type!)
    Any,
    // Lattice bottom type
    Undefined,
    // Higher order type, containing other types (including type itself!).
    Type,

    Bool,
    String,
    Int(MultiRange<BigInt>),
    Array(Arc<Type>, Option<BigUint>),
    Tuple(Option<Arc<Vec<Type>>>),
    // TODO make user type covariant? or allow users to define variance?
    Struct(ElaboratedStruct),
    Enum(ElaboratedEnum),
    // TODO include bound ranges as part of the type?
    Range,
    // TODO maybe maybe these (optionally) more specific
    Function,
    Module,
    Interface,
    InterfaceArray(Vec<BigUint>),
    InterfaceView,
    InterfaceViewArray(Vec<BigUint>),
    HierarchyNode,

    Ref(Arc<Type>),
    RefInterface(Vec<usize>, ElaboratedInterface),
}

// TODO change this to be a struct with some properties (size, ir, all valid, ...) plus a kind enum
// TODO get rid of this
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum HardwareType {
    Undefined,
    Bool,
    Int(ClosedNonEmptyMultiRange<BigInt>),
    Array(Arc<HardwareType>, BigUint),
    Tuple(Arc<Vec<HardwareType>>),
    Struct(HardwareChecked<ElaboratedStruct>),
    Enum(HardwareChecked<ElaboratedEnum>),
}

#[derive(Debug, Copy, Clone)]
pub struct TypeBool;

impl HardwareEnumInfo {
    pub fn check_tag_matches(&self, large: &mut IrLargeArena, value: IrExpression, variant: usize) -> IrExpression {
        let tag = large.push_expr(IrExpressionLarge::EnumTag { base: value });

        large.push_expr(IrExpressionLarge::IntCompare(
            IrIntCompareOp::Eq,
            tag,
            IrExpression::Int(BigInt::from(variant)),
        ))
    }

    pub fn extract_payload(
        &self,
        large: &mut IrLargeArena,
        value: &HardwareValue,
        variant: usize,
    ) -> Option<HardwareValue> {
        let (payload_ty, _) = self.payload_types[variant].as_ref()?;

        let payload = large.push_expr(IrExpressionLarge::EnumPayload {
            base: value.expr.clone(),
            variant,
        });

        Some(HardwareValue {
            ty: payload_ty.clone(),
            domain: value.domain,
            expr: payload,
        })
    }
}

pub trait Typed {
    fn ty(&self) -> Type;
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NonHardwareType;

impl Type {
    pub fn unit() -> Type {
        Type::Tuple(Some(Arc::new(vec![])))
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Type::Tuple(Some(inner)) if inner.is_empty())
    }

    pub fn union_all(types: impl IntoIterator<Item = Type>) -> Type {
        types.into_iter().fold(Type::Undefined, |acc, ty| acc.union(&ty))
    }

    pub fn union(&self, other: &Type) -> Type {
        match (self, other) {
            // top and bottom
            (Type::Any, _) | (_, Type::Any) => Type::Any,
            (Type::Undefined, other) | (other, Type::Undefined) => other.clone(),

            // simple matches
            (Type::Type, Type::Type) => Type::Type,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::String, Type::String) => Type::String,
            // TODO should we even allow unions for these?
            (Type::Range, Type::Range) => Type::Range,
            (Type::Function, Type::Function) => Type::Function,
            (Type::HierarchyNode, Type::HierarchyNode) => Type::HierarchyNode,
            (Type::Module, Type::Module) => Type::Module,
            (Type::Interface, Type::Interface) => Type::Interface,
            (Type::InterfaceView, Type::InterfaceView) => Type::InterfaceView,
            (Type::InterfaceArray(a), Type::InterfaceArray(b)) if a == b => Type::InterfaceArray(a.clone()),
            (Type::InterfaceViewArray(a), Type::InterfaceViewArray(b)) if a == b => Type::InterfaceViewArray(a.clone()),

            (Type::Int(a), Type::Int(b)) => Type::Int(a.union(b)),

            (Type::Array(a_inner, a_len), Type::Array(b_inner, b_len)) => {
                let result_inner = a_inner.union(b_inner);
                if a_len == b_len {
                    Type::Array(Arc::new(result_inner), a_len.clone())
                } else {
                    Type::Array(Arc::new(result_inner), None)
                }
            }
            (Type::Tuple(a), Type::Tuple(b)) => {
                if let Some(a) = a
                    && let Some(b) = b
                    && a.len() == b.len()
                {
                    Type::Tuple(Some(Arc::new(
                        zip_eq(a.iter(), b.iter()).map(|(a, b)| a.union(b)).collect_vec(),
                    )))
                } else {
                    Type::Tuple(None)
                }
            }
            (&Type::Struct(a_elab), &Type::Struct(b_elab)) => {
                if a_elab == b_elab {
                    Type::Struct(a_elab)
                } else {
                    Type::Any
                }
            }
            (&Type::Enum(a_elab), &Type::Enum(b_elab)) => {
                if a_elab == b_elab {
                    Type::Enum(a_elab)
                } else {
                    Type::Any
                }
            }
            (Type::Ref(a), Type::Ref(b)) => {
                if a == b {
                    Type::Ref(Arc::clone(a))
                } else {
                    Type::Any
                }
            }
            (Type::RefInterface(a_shape, a), Type::RefInterface(b_shape, b)) => {
                if a_shape == b_shape && a == b {
                    Type::RefInterface(a_shape.clone(), *a)
                } else {
                    Type::Any
                }
            }

            // simple mismatches (we list all of them out manually here to force exhaustiveness checking)
            (
                Type::Type
                | Type::Bool
                | Type::String
                | Type::Range
                | Type::Function
                | Type::Module
                | Type::Interface
                | Type::InterfaceArray(_)
                | Type::InterfaceView
                | Type::InterfaceViewArray(_)
                | Type::HierarchyNode
                | Type::Int(_)
                | Type::Array(_, _)
                | Type::Tuple(_)
                | Type::Struct(_)
                | Type::Enum(_)
                | Type::Ref(_)
                | Type::RefInterface(_, _),
                _,
            ) => Type::Any,
        }
    }

    pub fn contains_type(&self, ty: &Type) -> bool {
        // TODO optimize this?
        self == &self.union(ty)
    }

    // TODO centralize error messages for this, everyone is just doing them manually for now
    // TODO accept empty tuples here, maybe those need to be normal values instead of types,
    //   and then cast to type where needed
    pub fn as_hardware_type(&self, elab: &ElaborationArenas) -> Result<HardwareType, NonHardwareType> {
        match self {
            Type::Undefined => Ok(HardwareType::Undefined),
            Type::Bool => Ok(HardwareType::Bool),
            Type::Int(range) => match ClosedNonEmptyMultiRange::try_from(range.clone()) {
                Ok(range) => Ok(HardwareType::Int(range)),
                Err(_) => Err(NonHardwareType),
            },
            Type::Array(inner, len) => {
                let len = len.as_ref().ok_or(NonHardwareType)?;
                inner
                    .as_hardware_type(elab)
                    .map(|inner| HardwareType::Array(Arc::new(inner), len.clone()))
            }
            Type::Tuple(inner) => match inner {
                Some(inner) => inner
                    .iter()
                    .map(|ty| ty.as_hardware_type(elab))
                    .try_collect()
                    .map(|v| HardwareType::Tuple(Arc::new(v))),
                None => Err(NonHardwareType),
            },
            &Type::Struct(ty_struct) => {
                let info = elab.struct_info(ty_struct);
                match info.hw {
                    Ok(_) => Ok(HardwareType::Struct(HardwareChecked::new_unchecked(ty_struct))),
                    Err(_) => Err(NonHardwareType),
                }
            }
            &Type::Enum(ty_enum) => {
                let info = elab.enum_info(ty_enum);
                match info.hw {
                    Ok(_) => Ok(HardwareType::Enum(HardwareChecked::new_unchecked(ty_enum))),
                    Err(_) => Err(NonHardwareType),
                }
            }
            Type::Type
            | Type::Any
            | Type::String
            | Type::Range
            | Type::Function
            | Type::Module
            | Type::Interface
            | Type::InterfaceArray(_)
            | Type::InterfaceView
            | Type::InterfaceViewArray(_)
            | Type::HierarchyNode
            | Type::Ref(_)
            | Type::RefInterface(_, _) => Err(NonHardwareType),
        }
    }
}

impl HardwareType {
    pub fn as_type(&self) -> Type {
        match self {
            HardwareType::Undefined => Type::Undefined,
            HardwareType::Bool => Type::Bool,
            HardwareType::Int(range) => Type::Int(MultiRange::from(range.clone())),
            HardwareType::Array(inner, len) => Type::Array(Arc::new(inner.as_type()), Some(len.clone())),
            HardwareType::Tuple(inner) => {
                Type::Tuple(Some(Arc::new(inner.iter().map(HardwareType::as_type).collect_vec())))
            }
            HardwareType::Struct(elab) => Type::Struct(elab.inner()),
            HardwareType::Enum(elab) => Type::Enum(elab.inner()),
        }
    }

    pub fn as_ir(&self, refs: CompileRefs) -> IrType {
        match self {
            HardwareType::Undefined => IrType::Tuple(vec![]),
            HardwareType::Bool => IrType::Bool,
            HardwareType::Int(range) => IrType::Int(range.enclosing().cloned()),
            HardwareType::Array(inner, len) => IrType::Array(Box::new(inner.as_ir(refs)), len.clone()),
            HardwareType::Tuple(inner) => IrType::Tuple(inner.iter().map(|ty| ty.as_ir(refs)).collect_vec()),
            &HardwareType::Struct(ty) => {
                let info = refs.shared.elaboration_arenas.struct_info(ty.inner());
                let fields_hw = &info.hw.as_ref().unwrap().fields;

                let fields_ir = zip_eq(info.fields.keys(), fields_hw)
                    .map(|(field_name, field_ty)| {
                        (field_name.str(&refs.shared.interner).to_owned(), field_ty.as_ir(refs))
                    })
                    .collect();
                let info_ty = IrStructType {
                    ty,
                    debug_info_name: info.debug_info_name.clone(),
                    fields: fields_ir,
                };
                IrType::Struct(info_ty)
            }
            &HardwareType::Enum(ty) => {
                let info = refs.shared.elaboration_arenas.enum_info(ty.inner());
                let info_hw = info.hw.as_ref().unwrap();

                let variants_ir = zip_eq(info.variants.keys(), &info_hw.payload_types)
                    .map(|(variant_name, payload_ty)| {
                        (
                            variant_name.str(&refs.shared.interner).to_owned(),
                            payload_ty.as_ref().map(|(_, t)| t.clone()),
                        )
                    })
                    .collect();
                let info_ir = IrEnumType {
                    ty,
                    debug_info_name: info.debug_info_name.clone(),
                    variants: variants_ir,
                };
                IrType::Enum(info_ir)
            }
        }
    }

    pub fn every_bit_pattern_is_valid(&self, refs: CompileRefs) -> bool {
        match self {
            HardwareType::Undefined => true,
            HardwareType::Bool => true,
            HardwareType::Int(range) => {
                let repr = IntRepresentation::for_range(range.enclosing());
                &ClosedNonEmptyMultiRange::from(repr.range()) == range
            }
            HardwareType::Array(inner, _len) => inner.every_bit_pattern_is_valid(refs),
            HardwareType::Tuple(inner) => inner.iter().all(|ty| ty.every_bit_pattern_is_valid(refs)),
            &HardwareType::Struct(elab) => {
                let info = refs.shared.elaboration_arenas.struct_info(elab.inner());
                let fields_hw = &info.hw.as_ref_ok().unwrap().fields;
                fields_hw.iter().all(|ty| ty.every_bit_pattern_is_valid(refs))
            }
            &HardwareType::Enum(elab) => {
                let info = refs.shared.elaboration_arenas.enum_info(elab.inner());
                let info_hw = info.hw.as_ref().unwrap();

                // The tag needs to be fully valid.
                let tag_repr = IntRepresentation::for_range(info_hw.tag_range.as_ref());
                if tag_repr.range() != info_hw.tag_range {
                    return false;
                }

                // Padding bits must be zero, so there can't be any padding.
                let max_payload_size = info_hw.ty_ir.max_payload_size_bits();
                info_hw.payload_types.iter().all(|payload| match payload {
                    None => max_payload_size == BigUint::ZERO,
                    Some((ty, ty_ir)) => ty_ir.size_bits() == max_payload_size && ty.every_bit_pattern_is_valid(refs),
                })
            }
        }
    }

    // TODO cache converted IR type for these?
    pub fn size_bits(&self, refs: CompileRefs) -> BigUint {
        self.as_ir(refs).size_bits()
    }

    pub fn value_to_bits(&self, refs: CompileRefs, value: &CompileValue) -> Result<Vec<bool>, ToBitsWrongType> {
        self.as_ir(refs).value_to_bits(value)
    }

    pub fn value_from_bits(
        &self,
        refs: CompileRefs,
        bits: &[bool],
    ) -> Result<CompileValue, Either<FromBitsInvalidValue, FromBitsWrongLength>> {
        self.as_ir(refs).value_from_bits(bits)
    }
}

impl Typed for Never {
    fn ty(&self) -> Type {
        self.unreachable()
    }
}
