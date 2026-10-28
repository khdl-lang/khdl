use num_integer::Integer;
use num_traits::{Num, Pow, Signed};
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BigUint(Storage);

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BigInt(Storage);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Sign {
    Negative,
    Zero,
    Positive,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct IsZero;

// TODO benchmark i128 vs i64
type IStorage = i128;

#[derive(Clone, Eq, PartialEq, Hash)]
enum Storage {
    Small(IStorage),
    Big(num_bigint::BigInt),
}

pub trait AnyInt: Debug + Clone + Eq + PartialEq + Ord + PartialOrd + std::hash::Hash + Sized + Into<BigInt> {
    fn next(&self) -> Self;
}

impl AnyInt for BigUint {
    fn next(&self) -> Self {
        self + 1u8
    }
}
impl AnyInt for BigInt {
    fn next(&self) -> Self {
        self + 1u8
    }
}

impl Storage {
    const ZERO: Self = Storage::Small(0);
    const ONE: Self = Storage::Small(1);
    const TWO: Self = Storage::Small(2);
    const NEG_ONE: Self = Storage::Small(-1);

    fn from_maybe_big(value: num_bigint::BigInt) -> Self {
        match IStorage::try_from(&value) {
            Ok(value) => Storage::Small(value),
            Err(_) => Storage::Big(value),
        }
    }

    fn into_num_bigint(self) -> num_bigint::BigInt {
        match self {
            Storage::Small(value) => value.into(),
            Storage::Big(value) => value,
        }
    }

    fn check_valid(&self) {
        match self {
            Storage::Small(_) => {}
            Storage::Big(inner) => {
                // values that can be represented as Storage::Small should be,
                //   this ensures that each value has a unique representation
                debug_assert!(IStorage::try_from(inner).is_err());
            }
        }
    }

    fn sign(&self) -> Sign {
        match self {
            &Storage::Small(value) => match value {
                ..0 => Sign::Negative,
                0 => Sign::Zero,
                1.. => Sign::Positive,
            },
            Storage::Big(value) => match value.sign() {
                num_bigint::Sign::Minus => Sign::Negative,
                num_bigint::Sign::NoSign => unreachable!(),
                num_bigint::Sign::Plus => Sign::Positive,
            },
        }
    }
}

impl BigUint {
    pub const ZERO: Self = BigUint(Storage::ZERO);
    pub const ONE: Self = BigUint(Storage::ONE);
    pub const TWO: Self = BigUint(Storage::TWO);

    fn new(storage: Storage) -> Self {
        storage.check_valid();
        debug_assert_ne!(storage.sign(), Sign::Negative);
        BigUint(storage)
    }

    fn storage(&self) -> &Storage {
        &self.0
    }

    fn into_storage(self) -> Storage {
        self.0
    }

    pub fn is_zero(&self) -> bool {
        self.storage().sign() == Sign::Zero
    }

    pub fn is_positive(&self) -> bool {
        self.storage().sign() == Sign::Positive
    }

    pub fn into_num_biguint(self) -> num_bigint::BigUint {
        num_bigint::BigUint::try_from(self.into_storage().into_num_bigint()).unwrap()
    }

    pub fn from_str_radix(s: &str, radix: u32) -> Result<BigUint, num_bigint::ParseBigIntError> {
        let storage = match IStorage::from_str_radix(s, radix) {
            Ok(result) => Storage::Small(result),
            Err(_) => Storage::from_maybe_big(num_bigint::BigUint::from_str_radix(s, radix)?.into()),
        };
        Ok(BigUint::new(storage))
    }

    pub fn set_bit(self, index: u64, value: bool) -> BigUint {
        if let Storage::Small(slf) = self.0
            && index < IStorage::BITS.into()
        {
            let mask = 1 << index;
            let result = if value { slf | mask } else { slf & !mask };

            if result >= 0 {
                return BigUint::new(Storage::Small(result));
            }
        }

        let mut result = self.into_num_biguint();
        result.set_bit(index, value);
        BigUint::new(Storage::from_maybe_big(result.into()))
    }

    pub fn pow_2_to(exp: &BigUint) -> BigUint {
        if let Ok(exp) = u64::try_from(exp) {
            return BigUint::ZERO.set_bit(exp, true);
        }

        BigUint::TWO.pow(exp)
    }

    pub fn pow(&self, exp: &BigUint) -> BigUint {
        if let (&Storage::Small(base), &Storage::Small(exp)) = (self.storage(), exp.storage())
            && let Ok(exp) = u32::try_from(exp)
            && let Some(result) = base.checked_pow(exp)
        {
            return BigUint::new(Storage::Small(result));
        }

        BigUint::new(Storage::from_maybe_big(
            self.clone()
                .into_num_biguint()
                .pow(&exp.clone().into_num_biguint())
                .into(),
        ))
    }

    pub fn size_bits(&self) -> u64 {
        match self.storage() {
            Storage::Small(storage) => (IStorage::BITS - storage.leading_zeros()).into(),
            Storage::Big(storage) => storage.bits(),
        }
    }

    /// Get the bit at the given index.
    /// This acts as if the value is padded with an infinite number of 0s towards the higher indices.
    pub fn get_bit_zero_padded(&self, index: u64) -> bool {
        match self.storage() {
            Storage::Small(storage) => {
                if index >= u64::from(IStorage::BITS) {
                    false
                } else {
                    (storage >> index) & 1 != 0
                }
            }
            Storage::Big(storage) => storage.bit(index),
        }
    }

    pub fn as_usize_if_lt(&self, len: usize) -> Option<usize> {
        let s = self.try_into().ok()?;
        if s < len { Some(s) } else { None }
    }

    pub fn sub_1(&self) -> Result<BigUint, IsZero> {
        BigUint::try_from(self - 1).map_err(|_| IsZero)
    }
}

impl BigInt {
    pub const ZERO: Self = BigInt(Storage::ZERO);
    pub const ONE: Self = BigInt(Storage::ONE);
    pub const TWO: Self = BigInt(Storage::TWO);
    pub const NEG_ONE: Self = BigInt(Storage::NEG_ONE);

    fn new(storage: Storage) -> Self {
        storage.check_valid();
        BigInt(storage)
    }

    fn storage(&self) -> &Storage {
        &self.0
    }

    fn into_storage(self) -> Storage {
        self.0
    }

    pub fn sign(&self) -> Sign {
        self.storage().sign()
    }

    pub fn is_zero(&self) -> bool {
        self.sign() == Sign::Zero
    }

    pub fn is_negative(&self) -> bool {
        self.sign() == Sign::Negative
    }

    pub fn is_positive(&self) -> bool {
        self.sign() == Sign::Positive
    }

    pub fn into_num_bigint(self) -> num_bigint::BigInt {
        self.into_storage().into_num_bigint()
    }

    pub fn from_num_bigint(value: num_bigint::BigInt) -> Self {
        BigInt::new(Storage::from_maybe_big(value))
    }

    pub fn abs(&self) -> BigUint {
        if let Storage::Small(inner) = self.storage()
            && let Some(result) = inner.checked_abs()
        {
            return BigUint::new(Storage::Small(result));
        }

        BigUint::new(Storage::from_maybe_big(self.clone().into_num_bigint().abs()))
    }

    pub fn into_neg_abs(self) -> (bool, BigUint) {
        if self < BigInt::ZERO {
            (true, self.abs())
        } else {
            (false, BigUint::try_from(self).unwrap())
        }
    }

    pub fn div_floor(&self, rhs: &BigInt) -> Result<BigInt, DivideByZero> {
        // TODO small fast path
        if rhs.is_zero() {
            Err(DivideByZero)
        } else {
            Ok(BigInt::new(Storage::from_maybe_big(
                self.clone().into_num_bigint().div_floor(&rhs.clone().into_num_bigint()),
            )))
        }
    }

    pub fn mod_floor(&self, rhs: &BigInt) -> Result<BigInt, DivideByZero> {
        // TODO small fast path
        if rhs.is_zero() {
            Err(DivideByZero)
        } else {
            Ok(BigInt::new(Storage::from_maybe_big(
                self.clone().into_num_bigint().mod_floor(&rhs.clone().into_num_bigint()),
            )))
        }
    }

    pub fn div_ceil(&self, rhs: &BigInt) -> Result<BigInt, DivideByZero> {
        // TODO small fast path
        if rhs.is_zero() {
            Err(DivideByZero)
        } else {
            Ok(BigInt::new(Storage::from_maybe_big(
                self.clone().into_num_bigint().div_ceil(&rhs.clone().into_num_bigint()),
            )))
        }
    }

    pub fn pow(&self, exp: &BigUint) -> BigInt {
        if let (&Storage::Small(base), &Storage::Small(exp)) = (self.storage(), exp.storage())
            && let Ok(exp) = u32::try_from(exp)
            && let Some(result) = base.checked_pow(exp)
        {
            return BigInt::new(Storage::Small(result));
        }

        BigInt::new(Storage::from_maybe_big(
            self.clone().into_num_bigint().pow(&exp.clone().into_num_biguint()),
        ))
    }

    /// Get the bit at the given index.
    /// This acts as if the value is padded with an infinite number of sign bits toward the higher indices.
    pub fn get_bit_sign_padded(&self, index: u64) -> bool {
        match self.storage() {
            &Storage::Small(storage) => {
                if index >= u64::from(IStorage::BITS) {
                    storage < 0
                } else {
                    (storage >> index) & 1 != 0
                }
            }
            Storage::Big(storage) => storage.bit(index),
        }
    }
}

impl From<BigUint> for BigInt {
    fn from(value: BigUint) -> Self {
        BigInt::new(value.into_storage())
    }
}

impl From<&BigUint> for BigInt {
    fn from(value: &BigUint) -> Self {
        BigInt::new(value.storage().clone())
    }
}

impl TryFrom<BigInt> for BigUint {
    type Error = BigInt;
    fn try_from(value: BigInt) -> Result<Self, Self::Error> {
        match value.sign() {
            Sign::Negative => Err(value),
            Sign::Zero | Sign::Positive => Ok(BigUint::new(value.into_storage())),
        }
    }
}

impl<'a> TryFrom<&'a BigInt> for BigUint {
    type Error = &'a BigInt;
    fn try_from(value: &'a BigInt) -> Result<Self, Self::Error> {
        match value.sign() {
            Sign::Negative => Err(value),
            Sign::Zero | Sign::Positive => Ok(BigUint::new(value.storage().clone())),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct DivideByZero;

impl std::ops::Neg for &BigUint {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        -BigInt::from(self)
    }
}

impl std::ops::Neg for &BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        if let Storage::Small(inner) = self.storage()
            && let Some(result) = inner.checked_neg()
        {
            return BigInt::new(Storage::Small(result));
        }

        BigInt::new(Storage::from_maybe_big(-self.clone().into_num_bigint()))
    }
}

impl std::ops::Neg for BigUint {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        -BigInt::from(self)
    }
}

impl std::ops::Neg for BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        -&self
    }
}

impl Ord for Storage {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self - other).sign() {
            Sign::Negative => Ordering::Less,
            Sign::Zero => Ordering::Equal,
            Sign::Positive => Ordering::Greater,
        }
    }
}

impl PartialOrd for Storage {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl std::iter::Sum for BigUint {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(BigUint::ZERO, |a, x| a + x)
    }
}

impl std::iter::Sum for BigInt {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(BigInt::ZERO, |a, x| a + x)
    }
}

impl Display for BigUint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.storage() {
            Storage::Small(value) => write!(f, "{value}"),
            Storage::Big(value) => write!(f, "{value}"),
        }
    }
}

impl Display for BigInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.storage() {
            Storage::Small(value) => write!(f, "{value}"),
            Storage::Big(value) => write!(f, "{value}"),
        }
    }
}

impl Debug for BigUint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Debug for BigInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

macro_rules! impl_primitive {
    ($unsigned:ident, $signed:ident) => {
        // ops
        impl std::ops::Add<&$unsigned> for &BigUint {
            type Output = BigUint;
            fn add(self, rhs: &$unsigned) -> Self::Output {
                BigUint::new(self.storage() + Storage::from(*rhs))
            }
        }
        impl std::ops::Add<&$unsigned> for &BigInt {
            type Output = BigInt;
            fn add(self, rhs: &$unsigned) -> Self::Output {
                BigInt::new(self.storage() + Storage::from(*rhs))
            }
        }
        impl std::ops::Add<&$signed> for &BigInt {
            type Output = BigInt;
            fn add(self, rhs: &$signed) -> Self::Output {
                BigInt::new(self.storage() + Storage::from(*rhs))
            }
        }

        impl std::ops::Sub<&$unsigned> for &BigUint {
            type Output = BigInt;
            fn sub(self, rhs: &$unsigned) -> Self::Output {
                BigInt::new(self.storage() - Storage::from(*rhs))
            }
        }
        impl std::ops::Sub<&$signed> for &BigUint {
            type Output = BigInt;
            fn sub(self, rhs: &$signed) -> Self::Output {
                BigInt::new(self.storage() - Storage::from(*rhs))
            }
        }
        impl std::ops::Sub<&$unsigned> for &BigInt {
            type Output = BigInt;
            fn sub(self, rhs: &$unsigned) -> Self::Output {
                BigInt::new(self.storage() - Storage::from(*rhs))
            }
        }
        impl std::ops::Sub<&$signed> for &BigInt {
            type Output = BigInt;
            fn sub(self, rhs: &$signed) -> Self::Output {
                BigInt::new(self.storage() - Storage::from(*rhs))
            }
        }

        impl std::ops::Mul<&$unsigned> for &BigUint {
            type Output = BigUint;
            fn mul(self, rhs: &$unsigned) -> Self::Output {
                BigUint::new(self.storage() * Storage::from(*rhs))
            }
        }
        impl std::ops::Mul<&$signed> for &BigInt {
            type Output = BigInt;
            fn mul(self, rhs: &$signed) -> Self::Output {
                BigInt::new(self.storage() * Storage::from(*rhs))
            }
        }

        impl_op_owned!(Add, add, (BigUint, $unsigned) -> BigUint);
        impl_op_owned!(Add, add, (BigInt, $unsigned) -> BigInt);
        impl_op_owned!(Add, add, (BigInt, $signed) -> BigInt);

        impl_op_owned!(Sub, sub, (BigInt, $signed) -> BigInt);
        impl_op_owned!(Sub, sub, (BigInt, $unsigned) -> BigInt);
        impl_op_owned!(Sub, sub, (BigUint, $signed) -> BigInt);
        impl_op_owned!(Sub, sub, (BigUint, $unsigned) -> BigInt);

        impl_op_owned!(Mul, mul, (BigUint, $unsigned) -> BigUint);
        impl_op_owned!(Mul, mul, (BigInt, $signed) -> BigInt);

        // unsigned/signed -> Storage
        impl From<$unsigned> for Storage {
            fn from(value: $unsigned) -> Self {
                match IStorage::try_from(value) {
                    Ok(value) => Storage::Small(value),
                    Err(_) => Storage::from_maybe_big(value.into()),
                }
            }
        }
        impl From<$signed> for Storage {
            fn from(value: $signed) -> Self {
                match IStorage::try_from(value) {
                    Ok(value) => Storage::Small(value),
                    Err(_) => Storage::from_maybe_big(value.into()),
                }
            }
        }

        // unsigned->BigUint and unsigned/signed->BigInt
        impl From<$unsigned> for BigUint {
            fn from(value: $unsigned) -> Self {
                BigUint::new(Storage::from(value))
            }
        }
        impl From<$unsigned> for BigInt {
            fn from(value: $unsigned) -> Self {
                BigInt::new(Storage::from(value))
            }
        }
        impl From<$signed> for BigInt {
            fn from(value: $signed) -> Self {
                BigInt::new(Storage::from(value))
            }
        }

        // Storage/BigUint/BigInt -> unsigned/signed
        impl<'a> TryFrom<&'a BigUint> for $unsigned {
            type Error = &'a BigUint;
            fn try_from(value: &'a BigUint) -> Result<Self, Self::Error> {
                match value.storage() {
                    &Storage::Small(inner) => $unsigned::try_from(inner).map_err(|_| value),
                    Storage::Big(inner) => $unsigned::try_from(inner).map_err(|_| value),
                }
            }
        }
        impl<'a> TryFrom<&'a BigInt> for $unsigned {
            type Error = &'a BigInt;
            fn try_from(value: &'a BigInt) -> Result<Self, Self::Error> {
                match value.storage() {
                    &Storage::Small(inner) => $unsigned::try_from(inner).map_err(|_| value),
                    Storage::Big(inner) => $unsigned::try_from(inner).map_err(|_| value),
                }
            }
        }
        impl TryFrom<BigUint> for $unsigned {
            type Error = BigUint;
            fn try_from(value: BigUint) -> Result<Self, Self::Error> {
                match $unsigned::try_from(&value) {
                    Ok(value) => Ok(value),
                    Err(_) => Err(value),
                }
            }
        }
        impl TryFrom<BigInt> for $unsigned {
            type Error = BigInt;
            fn try_from(value: BigInt) -> Result<Self, Self::Error> {
                match $unsigned::try_from(&value) {
                    Ok(value) => Ok(value),
                    Err(_) => Err(value),
                }
            }
        }
    };
}

macro_rules! impl_op_owned {
    ($op_trait:ident, $op_fn:ident, ($ty_left:ty, $ty_right:ty) -> $ty_result:ident) => {
        // TODO re-use backing storage for big ints here?
        impl std::ops::$op_trait<$ty_right> for $ty_left {
            type Output = $ty_result;
            fn $op_fn(self, rhs: $ty_right) -> Self::Output {
                (&self).$op_fn(&rhs)
            }
        }
        impl std::ops::$op_trait<$ty_right> for &$ty_left {
            type Output = $ty_result;
            fn $op_fn(self, rhs: $ty_right) -> Self::Output {
                self.$op_fn(&rhs)
            }
        }
        impl std::ops::$op_trait<&$ty_right> for $ty_left {
            type Output = $ty_result;
            fn $op_fn(self, rhs: &$ty_right) -> Self::Output {
                (&self).$op_fn(rhs)
            }
        }
    };
}

macro_rules! impl_op_storage {
    ($op_trait:ident, $op_fn:ident, $op_small:expr) => {
        impl std::ops::$op_trait<&Storage> for &Storage {
            type Output = Storage;
            fn $op_fn(self, rhs: &Storage) -> Self::Output {
                if let (&Storage::Small(lhs), &Storage::Small(rhs)) = (self, rhs) {
                    let op_small: fn(IStorage, IStorage) -> Option<IStorage> = $op_small;
                    if let Some(result) = op_small(lhs, rhs) {
                        return Storage::Small(result);
                    }
                }

                Storage::from_maybe_big(self.clone().into_num_bigint().$op_fn(rhs.clone().into_num_bigint()))
            }
        }

        impl_op_owned!($op_trait, $op_fn, (Storage, Storage) -> Storage);
    };
}

macro_rules! impl_op_int {
    ($op_trait:ident, $op_fn:ident, ($ty_left:ty, $ty_right:ty) -> $ty_result:ident) => {
        impl std::ops::$op_trait<&$ty_right> for &$ty_left {
            type Output = $ty_result;
            fn $op_fn(self, rhs: &$ty_right) -> Self::Output {
                $ty_result::new((self.storage()).$op_fn(rhs.storage()))
            }
        }
        impl_op_owned!($op_trait, $op_fn, ($ty_left, $ty_right) -> $ty_result);
    };
}

impl_primitive!(u8, i8);
impl_primitive!(u16, i16);
impl_primitive!(u32, i32);
impl_primitive!(u64, i64);
impl_primitive!(u128, i128);
impl_primitive!(usize, isize);

impl_op_storage!(Add, add, IStorage::checked_add);
impl_op_storage!(Sub, sub, IStorage::checked_sub);
impl_op_storage!(Mul, mul, IStorage::checked_mul);

impl_op_storage!(BitAnd, bitand, |lhs, rhs| Some(lhs & rhs));
impl_op_storage!(BitOr, bitor, |lhs, rhs| Some(lhs | rhs));
impl_op_storage!(BitXor, bitxor, |lhs, rhs| Some(lhs ^ rhs));

impl_op_int!(Add, add, (BigUint, BigUint) -> BigUint);
impl_op_int!(Add, add, (BigUint, BigInt) -> BigInt);
impl_op_int!(Add, add, (BigInt, BigUint) -> BigInt);
impl_op_int!(Add, add, (BigInt, BigInt) -> BigInt);

impl_op_int!(Sub, sub, (BigUint, BigUint) -> BigInt);
impl_op_int!(Sub, sub, (BigUint, BigInt) -> BigInt);
impl_op_int!(Sub, sub, (BigInt, BigUint) -> BigInt);
impl_op_int!(Sub, sub, (BigInt, BigInt) -> BigInt);

impl_op_int!(Mul, mul, (BigUint, BigUint) -> BigUint);
impl_op_int!(Mul, mul, (BigUint, BigInt) -> BigInt);
impl_op_int!(Mul, mul, (BigInt, BigUint) -> BigInt);
impl_op_int!(Mul, mul, (BigInt, BigInt) -> BigInt);

impl_op_int!(BitAnd, bitand, (BigUint, BigUint) -> BigUint);
impl_op_int!(BitAnd, bitand, (BigUint, BigInt) -> BigUint);
impl_op_int!(BitAnd, bitand, (BigInt, BigUint) -> BigUint);
impl_op_int!(BitAnd, bitand, (BigInt, BigInt) -> BigInt);

impl_op_int!(BitOr, bitor, (BigUint, BigUint) -> BigUint);
impl_op_int!(BitOr, bitor, (BigUint, BigInt) -> BigInt);
impl_op_int!(BitOr, bitor, (BigInt, BigUint) -> BigInt);
impl_op_int!(BitOr, bitor, (BigInt, BigInt) -> BigInt);

impl_op_int!(BitXor, bitxor, (BigUint, BigUint) -> BigUint);
impl_op_int!(BitXor, bitxor, (BigUint, BigInt) -> BigInt);
impl_op_int!(BitXor, bitxor, (BigInt, BigUint) -> BigInt);
impl_op_int!(BitXor, bitxor, (BigInt, BigInt) -> BigInt);

impl std::ops::Not for &BigUint {
    type Output = BigInt;
    fn not(self) -> Self::Output {
        !BigInt::from(self)
    }
}

impl std::ops::Not for BigUint {
    type Output = BigInt;
    fn not(self) -> Self::Output {
        !BigInt::from(self)
    }
}

impl std::ops::Not for &BigInt {
    type Output = BigInt;
    fn not(self) -> Self::Output {
        -self - 1
    }
}

impl std::ops::Not for BigInt {
    type Output = BigInt;
    fn not(self) -> Self::Output {
        !&self
    }
}

impl<T: Into<BigUint>> std::ops::AddAssign<T> for BigUint {
    fn add_assign(&mut self, rhs: T) {
        *self = &*self + rhs.into();
    }
}
impl std::ops::AddAssign<&BigUint> for BigUint {
    fn add_assign(&mut self, rhs: &BigUint) {
        *self = &*self + rhs;
    }
}

impl<T: Into<BigInt>> std::ops::AddAssign<T> for BigInt {
    fn add_assign(&mut self, rhs: T) {
        *self = &*self + rhs.into();
    }
}

impl<T: Into<BigInt>> std::ops::SubAssign<T> for BigInt {
    fn sub_assign(&mut self, rhs: T) {
        *self = &*self - rhs.into();
    }
}
