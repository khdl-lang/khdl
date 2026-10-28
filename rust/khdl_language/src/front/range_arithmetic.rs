//! Module to compute output ranges of expressions.
//!
//! Proofs of the validity of these range bounds can be found in `int_range_proofs.py`.

use crate::mid::ir::IrBoolBinaryOp;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::range::{ClosedNonEmptyRange, Range};
use crate::util::range_multi::{AnyMultiRange, ClosedNonEmptyMultiRange, MultiRange};
use itertools::{Itertools, chain};
use std::cmp::{max, min};

pub fn range_unary_neg(a: ClosedNonEmptyRange<&BigInt>) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    range_from_min_max(-a_max, -a_min)
}

pub fn multi_range_unary_neg(a: &ClosedNonEmptyMultiRange<BigInt>) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_unary(a, range_unary_neg)
}

pub fn range_unary_bitwise_not(a: ClosedNonEmptyRange<&BigInt>) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    range_from_min_max(!a_max, !a_min)
}

pub fn multi_range_unary_bitwise_not(a: &ClosedNonEmptyMultiRange<BigInt>) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_unary(a, range_unary_bitwise_not)
}

pub fn range_unary_abs(a: ClosedNonEmptyRange<&BigInt>) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    if a_max < BigInt::ZERO {
        range_from_min_max(-a_max, -a_min)
    } else {
        range_from_min_max(max(a_min.clone(), BigInt::ZERO), max(-a_min, a_max.clone()))
    }
}

pub fn multi_range_unary_abs(a: &ClosedNonEmptyMultiRange<BigInt>) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_unary(a, range_unary_abs)
}

pub fn range_binary_add(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = range_to_min_max(b);
    range_from_min_max(a_min + b_min, a_max + b_max)
}

pub fn multi_range_binary_add(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_binary(a, b, range_binary_add)
}

pub fn range_binary_sub(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = range_to_min_max(b);
    range_from_min_max(a_min - b_max, a_max - b_min)
}

pub fn multi_range_binary_sub(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_binary(a, b, range_binary_sub)
}

pub fn range_binary_mul(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> ClosedNonEmptyRange<BigInt> {
    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = range_to_min_max(b);
    let extremes = [a_min * b_min, a_min * &b_max, &a_max * b_min, a_max * b_max];
    range_from_min_max(
        extremes.iter().min().unwrap().clone(),
        extremes.iter().max().unwrap().clone(),
    )
}

pub fn multi_range_binary_mul(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_binary(a, b, range_binary_mul)
}

pub fn range_binary_div_floor(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> Option<ClosedNonEmptyRange<BigInt>> {
    // check for potential division by zero
    if b.contains(&&BigInt::ZERO) {
        return None;
    }

    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = range_to_min_max(b);

    let right_positive = b_min > &BigInt::ZERO;
    if right_positive {
        Some(range_from_min_max(
            min(a_min.div_floor(&b_max).unwrap(), a_min.div_floor(b_min).unwrap()),
            max(a_max.div_floor(&b_max).unwrap(), a_max.div_floor(b_min).unwrap()),
        ))
    } else {
        Some(range_from_min_max(
            min(a_max.div_floor(&b_max).unwrap(), a_max.div_floor(b_min).unwrap()),
            max(a_min.div_floor(&b_max).unwrap(), a_min.div_floor(b_min).unwrap()),
        ))
    }
}

pub fn multi_range_binary_div_floor(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> Option<ClosedNonEmptyMultiRange<BigInt>> {
    if b.contains(&BigInt::ZERO) {
        return None;
    }
    Some(wrap_multi_binary(a, b, |r_a, r_b| {
        range_binary_div_floor(r_a, r_b).expect("already checked for division by zero")
    }))
}

pub fn range_binary_div_ceil(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> Option<ClosedNonEmptyRange<BigInt>> {
    // `ceil(a / b) == -floor(-a / b)`
    let a_neg = range_unary_neg(a);
    let result_neg = range_binary_div_floor(a_neg.as_ref(), b)?;
    Some(range_unary_neg(result_neg.as_ref()))
}

pub fn multi_range_binary_div_ceil(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> Option<ClosedNonEmptyMultiRange<BigInt>> {
    if b.contains(&BigInt::ZERO) {
        return None;
    }
    Some(wrap_multi_binary(a, b, |r_a, r_b| {
        range_binary_div_ceil(r_a, r_b).expect("already checked for division by zero")
    }))
}

/// The result range is tight if `b` is a single value or if all `floor(a / b)` are equal.
/// In general a tight range is not feasible to compute, it would require factoring integers.
pub fn range_binary_mod(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> Option<ClosedNonEmptyRange<BigInt>> {
    // check for potential division by zero
    if b.contains(&&BigInt::ZERO) {
        return None;
    }

    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = range_to_min_max(b);

    // we already checked that b cannot be zero,
    //   which means the entire (contiguous) range is either positive or negative
    let b_positive = b_min > &BigInt::ZERO;
    if b_positive {
        let (r_min, r_max) = range_binary_mod_positive(a_min, &a_max, b_min, &b_max);
        Some(range_from_min_max(r_min, r_max))
    } else {
        // use the identity `a mod b == -((-a) mod (-b))`
        let (r_min, r_max) = range_binary_mod_positive(&-a_max, &-a_min, &-b_max, &-b_min);
        Some(range_from_min_max(-r_max, -r_min))
    }
}

/// Inclusive (min, max) bounds of `a mod b`, for `0 < b_min`.
fn range_binary_mod_positive(a_min: &BigInt, a_max: &BigInt, b_min: &BigInt, b_max: &BigInt) -> (BigInt, BigInt) {
    assert!(&BigInt::ZERO < b_min);

    // floor(a / b) increases with `a`, and moves towards zero as `b` increases
    let q_min = if a_min >= &BigInt::ZERO {
        a_min.div_floor(b_max).unwrap()
    } else {
        a_min.div_floor(b_min).unwrap()
    };
    let q_max = if a_max >= &BigInt::ZERO {
        a_max.div_floor(b_min).unwrap()
    } else {
        a_max.div_floor(b_max).unwrap()
    };

    if q_min == q_max {
        // the quotient is the same for all values, so the result `a - q * b` is linear
        let q = q_min;
        let (b_for_min, b_for_max) = if q >= BigInt::ZERO {
            (b_max, b_min)
        } else {
            (b_min, b_max)
        };
        let r_min = a_min - &q * b_for_min;
        let r_max = a_max - &q * b_for_max;
        (r_min, r_max)
    } else {
        // the quotient changes, the result can be anything in the mod interval,
        //   except that it can't be larger than `a` itself if `a` is not negative
        let r_max = if a_min >= &BigInt::ZERO {
            min(a_max.clone(), b_max - 1)
        } else {
            b_max - 1
        };
        (BigInt::ZERO, r_max)
    }
}

pub fn multi_range_binary_mod(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> Option<ClosedNonEmptyMultiRange<BigInt>> {
    if b.contains(&BigInt::ZERO) {
        return None;
    }
    Some(wrap_multi_binary(a, b, |r_a, r_b| {
        range_binary_mod(r_a, r_b).expect("already checked for division by zero")
    }))
}

pub fn range_binary_pow(
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigUint>,
) -> Option<ClosedNonEmptyRange<BigInt>> {
    let (a_min, a_max) = range_to_min_max(a);
    let (b_min, b_max) = uint_range_to_min_max(b);

    // check for potential 0**0
    if a.contains(&&BigInt::ZERO) && b.contains(&&BigUint::ZERO) {
        return None;
    }

    // calculate and combine different cases
    let cases_basic = [a_min.pow(b_min), a_min.pow(&b_max), a_max.pow(&b_max)];
    let case_even_odd = if b_min < &b_max {
        let b_max_m1 = BigUint::try_from(b_max - 1).expect("start < end and 0 <= start, so 0 < end");
        Some(a_min.pow(&b_max_m1))
    } else {
        None
    };
    let case_zero = if a_min <= &BigInt::ZERO && BigInt::ZERO < a_max {
        Some(BigInt::ZERO)
    } else {
        None
    };

    let cases = chain!(cases_basic, case_even_odd, case_zero);
    let (result_min, result_max) = cases.minmax().into_option().unwrap();

    Some(range_from_min_max(result_min, result_max))
}

pub fn multi_range_binary_pow(
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigUint>,
) -> Option<ClosedNonEmptyMultiRange<BigInt>> {
    // check for potential 0**0
    if a.contains(&BigInt::ZERO) && b.contains(&BigUint::ZERO) {
        return None;
    }
    Some(wrap_multi_binary(a, b, |r_a, r_b| {
        range_binary_pow(r_a, r_b).expect("already checked for 0**0")
    }))
}

pub fn range_binary_bitwise(
    op: IrBoolBinaryOp,
    a: ClosedNonEmptyRange<&BigInt>,
    b: ClosedNonEmptyRange<&BigInt>,
) -> ClosedNonEmptyRange<BigInt> {
    /// The same as the outer function, but for ranges with a constant sign.
    fn range_binary_bitwise_same_sign(
        op: IrBoolBinaryOp,
        a: &(BigInt, BigInt),
        b: &(BigInt, BigInt),
    ) -> (BigInt, BigInt) {
        match op {
            IrBoolBinaryOp::And => (bitwise_and_min(a, b), bitwise_and_max(a, b)),
            // `x | y == ~(~x & ~y)`
            IrBoolBinaryOp::Or => min_max_not(&range_binary_bitwise_same_sign(
                IrBoolBinaryOp::And,
                &min_max_not(a),
                &min_max_not(b),
            )),
            // `x ^ y == ~(x ^ ~y)`
            IrBoolBinaryOp::Xor => (bitwise_xor_min(a, b), !bitwise_xor_min(a, &min_max_not(b))),
        }
    }

    /// Split the given range into min/max slices where each slice has a constant sign.
    fn sign_parts(a: ClosedNonEmptyRange<&BigInt>) -> impl Iterator<Item = (BigInt, BigInt)> + Clone {
        let (a_min, a_max) = range_to_min_max(a);
        let neg = a_min
            .is_negative()
            .then(|| (a_min.clone(), min(a_max.clone(), BigInt::NEG_ONE)));
        let non_neg = (!a_max.is_negative()).then(|| (max(a_min.clone(), BigInt::ZERO), a_max));
        chain(neg, non_neg)
    }

    /// Compute the min bound of the `&` operation.
    fn bitwise_and_min(a: &(BigInt, BigInt), b: &(BigInt, BigInt)) -> BigInt {
        let f = |(a_min, a_max): &(BigInt, BigInt), (b_min, _): &(BigInt, BigInt)| {
            a_min & b_min & !smear(&(!a_min & !b_min & smear(&(a_min ^ a_max))))
        };
        min(f(a, b), f(b, a))
    }

    /// Compute the max bound of the `&` operation.
    fn bitwise_and_max(a: &(BigInt, BigInt), b: &(BigInt, BigInt)) -> BigInt {
        let f = |(a_min, a_max): &(BigInt, BigInt), (_, b_max): &(BigInt, BigInt)| {
            b_max & (a_max | smear(&(a_max & !b_max & smear(&(a_min ^ a_max)))))
        };
        max(f(a, b), f(b, a))
    }

    /// Compute the min bound of the `^` operation.
    fn bitwise_xor_min(a: &(BigInt, BigInt), b: &(BigInt, BigInt)) -> BigInt {
        bitwise_and_min(a, &min_max_not(b)) | bitwise_and_min(&min_max_not(a), b)
    }

    /// Compute the min/max bounds of the `!` operation.
    fn min_max_not((min, max): &(BigInt, BigInt)) -> (BigInt, BigInt) {
        (!max, !min)
    }

    /// All bits at or below the highest set bit of the non-negative value `x`.
    fn smear(x: &BigInt) -> BigInt {
        let size_bits = BigUint::try_from(x)
            .expect("smear requires a non-negative value")
            .size_bits();
        BigInt::from(BigUint::pow_2_to(&BigUint::from(size_bits))) - 1
    }

    // Split the ranges up into pieces with a constant sign, then compute the result, then join everything again.
    let (r_min, r_max) = sign_parts(a)
        .cartesian_product(sign_parts(b))
        .map(|(a, b)| range_binary_bitwise_same_sign(op, &a, &b))
        .reduce(|(min_0, max_0), (min_1, max_1)| (min(min_0, min_1), max(max_0, max_1)))
        .unwrap();
    range_from_min_max(r_min, r_max)
}

pub fn multi_range_binary_bitwise(
    op: IrBoolBinaryOp,
    a: &ClosedNonEmptyMultiRange<BigInt>,
    b: &ClosedNonEmptyMultiRange<BigInt>,
) -> ClosedNonEmptyMultiRange<BigInt> {
    wrap_multi_binary(a, b, |a, b| range_binary_bitwise(op, a, b))
}

// multi-range versions just apply the single-range versions to each possible combination
fn wrap_multi_unary<A: Ord, R: Ord + Clone>(
    a: &ClosedNonEmptyMultiRange<A>,
    f: impl Fn(ClosedNonEmptyRange<&A>) -> ClosedNonEmptyRange<R>,
) -> ClosedNonEmptyMultiRange<R> {
    let mut result = MultiRange::EMPTY;
    for r in a.ranges() {
        result = result.union(&MultiRange::from(Range::from(f(r))));
    }
    ClosedNonEmptyMultiRange::try_from(result).unwrap()
}

fn wrap_multi_binary<A: Ord, B: Ord, R: Ord + Clone>(
    a: &ClosedNonEmptyMultiRange<A>,
    b: &ClosedNonEmptyMultiRange<B>,
    f: impl Fn(ClosedNonEmptyRange<&A>, ClosedNonEmptyRange<&B>) -> ClosedNonEmptyRange<R>,
) -> ClosedNonEmptyMultiRange<R> {
    let mut result = MultiRange::EMPTY;
    for r_a in a.ranges() {
        for r_b in b.ranges() {
            result = result.union(&MultiRange::from(Range::from(f(r_a, r_b))));
        }
    }
    ClosedNonEmptyMultiRange::try_from(result).unwrap()
}

// for arithmetic, reasoning about min/max(inclusive) is easier than start/end(exclusive)
fn range_to_min_max(a: ClosedNonEmptyRange<&BigInt>) -> (&BigInt, BigInt) {
    let ClosedNonEmptyRange { start, end } = a;
    (start, end - 1)
}

fn uint_range_to_min_max(a: ClosedNonEmptyRange<&BigUint>) -> (&BigUint, BigUint) {
    let ClosedNonEmptyRange { start, end } = a;
    (
        start,
        BigUint::try_from(end - 1).expect("non-empty, so max will not be negative"),
    )
}

fn range_from_min_max(min: BigInt, max: BigInt) -> ClosedNonEmptyRange<BigInt> {
    assert!(min <= max);
    ClosedNonEmptyRange {
        start: min,
        end: max + 1,
    }
}

#[cfg(test)]
mod tests {
    use crate::front::range_arithmetic::{
        range_binary_add, range_binary_bitwise, range_binary_div_ceil, range_binary_div_floor, range_binary_mod,
        range_binary_mul, range_binary_pow, range_binary_sub, range_from_min_max, range_unary_abs,
        range_unary_bitwise_not, range_unary_neg,
    };
    use crate::mid::ir::IrBoolBinaryOp;
    use crate::util::big_int::{BigInt, BigUint};
    use crate::util::exhaust::{Exhaust, exhaust};
    use crate::util::range::ClosedNonEmptyRange;
    use itertools::Itertools;

    #[test]
    fn test_neg() {
        check_unary(|a| Some(range_unary_neg(a)), |a| -a)
    }

    #[test]
    fn test_abs() {
        check_unary(|a| Some(range_unary_abs(a)), |a| BigInt::from(a.abs()))
    }

    #[test]
    fn test_bitwise_not() {
        check_unary(|a| Some(range_unary_bitwise_not(a)), |a| !a)
    }

    #[test]
    fn test_add() {
        check_binary(|a, b| Some((range_binary_add(a, b), true)), |a, b| a + b)
    }

    #[test]
    fn test_sub() {
        check_binary(|a, b| Some((range_binary_sub(a, b), true)), |a, b| a - b)
    }

    #[test]
    fn test_mul() {
        check_binary(|a, b| Some((range_binary_mul(a, b), true)), |a, b| a * b)
    }

    #[test]
    fn test_div() {
        check_binary(
            |a, b| range_binary_div_floor(a, b).map(|r| (r, true)),
            |a, b| a.div_floor(b).unwrap(),
        )
    }

    #[test]
    fn test_ceil_div() {
        check_binary(
            |a, b| range_binary_div_ceil(a, b).map(|r| (r, true)),
            |a, b| a.div_ceil(b).unwrap(),
        )
    }

    #[test]
    fn test_mod() {
        let f_range = |a: ClosedNonEmptyRange<&BigInt>, b: ClosedNonEmptyRange<&BigInt>| {
            let r = range_binary_mod(a, b)?;

            let b_single = b.as_single().is_some();
            let quotients_equal = range_iter(a)
                .flat_map(|a| range_iter(b).map(move |b| a.div_floor(&b).ok()))
                .all_equal();
            let tight = b_single || quotients_equal;

            Some((r, tight))
        };
        let f_value = |a: &BigInt, b: &BigInt| a.mod_floor(b).unwrap();
        check_binary(f_range, f_value)
    }

    #[test]
    fn test_pow() {
        check_binary(
            |a, b| {
                // the exponent must be non-negative, skip other ranges
                let b_start = BigUint::try_from(b.start).ok()?;
                let b_end = BigUint::try_from(b.end).unwrap();
                let r = range_binary_pow(
                    a,
                    ClosedNonEmptyRange {
                        start: &b_start,
                        end: &b_end,
                    },
                );
                r.map(|r| (r, true))
            },
            |a, b| a.pow(&BigUint::try_from(b).unwrap()),
        )
    }

    #[test]
    fn test_bitwise_and() {
        check_binary(
            |a, b| Some((range_binary_bitwise(IrBoolBinaryOp::And, a, b), true)),
            |a, b| a & b,
        )
    }

    #[test]
    fn test_bitwise_or() {
        check_binary(
            |a, b| Some((range_binary_bitwise(IrBoolBinaryOp::Or, a, b), true)),
            |a, b| a | b,
        )
    }

    #[test]
    fn test_bitwise_xor() {
        check_binary(
            |a, b| Some((range_binary_bitwise(IrBoolBinaryOp::Xor, a, b), true)),
            |a, b| a ^ b,
        )
    }

    /// Unary version of [check_binary].
    fn check_unary(
        f_range: impl Fn(ClosedNonEmptyRange<&BigInt>) -> Option<ClosedNonEmptyRange<BigInt>>,
        f_value: impl Fn(&BigInt) -> BigInt,
    ) {
        exhaust(|ex| {
            let a_range = choose_non_empty_range(ex);

            let r_range = f_range(a_range.as_ref());
            let Some(r_range) = r_range else {
                return;
            };
            println!("{} => {}", a_range, r_range);

            let mut hit_min = false;
            let mut hit_max = false;

            for a in range_iter(a_range.as_ref()) {
                let r = f_value(&a);
                assert!(r_range.contains(&r));
                if r == r_range.start {
                    hit_min = true;
                }
                if r == &r_range.end - 1 {
                    hit_max = true;
                }
            }

            assert!(hit_min);
            assert!(hit_max);
        });
    }

    /// Checks that for all possible (small) ranges and for all possible values:
    /// * The result range actually contains the given value.
    /// * (optionally) The result range is tight: both the max and max value are actually possible to reach.
    fn check_binary(
        f_range: impl Fn(
            ClosedNonEmptyRange<&BigInt>,
            ClosedNonEmptyRange<&BigInt>,
        ) -> Option<(ClosedNonEmptyRange<BigInt>, bool)>,
        f_value: impl Fn(&BigInt, &BigInt) -> BigInt,
    ) {
        exhaust(|ex| {
            let a_range = choose_non_empty_range(ex);
            let b_range = choose_non_empty_range(ex);

            let r_range = f_range(a_range.as_ref(), b_range.as_ref());
            let Some((r_range, r_tight)) = r_range else {
                return;
            };
            println!("{} {} => {}", a_range, b_range, r_range);

            let mut hit_min = false;
            let mut hit_max = false;

            for a in range_iter(a_range.as_ref()) {
                for b in range_iter(b_range.as_ref()) {
                    let r = f_value(&a, &b);
                    assert!(r_range.contains(&r));
                    if r == r_range.start {
                        hit_min = true;
                    }
                    if r == &r_range.end - 1 {
                        hit_max = true;
                    }
                }
            }

            if r_tight {
                assert!(hit_min);
                assert!(hit_max);
            }
        });
    }

    fn choose_non_empty_range(ex: &mut Exhaust) -> ClosedNonEmptyRange<BigInt> {
        let amplitude = 8;

        let a_min = ex.choose(2 * amplitude + 1);
        let b_max = ex.choose_range(a_min, 2 * amplitude + 1);
        range_from_min_max(BigInt::from(a_min) - amplitude, BigInt::from(b_max) - amplitude)
    }

    fn range_iter(range: ClosedNonEmptyRange<&BigInt>) -> impl Iterator<Item = BigInt> {
        let mut next = range.start.clone();
        std::iter::from_fn(move || {
            if &next < range.end {
                let curr = next.clone();
                next += 1;
                Some(curr)
            } else {
                None
            }
        })
    }
}
