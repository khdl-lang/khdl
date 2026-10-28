use crate::util::big_int::{AnyInt, BigInt, BigUint};
use crate::util::data::VecExt;
use crate::util::range::{ClosedNonEmptyRange, ClosedRange, NonEmptyRange, Range, RangeEmpty, RangeOpen};
use itertools::{Either, Itertools};
use std::fmt::{Debug, Display, Formatter};

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct MultiRange<T> {
    // TODO use SmallVec
    ranges: Vec<NonEmptyRange<T>>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ClosedMultiRange<T> {
    inner: MultiRange<T>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ClosedNonEmptyMultiRange<T> {
    inner: MultiRange<T>,
}

pub trait AnyMultiRange<T> {
    fn as_multi_range(&self) -> &MultiRange<T>;

    fn is_empty(&self) -> bool {
        self.as_multi_range().ranges.is_empty()
    }

    fn as_single<'a>(&'a self) -> Option<&'a T>
    where
        T: Ord,
        &'a T: std::ops::Add<u8, Output = T>,
    {
        self.as_multi_range().ranges.single_ref()?.as_ref().as_single()
    }

    fn contains(&self, value: &T) -> bool
    where
        T: Ord,
    {
        // TODO binary search
        self.as_multi_range().ranges.iter().any(|r| r.contains(value))
    }

    fn contains_range<'a>(&self, other: impl Into<Range<&'a T>>) -> bool
    where
        T: Ord + 'a,
    {
        // TODO binary search
        let other = other.into();
        self.as_multi_range().ranges.iter().any(|r| r.contains_range(other))
    }

    fn contains_multi_range(&self, other: &impl AnyMultiRange<T>) -> bool
    where
        T: Ord,
    {
        // TODO joint iteration
        other
            .as_multi_range()
            .ranges
            .iter()
            .all(|other_range| self.contains_range(other_range.as_ref()))
    }
}

impl<T> MultiRange<T> {
    pub const EMPTY: MultiRange<T> = MultiRange { ranges: vec![] };

    pub fn open() -> MultiRange<T> {
        MultiRange {
            ranges: vec![NonEmptyRange::OPEN],
        }
    }

    pub fn single(value: T) -> MultiRange<T>
    where
        T: AnyInt,
    {
        MultiRange {
            ranges: vec![NonEmptyRange::single(value)],
        }
    }

    pub fn ranges(&self) -> &[NonEmptyRange<T>] {
        &self.ranges
    }

    pub fn as_single_range(&self) -> Option<&NonEmptyRange<T>> {
        self.ranges.single_ref()
    }

    fn assert_valid(&self)
    where
        T: Ord,
    {
        for i in 0..self.ranges.len() {
            let curr = &self.ranges[i];
            let next = self.ranges.get(i + 1);

            curr.assert_valid();

            if let Some(next) = next {
                let curr_end = curr.end.as_ref().unwrap();
                let next_start = next.start.as_ref().unwrap();
                assert!(
                    curr_end < next_start,
                    "multi ranges must be non-overlapping and non-adjacent"
                );
            }
        }
    }

    #[must_use]
    pub fn enclosing(&self) -> Option<NonEmptyRange<&T>>
    where
        T: Ord,
    {
        let range = NonEmptyRange {
            start: self.ranges.first()?.start.as_ref(),
            end: self.ranges.last()?.end.as_ref(),
        };
        if cfg!(debug_assertions) {
            range.assert_valid();
        }
        Some(range)
    }

    #[must_use]
    pub fn complement(&self) -> MultiRange<T>
    where
        T: Ord + Clone,
    {
        let mut ranges = Vec::new();

        if self.ranges.is_empty() {
            ranges.push(NonEmptyRange::OPEN);
        } else {
            if let Some(first_start) = &self.ranges[0].start {
                ranges.push(NonEmptyRange {
                    start: None,
                    end: Some(first_start.clone()),
                });
            }

            for (curr, next) in self.ranges.iter().tuple_windows() {
                let curr_end = curr.end.as_ref().unwrap();
                let next_start = next.start.as_ref().unwrap();

                debug_assert!(curr_end < next_start);
                ranges.push(NonEmptyRange {
                    start: Some(curr_end.clone()),
                    end: Some(next_start.clone()),
                });
            }

            if let Some(last_end) = &self.ranges.last().unwrap().end {
                ranges.push(NonEmptyRange {
                    start: Some(last_end.clone()),
                    end: None,
                });
            }
        }

        let result = MultiRange { ranges };
        if cfg!(debug_assertions) {
            result.assert_valid();
        }
        result
    }

    #[must_use]
    pub fn union(&self, other: &MultiRange<T>) -> MultiRange<T>
    where
        T: Ord + Clone,
    {
        let mut iter_self = self.ranges.iter().peekable();
        let mut iter_other = other.ranges.iter().peekable();

        let mut result = Vec::new();
        let mut curr: Option<NonEmptyRange<T>> = None;

        loop {
            let next = match (iter_self.peek(), iter_other.peek()) {
                (Some(l), Some(r)) => {
                    let (l_start, _) = l.as_ref().bounds();
                    let (r_start, _) = r.as_ref().bounds();
                    if l_start <= r_start {
                        iter_self.next().unwrap()
                    } else {
                        iter_other.next().unwrap()
                    }
                }
                (Some(_), None) => iter_self.next().unwrap(),
                (None, Some(_)) => iter_other.next().unwrap(),
                (None, None) => break,
            };

            match &mut curr {
                None => {
                    curr = Some(next.clone());
                }
                Some(curr) => {
                    let (_, curr_end) = curr.as_ref().bounds();
                    let (next_start, next_end) = next.as_ref().bounds();

                    if next_start <= curr_end {
                        if next_end > curr_end {
                            curr.end = next.end.clone();
                        }
                    } else {
                        result.push(std::mem::replace(curr, next.clone()));
                    }
                }
            }
        }

        if let Some(curr) = curr {
            result.push(curr);
        }

        let result = MultiRange { ranges: result };
        if cfg!(debug_assertions) {
            result.assert_valid();
        }
        result
    }

    #[must_use]
    pub fn intersect(&self, other: &MultiRange<T>) -> MultiRange<T>
    where
        T: Ord + Clone,
    {
        self.complement().union(&other.complement()).complement()
    }

    #[must_use]
    pub fn subtract(&self, range: &MultiRange<T>) -> MultiRange<T>
    where
        T: Ord + Clone,
    {
        self.complement().union(range).complement()
    }

    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> MultiRange<U> {
        let ranges = self
            .ranges
            .into_iter()
            .map(|r| NonEmptyRange {
                start: r.start.map(&mut f),
                end: r.end.map(&mut f),
            })
            .collect();
        MultiRange { ranges }
    }
}

impl<T> AnyMultiRange<T> for MultiRange<T> {
    fn as_multi_range(&self) -> &MultiRange<T> {
        self
    }
}

impl<T> ClosedMultiRange<T> {
    pub const EMPTY: ClosedMultiRange<T> = ClosedMultiRange {
        inner: MultiRange::EMPTY,
    };

    fn assert_valid(&self)
    where
        T: Ord,
    {
        self.inner.assert_valid();

        // check that enclosing range is closed
        if let Some(range) = self.enclosing() {
            range.assert_valid();
        }
    }

    pub fn enclosing(&self) -> Option<ClosedNonEmptyRange<&T>>
    where
        T: Ord,
    {
        Some(
            ClosedNonEmptyRange::try_from(self.inner.enclosing()?)
                .expect("started from closed, result should be closed again"),
        )
    }

    pub fn ranges(&self) -> impl Iterator<Item = ClosedNonEmptyRange<&T>>
    where
        T: Ord,
    {
        self.inner.ranges.iter().map(|r| {
            let r = r.as_ref();
            ClosedNonEmptyRange::try_from(r).unwrap()
        })
    }

    #[must_use]
    pub fn intersect(&self, other: &MultiRange<T>) -> ClosedMultiRange<T>
    where
        T: Ord + Clone,
    {
        // intersecting with a closed range will always yield a closed (possibly empty) range
        ClosedMultiRange {
            inner: self.inner.intersect(other),
        }
    }

    #[must_use]
    pub fn subtract(&self, range: &MultiRange<T>) -> ClosedMultiRange<T>
    where
        T: Ord + Clone,
    {
        // subtracting from a closed range will always yield a closed (possibly empty) range
        ClosedMultiRange {
            inner: self.inner.subtract(range),
        }
    }
}

impl ClosedMultiRange<BigInt> {
    pub fn len(&self) -> BigUint {
        self.ranges().map(|r| BigUint::try_from(r.end - r.start).unwrap()).sum()
    }
}

impl<T> ClosedNonEmptyMultiRange<T> {
    pub fn ranges(&self) -> impl Iterator<Item = ClosedNonEmptyRange<&T>>
    where
        T: Ord,
    {
        self.inner.ranges.iter().map(|r| {
            let r = r.as_ref();
            ClosedNonEmptyRange::try_from(r).unwrap()
        })
    }

    pub fn enclosing(&self) -> ClosedNonEmptyRange<&T> {
        ClosedNonEmptyRange {
            start: self.inner.ranges.first().unwrap().start.as_ref().unwrap(),
            end: self.inner.ranges.last().unwrap().end.as_ref().unwrap(),
        }
    }

    #[must_use]
    pub fn union(&self, other: &ClosedMultiRange<T>) -> ClosedNonEmptyMultiRange<T>
    where
        T: Ord + Clone,
    {
        // self is closed and non-empty, so union with another closed range will also always be closed and non-empty
        ClosedNonEmptyMultiRange {
            inner: self.inner.union(&other.inner),
        }
    }
}

impl<T: Ord> From<Range<T>> for MultiRange<T> {
    fn from(value: Range<T>) -> Self {
        let ranges = match NonEmptyRange::try_from(value) {
            Ok(non_empty) => vec![non_empty],
            Err(RangeEmpty) => vec![],
        };
        let result = MultiRange { ranges };
        if cfg!(debug_assertions) {
            result.assert_valid();
        }
        result
    }
}

impl<T: Ord> From<ClosedRange<T>> for ClosedMultiRange<T> {
    fn from(value: ClosedRange<T>) -> Self {
        let inner = MultiRange::from(Range::from(value));
        let result = ClosedMultiRange { inner };
        if cfg!(debug_assertions) {
            result.assert_valid();
        }
        result
    }
}

impl<T: Ord> From<ClosedNonEmptyRange<T>> for ClosedNonEmptyMultiRange<T> {
    fn from(value: ClosedNonEmptyRange<T>) -> Self {
        ClosedNonEmptyMultiRange {
            inner: MultiRange::from(Range::from(value)),
        }
    }
}

impl<T: Ord> From<ClosedNonEmptyRange<T>> for ClosedMultiRange<T> {
    fn from(value: ClosedNonEmptyRange<T>) -> Self {
        ClosedMultiRange::from(ClosedRange::from(value))
    }
}

impl<T: Ord> From<ClosedNonEmptyMultiRange<T>> for ClosedMultiRange<T> {
    fn from(value: ClosedNonEmptyMultiRange<T>) -> Self {
        ClosedMultiRange { inner: value.inner }
    }
}

impl<T> TryFrom<ClosedMultiRange<T>> for ClosedNonEmptyMultiRange<T> {
    type Error = RangeEmpty;
    fn try_from(value: ClosedMultiRange<T>) -> Result<Self, Self::Error> {
        let ClosedMultiRange { inner } = value;
        if inner.is_empty() {
            Err(RangeEmpty)
        } else {
            Ok(ClosedNonEmptyMultiRange { inner })
        }
    }
}

impl<T> TryFrom<MultiRange<T>> for ClosedMultiRange<T> {
    type Error = RangeOpen;
    fn try_from(value: MultiRange<T>) -> Result<Self, Self::Error> {
        match (value.ranges.first(), value.ranges.last()) {
            (Some(first), Some(last)) if first.start.is_none() || last.end.is_none() => Err(RangeOpen),
            _ => Ok(ClosedMultiRange { inner: value }),
        }
    }
}

impl<T> TryFrom<MultiRange<T>> for ClosedNonEmptyMultiRange<T> {
    type Error = Either<RangeEmpty, RangeOpen>;
    fn try_from(value: MultiRange<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(Either::Left(RangeEmpty))
        } else if value.ranges.first().unwrap().start.is_none() || value.ranges.last().unwrap().end.is_none() {
            Err(Either::Right(RangeOpen))
        } else {
            Ok(ClosedNonEmptyMultiRange { inner: value })
        }
    }
}

impl<T: Display> Debug for MultiRange<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let MultiRange { ranges } = self;
        write!(f, "MultiRange({})", ranges.iter().format(", "))
    }
}

impl<T: Display> Display for MultiRange<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let MultiRange { ranges } = self;
        write!(f, "{}", ranges.iter().format(", "))
    }
}

macro_rules! impl_common {
    ($R:ident) => {
        impl<T> AnyMultiRange<T> for $R<T> {
            fn as_multi_range(&self) -> &MultiRange<T> {
                &self.inner
            }
        }

        impl<T> $R<T> {
            pub fn map<U>(self, f: impl FnMut(T) -> U) -> $R<U> {
                $R {
                    inner: self.inner.map(f),
                }
            }
        }

        impl<T: AnyInt> $R<T> {
            pub fn single(value: T) -> $R<T> {
                $R {
                    inner: MultiRange::single(value),
                }
            }
        }

        impl<T: Display> Debug for $R<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let $R { inner } = self;
                write!(f, "{}({})", stringify!($R), inner.ranges.iter().format(", "))
            }
        }

        impl<T: Display> Display for $R<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.inner)
            }
        }

        impl<T> From<$R<T>> for MultiRange<T> {
            fn from(value: $R<T>) -> Self {
                value.inner
            }
        }
    };
}

impl_common!(ClosedMultiRange);
impl_common!(ClosedNonEmptyMultiRange);

#[cfg(test)]
mod tests {
    use crate::util::range::{NonEmptyRange, Range};
    use crate::util::range_multi::MultiRange;
    use itertools::Itertools;

    #[test]
    fn test_remove_nothing() {
        test_remove_util(&[Some(0)..Some(8)], Some(10)..Some(11), &[Some(0)..Some(8)]);
        test_remove_util(&[Some(0)..Some(8)], Some(8)..Some(11), &[Some(0)..Some(8)]);
        test_remove_util(&[Some(0)..Some(8)], Some(-2)..Some(0), &[Some(0)..Some(8)]);
    }

    #[test]
    fn test_remove_full() {
        test_remove_util::<_, _, i8>(&[0..8], 0..8, &[]);
        test_remove_util::<_, _, i8>(&[0..8], -2..11, &[]);

        test_remove_util(&[2..5, 6..9, 10..13], 1..10, &[10..13]);
    }

    #[test]
    fn test_remove_split_edge() {
        test_remove_util(&[0..8], 4..11, &[0..4]);
        test_remove_util(&[0..8], -2..4, &[4..8]);
        test_remove_util(&[0..4, 6..10], 2..9, &[0..2, 9..10]);
    }

    #[test]
    fn test_remove_split_inside() {
        test_remove_util(&[0..8], 2..5, &[0..2, 5..8]);
        test_remove_util(&[0..4, 6..10], 7..9, &[0..4, 6..7, 9..10]);
    }

    #[test]
    fn test_remove_split_edge_and_full() {
        test_remove_util(&[0..4, 5..8, 9..12], 2..11, &[0..2, 11..12]);
    }

    #[test]
    fn test_complement() {
        test_complement_util::<i8, Option<i8>>(&[], &[None..None]);

        test_complement_util(&[None..Some(9)], &[Some(9)..None]);
        test_complement_util(&[Some(4)..Some(9)], &[None..Some(4), Some(9)..None]);
        test_complement_util(&[Some(4)..Some(9), Some(10)..None], &[None..Some(4), Some(9)..Some(10)]);
        test_complement_util(&[None..Some(9), Some(10)..None], &[Some(9)..Some(10)]);
    }

    #[test]
    fn test_union_empty() {
        test_union_util::<i8, i8>(&[], &[], &[]);
        test_union_util::<i8, i8>(&[], &[0..6], &[0..6]);
    }

    #[test]
    fn test_union_non_overlapping() {
        test_union_util(&[0..4], &[5..8], &[0..4, 5..8]);
        test_union_util(&[0..4, 10..13], &[5..8], &[0..4, 5..8, 10..13]);
        test_union_util(&[0..4], &[5..8, 10..13], &[0..4, 5..8, 10..13]);
    }

    #[test]
    fn test_union_overlapping() {
        test_union_util(&[0..6], &[3..9], &[0..9]);
        test_union_util(&[0..6], &[5..9], &[0..9]);
        test_union_util(&[0..6, 10..16], &[3..13], &[0..16]);
    }

    #[test]
    fn test_union_adjacent() {
        test_union_util(&[0..6], &[6..11], &[0..11]);
        test_union_util(&[0..6, 10..16], &[6..10], &[0..16]);
    }

    #[test]
    fn test_union_contained() {
        test_union_util(&[0..11], &[3..8], &[0..11]);
        test_union_util(&[3..8], &[0..11], &[0..11]);
    }

    #[test]
    fn test_union_open_ranges() {
        test_union_util(&[None..Some(6)], &[Some(10)..None], &[None..Some(6), Some(10)..None]);
        test_union_util(&[None..Some(6)], &[Some(3)..None], &[None..None]);
        test_union_util(&[Some(0)..Some(6)], &[None..Some(4)], &[None..Some(6)]);
    }

    fn build_range<I: Into<Option<i8>>>(range: std::ops::Range<I>) -> NonEmptyRange<i8> {
        let std::ops::Range { start, end } = range;
        let result = NonEmptyRange {
            start: start.into(),
            end: end.into(),
        };
        result.assert_valid();
        result
    }

    fn build_multi_range<I: Into<Option<i8>> + Clone>(ranges: &[std::ops::Range<I>]) -> MultiRange<i8> {
        let initial = ranges.iter().map(|r| build_range(r.clone())).collect_vec();
        let result = MultiRange { ranges: initial };
        result.assert_valid();
        result
    }

    fn test_remove_util<I: Into<Option<i8>> + Clone, R: Into<Option<i8>> + Clone, E: Into<Option<i8>> + Clone>(
        initial: &[std::ops::Range<I>],
        remove: std::ops::Range<R>,
        expected: &[std::ops::Range<E>],
    ) {
        let initial = build_multi_range(initial);

        let remove_range = MultiRange::from(Range::from(build_range(remove)));
        let result = initial.subtract(&remove_range);

        let expected = build_multi_range(expected);
        assert_eq!(result, expected);
    }

    fn test_complement_util<A: Into<Option<i8>> + Clone, B: Into<Option<i8>> + Clone>(
        a: &[std::ops::Range<A>],
        b: &[std::ops::Range<B>],
    ) {
        let a = build_multi_range(a);
        let b = build_multi_range(b);

        assert_eq!(a, b.complement());
        assert_eq!(b, a.complement());
    }

    fn test_union_util<A: Into<Option<i8>> + Clone, B: Into<Option<i8>> + Clone>(
        a: &[std::ops::Range<A>],
        b: &[std::ops::Range<B>],
        expected: &[std::ops::Range<A>],
    ) {
        let a = build_multi_range(a);
        let b = build_multi_range(b);
        let expected = build_multi_range(expected);

        let result = a.union(&b);
        result.assert_valid();
        assert_eq!(result, expected);

        let result_reverse = b.union(&a);
        result_reverse.assert_valid();
        assert_eq!(result_reverse, expected);
    }
}
