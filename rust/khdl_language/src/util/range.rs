use crate::util::big_int::{AnyInt, BigInt, BigUint};
use itertools::Either;
use std::fmt::{Debug, Display, Formatter};

/// Most general range. Bounds can be open/closed and the range can be empty.
/// Invariant: `start <= end`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Range<T> {
    /// Inclusive start, or None if no lower bound
    pub start: Option<T>,
    /// Exclusive end, or None if nu upper bound.
    pub end: Option<T>,
}

/// Closed range, can be empty.
/// Invariant: `start <= end`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ClosedRange<T> {
    /// Inclusive start.
    pub start: T,
    /// Exclusive end.
    pub end: T,
}

/// Non-empty range (guaranteed to contain at least one element), bounds can be open/closed.
/// Invariant: `start < end`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct NonEmptyRange<T> {
    /// Inclusive start, or None if no lower bound
    pub start: Option<T>,
    /// Exclusive end, or None if nu upper bound.
    pub end: Option<T>,
}

/// Non-empty closed range.
/// Invariant: `start < end`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ClosedNonEmptyRange<T> {
    pub start: T,
    pub end: T,
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum RangeBound<T> {
    // the order of these members is important because it determines comparison behavior
    OpenStart,
    Closed(T),
    OpenEnd,
}

pub struct ClosedIncRangeIterator<T> {
    next: T,
    end: T,
}

// TODO move these iterators to bit_int
impl IntoIterator for ClosedRange<BigUint> {
    type Item = BigUint;
    type IntoIter = ClosedIncRangeIterator<BigUint>;

    fn into_iter(self) -> Self::IntoIter {
        ClosedIncRangeIterator {
            next: self.start,
            end: self.end,
        }
    }
}

impl Iterator for ClosedIncRangeIterator<BigUint> {
    type Item = BigUint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.end {
            let curr = self.next.clone();
            self.next += 1u8;
            Some(curr)
        } else {
            None
        }
    }
}

impl IntoIterator for ClosedRange<BigInt> {
    type Item = BigInt;
    type IntoIter = ClosedIncRangeIterator<BigInt>;

    fn into_iter(self) -> Self::IntoIter {
        ClosedIncRangeIterator {
            next: self.start,
            end: self.end,
        }
    }
}

impl Iterator for ClosedIncRangeIterator<BigInt> {
    type Item = BigInt;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.end {
            let curr = self.next.clone();
            self.next += 1u8;
            Some(curr)
        } else {
            None
        }
    }
}

// From/TryFrom
impl<T> From<ClosedRange<T>> for Range<T> {
    fn from(value: ClosedRange<T>) -> Self {
        let ClosedRange { start, end } = value;
        Range {
            start: Some(start),
            end: Some(end),
        }
    }
}

impl<T> From<NonEmptyRange<T>> for Range<T> {
    fn from(value: NonEmptyRange<T>) -> Self {
        let NonEmptyRange { start, end } = value;
        Range { start, end }
    }
}

impl<T> From<ClosedNonEmptyRange<T>> for Range<T> {
    fn from(value: ClosedNonEmptyRange<T>) -> Self {
        let ClosedNonEmptyRange { start, end } = value;
        Range {
            start: Some(start),
            end: Some(end),
        }
    }
}

impl<T> From<ClosedNonEmptyRange<T>> for ClosedRange<T> {
    fn from(value: ClosedNonEmptyRange<T>) -> Self {
        let ClosedNonEmptyRange { start, end } = value;
        ClosedRange { start, end }
    }
}

impl<T> From<ClosedNonEmptyRange<T>> for NonEmptyRange<T> {
    fn from(value: ClosedNonEmptyRange<T>) -> Self {
        let ClosedNonEmptyRange { start, end } = value;
        NonEmptyRange {
            start: Some(start),
            end: Some(end),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RangeEmpty;

#[derive(Debug, Copy, Clone)]
pub struct RangeOpen;

impl<T> TryFrom<Range<T>> for ClosedRange<T> {
    type Error = RangeOpen;

    fn try_from(value: Range<T>) -> Result<Self, Self::Error> {
        let Range { start, end } = value;
        Ok(ClosedRange {
            start: start.ok_or(RangeOpen)?,
            end: end.ok_or(RangeOpen)?,
        })
    }
}

impl<T> TryFrom<NonEmptyRange<T>> for ClosedRange<T> {
    type Error = RangeOpen;

    fn try_from(value: NonEmptyRange<T>) -> Result<Self, Self::Error> {
        ClosedRange::try_from(Range::from(value))
    }
}

impl<T: Ord> TryFrom<ClosedRange<T>> for NonEmptyRange<T> {
    type Error = RangeEmpty;

    fn try_from(value: ClosedRange<T>) -> Result<Self, Self::Error> {
        NonEmptyRange::try_from(Range::from(value))
    }
}

impl<T: Ord> TryFrom<Range<T>> for NonEmptyRange<T> {
    type Error = RangeEmpty;

    fn try_from(value: Range<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(RangeEmpty)
        } else {
            let Range { start, end } = value;
            Ok(NonEmptyRange { start, end })
        }
    }
}

impl<T: Ord> TryFrom<Range<T>> for ClosedNonEmptyRange<T> {
    type Error = Either<RangeEmpty, RangeOpen>;

    fn try_from(value: Range<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(Either::Left(RangeEmpty))
        } else {
            let Range { start, end } = value;
            Ok(ClosedNonEmptyRange {
                start: start.ok_or(Either::Right(RangeOpen))?,
                end: end.ok_or(Either::Right(RangeOpen))?,
            })
        }
    }
}

impl<T: Ord> TryFrom<ClosedRange<T>> for ClosedNonEmptyRange<T> {
    type Error = RangeEmpty;

    fn try_from(value: ClosedRange<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(RangeEmpty)
        } else {
            let ClosedRange { start, end } = value;
            Ok(ClosedNonEmptyRange { start, end })
        }
    }
}

impl<T> TryFrom<NonEmptyRange<T>> for ClosedNonEmptyRange<T> {
    type Error = RangeOpen;

    fn try_from(value: NonEmptyRange<T>) -> Result<Self, Self::Error> {
        let NonEmptyRange { start, end } = value;
        Ok(ClosedNonEmptyRange {
            start: start.ok_or(RangeOpen)?,
            end: end.ok_or(RangeOpen)?,
        })
    }
}

// Common impls for different ranges
macro_rules! impl_common {
    ($R:ident) => {
        impl<T: Ord> $R<T> {
            #[must_use]
            pub fn contains(&self, value: &T) -> bool {
                let (start, end) = self.as_ref().bounds();
                start <= RangeBound::Closed(value) && RangeBound::Closed(value) < end
            }

            #[must_use]
            pub fn contains_range<'o>(&self, other: impl Into<Range<&'o T>>) -> bool
            where
                T: 'o,
            {
                let (slf_start, self_end) = self.as_ref().bounds();
                let (other_start, other_end) = other.into().bounds();

                slf_start <= other_start && other_end <= self_end
            }
        }

        impl<T: Display> Display for $R<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let (start, end) = self.as_ref().bounds();
                match start {
                    RangeBound::Closed(b) => write!(f, "{b}")?,
                    RangeBound::OpenStart | RangeBound::OpenEnd => {}
                }
                write!(f, "..")?;
                match end {
                    RangeBound::Closed(b) => write!(f, "{b}")?,
                    RangeBound::OpenStart | RangeBound::OpenEnd => {}
                }
                Ok(())
            }
        }

        impl<'a, T: PartialEq> $R<&'a T>
        where
            &'a T: std::ops::Add<u8, Output = T>,
        {
            pub fn as_single(self) -> Option<&'a T> {
                let Range { start, end } = Range::from(self);
                if let (Some(start), Some(end)) = (start, end)
                    && end == &(start + 1u8)
                {
                    Some(start)
                } else {
                    None
                }
            }
        }
    };
}

macro_rules! impl_open {
    ($R:ident) => {
        impl<T> $R<T> {
            pub const OPEN: $R<T> = $R {
                start: None,
                end: None,
            };

            pub fn bounds(self) -> (RangeBound<T>, RangeBound<T>) {
                let $R { start, end } = self;
                (
                    start.map_or(RangeBound::OpenStart, RangeBound::Closed),
                    end.map_or(RangeBound::OpenEnd, RangeBound::Closed),
                )
            }

            pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> $R<U> {
                let $R { start, end } = self;
                $R {
                    start: start.map(&mut f),
                    end: end.map(&mut f),
                }
            }

            pub fn as_ref(&self) -> $R<&T> {
                let $R { start, end } = self;
                $R {
                    start: start.as_ref(),
                    end: end.as_ref(),
                }
            }
        }

        impl<T: Clone> $R<&T> {
            pub fn cloned(self) -> $R<T> {
                let $R { start, end } = self;
                $R {
                    start: start.cloned(),
                    end: end.cloned(),
                }
            }
        }

        impl<T: AnyInt> $R<T> {
            pub fn single(value: T) -> $R<T> {
                let end = value.next();
                $R {
                    start: Some(value),
                    end: Some(end),
                }
            }
        }

        impl<T: Ord> $R<T> {
            pub fn union<'a>(&'a self, other: $R<&'a T>) -> $R<&'a T> {
                let $R {
                    start: a_start,
                    end: a_end,
                } = self;
                let $R {
                    start: b_start,
                    end: b_end,
                } = other;

                let start = match (a_start, b_start) {
                    (Some(a_start), Some(b_start)) => Some(a_start.min(b_start)),
                    (None, _) | (_, None) => None,
                };
                let end = match (a_end, b_end) {
                    (Some(a_end), Some(b_end)) => Some(a_end.max(b_end)),
                    (None, _) | (_, None) => None,
                };

                $R { start, end }
            }
        }
    };
}

macro_rules! impl_closed {
    ($R:ident) => {
        impl<T> $R<T> {
            pub fn bounds(self) -> (RangeBound<T>, RangeBound<T>) {
                let $R { start, end } = self;
                (RangeBound::Closed(start), RangeBound::Closed(end))
            }

            pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> $R<U> {
                let $R { start, end } = self;
                $R {
                    start: f(start),
                    end: f(end),
                }
            }

            pub fn as_ref(&self) -> $R<&T> {
                let $R { start, end } = self;
                $R { start, end }
            }
        }

        impl<T: Clone> $R<&T> {
            pub fn cloned(self) -> $R<T> {
                let $R { start, end } = self;
                $R {
                    start: start.clone(),
                    end: end.clone(),
                }
            }
        }

        impl<T: Ord> $R<T> {
            pub fn union(self, other: $R<T>) -> $R<T> {
                $R {
                    start: self.start.min(other.start),
                    end: self.end.max(other.end),
                }
            }
        }

        impl<T: AnyInt> $R<T> {
            pub fn single(value: T) -> $R<T> {
                let end = value.next();
                $R { start: value, end }
            }
        }
    };
}

macro_rules! impl_maybe_empty {
    ($R:ident) => {
        impl<T: Ord> $R<T> {
            pub fn assert_valid(&self) {
                let (start, end) = self.as_ref().bounds();
                assert!(start <= end);
            }

            #[must_use]
            pub fn is_empty(&self) -> bool {
                let (start, end) = self.as_ref().bounds();
                start == end
            }
        }
    };
}

macro_rules! impl_non_empty {
    ($R:ident) => {
        impl<T: Ord> $R<T> {
            pub fn assert_valid(&self) {
                let (start, end) = self.as_ref().bounds();
                assert!(start < end);
            }
        }
    };
}

impl_common!(Range);
impl_common!(ClosedRange);
impl_common!(NonEmptyRange);
impl_common!(ClosedNonEmptyRange);

impl_open!(Range);
impl_open!(NonEmptyRange);
impl_closed!(ClosedRange);
impl_closed!(ClosedNonEmptyRange);

impl_maybe_empty!(Range);
impl_maybe_empty!(ClosedRange);
impl_non_empty!(NonEmptyRange);
impl_non_empty!(ClosedNonEmptyRange);
