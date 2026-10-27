use crate::util::big_int::BigUint;
use crate::util::range::ClosedRange;
use std::fmt::Debug;
use std::iter::{Map, Peekable};
use std::ops::{ControlFlow, Range};

/// Data structure for arrays that are sparse, not in their values, but in _changes_ to their values.
///
/// Multiple instances instances of this array can be visited together, similar to `zip`,
/// using [ZipArrays::for_each_block].
/// Any combination of  `&SparseChangeArray`, `&mut SparseChangeArray`, `Option` and tuples implements the zip trait.
///
/// For all visitor calls:
///   The number of times the callback is called is not necessarily the same as the length of the array or range,
///   sub-ranges that don't contain any change points are only visited once.
///
/// For mutating visitor calls:
///   Range boundry indices are added to the array,
///   to ensure modifications to the inner element don't incorrectly affect elements outside the range.
///
/// For Eq/PartialEq:
///   These also require the change indices to match between both arrays, not just the values.
///   This is simple to implement, but could be changed in the future is necessary.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SparseChangeArray<T> {
    len: BigUint,
    start: Option<T>,
    changes: Vec<(BigUint, T)>,
}

impl<T> SparseChangeArray<T> {
    pub fn new(len: BigUint, init: T) -> SparseChangeArray<T> {
        let start = if len.is_zero() { None } else { Some(init) };
        SparseChangeArray {
            len,
            start,
            changes: vec![],
        }
    }

    pub fn len(&self) -> &BigUint {
        &self.len
    }

    pub fn get(&self, index: &BigUint) -> &T {
        assert!(index < &self.len);
        self.value_before(self.changes.partition_point(|(i, _)| i <= index))
    }

    fn assert_valid(&self) {
        if self.len.is_zero() {
            assert!(self.start.is_none());
            assert!(self.changes.is_empty());
        } else {
            assert!(self.start.is_some());
        }

        let mut prev_index = &BigUint::ZERO;
        for (index, _) in &self.changes {
            assert!(prev_index < index);
            assert!(index < &self.len);
            prev_index = index;
        }
    }

    /// Remove any duplicate change entries.
    pub fn canonicalize(&mut self)
    where
        T: Eq,
    {
        let Some(start) = self.start.as_ref() else { return };

        let mut write = 0;
        for read in 0..self.changes.len() {
            let curr = &self.changes[read].1;
            let prev = if write == 0 { start } else { &self.changes[write - 1].1 };
            if curr != prev {
                self.changes.swap(write, read);
                write += 1;
            }
        }
        self.changes.truncate(write);

        if cfg!(debug_assertions) {
            self.assert_valid();
        }
    }

    /// The range of change positions that are strictly inside `range`.
    fn change_range(&self, range: ClosedRange<&BigUint>) -> Range<usize> {
        let change_start = self.changes.partition_point(|(i, _)| i <= range.start);
        let change_end = self.changes.partition_point(|(i, _)| i < range.end);
        change_start..change_end
    }

    /// The active value right before change `change`.
    fn value_before(&self, change: usize) -> &T {
        match change.checked_sub(1) {
            None => self.start.as_ref().unwrap(),
            Some(prev) => &self.changes[prev].1,
        }
    }
}

/// A zip iterator over a combination of array views.
pub trait ZipArrays<'a>: Sized {
    /// The same as [Self::for_each_block_in_range], for the the entire arrays.
    fn for_each_block<B>(self, f: impl FnMut(ClosedRange<&BigUint>, Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        let Some(len) = self.len().cloned() else {
            return ControlFlow::Continue(());
        };
        let range = ClosedRange {
            start: &BigUint::ZERO,
            end: &len,
        };
        self.for_each_block_in_range(range, f)
    }

    /// Visit all blocks of the arrays that are inside `range`, calling `f` with the range and value of each block.
    ///
    /// Within each block the value is constant for all arrays.
    /// The start of the first block and the end of the last block always match exactly with the given range.
    fn for_each_block_in_range<B>(
        mut self,
        range: ClosedRange<&BigUint>,
        mut f: impl FnMut(ClosedRange<&BigUint>, Self::Item) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        // check lengths and range, handle empty edge cases
        let Some(len) = self.len() else {
            return ControlFlow::Continue(());
        };
        range.assert_valid();
        assert!(range.end <= len);
        if range.is_empty() {
            return ControlFlow::Continue(());
        }

        // ensure mutable arrays contain all change points we might need
        //   If there are no mutable arrays this can be skipped.
        //   If there is only one mutable array we can skip collecting its change points,
        //     since it is already guaranteed to have them.
        if Self::COUNT_MUT > 0 {
            let mut indices = vec![];
            if !range.start.is_zero() {
                indices.push(range.start.clone());
            }
            if range.end < len {
                indices.push(range.end.clone());
            }
            self.collect_indices(range, Self::COUNT_MUT > 1, &mut indices);
            indices.sort();
            indices.dedup();
            indices.retain(|i| !i.is_zero() && i != len);
            self.ensure_indices(&indices);
        }

        // walk over the union of all change indices
        let mut cursor = self.cursor(range);
        let mut block_start = None;
        loop {
            let (item, next) = Self::cursor_next(&mut cursor, block_start);
            let block = ClosedRange {
                start: block_start.unwrap_or(range.start),
                end: next.unwrap_or(range.end),
            };
            f(block, item)?;

            let Some(next) = next else { break };
            block_start = Some(next);
        }

        // TODO consider calling `canonicalize` on each mutable array here,
        //   to remove the split indices that turned out to be unnecessary
        ControlFlow::Continue(())
    }

    /// Internal types.
    type Item;
    type Cursor;

    /// The number of mutable arrays this zip has.
    const COUNT_MUT: usize;

    /// The length of all arrays, or None if there are none.
    fn len(&self) -> Option<&BigUint>;

    /// Collect all change indices that fall inside the given range in any of the arrays.
    /// Only include those of mutable arrays if `include_mut` is set.
    fn collect_indices(&self, range: ClosedRange<&BigUint>, include_mut: bool, indices: &mut Vec<BigUint>);
    /// Ensure `indices` are present in the arrays, by splitting up blocks if necessary.
    /// This only has to do something for mutable arrays, immutable arrays don't need all indices to be present.
    fn ensure_indices(&mut self, indices: &[BigUint]);

    /// Get the initial cursor for walking through the arrays.
    fn cursor(self, range: ClosedRange<&BigUint>) -> Self::Cursor;
    /// Advance the cursor for all arrays that change at `advance_to`, or advance to the first change if None.
    /// Returns the current item in each array, and the lowest next change index if any.
    fn cursor_next(cursor: &mut Self::Cursor, advance_to: Option<&BigUint>) -> (Self::Item, Option<&'a BigUint>);
}

impl<'a, T> ZipArrays<'a> for &'a SparseChangeArray<T> {
    type Item = &'a T;
    type Cursor = (&'a T, &'a [(BigUint, T)]);

    const COUNT_MUT: usize = 0;

    fn len(&self) -> Option<&BigUint> {
        Some(&self.len)
    }

    fn collect_indices(&self, range: ClosedRange<&BigUint>, _: bool, indices: &mut Vec<BigUint>) {
        indices.extend(self.changes[self.change_range(range)].iter().map(|(i, _)| i.clone()));
    }

    fn ensure_indices(&mut self, _: &[BigUint]) {
        // immutable array, we don't need to do anything
    }

    fn cursor(self, range: ClosedRange<&BigUint>) -> Self::Cursor {
        let changes = self.change_range(range);
        (self.value_before(changes.start), &self.changes[changes])
    }

    fn cursor_next(cursor: &mut Self::Cursor, advance_to: Option<&BigUint>) -> (Self::Item, Option<&'a BigUint>) {
        let (curr, rest) = cursor;
        if let Some(((index, value), rest_next)) = rest.split_first()
            && Some(index) == advance_to
        {
            *curr = value;
            *rest = rest_next;
        }
        (*curr, rest.first().map(pair_first))
    }
}

// Sadly rust does not support specifying a specific function as the type, so we have to use a function pointer.
type MutIterSlice<'a, T> = std::slice::IterMut<'a, (BigUint, T)>;
type MutIterMap<'a, T> = Map<MutIterSlice<'a, T>, fn(&'a mut (BigUint, T)) -> (&'a BigUint, &'a mut T)>;

impl<'a, T: Clone> ZipArrays<'a> for &'a mut SparseChangeArray<T> {
    type Item = &'a mut T;
    type Cursor = (Option<&'a mut T>, Peekable<MutIterMap<'a, T>>);

    const COUNT_MUT: usize = 1;

    fn len(&self) -> Option<&BigUint> {
        Some(&self.len)
    }

    fn collect_indices(&self, range: ClosedRange<&BigUint>, include_mut: bool, indices: &mut Vec<BigUint>) {
        if include_mut {
            (&**self).collect_indices(range, include_mut, indices);
        }
    }

    fn ensure_indices(&mut self, indices: &[BigUint]) {
        // TODO this can be optimized
        for index in indices {
            if let Err(insert) = self.changes.binary_search_by_key(&index, pair_first) {
                let prev_value = self.value_before(insert);
                self.changes.insert(insert, (index.clone(), prev_value.clone()));
            }
        }

        if cfg!(debug_assertions) {
            self.assert_valid();
        }
    }

    fn cursor(self, range: ClosedRange<&BigUint>) -> Self::Cursor {
        let changes = self.change_range(range);
        let SparseChangeArray {
            len: _,
            start,
            changes: all_changes,
        } = self;

        let (before, rest) = all_changes[..changes.end].split_at_mut(changes.start);
        let curr = match before.last_mut() {
            None => start.as_mut().unwrap(),
            Some((_, value)) => value,
        };
        let rest = rest.iter_mut().map(split_pair_mut as fn(_) -> _).peekable();
        (Some(curr), rest)
    }

    fn cursor_next(cursor: &mut Self::Cursor, advance_to: Option<&BigUint>) -> (Self::Item, Option<&'a BigUint>) {
        let (curr, rest) = cursor;
        if let Some((_, value)) = rest.next_if(|&(index, _)| Some(index) == advance_to) {
            *curr = Some(value);
        }
        (curr.take().unwrap(), rest.peek().map(|&(index, _)| index))
    }
}

impl<'a, A: ZipArrays<'a>> ZipArrays<'a> for Option<A> {
    type Item = Option<A::Item>;
    type Cursor = Option<A::Cursor>;

    const COUNT_MUT: usize = A::COUNT_MUT;

    fn len(&self) -> Option<&BigUint> {
        self.as_ref().and_then(A::len)
    }

    fn collect_indices(&self, range: ClosedRange<&BigUint>, include_mut: bool, indices: &mut Vec<BigUint>) {
        if let Some(a) = self {
            a.collect_indices(range, include_mut, indices);
        }
    }

    fn ensure_indices(&mut self, indices: &[BigUint]) {
        if let Some(a) = self {
            a.ensure_indices(indices);
        }
    }

    fn cursor(self, range: ClosedRange<&BigUint>) -> Self::Cursor {
        self.map(|a| a.cursor(range))
    }

    fn cursor_next(cursor: &mut Self::Cursor, advance_to: Option<&BigUint>) -> (Self::Item, Option<&'a BigUint>) {
        let (item, next) = cursor.as_mut().map(|cursor| A::cursor_next(cursor, advance_to)).unzip();
        (item, next.flatten())
    }
}

macro_rules! impl_zip_arrays_tuple {
    ($($A:ident $a:ident),*) => {
        impl<'a, $($A: ZipArrays<'a>),*> ZipArrays<'a> for ($($A,)*) {
            type Item = ($($A::Item,)*);
            type Cursor = ($($A::Cursor,)*);

            const COUNT_MUT: usize = 0 $(+ $A::COUNT_MUT)*;

            fn len(&self) -> Option<&BigUint> {
                let ($($a,)*) = self;
                let mut len = None;
                $(
                    if let Some(a_len) = $a.len() {
                        assert!(len.is_none_or(|len| len == a_len), "array lengths must match");
                        len = Some(a_len);
                    }
                )*
                len
            }

            fn collect_indices(&self, range: ClosedRange<&BigUint>, include_mut: bool, indices: &mut Vec<BigUint>) {
                let ($($a,)*) = self;
                $($a.collect_indices(range, include_mut, indices);)*
            }

            fn ensure_indices(&mut self, indices: &[BigUint]) {
                let ($($a,)*) = self;
                $($a.ensure_indices(indices);)*
            }

            fn cursor(self, range: ClosedRange<&BigUint>) -> Self::Cursor {
                let ($($a,)*) = self;
                ($($a.cursor(range),)*)
            }

            fn cursor_next(cursor: &mut Self::Cursor, advance_to: Option<&BigUint>) -> (Self::Item, Option<&'a BigUint>) {
                let ($($a,)*) = cursor;
                let mut next: Option<&'a BigUint> = None;
                let item = ($({
                    let (item, a_next) = $A::cursor_next($a, advance_to);
                    next = [next, a_next].into_iter().flatten().min();
                    item
                },)*);
                (item, next)
            }
        }
    };
}

impl_zip_arrays_tuple!(A a, B b);
impl_zip_arrays_tuple!(A a, B b, C c);
impl_zip_arrays_tuple!(A a, B b, C c, D d);

fn split_pair_mut<A, B>((a, b): &mut (A, B)) -> (&A, &mut B) {
    (a, b)
}

fn pair_first<A, B>(x: &(A, B)) -> &A {
    &x.0
}

#[cfg(test)]
mod tests {
    use crate::util::big_int::BigUint;
    use crate::util::exhaust::exhaust;
    use crate::util::range::ClosedRange;
    use crate::util::sparse_change_array::{SparseChangeArray, ZipArrays};
    use crate::util::{Never, ResultNeverExt};
    use indexmap::IndexSet;
    use itertools::{Itertools, enumerate};
    use std::ops::ControlFlow;

    #[test]
    fn test_exhaust() {
        const LEN_LIMIT: usize = 6;
        const VALUE_LIMIT: u64 = 3;

        exhaust(|ex| {
            let len = ex.choose(LEN_LIMIT as u64) as usize;
            let array_dense = (0..len).map(|_| ex.choose(VALUE_LIMIT)).collect_vec();
            let array_change = build_from_array(&array_dense, |_| false);

            println!("generated array");
            println!("  dense:  {:?}", array_dense);
            println!("  change: {:?}", array_change);

            for i in 0..len {
                assert_eq!(&array_dense[i], array_change.get(&BigUint::from(i)));
            }

            exhaust(|ex_inner| {
                let range_start = ex_inner.choose((len + 1) as u64);
                let range_end = ex_inner.choose_range(range_start, (len + 1) as u64);
                let range = ClosedRange {
                    start: range_start,
                    end: range_end,
                }
                .map(BigUint::from);

                println!("  visiting range {range_start}..{range_end}");

                // check immutable visit
                //   verify that we get the exact callback sequence we expect
                println!("  immutable");
                let expected_visit = {
                    let mut r = vec![];
                    if len != 0 {
                        let mut prev = None;
                        for &x in &array_dense[range_start as usize..range_end as usize] {
                            if Some(x) != prev {
                                r.push(x);
                                prev = Some(x);
                            }
                        }
                    }
                    r
                };

                let mut expected_cover = vec![false; len];
                expected_cover[range_start as usize..range_end as usize].fill(true);

                let (actual_visit, actual_cover) = {
                    let mut r = vec![];
                    let mut c = vec![false; len];
                    (&array_change)
                        .for_each_block_in_range::<Never>(range.as_ref(), |block, &x| {
                            r.push(x);
                            cover_check_set(&mut c, block);
                            ControlFlow::Continue(())
                        })
                        .remove_never();
                    (r, c)
                };
                assert_eq!(expected_visit, actual_visit);
                assert_eq!(expected_cover, actual_cover);

                // check mutable visit
                //   verify that filling a range works the same for dense and change arrays
                println!("  mutable");

                let mut array_dense_mut = array_dense.clone();
                array_dense_mut[range_start as usize..range_end as usize].fill(VALUE_LIMIT);

                let mut array_change_mut = array_change.clone();
                let mut actual_cover_mut = vec![false; len];

                (&mut array_change_mut)
                    .for_each_block_in_range::<Never>(range.as_ref(), |block, x| {
                        *x = VALUE_LIMIT;
                        cover_check_set(&mut actual_cover_mut, block);
                        ControlFlow::Continue(())
                    })
                    .remove_never();

                assert_array_match(&array_dense_mut, &array_change_mut);
                assert_eq!(expected_cover, actual_cover_mut);
            });
        });
    }

    #[test]
    fn test_zip3_exhaust() {
        const LEN_LIMIT: usize = 5;
        const VALUE_LIMIT: u64 = 2;

        exhaust(|ex| {
            let len = ex.choose(LEN_LIMIT as u64) as usize;

            let mut create_array_pair = || {
                ex.choose_bool().then(|| {
                    let dense = (0..len).map(|_| ex.choose(VALUE_LIMIT)).collect_vec();
                    let change = build_from_array(&dense, |_| false);
                    (dense, change)
                })
            };
            let mut a_pair = create_array_pair();
            let b_pair = create_array_pair();
            let c_pair = create_array_pair();

            println!("generated arrays");
            println!("  a: {:?}", a_pair);
            println!("  b: {:?}", b_pair);
            println!("  c: {:?}", c_pair);

            // we do two checks:
            //   * ensure we've seen all tuples we expected to see (including the order)
            //   * mutate using both dense and change arrays using the same operation, and check that results match
            let op = |seen: &mut IndexSet<(Option<u64>, Option<u64>, Option<u64>)>,
                      a: Option<&mut u64>,
                      b: Option<&u64>,
                      c: Option<&u64>| {
                seen.insert((a.as_ref().map(|a| **a), b.copied(), c.copied()));
                if let Some(a) = a {
                    let b = b.copied().unwrap_or(VALUE_LIMIT);
                    let c = c.copied().unwrap_or(VALUE_LIMIT);
                    if b < c {
                        *a = b + c;
                    }
                }
            };

            // run on dense
            let mut seen_dense = IndexSet::new();
            if a_pair.is_some() || b_pair.is_some() || c_pair.is_some() {
                for i in 0..len {
                    op(
                        &mut seen_dense,
                        a_pair.as_mut().map(|(a, _)| &mut a[i]),
                        b_pair.as_ref().map(|(b, _)| &b[i]),
                        c_pair.as_ref().map(|(c, _)| &c[i]),
                    );
                }
            }

            // run on change
            let mut seen_change = IndexSet::new();
            let mut cover_change = vec![false; len];

            (
                a_pair.as_mut().map(|(_, a)| a),
                b_pair.as_ref().map(|(_, b)| b),
                c_pair.as_ref().map(|(_, c)| c),
            )
                .for_each_block(|block, (a, b, c)| {
                    op(&mut seen_change, a, b, c);
                    cover_check_set(&mut cover_change, block);
                    ControlFlow::Continue(())
                })
                .remove_never();

            // check match (including set order)
            assert_eq!(
                seen_dense.into_iter().collect_vec(),
                seen_change.into_iter().collect_vec()
            );
            if let Some((a_dense, a_change)) = a_pair {
                assert_array_match(&a_dense, &a_change);
            }
        });
    }

    #[test]
    fn test_zip2_range_mut_exhaust() {
        const LEN_LIMIT: usize = 5;
        const VALUE_LIMIT: u64 = 3;

        exhaust(|ex| {
            let len = ex.choose(LEN_LIMIT as u64) as usize;

            let array_a_dense = (0..len).map(|_| ex.choose(VALUE_LIMIT)).collect_vec();
            let array_a_change = build_from_array(&array_a_dense, |_| ex.choose_bool());

            let other_pair = ex.choose_bool().then(|| {
                let dense = (0..len).map(|_| ex.choose(VALUE_LIMIT)).collect_vec();
                let change = build_from_array(&dense, |_| ex.choose_bool());
                (dense, change)
            });

            println!("generated arrays");
            println!("  a dense:  {:?}", array_a_dense);
            println!("  a change: {:?}", array_a_change);
            println!("  other:    {:?}", other_pair);

            exhaust(|ex_inner| {
                let range_start = ex_inner.choose((len + 1) as u64);
                let range_end = ex_inner.choose_range(range_start, (len + 1) as u64);
                let range = ClosedRange {
                    start: range_start,
                    end: range_end,
                }
                .map(BigUint::from);

                println!("  visiting range {range_start}..{range_end}");

                // dense reference run
                let op = |a: &mut u64, b: Option<&u64>| {
                    let b = b.copied().unwrap_or(VALUE_LIMIT);
                    if *a < b {
                        *a += b;
                    }
                };

                let mut expected_dense = array_a_dense.clone();
                for i in range_start as usize..range_end as usize {
                    let b = other_pair.as_ref().map(|(b, _)| &b[i]);
                    op(&mut expected_dense[i], b);
                }

                // sparse run
                let mut actual_change = array_a_change.clone();
                let mut actual_cover = vec![false; len];
                let mut seen = vec![];

                (&mut actual_change, other_pair.as_ref().map(|(_, b)| b))
                    .for_each_block_in_range::<Never>(range.as_ref(), |block, (a, b)| {
                        seen.push((*a, b.copied()));
                        op(a, b);
                        cover_check_set(&mut actual_cover, block);
                        ControlFlow::Continue(())
                    })
                    .remove_never();

                let mut expected_cover = vec![false; len];
                expected_cover[range_start as usize..range_end as usize].fill(true);

                assert_eq!(expected_cover, actual_cover);
                assert_array_match(&expected_dense, &actual_change);
                if range_start < range_end {
                    assert!(!seen.is_empty());
                }
            });
        });
    }

    #[test]
    fn test_canonicalize_exhaust() {
        const LEN_LIMIT: usize = 6;
        const VALUE_LIMIT: u64 = 3;

        exhaust(|ex| {
            let len = ex.choose(LEN_LIMIT as u64) as usize;

            let array_dense = (0..len).map(|_| ex.choose(VALUE_LIMIT)).collect_vec();
            let mut any_dummy = false;
            let mut array_sparse = build_from_array(&array_dense, |_| {
                let d = ex.choose_bool();
                any_dummy |= d;
                d
            });

            println!("dense:  {:?}", array_dense);
            println!("before: {:?}", array_sparse);
            assert_array_match(&array_dense, &array_sparse);

            let changes_before = array_sparse.changes.len();
            array_sparse.canonicalize();
            println!("after:  {:?}", array_sparse);
            assert_array_match(&array_dense, &array_sparse);
            assert_eq!(array_sparse.changes.len() < changes_before, any_dummy);
        });
    }

    fn build_from_array<T: Clone + Eq>(
        array_dense: &[T],
        mut include_dummy_change: impl FnMut(usize) -> bool,
    ) -> SparseChangeArray<T> {
        let result = match array_dense.split_first() {
            None => SparseChangeArray {
                len: BigUint::ZERO,
                start: None,
                changes: vec![],
            },
            Some((first, rest)) => {
                let mut changes = vec![];
                let mut prev = first;
                for (i, curr) in enumerate(rest) {
                    if curr != prev || include_dummy_change(i) {
                        changes.push((BigUint::from(i + 1), curr.clone()));
                        prev = curr;
                    }
                }

                SparseChangeArray {
                    len: BigUint::from(array_dense.len()),
                    start: Some(first.clone()),
                    changes,
                }
            }
        };
        result.assert_valid();
        result
    }

    fn assert_array_match(dense: &[u64], sparse: &SparseChangeArray<u64>) {
        sparse.assert_valid();

        assert_eq!(&BigUint::from(dense.len()), sparse.len());
        for i in 0..dense.len() {
            assert_eq!(&dense[i], sparse.get(&BigUint::from(i)));
        }
    }

    fn cover_check_set(cover: &mut [bool], range: ClosedRange<&BigUint>) {
        let range = range.map(|x| usize::try_from(x).unwrap());
        let range = range.start..range.end;

        for i in range {
            assert!(!cover[i]);
            cover[i] = true;
        }
    }
}
