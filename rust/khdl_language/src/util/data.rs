use crate::util::iter::IterExt;
use crate::util::{Never, ResultNeverExt};
use indexmap::IndexMap;
use indexmap::map::Entry;
use std::cell::RefCell;
use std::hash::Hash;
use std::ops::{Deref, DerefMut, Range};

// TODO add function to get entry with borrowed key, only cloning the key if necessary
pub trait IndexMapExt<K, V> {
    // The same as [IndexMap::insert], but asserts that the key is not already present.
    fn insert_first(&mut self, key: K, value: V) -> &mut V;

    fn sort_by_key<T: Ord>(&mut self, f: impl FnMut(&K, &V) -> T);

    fn get_index_owned(self, index: usize) -> Option<(K, V)>;
}

impl<K, V> IndexMapExt<K, V> for IndexMap<K, V>
where
    K: Eq + Hash,
{
    fn insert_first(&mut self, key: K, value: V) -> &mut V {
        match self.entry(key) {
            Entry::Occupied(_) => panic!("entry already exists"),
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    fn sort_by_key<T: Ord>(&mut self, mut f: impl FnMut(&K, &V) -> T) {
        self.sort_by(|k0, v0, k1, v1| f(k0, v0).cmp(&f(k1, v1)));
    }

    fn get_index_owned(mut self, index: usize) -> Option<(K, V)> {
        self.swap_remove_index(index)
    }
}

pub trait VecExt<T>: Sized {
    fn into_vec(self) -> Vec<T>;
    fn as_vec(&self) -> &Vec<T>;
    fn as_vec_mut(&mut self) -> &mut Vec<T>;

    fn single(self) -> Result<T, Vec<T>> {
        let mut slf = self.into_vec();
        if slf.len() == 1 {
            Ok(slf.pop().unwrap())
        } else {
            Err(slf)
        }
    }

    fn single_ref(&self) -> Option<&T> {
        let slf = self.as_vec();
        if slf.len() == 1 { Some(&slf[0]) } else { None }
    }

    fn with_pushed<R>(&mut self, v: T, f: impl FnOnce(&mut Vec<T>) -> R) -> R {
        let slf = self.as_vec_mut();

        slf.push(v);
        let result = f(slf);
        assert!(slf.pop().is_some());
        result
    }

    fn insert_iter(&mut self, index: usize, iter: impl IntoIterator<Item = T>) {
        let slf = self.as_vec_mut();
        drop(slf.splice(index..index, iter));
    }

    fn retain_range(&mut self, range: Range<usize>, mut f: impl FnMut(&T) -> bool) {
        let slf = self.as_vec_mut();
        let Range { start, end } = range;

        let mut write = start;
        for read in start..end {
            let retain = f(&slf[read]);
            if retain {
                slf.swap(read, write);
                write += 1;
            }
        }

        drop(slf.drain(write..end));
    }

    fn get_owned(self, index: usize) -> T {
        let mut slf = self.into_vec();
        slf.swap_remove(index)
    }

    fn slice_owned(self, range: Range<usize>) -> Vec<T> {
        let mut slf = self.into_vec();
        let Range { start, end } = range;

        slf.truncate(end);
        drop(slf.drain(..start));

        slf
    }
}

impl<T> VecExt<T> for Vec<T> {
    fn into_vec(self) -> Vec<T> {
        self
    }
    fn as_vec(&self) -> &Vec<T> {
        self
    }
    fn as_vec_mut(&mut self) -> &mut Vec<T> {
        self
    }
}

pub fn vec_concat<const N: usize, T>(vecs: [Vec<T>; N]) -> Vec<T> {
    let mut result = vec![];
    for vec in vecs {
        result.extend(vec);
    }
    result
}

/// Workaround for https://github.com/rust-lang/rust/issues/34162
pub trait SliceExt<T> {
    fn sort_by_key_ref<K: Ord>(&mut self, f: impl FnMut(&T) -> &K);
}

impl<T> SliceExt<T> for [T] {
    fn sort_by_key_ref<K: Ord>(&mut self, mut f: impl FnMut(&T) -> &K) {
        self.sort_by(|a, b| f(a).cmp(f(b)));
    }
}

/// Variant of Vec that provides stable references to its elements.
/// In return it's not possible to remove elements from it.
pub struct StableVec<T> {
    // TODO instead of boxing, use a stack of growing arrays?
    inner: RefCell<Vec<Box<T>>>,
}

impl<T> StableVec<T> {
    pub fn new() -> Self {
        Self {
            inner: RefCell::new(Vec::new()),
        }
    }

    pub fn push(&self, value: T) -> &T {
        let boxed = Box::new(value);
        let ptr = boxed.as_ref() as *const T;
        self.inner.borrow_mut().push(boxed);
        unsafe { &*ptr }
    }

    pub fn into_vec(self) -> Vec<Box<T>> {
        self.inner.into_inner()
    }

    pub fn len(&self) -> usize {
        self.inner.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.borrow().is_empty()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct NonEmptyVec<T> {
    inner: Vec<T>,
}

#[derive(Debug)]
pub struct EmptyVec;

impl<T> NonEmptyVec<T> {
    pub fn new_single(value: T) -> Self {
        Self { inner: vec![value] }
    }

    pub fn first(&self) -> &T {
        &self.inner[0]
    }

    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> NonEmptyVec<U> {
        self.try_map::<U, Never>(|v| Ok(f(v))).remove_never()
    }

    pub fn try_map<U, E>(self, f: impl FnMut(T) -> Result<U, E>) -> Result<NonEmptyVec<U>, E> {
        let inner = self.inner.into_iter().map(f).try_collect_vec()?;
        Ok(NonEmptyVec { inner })
    }

    pub fn try_map_ref<U, E>(&self, f: impl FnMut(&T) -> Result<U, E>) -> Result<NonEmptyVec<U>, E> {
        let inner = self.inner.iter().map(f).try_collect_vec()?;
        Ok(NonEmptyVec { inner })
    }
}

impl<T> TryFrom<Vec<T>> for NonEmptyVec<T> {
    type Error = EmptyVec;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(EmptyVec)
        } else {
            Ok(Self { inner: value })
        }
    }
}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<T> Deref for NonEmptyVec<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for NonEmptyVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

/// Visit all keys that exist in either map, only once.
pub fn chain_keys<'k, K: Eq + Hash, V, W>(
    left: &'k IndexMap<K, V>,
    right: &'k IndexMap<K, W>,
) -> impl Iterator<Item = &'k K> {
    left.keys().chain(right.keys().filter(|&k| !left.contains_key(k)))
}
