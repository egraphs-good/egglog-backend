//! A crate with utilities for working with numeric Ids.
use std::{
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
    ops,
};

#[cfg(test)]
mod tests;

/// A trait describing "newtypes" that wrap an integer.
pub trait NumericId: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash + Send + Sync {
    type Rep;
    type Atomic;
    fn new(val: Self::Rep) -> Self;
    fn from_usize(index: usize) -> Self;
    fn index(self) -> usize;
    fn rep(self) -> Self::Rep;
    fn inc(self) -> Self {
        Self::from_usize(self.index() + 1)
    }
}

impl NumericId for usize {
    type Rep = usize;
    type Atomic = std::sync::atomic::AtomicUsize;
    fn new(val: usize) -> Self {
        val
    }
    fn from_usize(index: usize) -> Self {
        index
    }

    fn rep(self) -> usize {
        self
    }

    fn index(self) -> usize {
        self
    }
}

/// A mapping from a [`NumericId`] to some value.
///
/// This mapping is _dense_: it stores a flat array indexed by `K::index()`,
/// with no hashing. For sparse mappings, use a HashMap.
#[derive(Clone)]
pub struct DenseIdMap<K, V> {
    free: Option<FreeList>,
    data: Vec<Slot<V>>,
    _marker: PhantomData<K>,
}

#[derive(Clone, Debug)]
enum Slot<V> {
    Free(FreeListNode),
    Full(V),
}

#[derive(Clone, Debug)]
struct FreeList {
    head: usize,
    last: usize,
}

#[derive(Clone, Debug)]
struct FreeListNode {
    next: Option<usize>,
    prev: Option<usize>,
}

impl<V> From<Slot<V>> for Option<V> {
    fn from(slot: Slot<V>) -> Option<V> {
        match slot {
            Slot::Full(v) => Some(v),
            Slot::Free(_) => None,
        }
    }
}

impl<V> Slot<V> {
    fn as_ref(&self) -> Option<&V> {
        match self {
            Slot::Full(v) => Some(v),
            Slot::Free(_) => None,
        }
    }

    fn as_mut(&mut self) -> Option<&mut V> {
        match self {
            Slot::Full(v) => Some(v),
            Slot::Free(_) => None,
        }
    }

    fn set_prev(&mut self, x: Option<usize>) {
        match self {
            Slot::Full(_) => panic!("tried to set_prev on full slot"),
            Slot::Free(FreeListNode { prev, .. }) => *prev = x,
        }
    }

    fn set_next(&mut self, x: Option<usize>) {
        match self {
            Slot::Full(_) => panic!("tried to set_next on full slot"),
            Slot::Free(FreeListNode { next, .. }) => *next = x,
        }
    }
}

impl<K: NumericId + Debug, V: Debug> Debug for DenseIdMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{:?}", self.free)?;
        let mut map = f.debug_map();
        for (k, v) in self.data.iter().enumerate() {
            map.entry(&k, v);
        }
        map.finish()
    }
}

impl<K, V> Default for DenseIdMap<K, V> {
    fn default() -> Self {
        Self {
            free: Default::default(),
            data: Default::default(),
            _marker: PhantomData,
        }
    }
}

impl<K: NumericId, V> DenseIdMap<K, V> {
    /// Create an empty map with space for `n` entries pre-allocated.
    pub fn with_capacity(n: usize) -> Self {
        let mut res = Self::new();
        res.reserve_space(K::from_usize(n));
        res
    }

    /// Create an empty map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Clear the table's contents.
    pub fn clear(&mut self) {
        self.data.clear();
    }

    /// Get the current capacity for the table.
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Get the number of ids currently indexed by the table (including "null"
    /// entries). This is a less useful version of "length" in other containers.
    pub fn n_ids(&self) -> usize {
        self.data.len()
    }

    /// Insert the given mapping into the table.
    pub fn insert(&mut self, key: K, value: V) {
        #[cfg(test)]
        crate::tests::assert_free_list_invariants(self);

        self.reserve_space(key);

        #[cfg(test)]
        crate::tests::assert_free_list_invariants(self);

        if let Slot::Free(FreeListNode { prev, next }) = self.data[key.index()] {
            #[cfg(test)]
            crate::tests::assert_free_list_invariants(self);

            if let Some(prev) = prev {
                #[cfg(test)]
                crate::tests::assert_free_list_invariants(self);

                self.data[prev].set_next(next);
            }
            if let Some(next) = next {
                self.data[next].set_prev(prev);
            }

            if prev.is_none() && next.is_none() {
                self.free = None;
            } else {
                let Some(free) = &mut self.free else {
                    panic!("free was none but there was a free node")
                };
                if free.head == key.index() {
                    free.head = next.unwrap();
                }
                if free.last == key.index() {
                    free.last = prev.unwrap();
                }
            }
        }
        self.data[key.index()] = Slot::Full(value);
    }

    /// Get the key that would be returned by the next call to [`DenseIdMap::push`].
    pub fn next_id(&self) -> K {
        K::from_usize(self.free.as_ref().map_or(self.data.len(), |x| x.head))
    }

    /// Add the given mapping to the table, returning the key that maps to it,
    pub fn push(&mut self, val: V) -> K {
        let res = self.next_id();
        self.insert(res, val);
        res
    }

    /// Get the current mapping for `key` in the table.
    pub fn get(&self, key: K) -> Option<&V> {
        self.data.get(key.index())?.as_ref()
    }

    /// Get a mutable reference to the current mapping for `key` in the table.
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        // TODO: why does this make sense?
        // self.reserve_space(key);
        self.data.get_mut(key.index())?.as_mut()
    }

    /// Remove the value mapped to by `key` from the table.
    ///
    /// # Panics
    /// This method panics if `key` is not in the table.
    pub fn unwrap_val(&mut self, key: K) -> V {
        self.take(key).unwrap()
    }

    /// Remove the value mapped to by `key` from the table, if it is present.
    pub fn take(&mut self, key: K) -> Option<V> {
        match self.data.get(key.index())? {
            Slot::Free(_) => None,
            Slot::Full(_) => match &mut self.free {
                None => {
                    self.free = Some(FreeList {
                        head: key.index(),
                        last: key.index(),
                    });
                    let mut res = Slot::Free(FreeListNode {
                        prev: None,
                        next: None,
                    });
                    std::mem::swap(&mut res, &mut self.data[key.index()]);
                    Option::from(res)
                }
                Some(free) => {
                    self.data[free.last].set_next(Some(key.index()));
                    let mut res = Slot::Free(FreeListNode {
                        prev: Some(free.last),
                        next: None,
                    });
                    free.last = key.index();
                    std::mem::swap(&mut res, &mut self.data[key.index()]);
                    Option::from(res)
                }
            },
        }
    }

    /// Get the current mapping for `key` in the table, or insert the value
    /// returned by `f` and return a mutable reference to it.
    pub fn get_or_insert(&mut self, key: K, f: impl FnOnce() -> V) -> &mut V {
        if self.get(key).is_none() {
            self.insert(key, f())
        }
        self.get_mut(key).unwrap()
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.data
            .iter()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_ref()?)))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_mut()?)))
    }

    /// Reserve space up to the given key in the table.
    pub fn reserve_space(&mut self, key: K) {
        let old_len = self.data.len();
        let new_len = key.index() + 1;
        if new_len > old_len {
            let mut i = old_len;
            self.data.resize_with(new_len, || {
                let res = Slot::Free(FreeListNode {
                    prev: if i == old_len {
                        self.free.as_ref().map(|x| x.last)
                    } else {
                        Some(i - 1)
                    },
                    next: if i == key.index() { None } else { Some(i + 1) },
                });
                i += 1;
                res
            });

            match &mut self.free {
                Some(free) => {
                    if free.last >= self.data.len() {
                        #[cfg(test)]
                        crate::tests::assert_free_list_invariants(self)
                    } else {
                        self.data[free.last].set_next(Some(old_len));
                        free.last = new_len - 1;
                    }
                }
                None => {
                    self.free = Some(FreeList {
                        head: old_len,
                        last: new_len - 1,
                    })
                }
            }
        }
    }

    pub fn drain(&mut self) -> impl Iterator<Item = (K, V)> + '_ {
        self.free = None;
        self.data
            .drain(..)
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), Option::from(v)?)))
    }
}

impl<K: NumericId, V: Send + Sync> DenseIdMap<K, V> {
    /// Get a parallel iterator over the entries in the table.
    pub fn par_iter(&self) -> impl ParallelIterator<Item = (K, &V)> {
        self.data
            .par_iter()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_ref()?)))
    }

    /// Get a parallel iterator over mutable references to the entries in the table.
    pub fn par_iter_mut(&mut self) -> impl ParallelIterator<Item = (K, &mut V)> {
        self.data
            .par_iter_mut()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_mut()?)))
    }
}

impl<K: NumericId, V> ops::Index<K> for DenseIdMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: NumericId, V> ops::IndexMut<K> for DenseIdMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

impl<K: NumericId, V: Default> DenseIdMap<K, V> {
    pub fn get_or_default(&mut self, key: K) -> &mut V {
        self.get_or_insert(key, V::default)
    }
}

pub struct IdVec<K, V> {
    data: Vec<V>,
    _marker: PhantomData<K>,
}

impl<K, V> Default for IdVec<K, V> {
    fn default() -> IdVec<K, V> {
        IdVec {
            data: Default::default(),
            _marker: PhantomData,
        }
    }
}

impl<K: NumericId, V> IdVec<K, V> {
    pub fn with_capacity(cap: usize) -> IdVec<K, V> {
        IdVec {
            data: Vec::with_capacity(cap),
            _marker: PhantomData,
        }
    }

    pub fn push(&mut self, elt: V) -> K {
        let res = K::from_usize(self.data.len());
        self.data.push(elt);
        res
    }

    pub fn resize_with(&mut self, size: usize, init: impl FnMut() -> V) {
        self.data.resize_with(size, init)
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.data
            .iter()
            .enumerate()
            .map(|(i, v)| (K::from_usize(i), v))
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .map(|(i, v)| (K::from_usize(i), v))
    }
    pub fn drain(&mut self) -> impl Iterator<Item = (K, V)> + '_ {
        self.data
            .drain(..)
            .enumerate()
            .map(|(i, v)| (K::from_usize(i), v))
    }
    pub fn get(&self, key: K) -> Option<&V> {
        self.data.get(key.index())
    }
}

impl<K: NumericId, V: Send + Sync> IdVec<K, V> {
    pub fn par_iter_mut(&mut self) -> impl IndexedParallelIterator<Item = (K, &mut V)> {
        self.data
            .par_iter_mut()
            .with_max_len(1)
            .enumerate()
            .map(|(i, v)| (K::from_usize(i), v))
    }
}

impl<K: NumericId, V> ops::Index<K> for IdVec<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        &self.data[key.index()]
    }
}

impl<K: NumericId, V> ops::IndexMut<K> for IdVec<K, V> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        &mut self.data[key.index()]
    }
}

use rayon::iter::{
    IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator,
};

#[macro_export]
#[doc(hidden)]
macro_rules! atomic_of {
    (usize) => {
        std::sync::atomic::AtomicUsize
    };
    (u8) => {
        std::sync::atomic::AtomicU8
    };
    (u16) => {
        std::sync::atomic::AtomicU16
    };
    (u32) => {
        std::sync::atomic::AtomicU32
    };
    (u64) => {
        std::sync::atomic::AtomicU64
    };
}

#[macro_export]
macro_rules! define_id {
    ($v:vis $name:ident, $repr:tt) => { define_id!($v, $name, $repr, ""); };
    ($v:vis $name:ident, $repr:tt, $doc:tt) => {
        #[derive(Copy, Clone)]
        #[doc = $doc]
        $v struct $name {
            rep: $repr,
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.rep == other.rep
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.rep.cmp(&other.rep)
            }
        }

        impl std::hash::Hash for $name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                self.rep.hash(state);
            }
        }

        impl $name {
            #[allow(unused)]
            $v const fn new_const(id: $repr) -> Self {
                $name {
                    rep: id,
                }
            }

            #[allow(unused)]
            $v fn range(low: Self, high: Self) -> impl Iterator<Item = Self> {
                use $crate::NumericId;
                (low.rep..high.rep).map(|i| $name::new(i))
            }

        }

        impl $crate::NumericId for $name {
            type Rep = $repr;
            type Atomic = $crate::atomic_of!($repr);
            fn new(id: $repr) -> Self {
                Self::new_const(id)
            }
            fn from_usize(index: usize) -> Self {
                assert!(<$repr>::MAX as usize >= index,
                    "overflowing id type {} (represented as {}) with index {}", stringify!($name), stringify!($repr), index);
                $name::new(index as $repr)
            }
            fn index(self) -> usize {
                self.rep as usize
            }
            fn rep(self) -> $repr {
                self.rep
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(fmt, "{}({:?})", stringify!($name), self.rep)
            }
        }
    };
}
