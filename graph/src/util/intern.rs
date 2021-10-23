//! Interning of strings.
//!
//! This module provides an interned string pool `AtomPool` and a map-like
//! data structore `Object` that uses the string pool. It offers two
//! different kinds of atom: a plain `Atom` (an integer) and a `FatAtom` (a
//! reference to the pool and an integer). The former is useful when the
//! pool is known from context whereas the latter carries a reference to the
//! pool and can be used anywhere.

use std::convert::TryFrom;
use std::{collections::HashMap, sync::Arc};

use super::cache_weight::CacheWeight;

// We could probably get away with a `u16` here, but unless we improve the
// layout of `Object`, there's little point in that
type AtomInt = u32;

/// An atom in a pool. To look up the underlying string, surrounding code
/// needs to know the pool for it.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
pub struct Atom(AtomInt);

/// An atom and the underlying pool. A `FatAtom` can be used in place of a
/// `String` or `Word`
pub struct FatAtom {
    pool: Arc<AtomPool>,
    atom: Atom,
}

impl FatAtom {
    pub fn as_str(&self) -> &str {
        self.pool.get(self.atom).expect("atom is in the pool")
    }
}

impl AsRef<str> for FatAtom {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

pub enum Error {
    NotInterned(String),
}

/// A pool of interned strings. Pools can be organized hierarchically with
/// lookups in child pools also considering the parent pool. The chain of
/// pools from a pool through all its ancestors act as one big pool to the
/// outside.
pub struct AtomPool {
    base: Option<Arc<AtomPool>>,
    base_sym: AtomInt,
    atoms: Vec<Box<str>>,
    words: HashMap<Box<str>, Atom>,
}

impl AtomPool {
    /// Create a new root pool.
    pub fn new() -> Self {
        Self {
            base: None,
            base_sym: 0,
            atoms: Vec::new(),
            words: HashMap::new(),
        }
    }

    /// Create a child pool that extends the set of strings interned in the
    /// current pool.
    pub fn child(self: &Arc<Self>) -> Self {
        let base_sym = AtomInt::try_from(self.atoms.len()).unwrap();
        AtomPool {
            base: Some(self.clone()),
            base_sym,
            atoms: Vec::new(),
            words: HashMap::new(),
        }
    }

    /// Get the string for `atom`. Return `None` if the atom is not in this
    /// pool or any of its ancestors.
    pub fn get(&self, atom: Atom) -> Option<&str> {
        if atom.0 < self.base_sym {
            self.base.as_ref().map(|base| base.get(atom)).flatten()
        } else {
            self.atoms
                .get((atom.0 - self.base_sym) as usize)
                .map(|s| s.as_ref())
        }
    }

    /// Get the atom for `word`. Return `None` if the word is not in this
    /// pool or any of its ancestors.
    pub fn lookup(&self, word: &str) -> Option<Atom> {
        if let Some(base) = &self.base {
            if let Some(atom) = base.lookup(word) {
                return Some(atom);
            }
        }

        self.words.get(word).cloned()
    }

    /// Add `word` to this pool if it is not already in it. Return the atom
    /// for the word.
    pub fn intern(&mut self, word: &str) -> Atom {
        if let Some(atom) = self.lookup(word) {
            return atom;
        }

        let atom =
            AtomInt::try_from(self.base_sym as usize + self.atoms.len()).expect("too many atoms");
        let atom = Atom(atom);
        if atom == TOMBSTONE_KEY {
            panic!("too many atoms");
        }
        self.words.insert(Box::from(word), atom);
        self.atoms.push(Box::from(word));
        atom
    }
}

/// A marker for an empty entry in an `Object`
const TOMBSTONE_KEY: Atom = Atom(AtomInt::MAX);

/// A value that can be used as a null value in an `Object`. The null value
/// is used when removing an entry as `Object.remove` does not actually
/// remove the entry but replaces it with a tombstone marker.
pub trait NullValue {
    fn null() -> Self;
}

impl<T: Default> NullValue for T {
    fn null() -> Self {
        T::default()
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Entry<V> {
    key: Atom,
    value: V,
}

/// A map-like data structure that uses an `AtomPool` for its keys. The data
/// structure assumes that reads are much more common than writes, and that
/// entries are rarely removed. It also assumes that each instance has
/// relatively few entries.
#[derive(Clone)]
pub struct Object<V> {
    pool: Arc<AtomPool>,
    // This could be further improved by using two `Vec`s, one for keys and
    // one for values. That would avoid losing memory to padding.
    entries: Vec<Entry<V>>,
}

impl<V> Object<V> {
    /// Create a new `Object` whose keys are interned in `pool`.
    pub fn new(pool: Arc<AtomPool>) -> Self {
        Self {
            pool,
            entries: Vec::new(),
        }
    }

    /// Find the value for `key` in the object. Return `None` if the key is
    /// not present.
    pub fn get(&self, key: &str) -> Option<&V> {
        match self.pool.lookup(key) {
            None => None,
            Some(key) => self
                .entries
                .iter()
                .find(|entry| entry.key == key)
                .map(|entry| &entry.value),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &V)> {
        ObjectIter::new(self)
    }

    /// Return the number of entries in the object.
    #[allow(dead_code)]
    fn len(&self) -> usize {
        self.entries.len()
    }

    /// Add or update an entry to the object. Return the value that was
    /// previously associated with the `key`
    pub fn insert<K: AsRef<str>>(&mut self, key: K, value: V) -> Result<Option<V>, Error> {
        let key = self
            .pool
            .lookup(key.as_ref())
            .ok_or_else(|| Error::NotInterned(key.as_ref().to_string()))?;
        Ok(self.insert_atom(key, value))
    }

    fn insert_atom(&mut self, key: Atom, value: V) -> Option<V> {
        match self.entries.iter_mut().find(|entry| entry.key == key) {
            Some(entry) => Some(std::mem::replace(&mut entry.value, value)),
            None => {
                self.entries.push(Entry { key, value });
                None
            }
        }
    }
}

impl<V: NullValue> Object<V> {
    /// Remove `key` from the object and return the value that was
    /// associated with the `key`. The entry is actually not removed for
    /// efficiency reasons. It is instead replaced with an entry with a
    /// dummy key and a null value.
    pub fn remove(&mut self, key: &str) -> Option<V> {
        match self.pool.lookup(key) {
            None => None,
            Some(key) => self
                .entries
                .iter_mut()
                .find(|entry| entry.key == key)
                .map(|entry| {
                    entry.key = TOMBSTONE_KEY;
                    std::mem::replace(&mut entry.value, V::null())
                }),
        }
    }
}

impl<V: NullValue> Extend<(Atom, V)> for Object<V> {
    fn extend<T: IntoIterator<Item = (Atom, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            if key == TOMBSTONE_KEY {
                continue;
            }
            self.insert_atom(key, value);
        }
    }
}

pub struct ObjectIter<'a, V> {
    pool: &'a AtomPool,
    iter: std::slice::Iter<'a, Entry<V>>,
}

impl<'a, V> ObjectIter<'a, V> {
    fn new(object: &'a Object<V>) -> Self {
        Self {
            pool: object.pool.as_ref(),
            iter: object.entries.as_slice().iter(),
        }
    }
}

impl<'a, V> Iterator for ObjectIter<'a, V> {
    type Item = (&'a str, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.iter.next() {
            if entry.key != TOMBSTONE_KEY {
                // unwrap: we only add entries that are backed by the pool
                let key = self.pool.get(entry.key).unwrap();
                return Some((key, &entry.value));
            }
        }
        None
    }
}

impl<'a, V> IntoIterator for &'a Object<V> {
    type Item = <ObjectIter<'a, V> as Iterator>::Item;

    type IntoIter = ObjectIter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        ObjectIter::new(self)
    }
}

impl<V: CacheWeight> CacheWeight for Entry<V> {
    fn indirect_weight(&self) -> usize {
        self.value.indirect_weight()
    }
}

impl<V: CacheWeight> CacheWeight for Object<V> {
    fn indirect_weight(&self) -> usize {
        self.entries.indirect_weight()
    }
}

impl<V: std::fmt::Debug> std::fmt::Debug for Object<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.entries.fmt(f)
    }
}

impl<V: PartialEq> PartialEq for Object<V> {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.pool, &other.pool) {
            self.entries == other.entries
        } else {
            self.entries
                .iter()
                .zip(other.entries.iter())
                .all(|(x, y)| x.value == y.value && self.pool.get(x.key) == other.pool.get(y.key))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::r;

    use super::*;

    #[test]
    fn simple() {
        let mut intern = AtomPool::new();
        let hello = intern.intern("Hello");
        assert_eq!(Some(hello), intern.lookup("Hello"));
        assert_eq!(None, intern.lookup("World"));
        assert_eq!(Some("Hello"), intern.get(hello));

        // Print some size information, just for understanding better how
        // big these data structures are
        use std::mem;

        println!(
            "pool: {}, arc: {}",
            mem::size_of::<AtomPool>(),
            mem::size_of::<Arc<AtomPool>>()
        );

        println!(
            "Atom: {}, FatAtom: {}",
            mem::size_of::<Atom>(),
            mem::size_of::<FatAtom>(),
        );
        println!(
            "Entry<u64>: {}, Object<u64>: {}",
            mem::size_of::<Entry<u64>>(),
            mem::size_of::<Object<u64>>()
        );
        println!(
            "Entry<Value>: {}, Object<Value>: {}, r::Value: {}",
            mem::size_of::<Entry<r::Value>>(),
            mem::size_of::<Object<r::Value>>(),
            mem::size_of::<r::Value>()
        );
    }

    #[test]
    fn stacked() {
        let mut base = AtomPool::new();
        let bsym = base.intern("base");
        let isym = base.intern("intern");
        let base = Arc::new(base);

        let mut intern = base.child();
        assert_eq!(Some(bsym), intern.lookup("base"));

        assert_eq!(bsym, intern.intern("base"));
        let hello = intern.intern("hello");
        assert_eq!(None, base.get(hello));
        assert_eq!(Some("hello"), intern.get(hello));
        assert_eq!(None, base.lookup("hello"));
        assert_eq!(Some(hello), intern.lookup("hello"));
        assert_eq!(Some(isym), base.lookup("intern"));
        assert_eq!(Some(isym), intern.lookup("intern"));
    }
}
