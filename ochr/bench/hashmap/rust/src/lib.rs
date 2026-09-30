//! A fixed-capacity hash map from `u64` keys to values of any type `V`, with
//! separate chaining.
//!
//! The regions between the FIXED begin and end marker comments must stay byte-identical.
//! Replace every `todo!()` with a real body. You may add private helper functions
//! (and `impl` blocks of private methods) anywhere outside the FIXED regions.

// FIXED-BEGIN types
/// A bucket: a singly linked list of (key, value) entries.
pub enum List<V> {
    Cons(u64, V, Box<List<V>>),
    Nil,
}

/// A hash map from `u64` keys to values of type `V` (any type: no trait bounds).
///
/// `slots` holds `cap` buckets, where `cap` is the argument of `new` and never
/// changes. The entry for key `k` lives in bucket `bucket_index(k, cap)`, that is
/// `slots[k % cap]`. `len` is the number of entries in the map.
pub struct HashMap<V> {
    slots: Vec<List<V>>,
    len: u64,
}

/// The bucket of `key` in a table of `cap` buckets: `key mod cap`.
pub fn bucket_index(key: u64, cap: usize) -> usize {
    (key % (cap as u64)) as usize
}
// FIXED-END types

impl<V> HashMap<V> {
    // FIXED-BEGIN new
    /// An empty map with `cap` buckets. Requires `cap > 0`.
    pub fn new(cap: usize) -> HashMap<V> {
    // FIXED-END new
        todo!()
    }

    // FIXED-BEGIN len
    /// The number of entries.
    pub fn len(&self) -> u64 {
    // FIXED-END len
        todo!()
    }

    // FIXED-BEGIN get
    /// A shared borrow of the value stored under `key`, if any.
    pub fn get(&self, key: u64) -> Option<&V> {
    // FIXED-END get
        todo!()
    }

    // FIXED-BEGIN insert
    /// Stores `value` under `key`, returning the previous value (moved out), if any.
    pub fn insert(&mut self, key: u64, value: V) -> Option<V> {
    // FIXED-END insert
        todo!()
    }

    // FIXED-BEGIN remove
    /// Removes the entry for `key`, returning its value (moved out), if any.
    pub fn remove(&mut self, key: u64) -> Option<V> {
    // FIXED-END remove
        todo!()
    }

    // FIXED-BEGIN get_mut
    /// A mutable borrow of the value stored under `key`.
    /// Requires `key` to be present (panics otherwise).
    pub fn get_mut(&mut self, key: u64) -> &mut V {
    // FIXED-END get_mut
        todo!()
    }
}
