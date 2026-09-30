//! A fixed-capacity hash map with separate chaining.
//!
//! The regions between the FIXED begin and end marker comments must stay byte-identical.
//! Replace every `todo!()` with a real body. You may add private helper functions
//! (and `impl` blocks of private methods) anywhere outside the FIXED regions.

// FIXED-BEGIN types
/// A bucket: a singly linked list of (key, value) entries.
pub enum List {
    Cons(u64, u64, Box<List>),
    Nil,
}

/// A hash map from `u64` keys to `u64` values.
///
/// `slots` holds `cap` buckets, where `cap` is the argument of `new` and never
/// changes. The entry for key `k` lives in bucket `bucket_index(k, cap)`, that is
/// `slots[k % cap]`. `len` is the number of entries in the map.
pub struct HashMap {
    slots: Vec<List>,
    len: u64,
}

/// The bucket of `key` in a table of `cap` buckets: `key mod cap`.
pub fn bucket_index(key: u64, cap: usize) -> usize {
    (key % (cap as u64)) as usize
}
// FIXED-END types

impl HashMap {
    // FIXED-BEGIN new
    /// An empty map with `cap` buckets. Requires `cap > 0`.
    pub fn new(cap: usize) -> HashMap {
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
    /// The value stored under `key`, if any.
    pub fn get(&self, key: u64) -> Option<u64> {
    // FIXED-END get
        todo!()
    }

    // FIXED-BEGIN insert
    /// Stores `value` under `key`, returning the previous value, if any.
    pub fn insert(&mut self, key: u64, value: u64) -> Option<u64> {
    // FIXED-END insert
        todo!()
    }

    // FIXED-BEGIN remove
    /// Removes the entry for `key`, returning its value, if any.
    pub fn remove(&mut self, key: u64) -> Option<u64> {
    // FIXED-END remove
        todo!()
    }

    // FIXED-BEGIN get_mut
    /// A mutable borrow of the value stored under `key`.
    /// Requires `key` to be present (panics otherwise).
    pub fn get_mut(&mut self, key: u64) -> &mut u64 {
    // FIXED-END get_mut
        todo!()
    }
}
