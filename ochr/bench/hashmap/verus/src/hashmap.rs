//! A fixed-capacity hash map with separate chaining, verified with Verus.
//!
//! The FIXED regions (each between a begin and an end marker comment) must stay
//! byte-identical.
//! Fill in every hole:
//!   - the `arbitrary()` bodies of the spec functions `inv`, `spec_get` and `spec_len`;
//!   - the `todo!()` bodies of the exec functions.
//! You may add spec functions, proof functions (lemmas) and private exec helpers anywhere
//! inside the `verus!` block outside the FIXED regions, and a `decreases` clause right
//! after a FIXED signature (before its body). See ASSIGNMENT.md.

// FIXED-BEGIN prelude
use vstd::prelude::*;

verus! {
// FIXED-END prelude

// FIXED-BEGIN types
/// A bucket: a singly linked list of (key, value) entries.
pub enum List<V> {
    Cons(u64, V, Box<List<V>>),
    Nil,
}

/// A hash map from `u64` keys to values of any type `V` (no trait bounds).
///
/// `slots` holds `cap` buckets, where `cap` is the argument of `new` and never
/// changes. The entry for key `k` lives in bucket `bucket_index(k, cap)`, that is
/// `slots[k % cap]`. `len` is the number of entries in the map.
pub struct HashMap<V> {
    slots: Vec<List<V>>,
    len: u64,
}

/// The value an `Option<&V>` observes: `Some(*v)` for `Some(v)`, `None` for `None`.
pub open spec fn observe<V>(r: Option<&V>) -> Option<V> {
    match r {
        Some(v) => Some(*v),
        None => None,
    }
}

/// The bucket of `key` in a table of `cap` buckets: `key mod cap`.
pub fn bucket_index(key: u64, cap: usize) -> (i: usize)
    requires
        cap > 0,
    ensures
        i == key as int % cap as int,
{
    (key % (cap as u64)) as usize
}
// FIXED-END types

// FIXED-BEGIN impl
impl<V> HashMap<V> {
// FIXED-END impl
    // FIXED-BEGIN inv
    /// `Inv`, the representation invariant (SPEC `Inv`). Its definition is yours.
    pub closed spec fn inv(&self) -> bool
    // FIXED-END inv
    {
        arbitrary()
    }

    // FIXED-BEGIN spec_get
    /// The value `get(self, key)` observes, as a spec function. Its definition is
    /// yours; the contract of `get` below ties it to the executable `get`.
    pub closed spec fn spec_get(&self, key: u64) -> Option<V>
    // FIXED-END spec_get
    {
        arbitrary()
    }

    // FIXED-BEGIN spec_len
    /// What `len(self)` returns, as a spec function. Its definition is yours;
    /// the contract of `len` below ties it to the executable `len`.
    pub closed spec fn spec_len(&self) -> nat
    // FIXED-END spec_len
    {
        arbitrary()
    }

    // FIXED-BEGIN new
    /// An empty map with `cap` buckets. Requires `cap > 0`.
    pub fn new(cap: usize) -> (m: HashMap<V>)
        requires
            cap > 0,
        ensures
            m.inv(), // H1
            forall|k: u64| m.spec_get(k) == None::<V>, // H4
            m.spec_len() == 0, // H11
    // FIXED-END new
    {
        todo!()
    }

    // FIXED-BEGIN len
    /// The number of entries.
    pub fn len(&self) -> (n: u64)
        requires
            self.inv(),
        ensures
            n == self.spec_len(),
    // FIXED-END len
    {
        todo!()
    }

    // FIXED-BEGIN get
    /// A shared borrow of the value stored under `key`, if any.
    pub fn get(&self, key: u64) -> (r: Option<&V>)
        requires
            self.inv(),
        ensures
            observe(r) == self.spec_get(key),
    // FIXED-END get
    {
        todo!()
    }

    // FIXED-BEGIN insert
    /// Stores `value` under `key`, returning the previous value (moved out), if any.
    pub fn insert(&mut self, key: u64, value: V) -> (r: Option<V>)
        requires
            old(self).inv(),
            old(self).spec_len() < u64::MAX, // bounded-integer allowance (SPEC section 5)
        ensures
            final(self).inv(), // H2
            final(self).spec_get(key) == Some(value), // H5
            forall|k2: u64| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2), // H6
            r == old(self).spec_get(key), // H7
            final(self).spec_len() == if old(self).spec_get(key) is None {
                old(self).spec_len() + 1
            } else {
                old(self).spec_len()
            }, // H12
    // FIXED-END insert
    {
        todo!()
    }

    // FIXED-BEGIN remove
    /// Removes the entry for `key`, returning its value (moved out), if any.
    pub fn remove(&mut self, key: u64) -> (r: Option<V>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(), // H3
            final(self).spec_get(key) == None::<V>, // H8
            forall|k2: u64| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2), // H9
            r == old(self).spec_get(key), // H10
            final(self).spec_len() == if old(self).spec_get(key) is Some {
                old(self).spec_len() - 1
            } else {
                old(self).spec_len() as int
            }, // H13
    // FIXED-END remove
    {
        todo!()
    }

    // FIXED-BEGIN get_mut
    /// A mutable borrow of the value stored under `key`. Requires `key` to be present.
    ///
    /// Writing `w` through the borrow has the same effect on `spec_get`, `spec_len` and
    /// `inv` as `insert(key, w)` (H14-H16): `final(r)` is the value the caller leaves
    /// behind the borrow, and `final(self)` is the map once the borrow ends.
    pub fn get_mut(&mut self, key: u64) -> (r: &mut V)
        requires
            old(self).inv(),
            old(self).spec_get(key) is Some,
        ensures
            final(self).spec_get(key) == Some(*final(r)), // H14, at `key`
            forall|k2: u64| k2 != key ==> final(self).spec_get(k2) == old(self).spec_get(k2), // H14, elsewhere
            final(self).spec_len() == old(self).spec_len(), // H15
            final(self).inv(), // H16
    // FIXED-END get_mut
    {
        todo!()
    }
}

// FIXED-BEGIN verus-end
} // verus!
// FIXED-END verus-end

// FIXED-BEGIN tests
// The tests, transcribed mechanically from tests.json (SPEC section 6) by a script.
// They run as ordinary Rust in the compiled binary: `./grade.sh` builds it with
// `verus --compile` and runs it. The value type is `V := u64`. Each sequence starts from
// `HashMap::<u64>::new(cap)`; after every op the result (if any) and then `len` are
// checked. `get`'s result is compared through the value it points to (`.copied()`).

struct Tally {
    passed: u64,
    failed: u64,
}

impl Tally {
    fn opt(&mut self, what: &str, got: Option<u64>, want: Option<u64>) {
        if got == want {
            self.passed += 1;
        } else {
            self.failed += 1;
            println!("FAIL {what}: got {got:?}, expected {want:?}");
        }
    }

    fn len(&mut self, what: &str, got: u64, want: u64) {
        if got == want {
            self.passed += 1;
        } else {
            self.failed += 1;
            println!("FAIL {what}: len is {got}, expected {want}");
        }
    }
}

fn seq_scripted(t: &mut Tally) {
    let mut m = HashMap::<u64>::new(4);
    let r = m.get(0).copied(); t.opt("scripted op 1: get(0)", r, None); let n = m.len(); t.len("scripted op 1", n, 0);
    let r = m.remove(3); t.opt("scripted op 2: remove(3)", r, None); let n = m.len(); t.len("scripted op 2", n, 0);
    let r = m.insert(1, 10); t.opt("scripted op 3: insert(1, 10)", r, None); let n = m.len(); t.len("scripted op 3", n, 1);
    let r = m.insert(5, 50); t.opt("scripted op 4: insert(5, 50)", r, None); let n = m.len(); t.len("scripted op 4", n, 2);
    let r = m.insert(9, 90); t.opt("scripted op 5: insert(9, 90)", r, None); let n = m.len(); t.len("scripted op 5", n, 3);
    let r = m.get(1).copied(); t.opt("scripted op 6: get(1)", r, Some(10)); let n = m.len(); t.len("scripted op 6", n, 3);
    let r = m.get(5).copied(); t.opt("scripted op 7: get(5)", r, Some(50)); let n = m.len(); t.len("scripted op 7", n, 3);
    let r = m.get(9).copied(); t.opt("scripted op 8: get(9)", r, Some(90)); let n = m.len(); t.len("scripted op 8", n, 3);
    let r = m.get(13).copied(); t.opt("scripted op 9: get(13)", r, None); let n = m.len(); t.len("scripted op 9", n, 3);
    let r = m.get(2).copied(); t.opt("scripted op 10: get(2)", r, None); let n = m.len(); t.len("scripted op 10", n, 3);
    let r = m.insert(5, 55); t.opt("scripted op 11: insert(5, 55)", r, Some(50)); let n = m.len(); t.len("scripted op 11", n, 3);
    let r = m.get(5).copied(); t.opt("scripted op 12: get(5)", r, Some(55)); let n = m.len(); t.len("scripted op 12", n, 3);
    let r = m.get(1).copied(); t.opt("scripted op 13: get(1)", r, Some(10)); let n = m.len(); t.len("scripted op 13", n, 3);
    let r = m.get(9).copied(); t.opt("scripted op 14: get(9)", r, Some(90)); let n = m.len(); t.len("scripted op 14", n, 3);
    let r = m.insert(0, 0); t.opt("scripted op 15: insert(0, 0)", r, None); let n = m.len(); t.len("scripted op 15", n, 4);
    let r = m.insert(4, 40); t.opt("scripted op 16: insert(4, 40)", r, None); let n = m.len(); t.len("scripted op 16", n, 5);
    let r = m.get(0).copied(); t.opt("scripted op 17: get(0)", r, Some(0)); let n = m.len(); t.len("scripted op 17", n, 5);
    let r = m.remove(5); t.opt("scripted op 18: remove(5)", r, Some(55)); let n = m.len(); t.len("scripted op 18", n, 4);
    let r = m.get(5).copied(); t.opt("scripted op 19: get(5)", r, None); let n = m.len(); t.len("scripted op 19", n, 4);
    let r = m.get(1).copied(); t.opt("scripted op 20: get(1)", r, Some(10)); let n = m.len(); t.len("scripted op 20", n, 4);
    let r = m.get(9).copied(); t.opt("scripted op 21: get(9)", r, Some(90)); let n = m.len(); t.len("scripted op 21", n, 4);
    let r = m.remove(5); t.opt("scripted op 22: remove(5)", r, None); let n = m.len(); t.len("scripted op 22", n, 4);
    let r = m.remove(13); t.opt("scripted op 23: remove(13)", r, None); let n = m.len(); t.len("scripted op 23", n, 4);
    let r = m.remove(1); t.opt("scripted op 24: remove(1)", r, Some(10)); let n = m.len(); t.len("scripted op 24", n, 3);
    let r = m.remove(9); t.opt("scripted op 25: remove(9)", r, Some(90)); let n = m.len(); t.len("scripted op 25", n, 2);
    let r = m.get(9).copied(); t.opt("scripted op 26: get(9)", r, None); let n = m.len(); t.len("scripted op 26", n, 2);
    *m.get_mut(4) = 44; let n = m.len(); t.len("scripted op 27", n, 2);
    let r = m.get(4).copied(); t.opt("scripted op 28: get(4)", r, Some(44)); let n = m.len(); t.len("scripted op 28", n, 2);
    let r = m.get(0).copied(); t.opt("scripted op 29: get(0)", r, Some(0)); let n = m.len(); t.len("scripted op 29", n, 2);
    *m.get_mut(0) = 7; let n = m.len(); t.len("scripted op 30", n, 2);
    let r = m.get(0).copied(); t.opt("scripted op 31: get(0)", r, Some(7)); let n = m.len(); t.len("scripted op 31", n, 2);
    let r = m.get(4).copied(); t.opt("scripted op 32: get(4)", r, Some(44)); let n = m.len(); t.len("scripted op 32", n, 2);
    let r = m.insert(4, 45); t.opt("scripted op 33: insert(4, 45)", r, Some(44)); let n = m.len(); t.len("scripted op 33", n, 2);
    let r = m.insert(1, 11); t.opt("scripted op 34: insert(1, 11)", r, None); let n = m.len(); t.len("scripted op 34", n, 3);
    let r = m.get(1).copied(); t.opt("scripted op 35: get(1)", r, Some(11)); let n = m.len(); t.len("scripted op 35", n, 3);
    let r = m.insert(7, 70); t.opt("scripted op 36: insert(7, 70)", r, None); let n = m.len(); t.len("scripted op 36", n, 4);
    let r = m.insert(3, 30); t.opt("scripted op 37: insert(3, 30)", r, None); let n = m.len(); t.len("scripted op 37", n, 5);
    let r = m.insert(11, 99); t.opt("scripted op 38: insert(11, 99)", r, None); let n = m.len(); t.len("scripted op 38", n, 6);
    *m.get_mut(3) = 33; let n = m.len(); t.len("scripted op 39", n, 6);
    let r = m.get(7).copied(); t.opt("scripted op 40: get(7)", r, Some(70)); let n = m.len(); t.len("scripted op 40", n, 6);
    let r = m.get(3).copied(); t.opt("scripted op 41: get(3)", r, Some(33)); let n = m.len(); t.len("scripted op 41", n, 6);
    let r = m.get(11).copied(); t.opt("scripted op 42: get(11)", r, Some(99)); let n = m.len(); t.len("scripted op 42", n, 6);
    let r = m.remove(11); t.opt("scripted op 43: remove(11)", r, Some(99)); let n = m.len(); t.len("scripted op 43", n, 5);
    let r = m.get(3).copied(); t.opt("scripted op 44: get(3)", r, Some(33)); let n = m.len(); t.len("scripted op 44", n, 5);
    let r = m.remove(0); t.opt("scripted op 45: remove(0)", r, Some(7)); let n = m.len(); t.len("scripted op 45", n, 4);
    let r = m.get(4).copied(); t.opt("scripted op 46: get(4)", r, Some(45)); let n = m.len(); t.len("scripted op 46", n, 4);
    let r = m.remove(4); t.opt("scripted op 47: remove(4)", r, Some(45)); let n = m.len(); t.len("scripted op 47", n, 3);
    let r = m.get(0).copied(); t.opt("scripted op 48: get(0)", r, None); let n = m.len(); t.len("scripted op 48", n, 3);
    let r = m.get(4).copied(); t.opt("scripted op 49: get(4)", r, None); let n = m.len(); t.len("scripted op 49", n, 3);
    let r = m.insert(0, 1); t.opt("scripted op 50: insert(0, 1)", r, None); let n = m.len(); t.len("scripted op 50", n, 4);
    let r = m.get(0).copied(); t.opt("scripted op 51: get(0)", r, Some(1)); let n = m.len(); t.len("scripted op 51", n, 4);
}

fn seq_random_cap1(t: &mut Tally) {
    let mut m = HashMap::<u64>::new(1);
    let r = m.remove(2); t.opt("random-cap1 op 1: remove(2)", r, None); let n = m.len(); t.len("random-cap1 op 1", n, 0);
    let r = m.insert(2, 27); t.opt("random-cap1 op 2: insert(2, 27)", r, None); let n = m.len(); t.len("random-cap1 op 2", n, 1);
    let r = m.remove(2); t.opt("random-cap1 op 3: remove(2)", r, Some(27)); let n = m.len(); t.len("random-cap1 op 3", n, 0);
    let r = m.get(1).copied(); t.opt("random-cap1 op 4: get(1)", r, None); let n = m.len(); t.len("random-cap1 op 4", n, 0);
    let r = m.get(3).copied(); t.opt("random-cap1 op 5: get(3)", r, None); let n = m.len(); t.len("random-cap1 op 5", n, 0);
    let r = m.insert(0, 38); t.opt("random-cap1 op 6: insert(0, 38)", r, None); let n = m.len(); t.len("random-cap1 op 6", n, 1);
    let r = m.insert(7, 65); t.opt("random-cap1 op 7: insert(7, 65)", r, None); let n = m.len(); t.len("random-cap1 op 7", n, 2);
    let r = m.insert(4, 20); t.opt("random-cap1 op 8: insert(4, 20)", r, None); let n = m.len(); t.len("random-cap1 op 8", n, 3);
    let r = m.get(4).copied(); t.opt("random-cap1 op 9: get(4)", r, Some(20)); let n = m.len(); t.len("random-cap1 op 9", n, 3);
    *m.get_mut(7) = 79; let n = m.len(); t.len("random-cap1 op 10", n, 3);
    let r = m.remove(2); t.opt("random-cap1 op 11: remove(2)", r, None); let n = m.len(); t.len("random-cap1 op 11", n, 3);
    let r = m.insert(7, 78); t.opt("random-cap1 op 12: insert(7, 78)", r, Some(79)); let n = m.len(); t.len("random-cap1 op 12", n, 3);
    let r = m.remove(1); t.opt("random-cap1 op 13: remove(1)", r, None); let n = m.len(); t.len("random-cap1 op 13", n, 3);
    let r = m.get(7).copied(); t.opt("random-cap1 op 14: get(7)", r, Some(78)); let n = m.len(); t.len("random-cap1 op 14", n, 3);
    let r = m.get(7).copied(); t.opt("random-cap1 op 15: get(7)", r, Some(78)); let n = m.len(); t.len("random-cap1 op 15", n, 3);
    *m.get_mut(0) = 41; let n = m.len(); t.len("random-cap1 op 16", n, 3);
    let r = m.get(5).copied(); t.opt("random-cap1 op 17: get(5)", r, None); let n = m.len(); t.len("random-cap1 op 17", n, 3);
    let r = m.insert(0, 8); t.opt("random-cap1 op 18: insert(0, 8)", r, Some(41)); let n = m.len(); t.len("random-cap1 op 18", n, 3);
    let r = m.remove(6); t.opt("random-cap1 op 19: remove(6)", r, None); let n = m.len(); t.len("random-cap1 op 19", n, 3);
    let r = m.insert(2, 8); t.opt("random-cap1 op 20: insert(2, 8)", r, None); let n = m.len(); t.len("random-cap1 op 20", n, 4);
    let r = m.get(4).copied(); t.opt("random-cap1 op 21: get(4)", r, Some(20)); let n = m.len(); t.len("random-cap1 op 21", n, 4);
    let r = m.get(7).copied(); t.opt("random-cap1 op 22: get(7)", r, Some(78)); let n = m.len(); t.len("random-cap1 op 22", n, 4);
    let r = m.remove(6); t.opt("random-cap1 op 23: remove(6)", r, None); let n = m.len(); t.len("random-cap1 op 23", n, 4);
    *m.get_mut(4) = 86; let n = m.len(); t.len("random-cap1 op 24", n, 4);
    let r = m.get(5).copied(); t.opt("random-cap1 op 25: get(5)", r, None); let n = m.len(); t.len("random-cap1 op 25", n, 4);
    let r = m.insert(1, 19); t.opt("random-cap1 op 26: insert(1, 19)", r, None); let n = m.len(); t.len("random-cap1 op 26", n, 5);
    let r = m.insert(2, 12); t.opt("random-cap1 op 27: insert(2, 12)", r, Some(8)); let n = m.len(); t.len("random-cap1 op 27", n, 5);
    let r = m.insert(7, 81); t.opt("random-cap1 op 28: insert(7, 81)", r, Some(78)); let n = m.len(); t.len("random-cap1 op 28", n, 5);
    let r = m.get(5).copied(); t.opt("random-cap1 op 29: get(5)", r, None); let n = m.len(); t.len("random-cap1 op 29", n, 5);
    let r = m.remove(6); t.opt("random-cap1 op 30: remove(6)", r, None); let n = m.len(); t.len("random-cap1 op 30", n, 5);
    let r = m.get(2).copied(); t.opt("random-cap1 op 31: get(2)", r, Some(12)); let n = m.len(); t.len("random-cap1 op 31", n, 5);
    let r = m.get(0).copied(); t.opt("random-cap1 op 32: get(0)", r, Some(8)); let n = m.len(); t.len("random-cap1 op 32", n, 5);
    let r = m.insert(4, 0); t.opt("random-cap1 op 33: insert(4, 0)", r, Some(86)); let n = m.len(); t.len("random-cap1 op 33", n, 5);
    let r = m.insert(7, 77); t.opt("random-cap1 op 34: insert(7, 77)", r, Some(81)); let n = m.len(); t.len("random-cap1 op 34", n, 5);
    let r = m.insert(5, 85); t.opt("random-cap1 op 35: insert(5, 85)", r, None); let n = m.len(); t.len("random-cap1 op 35", n, 6);
    let r = m.insert(0, 0); t.opt("random-cap1 op 36: insert(0, 0)", r, Some(8)); let n = m.len(); t.len("random-cap1 op 36", n, 6);
    let r = m.insert(3, 71); t.opt("random-cap1 op 37: insert(3, 71)", r, None); let n = m.len(); t.len("random-cap1 op 37", n, 7);
    let r = m.insert(0, 37); t.opt("random-cap1 op 38: insert(0, 37)", r, Some(0)); let n = m.len(); t.len("random-cap1 op 38", n, 7);
    *m.get_mut(4) = 85; let n = m.len(); t.len("random-cap1 op 39", n, 7);
    *m.get_mut(2) = 26; let n = m.len(); t.len("random-cap1 op 40", n, 7);
    let r = m.insert(3, 5); t.opt("random-cap1 op 41: insert(3, 5)", r, Some(71)); let n = m.len(); t.len("random-cap1 op 41", n, 7);
    let r = m.insert(0, 37); t.opt("random-cap1 op 42: insert(0, 37)", r, Some(37)); let n = m.len(); t.len("random-cap1 op 42", n, 7);
    let r = m.remove(6); t.opt("random-cap1 op 43: remove(6)", r, None); let n = m.len(); t.len("random-cap1 op 43", n, 7);
    let r = m.insert(0, 71); t.opt("random-cap1 op 44: insert(0, 71)", r, Some(37)); let n = m.len(); t.len("random-cap1 op 44", n, 7);
    let r = m.insert(5, 9); t.opt("random-cap1 op 45: insert(5, 9)", r, Some(85)); let n = m.len(); t.len("random-cap1 op 45", n, 7);
    let r = m.insert(2, 42); t.opt("random-cap1 op 46: insert(2, 42)", r, Some(26)); let n = m.len(); t.len("random-cap1 op 46", n, 7);
    let r = m.insert(0, 11); t.opt("random-cap1 op 47: insert(0, 11)", r, Some(71)); let n = m.len(); t.len("random-cap1 op 47", n, 7);
    let r = m.insert(1, 25); t.opt("random-cap1 op 48: insert(1, 25)", r, Some(19)); let n = m.len(); t.len("random-cap1 op 48", n, 7);
    let r = m.get(0).copied(); t.opt("random-cap1 op 49: get(0)", r, Some(11)); let n = m.len(); t.len("random-cap1 op 49", n, 7);
    *m.get_mut(0) = 84; let n = m.len(); t.len("random-cap1 op 50", n, 7);
}

fn seq_random_cap3(t: &mut Tally) {
    let mut m = HashMap::<u64>::new(3);
    let r = m.insert(6, 48); t.opt("random-cap3 op 1: insert(6, 48)", r, None); let n = m.len(); t.len("random-cap3 op 1", n, 1);
    let r = m.insert(2, 20); t.opt("random-cap3 op 2: insert(2, 20)", r, None); let n = m.len(); t.len("random-cap3 op 2", n, 2);
    let r = m.insert(3, 70); t.opt("random-cap3 op 3: insert(3, 70)", r, None); let n = m.len(); t.len("random-cap3 op 3", n, 3);
    let r = m.remove(11); t.opt("random-cap3 op 4: remove(11)", r, None); let n = m.len(); t.len("random-cap3 op 4", n, 3);
    let r = m.insert(11, 55); t.opt("random-cap3 op 5: insert(11, 55)", r, None); let n = m.len(); t.len("random-cap3 op 5", n, 4);
    let r = m.insert(5, 53); t.opt("random-cap3 op 6: insert(5, 53)", r, None); let n = m.len(); t.len("random-cap3 op 6", n, 5);
    *m.get_mut(6) = 36; let n = m.len(); t.len("random-cap3 op 7", n, 5);
    let r = m.insert(5, 2); t.opt("random-cap3 op 8: insert(5, 2)", r, Some(53)); let n = m.len(); t.len("random-cap3 op 8", n, 5);
    let r = m.get(10).copied(); t.opt("random-cap3 op 9: get(10)", r, None); let n = m.len(); t.len("random-cap3 op 9", n, 5);
    let r = m.remove(5); t.opt("random-cap3 op 10: remove(5)", r, Some(2)); let n = m.len(); t.len("random-cap3 op 10", n, 4);
    let r = m.insert(1, 97); t.opt("random-cap3 op 11: insert(1, 97)", r, None); let n = m.len(); t.len("random-cap3 op 11", n, 5);
    let r = m.insert(0, 57); t.opt("random-cap3 op 12: insert(0, 57)", r, None); let n = m.len(); t.len("random-cap3 op 12", n, 6);
    let r = m.insert(6, 18); t.opt("random-cap3 op 13: insert(6, 18)", r, Some(36)); let n = m.len(); t.len("random-cap3 op 13", n, 6);
    let r = m.get(3).copied(); t.opt("random-cap3 op 14: get(3)", r, Some(70)); let n = m.len(); t.len("random-cap3 op 14", n, 6);
    let r = m.insert(2, 42); t.opt("random-cap3 op 15: insert(2, 42)", r, Some(20)); let n = m.len(); t.len("random-cap3 op 15", n, 6);
    let r = m.remove(0); t.opt("random-cap3 op 16: remove(0)", r, Some(57)); let n = m.len(); t.len("random-cap3 op 16", n, 5);
    let r = m.remove(0); t.opt("random-cap3 op 17: remove(0)", r, None); let n = m.len(); t.len("random-cap3 op 17", n, 5);
    let r = m.insert(3, 18); t.opt("random-cap3 op 18: insert(3, 18)", r, Some(70)); let n = m.len(); t.len("random-cap3 op 18", n, 5);
    let r = m.insert(7, 12); t.opt("random-cap3 op 19: insert(7, 12)", r, None); let n = m.len(); t.len("random-cap3 op 19", n, 6);
    *m.get_mut(6) = 40; let n = m.len(); t.len("random-cap3 op 20", n, 6);
    *m.get_mut(2) = 53; let n = m.len(); t.len("random-cap3 op 21", n, 6);
    *m.get_mut(3) = 31; let n = m.len(); t.len("random-cap3 op 22", n, 6);
    let r = m.get(7).copied(); t.opt("random-cap3 op 23: get(7)", r, Some(12)); let n = m.len(); t.len("random-cap3 op 23", n, 6);
    let r = m.insert(9, 60); t.opt("random-cap3 op 24: insert(9, 60)", r, None); let n = m.len(); t.len("random-cap3 op 24", n, 7);
    let r = m.insert(8, 83); t.opt("random-cap3 op 25: insert(8, 83)", r, None); let n = m.len(); t.len("random-cap3 op 25", n, 8);
    let r = m.insert(7, 66); t.opt("random-cap3 op 26: insert(7, 66)", r, Some(12)); let n = m.len(); t.len("random-cap3 op 26", n, 8);
    let r = m.get(11).copied(); t.opt("random-cap3 op 27: get(11)", r, Some(55)); let n = m.len(); t.len("random-cap3 op 27", n, 8);
    let r = m.remove(8); t.opt("random-cap3 op 28: remove(8)", r, Some(83)); let n = m.len(); t.len("random-cap3 op 28", n, 7);
    let r = m.insert(11, 32); t.opt("random-cap3 op 29: insert(11, 32)", r, Some(55)); let n = m.len(); t.len("random-cap3 op 29", n, 7);
    let r = m.insert(8, 77); t.opt("random-cap3 op 30: insert(8, 77)", r, None); let n = m.len(); t.len("random-cap3 op 30", n, 8);
    let r = m.insert(10, 73); t.opt("random-cap3 op 31: insert(10, 73)", r, None); let n = m.len(); t.len("random-cap3 op 31", n, 9);
    let r = m.remove(0); t.opt("random-cap3 op 32: remove(0)", r, None); let n = m.len(); t.len("random-cap3 op 32", n, 9);
    let r = m.get(11).copied(); t.opt("random-cap3 op 33: get(11)", r, Some(32)); let n = m.len(); t.len("random-cap3 op 33", n, 9);
    let r = m.get(7).copied(); t.opt("random-cap3 op 34: get(7)", r, Some(66)); let n = m.len(); t.len("random-cap3 op 34", n, 9);
    let r = m.get(4).copied(); t.opt("random-cap3 op 35: get(4)", r, None); let n = m.len(); t.len("random-cap3 op 35", n, 9);
    let r = m.get(2).copied(); t.opt("random-cap3 op 36: get(2)", r, Some(53)); let n = m.len(); t.len("random-cap3 op 36", n, 9);
    let r = m.insert(2, 53); t.opt("random-cap3 op 37: insert(2, 53)", r, Some(53)); let n = m.len(); t.len("random-cap3 op 37", n, 9);
    let r = m.get(2).copied(); t.opt("random-cap3 op 38: get(2)", r, Some(53)); let n = m.len(); t.len("random-cap3 op 38", n, 9);
    let r = m.insert(4, 30); t.opt("random-cap3 op 39: insert(4, 30)", r, None); let n = m.len(); t.len("random-cap3 op 39", n, 10);
    let r = m.remove(11); t.opt("random-cap3 op 40: remove(11)", r, Some(32)); let n = m.len(); t.len("random-cap3 op 40", n, 9);
    let r = m.remove(0); t.opt("random-cap3 op 41: remove(0)", r, None); let n = m.len(); t.len("random-cap3 op 41", n, 9);
    let r = m.insert(0, 15); t.opt("random-cap3 op 42: insert(0, 15)", r, None); let n = m.len(); t.len("random-cap3 op 42", n, 10);
    let r = m.insert(1, 20); t.opt("random-cap3 op 43: insert(1, 20)", r, Some(97)); let n = m.len(); t.len("random-cap3 op 43", n, 10);
    let r = m.insert(10, 20); t.opt("random-cap3 op 44: insert(10, 20)", r, Some(73)); let n = m.len(); t.len("random-cap3 op 44", n, 10);
    let r = m.insert(5, 90); t.opt("random-cap3 op 45: insert(5, 90)", r, None); let n = m.len(); t.len("random-cap3 op 45", n, 11);
    let r = m.remove(7); t.opt("random-cap3 op 46: remove(7)", r, Some(66)); let n = m.len(); t.len("random-cap3 op 46", n, 10);
    *m.get_mut(4) = 40; let n = m.len(); t.len("random-cap3 op 47", n, 10);
    let r = m.get(11).copied(); t.opt("random-cap3 op 48: get(11)", r, None); let n = m.len(); t.len("random-cap3 op 48", n, 10);
    let r = m.insert(3, 75); t.opt("random-cap3 op 49: insert(3, 75)", r, Some(31)); let n = m.len(); t.len("random-cap3 op 49", n, 10);
    let r = m.insert(0, 29); t.opt("random-cap3 op 50: insert(0, 29)", r, Some(15)); let n = m.len(); t.len("random-cap3 op 50", n, 10);
}

fn seq_random_cap4(t: &mut Tally) {
    let mut m = HashMap::<u64>::new(4);
    let r = m.insert(3, 6); t.opt("random-cap4 op 1: insert(3, 6)", r, None); let n = m.len(); t.len("random-cap4 op 1", n, 1);
    *m.get_mut(3) = 19; let n = m.len(); t.len("random-cap4 op 2", n, 1);
    let r = m.insert(1, 39); t.opt("random-cap4 op 3: insert(1, 39)", r, None); let n = m.len(); t.len("random-cap4 op 3", n, 2);
    *m.get_mut(1) = 3; let n = m.len(); t.len("random-cap4 op 4", n, 2);
    *m.get_mut(3) = 73; let n = m.len(); t.len("random-cap4 op 5", n, 2);
    let r = m.get(1).copied(); t.opt("random-cap4 op 6: get(1)", r, Some(3)); let n = m.len(); t.len("random-cap4 op 6", n, 2);
    let r = m.insert(12, 39); t.opt("random-cap4 op 7: insert(12, 39)", r, None); let n = m.len(); t.len("random-cap4 op 7", n, 3);
    let r = m.insert(3, 19); t.opt("random-cap4 op 8: insert(3, 19)", r, Some(73)); let n = m.len(); t.len("random-cap4 op 8", n, 3);
    let r = m.insert(7, 84); t.opt("random-cap4 op 9: insert(7, 84)", r, None); let n = m.len(); t.len("random-cap4 op 9", n, 4);
    let r = m.get(12).copied(); t.opt("random-cap4 op 10: get(12)", r, Some(39)); let n = m.len(); t.len("random-cap4 op 10", n, 4);
    let r = m.remove(2); t.opt("random-cap4 op 11: remove(2)", r, None); let n = m.len(); t.len("random-cap4 op 11", n, 4);
    let r = m.insert(0, 26); t.opt("random-cap4 op 12: insert(0, 26)", r, None); let n = m.len(); t.len("random-cap4 op 12", n, 5);
    let r = m.insert(2, 10); t.opt("random-cap4 op 13: insert(2, 10)", r, None); let n = m.len(); t.len("random-cap4 op 13", n, 6);
    let r = m.insert(5, 40); t.opt("random-cap4 op 14: insert(5, 40)", r, None); let n = m.len(); t.len("random-cap4 op 14", n, 7);
    *m.get_mut(5) = 86; let n = m.len(); t.len("random-cap4 op 15", n, 7);
    let r = m.get(4).copied(); t.opt("random-cap4 op 16: get(4)", r, None); let n = m.len(); t.len("random-cap4 op 16", n, 7);
    let r = m.get(12).copied(); t.opt("random-cap4 op 17: get(12)", r, Some(39)); let n = m.len(); t.len("random-cap4 op 17", n, 7);
    let r = m.insert(1, 59); t.opt("random-cap4 op 18: insert(1, 59)", r, Some(3)); let n = m.len(); t.len("random-cap4 op 18", n, 7);
    let r = m.get(4).copied(); t.opt("random-cap4 op 19: get(4)", r, None); let n = m.len(); t.len("random-cap4 op 19", n, 7);
    let r = m.get(8).copied(); t.opt("random-cap4 op 20: get(8)", r, None); let n = m.len(); t.len("random-cap4 op 20", n, 7);
    let r = m.remove(15); t.opt("random-cap4 op 21: remove(15)", r, None); let n = m.len(); t.len("random-cap4 op 21", n, 7);
    let r = m.insert(15, 68); t.opt("random-cap4 op 22: insert(15, 68)", r, None); let n = m.len(); t.len("random-cap4 op 22", n, 8);
    let r = m.insert(11, 80); t.opt("random-cap4 op 23: insert(11, 80)", r, None); let n = m.len(); t.len("random-cap4 op 23", n, 9);
    let r = m.get(10).copied(); t.opt("random-cap4 op 24: get(10)", r, None); let n = m.len(); t.len("random-cap4 op 24", n, 9);
    let r = m.remove(4); t.opt("random-cap4 op 25: remove(4)", r, None); let n = m.len(); t.len("random-cap4 op 25", n, 9);
    let r = m.insert(13, 20); t.opt("random-cap4 op 26: insert(13, 20)", r, None); let n = m.len(); t.len("random-cap4 op 26", n, 10);
    let r = m.insert(9, 7); t.opt("random-cap4 op 27: insert(9, 7)", r, None); let n = m.len(); t.len("random-cap4 op 27", n, 11);
    *m.get_mut(5) = 30; let n = m.len(); t.len("random-cap4 op 28", n, 11);
    let r = m.get(1).copied(); t.opt("random-cap4 op 29: get(1)", r, Some(59)); let n = m.len(); t.len("random-cap4 op 29", n, 11);
    let r = m.remove(4); t.opt("random-cap4 op 30: remove(4)", r, None); let n = m.len(); t.len("random-cap4 op 30", n, 11);
    let r = m.remove(10); t.opt("random-cap4 op 31: remove(10)", r, None); let n = m.len(); t.len("random-cap4 op 31", n, 11);
    let r = m.get(13).copied(); t.opt("random-cap4 op 32: get(13)", r, Some(20)); let n = m.len(); t.len("random-cap4 op 32", n, 11);
    let r = m.remove(9); t.opt("random-cap4 op 33: remove(9)", r, Some(7)); let n = m.len(); t.len("random-cap4 op 33", n, 10);
    *m.get_mut(7) = 75; let n = m.len(); t.len("random-cap4 op 34", n, 10);
    let r = m.get(8).copied(); t.opt("random-cap4 op 35: get(8)", r, None); let n = m.len(); t.len("random-cap4 op 35", n, 10);
    let r = m.remove(11); t.opt("random-cap4 op 36: remove(11)", r, Some(80)); let n = m.len(); t.len("random-cap4 op 36", n, 9);
    *m.get_mut(1) = 32; let n = m.len(); t.len("random-cap4 op 37", n, 9);
    let r = m.get(6).copied(); t.opt("random-cap4 op 38: get(6)", r, None); let n = m.len(); t.len("random-cap4 op 38", n, 9);
    let r = m.get(11).copied(); t.opt("random-cap4 op 39: get(11)", r, None); let n = m.len(); t.len("random-cap4 op 39", n, 9);
    let r = m.get(4).copied(); t.opt("random-cap4 op 40: get(4)", r, None); let n = m.len(); t.len("random-cap4 op 40", n, 9);
    let r = m.remove(6); t.opt("random-cap4 op 41: remove(6)", r, None); let n = m.len(); t.len("random-cap4 op 41", n, 9);
    let r = m.insert(8, 82); t.opt("random-cap4 op 42: insert(8, 82)", r, None); let n = m.len(); t.len("random-cap4 op 42", n, 10);
    let r = m.insert(3, 86); t.opt("random-cap4 op 43: insert(3, 86)", r, Some(19)); let n = m.len(); t.len("random-cap4 op 43", n, 10);
    let r = m.get(12).copied(); t.opt("random-cap4 op 44: get(12)", r, Some(39)); let n = m.len(); t.len("random-cap4 op 44", n, 10);
    *m.get_mut(7) = 17; let n = m.len(); t.len("random-cap4 op 45", n, 10);
    let r = m.get(10).copied(); t.opt("random-cap4 op 46: get(10)", r, None); let n = m.len(); t.len("random-cap4 op 46", n, 10);
    let r = m.get(12).copied(); t.opt("random-cap4 op 47: get(12)", r, Some(39)); let n = m.len(); t.len("random-cap4 op 47", n, 10);
    let r = m.remove(4); t.opt("random-cap4 op 48: remove(4)", r, None); let n = m.len(); t.len("random-cap4 op 48", n, 10);
    let r = m.insert(7, 79); t.opt("random-cap4 op 49: insert(7, 79)", r, Some(17)); let n = m.len(); t.len("random-cap4 op 49", n, 10);
    let r = m.remove(2); t.opt("random-cap4 op 50: remove(2)", r, Some(10)); let n = m.len(); t.len("random-cap4 op 50", n, 9);
}

fn seq_random_cap7(t: &mut Tally) {
    let mut m = HashMap::<u64>::new(7);
    let r = m.insert(10, 82); t.opt("random-cap7 op 1: insert(10, 82)", r, None); let n = m.len(); t.len("random-cap7 op 1", n, 1);
    let r = m.insert(15, 33); t.opt("random-cap7 op 2: insert(15, 33)", r, None); let n = m.len(); t.len("random-cap7 op 2", n, 2);
    let r = m.insert(0, 14); t.opt("random-cap7 op 3: insert(0, 14)", r, None); let n = m.len(); t.len("random-cap7 op 3", n, 3);
    let r = m.insert(8, 60); t.opt("random-cap7 op 4: insert(8, 60)", r, None); let n = m.len(); t.len("random-cap7 op 4", n, 4);
    let r = m.get(4).copied(); t.opt("random-cap7 op 5: get(4)", r, None); let n = m.len(); t.len("random-cap7 op 5", n, 4);
    *m.get_mut(0) = 39; let n = m.len(); t.len("random-cap7 op 6", n, 4);
    let r = m.get(3).copied(); t.opt("random-cap7 op 7: get(3)", r, None); let n = m.len(); t.len("random-cap7 op 7", n, 4);
    let r = m.insert(19, 57); t.opt("random-cap7 op 8: insert(19, 57)", r, None); let n = m.len(); t.len("random-cap7 op 8", n, 5);
    let r = m.remove(15); t.opt("random-cap7 op 9: remove(15)", r, Some(33)); let n = m.len(); t.len("random-cap7 op 9", n, 4);
    let r = m.insert(13, 82); t.opt("random-cap7 op 10: insert(13, 82)", r, None); let n = m.len(); t.len("random-cap7 op 10", n, 5);
    let r = m.remove(18); t.opt("random-cap7 op 11: remove(18)", r, None); let n = m.len(); t.len("random-cap7 op 11", n, 5);
    let r = m.remove(0); t.opt("random-cap7 op 12: remove(0)", r, Some(39)); let n = m.len(); t.len("random-cap7 op 12", n, 4);
    let r = m.get(13).copied(); t.opt("random-cap7 op 13: get(13)", r, Some(82)); let n = m.len(); t.len("random-cap7 op 13", n, 4);
    let r = m.insert(5, 37); t.opt("random-cap7 op 14: insert(5, 37)", r, None); let n = m.len(); t.len("random-cap7 op 14", n, 5);
    let r = m.insert(7, 48); t.opt("random-cap7 op 15: insert(7, 48)", r, None); let n = m.len(); t.len("random-cap7 op 15", n, 6);
    let r = m.remove(7); t.opt("random-cap7 op 16: remove(7)", r, Some(48)); let n = m.len(); t.len("random-cap7 op 16", n, 5);
    let r = m.insert(23, 31); t.opt("random-cap7 op 17: insert(23, 31)", r, None); let n = m.len(); t.len("random-cap7 op 17", n, 6);
    *m.get_mut(19) = 27; let n = m.len(); t.len("random-cap7 op 18", n, 6);
    let r = m.get(1).copied(); t.opt("random-cap7 op 19: get(1)", r, None); let n = m.len(); t.len("random-cap7 op 19", n, 6);
    let r = m.remove(3); t.opt("random-cap7 op 20: remove(3)", r, None); let n = m.len(); t.len("random-cap7 op 20", n, 6);
    let r = m.insert(11, 18); t.opt("random-cap7 op 21: insert(11, 18)", r, None); let n = m.len(); t.len("random-cap7 op 21", n, 7);
    let r = m.insert(5, 67); t.opt("random-cap7 op 22: insert(5, 67)", r, Some(37)); let n = m.len(); t.len("random-cap7 op 22", n, 7);
    let r = m.insert(20, 96); t.opt("random-cap7 op 23: insert(20, 96)", r, None); let n = m.len(); t.len("random-cap7 op 23", n, 8);
    let r = m.get(12).copied(); t.opt("random-cap7 op 24: get(12)", r, None); let n = m.len(); t.len("random-cap7 op 24", n, 8);
    let r = m.get(15).copied(); t.opt("random-cap7 op 25: get(15)", r, None); let n = m.len(); t.len("random-cap7 op 25", n, 8);
    let r = m.get(5).copied(); t.opt("random-cap7 op 26: get(5)", r, Some(67)); let n = m.len(); t.len("random-cap7 op 26", n, 8);
    let r = m.remove(9); t.opt("random-cap7 op 27: remove(9)", r, None); let n = m.len(); t.len("random-cap7 op 27", n, 8);
    let r = m.insert(13, 87); t.opt("random-cap7 op 28: insert(13, 87)", r, Some(82)); let n = m.len(); t.len("random-cap7 op 28", n, 8);
    let r = m.get(19).copied(); t.opt("random-cap7 op 29: get(19)", r, Some(27)); let n = m.len(); t.len("random-cap7 op 29", n, 8);
    *m.get_mut(11) = 84; let n = m.len(); t.len("random-cap7 op 30", n, 8);
    let r = m.get(16).copied(); t.opt("random-cap7 op 31: get(16)", r, None); let n = m.len(); t.len("random-cap7 op 31", n, 8);
    let r = m.insert(3, 78); t.opt("random-cap7 op 32: insert(3, 78)", r, None); let n = m.len(); t.len("random-cap7 op 32", n, 9);
    let r = m.remove(4); t.opt("random-cap7 op 33: remove(4)", r, None); let n = m.len(); t.len("random-cap7 op 33", n, 9);
    *m.get_mut(20) = 89; let n = m.len(); t.len("random-cap7 op 34", n, 9);
    let r = m.get(0).copied(); t.opt("random-cap7 op 35: get(0)", r, None); let n = m.len(); t.len("random-cap7 op 35", n, 9);
    let r = m.insert(23, 28); t.opt("random-cap7 op 36: insert(23, 28)", r, Some(31)); let n = m.len(); t.len("random-cap7 op 36", n, 9);
    let r = m.insert(20, 74); t.opt("random-cap7 op 37: insert(20, 74)", r, Some(89)); let n = m.len(); t.len("random-cap7 op 37", n, 9);
    let r = m.remove(5); t.opt("random-cap7 op 38: remove(5)", r, Some(67)); let n = m.len(); t.len("random-cap7 op 38", n, 8);
    let r = m.insert(19, 32); t.opt("random-cap7 op 39: insert(19, 32)", r, Some(27)); let n = m.len(); t.len("random-cap7 op 39", n, 8);
    let r = m.remove(9); t.opt("random-cap7 op 40: remove(9)", r, None); let n = m.len(); t.len("random-cap7 op 40", n, 8);
    let r = m.insert(11, 98); t.opt("random-cap7 op 41: insert(11, 98)", r, Some(84)); let n = m.len(); t.len("random-cap7 op 41", n, 8);
    let r = m.remove(13); t.opt("random-cap7 op 42: remove(13)", r, Some(87)); let n = m.len(); t.len("random-cap7 op 42", n, 7);
    let r = m.remove(11); t.opt("random-cap7 op 43: remove(11)", r, Some(98)); let n = m.len(); t.len("random-cap7 op 43", n, 6);
    let r = m.get(15).copied(); t.opt("random-cap7 op 44: get(15)", r, None); let n = m.len(); t.len("random-cap7 op 44", n, 6);
    let r = m.get(11).copied(); t.opt("random-cap7 op 45: get(11)", r, None); let n = m.len(); t.len("random-cap7 op 45", n, 6);
    *m.get_mut(3) = 16; let n = m.len(); t.len("random-cap7 op 46", n, 6);
    let r = m.get(13).copied(); t.opt("random-cap7 op 47: get(13)", r, None); let n = m.len(); t.len("random-cap7 op 47", n, 6);
    *m.get_mut(19) = 17; let n = m.len(); t.len("random-cap7 op 48", n, 6);
    let r = m.get(5).copied(); t.opt("random-cap7 op 49: get(5)", r, None); let n = m.len(); t.len("random-cap7 op 49", n, 6);
    let r = m.remove(14); t.opt("random-cap7 op 50: remove(14)", r, None); let n = m.len(); t.len("random-cap7 op 50", n, 6);
}

fn main() {
    let mut t = Tally { passed: 0, failed: 0 };
    seq_scripted(&mut t);
    seq_random_cap1(&mut t);
    seq_random_cap3(&mut t);
    seq_random_cap4(&mut t);
    seq_random_cap7(&mut t);
    println!("tests: {} passed, {} failed", t.passed, t.failed);
    if t.failed > 0 {
        std::process::exit(1);
    }
}
// FIXED-END tests
