//! The two hashmaps under one interface, plus the shared op-stream driver.
//!
//! [`baseline::HashMap`](crate::baseline::HashMap) and
//! [`splice::HashMap`](crate::splice::HashMap) are distinct types that happen
//! to have the same surface. [`MapUnderTest`] is that surface, so a test can be
//! written once and run against both. It is a generic bound, never a trait
//! object, so no dispatch machinery ends up in the allocation measurements.

use crate::{baseline, splice};

pub trait MapUnderTest {
    fn new() -> Self;
    fn insert(&mut self, key: usize, value: u64);
    fn get(&self, key: &usize) -> Option<&u64>;
    fn get_mut(&mut self, key: &usize) -> Option<&mut u64>;
    fn remove(&mut self, key: &usize) -> Option<u64>;
    fn contains_key(&self, key: &usize) -> bool;
    fn len(&self) -> usize;
    fn clear(&mut self);

    /// The heap footprint of one bucket node, which is what `Box::new` asks for
    /// when upstream's `insert_in_list` reaches its `Nil` arm.
    fn node_size() -> usize;

    /// Which file this implementation came from, for assertion messages.
    fn name() -> &'static str;
}

macro_rules! impl_map_under_test {
    ($m:ident, $name:literal) => {
        impl MapUnderTest for $m::HashMap<u64> {
            fn new() -> Self {
                $m::HashMap::new()
            }
            fn insert(&mut self, key: usize, value: u64) {
                $m::HashMap::insert(self, key, value)
            }
            fn get(&self, key: &usize) -> Option<&u64> {
                $m::HashMap::get(self, key)
            }
            fn get_mut(&mut self, key: &usize) -> Option<&mut u64> {
                $m::HashMap::get_mut(self, key)
            }
            fn remove(&mut self, key: &usize) -> Option<u64> {
                $m::HashMap::remove(self, key)
            }
            fn contains_key(&self, key: &usize) -> bool {
                $m::HashMap::contains_key(self, key)
            }
            fn len(&self) -> usize {
                $m::HashMap::len(self)
            }
            fn clear(&mut self) {
                $m::HashMap::clear(self)
            }
            fn node_size() -> usize {
                std::mem::size_of::<$m::AList<u64>>()
            }
            fn name() -> &'static str {
                $name
            }
        }
    };
}

impl_map_under_test!(baseline, "current/hashmap.rs (upstream re-insert)");
impl_map_under_test!(splice, "splice/hashmap.rs (relinking move)");

/// The table starts at 32 slots with a max load factor of 4/5, so it holds 25
/// entries and resizes on the insert that would make it 26.
pub const INITIAL_CAPACITY: usize = 32;

/// Entry counts at which the table resizes, and how many entries each of those
/// resizes moves. `insert` bumps `num_entries` first and resizes when the new
/// count exceeds `capacity * 4 / 5`, so the move carries the entry that
/// triggered it as well.
///
/// capacity 32 -> load 25 -> resizes at 26 entries, moving 26
/// capacity 64 -> load 51 -> resizes at 52 entries, moving 52
/// capacity 128 -> load 102 -> resizes at 103 entries, moving 103
pub fn resize_points(count: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut capacity = INITIAL_CAPACITY;
    while out.len() < count {
        let entries = capacity * 4 / 5 + 1;
        out.push((entries, capacity));
        capacity *= 2;
    }
    out
}

/// xorshift64*, so the op streams are reproducible without a dependency.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// One step of a randomised op stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Insert(usize, u64),
    Get(usize),
    GetMutIncr(usize),
    Remove(usize),
    Contains(usize),
    Len,
}

/// What a step observed, so two implementations can be compared step by step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Obs {
    Unit,
    Value(Option<u64>),
    Flag(bool),
    Count(usize),
}

/// Build an op stream over a key pool chosen to collide hard.
///
/// The hash is the identity and the slot is `key % capacity`, so keys that are
/// congruent mod 32 share a bucket at every capacity the table ever reaches.
/// Roughly half the pool is drawn from multiples of 32 (0, 128, 1024, 1056 and
/// their kin — the set the vendored file's own `test1` uses), which is what
/// makes the destination buckets long enough for the append-versus-prepend
/// difference to be doing real work.
pub fn op_stream(seed: u64, steps: usize) -> Vec<Op> {
    let mut rng = Rng::new(seed);
    let mut ops = Vec::with_capacity(steps);
    for _ in 0..steps {
        let key = if rng.below(2) == 0 {
            (rng.below(24) * 32) as usize
        } else {
            (rng.below(4096)) as usize
        };
        let value = rng.next();
        ops.push(match rng.below(10) {
            0..=4 => Op::Insert(key, value),
            5 => Op::Get(key),
            6 => Op::GetMutIncr(key),
            7 => Op::Remove(key),
            8 => Op::Contains(key),
            _ => Op::Len,
        });
    }
    ops
}

/// Run an op stream against a map, returning what each step observed.
pub fn run<M: MapUnderTest>(map: &mut M, ops: &[Op]) -> Vec<Obs> {
    ops.iter()
        .map(|op| match *op {
            Op::Insert(k, v) => {
                map.insert(k, v);
                Obs::Unit
            }
            Op::Get(k) => Obs::Value(map.get(&k).copied()),
            Op::GetMutIncr(k) => match map.get_mut(&k) {
                Some(v) => {
                    *v = v.wrapping_add(1);
                    Obs::Value(Some(*v))
                }
                None => Obs::Value(None),
            },
            Op::Remove(k) => Obs::Value(map.remove(&k)),
            Op::Contains(k) => Obs::Flag(map.contains_key(&k)),
            Op::Len => Obs::Count(map.len()),
        })
        .collect()
}

/// The same op stream against `std::collections::HashMap`, which is the oracle.
pub fn run_oracle(ops: &[Op]) -> Vec<Obs> {
    let mut map: std::collections::HashMap<usize, u64> = std::collections::HashMap::new();
    ops.iter()
        .map(|op| match *op {
            Op::Insert(k, v) => {
                map.insert(k, v);
                Obs::Unit
            }
            Op::Get(k) => Obs::Value(map.get(&k).copied()),
            Op::GetMutIncr(k) => match map.get_mut(&k) {
                Some(v) => {
                    *v = v.wrapping_add(1);
                    Obs::Value(Some(*v))
                }
                None => Obs::Value(None),
            },
            Op::Remove(k) => Obs::Value(map.remove(&k)),
            Op::Contains(k) => Obs::Flag(map.contains_key(&k)),
            Op::Len => Obs::Count(map.len()),
        })
        .collect()
}

/// Compare two observation streams and report the first divergence with the op
/// that caused it, rather than a bare `assert_eq!` on two long vectors.
pub fn assert_same(what: &str, ops: &[Op], left: &[Obs], right: &[Obs]) {
    assert_eq!(left.len(), right.len(), "{what}: different stream lengths");
    for (i, ((l, r), op)) in left.iter().zip(right).zip(ops).enumerate() {
        assert_eq!(
            l, r,
            "{what}: diverged at step {i} on {op:?} (left {l:?}, right {r:?})"
        );
    }
}
