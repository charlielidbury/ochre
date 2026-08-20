//! Relinking nodes by hand is exactly the kind of change that leaks a box or
//! drops one twice, and neither shows up in a functional-equivalence test. Two
//! checks that would catch it:
//!
//! 1. **Allocator balance.** Over a create-fill-drop lifecycle, every
//!    allocation must be matched by a free. A leaked box shows as an excess
//!    allocation; a double free would abort the process outright.
//! 2. **Value drops.** Values are a type that counts its own constructions and
//!    destructions, so an entry that is lost or destroyed twice is visible even
//!    when its box is accounted for.

use aeneas_hashmap_check::counting_alloc::measure;
use aeneas_hashmap_check::{baseline, splice};
use std::cell::Cell;

thread_local! {
    static LIVE: Cell<isize> = const { Cell::new(0) };
    static DROPS: Cell<usize> = const { Cell::new(0) };
}

/// A value that is not `Copy` and has a destructor, so the map has to move it
/// exactly once and drop it exactly once.
struct Tracked(#[allow(dead_code)] u64);

impl Tracked {
    fn new(v: u64) -> Self {
        LIVE.with(|c| c.set(c.get() + 1));
        Tracked(v)
    }
}

impl Drop for Tracked {
    fn drop(&mut self) {
        LIVE.with(|c| c.set(c.get() - 1));
        DROPS.with(|c| c.set(c.get() + 1));
        assert!(
            LIVE.with(|c| c.get()) >= 0,
            "a value was dropped more times than it was created"
        );
    }
}

fn reset() {
    LIVE.with(|c| c.set(0));
    DROPS.with(|c| c.set(0));
}

macro_rules! lifecycle_tests {
    ($m:ident, $modname:ident, $label:literal) => {
        mod $modname {
            use super::*;

            /// Build a map, cross several resizes, then drop it. Allocations and
            /// frees must balance exactly.
            #[test]
            fn allocator_balances_over_a_lifecycle() {
                let node = std::mem::size_of::<$m::AList<u64>>();
                let (_, c) = measure(node, || {
                    let mut hm = $m::HashMap::<u64>::new();
                    for i in 0..400 {
                        hm.insert(i * 32, i as u64);
                    }
                    for i in 0..200 {
                        hm.remove(&(i * 32));
                    }
                    for i in 400..600 {
                        hm.insert(i * 32, i as u64);
                    }
                    drop(hm);
                });
                assert_eq!(
                    c.allocs, c.deallocs,
                    "{}: {} allocations but {} frees — a node or vector leaked",
                    $label, c.allocs, c.deallocs
                );
                assert!(c.allocs > 600, "{}: the workload barely allocated", $label);
            }

            /// Every value put in comes back out exactly once.
            #[test]
            fn values_are_moved_once_and_dropped_once() {
                reset();
                let n = 500usize;
                {
                    let mut hm = $m::HashMap::<Tracked>::new();
                    // All keys collide at capacity 32 and stay together for a
                    // while, so resizes move long buckets.
                    for i in 0..n {
                        hm.insert(i * 32, Tracked::new(i as u64));
                    }
                    assert_eq!(
                        LIVE.with(|c| c.get()),
                        n as isize,
                        "{}: values went missing while filling",
                        $label
                    );
                    // Overwriting a key must drop exactly the old value.
                    let before = DROPS.with(|c| c.get());
                    hm.insert(0, Tracked::new(999));
                    assert_eq!(
                        DROPS.with(|c| c.get()),
                        before + 1,
                        "{}: overwriting did not drop exactly one old value",
                        $label
                    );
                    assert_eq!(LIVE.with(|c| c.get()), n as isize, "{}", $label);
                    // Removing hands the value back to us; dropping it here is
                    // the only drop it gets.
                    for i in 0..100 {
                        let got = hm.remove(&(i * 32));
                        assert!(got.is_some(), "{}: key {} vanished", $label, i * 32);
                    }
                    assert_eq!(
                        LIVE.with(|c| c.get()),
                        (n - 100) as isize,
                        "{}: removal accounting is off",
                        $label
                    );
                }
                assert_eq!(
                    LIVE.with(|c| c.get()),
                    0,
                    "{}: dropping the map leaked {} values",
                    $label,
                    LIVE.with(|c| c.get())
                );
            }

            /// `clear` on a grown table has to drop every value it discards.
            #[test]
            fn clear_drops_everything() {
                reset();
                let mut hm = $m::HashMap::<Tracked>::new();
                for i in 0..300 {
                    hm.insert(i * 32, Tracked::new(i as u64));
                }
                assert_eq!(LIVE.with(|c| c.get()), 300, "{}", $label);
                hm.clear();
                assert_eq!(
                    LIVE.with(|c| c.get()),
                    0,
                    "{}: clear leaked values",
                    $label
                );
            }
        }
    };
}

lifecycle_tests!(baseline, baseline_tests, "current/hashmap.rs");
lifecycle_tests!(splice, splice_tests, "splice/hashmap.rs");
