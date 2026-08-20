//! The second saving, reported rather than asserted: the destination walk.
//!
//! Allocation is not the only thing upstream's `insert_no_resize` does per
//! moved entry — it also walks the destination bucket to its end, because that
//! is how it would find a duplicate key to overwrite. During a resize there are
//! no duplicates, so the walk is pure overhead. The splice prepends and never
//! looks at the destination, making a *move* O(1) per entry instead of
//! O(destination bucket length).
//!
//! What that is not: an asymptotic win for the map as a whole. The ordinary
//! `insert` path still walks its bucket looking for the key, and the splice
//! does not touch that path, so on a workload where every key collides both
//! versions stay quadratic — the numbers below show both quadrupling per
//! doubling of `n`. The splice removes a constant factor from it (roughly 1.9×
//! on that workload), not an exponent.
//!
//! Bucket traversals are not observable through the public API, so this is
//! measured as wall-clock time and only *printed*: a timing assertion would be
//! flaky, and the allocation counts in `alloc_counts.rs` are the claim that is
//! machine-checked. Run with
//! `cargo test --release --test walk_cost -- --nocapture --test-threads=1`.

use aeneas_hashmap_check::testkit::MapUnderTest;
use aeneas_hashmap_check::{baseline, splice};
use std::time::{Duration, Instant};

fn time_fill<M: MapUnderTest>(n: usize, key: impl Fn(usize) -> usize) -> Duration {
    let start = Instant::now();
    let mut hm = M::new();
    for i in 0..n {
        hm.insert(key(i), i as u64);
    }
    // Keep the map alive past the timer and make the loop observable.
    assert_eq!(hm.len(), n);
    start.elapsed()
}

#[test]
fn destination_walk_cost() {
    println!();
    // The stride has to exceed every capacity the table will reach, not just
    // the initial 32: keys `i * 32` all share slot 0 at capacity 32 but fan out
    // over eight slots by capacity 256, which is why a stride of 32 shows
    // almost no gap here. `STRIDE` is past the largest capacity these runs
    // reach, so every key stays in slot 0 forever and the destination bucket
    // upstream walks is as long as the table is full.
    const STRIDE: usize = 1 << 17;
    println!("all keys collide at every capacity (stride {STRIDE}):");
    for n in [2000usize, 4000, 8000] {
        let b = time_fill::<baseline::HashMap<u64>>(n, |i| i * STRIDE);
        let s = time_fill::<splice::HashMap<u64>>(n, |i| i * STRIDE);
        println!(
            "  n={n:<6} upstream {:>10.3?}  splice {:>10.3?}  ({:.1}x)",
            b,
            s,
            b.as_secs_f64() / s.as_secs_f64().max(f64::MIN_POSITIVE)
        );
    }
    // Keys spread over slots: buckets stay short, so the walk costs little and
    // the two are close. This is the control that says the gap above is the
    // walk and not something else.
    println!("keys spread across slots (short buckets):");
    for n in [2000usize, 4000, 8000] {
        let b = time_fill::<baseline::HashMap<u64>>(n, |i| i * 7 + 1);
        let s = time_fill::<splice::HashMap<u64>>(n, |i| i * 7 + 1);
        println!(
            "  n={n:<6} upstream {:>10.3?}  splice {:>10.3?}  ({:.1}x)",
            b,
            s,
            b.as_secs_f64() / s.as_secs_f64().max(f64::MIN_POSITIVE)
        );
    }
}
