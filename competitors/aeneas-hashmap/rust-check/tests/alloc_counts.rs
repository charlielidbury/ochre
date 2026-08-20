//! Deliverable 2: the allocation counts, measured rather than argued.
//!
//! The quantity of interest is how many heap allocations a *resize* performs.
//! `try_resize` is private, so the measurement is taken around the single
//! `insert` call that crosses the load threshold — that call does exactly one
//! ordinary insertion (one bucket node) and then the whole resize. Allocations
//! are classified by requested size, which separates the two contributions
//! without needing access to the map's internals:
//!
//! - `size_of::<AList<u64>>()` bytes — a bucket node, i.e. a `Box::new` inside
//!   `insert_in_list`. One per entry moved is upstream's cost.
//! - `capacity * size_of::<AList<u64>>()` bytes — the slots `Vec`, which
//!   `allocate_slots` grows by pushing, so it appears as a doubling chain.
//!
//! Run with `cargo test --test alloc_counts -- --nocapture` to see the tables.

use aeneas_hashmap_check::counting_alloc::{measure, Counts};
use aeneas_hashmap_check::testkit::{resize_points, MapUnderTest};
use aeneas_hashmap_check::{baseline, splice};

/// Fill a map to `entries - 1` and measure only the insert that resizes it.
fn measure_resizing_insert<M: MapUnderTest>(entries: usize, key: impl Fn(usize) -> usize) -> Counts {
    let mut hm = M::new();
    for i in 0..entries - 1 {
        hm.insert(key(i), i as u64);
    }
    assert_eq!(hm.len(), entries - 1);
    let last = key(entries - 1);
    let (_, counts) = measure(M::node_size(), || hm.insert(last, 0));
    assert_eq!(hm.len(), entries, "the measured insert must be a new key");
    counts
}

/// An insert that does not resize, as the control: it should cost exactly one
/// bucket node and nothing else.
fn measure_plain_insert<M: MapUnderTest>() -> Counts {
    let mut hm = M::new();
    hm.insert(0, 0);
    let (_, counts) = measure(M::node_size(), || hm.insert(1, 1));
    counts
}

fn report(label: &str, entries: usize, c: &Counts) {
    println!(
        "{label:<46} entries_moved={entries:<4} allocs={:<4} node_allocs={:<4} deallocs={:<4} bytes={:<6} sizes={:?}",
        c.allocs,
        c.watch_hits,
        c.deallocs,
        c.bytes,
        c.size_histogram()
    );
    assert!(!c.sizes_overflowed, "{label}: size histogram overflowed");
}

/// Every allocation that is not a bucket node.
fn non_node_allocs(c: &Counts) -> usize {
    c.allocs - c.watch_hits
}

#[test]
fn node_layout_is_what_the_measurement_assumes() {
    // The two files must agree on the node size, or the two columns below are
    // not comparable. The niche in `Box` absorbs the discriminant, so a node is
    // key + value + pointer with no tag word.
    assert_eq!(
        <baseline::HashMap<u64> as MapUnderTest>::node_size(),
        <splice::HashMap<u64> as MapUnderTest>::node_size()
    );
    let n = <baseline::HashMap<u64> as MapUnderTest>::node_size();
    println!("AList<u64> node size = {n} bytes");
    assert_eq!(n, 3 * std::mem::size_of::<usize>());
    // A bucket node and a slots vector can never be confused: the smallest
    // vector the table ever allocates is the first `push`, four slots wide.
    assert!(4 * n > n);
}

#[test]
fn plain_insert_costs_one_node() {
    let b = measure_plain_insert::<baseline::HashMap<u64>>();
    let s = measure_plain_insert::<splice::HashMap<u64>>();
    report("baseline: insert without resize", 0, &b);
    report("splice:   insert without resize", 0, &s);
    assert_eq!(b.allocs, 1);
    assert_eq!(b.watch_hits, 1);
    assert_eq!(s.allocs, 1);
    assert_eq!(s.watch_hits, 1);
}

/// THE HEADLINE. For each of the first three resizes, upstream allocates one
/// bucket node per entry moved; the splice allocates none.
#[test]
fn resize_allocations() {
    println!();
    for (entries, capacity) in resize_points(3) {
        for (kind, key) in [
            ("all keys collide", Box::new(|i: usize| i * 32) as Box<dyn Fn(usize) -> usize>),
            ("keys spread out", Box::new(|i: usize| i * 7 + 1)),
        ] {
            let b = measure_resizing_insert::<baseline::HashMap<u64>>(entries, &key);
            let s = measure_resizing_insert::<splice::HashMap<u64>>(entries, &key);
            report(
                &format!("baseline cap {capacity}->{}, {kind}", capacity * 2),
                entries,
                &b,
            );
            report(
                &format!("splice   cap {capacity}->{}, {kind}", capacity * 2),
                entries,
                &s,
            );

            // Upstream: one fresh node per entry moved, plus the one node the
            // triggering insert legitimately builds for its own entry.
            assert_eq!(
                b.watch_hits,
                entries + 1,
                "baseline should allocate one node per moved entry (+1 for the insert itself)"
            );
            // ...and it drops the same number of old nodes.
            assert!(
                b.deallocs >= entries,
                "baseline should free one old node per moved entry"
            );

            // The splice: the only node allocated is the one the triggering
            // insert builds for its own entry. Zero during the move.
            assert_eq!(
                s.watch_hits, 1,
                "splice must allocate NO bucket node while moving entries"
            );

            // Everything that is not a bucket node is the new slots vector, and
            // that part is untouched by the change.
            assert_eq!(
                non_node_allocs(&b),
                non_node_allocs(&s),
                "the slots-vector allocations must be identical in both"
            );

            // The saving is exactly the entries moved.
            assert_eq!(b.allocs - s.allocs, entries);
        }
    }
}

/// `allocate_slots` transcribed, so the test has an independently measured
/// reference for what building the new table costs.
///
/// Upstream builds the new slots array as `Vec::new()` followed by `capacity`
/// pushes of `AList::Nil`, so its allocation behaviour is `Vec`'s doubling
/// policy and nothing else. Measuring a transcription rather than hard-coding
/// the chain `96, 192, 384, …` keeps the assertion exact without making it
/// hostage to a future change in how `Vec` grows.
fn measure_allocate_slots(capacity: usize) -> Counts {
    let (v, counts) = measure(
        std::mem::size_of::<baseline::AList<u64>>(),
        || {
            let mut slots: Vec<baseline::AList<u64>> = Vec::new();
            let mut n = capacity;
            while n > 0 {
                slots.push(baseline::AList::Nil);
                n -= 1;
            }
            slots
        },
    );
    assert_eq!(v.len(), capacity);
    counts
}

/// The claim in its strongest form: during a resize the splice performs
/// *exactly* the allocations of `new_with_capacity` and not one more.
#[test]
fn splice_resize_allocates_exactly_the_new_table() {
    println!();
    for (entries, capacity) in resize_points(3) {
        let reference = measure_allocate_slots(capacity * 2);
        let s = measure_resizing_insert::<splice::HashMap<u64>>(entries, |i| i * 32);
        report(
            &format!("reference: allocate_slots({})", capacity * 2),
            0,
            &reference,
        );
        report(&format!("splice   cap {capacity}->{}", capacity * 2), entries, &s);

        // One node for the entry the triggering insert adds, and then precisely
        // the new table.
        assert_eq!(
            s.allocs,
            reference.allocs + 1,
            "splice at cap {capacity}: allocations beyond the new table and the inserted entry"
        );
        assert_eq!(
            s.bytes,
            reference.bytes + <splice::HashMap<u64> as MapUnderTest>::node_size(),
            "splice at cap {capacity}: bytes beyond the new table and the inserted entry"
        );
        // Same sizes, same multiplicities, in the same order — with the single
        // node the insert added.
        let mut expected = reference.size_histogram();
        let node = <splice::HashMap<u64> as MapUnderTest>::node_size();
        expected.insert(0, (node, 1));
        assert_eq!(
            s.size_histogram(),
            expected,
            "splice at cap {capacity}: allocation profile differs from the new table's"
        );
    }
}

/// The slope, stated as its own claim: doubling the number of entries moved
/// doubles upstream's allocation count and leaves the splice's unchanged. This
/// is the part that does not depend on how `Vec` happens to grow.
#[test]
fn allocation_count_is_linear_in_entries_for_baseline_and_flat_for_splice() {
    println!();
    let key = |i: usize| i * 32;
    let points = resize_points(3);
    let mut baseline_nodes = Vec::new();
    let mut splice_nodes = Vec::new();
    for &(entries, _) in &points {
        baseline_nodes.push((
            entries,
            measure_resizing_insert::<baseline::HashMap<u64>>(entries, key).watch_hits,
        ));
        splice_nodes.push((
            entries,
            measure_resizing_insert::<splice::HashMap<u64>>(entries, key).watch_hits,
        ));
    }
    println!("baseline (entries moved, node allocations): {baseline_nodes:?}");
    println!("splice   (entries moved, node allocations): {splice_nodes:?}");

    // Slope 1 for upstream: each extra entry moved costs exactly one more.
    for w in baseline_nodes.windows(2) {
        let (e0, a0) = w[0];
        let (e1, a1) = w[1];
        assert_eq!(a1 - a0, e1 - e0, "baseline slope should be exactly 1");
    }
    // Slope 0 for the splice, at the constant 1 the triggering insert costs.
    for &(_, a) in &splice_nodes {
        assert_eq!(a, 1, "splice slope should be exactly 0");
    }
}

/// A whole run, not just one resize: filling a map to 400 entries goes through
/// four resizes, and the splice never pays for any of them.
#[test]
fn whole_fill_totals() {
    println!();
    fn fill<M: MapUnderTest>(n: usize) -> Counts {
        let (_, counts) = measure(M::node_size(), || {
            let mut hm = M::new();
            for i in 0..n {
                hm.insert(i * 32, i as u64);
            }
            hm
        });
        counts
    }
    let n = 400;
    let b = fill::<baseline::HashMap<u64>>(n);
    let s = fill::<splice::HashMap<u64>>(n);
    report("baseline: build a 400-entry map from empty", n, &b);
    report("splice:   build a 400-entry map from empty", n, &s);

    // Every distinct key costs one node in both: that is the map's own data.
    // The resizes moved 26 + 52 + 103 + 205 = 386 entries, and upstream
    // rebuilt every one of them.
    let moved: usize = resize_points(4).iter().map(|&(e, _)| e).sum();
    assert_eq!(s.watch_hits, n, "splice: one node per key stored, and no more");
    assert_eq!(
        b.watch_hits,
        n + moved,
        "baseline: one node per key stored plus one per entry moved ({moved} moved)"
    );
    println!("entries moved across the four resizes: {moved}");
    println!(
        "node allocations to build a {n}-entry map: baseline {} vs splice {} ({} wasted, {:.1}x)",
        b.watch_hits,
        s.watch_hits,
        b.watch_hits - s.watch_hits,
        b.watch_hits as f64 / s.watch_hits as f64
    );
}
