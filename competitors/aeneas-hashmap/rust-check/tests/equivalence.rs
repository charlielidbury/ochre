//! Deliverable 1's safety net: the splice is the same map as upstream.
//!
//! Every test here runs against both `current/hashmap.rs` and
//! `splice/hashmap.rs`, and where there is an answer to check it is checked
//! against `std::collections::HashMap`.

use aeneas_hashmap_check::testkit::{
    assert_same, op_stream, resize_points, run, run_oracle, MapUnderTest, Obs, Op,
};
use aeneas_hashmap_check::{baseline, splice};

/// The test the vendored file itself carries, commented out because Charon
/// could not extract `#[test]` functions at the time. Keys 0, 128, 1024 and
/// 1056 are all congruent to 0 mod 32, so they pile into slot 0 of 32 and the
/// whole thing exercises one collision list.
fn paper_test1<M: MapUnderTest>() {
    let mut hm = M::new();
    hm.insert(0, 42);
    hm.insert(128, 18);
    hm.insert(1024, 138);
    hm.insert(1056, 256);

    assert_eq!(hm.get(&128), Some(&18), "{}", M::name());
    *hm.get_mut(&1024).unwrap() = 56;
    assert_eq!(hm.get(&1024), Some(&56), "{}", M::name());
    assert_eq!(hm.remove(&1024), Some(56), "{}", M::name());
    assert_eq!(hm.get(&0), Some(&42), "{}", M::name());
    assert_eq!(hm.get(&128), Some(&18), "{}", M::name());
    assert_eq!(hm.get(&1056), Some(&256), "{}", M::name());
    assert_eq!(hm.len(), 3, "{}", M::name());
}

#[test]
fn paper_test1_both() {
    paper_test1::<baseline::HashMap<u64>>();
    paper_test1::<splice::HashMap<u64>>();
}

/// Fill one bucket to the brim and then resize repeatedly. Every key here is a
/// multiple of 32, so before *and* after every resize they all still collide —
/// this is the case where the destination bucket is longest and where upstream
/// pays the most for walking it.
fn all_colliding<M: MapUnderTest>() {
    let mut hm = M::new();
    let keys: Vec<usize> = (0..200).map(|i| i * 32).collect();
    for (i, k) in keys.iter().enumerate() {
        hm.insert(*k, i as u64);
        assert_eq!(hm.len(), i + 1, "{} after inserting {k}", M::name());
    }
    // Everything is still there and still paired with its own value.
    for (i, k) in keys.iter().enumerate() {
        assert_eq!(hm.get(k), Some(&(i as u64)), "{} key {k}", M::name());
    }
    // Overwriting an existing key must not change the count.
    hm.insert(keys[7], 999);
    assert_eq!(hm.get(&keys[7]), Some(&999), "{}", M::name());
    assert_eq!(hm.len(), keys.len(), "{}", M::name());
    // Removing walks the same bucket.
    for (i, k) in keys.iter().enumerate().rev() {
        let expected = if i == 7 { 999 } else { i as u64 };
        assert_eq!(hm.remove(k), Some(expected), "{} key {k}", M::name());
    }
    assert_eq!(hm.len(), 0, "{}", M::name());
    for k in &keys {
        assert_eq!(hm.get(k), None, "{} key {k}", M::name());
    }
}

#[test]
fn all_colliding_both() {
    all_colliding::<baseline::HashMap<u64>>();
    all_colliding::<splice::HashMap<u64>>();
}

/// Straight across a resize boundary: insert exactly enough to trigger the
/// first resize, then check that nothing moved out from under a lookup.
fn survives_first_resize<M: MapUnderTest>() {
    let (entries, capacity) = resize_points(1)[0];
    assert_eq!((entries, capacity), (26, 32));
    let mut hm = M::new();
    for i in 0..entries {
        // A mix of colliding and non-colliding keys so both kinds of bucket
        // are non-empty when the move runs.
        let key = if i % 3 == 0 { i * 32 } else { i * 7 + 1 };
        hm.insert(key, i as u64);
    }
    assert_eq!(hm.len(), entries, "{}", M::name());
    for i in 0..entries {
        let key = if i % 3 == 0 { i * 32 } else { i * 7 + 1 };
        assert_eq!(hm.get(&key), Some(&(i as u64)), "{} key {key}", M::name());
    }
}

#[test]
fn survives_first_resize_both() {
    survives_first_resize::<baseline::HashMap<u64>>();
    survives_first_resize::<splice::HashMap<u64>>();
}

#[test]
fn clear_then_reuse() {
    fn go<M: MapUnderTest>() {
        let mut hm = M::new();
        for i in 0..100 {
            hm.insert(i * 32, i as u64);
        }
        hm.clear();
        assert_eq!(hm.len(), 0, "{}", M::name());
        for i in 0..100 {
            assert_eq!(hm.get(&(i * 32)), None, "{}", M::name());
        }
        // The table keeps its grown capacity; refilling must still work.
        for i in 0..100 {
            hm.insert(i * 32, (i as u64) * 3);
        }
        for i in 0..100 {
            assert_eq!(hm.get(&(i * 32)), Some(&((i as u64) * 3)), "{}", M::name());
        }
    }
    go::<baseline::HashMap<u64>>();
    go::<splice::HashMap<u64>>();
}

/// The main event: long randomised op streams, each checked against
/// `std::collections::HashMap` and against the other implementation.
#[test]
fn matches_std_oracle_and_each_other() {
    for seed in [1u64, 2, 3, 0xDEAD_BEEF, 0x5EED, 12345, 99991] {
        let ops = op_stream(seed, 4000);
        // Enough inserts land to force several resizes.
        let inserts = ops
            .iter()
            .filter(|o| matches!(o, Op::Insert(..)))
            .count();
        assert!(inserts > 1500, "seed {seed}: only {inserts} inserts");

        let oracle = run_oracle(&ops);
        let mut b = baseline::HashMap::<u64>::new();
        let got_baseline = run(&mut b, &ops);
        let mut s = splice::HashMap::<u64>::new();
        let got_splice = run(&mut s, &ops);

        assert_same(&format!("seed {seed}: baseline vs std"), &ops, &got_baseline, &oracle);
        assert_same(&format!("seed {seed}: splice vs std"), &ops, &got_splice, &oracle);
        assert_same(&format!("seed {seed}: splice vs baseline"), &ops, &got_splice, &got_baseline);

        // And the final states agree key by key over the whole pool.
        for key in (0..4096).chain((0..24).map(|i| i * 32)) {
            assert_eq!(
                b.get(&key).copied(),
                s.get(&key).copied(),
                "seed {seed}: final state differs at key {key}"
            );
        }
        assert_eq!(b.len(), s.len(), "seed {seed}: final len differs");
    }
}

/// A stream made only of insert and remove on a small, entirely colliding key
/// pool: this is the shape most likely to expose an ordering bug, because the
/// same bucket is rebuilt over and over across resizes.
#[test]
fn colliding_pool_insert_remove_churn() {
    let mut rng = aeneas_hashmap_check::testkit::Rng::new(0xC0FFEE);
    let mut ops = Vec::new();
    for _ in 0..6000 {
        let key = (rng.below(40) * 32) as usize;
        if rng.below(3) == 0 {
            ops.push(Op::Remove(key));
        } else {
            ops.push(Op::Insert(key, rng.next()));
        }
        ops.push(Op::Get(key));
        ops.push(Op::Len);
    }
    let oracle = run_oracle(&ops);
    let mut b = baseline::HashMap::<u64>::new();
    let mut s = splice::HashMap::<u64>::new();
    assert_same("churn: baseline vs std", &ops, &run(&mut b, &ops), &oracle);
    assert_same("churn: splice vs std", &ops, &run(&mut s, &ops), &oracle);
    // The oracle stream contains real answers, not a run of `None`s.
    assert!(oracle.iter().any(|o| matches!(o, Obs::Value(Some(_)))));
}
