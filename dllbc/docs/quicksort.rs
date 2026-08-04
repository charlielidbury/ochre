//! The algorithmic content of `Dllbc/Tests/S25ArrSort.lean`, with every proof term erased.
//! `Nat` is rendered as `u32`. Compile and run the transcribed test vectors with:
//!
//!     rustc quicksort.rs -o /tmp/qs && /tmp/qs
//!
//! What was dropped, and why it leaves no residue:
//!
//! * `fuel` / `hfuel` — DLLBC's termination story. Rust recursion on strictly shorter
//!   slices terminates structurally.
//! * The evidence telescope (`hlen`, `hsp`/`hp`, the `Π q. countA …` count family) — the
//!   specification. Only the data components survive: the split point `k`. (`r` is also
//!   data in DLLBC, but here it is just `len - k`.)
//! * The staged builders (`mkC`, `mkTop`, `mkS`, `mkAD`, `mkHf`) — proof plumbing for
//!   naming entry-time snapshots across consuming calls; zero runtime content.
//! * The `botElim` branches — discharges of impossible cases; dead code.
//!
//! What maps to what:
//!
//! * The head peel `&mut (*t)[Z ; 1 ; m2]` / `&mut (*t)[S Z ; m2]` is `t[0]` / `&mut t[1..]`.
//! * The three-way carve `lo`/`mid`/`hi` only ever reads/writes the two cells at the head
//!   and the boundary, so the whole swap branch erases to `t.swap(0, k)`.
//! * "Every element access is at index 0 of a segment the program carved" shows up here
//!   as: the only indices in the whole file are `0` and `k`.
//!
//! Two structural facts of the DLLBC original that do NOT carry over:
//!
//! * The one-swap-per-level recursive shape is *forced* there (two live symbolic cursors
//!   into one array are unwritable — §25 vii, ledger R13), so Lomuto/Hoare scans are
//!   unavailable. In Rust this shape is a choice; it is kept for the correspondence.
//! * `partition` must be a separate function there (a body that has matched its length
//!   rigid cannot carve at a symbolic index; the call boundary re-mints the array flex —
//!   §25 iii). In Rust the boundary is optional; kept, likewise.

/// §25 (ii) `splitA` — rearrange `t` in place so its first `k` elements are `<= p` and
/// the rest are `>= p`; return `k`.
fn split(p: u32, t: &mut [u32]) -> usize {
    // `match m { Z => … }`: the empty array splits at 0.
    if t.is_empty() {
        return 0;
    }
    // Peel the head, split the tail recursively, then place the head.
    let x = t[0];
    let k2 = split(p, &mut t[1..]);
    if x <= p {
        // x <= p: the head belongs at the front, where it already is. NO WRITE.
        k2 + 1
    } else if k2 == 0 {
        // x > p and the tail's left part is empty: everything after the head is already
        // >= p. NO WRITE.
        0
    } else {
        // x > p with a non-empty left part: the head must cross it. Swap it with that
        // part's LAST element — `t[k2]`, which is <= p and lands at the front
        // legitimately, while the head lands exactly at the new boundary. ONE swap, and
        // the only mutation the program performs.
        t.swap(0, k2);
        k2
    }
}

/// §25 (iii) `partitionA` — pick `a[0]` as the pivot, split the tail around it, swap the
/// pivot into its final position; return that position.
///
/// The erased `PartA` postcondition: `a[..k]` all `<=` pivot, `a[k]` IS the pivot,
/// `a[k+1..]` all `>=` pivot. Requires `!a.is_empty()` (DLLBC: `hne : Le 1 n`).
fn partition(a: &mut [u32]) -> usize {
    let x = a[0];
    let k = split(x, &mut a[1..]);
    // k == 0: nothing is <= the pivot, so it is already in its final place at index 0.
    // k > 0:  the pivot must cross the left part: swap it with that part's last element
    //         `a[k]` (<= pivot, so it may sit at the front); the pivot lands at index
    //         `k`, which is the boundary.
    if k > 0 {
        a.swap(0, k);
    }
    k
}

/// §25 (iv) `quicksortA` — the headline. The erased spec: sorted, and a permutation of
/// the entry array (stated there as count preservation over the exit snapshot), in place.
fn quicksort(a: &mut [u32]) {
    // `if he : leb 1 n` — note the base case is ONLY the empty array; a singleton still
    // goes through partition, exactly as in the original.
    if a.is_empty() {
        return;
    }
    let k = partition(a);
    // The three-way carve at the index the partition just returned: left part, pivot
    // cell, right part. The pivot cell is never touched again.
    let (l, rest) = a.split_at_mut(k);
    let r = &mut rest[1..];
    quicksort(l);
    quicksort(r);
}

// ---------------------------------------------------------------------------
// §25 (vi) — the executing test vectors, transcribed.

fn main() {
    // (vi.a) `runSplA`: the pivot-crossing SWAP branch, then both no-write branches.
    let check_split = |mut v: Vec<u32>, p: u32, want: &[u32]| {
        split(p, &mut v);
        assert_eq!(v, want, "split p={p}");
    };
    check_split(vec![3, 1], 2, &[1, 3]);
    check_split(vec![1, 3], 2, &[1, 3]);
    check_split(vec![1], 2, &[1]);
    check_split(vec![3], 2, &[3]);
    check_split(vec![], 2, &[]);
    check_split(vec![3, 1, 4], 2, &[1, 3, 4]);
    // Order WITHIN each part is unspecified; this pins the exact trace the DLLBC
    // machine produces, and this transcription reproduces it.
    check_split(vec![4, 1, 3, 2], 2, &[2, 1, 4, 3]);

    // (vi.b/c) `runQsA` against the trusted sort, on the cross-differential inputs.
    let cases: &[&[u32]] = &[
        &[],
        &[1],
        &[2, 1],
        &[3, 1, 2],
        &[1, 2, 3],
        &[3, 2, 1],
        &[5, 5, 5],
        &[4, 1, 3, 2, 5],
        &[3, 1, 4, 1, 5, 9, 2],
        &[9, 8, 7, 6, 5, 4, 3, 2, 1],
        &[2, 2, 1, 1],
        &[7, 3, 7, 3, 7],
    ];
    for c in cases {
        let mut got = c.to_vec();
        quicksort(&mut got);
        let mut want = c.to_vec();
        want.sort();
        assert_eq!(got, want, "quicksort {c:?}");
    }
    println!("all §25 test vectors pass");
}
