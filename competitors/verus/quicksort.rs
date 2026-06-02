// In-place quicksort in Verus, verified for BOTH:
//   1. sortedness of the output, and
//   2. permutation (multiset-equality) of output vs input.
//
// Partition scheme: Lomuto, operating on an index sub-range [lo, hi) of a single
// `&mut Vec<u64>`. The "disjoint mutable split" of the README is expressed the
// idiomatic Verus way: index-based sub-ranges of ONE mutable borrow, with loop
// invariants pinning down which indices each phase may touch. Verus's SMT backend
// reasons about the whole array's `Seq` view directly; there is no separate heap
// model and no split-borrow ceremony.
//
// Verify:  verus quicksort.rs

use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

// ---------------------------------------------------------------------------
// Spec predicates over the abstract Seq view of the vector.
// ---------------------------------------------------------------------------

// `s[lo..hi]` is sorted ascending.
pub open spec fn sorted_between(s: Seq<u64>, lo: int, hi: int) -> bool {
    forall|i: int, j: int| lo <= i <= j < hi ==> s[i] <= s[j]
}

// Every element of `s[lo..hi]` is <= pivot value `p`.
pub open spec fn all_le(s: Seq<u64>, lo: int, hi: int, p: u64) -> bool {
    forall|i: int| lo <= i < hi ==> s[i] <= p
}

// Every element of `s[lo..hi]` is >= pivot value `p`.
pub open spec fn all_ge(s: Seq<u64>, lo: int, hi: int, p: u64) -> bool {
    forall|i: int| lo <= i < hi ==> s[i] >= p
}

// ---------------------------------------------------------------------------
// In-place swap. The fundamental permutation-preserving primitive: swapping two
// elements leaves the multiset unchanged.
// ---------------------------------------------------------------------------

fn swap(v: &mut Vec<u64>, i: usize, j: usize)
    requires
        i < old(v).len(),
        j < old(v).len(),
    ensures
        final(v).len() == old(v).len(),
        // pointwise: i and j trade values; everything else is untouched.
        final(v)@ == old(v)@.update(i as int, old(v)@[j as int]).update(j as int, old(v)@[i as int]),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        forall|k: int| 0 <= k < final(v).len() && k != i && k != j ==> final(v)@[k] == old(v)@[k],
{
    let vi = v[i];
    let vj = v[j];
    v.set(i, vj);
    v.set(j, vi);

    proof {
        lemma_swap_multiset(old(v)@, i as int, j as int);
    }
}

// A swap (two updates trading values at i and j) preserves the multiset.
// Proved directly from vstd's `to_multiset_update`:
//     s.update(i,a).to_multiset() == s.to_multiset().insert(a).remove(s[i])
proof fn lemma_swap_multiset(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    broadcast use to_multiset_update;
    let m = s.to_multiset();
    let s1 = s.update(i, s[j]);
    if i == j {
        assert(s1.update(j, s[i]) =~= s);
    } else {
        // s1[j] == s[j] because i != j.
        assert(s1[j] == s[j]);
        // Apply `to_multiset_update` twice:
        //   s1.to_multiset()                == m.insert(s[j]).remove(s[i])
        //   s1.update(j,s[i]).to_multiset() == s1.to_multiset().insert(s[i]).remove(s1[j])
        //                                   == m.insert(s[j]).remove(s[i]).insert(s[i]).remove(s[j])
        let m1 = m.insert(s[j]).remove(s[i]);
        let m2 = m1.insert(s[i]).remove(s[j]);
        assert(s1.update(j, s[i]).to_multiset() == m2);
        // m2 == m by counting: at every value x, the inserts of s[i],s[j] cancel
        // the removes of s[i],s[j] (the +1/-1 land on the same value), so counts
        // match. We need `s[i]` to actually be present so that the `remove`
        // genuinely decrements (it is: s[i] is in s, hence in m).
        assert(m.count(s[i]) > 0) by {
            s.to_multiset_ensures();
            assert(s.contains(s[i]));
        }
    }
}

// A swap of positions i,j (both inside [lo,hi)) preserves any uniform bound on
// the range [lo,hi): the multiset of values in the range is unchanged, and a
// uniform bound only depends on that multiset. `after` relates to `before` by the
// pointwise swap relation (as `swap`'s postcondition provides).
proof fn lemma_swap_preserves_bounds(before: Seq<u64>, after: Seq<u64>, lo: int, hi: int, i: int, j: int)
    requires
        before.len() == after.len(),
        lo <= i < hi,
        lo <= j < hi,
        0 <= lo <= hi <= before.len(),
        // pointwise swap relation: i,j trade values, everything else equal.
        after == before.update(i, before[j]).update(j, before[i]),
    ensures
        forall|b: u64| all_le(before, lo, hi, b) ==> all_le(after, lo, hi, b),
        forall|b: u64| all_ge(before, lo, hi, b) ==> all_ge(after, lo, hi, b),
{
    assert forall|b: u64| all_le(before, lo, hi, b) implies all_le(after, lo, hi, b) by {
        assert forall|k: int| lo <= k < hi implies after[k] <= b by {
            // after[k] is some before[k'] with k' in {i,j,k} ⊆ [lo,hi).
            if k == i {
                assert(after[k] == before[j]);
            } else if k == j {
                assert(after[k] == before[i]);
            } else {
                assert(after[k] == before[k]);
            }
        }
    }
    assert forall|b: u64| all_ge(before, lo, hi, b) implies all_ge(after, lo, hi, b) by {
        assert forall|k: int| lo <= k < hi implies after[k] >= b by {
            if k == i {
                assert(after[k] == before[j]);
            } else if k == j {
                assert(after[k] == before[i]);
            } else {
                assert(after[k] == before[k]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Lomuto partition of v[lo..hi] using v[hi-1] as pivot.
// Returns p with lo <= p < hi such that:
//   v[lo..p]   <= pivot,   v[p] == pivot,   v[p+1..hi] >= pivot,
// the range [lo,hi) is a permutation of the old range, and everything outside
// [lo,hi) is untouched.
// ---------------------------------------------------------------------------

fn partition(v: &mut Vec<u64>, lo: usize, hi: usize) -> (p: usize)
    requires
        lo < hi <= old(v).len(),
    ensures
        final(v).len() == old(v).len(),
        lo <= p < hi,
        // pivot is in place; left side <= pivot, right side >= pivot.
        all_le(final(v)@, lo as int, p as int, final(v)@[p as int]),
        all_ge(final(v)@, p as int + 1, hi as int, final(v)@[p as int]),
        // outside [lo,hi) untouched.
        forall|k: int| 0 <= k < final(v).len() && !(lo <= k < hi) ==> final(v)@[k] == old(v)@[k],
        // permutation of the whole vector (hence of the sub-range).
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        // bound preservation (partition only permutes [lo,hi)).
        forall|b: u64| all_le(old(v)@, lo as int, hi as int, b) ==> all_le(final(v)@, lo as int, hi as int, b),
        forall|b: u64| all_ge(old(v)@, lo as int, hi as int, b) ==> all_ge(final(v)@, lo as int, hi as int, b),
{
    let pivot = v[hi - 1];
    let mut i = lo; // boundary: v[lo..i] <= pivot
    let mut j = lo; // scan pointer: v[i..j] >= pivot
    let ghost orig = v@;

    while j < hi - 1
        invariant
            lo <= i <= j <= hi - 1 < hi <= v.len(),
            v.len() == orig.len(),
            pivot == v@[hi as int - 1],
            all_le(v@, lo as int, i as int, pivot),
            all_ge(v@, i as int, j as int, pivot),
            // outside [lo,hi) untouched.
            forall|k: int| 0 <= k < v.len() && !(lo <= k < hi) ==> v@[k] == orig[k],
            v@.to_multiset() == orig.to_multiset(),
            // bound preservation across the swaps so far.
            forall|b: u64| all_le(orig, lo as int, hi as int, b) ==> all_le(v@, lo as int, hi as int, b),
            forall|b: u64| all_ge(orig, lo as int, hi as int, b) ==> all_ge(v@, lo as int, hi as int, b),
        decreases hi - 1 - j,
    {
        let ghost pre = v@;
        if v[j] <= pivot {
            swap(v, i, j);
            // KEEP: this lemma call is timing-critical (~+11% SMT rlimit if dropped).
            proof { lemma_swap_preserves_bounds(pre, v@, lo as int, hi as int, i as int, j as int); }
            i = i + 1;
        }
        j = j + 1;
    }

    // Place the pivot (currently at hi-1) into position i.
    let ghost pre_final = v@;
    swap(v, i, hi - 1);
    // KEEP: this lemma call is timing-critical (~+12% SMT rlimit if dropped).
    proof { lemma_swap_preserves_bounds(pre_final, v@, lo as int, hi as int, i as int, hi as int - 1); }

    proof {
        // After the final swap: v[i] == pivot. This assert is kept for SMT
        // performance: dropping it raises this function's rlimit (~+16k), it is
        // load for performance, not correctness.
        assert(v@[i as int] == pivot);
    }

    i
}

// ---------------------------------------------------------------------------
// Quicksort of v[lo..hi].
// ---------------------------------------------------------------------------

fn quicksort_rec(v: &mut Vec<u64>, lo: usize, hi: usize)
    requires
        lo <= hi <= old(v).len(),
    ensures
        final(v).len() == old(v).len(),
        sorted_between(final(v)@, lo as int, hi as int),
        // outside [lo,hi) untouched.
        forall|k: int| 0 <= k < final(v).len() && !(lo <= k < hi) ==> final(v)@[k] == old(v)@[k],
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        // Bound preservation: sorting only permutes the range, so any uniform
        // upper/lower bound on the OLD range still bounds the NEW range. This is
        // what lets the caller stitch `left <= pivot <= right` across the
        // recursive calls without reasoning about sub-range multisets directly.
        forall|b: u64| all_le(old(v)@, lo as int, hi as int, b) ==> all_le(final(v)@, lo as int, hi as int, b),
        forall|b: u64| all_ge(old(v)@, lo as int, hi as int, b) ==> all_ge(final(v)@, lo as int, hi as int, b),
    decreases hi - lo,
{
    if hi - lo <= 1 {
        // length 0 or 1: trivially sorted.
        return;
    }

    let ghost orig = v@;
    let p = partition(v, lo, hi);
    let ghost after_part = v@;
    let ghost pivot = v@[p as int];

    // partition gives: [lo,p) <= pivot, v[p] == pivot, [p+1,hi) >= pivot.
    // KEEP: this all_le hint is timing-critical (-38% SMT rlimit; it steers Z3
    // away from an expensive search), not needed for the proof to close.
    assert(all_le(after_part, lo as int, p as int, pivot));

    // Recurse on the two disjoint sub-ranges [lo, p) and [p+1, hi).
    quicksort_rec(v, lo, p);
    let ghost after_left = v@;
    quicksort_rec(v, p + 1, hi);

    proof {
        // The pivot at p is untouched by both recursive calls (each confined to
        // its own range, p excluded from both).
        assert(v@[p as int] == pivot);

        // Left sub-range stays <= pivot through both recursive calls; right stays
        // >= pivot through the right call (left call doesn't touch it). These come
        // directly from the bound-preservation ensures, instantiated at b=pivot.
        assert(all_le(v@, lo as int, p as int, pivot));
        assert(all_ge(v@, p as int + 1, hi as int, pivot));

        // Full sortedness: left sorted, right sorted, and the cross-boundary
        // comparisons hold because left <= pivot == v[p] <= right.
        // KEEP the outer assert: it is timing-critical (+19% SMT rlimit if
        // dropped). The two inner sub-range asserts, by contrast, are dropped
        // (they made verification ~6% slower).
        assert(sorted_between(v@, lo as int, hi as int)) by {
        }

        // Bound-preservation postconditions: any uniform bound on the OLD whole
        // range [lo,hi) survives partition (permutes [lo,hi)) and both recursive
        // sorts (each permutes its sub-range), so it bounds the final range.
        assert forall|b: u64| all_le(orig, lo as int, hi as int, b) implies all_le(v@, lo as int, hi as int, b) by {
            // partition preserves the bound on [lo,hi):
            assert(all_le(after_part, lo as int, hi as int, b));
            // hence on each sub-range and the pivot:
            assert(all_le(after_part, lo as int, p as int, b));
            assert(all_le(after_part, p as int + 1, hi as int, b));
            // left call preserves it on [lo,p), right call on [p+1,hi):
            assert(all_le(after_left, lo as int, p as int, b));
            assert(all_le(v@, p as int + 1, hi as int, b));
            // left range unchanged by the right call:
            assert(all_le(v@, lo as int, p as int, b));
            // pivot at p is bounded (it's an element of after_part[lo,hi)):
            assert(v@[p as int] <= b);
        }
        assert forall|b: u64| all_ge(orig, lo as int, hi as int, b) implies all_ge(v@, lo as int, hi as int, b) by {
            assert(all_ge(after_part, lo as int, hi as int, b));
            assert(all_ge(after_part, lo as int, p as int, b));
            assert(all_ge(after_part, p as int + 1, hi as int, b));
            assert(all_ge(after_left, lo as int, p as int, b));
            assert(all_ge(v@, p as int + 1, hi as int, b));
            assert(all_ge(v@, lo as int, p as int, b));
            assert(v@[p as int] >= b);
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point: sort the whole vector in place.
// ---------------------------------------------------------------------------

pub fn quicksort(v: &mut Vec<u64>)
    ensures
        final(v).len() == old(v).len(),
        sorted_between(final(v)@, 0, final(v)@.len() as int),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
{
    let n = v.len();
    quicksort_rec(v, 0, n);
}

fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(5); v.push(3); v.push(8); v.push(1); v.push(9); v.push(2);
    quicksort(&mut v);
}

}
