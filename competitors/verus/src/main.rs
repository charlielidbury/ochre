use vstd::prelude::*;

verus! {

// SPECS

spec fn sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < arr.len() ==> arr[i] <= arr[j]
}

spec fn perm(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    arr1.to_multiset() == arr2.to_multiset()
}


// HELPER PROOFS

broadcast proof fn lemma_swap_preserves_multiset(s: Seq<i32>, i: usize, j: usize)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        #[trigger] s
            .update(i as int, s[j as int])
            .update(j as int, s[i as int])
            .to_multiset() == s.to_multiset()
{
    broadcast use vstd::seq_lib::to_multiset_update;
    broadcast use vstd::seq_lib::to_multiset_contains;
}


// HELPER FUNCTIONS

fn swap(arr: &mut [i32], i: usize, j: usize)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
    ensures
        final(arr)@ == old(arr)@
            .update(i as int, old(arr)@[j as int])
            .update(j as int, old(arr)@[i as int]),
{
    let tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}

// CORE ALGORITHM

/// arranges arr into
/// [<p, ...] ++ [p] ++ [>=p, ...]
fn partition(arr: &mut [i32]) -> (pivot: usize)
    requires arr.len() >= 1
    ensures
        0 <= pivot < final(arr).len(), // "returns an index into the slice"
        perm(final(arr)@, old(arr)@), // "partition only moves elements"
        final(arr).len() == old(arr).len(), // required for termination

        // elements below the pivot are less than it, elements above are more than (or equal)
        forall|k: int| 0    <= k < pivot            ==> final(arr)[k] <  final(arr)[pivot as int],
        forall|k: int| pivot < k < final(arr).len() ==> final(arr)[k] >= final(arr)[pivot as int],
{
    broadcast use lemma_swap_preserves_multiset;

    let p = arr[arr.len() - 1];

    let mut lo = 0; // index of first element NOT in low range
    let mut hi = 0;
    while hi < arr.len() - 1
        invariant
            lo <= hi < arr.len(), // "loop preseves {lo, hi} ordering and validity"
            arr.len() == old(arr).len(), // "loop preserves arr len"
            perm(arr@, old(arr)@), // "loop only moves elements"
            forall|k: int| 0 <= k < lo ==> arr[k] < p, // "low region is lt pivot"
            forall|k: int| lo <= k < hi ==> arr[k] >= p, // "high region is gte pivot"

            arr[arr.len() - 1] == p, // "loop does not touch pivot element"
        decreases arr.len() - hi,
    {
        if arr[hi] < p {
            // hi is in the wrong place
            // move it into the low region
            swap(arr, hi, lo);
            lo += 1;
        }
        hi += 1;
        broadcast use lemma_swap_preserves_multiset; // needed for it to get the perm loop invariant
    }

    // arr = [<p, ...] ++ [>=p, ...] ++ [p]
    let ghost arr_pre = arr@;
    swap(arr, arr.len() - 1, lo);
    assert(arr_pre.subrange(0, lo as int) == arr@.subrange(0, lo as int)); // elements before lo are uneffected
    // arr = [<p, ...] ++ [p] ++ [>=p, ...]

    lo
}

proof fn lemma_multiset_preserves_forall(s1: Seq<i32>, s2: Seq<i32>, pred: spec_fn(i32) -> bool)
    requires
        s1.to_multiset() == s2.to_multiset(),
        forall|i: int| 0 <= i < s1.len() ==> pred(s1[i])
    ensures
        forall|i: int| 0 <= i < s2.len() ==> pred(s2[i])
{
    broadcast use vstd::seq_lib::group_seq_properties;

    assert(s1.len() == s2.len()) by {
        let ghost sm1 = s1.to_multiset().len();
    };
    assert forall|i: int| 0 <= i < s2.len() implies pred(s2[i]) by {
        let ghost e = s2[i];

        // s1 and s2's multisets are equal, so anything in one is in the other
        assert(s1.to_multiset().contains(s2[i]));
        // once solver realises s2[i] is somewhere in s1
        // it notices that pred holds forall elements and closes the goal
    };
}

fn quicksort(arr: &mut [i32])
    ensures
        perm(final(arr)@, old(arr)@),
        sorted(final(arr)@)
    decreases arr.len()
{
    if arr.len() <= 1 {
        return;
    }

    // Subdivide `arr` into `lo` and `hi`
    let p = partition(arr);
    let ghost partitioned_arr = arr@;
    let ghost pivot = arr[p as int];

    let (lo, p_hi) = arr.split_at_mut(p);
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    assert(partitioned_arr == lo@ + p_hi@);

    let (_p, hi) = p_hi.split_at_mut(1);
    assert(partitioned_arr == lo@ + _p@ + hi@);


    // Sort each half
    let ghost pre_lo = lo@;
    quicksort(lo);
    assert(forall|k: int| 0 <= k < lo.len() ==> lo[k] < pivot) by {
        lemma_multiset_preserves_forall(pre_lo, lo@, |e: i32| e < pivot);
    };
    let ghost pre_hi = hi@;
    quicksort(hi);
    assert(forall|k: int| 0 <= k < hi.len() ==> hi[k] >= pivot) by {
        lemma_multiset_preserves_forall(pre_hi, hi@, |e: i32| e >= pivot);
    }

    assert((lo@ + _p@ + hi@).to_multiset() == final(arr)@.to_multiset());
}

fn test() {
    let mut v1: Vec<i32> = vec![4, 3, 5, 1, 2];
    let mut v2: Vec<i32> = vec![1, 2, 3, 4, 5];

    // intermediate proof BS
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    assert(v1@ == Seq::<i32>::empty().push(4).push(3).push(5).push(1).push(2));
    assert(v2@ == Seq::<i32>::empty().push(1).push(2).push(3).push(4).push(5));

    assert(v1@.to_multiset() == v2@.to_multiset());
}

}

fn main() {
    let mut v: Vec<i32> = vec![4, 31, 22, 1, 12];
    println!("{:?}", &v);
    quicksort(&mut v);
    println!("{:?}", v);
}
