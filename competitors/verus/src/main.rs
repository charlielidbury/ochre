use vstd::prelude::*;

verus! {

// SPECS

spec fn perm(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    arr1.to_multiset() == arr2.to_multiset()
}

// HELPER FUNCTIONS

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

fn swap(arr: &mut [i32], i: usize, j: usize)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
    ensures
        final(arr)@ == old(arr)@
            .update(i as int, old(arr)@[j as int])
            .update(j as int, old(arr)@[i as int]),
        final(arr)@.to_multiset() == old(arr)@.to_multiset()
{
    let tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;

    proof {
        broadcast use lemma_swap_preserves_multiset;
    }
}

// CORE ALGORITHM

/// arranges arr into
/// [<p, ...] ++ [p] ++ [>=p, ...]
fn partition(arr: &mut [i32]) -> (pivot: usize)
    requires arr.len() >= 1
    ensures
        0 <= pivot < final(arr).len(),
        perm(final(arr)@, old(arr)@),
        final(arr).len() == old(arr).len()
{
    let p = arr[arr.len() - 1];

    let mut lo = 0; // index of first element NOT in low range
    let mut hi = 0;
    while hi < arr.len() - 1
        invariant
            lo <= hi < arr.len(),
            arr.len() == old(arr).len(),
            perm(arr@, old(arr)@)
        decreases arr.len() - hi,
    {
        assert(perm(arr@, old(arr)@));
        if arr[hi] < p {
            // hi is in the wrong place
            // move it into the low region
            assert(perm(arr@, old(arr)@));
            swap(arr, hi, lo);
            assert(perm(arr@, old(arr)@));
            lo += 1;
            assert(perm(arr@, old(arr)@));
        }
        hi += 1;
    }

    // arr = [<p, ...] ++ [>=p, ...] ++ [p]
    swap(arr, arr.len() - 1, lo);
    // arr = [<p, ...] ++ [p] ++ [>=p, ...]

    lo
}


fn quicksort(arr: &mut [i32])
    ensures
        perm(final(arr)@, old(arr)@)
    decreases arr.len()
{
    if arr.len() <= 1 {
        return;
    }

    // Subdivide `arr` into `lo` and `hi`
    let p = partition(arr);
    let ghost partitioned_arr = arr@;

    let (lo, p_hi) = arr.split_at_mut(p);
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    assert(partitioned_arr == lo@ + p_hi@);

    let (_p, hi) = p_hi.split_at_mut(1);
    assert(partitioned_arr == lo@ + _p@ + hi@);

    // Sort each half
    quicksort(lo);
    quicksort(hi);

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
