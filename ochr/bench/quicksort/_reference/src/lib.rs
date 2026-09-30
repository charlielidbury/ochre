//! Unverified reference for ../SPEC.md: in-place quicksort with Lomuto
//! partition and two recursive calls on disjoint sub-slices obtained by
//! `split_at_mut`. It exists only to validate tests.json; it is never copied
//! into a sandbox.

pub fn quicksort(a: &mut [u64]) {
    if a.len() <= 1 {
        return;
    }
    let p = partition(a);
    // a[p] is the pivot in its final place; it belongs to neither half.
    let (left, right) = a.split_at_mut(p);
    quicksort(left);
    quicksort(&mut right[1..]);
}

/// Lomuto: the pivot is the last element. Returns its final index p, with
/// a[..p] <= a[p] < a[p + 1..].
fn partition(a: &mut [u64]) -> usize {
    let hi = a.len() - 1;
    let pivot = a[hi];
    let mut i = 0;
    for j in 0..hi {
        if a[j] <= pivot {
            a.swap(i, j);
            i += 1;
        }
    }
    a.swap(i, hi);
    i
}
