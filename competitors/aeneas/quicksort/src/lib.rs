//! In-place quicksort on a mutable slice of `u32`, written so that the
//! partition step splits the buffer into two *disjoint mutable halves* via
//! [`slice::split_at_mut`]. The Rust borrow checker proves the two halves are
//! disjoint for free — there is no separation-logic obligation to discharge.
//!
//! This crate is the input to the Charon -> Aeneas -> Lean pipeline. The
//! interesting artifact is how Aeneas turns the `split_at_mut` borrow (a
//! mutable view that is later given back) into a *pure* functional value plus
//! a "back" / continuation function that re-propagates the mutations of the
//! two halves into the parent slice once the borrows end. See `NOTES.md`.

#![allow(clippy::needless_range_loop)]

/// Lomuto partition over `s`, using the last element as the pivot.
///
/// Returns the final pivot index `p`. After the call every element in
/// `s[0..p]` is `<= s[p]` and every element in `s[p+1..]` is `>= s[p]`.
///
/// This works purely by swapping inside the single mutable slice `s`; it does
/// not itself perform the disjoint split. The disjoint `split_at_mut` happens
/// in `quicksort` once we know the pivot index.
fn partition(s: &mut [u32]) -> usize {
    let len = s.len();
    // Pivot is the last element.
    let pivot = s[len - 1];
    let mut i = 0usize;
    let mut j = 0usize;
    while j < len - 1 {
        if s[j] <= pivot {
            s.swap(i, j);
            i += 1;
        }
        j += 1;
    }
    // Put the pivot into its final place.
    s.swap(i, len - 1);
    i
}

/// In-place quicksort of `s` (ascending).
///
/// The recursive structure is the focal point of the comparison: after
/// partitioning we call [`slice::split_at_mut`] to obtain two *disjoint*
/// mutable sub-slices — the elements `<=` the pivot, and the elements `>=`
/// the pivot — and recurse into each independently. The pivot element itself
/// sits between the two halves and is left untouched.
///
/// No copy-out / copy-back: every mutation happens through the borrowed
/// sub-slices.
pub fn quicksort(s: &mut [u32]) {
    let len = s.len();
    if len <= 1 {
        return;
    }
    let p = partition(s);

    // `split_at_mut(p)` yields:
    //   lo = s[0..p]      (elements <= pivot)
    //   hi = s[p..]       where hi[0] is the pivot
    // The borrow checker guarantees `lo` and `hi` are disjoint mutable views.
    let (lo, hi) = s.split_at_mut(p);

    // Recurse into the low half.
    quicksort(lo);
    // `hi[0]` is the pivot; split it off to get the strictly-upper half.
    let (_pivot, upper) = hi.split_at_mut(1);
    quicksort(upper);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_sorted(s: &[u32]) -> bool {
        s.windows(2).all(|w| w[0] <= w[1])
    }

    #[test]
    fn empty() {
        let mut v: Vec<u32> = vec![];
        quicksort(&mut v);
        assert!(is_sorted(&v));
    }

    #[test]
    fn already_sorted() {
        let mut v = vec![1u32, 2, 3, 4, 5];
        quicksort(&mut v);
        assert_eq!(v, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn reverse() {
        let mut v = vec![5u32, 4, 3, 2, 1];
        quicksort(&mut v);
        assert_eq!(v, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn with_dups() {
        let mut v = vec![3u32, 1, 2, 3, 1, 2, 5, 4, 3];
        let mut expected = v.clone();
        expected.sort();
        quicksort(&mut v);
        assert_eq!(v, expected);
    }
}
