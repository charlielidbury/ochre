//! In-place quicksort of a `u64` slice, to be verified with Aeneas.
//!
//! The regions between the FIXED begin and end marker comments must stay byte-identical.
//! Replace the `todo!()` with a real body. You may add private helper functions
//! (a partition function, for instance) anywhere outside the FIXED regions.

// FIXED-BEGIN quicksort
/// Sorts `a` in place, in ascending order.
///
/// Partition the slice (Lomuto or Hoare; say which in a comment), then sort the
/// two disjoint sub-slices on either side of the pivot by recursive calls on
/// borrows obtained with `split_at_mut` (or `split_at_mut`-style reborrows). No
/// copy-out/copy-back: auxiliary space is O(1) beyond the recursion.
pub fn quicksort(a: &mut [u64]) {
// FIXED-END quicksort
    todo!()
}
