//! In-place quicksort of a `u64` slice, verified with Verus.
//!
//! The FIXED regions (each between a begin and an end marker comment) must stay
//! byte-identical.
//! Fill in the hole: the `todo!()` body of `quicksort`. You may add spec functions,
//! proof functions (lemmas) and private exec helpers (a partition function, a recursive
//! sorting function) anywhere inside the `verus!` block outside the FIXED regions, and a
//! `decreases` clause right after the FIXED signature (before its body). See ASSIGNMENT.md.

// FIXED-BEGIN prelude
use vstd::prelude::*;

verus! {
// FIXED-END prelude

// FIXED-BEGIN defs
/// `sorted(s)`: every element is at most every later one (SPEC `sorted`).
pub open spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

/// `perm(a, b)`: every value occurs equally often in `a` and in `b` (SPEC `perm`).
///
/// `s.to_multiset()` is vstd's multiset of the elements of `s`, and
/// `s.to_multiset().count(x)` is the number of positions of `s` holding `x`; two
/// multisets are equal exactly when every count agrees.
pub open spec fn perm(a: Seq<u64>, b: Seq<u64>) -> bool {
    a.to_multiset() == b.to_multiset()
}
// FIXED-END defs

// FIXED-BEGIN quicksort
/// Sorts `a` in place, in ascending order.
///
/// Partition the slice (Lomuto or Hoare; say which in a comment), then sort the
/// two disjoint sub-slices on either side of the pivot by recursive calls on
/// borrows obtained with `split_at_mut`. No copy-out/copy-back: auxiliary space
/// is O(1) beyond the recursion.
pub fn quicksort(a: &mut [u64])
    ensures
        sorted(final(a)@), // Q1
        perm(final(a)@, old(a)@), // Q2
// FIXED-END quicksort
{
    todo!()
}

// FIXED-BEGIN verus-end
} // verus!
// FIXED-END verus-end

// FIXED-BEGIN tests
// The tests, transcribed mechanically from tests.json (SPEC section 6) by a script.
// They run as ordinary Rust in the compiled binary: `./grade.sh` builds it with
// `verus --compile` and runs it. Each case sorts a fresh copy of `input` in place
// and compares it with `expected`.

struct Tally {
    passed: u64,
    failed: u64,
}

fn case(t: &mut Tally, name: &str, input: &[u64], expected: &[u64]) {
    let mut a = input.to_vec();
    quicksort(&mut a);
    if a == expected {
        t.passed += 1;
    } else {
        t.failed += 1;
        println!("FAIL {name}: got {a:?}, expected {expected:?}");
    }
}

fn main() {
    let mut t = Tally { passed: 0, failed: 0 };
    case(&mut t, "empty", &[], &[]);
    case(&mut t, "one", &[42], &[42]);
    case(&mut t, "two-sorted", &[1, 2], &[1, 2]);
    case(&mut t, "two-reversed", &[2, 1], &[1, 2]);
    case(&mut t, "duplicates", &[3, 1, 3, 2, 1, 3, 0, 2], &[0, 1, 1, 2, 2, 3, 3, 3]);
    case(&mut t, "sorted", &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
    case(&mut t, "reverse-sorted", &[16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
    case(&mut t, "all-equal", &[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], &[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]);
    case(&mut t, "mixed", &[5, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 0, 99], &[0, 1, 1, 2, 3, 4, 5, 5, 5, 5, 6, 9, 99]);
    case(&mut t, "random-00", &[70, 30, 15, 26, 27, 68, 94, 48, 69, 54, 87, 20, 36, 38, 0, 67, 65, 22, 80, 20, 62, 12, 97, 53], &[0, 12, 15, 20, 20, 22, 26, 27, 30, 36, 38, 48, 53, 54, 62, 65, 67, 68, 69, 70, 80, 87, 94, 97]);
    case(&mut t, "random-01", &[79, 68, 98, 29, 19, 78, 77, 1, 47, 79, 53, 91, 91, 83, 35, 41, 55, 25, 9, 96, 8, 76, 70], &[1, 8, 9, 19, 25, 29, 35, 41, 47, 53, 55, 68, 70, 76, 77, 78, 79, 79, 83, 91, 91, 96, 98]);
    case(&mut t, "random-02", &[], &[]);
    case(&mut t, "random-03", &[0, 2, 0, 3, 3, 0, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2], &[0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]);
    case(&mut t, "random-04", &[32, 15, 81, 46, 25, 65, 74, 57, 34, 50, 96, 34], &[15, 25, 32, 34, 34, 46, 50, 57, 65, 74, 81, 96]);
    case(&mut t, "random-05", &[0, 3, 27, 77, 14, 37, 85, 5, 76, 0, 31, 87, 71, 11, 48, 37, 91, 56, 95, 85, 91, 71, 48], &[0, 0, 3, 5, 11, 14, 27, 31, 37, 37, 48, 48, 56, 71, 71, 76, 77, 85, 85, 87, 91, 91, 95]);
    case(&mut t, "random-06", &[29], &[29]);
    case(&mut t, "random-07", &[1, 1, 0, 1, 0, 2, 2, 0, 3, 2, 1, 1, 2, 2, 2], &[0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]);
    case(&mut t, "random-08", &[0], &[0]);
    case(&mut t, "random-09", &[20, 25, 25, 62, 64, 98, 39, 57, 84, 29, 30], &[20, 25, 25, 29, 30, 39, 57, 62, 64, 84, 98]);
    case(&mut t, "random-10", &[31, 30, 20, 2, 67, 70, 83, 63, 31, 51, 55, 13, 5, 53, 93, 57, 58, 36, 39, 93, 2, 51, 6], &[2, 2, 5, 6, 13, 20, 30, 31, 31, 36, 39, 51, 51, 53, 55, 57, 58, 63, 67, 70, 83, 93, 93]);
    case(&mut t, "random-11", &[1, 3, 1, 1, 1, 0], &[0, 1, 1, 1, 1, 3]);
    case(&mut t, "random-12", &[32, 6, 18, 62, 15, 33, 90], &[6, 15, 18, 32, 33, 62, 90]);
    case(&mut t, "random-13", &[81, 92, 71, 92, 35, 19, 18, 39, 3, 12, 94, 12, 73, 40, 99, 8, 71], &[3, 8, 12, 12, 18, 19, 35, 39, 40, 71, 71, 73, 81, 92, 92, 94, 99]);
    case(&mut t, "random-14", &[92, 18, 32], &[18, 32, 92]);
    case(&mut t, "random-15", &[0, 3, 1, 1, 0, 2], &[0, 0, 1, 1, 2, 3]);
    case(&mut t, "random-16", &[83, 33], &[33, 83]);
    case(&mut t, "random-17", &[66, 41, 59, 84, 32, 11, 27, 32, 18, 96, 77, 21, 6, 73, 80, 92, 42, 91, 40, 3, 41], &[3, 6, 11, 18, 21, 27, 32, 32, 40, 41, 41, 42, 59, 66, 73, 77, 80, 84, 91, 92, 96]);
    case(&mut t, "random-18", &[63, 26, 27, 90, 53, 58, 2, 13, 8, 30, 79, 39, 77, 24, 5, 32], &[2, 5, 8, 13, 24, 26, 27, 30, 32, 39, 53, 58, 63, 77, 79, 90]);
    case(&mut t, "random-19", &[0, 1, 0, 0, 2, 0, 0, 1, 2, 1, 3, 0, 3, 0, 0], &[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3]);
    println!("tests: {} passed, {} failed", t.passed, t.failed);
    if t.failed > 0 {
        std::process::exit(1);
    }
}
// FIXED-END tests
