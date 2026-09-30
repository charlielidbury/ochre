import Mathlib

/-!
# In-place quicksort on an array of words, as a pure function

Read ASSIGNMENT.md first. Every FIXED region (from a begin-marker comment to the
matching end-marker comment) must stay byte-for-byte as it is. Replace every
`sorry`. You may add definitions and lemmas anywhere outside the FIXED regions.
-/

namespace Bench

-- FIXED-BEGIN defs
/-- `sorted a`: every element is at most every later one. -/
def sorted (a : Array UInt64) : Prop :=
  ∀ (i j : Nat) (hij : i < j) (hj : j < a.size), a[i]'(Nat.lt_trans hij hj) ≤ a[j]

/-- `count x l`: the number of positions of `l` holding `x`. -/
def count (x : UInt64) : List UInt64 → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + count x ys

/-- `perm a b`: every word occurs as often in `a` as in `b`. -/
def perm (a b : Array UInt64) : Prop :=
  ∀ x : UInt64, count x a.toList = count x b.toList
-- FIXED-END defs

-- FIXED-BEGIN quicksort
/-- Sorts `a` in ascending order: in place when `a` is unshared (see
ASSIGNMENT.md for the algorithm required). -/
def quicksort (a : Array UInt64) : Array UInt64 :=
-- FIXED-END quicksort
  sorry

/-! ## Properties (see ASSIGNMENT.md) -/

-- FIXED-BEGIN Q1
/-- Q1. -/
theorem quicksort_sorted : ∀ (a : Array UInt64), sorted (quicksort a) :=
-- FIXED-END Q1
  sorry

-- FIXED-BEGIN Q2
/-- Q2. -/
theorem quicksort_perm : ∀ (a : Array UInt64), perm (quicksort a) a :=
-- FIXED-END Q2
  sorry

-- FIXED-BEGIN end
end Bench
-- FIXED-END end
