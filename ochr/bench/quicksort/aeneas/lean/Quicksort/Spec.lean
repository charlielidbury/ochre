-- FIXED-BEGIN spec
-- The definitions of ASSIGNMENT.md (Definitions), over the list of elements of a slice.
-- This whole file is FIXED, and grade.sh always uses the original.
import Aeneas

open Aeneas Aeneas.Std

namespace quicksort

/-- `sorted l`: every element is at most every later element. -/
def sorted (l : List U64) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]!.val ≤ l[j]!.val

/-- `count x l`: the number of positions of `l` holding `x`. -/
def count (x : U64) : List U64 → Nat
  | [] => 0
  | y :: l => (if y = x then 1 else 0) + count x l

/-- `perm l₁ l₂`: every word occurs equally often in `l₁` and `l₂`. -/
def perm (l₁ l₂ : List U64) : Prop :=
  ∀ x, count x l₁ = count x l₂

end quicksort
-- FIXED-END spec
