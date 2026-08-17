import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# HM PROBE — arrays whose payload is STRUCTURED

A viability probe for a planned hashmap flagship: `slots : Array cap (List (Σ k. T))`,
i.e. the Aeneas ICFP'22 case study's shape (buckets = association lists in the slots
of an array). Every existing array test in the tree uses `Array n Nat`; the question
this file answers is what changes when the payload is a list, a pair, or a list of
pairs.

Each section is one probe question. Verdicts are asserted, not narrated — a `= true`
is a WORKS and a `= false` (or a `progRejects` needle) is a FAILS with the error
pinned in the assertion itself.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  LebTrueLe LebFalseGt AddSucc AddZero IdTrans IdCongr IdSym)

namespace Dllbc.Tests.HmProbeArrays

/-- Type-check a closed term against a closed type in the pure seed (as ArraySort's). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## A1 — array literals of structured payload

    `ctorSig "Arr"` builds its field telescope as `T` repeated `n` times, generic in
    `T` (Pure.lean ~498), so the question is whether anything downstream is
    Nat-specific. -/

-- (a) An array of LISTS.
example : chkL prog{ Arr(Nil, Cons(1, Nil)) } prog{ Array 2 (List Nat) } = true := by
  native_decide

-- …and it is not vacuous: the payload type is checked elementwise.
example : chkL prog{ Arr(Nil, Cons(True, Nil)) } prog{ Array 2 (List Nat) } = false := by
  native_decide
example : chkL prog{ Arr(Nil, 3) } prog{ Array 2 (List Nat) } = false := by native_decide

-- (b) An array of PAIRS — the association-list entry shape, non-dependently.
example : chkL prog{ Arr(Pair(1, 2), Pair(3, 4)) } prog{ Array 2 (Σ (k : Nat) → Nat) } = true := by
  native_decide
example : chkL prog{ Arr(Pair(1, True), Pair(3, 4)) } prog{ Array 2 (Σ (k : Nat) → Nat) }
    = false := by native_decide

-- (c) THE HASHMAP SHAPE: an array of lists of pairs.
example : chkL prog{ Arr(Nil, Cons(Pair(5, 7), Nil), Cons(Pair(1, 2), Cons(Pair(3, 4), Nil))) }
               prog{ Array 3 (List (Σ (k : Nat) → Nat)) } = true := by native_decide

-- (d) Empty and singleton, and the length index is enforced.
example : chkL prog{ Arr() } prog{ Array 0 (List Nat) } = true := by native_decide
example : chkL prog{ Arr(Nil) } prog{ Array 2 (List Nat) } = false := by native_decide

end Dllbc.Tests.HmProbeArrays
end
