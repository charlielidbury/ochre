import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# §16 test suite — the count-preservation proof stack (and, later, swapS)

The campaign's verification heart. This file checks the pure lemma stack that a
spec-carrying swap's `↝`-obligation consumes: the arithmetic warm-ups (the first
real double-inductions after the M11 wall — `add_comm`/`add_assoc` are the
calibration data), then the count/append/take/drop lemmas building to
`count_swapL` (swap preserves the multiset).

Calibration finding: every arithmetic lemma below — including the classic
commutativity and associativity proofs — was authored in the §15 surface and
checked on the FIRST attempt. The surface layer's payoff is not just `le_trans`;
routine nested inductions are now routine.
-/

open Dllbc

namespace Dllbc.Tests.S16Spec

/-- Check a pure lemma `Term` against its type `Term` (deep fuel). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.StdLemmas in
/-! ## The arithmetic warm-ups -/

example : chk StdLemmas.id_sym StdLemmas.id_sym_ty = true := by native_decide
example : chk StdLemmas.add_zero StdLemmas.add_zero_ty = true := by native_decide
example : chk StdLemmas.add_succ StdLemmas.add_succ_ty = true := by native_decide
example : chk StdLemmas.add_comm StdLemmas.add_comm_ty = true := by native_decide
example : chk StdLemmas.add_assoc StdLemmas.add_assoc_ty = true := by native_decide
example : chk StdLemmas.count_cons StdLemmas.count_cons_ty = true := by native_decide

/-! ## The count/append/take/drop lemmas -/

example : chk StdLemmas.count_append StdLemmas.count_append_ty = true := by native_decide
example : chk StdLemmas.take_drop_id StdLemmas.take_drop_id_ty = true := by native_decide

/-! ## `swapL` computes (the pure swap specification) -/

def rd (t : Term) : Val := match (readC 3000 t).run (seedPure [] []) with | .ok v _ => v | .error _ _ => .const "ERR"
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | h :: t => .ctorApp "Cons" [tnat h, tlist t]
def swapLApp (i j l : Term) : Term := .app (.app (.app StdLemmas.swapL i) j) l

example : (rd (swapLApp (tnat 0) (tnat 2) (tlist [1, 2, 3])) == Std.ofList [Std.ofNat 3, Std.ofNat 2, Std.ofNat 1]) = true := by
  native_decide
example : (rd (swapLApp (tnat 1) (tnat 2) (tlist [1, 2, 3])) == Std.ofList [Std.ofNat 1, Std.ofNat 3, Std.ofNat 2]) = true := by
  native_decide

/-! ## Length preservation (the spec swapS carries) — unconditional, no bounds -/

example : chk StdLemmas.len_set StdLemmas.len_set_ty = true := by native_decide
example : chk StdLemmas.len_swapL StdLemmas.len_swapL_ty = true := by native_decide

end Dllbc.Tests.S16Spec
