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

end Dllbc.Tests.S16Spec
