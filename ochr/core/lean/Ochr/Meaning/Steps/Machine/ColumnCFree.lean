import Ochr.Meaning.Steps.ColumnCFF

/-!
# `def C : Nat := let x = S(Z); x`, with no assumed fact about the checker (machine lane)

`ColumnC.column_C_ff` assumes the state-level lemmas (`InvSteps`) and that the fuel-free table is
local in its places (`PlaceLocal`); both are proved (`Machine.invSteps`, `Machine.placeLocal_ff`).
What remains assumed is only what the statement is about: a successful run of the checker on the
body of `C` from a state with the kernel `checkDef` starts it from, in the plain mode, no handed-down
reading. That run itself is `#guard`ed (`ColumnC.lean`, `isOk (Ochr.eval 100 true bodyC …) stC`),
not proved by the kernel (the variable read goes through code the kernel does not unfold).
-/

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The first end-to-end statement with no assumed fact about the checker**: for every successful
typed run of the checker's `eval` on the body of `C` (at any fuel from 9 on) from a state with `C`'s
starting kernel, in the plain mode and with no handed-down reading, the reference interpreter's
strict run of the body, under the checker's own decisions (the fuel-free table at the run's end),
succeeds from the reference state, and its value is `1`, a member of `Nat`, read at the type `Nat`;
for every data model, assignment and future. -/
theorem column_C_free {g : Nat} (dm : DataModel) (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 9) true bodyC (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat))
        bodyC (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat :=
  column_C_ff Machine.invSteps dm ρ φ hk hm htd h (Machine.placeLocal_ff st' _)

#print axioms column_C_free

end Ochr.Meaning.Steps.Form.ColumnC
