import Ochr.Meaning.Steps.ColumnBFF
import Ochr.Meaning.Steps.Machine.FormFacts

/-!
# `def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`, with no assumed fact about the checker (machine lane)

The borrow column: a live borrow of `x` written through (`*y := Z`), then ended by reading its
lender (`x`). `ColumnB.column_B_ff` assumes three facts about the checker's runs (`AssignDerefInv`,
`VarEndInv`, `SeqInv`), the state-level lemmas (`InvSteps`) and that the fuel-free table is local in
its places (`PlaceLocal`); all are proved (`Machine.assignDerefInv`, `Machine.varEndInv`,
`Machine.seqInv`, `Machine.invSteps`, `Machine.placeLocal_ff`).

What it says: every successful typed run of the checker's `eval` on the body of `B` (at any fuel from
15 on), from a state with the kernel `checkDef` starts a constant's body at, in the plain mode and
with no handed-down reading, makes the reference interpreter's strict run of the body succeed (under
the checker's own decisions, the fuel-free table at the run's end) with `0`, a member of `Nat`, at the
type `Nat`, for every data model, assignment and future.

What it does not say: that such a run exists (that is `#guard`ed, `ColumnB.lean`: `outVal (Ochr.eval
100 true bodyB (some .tNat)) stC 1000 == (.zero, some .tNat)`, not proved by the kernel: the access
and the ending go through well-founded code the kernel does not unfold); anything about another
program (it is one program, each step's fact restricted to that step's shape: a borrow of a variable
holding a number stored at `Nat`, a write through a variable stored at `&Nat` holding `borrow_l w`
with `w` a number, the read of a lender at the two-binding state); and what the value means, which
comes from the model half (`runT`, `∈ₛ`), not from this file.
-/

namespace Ochr.Meaning.Steps.Form.ColumnB

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnC

/-- **The borrow column with no assumed fact about the checker**: for every successful typed run of
the checker's `eval` on the body of `B` from a state with `B`'s starting kernel, in the plain mode and
with no handed-down reading, the strict run of the body under the checker's fuel-free decisions
succeeds from the reference state with `0`, a member of `Nat`, read at `Nat`; for every data model,
assignment and future. -/
theorem column_B_free {g : Nat} (dm : DataModel) (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 15) true bodyB (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat))
        bodyB (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 0 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat :=
  column_B_ff Machine.assignDerefInv Machine.varEndInv Machine.seqInv Machine.invSteps dm ρ φ hk hm htd h
    (Machine.placeLocal_ff st' _)

#print axioms column_B_free

end Ochr.Meaning.Steps.Form.ColumnB
