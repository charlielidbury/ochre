import Ochr.Meaning.Steps.Statements

/-!
# Attack: [Close] is exact, on the shape `let r = σ_g(&a)` (docs/27 §3.2, UseG)

The riskiest central step: a closed-off call means its sealed program's run, which must be
`callOf` of the callee's meaning on the same arguments. This file instantiates `closeCall_step`
on the concrete shape the checker produces for `σ_g(&a)` with `σ_g : Π(x : &Nat). &Nat`
(probed on the checker at 5dc7710b: result `borrow_1 ⌈let c1 = σ0; let r = σ1(&c1); *r⌉`, the
lender `a ↦ ⌈let c1 = σ0; let r = σ1(&c1); *r := loan_1; c1⌉`, counter `2`), and proves what it
can of it, or refutes it. Every piece of the run's borrow bookkeeping (D10–D15), `RunCtx.Δ`
(D17), `piCarL`/`applyFnL` and the knot is exercised end to end.

Status (2026-11-10, first attack): both statements compile against the real `meanV`/`run` and are
open. Probe findings (a throwaway `simp` unfolding of `res_means_fwd`): `unfold meanV` then
`simp [run, emptyState, pushBindShaped, contentOf, readPlace, borrowPlace, runArgs, callOf,
callOfL, applyFnL, …]` reduces the `ascribe`/`letIn`/`borrow` prefix and reaches `callOf` with
`fv.2.shape = (Δ₀ 1).shape = some (psG, outG)` and `fv.1 = meanV … (.abs 1)`, as intended. Two
obstacles: (1) `simp [Sem.updAt]` fails outright ("failed to generate equational theorem for
`Sem.updAt`", at the `isTrue`/`.ty0 Nat` branch of `Places.lean:93`), so every place write
(`setContent`, hence the fill's `*r := loan_1`) must be reduced by a hand lemma on the concrete
steps; (2) the ascription's hint becomes `plain (meanV … .tNat).asTy`, which only reduces with
`meanV` itself in the simp set (its `.sealed`/`.clo` clauses then unfold the knot everywhere, so
the set must be restricted to the clauses used: `.abs`, `.tNat`, `.loan`). Neither is a
refutation; both are proof-engineering debt of the run layer. Next: a `run_letIn`/`run_ascribe`
/`run_borrowVar` equation-lemma file for the run layer, then (A') by rewriting, then (A).
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning Ochr.Meaning.Steps

/-- `σ_g`'s shape: one borrow parameter of content type `Nat`, a borrow result of type `Nat`. -/
def psG : List PiParam := [⟨true, fun _ => .ty0 Nat⟩]
def outG : PiOut := .ref fun _ => .ty0 Nat

/-- The carrier of `Π(x : &Nat). &Nat` at level 0: from a starting content to a forward value
and an injective backward function into the final contents `PUnit × Nat`. -/
abbrev GCar : Type := piCarL lvl0 psG [] PUnit outG

example : GCar = ((d : Nat) → Back (PUnit × Nat) Nat) := rfl

/-- Decisions for the shape: nothing is a statement or a proof, nothing is copied, no join, no
re-pointing. -/
def D₀ : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  copy _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := []
  rePointed _ _ := []

/-- Δ: `σ0 : Nat`, `σ1 : Π(x : &Nat). &Nat` with its shape. -/
def Δ₀ : Nat → TyS
  | 0 => .plain (.ty0 Nat)
  | 1 => ⟨.ty0 GCar, some (psG, outG), none, none⟩
  | _ => .plain .err

/-- The context: an arbitrary data model and code meaning (no inductive and no global is
touched), `D₀`, `Δ₀`. -/
def K₀ (dm : DataModel) (C : CodeMeaning) : RunCtx := { dm, Γ := [], C, D := D₀, Δ := Δ₀ }

/-- The assignment: `σ0 ↦ n`, `σ1 ↦ F`, an arbitrary good function. -/
noncomputable def ρ₀ (n : Nat) (F : GCar) : Assignment
  | 0 => .el0 Nat n
  | 1 => .el0 GCar F
  | _ => .err

/-- The checker's fill for the lent place (`closeCall`'s row for `&T`, hole `loan_1`). -/
def fillA : Term :=
  .letIn ⟨"c1"⟩ (.ascribe (.val (.abs 0)) (.val .tNat))
    (.letIn ⟨"r"⟩ (.call (.val (.abs 1)) [.borrow (.var 0)] true)
      (.seq (.assign (.deref (.var 0)) (.val (.loan 1))) (.prim "peek" [.place (.var 1)])))

/-- The checker's result program (the returned borrow's content). -/
def resR : Term :=
  .letIn ⟨"c1"⟩ (.ascribe (.val (.abs 0)) (.val .tNat))
    (.letIn ⟨"r"⟩ (.call (.val (.abs 1)) [.borrow (.var 0)] true)
      (.prim "peek" [.place (.deref (.var 0))]))

/-- **(A) The fill means the backward function at the hole**: `⟦⌈…; *r := loan_1; c1⌉⟧_φ` is
`(back_F(n))(φ 1)`'s final content of the lent place, when the hole holds a number; `err`
otherwise. -/
theorem fill_means_back (dm : DataModel) (C : CodeMeaning) (n : Nat) (F : GCar) (φ : Future) (hint : TyS) :
    meanV (K₀ dm C) (ρ₀ n F) φ hint (.sealed fillA)
      = match (φ 1).asNat with
        | some v => .el0 Nat ((F n).val.2 v).2
        | none => .err := by
  sorry

/-- **(A') The result program means the forward value.** -/
theorem res_means_fwd (dm : DataModel) (C : CodeMeaning) (n : Nat) (F : GCar) (φ : Future) (hint : TyS) :
    meanV (K₀ dm C) (ρ₀ n F) φ hint (.sealed resR) = .el0 Nat (F n).val.1 := by
  sorry

end Ochr.Meaning.Attack
