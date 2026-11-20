import Ochr.Meaning.Steps.Statements

/-!
# Attack: [Close] is exact, on the shape `let r = σ_g(&a)` (docs/27 §3.2, UseG)

The riskiest central step: a closed-off call means its sealed program's run, which must be
`callOf` of the callee's meaning on the same arguments. This file instantiates `closeCall_step`
on the concrete shape the checker produces for `σ_g(&a)` with `σ_g : Π(x : &Nat). &Nat`
(probed on the checker at 5dc7710b: result `borrow_1 ⌈let c1 = σ0; let r = σ1(&c1); *r⌉`, the
lender `a ↦ ⌈let c1 = σ0; let r = σ1(&c1); *r := loan_1; c1⌉`, counter `2`), and proves what it
can of it, or refutes it. Every piece of the run's borrow bookkeeping (D10–D15), `RunCtx.Δ`
(D17), the telescope code's carrier and `applyFnL` (D59) and the knot are exercised end to end.

Status (2026-11-10): both proved. (A') in `CloseCallFwd.lean`, by stepping the run through the
concrete-state normal forms of `RunEqs.lean` (binding, borrow `S₂`, call `S₃`, `r` bound `S₄`,
`peek(*r)`); (A) in `CloseCallBack.lean`, the same chain then the write through `r` (`S₅`) and
the read of `c1`, whose [Access] ends `r`'s borrow and fixes the returned label's final content
to the hole's (`S₆`). So on this shape [Close] is exact against the reference's call: the
checker's sealed programs mean the forward value and the backward function, as `callOf` gives
them. Probe findings that shaped `RunEqs.lean` (a throwaway `simp` unfolding of `res_means_fwd`): `unfold meanV` then
`simp [run, emptyState, pushBindShaped, contentOf, readPlace, borrowPlace, runArgs, callOf,
callOfL, applyFnL, …, runT]` reduces the `ascribe`/`letIn`/`borrow` prefix and reaches `callOf` with
`fv.2 = Δ₀ 1` (the telescope code `telG`) and `fv.1 = meanV … (.abs 1)`, as intended. Two
obstacles: (1) `simp [Sem.updAt]` fails outright ("failed to generate equational theorem for
`Sem.updAt`", at its number branch), so every place write
(`setContent`, hence the fill's `*r := loan_1`) must be reduced by a hand lemma on the concrete
steps; (2) the ascription's hint becomes `plain (meanV … .tNat).asTy`, which only reduces with
`meanV` itself in the simp set (its `.sealed`/`.clo` clauses then unfold the knot everywhere, so
the set must be restricted to the clauses used: `.abs`, `.tNat`, `.loan`). Neither is a
refutation; both are proof-engineering debt of the run layer, discharged for this shape by
`RunEqs.lean` (equations by `rfl`, normal forms per state, `simp only [h]` to rewrite under the
run's `match`es where `rw` fails on the motive).
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning Ochr.Meaning.Steps

/-- The carrier of `Π(x : &Nat). &Nat` at level 0: from a starting content to a forward value
and an injective backward function into the final contents `PUnit × Nat`. -/
abbrev GCar : Type := (d : Nat) → Back (PUnit × Nat) Nat

/-- `σ_g`'s telescope code: one borrow parameter of content type `Nat`, a borrow result of
content type `Nat`; its carrier is `GCar` (the index of the code). -/
def telG : Tel Code0 PUnit GCar :=
  .param PUnit true Nat .nat (fun _ => Back (PUnit × Nat) Nat) fun _ => .ref (PUnit × Nat) Nat .nat

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
  typeDecl _ _ := .other

/-- Δ: `σ0 : Nat`, `σ1 : Π(x : &Nat). &Nat` at its code. -/
def Δ₀ : Nat → TyS
  | 0 => .plain TyM.nat
  | 1 => .plain (.t0 GCar (.pi GCar telG))
  | _ => .plain TyM.err

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

/- **(A) The fill means the backward function at the hole**: stated and proved in
`CloseCallBack.lean` (`fill_means_back`): `⟦⌈…; *r := loan_1; c1⌉⟧_φ` is `(back_F(n))(φ 1)`'s
final content of the lent place when the hole holds a number, `err` otherwise. -/

/- **(A') The result program means the forward value**: stated and proved in `CloseCallFwd.lean`
(`res_means_fwd`), through the run-layer normal forms of `RunEqs.lean`. -/

end Ochr.Meaning.Attack
