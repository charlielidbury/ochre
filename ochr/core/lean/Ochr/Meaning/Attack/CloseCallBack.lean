import Ochr.Meaning.Attack.RunEqs

/-!
# (A) of `CloseCall.lean`: the fill means the backward function at the hole

The run of `⌈let c1 = σ0 : Nat; let r = σ1(&c1); *r := loan_1; peek(c1)⌉`: the prefix as in
`CloseCallFwd.lean` to `S₄`; the write through `r` makes `S₅`; reading `c1` is an [Access] that
ends `r`'s borrow, fixing the returned label's final content to the hole's content (`S₆`), so
`c1` means the backward function there, or the read fails when the hole holds no number.
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning

set_option maxHeartbeats 1000000 in
/-- **(A) The fill means the backward function at the hole** (`CloseCall.lean`'s statement). -/
theorem fill_means_back (dm : DataModel) (C : CodeMeaning) (n : Nat) (F : GCar) (φ : Future) (hint : TyS) :
    meanV (K₀ dm C) (ρ₀ n F) φ hint (.sealed fillA)
      = match (φ 1).asNat with
        | some v => .el0 Nat ((F n).val.2 v).2
        | none => .err := by
  unfold meanV
  simp only [fillA, Ochr.Term.loans, Ochr.Term.loansList, Ochr.Value.loans]
  rw [run_letIn (hfl := fun _ _ => rfl), run_ascribe (hfl := fun _ _ => rfl)]
  simp only [run, SM.stmtIf, SM.headOf, SM.onCopy, meanV_abs, meanV_tNat, meanV_loan, K₀, D₀, ρ₀, Δ₀, bind, Option.bind, Option.map,
    pure, Sem.asTy, TyS.plain, Bool.false_eq_true, if_false]
  rw [pushBindShaped_noLabel _ _ rfl, pushBind_emptyState]
  simp only [runArgs, psG, List.getElem?_cons_zero, bind, pure]
  simp only [run, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false]
  rw [borrowPlace_var0_one _ _ _ _ (by simp [Sem.whole])]
  dsimp only
  simp only [List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, Nat.zero_max,
    Nat.reduceAdd, Bool.false_eq_true, reduceIte]
  erw [callOf_S₂ F n ⟨.plain (.ty0 Nat), fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n) .err]
  dsimp only
  have hp := pushBindShaped_S₃ F n ⟨.plain (.ty0 Nat), fun _ => .el0 Nat n, .other, none⟩ 0
  simp only [rBind] at hp
  simp only [hp, contentOf_deref_r, List.isEmpty_cons, Bool.false_eq_true, reduceIte, setContent_deref_r]
  simp only [TyS.plain]
  have hc := readPlace_c1 (K₀ dm C) φ F n ⟨{ m := .ty0 Nat }, fun _ => .el0 Nat n, .other, none⟩ 0 (φ 1) rfl
  simp only [K₀, D₀, TyS.plain] at hc
  first
    | (simp only [hc, Sem.asNat]; cases (φ 1).as Nat <;> simp)
    | (trace_state; sorry)

end Ochr.Meaning.Attack
