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
open Classical

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
  simp only [run, SM.erasedIf, SM.stmtIf, SM.headOf, SM.onCopy, meanV_abs, meanV_tNat, meanV_loan, K₀, D₀, ρ₀, Δ₀, bind, Option.bind, Option.map,
    pure, Sem.asTy, TyS.plain, Bool.false_eq_true, if_false, runT]
  -- the strict ascription `σ0 : Nat`: `n` is a `Nat`, and the unknown's run carries no label
  simp only [SM.strictS, strictVal, pure, labTyOk, reduceCtorEq, false_implies, implies_true, if_true, mem_nat]
  rw [pushBindShaped_noLabel _ _ rfl, pushBind_emptyState]
  simp only [runArgs, bind, pure]
  simp only [run, SM.erasedIf, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, runT]
  simp only [SM.strictS]
  erw [SM.guarded_of (contentOk_one _ _ _ _)]
  rw [borrowPlace_var0_one _ _ _ _ (by simp [Sem.whole])]
  dsimp only
  simp only [List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, Nat.zero_max,
    Nat.reduceAdd, Bool.false_eq_true, reduceIte, mem_nat, if_true]
  erw [invalidate_noInv (K₀ dm C) φ (fun _ _ => rfl)]
  erw [if_pos ⟨invalidateOk_noInv (K₀ dm C) φ (fun _ _ => rfl) _ _, lentOk_root (K₀ dm C) φ (pos := .bind 0 0) rfl⟩]
  dsimp only
  -- the strict call: the borrow of `c1` is live and holds `Nat`, `σ1`'s parameter's content type
  erw [if_pos (borrowArgs_S₂ dm.read F n ⟨.plain TyM.nat, fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n) rfl)]
  erw [callOf_S₂ _ F n ⟨.plain TyM.nat, fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n)]
  dsimp only
  have hp := pushBindShaped_S₃ F n ⟨.plain TyM.nat, fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n)
  simp only [rBind] at hp
  -- the strict write `*r := loan_1`: the hole's content is written where it is a number (the
  -- place's type is `Nat`), and the run fails where it is not, so the fill means `err` there
  simp only [hp, placeTy, contentOf_deref_r, labTyOk, reduceCtorEq, false_implies, implies_true, and_true]
  cases hφ : (φ 1).as Nat with
  | none =>
    rw [if_neg (by exact not_mem_nat_of_as hφ)]
    simp [Sem.asNat, hφ]
  | some x =>
    rw [if_pos (by exact mem_nat_of_as hφ)]
    erw [SM.guarded_of (assignOk_deref_S₄ _ φ F n _ 0 (.el0 Nat n))]
    simp only [contentOf_deref_r, assignAt, resolve_deref_r, access_S₄, List.isEmpty_cons, Bool.false_and,
      Bool.false_eq_true, reduceIte, setContent_deref_r]
    erw [invalidate_noInv (K₀ dm C) φ (fun _ _ => rfl)]
    erw [if_pos ⟨invalidateOk_noInv (K₀ dm C) φ (fun _ _ => rfl) _ _,
      lentOk_deref_S₅ (K₀ dm C) φ F n _ 0 (.el0 Nat n) (φ 1) rfl (mem_nat_of_as hφ)⟩]
    dsimp only
    simp only [TyS.plain, discardEnd, SM.modify, bind, Option.bind]
    have hc := readPlace_c1 (K₀ dm C) φ F n ⟨.plain TyM.nat, fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n) (φ 1) rfl
    simp only [K₀, D₀, TyS.plain] at hc
    erw [guardMod_discard_plain (K₀ dm C) φ TyM.unit]
    dsimp only
    erw [SM.guarded_of (contentOk_c1_S₅ (K₀ dm C) φ F n _ 0 (.el0 Nat n) (φ 1) (mem_nat_of_as hφ))]
    simp only [hc, Sem.asNat, hφ]
    erw [if_pos (letGuard_noShape _ φ _ (shape_S₆ F n _ 0 (.el0 Nat n) (φ 1)))]
    simp only [held_noShape _ (shape_S₆ F n _ 0 (.el0 Nat n) (φ 1))]
    erw [if_pos (letGuard_noShape _ φ _ (shape_letLenders_dropLast _ (shape_S₆ F n _ 0 (.el0 Nat n) (φ 1))))]

end Ochr.Meaning.Attack
