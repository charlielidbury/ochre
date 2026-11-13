import Ochr.Meaning.Attack.RunEqs

/-!
# (A') of `CloseCall.lean`: the result program means the forward value

The run of `⌈let c1 = σ0 : Nat; let r = σ1(&c1); peek(*r)⌉` from the empty state, stepped
through the normal forms of `RunEqs.lean`: the ascription binds `n`, the borrow makes `S₂`, the
call `S₃`, the binding of `r` `S₄`, and `peek(*r)` reads the forward value.
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning

set_option maxHeartbeats 1000000 in
/-- **(A') The result program means the forward value** (`CloseCall.lean`'s statement): the run
of `⌈let c1 = σ0 : Nat; let r = σ1(&c1); peek(*r)⌉` at any hint and future is `(F n).val.1`. -/
theorem res_means_fwd (dm : DataModel) (C : CodeMeaning) (n : Nat) (F : GCar) (φ : Future) (hint : TyS) :
    meanV (K₀ dm C) (ρ₀ n F) φ hint (.sealed resR) = .el0 Nat (F n).val.1 := by
  unfold meanV
  simp only [resR, Ochr.Term.loans, Ochr.Term.loansList, Ochr.Value.loans]
  rw [run_letIn, run_ascribe]
  simp only [run, SM.onCopy, meanV_abs, meanV_tNat, K₀, D₀, ρ₀, Δ₀, bind, Option.bind, Option.map, pure,
    Sem.asTy, TyS.plain, Bool.false_eq_true, if_false]
  rw [pushBindShaped_noLabel _ _ rfl, pushBind_emptyState]
  simp only [runArgs, psG, List.getElem?_cons_zero, bind, pure]
  simp only [run]
  rw [borrowPlace_var0_one _ _ _ _ (by simp [Sem.whole])]
  dsimp only
  simp only [List.nil_append, List.foldl_nil, Nat.zero_add, Bool.false_eq_true, reduceIte]
  erw [callOf_S₂ F n ⟨.plain (.ty0 Nat), fun _ => .el0 Nat n, .other, none⟩ 0 (.el0 Nat n) .err]
  dsimp only
  have hp := pushBindShaped_S₃ F n ⟨.plain (.ty0 Nat), fun _ => .el0 Nat n, .other, none⟩ 0
  simp only [rBind] at hp
  simp only [hp, readPlace_deref_r]

end Ochr.Meaning.Attack
