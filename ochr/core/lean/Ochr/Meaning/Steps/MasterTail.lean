import Ochr.Meaning.Steps.MasterLeaf
import Ochr.Meaning.Steps.MasterGuards

/-!
# The master induction's tail step for a term `checkTail` does not treat by shape (lead22, 2026-11-22; docs/31 D151)

`checkTailAt`'s default case evaluates the term TYPED with the goal as its hint and hands the value and
its type to the continuation. So `TStepOther` is the evaluation step at a lower fuel, read in tail
position: `tStepOther` proves it from the induction hypothesis, one new fact about the checker
(`TailOtherInv`: that inversion, stated and guarded here) and one fact about the model proved here
(`runT_tl_indep`: the reference reads its tail flag only at `let`, `;` and the two matches).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The reference reads the tail flag only at the shapes `checkTail` treats -/

/-- **The reference's run of a term `checkTail` does not treat by shape reads no tail flag.** -/
theorem runT_tl_indep {K : RunCtx} {ρ : Assignment} {φ : Future} (t : Term) (ht : tailShaped t = false)
    (tl tl' : Bool) (hint : TyS) : runT K ρ φ tl hint t = runT K ρ φ tl' hint t := by
  cases t with
  | letIn => simp [tailShaped] at ht
  | seq => simp [tailShaped] at ht
  | matchNat => simp [tailShaped] at ht
  | matchInd => simp [tailShaped] at ht
  | prim n args =>
    by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
    · obtain ⟨h0, rfl, rfl⟩ := e1; rw [runT, runT]
    by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
    · obtain ⟨h0, k0, rfl, rfl⟩ := e2; rw [runT, runT]
    by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, rfl⟩ := e3; simp [tailShaped] at ht
    by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, rfl⟩ := e4; simp [tailShaped] at ht
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ; rw [runT, runT]
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, rfl⟩ := hc
      rcases hn with rfl | rfl | rfl <;> rw [runT, runT]
    by_cases hsp : ∃ f u, n = "split" ∧ args = [.const f, u]
    · obtain ⟨f, u, rfl, rfl⟩ := hsp; simp [tailShaped] at ht
    have hs' : ∀ f u, n = "split" → args = [.const f, u] → False := fun f u e1 e2 => hsp ⟨f, u, e1, e2⟩
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    have f1 : ∀ h, n = "symm" → args = [h] → False := fun h0 a b => e1 ⟨h0, a, b⟩
    have f2 : ∀ h k, n = "trans" → args = [h, k] → False := fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
    have f3 : ∀ h u, n = "rewrite" → args = [h, u] → False := fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
    have f4 : ∀ h u, n = "rewriteR" → args = [h, u] → False := fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
    rw [runT, runT]
    all_goals first | rfl | exact f1 | exact f2 | exact f3 | exact f4 | exact hJ' | exact hc1 | exact hc2 | exact hc3 | exact hs'
  | _ => rw [runT.eq_def, runT.eq_def]

/-! ## The checker's default case in tail position -/

/-- **`checkTail` of a term it does not treat by shape** (a fact about the checker alone, NEW, for the
machine lane; guarded below): the run is `eval` of the term, typed, two fuel down, with the goal as its
hint, from a state with the same kernel, mode, handed-down reading, tail flag and goal (the editor's
`locatedTail` touches none of them), returning a type, followed by the continuation on the value and
that type, which ends the run. -/
def TailOtherInv : Prop :=
  ∀ (n : Nat) (t : Term) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    tailShaped t = false → Runs (Ochr.checkTail n t k) st bh () st' →
    ∃ (m : Nat) (st₀ st₁ : MState) (v T : Value) (b₁ b₂ : Nat),
      m + 2 ≤ n ∧ Kern st st₀ ∧ ModeEq st st₀ ∧ st₀.tailDecl = st.tailDecl ∧ st₀.tailNext = st.tailNext ∧
      st₀.goal = st.goal ∧
      Runs (Ochr.eval m true t st.goal) st₀ b₁ (v, some T) st₁ ∧ Runs (k v T) st₁ b₂ () st'

namespace TailGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk)

/-- A continuation that succeeds exactly on `S(Z)` at `Nat`. -/
def kOne : Value → Value → M Unit := fun v T => if v == .succ .zero && T == .tNat then pure () else err "k"

-- the default case hands the continuation the value and type of the typed evaluation
#guard isOk (Ochr.checkTail 100 (.succ .zero) kOne) { goal := some .tNat } 100000
#guard !isOk (Ochr.checkTail 100 .zero kOne) { goal := some .tNat } 100000
#guard !isOk (Ochr.checkTail 100 (.succ .zero) (fun _ _ => err "k")) { goal := some .tNat } 100000
-- a term of the shape the default case does not treat: `tailShaped` is `false` on both, `true` on `let`
#guard tailShaped (.succ .zero) == false && tailShaped (.prim "clone" [.place (.var 0)]) == false &&
  tailShaped (.letIn ⟨"x"⟩ .zero .zero) == true && tailShaped (.prim "rewrite" [.zero, .zero]) == true

end TailGuards

/-! ## The step -/

/-- **The tail step for every term `checkTail` does not treat by shape, in general**: `TStepOther` for every
context and future. ASSUMES 1 fact about the checker, `TailOtherInv`; the model fact it uses,
`runT_tl_indep`, is proved. -/
theorem tStepOther (hT : TailOtherInv) (K : RunCtx) (φ : Future) : TStepOther K φ := by
  intro n ih Δ ρ t ht st k s π bh st' hm htn hne htd hk hp hr hS hv hab hnh hD hrun
  obtain ⟨m, st₀, st₁, v, T, b₁, b₂, hmn, hk₀, hme₀, htd₀, htn₀, hg₀, hev, hkr⟩ := hT n t k st st' bh ht hrun
  have hD₁ : DecTab K.D st₁ := hD.back (hk v T st₁ b₂ () st' hkr)
  have hab₀ : t.absBelow st₀.absTy.size := by rw [← hk₀.absTy]; exact hab
  have hO := (ih m (by omega) Δ ρ).1 t st₀ st₁ true st.goal v (some T) s π (hm.of_modeEq hme₀)
    (fun _ => htn₀.trans htn) (by rw [← ColumnC.size_of_erase hk₀.env]; exact hne)
    (Or.inl (htd₀.trans htd)) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv hab₀ hnh (fun e => by cases e) hD₁ b₁ hev
  refine ⟨st₁, v, T, ⟨b₂, st', hkr⟩, ?_, (Kept.of_kern hk₀ hme₀).trans hO.2⟩
  rw [runT_tl_indep t ht true st₀.tailNext]
  exact Out.of_kern hk₀ (Kern.rfl' _) hO.1

end Ochr.Meaning.Steps.Form.Master
