import Ochr.Meaning.Steps.Machine.EvalInv

/-!
# `evalCore`'s steps of the column, inverted (the machine lane)

Each fact here inverts one case of `Machine.evalCore` (unfolded with `unfold`, the prefix `tick`,
`curTail`, `wanted` peeled, then the case's own code stated by `change`: the definitional unfolding
of the `match` on a known term) into its sub-runs, with what lies between them: the kernel kept
(`Kern`), the mode kept (`ModeEq`), or a private computation's quiet exit (`Quiet`: a comparison,
D103, `quiet_conv`).

Statements in the proposed form (`…R`) differ from the lead's `FormMachine` where the lead's is not
provable from the checker's code alone (reported): see each docstring.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem runs_wanted_inv {st st' : MState} {b : Nat} {w : Bool} (h : Runs wanted st b w st') :
    w = st.wantHere ∧ st' = st := by
  unfold wanted at h
  peel h
  exact runs_pure_inv h

theorem Quiet.refl (st : MState) : Quiet st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_conv (n : Nat) (v w : Value) : GrowsM (Ochr.conv n v w) :=
  growsM_of_growsIn fun _ => (machineGrows n).conv v w

/-- **A comparison is quiet** (D103): `conv` puts back the state it started from, keeping only the
names made inside (`restoreNames`). -/
theorem quiet_conv {n : Nat} {v w : Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (Ochr.conv n v w) st b r st') : Quiet st st' := by
  have hg := Runs.grows (grows_conv _ _ _) h
  cases n with
  | zero => unfold Ochr.conv at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.conv.eq_1] at h
    obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
    clear h
    unfold restoreNames at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨-, rfl⟩ := runs_pure_inv h₂
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.nextLoan, ?_, ?_⟩
    · simp
    · intro σ hσ
      simp only [Array.getElem?_append_left hσ]

theorem quiet_expectTy {n : Nat} {w : String} {T : Option Value} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w T A) st b () st') : Quiet st st' := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.expectTy at h
    peel h
    split at h
    · obtain ⟨c, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
      have hq := quiet_conv hc
      split at h₂ <;> first
        | exact (runs_err_false h₂).elim
        | (obtain ⟨-, rfl⟩ := runs_pure_inv h₂; exact hq)
    · obtain ⟨-, rfl⟩ := runs_pure_inv h; exact Quiet.refl _

theorem quiet_modeEq_conv {n : Nat} {v w : Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (Ochr.conv n v w) st b r st') : ModeEq st st' := by
  cases n with
  | zero => unfold Ochr.conv at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.conv.eq_1] at h
    obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
    clear h
    unfold restoreNames at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨-, rfl⟩ := runs_pure_inv h₂
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem expectTy_inv {n : Nat} {w : String} {T : Option Value} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w T A) st b () st') : Quiet st st' ∧ ModeEq st st' := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.expectTy at h
    peel h
    split at h
    · obtain ⟨c, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
      have hq := quiet_conv hc
      have hm := quiet_modeEq_conv hc
      split at h₂ <;> first
        | exact (runs_err_false h₂).elim
        | (obtain ⟨-, rfl⟩ := runs_pure_inv h₂; exact ⟨hq, hm⟩)
    · obtain ⟨-, rfl⟩ := runs_pure_inv h; exact ⟨Quiet.refl _, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **`SuccInv` in the proposed form**: as the lead's, the typed clause stating the check of `u`'s
type as the checker runs it (`expectTy … T₀ …`, `T₀` the type `u`'s run returned) rather than
asserting `T₀ = some T` (a typed `eval` returns `some` for every term only by a whole-checker fact). -/
def SuccInvR : Prop :=
  ∀ (n : Nat) (typed : Bool) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    Mode st → st.tailNext = false → st.tailDecl = none →
    Runs (Ochr.evalCore (n + 1) typed (.succ u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat), Kern st st₀ ∧ Mode st₀ ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n typed u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      v = .succ v₀ ∧ T? = some .tNat ∧ Quiet st₁ st' ∧ ModeEq st₁ st' ∧ (∀ D, DecTab D st' → DecTab D st₁) ∧
      (typed = true → ∃ (st₂ : MState) (bh₂ : Nat),
        Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st')

set_option maxHeartbeats 4000000 in
theorem succInvR : SuccInvR := by
  intro n typed u hint st st' bh v T? hm htn htd h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨w, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨-, rfl⟩ := runs_wanted_inv hw
  change Runs (do
    let (v, T) ← Ochr.eval n typed u
    if typed then Ochr.expectTy n "the argument of S" T .tNat
    pure (Value.succ v, some Value.tNat)) _ _ _ _ at h
  obtain ⟨⟨v₀, T₀⟩, s₂, b₃, he, h₂⟩ := Runs.bind_inv h
  clear h
  cases typed with
  | false =>
    simp only [if_false, Bool.false_eq_true] at h₂
    peel h₂
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₂
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    exact ⟨_, _, v₀, T₀, _, Kern.rfl' _, hm, htn, htd, he, rfl, rfl, Quiet.refl _, ⟨rfl, rfl, rfl, rfl⟩,
      fun _ hd => hd, fun e => by cases e⟩
  | true =>
    simp only [if_true] at h₂
    obtain ⟨_, s₃, b₄, hx, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₃
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    obtain ⟨hq, hme⟩ := expectTy_inv hx
    exact ⟨_, _, v₀, T₀, _, Kern.rfl' _, hm, htn, htd, he, rfl, rfl, hq, hme,
      fun _ hd => DecTab.back hd (Runs.grows (grows_expectTy _ _ _ _) hx), fun _ => ⟨_, _, hx, Kern.rfl' _⟩⟩

end Ochr.Meaning.Steps.Machine
