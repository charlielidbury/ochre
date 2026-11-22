import Ochr.Meaning.Steps.Machine.EvalInvT

/-!
# `PlaceInvD`, proved (machine10)

`Master.PlaceInvD` (`Steps/MasterPlace.lean`): `evalCore (m + 1)` of a direct place (no positional projection) is
the type part `placeTyPart m typed want p` at the state's wanted flag, then `readPlace m p`. `tick` touches only the
budget; `wanted` reads `wantHere`; `projIn` of a direct place is `none` and writes nothing (`runs_projIn_direct`);
the `.place` clause is `placeTyPart` followed by `readPlace` up to the monad laws; `readPlace 0` is out of fuel.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- `projIn` of a direct place finds no projection and writes nothing. -/
theorem runs_projIn_direct : ∀ {n : Nat} {p : Place}, p.Direct → ∀ {st st' : MState} {b : Nat}
    {o : Option (Place × Nat × (Place → Place))}, Runs (projIn n p) st b o st' → o = none ∧ st' = st := by
  intro n
  induction n with
  | zero => intro p _ st st' b o h; unfold projIn at h; simp only [runs_exhausted_iff] at h
  | succ k ih =>
    intro p hd st st' b o h
    cases p with
    | var i => exact runs_projIn_var h
    | deref q =>
      unfold projIn at h
      obtain ⟨o', s₁, b₁, hq, h₁⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := ih (p := q) hd hq
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
      exact ⟨rfl, rfl⟩
    | field g q =>
      unfold projIn at h
      obtain ⟨o', s₁, b₁, hq, h₁⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := ih (p := q) hd hq
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
      exact ⟨rfl, rfl⟩
    | proj i q => exact absurd hd id

theorem runs_readPlace_zero {p : Place} {st st' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.readPlace 0 p) st b v st') : False := by
  unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h

set_option maxHeartbeats 4000000 in
/-- **`PlaceInvD`, PROVED**. -/
theorem placeInvD : Master.PlaceInvD := by
  intro m typed p hint st st' bh v T? hd h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1
  rw [hw2] at h
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, hs₂⟩ := runs_projIn_direct hd hp
  rw [hs₂] at h₁
  have h₂ : Runs (Master.placeTyPart m typed st.wantHere p >>= fun T => Ochr.readPlace m p >>= fun v => pure (v, T))
      st b₃ (v, T?) st' := by
    cases typed <;> cases hwh : st.wantHere <;>
      simp only [hwh, Master.placeTyPart, bind_assoc, pure_bind, map_eq_pure_bind, if_true, if_false,
        Bool.false_eq_true] at h₁ ⊢ <;> exact h₁
  clear h₁
  obtain ⟨T, s₃, b₄, hpt, h₃⟩ := Runs.bind_inv h₂
  obtain ⟨v', s₄, b₅, hr, h₄⟩ := Runs.bind_inv h₃
  obtain ⟨he, rfl⟩ := runs_pure_inv h₄
  cases he
  cases m with
  | zero => exact (runs_readPlace_zero hr).elim
  | succ n => exact ⟨n, s₃, _, _, rfl, hpt, hr⟩

/-- **`stepPlace_direct` with its two inversions discharged** (`EvalInvDT`, `PlaceInvD`): ASSUMES 5 facts
(`PlaceTypeG`, `ReadInvD`, `BorrowReadWhole`, `AccessG`, `ReadOutG`). -/
theorem stepPlace_direct5 {K : RunCtx} {φ : Future} (hPT : Master.PlaceTypeG) (hRI : Master.ReadInvD)
    (hBW : Master.BorrowReadWhole) (hA : Master.AccessG) (hRO : Master.ReadOutG) :
    ∀ n, Master.IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (p : Place), p.Direct →
      Master.EvalSimK { K with Δ := Δ } ρ φ n (.place p)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.place p) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.place p)).isProof = false) :=
  Master.stepPlace_direct evalInvDT placeInvD hPT hRI hBW hA hRO

end Ochr.Meaning.Steps.Machine
