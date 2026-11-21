import Ochr.Meaning.Steps.FragMachine
import Ochr.Meaning.Steps.Machine.FormFacts

/-!
# The fragment's facts about the checker (machine lane; `Steps/FragMachine.lean`'s statements)

`DropLentFail` (in its restated form: the temporary is the only holder of the borrow): [Drop] of a
binding lent to the value in flight fails, `endLoansOfTopBind` finding the loan's borrow at a
temporary (D106).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- The first holder of a borrow is its only holder. -/
theorem findBorrow_unique {env : Env} {m : Nat} {q₀ : Pos} (hq : q₀ ∈ allPos env)
    (hh : (valAt env q₀).holdsBorrow m = true) (hu : ∀ q ∈ allPos env, (valAt env q).holdsBorrow m = true → q = q₀) :
    findBorrow env m = some q₀ := by
  unfold findBorrow
  cases hfind : (allPos env).find? (fun p => (valAt env p).holdsBorrow m) with
  | none => exact absurd (List.find?_eq_none.mp hfind q₀ hq) (by simp [hh])
  | some q =>
    have hq' := List.find?_some hfind
    rw [hu q (List.mem_of_find?_eq_some hfind) hq']

theorem runs_endLoansOfTopBind_lent {k f : Nat} {st st' : MState} {bh : Nat} {b : Binding} {m fT i : Nat}
    (hb : (st.env[f]!).binds.back? = some b) (hv : b.val = .loan m)
    (hfb : findBorrow st.env m = some (.temp fT i))
    (h : Runs (Ochr.endLoansOfTopBind k f) st bh () st') : False := by
  cases k with
  | zero => unfold Ochr.endLoansOfTopBind at h; simp only [runs_exhausted_iff] at h
  | succ j =>
    rw [Ochr.endLoansOfTopBind.eq_1] at h
    peel h
    rw [hb] at h
    peel h
    have hll : liveLoansIn st.env b.val = [m] := by
      simp [liveLoansIn, hv, Value.loans, liveLoan, hfb]
    rw [hll] at h
    peel h
    rw [hfb] at h
    simp only [runs_err_iff] at h

/-- **`DropLentFail`, proved**. -/
theorem dropLentFail : DropLentFail := by
  intro n st st' bh fr b m f i w hfr hb hv hq hy hu h
  have hfb : findBorrow st.env m = some (.temp f i) :=
    findBorrow_unique hq (by rw [hy]; simp [Value.holdsBorrow]) hu
  cases n with
  | zero => unfold Ochr.dropTopBind at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.dropTopBind.eq_1] at h
    obtain ⟨f0, s₁, b₁, hf, h₁⟩ := Runs.bind_inv h
    clear h
    obtain ⟨hf1, hs⟩ := runs_topIdx_inv hf
    clear hf
    subst hf1
    rw [hs] at h₁
    clear hs
    have hb' : (st.env[st.env.size - 1]!).binds.back? = some b := by
      rw [getElem!_def, hfr]; exact hb
    peel h₁
    rw [hb'] at h₁
    peel h₁
    split at h₁
    · simp only [runs_err_bind] at h₁
    · rw [hv] at h₁
      dsimp only at h₁
      obtain ⟨u, s₂, b₂, he, h₂⟩ := Runs.bind_inv h₁
      exact runs_endLoansOfTopBind_lent hb' hv hfb he

#print axioms dropLentFail

end Ochr.Meaning.Steps.Machine
