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

/-! ## `VarBotInv`: the read of a moved variable fails -/

section Bot
variable {i f j : Nat} {st : MState} (hpos : ckVarPos st.env i = some (.bind f j)) (hx : valAt st.env (.bind f j) = .bot)
include hpos hx

theorem runs_content_bot {st' : MState} {b : Nat} {v : Value} (h : Runs (content (.var i)) st b v st') :
    v = .bot ∧ st' = st := by
  unfold content at h
  obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
  rw [hpos] at hp; cases hp
  obtain ⟨w, s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := Steps.runs_getAt_inv hg
  simp only [Place.steps, Value.follow] at h₂
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨hx, rfl⟩

theorem runs_accessPath_bot {n : Nat} {st' : MState} {b : Nat} {u : Unit}
    (h : Runs (accessPath n (.var i)) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
    rw [hpos] at hp; cases hp
    rw [hx] at h₁
    simp only [firstLiveLoanOnPath] at h₁
    exact (runs_pure_inv h₁).2

theorem runs_accessInside_bot {n : Nat} {o : Bool} {st' : MState} {b : Nat} {u : Unit}
    (h : Runs (accessInside n (.var i) o) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessInside at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessInside at h
    obtain ⟨v, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_content_bot hpos hx hc
    have h1 : liveOwnedLoansIn s₁.env .bot = [] := by first | rfl | simp [liveOwnedLoansIn, Value.ownedLoans] | (unfold liveOwnedLoansIn; rfl)
    have h2 : liveLoansIn s₁.env .bot = [] := by first | rfl | simp [liveLoansIn, Value.loans]
    cases o <;> (peel h₁; simp only [h1, h2, Bool.false_eq_true, if_false, if_true, List.isEmpty_nil] at h₁; peel h₁; exact (runs_pure_inv h₁).2)

theorem runs_readPlace_bot {n : Nat} {st' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.readPlace n (.var i)) st b v st') : False := by
  cases n with
  | zero => unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.readPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    clear h
    have := runs_accessPath_bot hpos hx ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    have := runs_accessInside_bot hpos hx hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    obtain ⟨rfl, rfl⟩ := runs_content_bot hpos hx hc
    peel h₃
    simp only [Value.outerLoans, List.any_nil, Bool.false_eq_true, if_false] at h₃
    peel h₃
    obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
    clear h₃
    peel h₄
    peel h₄
    split at h₄
    · peel h₄
      obtain ⟨_, _, _, _, he⟩ := Runs.bind_inv h₄
      simp only [runs_err_iff] at he
    · obtain ⟨_, _, _, _, he⟩ := Runs.bind_inv h₄
      simp only [runs_err_iff] at he

theorem runs_repackAt_bot {n : Nat} {T : Value} {w : String} {st' : MState} {b : Nat}
    (h : Runs (repackAt n (.var i) T w) st b () st') : st' = st := by
  cases n with
  | zero => unfold repackAt at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold repackAt at h
    obtain ⟨o, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, pos, hp, rfl⟩ := runs_content?_inv hc
    simp only [Place.steps] at hp
    rw [hpos] at hp; cases hp
    simp only [Place.steps, Value.follow, hx] at h₁
    exact (runs_pure_inv h₁).2

end Bot

set_option maxHeartbeats 4000000 in
/-- **`VarBotInv`, proved**: every branch of `.place` reaches `readPlace` with the state unchanged
(`placeType`, `placeType?` read; the typed [Repack] returns at `⊥`), and `readPlace` of `⊥` errs. -/
theorem varBotInv : VarBotInv := by
  intro n typed i hint st st' bh v T? f j b hpos hb hv hT h
  have hx : valAt st.env (.bind f j) = .bot := by
    show (st.env[f]!).binds[j]!.val = _; rw [binds_get! hb, hv]
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
  simp only at h₁
  cases typed with
  | true =>
    simp only [if_true] at h₁
    obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    obtain ⟨T'', hpt', rfl⟩ := Runs.map_inv hpt
    obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hT hpt'
    try simp only [if_true] at h₂
    obtain ⟨_, s₄, b₅, hra, h₃⟩ := Runs.bind_inv h₂
    have := runs_repackAt_bot hpos hx hra
    subst this
    obtain ⟨_, _, _, hrp, -⟩ := Runs.bind_inv h₃
    exact runs_readPlace_bot hpos hx hrp
  | false =>
    simp only [Bool.false_eq_true, if_false] at h₁
    split at h₁
    · obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hpos hb hT hpt
      try simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
      obtain ⟨_, _, _, hrp, -⟩ := Runs.bind_inv h₂
      exact runs_readPlace_bot hpos hx hrp
    · try simp only [pure_bind, Bool.false_eq_true, if_false] at h₁
      obtain ⟨_, _, _, hrp, -⟩ := Runs.bind_inv h₁
      exact runs_readPlace_bot hpos hx hrp

#print axioms varBotInv

#print axioms dropLentFail

end Ochr.Meaning.Steps.Machine
