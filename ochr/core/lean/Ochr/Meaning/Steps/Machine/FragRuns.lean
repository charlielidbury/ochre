import Ochr.Meaning.Steps.Machine.FragInv
import Ochr.Meaning.Steps.Machine.BorrowInv

/-!
# The fragment's inversion facts (machine lane; `Steps/FragMachine.lean`'s statements)

`EvalLow` (the evaluator below fuel 3 runs out of fuel), `VarBotInv` and `BorrowBotInv` (a read or a
borrow of a moved variable fails).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- `x` has no successful run. -/
def NoRun {α : Type} (x : M α) : Prop := ∀ s b a s', ¬ Runs x s b a s'

theorem NoRun.bind {α β : Type} {x : M α} {k : α → M β} (hx : NoRun x) : NoRun (x >>= k) := by
  intro s b a s' h
  obtain ⟨_, _, _, h1, -⟩ := Runs.bind_inv h
  exact hx _ _ _ _ h1

theorem NoRun.onFail {α : Type} {x : M α} {c : M Unit} (hx : NoRun x) : NoRun (Ochr.onFail x c) :=
  fun _ _ _ _ h => hx _ _ _ _ (Runs.onFail_inv h)

theorem NoRun.privately {α : Type} {x : M α} (hx : NoRun x) : NoRun (Ochr.privately x) := by
  intro s b a s' h
  have e : Ochr.privately x = (do
      let saved ← get
      modify fun s => { s with privateDepth := s.privateDepth + 1 }
      let r ← Ochr.onFail x (restoreKeep saved)
      restoreKeep saved
      pure r) := rfl
  rw [e, runs_get_bind, runs_modify_bind] at h
  exact (NoRun.onFail hx).bind _ _ _ _ h

theorem NoRun.withErased {α : Type} {x : M α} (hx : NoRun x) : NoRun (Ochr.withErased x) := by
  intro s b a s' h
  unfold Ochr.withErased at h
  rw [runs_modify_bind] at h
  exact (NoRun.onFail hx).bind _ _ _ _ h

theorem noRun_evalCore_zero (typed : Bool) (t : Term) (hint : Option Value) : NoRun (Ochr.evalCore 0 typed t hint) := by
  intro s b a s' h
  unfold Ochr.evalCore at h
  exact runs_exhausted_iff.mp h

theorem noRun_evalAt_zero (typed : Bool) (t : Term) (hint : Option Value) : NoRun (Ochr.evalAt 0 typed t hint) := by
  intro s b a s' h
  unfold Ochr.evalAt at h
  exact runs_exhausted_iff.mp h

theorem NoRun.bind_right {α β : Type} {x : M α} {k : α → M β} (hk : ∀ a, NoRun (k a)) : NoRun (x >>= k) := by
  intro s b a s' h
  obtain ⟨a', _, _, -, h2⟩ := Runs.bind_inv h
  exact hk a' _ _ _ _ h2


theorem NoRun.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : NoRun x) (hy : NoRun y) :
    NoRun (if c then x else y) := by
  by_cases h : c
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact hy

set_option maxHeartbeats 4000000 in
theorem noRun_evalAt_one (typed : Bool) (t : Term) (hint : Option Value) : NoRun (Ochr.evalAt 1 typed t hint) := by
  unfold Ochr.evalAt
  repeat (any_goals (first
    | (apply NoRun.bind; apply NoRun.onFail; apply NoRun.ite
       · exact (NoRun.privately (NoRun.withErased (noRun_evalCore_zero _ _ _).bind)).bind
       · exact noRun_evalCore_zero _ _ _)
    | (apply NoRun.bind_right; intro _)
    | (apply NoRun.ite)
    | (dsimp only)
    | split))

theorem noRun_eval_low (m : Nat) (hm : m < 3) (typed : Bool) (t : Term) (hint : Option Value) :
    NoRun (Ochr.eval m typed t hint) := by
  intro s b a s' h
  match m, hm with
  | 0, _ => unfold Ochr.eval at h; exact runs_exhausted_iff.mp h
  | 1, _ =>
    rw [Ochr.eval.eq_1] at h
    obtain ⟨_, _, _, -, h, -⟩ := Runs.located_inv h
    obtain ⟨_, h⟩ := Runs.noteValue_inv h
    exact noRun_evalAt_zero _ _ _ _ _ _ _ h
  | 2, _ =>
    rw [Ochr.eval.eq_1] at h
    obtain ⟨_, _, _, -, h, -⟩ := Runs.located_inv h
    obtain ⟨_, h⟩ := Runs.noteValue_inv h
    exact noRun_evalAt_one _ _ _ _ _ _ _ h

theorem evalLow : EvalLow := fun m typed t hint st st' bh r hm _ h => noRun_eval_low m hm typed t hint st bh r st' h

/-! ## A variable holding `⊥` -/

section BotVar
variable {i f j : Nat} {st : MState}

theorem runs_content_at {w : Value} {st' : MState} {b : Nat} {v : Value}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = w)
    (h : Runs (content (.var i)) st b v st') : v = w ∧ st' = st := by
  unfold content at h
  obtain ⟨pos, s₁, b₁, hvp, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hvp
  rw [hpos] at hp; cases hp
  obtain ⟨w', s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := Steps.runs_getAt_inv hg
  simp only [Place.steps, Value.follow] at h₂
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨hv, rfl⟩

theorem runs_repackAt_bot {n : Nat} {T : Value} {w : String} {st' : MState} {b : Nat}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = .bot)
    (h : Runs (repackAt n (.var i) T w) st b () st') : st' = st := by
  cases n with
  | zero => unfold repackAt at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold repackAt at h
    obtain ⟨o, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, pos, hp, rfl⟩ := runs_content?_inv hc
    simp only [Place.steps] at hp
    rw [hpos] at hp; cases hp
    simp only [Place.steps, Value.follow, hv] at h₁
    exact (runs_pure_inv h₁).2

theorem runs_accessPath_bot {n : Nat} {st' : MState} {b : Nat} {u : Unit}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = .bot)
    (h : Runs (accessPath n (.var i)) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hvp, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, hp⟩ := runs_varPos_inv hvp
    rw [hpos] at hp; cases hp
    rw [hv, show firstLiveLoanOnPath s₁.env .bot [] = none by simp [firstLiveLoanOnPath]] at h₁
    exact (runs_pure_inv h₁).2

theorem runs_accessInside_bot {n : Nat} {o : Bool} {st' : MState} {b : Nat} {u : Unit}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = .bot)
    (h : Runs (accessInside n (.var i) o) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessInside at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessInside at h
    obtain ⟨v, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_content_at hpos hv hc
    have h1 : ∀ E, liveOwnedLoansIn E .bot = [] := fun E => rfl
    have h2 : ∀ E, liveLoansIn E .bot = [] := fun E => liveLoansIn_nil rfl
    cases o <;> (peel h₁; simp only [h1, h2, Bool.false_eq_true, if_false, if_true, ↓reduceIte, List.isEmpty_nil] at h₁; peel h₁; exact (runs_pure_inv h₁).2)

theorem noRun_readPlace_bot {n : Nat} (hpos : ckVarPos st.env i = some (.bind f j))
    (hv : valAt st.env (.bind f j) = .bot) {b : Nat} {v : Value} {st' : MState} :
    ¬ Runs (Ochr.readPlace n (.var i)) st b v st' := by
  intro h
  cases n with
  | zero => unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.readPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    have := runs_accessPath_bot hpos hv ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    have := runs_accessInside_bot hpos hv hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := runs_content_at hpos hv hc
    peel h₃
    rw [show Value.bot.outerLoans = [] from rfl] at h₃
    simp only [List.any_nil, Bool.false_eq_true, if_false] at h₃
    peel h₃
    obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
    peel h₄
    split at h₄ <;> (peel h₄; obtain ⟨_, _, _, -, h₅⟩ := Runs.bind_inv h₄; exact runs_err_iff.mp h₅)

theorem noRun_borrowPlace_bot {n : Nat} (hpos : ckVarPos st.env i = some (.bind f j))
    (hv : valAt st.env (.bind f j) = .bot) {b : Nat} {v : Value} {st' : MState} :
    ¬ Runs (Ochr.borrowPlace n (.var i)) st b v st' := by
  intro h
  cases n with
  | zero => unfold Ochr.borrowPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.borrowPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    have := runs_accessPath_bot hpos hv ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    have := runs_accessInside_bot hpos hv hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := runs_content_at hpos hv hc
    obtain ⟨_, _, _, -, h₄⟩ := Runs.bind_inv h₃
    exact runs_err_iff.mp h₄

end BotVar

set_option maxHeartbeats 4000000 in
theorem varBotInv : VarBotInv := by
  intro n typed i hint st st' bh v T? f j bd hpos hb hbot hty h
  have hv : valAt st.env (.bind f j) = .bot := by
    show (st.env[f]!).binds[j]!.val = _; rw [binds_get! hb]; exact hbot
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
    obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hty hpt'
    try simp only [if_true] at h₂
    obtain ⟨_, s₄, b₅, hra, h₃⟩ := Runs.bind_inv h₂
    have := runs_repackAt_bot hpos hv hra
    subst this
    obtain ⟨w, s₅, b₆, hrp, -⟩ := Runs.bind_inv h₃
    exact noRun_readPlace_bot hpos hv hrp
  | false =>
    simp only [Bool.false_eq_true, if_false] at h₁
    split at h₁
    · obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hpos hb hty hpt
      try simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
      obtain ⟨w, s₅, b₆, hrp, -⟩ := Runs.bind_inv h₂
      exact noRun_readPlace_bot hpos hv hrp
    · try simp only [pure_bind, Bool.false_eq_true, if_false] at h₁
      obtain ⟨w, s₅, b₆, hrp, -⟩ := Runs.bind_inv h₁
      exact noRun_readPlace_bot hpos hv hrp

set_option maxHeartbeats 4000000 in
theorem borrowBotInv : BorrowBotInv := by
  intro n i hint st st' bh v T? f j bd hpos hb hbot hty h
  have hv : valAt st.env (.bind f j) = .bot := by
    show (st.env[f]!).binds[j]!.val = _; rw [binds_get! hb]; exact hbot
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
  simp only [if_true] at h₁
  obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  obtain ⟨T'', hpt', rfl⟩ := Runs.map_inv hpt
  obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hty hpt'
  simp only [Value.typeHasRef, Bool.false_eq_true, if_false] at h₂
  obtain ⟨c, s₄, b₅, hib, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_isBorrowable _ _) hib
  subst this
  split at h₃
  · obtain ⟨_, s₅, b₆, hpp, h₄⟩ := Runs.bind_inv h₃
    exact absurd h₄ (fun h => by simp only [runs_err_bind] at h)
  · obtain ⟨_, s₅, b₆, hra, h₄⟩ := Runs.bind_inv h₃
    have := runs_repackAt_bot hpos hv hra
    subst this
    obtain ⟨bv, s₆, b₇, hbp, -⟩ := Runs.bind_inv h₄
    exact noRun_borrowPlace_bot hpos hv hbp

end Ochr.Meaning.Steps.Machine
