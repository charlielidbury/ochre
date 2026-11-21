import Ochr.Meaning.Steps.Machine.ReadInv

/-!
# The borrow column's `&x` of a variable holding a number (`BorrowNumInv`), proved

`evalCore` of a typed `.borrow (.var i)` where the variable holds a number stored at `Nat`: the type
read (`placeType`), the D66 test (`isBorrowable`, a decision that keeps the state), [Repack] of a
number (nothing), `borrowPlace` (the accesses end nothing at a number, `logEffect`, a fresh label,
`loan_l` written at the variable: `runs_borrowPlace_num`), and D112's `openWrite`, which writes
nothing at a root (`Place.fieldPrefixes (.var i) = []`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem keep_isBorrowable (n : Nat) (T : Value) : Keep (isBorrowable n T) := by
  unfold isBorrowable sortOf?; keep_go
  all_goals first
    | exact (decideKeep _).2.2.2.2.2.2.1 _
    | exact keep_sealedSort _

theorem runs_freshLoan_inv {st st' : MState} {b : Nat} {l : Nat} (h : Runs freshLoan st b l st') :
    l = st.nextLoan ∧ st' = { st with nextLoan := st.nextLoan + 1 } := by
  unfold freshLoan at h
  peel h
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h
  exact ⟨rfl, rfl⟩

theorem runs_openWrite_var {n i : Nat} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (openWrite n (.var i)) st b u st') : st' = st := by
  cases n with
  | zero => unfold openWrite at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold openWrite at h
    simp only [Place.fieldPrefixes, List.forIn_nil] at h
    exact (runs_pure_inv h).2

theorem runs_borrowPlace_num {n i f j : Nat} {bd : Binding} {st st' : MState} {b : Nat} {v : Value}
    (hn : NumAt st i f j bd) (h : Runs (Ochr.borrowPlace n (.var i)) st b v st') :
    v = .borrow st.nextLoan bd.val ∧
      ∃ X, st' = { st with env := Env.setAtE st.env (.bind f j) (.loan st.nextLoan), nextLoan := st.nextLoan + 1, placeLog := X } := by
  cases n with
  | zero => unfold Ochr.borrowPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.borrowPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    clear h
    have := runs_accessPath_num hn ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    have := runs_accessInside_num hn hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    obtain ⟨rfl, rfl⟩ := runs_content_var hn hc
    have hnum := hn.num
    have hx : ∀ x : Value, x.Num → x = .zero ∨ ∃ w, x = .succ w := fun x hx => by
      cases hx with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨_, rfl⟩
    have hh : ∀ x, bd.val = x → x.hasHole = false := fun x ex => ex ▸ Value.Num.hasHole hnum
    rcases hx _ hnum with e | ⟨w', e⟩ <;> rw [e] at h₃ <;> simp only [] at h₃ <;> rw [hh _ e] at h₃ <;>
      simp only [Bool.false_eq_true, if_false] at h₃ <;>
      (obtain ⟨X, s₄, b₄, hle, h₄⟩ := Runs.bind_inv h₃
       obtain ⟨X, rfl⟩ := runs_logEffect_inv hle
       obtain ⟨l, s₅, b₅, hfl, h₅⟩ := Runs.bind_inv h₄
       obtain ⟨rfl, rfl⟩ := runs_freshLoan_inv hfl
       obtain ⟨_, s₆, b₆, hsp, h₆⟩ := Runs.bind_inv h₅
       obtain ⟨pos, v', hp, hu', rfl⟩ := runs_setPlace_inv hsp
       simp only [Place.steps] at hp hu'
       rw [hn.pos] at hp; cases hp
       simp only [Value.updAt, Option.some.injEq] at hu'
       subst hu'
       obtain ⟨rfl, rfl⟩ := runs_pure_inv h₆
       exact ⟨by rw [e], X, rfl⟩)
set_option maxHeartbeats 4000000 in
theorem borrowNumInv : BorrowNumInv := by
  intro n i hint st st' bh v T? f j bd D hm hpos hb hnum hty hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  have hn : NumAt s₁ i f j bd := ⟨hpos, hb, hnum⟩
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
    have := runs_repackAt_num hn hra
    subst this
    obtain ⟨bv, s₆, b₇, hbp, h₅⟩ := Runs.bind_inv h₄
    obtain ⟨rfl, X, rfl⟩ := runs_borrowPlace_num hn hbp
    obtain ⟨_, s₇, b₈, how, h₆⟩ := Runs.bind_inv h₅
    have := runs_openWrite_var how
    subst this
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₆
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    exact ⟨⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s₅, Quiet.refl _, fun _ _ h => h, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Ochr.Meaning.Steps.Machine
