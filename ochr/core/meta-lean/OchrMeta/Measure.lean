import OchrMeta.Env

/-! # The termination measure of [Access]: ending a borrow removes one `borrow` constructor -/

namespace OchrMeta

theorem Val.nb_substLoan (l : Nat) (w : Val) (hw : w.nb = 0) :
    ∀ v : Val, (Val.substLoan l w v).nb = v.nb := by
  intro v
  induction v with
  | loan m => simp only [Val.substLoan]; split <;> simp_all [Val.nb]
  | _ => simp_all [Val.substLoan, Val.nb]

theorem Frame.nb_mapVals_substLoan (l : Nat) (w : Val) (hw : w.nb = 0) :
    ∀ F : Frame, (F.mapVals (Val.substLoan l w)).nb = F.nb := by
  intro F
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨x, v⟩ := b
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    simp only [Frame.nb, ih, Val.nb_substLoan l w hw]

theorem Env.nb_substLoan (l : Nat) (w : Val) (hw : w.nb = 0) :
    ∀ Ω : Env, (Ω.substLoan l w).nb = Ω.nb := by
  intro Ω
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.substLoan, Env.mapVals, List.map_cons] at ih ⊢
    simp only [Env.nb, ih, Frame.nb_mapVals_substLoan l w hw]


private theorem clearB_le (l : Nat) (v : Val) : (Val.clearB l v).nb ≤ v.nb := by
  unfold Val.clearB; split <;> simp [Val.nb]

theorem Val.clearB_eq_self {l : Nat} {v : Val} (h : v.isBorrowOf l = false) : Val.clearB l v = v := by
  simp [Val.clearB, h]

theorem Frame.nb_clear_le (l : Nat) :
    ∀ F : Frame, (F.mapVals (Val.clearB l)).nb ≤ F.nb := by
  intro F
  induction F with
  | nil => simp [Frame.mapVals, Frame.nb]
  | cons b F ih =>
    obtain ⟨x, v⟩ := b
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    simp only [Frame.nb]
    have := clearB_le l v
    omega

theorem Frame.nb_clear_lt (l : Nat) :
    ∀ (F : Frame) (w : Val), F.holderContent l = some w → (F.mapVals (Val.clearB l)).nb < F.nb := by
  intro F
  induction F with
  | nil => simp [Frame.holderContent]
  | cons b F ih =>
    intro w h
    obtain ⟨x, v⟩ := b
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    simp only [Frame.nb]
    cases v with
    | borrow m u =>
      simp only [Frame.holderContent] at h
      by_cases hm : m = l
      · subst hm
        have := Frame.nb_clear_le m F
        have hc : Val.clearB m (Val.borrow m u) = Val.moved := by simp [Val.clearB, Val.isBorrowOf]
        rw [hc]
        simp only [Frame.mapVals] at this
        simp only [Val.nb]
        omega
      · simp only [hm, if_false] at h
        have := ih w h
        have := clearB_le l (Val.borrow m u)
        omega
    | _ =>
      simp only [Frame.holderContent] at h
      have := ih w h
      rw [Val.clearB_eq_self (by simp [Val.isBorrowOf])]
      omega

theorem Env.nb_clear_lt (l : Nat) :
    ∀ (Ω : Env) (w : Val), Ω.holderContent l = some w → (Ω.clearHolder l).nb < Ω.nb := by
  intro Ω
  induction Ω with
  | nil => simp [Env.holderContent]
  | cons F Ω ih =>
    intro w h
    simp only [Env.clearHolder, Env.mapVals, List.map_cons] at ih ⊢
    simp only [Env.nb]
    simp only [Env.holderContent] at h
    cases hF : F.holderContent l with
    | some u =>
      have h1 := Frame.nb_clear_lt l F u hF
      have h2 : Env.nb (Env.mapVals (Val.clearB l) Ω) ≤ Env.nb Ω := by
        clear ih h hF h1
        induction Ω with
        | nil => simp [Env.mapVals, Env.nb]
        | cons G Ω ih2 =>
          simp only [Env.mapVals, List.map_cons] at ih2 ⊢
          simp only [Env.nb]
          have := Frame.nb_clear_le l G
          omega
      simp only [Env.mapVals] at h2
      omega
    | none =>
      simp only [hF, Option.none_or] at h
      have h1 := ih w h
      have := Frame.nb_clear_le l F
      omega

theorem endBorrow_nb_lt {l : Nat} {s s' : St} (h : endBorrow l s = some s') :
    s'.env.nb < s.env.nb := by
  unfold endBorrow at h
  split at h
  · cases h
  · rename_i w hw
    unfold endWith at h
    split at h
    · rename_i hw0
      cases h
      simp only
      rw [Env.nb_substLoan l w hw0]
      exact Env.nb_clear_lt l s.env w hw
    · cases h

end OchrMeta
