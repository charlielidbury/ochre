import OchrMeta.FrameOps

/-! # T1(a): ending two borrows commutes

[End ℓ] is the substitution `loan_ℓ := content` (plus clearing the holder), so two ends commute
as substitutions, given that the two borrows do not each lie inside the other's content
(W3, acyclicity).  In this machine [End] does not re-normalise sealed programs (outside a
refinement there is nothing to re-normalise: a sealed program produced by [Close] stays stuck),
so the equation holds on the nose. -/

namespace OchrMeta

theorem Val.substLoan_of_not_mem {l : Nat} {w : Val} :
    ∀ v : Val, l ∉ v.loans → Val.substLoan l w v = v := by
  intro v h
  induction v with
  | loan m =>
    simp only [Val.loans, List.mem_singleton] at h
    simp [Val.substLoan, Ne.symm h]
  | _ => simp_all [Val.substLoan, Val.loans]

/-- The substitution lemma behind T1(a). -/
theorem Val.substLoan_comm {l m : Nat} (hne : l ≠ m) {cl cm : Val}
    (hacyc : ¬ (l ∈ cm.loans ∧ m ∈ cl.loans)) :
    ∀ u : Val,
      Val.substLoan m (Val.substLoan l cl cm) (Val.substLoan l cl u) =
      Val.substLoan l (Val.substLoan m cm cl) (Val.substLoan m cm u) := by
  intro u
  induction u with
  | loan k =>
    by_cases hkl : k = l
    · subst hkl
      simp only [Val.substLoan, if_true, hne, if_false]
      by_cases hm : m ∈ cl.loans
      · have hl : k ∉ cm.loans := fun h => hacyc ⟨h, hm⟩
        rw [Val.substLoan_of_not_mem cm hl]
      · rw [Val.substLoan_of_not_mem cl hm, Val.substLoan_of_not_mem cl hm]
    · by_cases hkm : k = m
      · subst hkm
        simp only [Val.substLoan, if_true, hkl, if_false]
        by_cases hl : l ∈ cm.loans
        · have hm : k ∉ cl.loans := fun h => hacyc ⟨hl, h⟩
          rw [Val.substLoan_of_not_mem cl hm]
        · rw [Val.substLoan_of_not_mem cm hl, Val.substLoan_of_not_mem cm hl]
      · simp [Val.substLoan, hkl, hkm]
  | _ => simp_all [Val.substLoan]

theorem Val.clearB_comm (l m : Nat) (v : Val) : Val.clearB l (Val.clearB m v) = Val.clearB m (Val.clearB l v) := by
  cases v with
  | borrow k x =>
    by_cases hkl : k = l
    · subst hkl
      have h1 : Val.clearB k (Val.borrow k x) = .moved := by simp [Val.clearB, Val.isBorrowOf]
      rw [h1, Val.clearB_eq_self (v := .moved) (by simp [Val.isBorrowOf])]
      by_cases hkm : k = m
      · subst hkm; rw [h1]; exact Val.clearB_eq_self (by simp [Val.isBorrowOf])
      · have h2 : Val.clearB m (Val.borrow k x) = .borrow k x := Val.clearB_eq_self (by simp [Val.isBorrowOf, hkm])
        rw [h2, h1]
    · have h2 : Val.clearB l (Val.borrow k x) = .borrow k x := Val.clearB_eq_self (by simp [Val.isBorrowOf, hkl])
      rw [h2]
      by_cases hkm : k = m
      · subst hkm
        have h1 : Val.clearB k (Val.borrow k x) = .moved := by simp [Val.clearB, Val.isBorrowOf]
        rw [h1, Val.clearB_eq_self (v := .moved) (by simp [Val.isBorrowOf])]
      · have h3 : Val.clearB m (Val.borrow k x) = .borrow k x := Val.clearB_eq_self (by simp [Val.isBorrowOf, hkm])
        rw [h3, h2]
  | _ => simp [Val.clearB, Val.isBorrowOf]

theorem Val.clearB_substLoan {l m : Nat} {w : Val} (hw : w.isBorrowOf m = false) (v : Val) :
    Val.clearB m (Val.substLoan l w v) = Val.substLoan l w (Val.clearB m v) := by
  cases v with
  | loan k =>
    have e : Val.clearB m (Val.loan k) = Val.loan k := Val.clearB_eq_self (by simp [Val.isBorrowOf])
    rw [e]
    simp only [Val.substLoan]
    split
    · exact Val.clearB_eq_self hw
    · exact e
  | borrow k x =>
    by_cases h : k = m
    · subst h; simp [Val.clearB, Val.isBorrowOf, Val.substLoan]
    · simp [Val.clearB, Val.isBorrowOf, Val.substLoan, h]
  | _ => simp [Val.clearB, Val.isBorrowOf, Val.substLoan]

/-! ## Holders after an [End] -/

theorem Frame.holderContent_mapVals {m : Nat} {g h : Val → Val}
    (hg : ∀ v, (g v).isBorrowOf m = v.isBorrowOf m) (hb : ∀ x, g (.borrow m x) = .borrow m (h x)) :
    ∀ F : Frame, Frame.holderContent m (F.mapVals g) = (F.holderContent m).map h := by
  intro F
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    by_cases hv : v.isBorrowOf m = true
    · cases v with
      | borrow k x =>
        simp [Val.isBorrowOf] at hv; subst hv
        rw [hb]; simp [Frame.holderContent]
      | _ => simp [Val.isBorrowOf] at hv
    · have hgv : (g v).isBorrowOf m = false := by rw [hg]; simpa using hv
      have e1 : ∀ (u : Val) (G : Frame), u.isBorrowOf m = false →
          Frame.holderContent m ((y, u) :: G) = Frame.holderContent m G := by
        intro u G hu
        cases u with
        | borrow k x =>
          simp only [Val.isBorrowOf, beq_eq_false_iff_ne, ne_eq] at hu
          simp [Frame.holderContent, hu]
        | _ => rfl
      rw [e1 _ _ hgv, e1 _ _ (by simpa using hv), ih]

theorem Env.holderContent_mapVals {m : Nat} {g h : Val → Val}
    (hg : ∀ v, (g v).isBorrowOf m = v.isBorrowOf m) (hb : ∀ x, g (.borrow m x) = .borrow m (h x)) :
    ∀ Ω : Env, Env.holderContent m (Ω.mapVals g) = (Ω.holderContent m).map h := by
  intro Ω
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.mapVals, List.map_cons, Env.holderContent] at ih ⊢
    rw [ih, Frame.holderContent_mapVals hg hb]
    cases Frame.holderContent m F <;> simp

/-- The composite of clearing the holders of `l` and substituting `loan_l := cl`. -/
def endMap (l : Nat) (cl : Val) (v : Val) : Val := Val.substLoan l cl (Val.clearB l v)

theorem endMap_isBorrowOf {l m : Nat} (hne : l ≠ m) {cl : Val} (hcl : cl.nb = 0) (v : Val) :
    (endMap l cl v).isBorrowOf m = v.isBorrowOf m := by
  unfold endMap
  cases v with
  | borrow k x =>
    by_cases hk : k = l
    · subst hk
      have : Val.clearB k (Val.borrow k x) = .moved := by simp [Val.clearB, Val.isBorrowOf]
      rw [this]; simp [Val.substLoan, Val.isBorrowOf, hne]
    · rw [Val.clearB_eq_self (by simp [Val.isBorrowOf, hk])]; simp [Val.substLoan, Val.isBorrowOf]
  | loan k =>
    rw [Val.clearB_eq_self (by simp [Val.isBorrowOf])]
    simp only [Val.substLoan]
    split
    · rw [Val.not_isBorrowOf_of_nb hcl]; rfl
    · rfl
  | _ => simp [Val.clearB, Val.isBorrowOf, Val.substLoan]

theorem endBorrow_eq {l : Nat} {s : St} {cl : Val} (hl : s.env.holderContent l = some cl) :
    endBorrow l s = if cl.nb = 0 then some ⟨s.env.mapVals (endMap l cl), s.next⟩ else none := by
  unfold endBorrow endWith
  rw [hl]
  simp only
  split
  · simp [Env.substLoan, Env.clearHolder, Env.mapVals_mapVals, Function.comp_def]; rfl
  · rfl

/-- **T1(a).** Ending two distinct borrows commutes, provided neither lies inside the other's
content in both directions (acyclicity, W3).  On the nose: the machine's [End] is a plain
substitution. -/
theorem end_comm {l m : Nat} (hne : l ≠ m) {s : St} {cl cm : Val}
    (hl : s.env.holderContent l = some cl) (hm : s.env.holderContent m = some cm)
    (hacyc : ¬ (l ∈ cm.loans ∧ m ∈ cl.loans)) :
    (endBorrow l s).bind (endBorrow m) = (endBorrow m s).bind (endBorrow l) := by
  -- holders after one end
  have hml : ∀ (cl : Val), cl.nb = 0 → Env.holderContent m (s.env.mapVals (endMap l cl)) =
      some (Val.substLoan l cl cm) := by
    intro c hc
    rw [Env.holderContent_mapVals (h := Val.substLoan l c) (endMap_isBorrowOf hne hc)
      (fun x => by simp [endMap, Val.clearB, Val.isBorrowOf, Ne.symm hne, Val.substLoan]), hm]
    rfl
  have hlm : ∀ (cm : Val), cm.nb = 0 → Env.holderContent l (s.env.mapVals (endMap m cm)) =
      some (Val.substLoan m cm cl) := by
    intro c hc
    rw [Env.holderContent_mapVals (h := Val.substLoan m c) (endMap_isBorrowOf (Ne.symm hne) hc)
      (fun x => by simp [endMap, Val.clearB, Val.isBorrowOf, hne, Val.substLoan]), hl]
    rfl
  rw [endBorrow_eq hl, endBorrow_eq hm]
  by_cases hcl : cl.nb = 0 <;> by_cases hcm : cm.nb = 0
  · simp only [hcl, hcm, if_true, Option.bind_some]
    rw [endBorrow_eq (hml cl hcl), endBorrow_eq (hlm cm hcm)]
    simp only [Val.nb_substLoan l cl hcl, Val.nb_substLoan m cm hcm, hcl, hcm, if_true]
    simp only [Env.mapVals_mapVals, Option.some.injEq, St.mk.injEq, and_true]
    apply Env.mapVals_congr
    intro F _ b _
    simp only [Function.comp, endMap]
    have hclm : cl.isBorrowOf m = false := Val.not_isBorrowOf_of_nb hcl m
    have hcml : cm.isBorrowOf l = false := Val.not_isBorrowOf_of_nb hcm l
    rw [Val.clearB_substLoan hclm, Val.clearB_substLoan hcml, Val.clearB_comm m l]
    exact Val.substLoan_comm hne hacyc _
  · simp only [hcl, hcm, if_true, if_false, Option.bind_some, Option.bind_none]
    rw [endBorrow_eq (hml cl hcl)]
    simp [Val.nb_substLoan l cl hcl, hcm]
  · simp only [hcl, hcm, if_true, if_false, Option.bind_some, Option.bind_none]
    rw [endBorrow_eq (hlm cm hcm)]
    simp [Val.nb_substLoan m cm hcm, hcl]
  · simp [hcl, hcm]

end OchrMeta
