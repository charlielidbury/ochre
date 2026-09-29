import OchrMeta.WFCore

/-! # Lemma 0, part 2: reading and writing a value at a path -/

namespace OchrMeta

theorem Proj.step_nb {pr : Proj} {v w : Val} (h : pr.step v = .ok w) : w.nb ≤ v.nb := by
  cases pr <;> cases v <;> simp_all [Proj.step, Val.isNeutral, Val.nb] <;> (subst h; omega)

/-- One projection step, written back. -/
theorem Proj.put_spec {pr : Proj} {v w w' v' : Val} (h1 : pr.step v = .ok w) (h2 : pr.put v w' = some v') :
    (∀ m ∈ v'.loans, m ∈ v.loans ∨ m ∈ w'.loans) ∧ (∀ m ∈ v.loans, m ∈ w.loans ∨ m ∈ v'.loans) ∧
    (∀ m ∈ w'.loans, m ∈ v'.loans) ∧ (v.nb = 0 → w'.nb = 0 → v'.nb = 0) ∧ v'.hd = v.hd ∧
    (∀ p ∈ v'.hp, ∃ p0 ∈ v.hp, p.1 = p0.1 ∧ p0.2 = w ∧ p.2 = w') := by
  cases pr <;> cases v <;> simp [Proj.step, Proj.put, Val.isNeutral] at h1 h2 <;>
    (subst h1; subst h2; simp [Val.loans, Val.nb, Val.hd, Val.hp]) <;> grind

theorem Val.get_cons {v : Val} {pr : Proj} {ps : List Proj} {c : Val} (h : v.get (pr :: ps) = some c) :
    ∃ w, pr.step v = .ok w ∧ w.get ps = some c := by
  simp only [Val.get] at h
  cases hs : pr.step v with
  | ok w => rw [hs] at h; exact ⟨w, rfl, h⟩
  | _ => rw [hs] at h; cases h

theorem Val.set_cons {v : Val} {pr : Proj} {ps : List Proj} {new v' : Val}
    (h : v.set (pr :: ps) new = some v') :
    ∃ w w', pr.step v = .ok w ∧ w.set ps new = some w' ∧ pr.put v w' = some v' := by
  simp only [Val.set] at h
  cases hs : pr.step v with
  | ok w =>
    rw [hs] at h
    simp only at h
    cases hw : w.set ps new with
    | none => rw [hw] at h; cases h
    | some w' => rw [hw] at h; exact ⟨w, w', rfl, hw, h⟩
  | _ => rw [hs] at h; cases h

theorem Val.get_loans : ∀ (π : List Proj) {v c : Val}, v.get π = some c → ∀ m ∈ c.loans, m ∈ v.loans := by
  intro π
  induction π with
  | nil => intro v c h; simp [Val.get] at h; subst h; exact fun _ h => h
  | cons pr ps ih =>
    intro v c h m hm
    obtain ⟨w, hs, hg⟩ := Val.get_cons h
    exact Proj.step_loans hs m (ih hg m hm)

theorem Val.get_names : ∀ (π : List Proj) {v c : Val}, v.get π = some c → ∀ m ∈ c.names, m ∈ v.names := by
  intro π
  induction π with
  | nil => intro v c h; simp [Val.get] at h; subst h; exact fun _ h => h
  | cons pr ps ih =>
    intro v c h m hm
    obtain ⟨w, hs, hg⟩ := Val.get_cons h
    exact Proj.step_names hs m (ih hg m hm)

theorem Val.get_nb : ∀ (π : List Proj) {v c : Val}, v.get π = some c → c.nb ≤ v.nb := by
  intro π
  induction π with
  | nil => intro v c h; simp [Val.get] at h; subst h; exact Nat.le_refl _
  | cons pr ps ih =>
    intro v c h
    obtain ⟨w, hs, hg⟩ := Val.get_cons h
    exact Nat.le_trans (ih hg) (Proj.step_nb hs)

theorem Val.get_nil {v c : Val} (h : v.get [] = some c) : c = v := by
  simp [Val.get] at h; exact h.symm

/-- No borrows inside data: only the whole of a binding can be a borrow. -/
theorem Val.get_sh {π : List Proj} {v c : Val} (hv : v.Sh) (h : v.get π = some c) : π = [] ∨ c.nb = 0 := by
  cases π with
  | nil => exact Or.inl rfl
  | cons pr ps =>
    right
    rcases hv with hv | ⟨l, d, rfl, hd⟩
    · have := Val.get_nb _ h; omega
    · obtain ⟨w, hs, hg⟩ := Val.get_cons h
      cases pr <;> simp [Proj.step, Val.isNeutral] at hs
      subst hs
      have := Val.get_nb _ hg; omega

theorem Val.set_nil {v new v' : Val} (h : v.set [] new = some v') : v' = new := by
  simp [Val.set] at h; exact h.symm

theorem Val.set_spec : ∀ (π : List Proj) {v new v' : Val}, v.set π new = some v' →
    (∀ m ∈ v'.loans, m ∈ v.loans ∨ m ∈ new.loans) ∧ (∀ m ∈ new.loans, m ∈ v'.loans) ∧
    (v.nb = 0 → new.nb = 0 → v'.nb = 0) := by
  intro π
  induction π with
  | nil => intro v new v' h; rw [Val.set_nil h]; exact ⟨fun _ h => Or.inr h, fun _ h => h, fun _ h => h⟩
  | cons pr ps ih =>
    intro v new v' h
    obtain ⟨w, w', hs, hw, hp⟩ := Val.set_cons h
    obtain ⟨p1, _, p3, p4, _⟩ := Proj.put_spec hs hp
    obtain ⟨i1, i2, i3⟩ := ih hw
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rcases p1 m hm with h | h
      · exact Or.inl h
      · rcases i1 m h with h | h
        · exact Or.inl (Proj.step_loans hs m h)
        · exact Or.inr h
    · exact fun m hm => p3 m (i2 m hm)
    · intro hv hn
      exact p4 hv (i3 (by have := Proj.step_nb hs; omega) hn)

theorem Val.set_keep : ∀ (π : List Proj) {v new v' c : Val}, v.set π new = some v' → v.get π = some c →
    ∀ m ∈ v.loans, m ∈ c.loans ∨ m ∈ v'.loans := by
  intro π
  induction π with
  | nil => intro v new v' c _ hg; rw [Val.get_nil hg]; exact fun _ h => Or.inl h
  | cons pr ps ih =>
    intro v new v' c h hg m hm
    obtain ⟨w, w', hs, hw, hp⟩ := Val.set_cons h
    obtain ⟨w2, hs2, hg2⟩ := Val.get_cons hg
    rw [hs] at hs2; cases hs2
    obtain ⟨_, p2, p3, _⟩ := Proj.put_spec hs hp
    rcases p2 m hm with h | h
    · rcases ih hw hg2 m h with h | h
      · exact Or.inl h
      · exact Or.inr (p3 m h)
    · exact Or.inr h

theorem Val.set_hd_cons {pr : Proj} {ps : List Proj} {v new v' : Val} (h : v.set (pr :: ps) new = some v') :
    v'.hd = v.hd := by
  obtain ⟨w, w', hs, _, hp⟩ := Val.set_cons h
  exact (Proj.put_spec hs hp).2.2.2.2.1

theorem Val.set_hp_cons {pr : Proj} {ps : List Proj} {v new v' : Val} (h : v.set (pr :: ps) new = some v') :
    ∀ p ∈ v'.hp, ∃ p0 ∈ v.hp, p.1 = p0.1 ∧ ∀ m ∈ p.2.loans, m ∈ p0.2.loans ∨ m ∈ new.loans := by
  obtain ⟨w, w', hs, hw, hp⟩ := Val.set_cons h
  intro p hpp
  obtain ⟨p0, hp0, e1, e2, e3⟩ := (Proj.put_spec hs hp).2.2.2.2.2 p hpp
  refine ⟨p0, hp0, e1, ?_⟩
  rw [e3, e2]
  exact (Val.set_spec ps hw).1

theorem Val.set_sh {π : List Proj} {v new v' : Val} (hv : v.Sh) (hn : new.nb = 0)
    (h : v.set π new = some v') : v'.Sh := by
  cases π with
  | nil => rw [Val.set_nil h]; exact Val.sh_of_nb hn
  | cons pr ps =>
    rcases hv with hv | ⟨l, d, rfl, hd⟩
    · exact Val.sh_of_nb ((Val.set_spec _ h).2.2 hv hn)
    · obtain ⟨w, w', hs, hw, hp⟩ := Val.set_cons h
      cases pr <;> simp [Proj.step, Val.isNeutral] at hs
      subst hs
      simp [Proj.put] at hp
      subst hp
      exact Or.inr ⟨l, w', rfl, (Val.set_spec ps hw).2.2 hd hn⟩

namespace Inv
variable {R : Bs} {V : List Val} {n : Nat}

/-- Overwriting a loan-free part of a binding (below its top) by a loan-free, borrow-free
value. -/
theorem set_clean {x : Var} {b c new b' : Val} {π : List Proj} (h : Inv ((x, b) :: R) V n)
    (hg : b.get π = some c) (hs : b.set π new = some b') (hπ : π ≠ []) (hc : c.loans = [])
    (hl : new.loans = []) (hn : new.nb = 0) : Inv ((x, b') :: R) V n := by
  obtain ⟨pr, ps, rfl⟩ : ∃ pr ps, π = pr :: ps := by cases π with
    | nil => exact absurd rfl hπ
    | cons pr ps => exact ⟨pr, ps, rfl⟩
  have hhd := Val.set_hd_cons hs
  have hHE : HE ((x, b') :: R) = HE ((x, b) :: R) := by simp [hhd]
  obtain ⟨s1, _, _⟩ := Val.set_spec _ hs
  have s1' : ∀ m ∈ b'.loans, m ∈ b.loans := fun m hm => by simpa [hl] using s1 m hm
  refine ⟨?_, h.freshV, ?_, h.shV, ?_, ?_, ?_, h.clean, ?_, ?_⟩
  · intro b0 hb0 m hm
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · rcases Val.names_set _ b new b' hs m hm with h1 | h1
      · exact h.fresh _ List.mem_cons_self m h1
      · simp [Val.names_nil hn hl] at h1
    · exact h.fresh b0 (List.mem_cons_of_mem _ hb0) m hm
  · intro b0 hb0
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · exact Val.set_sh (h.sh _ List.mem_cons_self) hn hs
    · exact h.sh b0 (List.mem_cons_of_mem _ hb0)
  · rw [hHE]; exact h.uniq
  · intro b0 hb0 m hm
    rw [hHE]
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · exact h.live _ List.mem_cons_self m (s1' m hm)
    · exact h.live b0 (List.mem_cons_of_mem _ hb0) m hm
  · intro m hm
    rw [hHE] at hm
    obtain ⟨b0, hb0, hmb⟩ := h.owned m hm
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · rcases Val.set_keep _ hs hg m hmb with h1 | h1
      · simp [hc] at h1
      · exact ⟨_, List.mem_cons_self, h1⟩
    · exact ⟨b0, List.mem_cons_of_mem _ hb0, hmb⟩
  · intro b0 hb0 p hp m hm
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · obtain ⟨p0, hp0, e1, hl0⟩ := Val.set_hp_cons hs p hp
      rw [e1]
      rcases hl0 m hm with h1 | h1
      · exact h.acyc _ List.mem_cons_self p0 hp0 m h1
      · simp [hl] at h1
    · exact h.acyc b0 (List.mem_cons_of_mem _ hb0) p hp m hm
  · intro b0 hb0 ht
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · have := h.tmps _ List.mem_cons_self ht
      simp only at this ⊢
      exact List.eq_nil_iff_forall_not_mem.mpr fun m hm => by simpa [this] using s1' m hm
    · exact h.tmps b0 (List.mem_cons_of_mem _ hb0) ht

/-- [Borrow]: the place (loan-free, borrow-free content `c`) receives the fresh `loan_n`, and
`borrow_n c` is put in flight. -/
theorem set_loan {x : Var} {b c b' : Val} {π : List Proj} (h : Inv ((x, b) :: R) [] n)
    (hg : b.get π = some c) (hs : b.set π (.loan n) = some b') (hcn : c.nb = 0) (hc : c.loans = [])
    (hx : ∀ i, x ≠ .tmp i) : Inv ((x, b') :: R) [.borrow n c] (n + 1) := by
  have hhd : b'.hd = b.hd := by
    cases π with
    | nil => rw [Val.set_nil hs, ← Val.get_nil hg, Val.hd_of_nb hcn]; rfl
    | cons pr ps => exact Val.set_hd_cons hs
  have hHE : HE ((x, b') :: R) = HE ((x, b) :: R) := by simp [hhd]
  obtain ⟨s1, s2, _⟩ := Val.set_spec _ hs
  have s1' : ∀ m ∈ b'.loans, m ∈ b.loans ∨ m = n := fun m hm => by simpa [Val.loans] using s1 m hm
  have hHn : ∀ m ∈ HE ((x, b) :: R), m < n := by
    intro m hm
    obtain ⟨b0, hb0, hm0⟩ := HE_names hm
    exact h.fresh b0 hb0 m hm0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b0 hb0 m hm
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · rcases Val.names_set _ b _ b' hs m hm with h1 | h1
      · exact Nat.lt_succ_of_lt (h.fresh _ List.mem_cons_self m h1)
      · simp [Val.names] at h1; omega
    · exact Nat.lt_succ_of_lt (h.fresh b0 (List.mem_cons_of_mem _ hb0) m hm)
  · intro v hv m hm
    simp only [List.mem_singleton] at hv; subst hv
    simp only [Val.names, List.mem_cons] at hm
    rcases hm with rfl | hm
    · omega
    · exact Nat.lt_succ_of_lt (h.fresh _ List.mem_cons_self m (Val.get_names _ hg m hm))
  · intro b0 hb0
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · exact Val.set_sh (h.sh _ List.mem_cons_self) (by simp [Val.nb]) hs
    · exact h.sh b0 (List.mem_cons_of_mem _ hb0)
  · intro v hv
    simp only [List.mem_singleton] at hv; subst hv
    exact Or.inr ⟨n, c, rfl, hcn⟩
  · rw [hHE]
    have hu := h.uniq
    simp only [HV_nil, List.append_nil] at hu
    simp only [HV_cons, Val.hd, HV_nil, List.append_nil, List.nodup_append, List.nodup_cons,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_singleton, true_and]
    refine ⟨hu, ?_⟩
    intro a ha b hb; subst hb; have := hHn a ha; omega
  · intro b0 hb0 m hm
    rw [hHE]
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · rcases s1' m hm with h1 | rfl
      · exact Or.inl (by simpa using h.live _ List.mem_cons_self m h1)
      · right; simp [Val.hd]
    · exact Or.inl (by simpa using h.live b0 (List.mem_cons_of_mem _ hb0) m hm)
  · intro m hm
    rw [hHE] at hm
    rcases hm with hm | hm
    · obtain ⟨b0, hb0, hmb⟩ := h.owned m (Or.inl hm)
      rcases List.mem_cons.mp hb0 with rfl | hb0
      · rcases Val.set_keep _ hs hg m hmb with h1 | h1
        · simp [hc] at h1
        · exact ⟨_, List.mem_cons_self, h1⟩
      · exact ⟨b0, List.mem_cons_of_mem _ hb0, hmb⟩
    · simp [Val.hd] at hm; subst hm
      exact ⟨_, List.mem_cons_self, s2 m (by simp [Val.loans])⟩
  · intro v hv
    simp only [List.mem_singleton] at hv; subst hv
    simpa [Val.loans] using hc
  · intro b0 hb0 p hp m hm
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · cases π with
      | nil => rw [Val.set_nil hs] at hp; simp [Val.hp] at hp
      | cons pr ps =>
        obtain ⟨p0, hp0, e1, hl0⟩ := Val.set_hp_cons hs p hp
        rw [e1]
        rcases hl0 m hm with h1 | h1
        · exact h.acyc _ List.mem_cons_self p0 hp0 m h1
        · simp [Val.loans] at h1; subst h1
          exact h.fresh _ List.mem_cons_self _ (Val.hp_fst_names hp0)
    · exact h.acyc b0 (List.mem_cons_of_mem _ hb0) p hp m hm
  · intro b0 hb0 ht
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · obtain ⟨i, hi⟩ := ht; exact absurd hi (hx i)
    · exact h.tmps b0 (List.mem_cons_of_mem _ hb0) ht

end Inv

end OchrMeta
