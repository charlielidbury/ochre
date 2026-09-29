import OchrMeta.WFOps

/-! # Lemma 0, part 4: [Close] and [Call] -/

namespace OchrMeta

/-- The substitutions of `fillLoans`, one after the other, on one value. -/
def fillV : List (Nat × Val) → Val → Val
  | [], v => v
  | (l, w) :: fs, v => fillV fs (Val.substLoan l w v)

theorem fillV_loans : ∀ (fs : List (Nat × Val)) {v : Val} {m : Nat}, m ∈ (fillV fs v).loans →
    (m ∈ v.loans ∧ m ∉ fs.map Prod.fst) ∨ ∃ p ∈ fs, m ∈ p.2.loans := by
  intro fs
  induction fs with
  | nil => intro v m h; exact Or.inl ⟨h, by simp⟩
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro v m h
    rcases ih h with ⟨h1, h2⟩ | ⟨q, hq, h3⟩
    · rcases Val.loans_substLoan h1 with ⟨h4, h5⟩ | ⟨_, h6⟩
      · exact Or.inl ⟨h4, by simp at h2 ⊢; exact ⟨h5, h2⟩⟩
      · exact Or.inr ⟨(l, w), List.mem_cons_self, h6⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h3⟩

theorem fillV_keep : ∀ (fs : List (Nat × Val)) {v : Val} {m : Nat}, m ∈ v.loans → m ∉ fs.map Prod.fst →
    m ∈ (fillV fs v).loans := by
  intro fs
  induction fs with
  | nil => intro v m h _; exact h
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro v m h hm
    simp only [List.map_cons, List.mem_cons, not_or] at hm
    exact ih (Val.loans_substLoan_keep h hm.1) hm.2

theorem fillV_new : ∀ (fs : List (Nat × Val)) {v : Val} {k : Nat}, (∃ p ∈ fs, p.1 ∈ v.loans) →
    (∀ p ∈ fs, k ∈ p.2.loans) → k ∉ fs.map Prod.fst → k ∈ (fillV fs v).loans := by
  intro fs
  induction fs with
  | nil => intro v k h; simp at h
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro v k h hk hkL
    simp only [List.map_cons, List.mem_cons, not_or] at hkL
    have hkw : k ∈ w.loans := hk (l, w) List.mem_cons_self
    by_cases hl : l ∈ v.loans
    · exact fillV_keep fs (Val.loans_substLoan_new hl hkw) hkL.2
    · obtain ⟨q, hq, hqv⟩ := h
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd hqv hl
      · have hne : q.1 ≠ l := fun e => hl (e ▸ hqv)
        exact ih ⟨q, hq, Val.loans_substLoan_keep hqv hne⟩
          (fun p hp => hk p (List.mem_cons_of_mem _ hp)) hkL.2

theorem fillV_names : ∀ (fs : List (Nat × Val)) {v : Val} {m : Nat}, m ∈ (fillV fs v).names →
    m ∈ v.names ∨ ∃ p ∈ fs, m ∈ p.2.names := by
  intro fs
  induction fs with
  | nil => intro v m h; exact Or.inl h
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro v m h
    rcases ih h with h1 | ⟨q, hq, h3⟩
    · rcases Val.names_substLoan h1 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr ⟨(l, w), List.mem_cons_self, h4⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h3⟩

theorem fillV_of_nil : ∀ (fs : List (Nat × Val)) {v : Val}, v.loans = [] → fillV fs v = v := by
  intro fs
  induction fs with
  | nil => intro v _; rfl
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro v h
    simp only [fillV]
    rw [Val.substLoan_of_not_mem (by simp [h])]
    exact ih h

theorem fillV_hd : ∀ (fs : List (Nat × Val)), (∀ p ∈ fs, p.2.nb = 0) → ∀ v, (fillV fs v).hd = v.hd := by
  intro fs
  induction fs with
  | nil => intro _ v; rfl
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro hW v
    simp only [fillV]
    rw [ih (fun q hq => hW q (List.mem_cons_of_mem _ hq)), Val.hd_substLoan (hW _ List.mem_cons_self)]

theorem fillV_hp : ∀ (fs : List (Nat × Val)), (∀ p ∈ fs, p.2.nb = 0) → ∀ v,
    (fillV fs v).hp = v.hp.map fun p => (p.1, fillV fs p.2) := by
  intro fs
  induction fs with
  | nil => intro _ v; simp [fillV]
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro hW v
    simp only [fillV]
    rw [ih (fun q hq => hW q (List.mem_cons_of_mem _ hq)), Val.hp_substLoan (hW _ List.mem_cons_self),
      List.map_map]
    rfl

theorem fillV_sh : ∀ (fs : List (Nat × Val)), (∀ p ∈ fs, p.2.nb = 0) → ∀ {v : Val}, v.Sh → (fillV fs v).Sh := by
  intro fs
  induction fs with
  | nil => intro _ v h; exact h
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro hW v h
    exact ih (fun q hq => hW q (List.mem_cons_of_mem _ hq)) (Val.sh_substLoan (hW _ List.mem_cons_self) h)

theorem fillLoans_spec : ∀ (fs : List (Nat × Val)) {s s' : St}, fillLoans fs s = some s' →
    s'.env.flatten = s.env.flatten.map (fun b => (b.1, fillV fs b.2)) ∧ s'.next = s.next ∧
      s'.env.length = s.env.length ∧ ∀ p ∈ fs, p.2.nb = 0 := by
  intro fs
  induction fs with
  | nil => intro s s' h; simp [fillLoans] at h; subst h; simp [fillV]
  | cons p fs ih =>
    obtain ⟨l, w⟩ := p
    intro s s' h
    simp only [fillLoans] at h
    cases he : endWith l w s with
    | none => rw [he] at h; cases h
    | some s1 =>
      rw [he] at h
      simp only [Option.bind_some] at h
      obtain ⟨e0, e1, e2, e3⟩ := endWith_spec he
      obtain ⟨r1, r2, r3, r4⟩ := ih h
      refine ⟨?_, r2.trans e2, r3.trans e3, ?_⟩
      · rw [r1, e1, List.map_map]; rfl
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact e0
        · exact r4 q hq

theorem Val.hd_nodup (v : Val) : v.hd.Nodup := by cases v <;> simp [Val.hd]

/-- [Close] on the list of bindings: the borrow arguments in flight (`ws`) are consumed, their
loans `L` are filled, and the result `res` goes in flight.  The only new names (in the fills
and in `res`) are `≥ n` and `< n'`. -/
theorem Inv.fill {E : Bs} {ws : List Val} {n n' : Nat} {fs : List (Nat × Val)} {res : Val}
    (h : Inv E ws n) (hnn : n ≤ n')
    (hW : ∀ p ∈ fs, p.2.nb = 0 ∧ ∀ m ∈ p.2.names, n ≤ m ∧ m < n')
    (hres : res.Sh ∧ res.loans = [] ∧ ∀ m ∈ res.names, n ≤ m ∧ m < n')
    (hlive : ∀ p ∈ fs, ∀ m ∈ p.2.loans, m ∈ res.hd)
    (hown : ∀ m ∈ res.hd, fs ≠ [] ∧ ∀ p ∈ fs, m ∈ p.2.loans)
    (hL1 : ∀ l ∈ HV ws, l ∈ fs.map Prod.fst) (hL2 : ∀ l ∈ fs.map Prod.fst, l ∈ HV ws) :
    Inv (E.map fun b => (b.1, fillV fs b.2)) [res] n' := by
  have hW0 : ∀ p ∈ fs, p.2.nb = 0 := fun p hp => (hW p hp).1
  have hHE : HE (E.map fun b => (b.1, fillV fs b.2)) = HE E := HE_map (fun b _ => fillV_hd fs hW0 b.2)
  have hEn : ∀ m ∈ HE E, m < n := by
    intro m hm; obtain ⟨b, hb, hmb⟩ := HE_names hm; exact h.fresh b hb m hmb
  have hVn : ∀ m ∈ HV ws, m < n := by
    intro m hm; obtain ⟨v, hv, hmv⟩ := mem_HV.mp hm; exact h.freshV v hv m (Val.hd_names hmv)
  have hdisj : ∀ m ∈ HE E, m ∉ HV ws := by
    have := (List.nodup_append.mp h.uniq).2.2
    intro m hm hm'; exact this m hm m hm' rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb m hm
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    rcases fillV_names fs hm with h1 | ⟨p, hp, h1⟩
    · exact Nat.lt_of_lt_of_le (h.fresh b0 hb0 m h1) hnn
    · exact ((hW p hp).2 m h1).2
  · intro v hv m hm
    simp only [List.mem_singleton] at hv; subst hv
    exact (hres.2.2 m hm).2
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    exact fillV_sh fs hW0 (h.sh b0 hb0)
  · intro v hv
    simp only [List.mem_singleton] at hv; subst hv; exact hres.1
  · rw [hHE]
    simp only [HV_cons, HV_nil, List.append_nil]
    refine List.nodup_append.mpr ⟨(List.nodup_append.mp h.uniq).1, Val.hd_nodup res, ?_⟩
    intro a ha b hb e
    subst e
    have := hEn a ha
    have := (hres.2.2 a (Val.hd_names hb)).1
    omega
  · intro b hb m hm
    rw [hHE]
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    rcases fillV_loans fs hm with ⟨h1, h2⟩ | ⟨p, hp, h1⟩
    · rcases h.live b0 hb0 m h1 with h3 | h3
      · exact Or.inl h3
      · exact absurd (hL1 m h3) h2
    · exact Or.inr (by simpa using hlive p hp m h1)
  · intro m hm
    rw [hHE] at hm
    rcases hm with hm | hm
    · obtain ⟨b0, hb0, hmb⟩ := h.owned m (Or.inl hm)
      refine ⟨_, List.mem_map_of_mem hb0, fillV_keep fs hmb ?_⟩
      intro hmL; exact hdisj m hm (hL2 m hmL)
    · simp only [HV_cons, HV_nil, List.append_nil] at hm
      obtain ⟨hne, hall⟩ := hown m hm
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil fs hne
      have hpL : p.1 ∈ HV ws := hL2 p.1 (List.mem_map_of_mem hp)
      obtain ⟨b0, hb0, hpb⟩ := h.owned p.1 (Or.inr hpL)
      refine ⟨_, List.mem_map_of_mem hb0, fillV_new fs ⟨p, hp, hpb⟩ hall ?_⟩
      intro hmL
      have := hVn m (hL2 m hmL)
      have := (hres.2.2 m (Val.hd_names hm)).1
      omega
  · intro v hv
    simp only [List.mem_singleton] at hv; subst hv; exact hres.2.1
  · intro b hb p hp m hm
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    simp only [fillV_hp fs hW0, List.mem_map] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    rcases fillV_loans fs hm with ⟨h1, _⟩ | ⟨q, hq, h1⟩
    · exact h.acyc b0 hb0 p0 hp0 m h1
    · have := h.fresh b0 hb0 _ (Val.hp_fst_names hp0)
      have := ((hW q hq).2 m (Val.loans_sub_names h1)).1
      simp only; omega
  · intro b hb ht
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    have := h.tmps b0 hb0 ht
    simp only
    rw [fillV_of_nil fs this, this]

/-! ## [Close] -/

theorem sealArgs_inv : ∀ (i : Nat) (ps : List (Var × Ty)) (ws as : List Val) (ls : List (Nat × Nat)),
    sealArgs i ps ws = some (as, ls) →
    (∀ a ∈ as, a ∈ ws ∨ ∃ l, Val.borrow l a ∈ ws) ∧ (∀ p ∈ ls, ∃ u, Val.borrow p.2 u ∈ ws) ∧
    (∀ w ∈ ws, w ∈ as ∨ ∃ p ∈ ls, ∃ u, w = Val.borrow p.2 u) := by
  intro i ps
  induction ps generalizing i with
  | nil =>
    intro ws as ls h
    cases ws with
    | nil => simp [sealArgs] at h; obtain ⟨rfl, rfl⟩ := h; simp
    | cons w ws => simp [sealArgs] at h
  | cons p ps ih =>
    intro ws as ls h
    obtain ⟨y, ty⟩ := p
    cases ws with
    | nil => cases ty <;> simp [sealArgs] at h
    | cons w ws =>
      have step : ∀ (as' : List Val) (ls' : List (Nat × Nat)), sealArgs (i + 1) ps ws = some (as', ls') →
          (∀ a ∈ as', a ∈ w :: ws ∨ ∃ l, Val.borrow l a ∈ w :: ws) ∧
          (∀ p ∈ ls', ∃ u, Val.borrow p.2 u ∈ w :: ws) ∧
          (∀ w' ∈ ws, w' ∈ as' ∨ ∃ p ∈ ls', ∃ u, w' = Val.borrow p.2 u) := by
        intro as' ls' hr
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) ws as' ls' hr
        refine ⟨?_, ?_, h3⟩
        · intro a ha
          rcases h1 a ha with h | ⟨l, h⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨l, List.mem_cons_of_mem _ h⟩
        · intro q hq
          obtain ⟨u, hu⟩ := h2 q hq
          exact ⟨u, List.mem_cons_of_mem _ hu⟩
      cases ty with
      | ref T =>
        cases w with
        | borrow l u =>
          simp only [sealArgs] at h
          cases hr : sealArgs (i + 1) ps ws with
          | none => rw [hr] at h; cases h
          | some q =>
            obtain ⟨as', ls'⟩ := q
            rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨h1, h2, h3⟩ := step as' ls' hr
            refine ⟨?_, ?_, ?_⟩
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact Or.inr ⟨l, List.mem_cons_self⟩
              · exact h1 a ha
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact ⟨u, List.mem_cons_self⟩
              · exact h2 q hq
            · intro w' hw'
              rcases List.mem_cons.mp hw' with rfl | hw'
              · exact Or.inr ⟨(i, l), List.mem_cons_self, u, rfl⟩
              · rcases h3 w' hw' with h | ⟨q, hq, u', e⟩
                · exact Or.inl (List.mem_cons_of_mem _ h)
                · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, u', e⟩
        | _ => simp [sealArgs] at h
      | _ =>
        simp only [sealArgs] at h
        cases hr : sealArgs (i + 1) ps ws with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨as', ls'⟩ := q
          rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3⟩ := step as' ls' hr
          refine ⟨?_, h2, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact Or.inl List.mem_cons_self
            · exact h1 a ha
          · intro w' hw'
            rcases List.mem_cons.mp hw' with rfl | hw'
            · exact Or.inl List.mem_cons_self
            · rcases h3 w' hw' with h | ⟨q, hq, u', e⟩
              · exact Or.inl (List.mem_cons_of_mem _ h)
              · exact Or.inr ⟨q, hq, u', e⟩

theorem Val.nb_ofList_wf {as : List Val} (h : (Val.ofList as).nb = 0) : ∀ a ∈ as, a.nb = 0 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [Val.ofList, Val.nb] at h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · exact ih (by omega) b hb

/-- The fills of one row of the [Close] table, on the state. -/
theorem closeFill {s s1 s2 : St} {ws : List Val} {ls : List (Nat × Nat)} (W : Nat → Val) {res : Val}
    {n' : Nat} (hs : Inv s.env.flatten ws s.next) (he : s1.env = s.env) (hn : s1.next = n')
    (hnn : s.next ≤ n') (hf : fillLoans (ls.map fun x => (x.2, W x.1)) s1 = some s2)
    (hW : ∀ i, (W i).nb = 0 ∧ ∀ m ∈ (W i).names, s.next ≤ m ∧ m < n')
    (hres : res.Sh ∧ res.loans = [] ∧ ∀ m ∈ res.names, s.next ≤ m ∧ m < n')
    (hlive : ∀ i, ∀ m ∈ (W i).loans, m ∈ res.hd)
    (hown : ∀ m ∈ res.hd, ls ≠ [] ∧ ∀ i, m ∈ (W i).loans)
    (hL1 : ∀ l ∈ HV ws, l ∈ ls.map Prod.snd) (hL2 : ∀ l ∈ ls.map Prod.snd, l ∈ HV ws) :
    Inv s2.env.flatten [res] s2.next ∧ s.next ≤ s2.next ∧ s2.env.length = s.env.length := by
  obtain ⟨e1, e2, e3, _⟩ := fillLoans_spec _ hf
  refine ⟨?_, by omega, by rw [e3, he]⟩
  rw [e1, e2, he, hn]
  have hfst : (ls.map fun x => (x.2, W x.1)).map Prod.fst = ls.map Prod.snd := by
    rw [List.map_map]; rfl
  apply hs.fill hnn
  · intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    exact hW x.1
  · exact hres
  · intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    exact hlive x.1
  · intro m hm
    obtain ⟨hne, hall⟩ := hown m hm
    refine ⟨by simpa using hne, ?_⟩
    intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    exact hall x.1
  · rw [hfst]; exact hL1
  · rw [hfst]; exact hL2

theorem closeCall_inv (f : String) (d : FunDef) {ws : List Val} {s s' : St} {v : Val}
    (hs : Inv s.env.flatten ws s.next) (h : closeCall f d ws s = .ok s' v) :
    Inv s'.env.flatten [v] s'.next ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length := by
  unfold closeCall at h
  cases hsa : sealArgs 0 d.params ws with
  | none => rw [hsa] at h; cases h
  | some q =>
    obtain ⟨as, ls⟩ := q
    rw [hsa] at h
    simp only at h
    obtain ⟨f1, f2, f3⟩ := sealArgs_inv 0 d.params ws as ls hsa
    by_cases hnb : (Val.ofList as).nb ≠ 0
    · rw [if_pos hnb] at h; cases h
    rw [if_neg hnb] at h
    have hnb0 : (Val.ofList as).nb = 0 := by omega
    have has : ∀ a ∈ as, a.nb = 0 ∧ a.loans = [] := by
      intro a ha
      refine ⟨Val.nb_ofList_wf hnb0 a ha, ?_⟩
      rcases f1 a ha with h1 | ⟨l, h1⟩
      · exact hs.clean a h1
      · simpa [Val.loans] using hs.clean _ h1
    have hargs : (Val.ofList as).names = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro m hm
      obtain ⟨a, ha, hma⟩ := Val.names_ofList hm
      rw [Val.names_nil_wf (has a ha).1 (has a ha).2] at hma
      simp at hma
    have hargsl : (Val.ofList as).loans = [] := List.eq_nil_iff_forall_not_mem.mpr fun m hm => by
      have := Val.loans_sub_names hm; simp [hargs] at this
    have hL1 : ∀ l ∈ HV ws, l ∈ ls.map Prod.snd := by
      intro l hl
      obtain ⟨w, hw, hlw⟩ := mem_HV.mp hl
      obtain ⟨u, rfl⟩ := Val.mem_hd.mp hlw
      rcases f3 _ hw with h1 | ⟨p, hp, u', e⟩
      · have := Val.nb_ofList_wf hnb0 _ h1; simp [Val.nb] at this
      · cases e; exact List.mem_map_of_mem hp
    have hL2 : ∀ l ∈ ls.map Prod.snd, l ∈ HV ws := by
      intro l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨u, hu⟩ := f2 p hp
      exact mem_HV.mpr ⟨_, hu, by simp [Val.hd]⟩
    have hfin : ∀ (i : Nat), (Val.sealed f (Val.ofList as) (.fin i) .unit).nb = 0 ∧
        ∀ m ∈ (Val.sealed f (Val.ofList as) (.fin i) .unit).names, s.next ≤ m ∧ m < s.next := by
      intro i; simp [Val.nb, Val.names, hnb0, hargs]
    have hfinl : ∀ (i : Nat), ∀ m ∈ (Val.sealed f (Val.ofList as) (.fin i) .unit).loans, m ∈ Val.hd .unit := by
      intro i m hm; simp [Val.loans, hargsl] at hm
    split at h
    · -- a returned borrow
      split at h
      · cases h
      · rename_i hls
        split at h
        · cases h
        · rename_i s2 hf
          cases h
          refine closeFill (s1 := { env := s.env, next := s.next + 1 })
            (fun i => Val.sealed f (Val.ofList as) (.back i) (.loan s.next)) hs rfl rfl
            (Nat.le_succ _) hf ?_ ?_ ?_ ?_ hL1 hL2
          · intro i; simp [Val.nb, Val.names, hnb0, hargs]
          · refine ⟨Or.inr ⟨_, _, rfl, by simp [Val.nb, hnb0]⟩, by simp [Val.loans, hargsl], ?_⟩
            intro m hm; simp [Val.names, hargs] at hm; subst hm; simp
          · intro i m hm; simp [Val.loans, hargsl] at hm; simp [Val.hd, hm]
          · intro m hm; simp [Val.hd] at hm; subst hm
            exact ⟨hls, fun i => by simp [Val.loans]⟩
    · split at h
      · cases h
      · rename_i s2 hf
        cases h
        exact closeFill (fun i => Val.sealed f (Val.ofList as) (.fin i) .unit) hs rfl rfl (Nat.le_refl _)
          hf hfin ⟨Val.sh_of_nb rfl, rfl, by simp [Val.names]⟩ hfinl (by simp [Val.hd]) hL1 hL2
    · split at h
      · cases h
      · rename_i s2 hf
        cases h
        exact closeFill (fun i => Val.sealed f (Val.ofList as) (.fin i) .unit) hs rfl rfl (Nat.le_refl _)
          hf hfin ⟨Val.sh_of_nb (by simp [Val.nb, hnb0]), by simp [Val.loans, hargsl],
            by simp [Val.names, hargs]⟩ hfinl (by simp [Val.hd]) hL1 hL2

/-! ## [Call] -/

/-- The arguments in flight become the parameter frame. -/
theorem Inv.move_in_zip : ∀ {ws : List Val} {xs : List Var} {E : Bs} {n : Nat}, Inv E ws n →
    xs.length = ws.length → Inv (xs.zip ws ++ E) [] n := by
  intro ws
  induction ws with
  | nil => intro xs E n h _; simpa using h
  | cons w ws ih =>
    intro xs E n h hl
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have := ih (h.move_in x) hl
      exact this.perm (by simp) (List.Perm.refl _)

theorem callWith_inv {T : Term → Prop} {run : St → Term → Res} (hrun : EvInv T run) (cc : Bool)
    (f : String) (d : FunDef) {ws : List Val} {s s' : St} {v : Val} (hT : ∀ b, d.body = some b → T b)
    (hs : Inv s.env.flatten ws s.next) (h : callWith run cc f d ws s = .ok s' v) :
    Inv s'.env.flatten [v] s'.next ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length := by
  unfold callWith at h
  cases hb : d.body with
  | none =>
    rw [hb] at h
    simp only at h
    split at h
    · exact closeCall_inv f d hs h
    · cases h
  | some b =>
    rw [hb] at h
    simp only at h
    split at h
    · rename_i hlen
      have hpush : Inv (s.push (paramFrame d ws)).env.flatten [] (s.push (paramFrame d ws)).next := by
        simp only [St.push, List.flatten_cons, paramFrame]
        exact hs.move_in_zip (by simp [hlen])
      cases hr : run (s.push (paramFrame d ws)) b with
      | ok s1 v1 =>
        rw [hr] at h
        simp only at h
        split at h
        · cases h
        · rename_i s2 hp
          cases h
          obtain ⟨r1, r2, r3⟩ := hrun _ b _ _ (hT b hb) hpush hr
          obtain ⟨p1, p2, p3⟩ := popFrame_inv r1 hp
          refine ⟨p1, by simp [St.push] at r2; omega, ?_⟩
          simp [St.push] at r3; omega
      | stuck =>
        rw [hr] at h
        simp only at h
        split at h
        · exact closeCall_inv f d hs h
        · cases h
      | err => rw [hr] at h; cases h
      | oof => rw [hr] at h; cases h
    · cases h

end OchrMeta
