import OchrMeta.WFSet

/-! # Lemma 0, part 3: the machine's operations on the list of bindings -/

namespace OchrMeta

/-! ## The bindings of a state -/

theorem Env.flatten_mapVals (g : Val → Val) (Ω : Env) :
    (Ω.mapVals g).flatten = Ω.flatten.map fun b => (b.1, g b.2) := by
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.mapVals, List.map_cons, List.flatten_cons, List.map_append] at ih ⊢
    rw [ih]; rfl

theorem Env.holds_iff {Ω : Env} {l : Nat} : Ω.holds l = true ↔ l ∈ HE Ω.flatten := by
  simp only [Env.holds, Frame.holds, List.any_eq_true, mem_HE, List.mem_flatten,
    Val.isBorrowOf_iff]
  constructor
  · rintro ⟨F, hF, b, hb, hl⟩; exact ⟨b, ⟨F, hF, hb⟩, hl⟩
  · rintro ⟨b, ⟨F, hF, hb⟩, hl⟩; exact ⟨F, hF, b, hb, hl⟩

theorem Frame.holderContent_mem {F : Frame} {l : Nat} {w : Val} (h : F.holderContent l = some w) :
    ∃ x, (x, Val.borrow l w) ∈ F := by
  induction F with
  | nil => simp [Frame.holderContent] at h
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    cases v with
    | borrow m u =>
      simp only [Frame.holderContent] at h
      split at h
      · rename_i hm; cases h; subst hm; exact ⟨y, by simp⟩
      · obtain ⟨x, hx⟩ := ih h; exact ⟨x, List.mem_cons_of_mem _ hx⟩
    | _ =>
      simp only [Frame.holderContent] at h
      obtain ⟨x, hx⟩ := ih h; exact ⟨x, List.mem_cons_of_mem _ hx⟩

theorem Env.holderContent_mem {Ω : Env} {l : Nat} {w : Val} (h : Ω.holderContent l = some w) :
    ∃ x, (x, Val.borrow l w) ∈ Ω.flatten := by
  induction Ω with
  | nil => simp [Env.holderContent] at h
  | cons F Ω ih =>
    simp only [Env.holderContent] at h
    cases hF : F.holderContent l with
    | some u =>
      rw [hF] at h; cases h
      obtain ⟨x, hx⟩ := Frame.holderContent_mem hF
      exact ⟨x, by simp only [List.flatten_cons, List.mem_append]; exact Or.inl hx⟩
    | none =>
      rw [hF] at h
      obtain ⟨x, hx⟩ := ih (by simpa using h)
      exact ⟨x, by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hx⟩

theorem Frame.lookup_split {F : Frame} {x : Var} {b : Val} (h : F.lookup x = some b) :
    ∃ A B, F = A ++ (x, b) :: B ∧ ∀ v, Frame.set x v F = A ++ (x, v) :: B := by
  induction F with
  | nil => simp at h
  | cons c F ih =>
    obtain ⟨y, w⟩ := c
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hxy
      cases h
      have : y = x := by simp at hxy; exact hxy.symm
      subst this
      exact ⟨[], F, rfl, fun v => by simp [Frame.set]⟩
    · rename_i hxy
      have hne : y ≠ x := by intro e; subst e; simp at hxy
      obtain ⟨A, B, rfl, hs⟩ := ih h
      exact ⟨(y, w) :: A, B, rfl, fun v => by simp [Frame.set, hne, hs v]⟩

theorem St.lookup_perm {s : St} {x : Var} {b : Val} (h : s.lookup x = some b) :
    ∃ R : Bs, s.env.flatten.Perm ((x, b) :: R) ∧ ∀ v, (s.setVar x v).env.flatten.Perm ((x, v) :: R) ∧
      (s.setVar x v).env.length = s.env.length ∧ (s.setVar x v).next = s.next := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => simp [St.lookup] at h
  | cons F Ω =>
    simp only [St.lookup, List.head?_cons, Option.bind_some] at h
    obtain ⟨A, B, rfl, hs⟩ := Frame.lookup_split h
    refine ⟨A ++ B ++ Ω.flatten, ?_, fun v => ⟨?_, by simp [St.setVar, St.modTop], rfl⟩⟩
    · simp only [List.flatten_cons, List.append_assoc]
      exact List.perm_middle
    · simp only [St.setVar, St.modTop, hs v, List.flatten_cons, List.append_assoc]
      exact List.perm_middle

theorem Frame.remove_split {F F' : Frame} {x : Var} {v : Val} (h : Frame.remove x F = some (v, F')) :
    ∃ A B, F = A ++ (x, v) :: B ∧ F' = A ++ B := by
  induction F generalizing F' with
  | nil => simp [Frame.remove] at h
  | cons c F ih =>
    obtain ⟨y, w⟩ := c
    simp only [Frame.remove] at h
    split at h
    · rename_i hy; subst hy; cases h; exact ⟨[], F, rfl, rfl⟩
    · cases hr : Frame.remove x F with
      | none => rw [hr] at h; cases h
      | some p =>
        obtain ⟨v', F''⟩ := p
        rw [hr] at h; cases h
        obtain ⟨A, B, rfl, rfl⟩ := ih hr
        exact ⟨(y, w) :: A, B, rfl, rfl⟩

theorem St.unbind_perm {s s' : St} {x : Var} {c : Val} (h : s.unbind x = some (c, s')) :
    s.env.flatten.Perm ((x, c) :: s'.env.flatten) ∧ s'.env.length = s.env.length ∧ s'.next = s.next := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => simp [St.unbind] at h
  | cons F Ω =>
    simp only [St.unbind] at h
    cases hr : Frame.remove x F with
    | none => rw [hr] at h; cases h
    | some p =>
      obtain ⟨v', F'⟩ := p
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨A, B, rfl, rfl⟩ := Frame.remove_split hr
      refine ⟨?_, rfl, rfl⟩
      simp only [List.flatten_cons, List.append_assoc]
      exact List.perm_middle

theorem St.bind_flatten {s : St} (hs : s.env ≠ []) (x : Var) (v : Val) :
    (s.bind x v).env.flatten = (x, v) :: s.env.flatten ∧ (s.bind x v).env.length = s.env.length ∧
      (s.bind x v).next = s.next := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => exact absurd rfl hs
  | cons F Ω => simp [St.bind, St.modTop]

theorem St.bind_nil {s : St} (hs : s.env = []) (x : Var) (v : Val) : s.bind x v = s := by
  obtain ⟨Ω, n⟩ := s
  subst hs; rfl

theorem St.lookup_mem {s : St} {x : Var} {b : Val} (h : s.lookup x = some b) : (x, b) ∈ s.env.flatten := by
  obtain ⟨R, hR, _⟩ := St.lookup_perm h
  exact hR.mem_iff.mpr List.mem_cons_self

/-! ## [End] -/

theorem endWith_spec {l : Nat} {w : Val} {s s' : St} (h : endWith l w s = some s') :
    w.nb = 0 ∧ s'.env.flatten = s.env.flatten.map (fun b => (b.1, Val.substLoan l w b.2)) ∧
      s'.next = s.next ∧ s'.env.length = s.env.length := by
  unfold endWith at h
  split at h
  · rename_i hw; cases h
    exact ⟨hw, Env.flatten_mapVals _ _, rfl, by simp⟩
  · cases h

theorem endBorrow_inv {l : Nat} {s s' : St} {V : List Val} (hs : Inv s.env.flatten V s.next)
    (h : endBorrow l s = some s') :
    Inv s'.env.flatten V s'.next ∧ s'.next = s.next ∧ s'.env.length = s.env.length := by
  unfold endBorrow at h
  split at h
  · cases h
  · rename_i w hw
    obtain ⟨_, e1, e2, e3⟩ := endWith_spec h
    obtain ⟨x, hx⟩ := Env.holderContent_mem hw
    refine ⟨?_, e2, by rw [e3]; simp [Env.clearHolder]⟩
    rw [e1, e2]
    simp only [Env.clearHolder, Env.flatten_mapVals, List.map_map]
    exact hs.endMap hx

/-! ## [Access] -/

theorem Val.firstLive_none {f : Nat → Bool} {v : Val} (h : v.firstLive f = none) :
    ∀ l ∈ v.loans, f l = false := by
  induction v with
  | loan m =>
    simp only [Val.firstLive] at h
    intro l hl; simp [Val.loans] at hl; subst hl
    split at h
    · cases h
    · simpa using ‹¬f l = true›
  | succ v ih => exact ih (by simpa [Val.firstLive] using h)
  | borrow m v ih => exact ih (by simpa [Val.firstLive] using h)
  | pair a b iha ihb =>
    simp only [Val.firstLive, Option.or_eq_none_iff] at h
    intro l hl; simp only [Val.loans, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iha h.1 l hl
    · exact ihb h.2 l hl
  | sealed g a k x iha ihx =>
    simp only [Val.firstLive, Option.or_eq_none_iff] at h
    intro l hl; simp only [Val.loans, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iha h.1 l hl
    · exact ihx h.2 l hl
  | _ => simp [Val.loans]

theorem walk_done_get {f : Nat → Bool} {deep : Bool} :
    ∀ (π : List Proj) (v c : Val), walk f deep v π = .done c →
      v.get π = some c ∧ (deep = true → c.firstLive f = none) := by
  intro π
  induction π with
  | nil =>
    intro v c h
    simp only [walk] at h
    split at h
    · cases h
    · split at h
      · rename_i hd
        split at h
        · cases h
        · rename_i hf; cases h; exact ⟨rfl, fun _ => hf⟩
      · rename_i hd; cases h; exact ⟨rfl, fun h => absurd h hd⟩
  | cons pr ps ih =>
    intro v c h
    simp only [walk] at h
    split at h
    · cases h
    · cases hs : pr.step v with
      | ok w =>
        rw [hs] at h
        obtain ⟨h1, h2⟩ := ih w c h
        exact ⟨by simp [Val.get, hs, h1], h2⟩
      | stuck => rw [hs] at h; cases h
      | err => rw [hs] at h; cases h

theorem access_inv (deep : Bool) (x : Var) (π : List Proj) : ∀ (N : Nat) (s : St), s.env.nb = N →
    ∀ {V : List Val} {s' : St} {c : Val}, Inv s.env.flatten V s.next → access deep x π s = .ok s' c →
    Inv s'.env.flatten V s'.next ∧ s'.next = s.next ∧ s'.env.length = s.env.length ∧
      ∃ b, s'.lookup x = some b ∧ b.get π = some c ∧
        (deep = true → ∀ l ∈ c.loans, s'.env.holds l = false) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s hN V s' c hs h
  rw [access] at h
  cases hl : s.lookup x with
  | none => rw [hl] at h; cases h
  | some v =>
    rw [hl] at h
    simp only at h
    cases hwk : walk s.live deep v π with
    | found l =>
      rw [hwk] at h
      simp only at h
      split at h
      · cases h
      · rename_i s1 he
        obtain ⟨hs1, hn1, hl1⟩ := endBorrow_inv hs he
        obtain ⟨r1, r2, r3, r4⟩ := ih _ (hN ▸ endBorrow_nb_lt he) s1 rfl hs1 h
        exact ⟨r1, r2.trans hn1, r3.trans hl1, r4⟩
    | done c0 =>
      rw [hwk] at h
      cases h
      obtain ⟨hg, hf⟩ := walk_done_get π v c hwk
      exact ⟨hs, rfl, rfl, v, hl, hg, fun hd l hl' => Val.firstLive_none (hf hd) l hl'⟩
    | stuck => rw [hwk] at h; cases h
    | err => rw [hwk] at h; cases h

/-- After a deep [Access], the content's loans are all held by values in flight. -/
theorem access_clean {s : St} {V : List Val} (hs : Inv s.env.flatten V s.next) {x : Var} {b c : Val}
    {π : List Proj} (hb : s.lookup x = some b) (hg : b.get π = some c)
    (hd : ∀ l ∈ c.loans, s.env.holds l = false) : ∀ l ∈ c.loans, l ∈ HV V := by
  intro l hl
  rcases hs.live _ (St.lookup_mem hb) l (Val.get_loans π hg l hl) with h | h
  · have := hd l hl; rw [← Env.holds_iff] at h; simp_all
  · exact h

/-! ## [Drop], frame pops -/

theorem dropVal_nb {extra c : Val} {s : St} (hc : ∀ l d, c ≠ .borrow l d) :
    dropVal extra c s = if hasLive s extra c then none else some s := by
  cases c <;> simp_all [dropVal]

/-- Dropping a value `c` that has just left the environment (it still counts as a binding),
while `V` is in flight and `extra` holds every borrow of `V`. -/
theorem dropVal_inv {extra c : Val} {x : Var} {s s' : St} {V : List Val}
    (hs : Inv ((x, c) :: s.env.flatten) V s.next) (hV : ∀ l ∈ HV V, extra.isBorrowOf l = true)
    (h : dropVal extra c s = some s') :
    Inv s'.env.flatten V s'.next ∧ s'.next = s.next ∧ s'.env.length = s.env.length := by
  by_cases hb : ∃ l d, c = .borrow l d
  · obtain ⟨l, d, rfl⟩ := hb
    simp only [dropVal] at h
    obtain ⟨_, e1, e2, e3⟩ := endWith_spec h
    rw [e1, e2]
    exact ⟨hs.end_, rfl, e3⟩
  · have hc : ∀ l d, c ≠ .borrow l d := fun l d e => hb ⟨l, d, e⟩
    rw [dropVal_nb hc] at h
    split at h
    · cases h
    · rename_i hl
      cases h
      have hhd : c.hd = [] := by
        cases c <;> simp_all [Val.hd]
      have hf : c.firstLive (fun l => s.live l || extra.isBorrowOf l) = none := by
        simpa [hasLive] using hl
      have hcl : c.loans = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro l hlc
        have h1 := Val.firstLive_none hf l hlc
        simp only [Bool.or_eq_false_iff] at h1
        rcases hs.live _ List.mem_cons_self l hlc with h2 | h2
        · simp only [HE_cons, hhd, List.nil_append] at h2
          rw [← Env.holds_iff] at h2
          simp [St.live, h2] at h1
        · simp [hV l h2] at h1
      exact ⟨hs.drop_bind hcl (Val.nb_of_sh (hs.sh _ List.mem_cons_self) hhd), rfl, rfl⟩

theorem popFrameN_inv {extra : Val} : ∀ (k : Nat) {s s' : St}, Inv s.env.flatten [extra] s.next →
    popFrameN extra k s = some s' →
    Inv s'.env.flatten [extra] s'.next ∧ s'.next = s.next ∧ s'.env.length + 1 = s.env.length := by
  intro k
  induction k with
  | zero =>
    intro s s' hs h
    obtain ⟨Ω, n⟩ := s
    cases Ω with
    | nil => simp [popFrameN] at h
    | cons F Ω =>
      cases F with
      | nil => simp [popFrameN] at h; subst h; exact ⟨by simpa using hs, rfl, rfl⟩
      | cons b F => simp [popFrameN] at h
  | succ k ih =>
    intro s s' hs h
    obtain ⟨Ω, n⟩ := s
    cases Ω with
    | nil => simp [popFrameN] at h
    | cons F Ω =>
      cases F with
      | nil => simp [popFrameN] at h
      | cons b F =>
        obtain ⟨y, c⟩ := b
        simp only [popFrameN] at h
        cases hd : dropVal extra c { env := F :: Ω, next := n } with
        | none => rw [hd] at h; cases h
        | some s1 =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          have hV : ∀ l ∈ HV [extra], extra.isBorrowOf l = true := by
            intro l hl; simpa [Val.isBorrowOf_iff] using hl
          obtain ⟨h1, h2, h3⟩ := dropVal_inv (x := y) (by simpa using hs) hV hd
          obtain ⟨r1, r2, r3⟩ := ih h1 h
          exact ⟨r1, r2.trans h2, by rw [r3, h3]; rfl⟩

theorem popFrame_inv {extra : Val} {s s' : St} (hs : Inv s.env.flatten [extra] s.next)
    (h : popFrame extra s = some s') :
    Inv s'.env.flatten [extra] s'.next ∧ s'.next = s.next ∧ s'.env.length + 1 = s.env.length :=
  popFrameN_inv _ hs h

/-! ## Arguments and temporaries -/

theorem Res.bind_eq_ok {r : Res} {k : St → Val → Res} {s : St} {v : Val} (h : r.bind k = .ok s v) :
    ∃ s1 v1, r = .ok s1 v1 ∧ k s1 v1 = .ok s v := by
  cases r with
  | ok s1 v1 => exact ⟨s1, v1, rfl, h⟩
  | _ => simp [Res.bind] at h

/-- Binding the value in flight. -/
theorem St.bind_inv {s : St} {v : Val} {V : List Val} (hs : Inv s.env.flatten (v :: V) s.next) (x : Var) :
    Inv (s.bind x v).env.flatten V (s.bind x v).next ∧ (s.bind x v).next = s.next ∧
      (s.bind x v).env.length = s.env.length := by
  by_cases he : s.env = []
  · rw [St.bind_nil he]
    refine ⟨hs.drop_flight ?_, rfl, rfl⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro l hl
    obtain ⟨b, hb, _⟩ := hs.owned l (Or.inr (by simp [hl]))
    simp [he] at hb
  · obtain ⟨e1, e2, e3⟩ := St.bind_flatten he x v
    rw [e1, e3]
    exact ⟨hs.move_in x, rfl, e2⟩

/-- An evaluator that preserves the invariant on the terms satisfying `T`. -/
def EvInv (T : Term → Prop) (ev : St → Term → Res) : Prop :=
  ∀ (s : St) (t : Term) (s' : St) (v : Val), T t → Inv s.env.flatten [] s.next → ev s t = .ok s' v →
    Inv s'.env.flatten [v] s'.next ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length

theorem execArgs_inv {T : Term → Prop} {ev : St → Term → Res} (hev : EvInv T ev) :
    ∀ (args : List Term) (i : Nat) {s s' : St} {u : Val}, (∀ a ∈ args, T a) →
      Inv s.env.flatten [] s.next → execArgs ev i s args = .ok s' u →
      Inv s'.env.flatten [] s'.next ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length := by
  intro args
  induction args with
  | nil => intro i s s' u _ hs h; simp [execArgs] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, Nat.le_refl _, rfl⟩
  | cons a as ih =>
    intro i s s' u hT hs h
    simp only [execArgs] at h
    obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
    obtain ⟨i1, i2, i3⟩ := hev s a s1 v1 (hT a List.mem_cons_self) hs h1
    obtain ⟨b1, b2, b3⟩ := St.bind_inv i1 (.tmp i)
    obtain ⟨r1, r2, r3⟩ := ih (i + 1) (fun a ha => hT a (List.mem_cons_of_mem _ ha)) b1 h2
    exact ⟨r1, by omega, by rw [r3, b3, i3]⟩

theorem takeTemps_inv : ∀ (is : List Nat) {s s' : St} {V ws : List Val}, Inv s.env.flatten V s.next →
    takeTemps is s = some (ws, s') →
    Inv s'.env.flatten (V ++ ws) s'.next ∧ s'.next = s.next ∧ s'.env.length = s.env.length := by
  intro is
  induction is with
  | nil => intro s s' V ws hs h; simp [takeTemps] at h; obtain ⟨rfl, rfl⟩ := h; simpa using hs
  | cons i is ih =>
    intro s s' V ws hs h
    simp only [takeTemps] at h
    cases hu : s.unbind (.tmp i) with
    | none => rw [hu] at h; cases h
    | some p =>
      obtain ⟨c, s1⟩ := p
      rw [hu] at h
      simp only [Option.bind_some] at h
      cases ht : takeTemps is s1 with
      | none => rw [ht] at h; cases h
      | some q =>
        obtain ⟨vs, s2⟩ := q
        rw [ht] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨u1, u2, u3⟩ := St.unbind_perm hu
        have h1 : Inv ((Var.tmp i, c) :: s1.env.flatten) V s1.next := u3 ▸ hs.perm u1 (List.Perm.refl _)
        have hc : c.loans = [] := h1.tmps _ List.mem_cons_self ⟨i, rfl⟩
        have h2 : Inv s1.env.flatten (V ++ [c]) s1.next :=
          (h1.move_out (b := (Var.tmp i, c)) hc).perm (List.Perm.refl _) (List.perm_append_singleton _ _).symm
        obtain ⟨r1, r2, r3⟩ := ih h2 ht
        refine ⟨by simpa using r1, r2.trans u3, r3.trans u2⟩

end OchrMeta
