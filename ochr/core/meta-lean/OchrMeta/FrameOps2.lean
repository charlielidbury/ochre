import OchrMeta.FrameOps

/-! # Frame lemma, part 2: names and invariant for top-frame operations -/

namespace OchrMeta

theorem Val.names_set : ∀ (π : List Proj) (v new v' : Val), v.set π new = some v' →
    ∀ x ∈ v'.names, x ∈ v.names ∨ x ∈ new.names := by
  intro π
  induction π with
  | nil => intro v new v' h; simp [Val.set] at h; subst h; exact fun x hx => Or.inr hx
  | cons pr ps ih =>
    intro v new v' h x hx
    simp only [Val.set] at h
    cases hs : pr.step v with
    | ok w =>
      rw [hs] at h
      simp only at h
      cases hw : w.set ps new with
      | none => rw [hw] at h; cases h
      | some w' =>
        rw [hw] at h
        simp only [Option.bind_some] at h
        have ihw := ih w new w' hw
        have hwv := Proj.step_names hs
        cases pr <;> cases v <;> simp [Proj.put, Proj.step] at h hs <;>
          (subst h; subst hs; simp [Val.names] at hx ⊢) <;> grind
    | stuck => rw [hs] at h; cases h
    | err => rw [hs] at h; cases h

/-- Names of a state's environment are closed under an operation on the top frame. -/
theorem St.names_modTop {c : St} {g : Frame → Frame} {S : Nat → Prop}
    (hg : ∀ F, ∀ b ∈ g F, ∀ x ∈ b.2.names, (∃ b' ∈ F, x ∈ b'.2.names) ∨ S x) :
    ∀ x ∈ (c.modTop g).env.names, x ∈ c.env.names ∨ S x := by
  intro x hx
  obtain ⟨Ω, n⟩ := c
  cases Ω with
  | nil => exact Or.inl hx
  | cons F Ω =>
    simp only [St.modTop] at hx
    rw [Env.mem_names] at hx ⊢
    obtain ⟨G, hG, b, hb, hxb⟩ := hx
    rcases List.mem_cons.mp hG with rfl | hG
    · rcases hg F b hb x hxb with ⟨b', hb', hx'⟩ | h
      · exact Or.inl ⟨F, by simp, b', hb', hx'⟩
      · exact Or.inr h
    · exact Or.inl ⟨G, List.mem_cons_of_mem _ hG, b, hb, hxb⟩

theorem Frame.mem_set {x : Var} {v : Val} : ∀ (F : Frame) (b : Var × Val), b ∈ F.set x v → b ∈ F ∨ b = (x, v) := by
  intro F
  induction F with
  | nil => simp [Frame.set]
  | cons c F ih =>
    intro b hb
    obtain ⟨y, w⟩ := c
    simp only [Frame.set] at hb
    split at hb
    · rename_i hy; subst hy
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ hb)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl (by simp)
      · rcases ih b hb with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem Frame.remove_sub {x : Var} : ∀ (F F' : Frame) (v : Val), F.remove x = some (v, F') →
    (x, v) ∈ F ∧ ∀ b ∈ F', b ∈ F := by
  intro F
  induction F with
  | nil => simp [Frame.remove]
  | cons c F ih =>
    intro F' v h
    obtain ⟨y, w⟩ := c
    simp only [Frame.remove] at h
    split at h
    · rename_i hy; subst hy; cases h; exact ⟨by simp, fun b hb => List.mem_cons_of_mem _ hb⟩
    · cases hr : Frame.remove x F with
      | none => rw [hr] at h; cases h
      | some p =>
        obtain ⟨v', F''⟩ := p
        rw [hr] at h; cases h
        obtain ⟨h1, h2⟩ := ih F'' v' hr
        refine ⟨List.mem_cons_of_mem _ h1, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · exact List.mem_cons_of_mem _ (h2 b hb)

theorem St.names_setVar {c : St} {x : Var} {v : Val} :
    ∀ y ∈ (c.setVar x v).env.names, y ∈ c.env.names ∨ y ∈ v.names := by
  apply St.names_modTop
  intro F b hb y hy
  rcases Frame.mem_set F b hb with h | rfl
  · exact Or.inl ⟨b, h, hy⟩
  · exact Or.inr hy

theorem St.names_bind {c : St} {x : Var} {v : Val} :
    ∀ y ∈ (c.bind x v).env.names, y ∈ c.env.names ∨ y ∈ v.names := by
  apply St.names_modTop
  intro F b hb y hy
  rcases List.mem_cons.mp hb with rfl | h
  · exact Or.inr hy
  · exact Or.inl ⟨b, h, hy⟩

theorem St.unbind_spec {c c' : St} {x : Var} {v : Val} (h : c.unbind x = some (v, c')) :
    (∀ y ∈ c'.env.names, y ∈ c.env.names) ∧ (∀ y ∈ v.names, y ∈ c.env.names) ∧
      c'.env.length = c.env.length ∧ c'.next = c.next := by
  obtain ⟨Ω, n⟩ := c
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
      obtain ⟨h1, h2⟩ := Frame.remove_sub F F' v' hr
      refine ⟨?_, ?_, rfl, rfl⟩
      · intro y hy
        rw [Env.mem_names] at hy ⊢
        obtain ⟨G, hG, b, hb, hyb⟩ := hy
        rcases List.mem_cons.mp hG with rfl | hG
        · exact ⟨F, by simp, b, h2 b hb, hyb⟩
        · exact ⟨G, List.mem_cons_of_mem _ hG, b, hb, hyb⟩
      · intro y hy
        rw [Env.mem_names]
        exact ⟨F, by simp, (x, _), h1, hy⟩

theorem St.setPlace_spec {c c' : St} {x : Var} {π : List Proj} {v : Val} (h : c.setPlace x π v = some c') :
    (∀ y ∈ c'.env.names, y ∈ c.env.names ∨ y ∈ v.names) ∧ c'.env.length = c.env.length ∧ c'.next = c.next := by
  simp only [St.setPlace] at h
  cases hl : c.lookup x with
  | none => rw [hl] at h; cases h
  | some r =>
    rw [hl] at h
    simp only [Option.bind_some] at h
    cases hs : r.set π v with
    | none => rw [hs] at h; cases h
    | some r' =>
      rw [hs] at h; cases h
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rcases St.names_setVar y hy with h | h
        · exact Or.inl h
        · rcases Val.names_set π r v r' hs y h with h | h
          · exact Or.inl (St.lookup_names hl y h)
          · exact Or.inr h
      · obtain ⟨Ω, n⟩ := c; cases Ω <;> simp [St.setVar, St.modTop]
      · obtain ⟨Ω, n⟩ := c; cases Ω <;> simp [St.setVar, St.modTop]

end OchrMeta

namespace OchrMeta

/-! ## [Drop] and frame pops -/

section
variable {Ω₂ : Env} {K : List Nat}

/-- Port-side shape of an `Option St` result. -/
def PSt (Ω₂ : Env) (K : List Nat) (len : Nat) (next : Nat) : Option St → Prop
  | some s => ∃ c' P', s = c'.app [P'] ∧ PInv Ω₂ K c' P' ∧ c'.env.length = len ∧ next ≤ c'.next
  | none => True

theorem hasLive_frame {c : St} {P : Frame} (hc : PInv Ω₂ K c P) {v : Val}
    (hv : ∀ l ∈ v.names, Good Ω₂ K l) (extra : Val) :
    hasLive (c.app (Ω₂.substPorts K P)) extra v = hasLive (c.app [P]) extra v := by
  unfold hasLive
  rw [Val.firstLive_congr v (fun l hl => by rw [live_app_good hc (hv l (Val.loans_sub_names hl))])]

theorem dropVal_frame {c : St} {P : Frame} (hc : PInv Ω₂ K c P) {v : Val}
    (hv : ∀ l ∈ v.names, Good Ω₂ K l) (extra : Val) :
    dropVal extra v (c.app (Ω₂.substPorts K P)) = (dropVal extra v (c.app [P])).map (frameMap K Ω₂) ∧
    PSt Ω₂ K c.env.length c.next (dropVal extra v (c.app [P])) := by
  cases v with
  | borrow l w =>
    simp only [dropVal]
    have hg : Good Ω₂ K l := hv l (by simp [Val.names])
    refine ⟨endWith_frame w hc hg, ?_⟩
    cases h : endWith l w (c.app [P]) with
    | none => trivial
    | some s' =>
      obtain ⟨c', P', rfl, hc', hlen, hn⟩ := endWith_pinv hc (fun x hx => hv x (by simp [Val.names, hx])) h
      exact ⟨c', P', rfl, hc', hlen, hn ▸ Nat.le_refl _⟩
  | _ =>
    simp only [dropVal, hasLive_frame hc hv extra]
    split
    · exact ⟨rfl, trivial⟩
    · exact ⟨by simp [St.frameMap_app], c, P, rfl, hc, rfl, Nat.le_refl _⟩

theorem PInv.shrink {c c' : St} {P : Frame} (hc : PInv Ω₂ K c P) (hne : c'.env ≠ [])
    (hn : ∀ x ∈ c'.env.names, x ∈ c.env.names) (hnx : c.next ≤ c'.next) : PInv Ω₂ K c' P where
  ne := hne
  pnb := hc.pnb
  keys := hc.keys
  good := fun x hx => hc.good x (hn x hx)
  fresh := fun l hl => hc.fresh l (Nat.le_trans hnx hl)

theorem PInv.grow {c c' : St} {P : Frame} (hc : PInv Ω₂ K c P) (hne : c'.env ≠ []) {S : Nat → Prop}
    (hS : ∀ x, S x → Good Ω₂ K x)
    (hn : ∀ x ∈ c'.env.names, x ∈ c.env.names ∨ S x) (hnx : c.next ≤ c'.next) : PInv Ω₂ K c' P where
  ne := hne
  pnb := hc.pnb
  keys := hc.keys
  good := fun x hx => (hn x hx).elim (hc.good x) (hS x)
  fresh := fun l hl => hc.fresh l (Nat.le_trans hnx hl)

theorem popFrameN_frame (extra : Val) :
    ∀ (n : Nat) (c : St) (P : Frame), PInv Ω₂ K c P → 2 ≤ c.env.length →
      popFrameN extra n (c.app (Ω₂.substPorts K P)) = (popFrameN extra n (c.app [P])).map (frameMap K Ω₂) ∧
      PSt Ω₂ K (c.env.length - 1) c.next (popFrameN extra n (c.app [P])) := by
  intro n
  induction n with
  | zero =>
    intro c P hc h2
    obtain ⟨Ω, m⟩ := c
    rcases Ω with _ | ⟨F, A'⟩
    · simp at h2
    · cases F with
      | nil =>
        simp only [popFrameN, St.app, List.cons_append]
        refine ⟨by simp [frameMap], ⟨A', m⟩, P, rfl, ?_, by simp, Nat.le_refl _⟩
        exact hc.shrink (by rintro rfl; simp at h2)
          (fun x hx => by simp only [Env.mem_names] at hx ⊢; obtain ⟨G, hG, b, hb, h⟩ := hx; exact ⟨G, List.mem_cons_of_mem _ hG, b, hb, h⟩)
          (Nat.le_refl _)
      | cons b F => exact ⟨rfl, trivial⟩
  | succ n ih =>
    intro c P hc h2
    obtain ⟨Ω, m⟩ := c
    rcases Ω with _ | ⟨F, A'⟩
    · simp at h2
    · cases F with
      | nil => exact ⟨rfl, trivial⟩
      | cons b F =>
        obtain ⟨y, cv⟩ := b
        simp only [popFrameN, St.app, List.cons_append]
        have hsub : ∀ x ∈ Env.names (F :: A'), x ∈ Env.names (((y, cv) :: F) :: A') := by
          intro x hx
          simp only [Env.mem_names] at hx ⊢
          obtain ⟨G, hG, b, hb, h⟩ := hx
          rcases List.mem_cons.mp hG with hGF | hG
          · subst hGF; exact ⟨(y, cv) :: G, List.mem_cons_self .., b, List.mem_cons_of_mem _ hb, h⟩
          · exact ⟨G, List.mem_cons_of_mem _ hG, b, hb, h⟩
        have hc0 : PInv Ω₂ K ⟨F :: A', m⟩ P := hc.shrink (by simp) hsub (Nat.le_refl _)
        have hcv : ∀ l ∈ cv.names, Good Ω₂ K l := fun l hl =>
          hc.good l (by
            simp only [Env.mem_names]
            exact ⟨((y, cv) :: F), List.mem_cons_self .., (y, cv), List.mem_cons_self .., hl⟩)
        obtain ⟨hd1, hd2⟩ := dropVal_frame (c := ⟨F :: A', m⟩) hc0 hcv extra
        simp only [St.app, List.cons_append] at hd1 hd2
        rw [hd1]
        cases hd : dropVal extra cv ⟨F :: (A' ++ [P]), m⟩ with
        | none => exact ⟨rfl, trivial⟩
        | some s' =>
          rw [hd] at hd2
          obtain ⟨c', P', rfl, hc', hlen, hnx⟩ := hd2
          simp only [Option.map_some, Option.bind_some, St.frameMap_app]
          dsimp only at h2 hlen hnx
          simp only [List.length_cons] at h2 hlen
          have := ih c' P' hc' (by omega)
          refine ⟨this.1, ?_⟩
          have h3 := this.2
          cases hp : popFrameN extra n (c'.app [P']) with
          | none => trivial
          | some s'' =>
            rw [hp] at h3
            obtain ⟨c'', P'', rfl, hc'', hl'', hn''⟩ := h3
            exact ⟨c'', P'', rfl, hc'', by simp only [List.length_cons]; omega, by omega⟩

/-- The commutation half of `popFrameN_frame` also holds when the popped frame is the last
core frame (the core becomes empty: this is the pop that ends a call run in isolation). -/
theorem popFrameN_frame1 (extra : Val) :
    ∀ (n : Nat) (c : St) (P : Frame), PInv Ω₂ K c P →
      popFrameN extra n (c.app (Ω₂.substPorts K P)) = (popFrameN extra n (c.app [P])).map (frameMap K Ω₂) := by
  intro n
  induction n with
  | zero =>
    intro c P hc
    obtain ⟨Ω, m⟩ := c
    rcases Ω with _ | ⟨F, A'⟩
    · exact absurd rfl hc.ne
    · cases F with
      | nil => simp [popFrameN, St.app, frameMap]
      | cons b F => rfl
  | succ n ih =>
    intro c P hc
    obtain ⟨Ω, m⟩ := c
    rcases Ω with _ | ⟨F, A'⟩
    · exact absurd rfl hc.ne
    · cases F with
      | nil => rfl
      | cons b F =>
        obtain ⟨y, cv⟩ := b
        simp only [popFrameN, St.app, List.cons_append]
        have hsub : ∀ x ∈ Env.names (F :: A'), x ∈ Env.names (((y, cv) :: F) :: A') := by
          intro x hx
          simp only [Env.mem_names] at hx ⊢
          obtain ⟨G, hG, b, hb, h⟩ := hx
          rcases List.mem_cons.mp hG with hGF | hG
          · subst hGF; exact ⟨(y, cv) :: G, List.mem_cons_self .., b, List.mem_cons_of_mem _ hb, h⟩
          · exact ⟨G, List.mem_cons_of_mem _ hG, b, hb, h⟩
        have hc0 : PInv Ω₂ K ⟨F :: A', m⟩ P := hc.shrink (by simp) hsub (Nat.le_refl _)
        have hcv : ∀ l ∈ cv.names, Good Ω₂ K l := fun l hl =>
          hc.good l (by
            simp only [Env.mem_names]
            exact ⟨((y, cv) :: F), List.mem_cons_self .., (y, cv), List.mem_cons_self .., hl⟩)
        obtain ⟨hd1, hd2⟩ := dropVal_frame (c := ⟨F :: A', m⟩) hc0 hcv extra
        simp only [St.app, List.cons_append] at hd1 hd2
        rw [hd1]
        cases hd : dropVal extra cv ⟨F :: (A' ++ [P]), m⟩ with
        | none => rfl
        | some s' =>
          rw [hd] at hd2
          obtain ⟨c', P', rfl, hc', _, _⟩ := hd2
          simp only [Option.map_some, Option.bind_some, St.frameMap_app]
          exact ih c' P' hc'

theorem popFrame_frame (extra : Val) {c : St} {P : Frame} (hc : PInv Ω₂ K c P) (h2 : 2 ≤ c.env.length) :
    popFrame extra (c.app (Ω₂.substPorts K P)) = (popFrame extra (c.app [P])).map (frameMap K Ω₂) ∧
    PSt Ω₂ K (c.env.length - 1) c.next (popFrame extra (c.app [P])) := by
  have hh : ∀ X : Env, (c.app X).env.head? = c.env.head? := by
    intro X; obtain ⟨Ω, m⟩ := c; cases Ω with
    | nil => simp at h2
    | cons F A => rfl
  unfold popFrame
  rw [hh, hh]
  exact popFrameN_frame extra _ c P hc h2

end
end OchrMeta
