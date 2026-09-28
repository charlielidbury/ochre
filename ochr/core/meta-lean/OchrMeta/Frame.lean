import OchrMeta.FrameCall

/-! # T2a (frame lemma, locality) and T2b (call effect)

`exec` from `Ω₁ ++ Ω₂` is `exec` from `Ω₁ ++ [ports]`, with the ports' final values substituted
into `Ω₂` (`frameMap`).  The proof is one induction on fuel; every clause of `exec` is a
composition of the primitive commutations proved in `FrameOps*`/`FrameCall`. -/

namespace OchrMeta

section
variable {Ω₂ : Env} {K : List Nat}

/-- Full-side result `rf` is the port-side result `rp` seen through `frameMap`. -/
def Sim (Ω₂ : Env) (K : List Nat) (len : Nat) (rf rp : Res) : Prop :=
  rf = rp.map (frameMap K Ω₂) ∧ PRes Ω₂ K len rp

theorem Sim.bind {len len' : Nat} {rf rp : Res} (h : Sim Ω₂ K len rf rp) {k : St → Val → Res}
    (hk : ∀ c' P' v, PInv Ω₂ K c' P' → c'.env.length = len → (∀ l ∈ v.names, Good Ω₂ K l) →
      Sim Ω₂ K len' (k (c'.app (Ω₂.substPorts K P')) v) (k (c'.app [P']) v)) :
    Sim Ω₂ K len' (rf.bind k) (rp.bind k) := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  cases rp with
  | ok s v =>
    obtain ⟨c', P', rfl, hc', hlen, hv⟩ := h2
    simp only [Res.map_ok, Res.bind_ok, St.frameMap_app]
    exact hk c' P' v hc' hlen hv
  | _ => exact ⟨rfl, trivial⟩

theorem Sim.ok {c : St} {P : Frame} (hc : PInv Ω₂ K c P) {v : Val} (hv : ∀ l ∈ v.names, Good Ω₂ K l) :
    Sim Ω₂ K c.env.length (.ok (c.app (Ω₂.substPorts K P)) v) (.ok (c.app [P]) v) :=
  ⟨by simp [St.frameMap_app], c, P, rfl, hc, rfl, hv⟩

theorem Sim.ok' {c : St} {P : Frame} (hc : PInv Ω₂ K c P) {len : Nat} (hl : c.env.length = len)
    {v : Val} (hv : ∀ l ∈ v.names, Good Ω₂ K l) :
    Sim Ω₂ K len (.ok (c.app (Ω₂.substPorts K P)) v) (.ok (c.app [P]) v) :=
  hl ▸ Sim.ok hc hv

theorem Sim.same {len : Nat} {r : Res} (h : ∀ s v, r ≠ .ok s v) : Sim Ω₂ K len r r := by
  cases r with
  | ok s v => exact absurd rfl (h s v)
  | _ => exact ⟨rfl, trivial⟩

/-- Option-valued state steps. -/
theorem Sim.optBind {len : Nat} {c : St} {of op : Option St} {len' : Nat}
    (h1 : of = op.map (frameMap K Ω₂)) (h2 : PSt Ω₂ K len' c.next op) {k : St → Res} {kerr : Res}
    (hkerr : Sim Ω₂ K len kerr kerr)
    (hk : ∀ c' P', PInv Ω₂ K c' P' → c'.env.length = len' →
      Sim Ω₂ K len (k (c'.app (Ω₂.substPorts K P'))) (k (c'.app [P']))) :
    Sim Ω₂ K len (of.elim kerr k) (op.elim kerr k) := by
  subst h1
  cases op with
  | none => exact hkerr
  | some s =>
    obtain ⟨c', P', rfl, hc', hlen, _⟩ := h2
    simp only [Option.map_some, St.frameMap_app]
    exact hk c' P' hc' hlen

theorem Sim.err {len : Nat} : Sim Ω₂ K len .err .err := ⟨rfl, trivial⟩
theorem Sim.stuck {len : Nat} : Sim Ω₂ K len .stuck .stuck := ⟨rfl, trivial⟩

theorem access_sim (deep : Bool) (x : Var) (π : List Proj) {c : St} {P : Frame} (hc : PInv Ω₂ K c P) :
    Sim Ω₂ K c.env.length (access deep x π (c.app (Ω₂.substPorts K P))) (access deep x π (c.app [P])) :=
  access_frame deep x π _ c P rfl hc

theorem PInv.setPlace {c c' : St} {P : Frame} (hc : PInv Ω₂ K c P) {x : Var} {π : List Proj} {v : Val}
    (hv : ∀ l ∈ v.names, Good Ω₂ K l) (h : c.setPlace x π v = some c') :
    PInv Ω₂ K c' P ∧ c'.env.length = c.env.length ∧ c'.next = c.next := by
  obtain ⟨hn, hl, hx⟩ := St.setPlace_spec h
  exact ⟨hc.grow (Env.ne_nil_of_length hl hc.ne) (S := fun l => l ∈ v.names) hv hn (hx ▸ Nat.le_refl _), hl, hx⟩

/-- `setPlace` as a port-side `Option` step. -/
theorem setPlace_sim {c : St} {P : Frame} (hc : PInv Ω₂ K c P) (x : Var) (π : List Proj) {v : Val}
    (hv : ∀ l ∈ v.names, Good Ω₂ K l) :
    (c.app (Ω₂.substPorts K P)).setPlace x π v = ((c.app [P]).setPlace x π v).map (frameMap K Ω₂) ∧
    PSt Ω₂ K c.env.length c.next ((c.app [P]).setPlace x π v) := by
  rw [St.setPlace_app _ hc.ne, St.setPlace_app _ hc.ne]
  cases h : c.setPlace x π v with
  | none => exact ⟨rfl, trivial⟩
  | some c' =>
    obtain ⟨hc', hl, hx⟩ := hc.setPlace hv h
    exact ⟨by simp [St.frameMap_app], c', P, rfl, hc', hl, hx ▸ Nat.le_refl _⟩

theorem unbind_sim {c : St} {P : Frame} (hc : PInv Ω₂ K c P) (x : Var) :
    (c.app (Ω₂.substPorts K P)).unbind x = ((c.app [P]).unbind x).map (fun p => (p.1, frameMap K Ω₂ p.2)) ∧
    ∀ v s', (c.app [P]).unbind x = some (v, s') → ∃ c', s' = c'.app [P] ∧ PInv Ω₂ K c' P ∧
      c'.env.length = c.env.length ∧ c'.next = c.next ∧ ∀ l ∈ v.names, Good Ω₂ K l := by
  rw [St.unbind_app _ hc.ne, St.unbind_app _ hc.ne]
  cases h : c.unbind x with
  | none => exact ⟨rfl, by simp⟩
  | some p =>
    obtain ⟨v, c'⟩ := p
    obtain ⟨hn, hnv, hl, hx⟩ := St.unbind_spec h
    refine ⟨by simp [St.frameMap_app], ?_⟩
    intro v' s' h'
    simp at h'; obtain ⟨rfl, rfl⟩ := h'
    exact ⟨c', rfl, hc.shrink (Env.ne_nil_of_length hl hc.ne) hn (hx ▸ Nat.le_refl _), hl, hx,
      fun l hl' => hc.good l (hnv l hl')⟩

theorem exec_frame (Pr : Prog) : ∀ n, EvF Ω₂ K (exec Pr n) := by
  intro n
  induction n with
  | zero => intro c P t hc; exact ⟨rfl, trivial⟩
  | succ n ih =>
    intro c P t hc
    show Sim Ω₂ K c.env.length _ _
    cases t with
    | read p =>
      simp only [exec]
      apply Sim.bind (access_sim true _ _ hc)
      intro c' P' v hc' hlen hv
      cases v with
      | moved => exact Sim.err
      | borrow l w =>
        obtain ⟨h1, h2⟩ := setPlace_sim hc' p.root p.path (v := .moved) (by simp [Val.names])
        dsimp only
        rw [h1]
        cases hop : St.setPlace p.root p.path Val.moved (c'.app [P']) with
        | none => exact Sim.err
        | some s =>
          rw [hop] at h2
          obtain ⟨c'', P'', rfl, hc'', hl'', _⟩ := h2
          simp only [Option.map_some, St.frameMap_app]
          exact Sim.ok' hc'' (by omega) hv
      | _ => exact Sim.ok' hc' hlen hv
    | borrow p =>
      simp only [exec]
      apply Sim.bind (access_sim true _ _ hc)
      intro c' P' v hc' hlen hv
      simp only [St.app_next]
      by_cases hcond : v = .moved ∨ v.nb ≠ 0
      · rw [if_pos hcond, if_pos hcond]; exact Sim.err
      · rw [if_neg hcond, if_neg hcond]
        have hk : Good Ω₂ K c'.next := hc'.fresh _ (Nat.le_refl _)
        obtain ⟨h1, h2⟩ := setPlace_sim hc' p.root p.path (v := .loan c'.next)
          (by intro l hl; simp [Val.names] at hl; subst hl; exact hk)
        rw [h1]
        cases hop : St.setPlace p.root p.path (.loan c'.next) (c'.app [P']) with
        | none => exact Sim.err
        | some s =>
          rw [hop] at h2
          obtain ⟨c'', P'', rfl, hc'', hl'', _⟩ := h2
          simp only [Option.map_some, St.frameMap_app]
          have e : ∀ X, ({ c''.app X with next := c'.next + 1 } : St) = (⟨c''.env, c'.next + 1⟩ : St).app X :=
            fun X => rfl
          rw [e, e]
          have hc3 : PInv Ω₂ K ⟨c''.env, c'.next + 1⟩ P'' :=
            ⟨hc''.ne, hc''.pnb, hc''.keys, hc''.good, fun l hl => hc'.fresh l (by simp at hl; omega)⟩
          refine Sim.ok' hc3 (by simp; omega) ?_
          intro l hl
          simp only [Val.names, List.mem_cons] at hl
          rcases hl with rfl | hl
          · exact hk
          · exact hv l hl
    | assign p t =>
      simp only [exec]
      apply Sim.bind (ih c P t hc)
      intro c1 P1 v hc1 hlen1 hv
      apply Sim.bind (access_sim true _ _ hc1)
      intro c2 P2 w hc2 hlen2 hw
      by_cases hnb : p.path ≠ [] ∧ v.nb ≠ 0
      · rw [if_pos hnb, if_pos hnb]; exact Sim.err
      rw [if_neg hnb, if_neg hnb]
      obtain ⟨h1, h2⟩ := setPlace_sim hc2 p.root p.path hv
      rw [h1]
      cases hop : St.setPlace p.root p.path v (c2.app [P2]) with
      | none => exact Sim.err
      | some s =>
        rw [hop] at h2
        obtain ⟨c3, P3, rfl, hc3, hl3, _⟩ := h2
        simp only [Option.map_some, St.frameMap_app]
        obtain ⟨d1, d2⟩ := dropVal_frame hc3 hw .unit
        rw [d1]
        cases hd : dropVal .unit w (c3.app [P3]) with
        | none => exact Sim.err
        | some s' =>
          rw [hd] at d2
          obtain ⟨c4, P4, rfl, hc4, hl4, _⟩ := d2
          simp only [Option.map_some, St.frameMap_app]
          exact Sim.ok' hc4 (by omega) (by simp [Val.names])
    | letIn x t u =>
      simp only [exec]
      apply Sim.bind (ih c P t hc)
      intro c1 P1 v hc1 hlen1 hv
      rw [St.bind_app _ hc1.ne, St.bind_app _ hc1.ne]
      have hb := ih (c1.bind x v) P1 u (hc1.bind x hv)
      rw [St.length_bind hc1.ne, hlen1] at hb
      apply Sim.bind hb
      intro c2 P2 w hc2 hlen2 hw
      obtain ⟨u1, u2⟩ := unbind_sim hc2 x
      rw [u1]
      cases hu : (c2.app [P2]).unbind x with
      | none => exact Sim.err
      | some q =>
        obtain ⟨cv, s3⟩ := q
        obtain ⟨c3, rfl, hc3, hl3, _, hcv⟩ := u2 cv s3 hu
        simp only [Option.map_some, St.frameMap_app]
        obtain ⟨d1, d2⟩ := dropVal_frame hc3 hcv w
        rw [d1]
        cases hd : dropVal w cv (c3.app [P2]) with
        | none => exact Sim.err
        | some s' =>
          rw [hd] at d2
          obtain ⟨c4, P4, rfl, hc4, hl4, _⟩ := d2
          simp only [Option.map_some, St.frameMap_app]
          exact Sim.ok' hc4 (by omega) hw
    | seq t u =>
      simp only [exec]
      apply Sim.bind (ih c P t hc)
      intro c1 P1 v hc1 hlen1 hv
      obtain ⟨d1, d2⟩ := dropVal_frame hc1 hv .unit
      rw [d1]
      cases hd : dropVal .unit v (c1.app [P1]) with
      | none => exact Sim.err
      | some s' =>
        rw [hd] at d2
        obtain ⟨c2, P2, rfl, hc2, hl2, _⟩ := d2
        simp only [Option.map_some, St.frameMap_app]
        have := ih c2 P2 u hc2
        rwa [hl2, hlen1] at this
    | zero => exact Sim.ok hc (by simp [Val.names])
    | unit => exact Sim.ok hc (by simp [Val.names])
    | erase t => exact Sim.ok hc (by simp [Val.names])
    | succ t =>
      simp only [exec]
      apply Sim.bind (ih c P t hc)
      intro c1 P1 v hc1 hlen1 hv
      by_cases hnb : v.nb = 0
      · rw [if_pos hnb, if_pos hnb]; exact Sim.ok' hc1 hlen1 (by simpa [Val.names] using hv)
      · rw [if_neg hnb, if_neg hnb]; exact Sim.err
    | pair t u =>
      simp only [exec]
      apply Sim.bind (ih c P t hc)
      intro c1 P1 v hc1 hlen1 hv
      have := ih c1 P1 u hc1
      rw [hlen1] at this
      apply Sim.bind this
      intro c2 P2 w hc2 hlen2 hw
      by_cases hnb : v.nb = 0 ∧ w.nb = 0
      rotate_left
      · rw [if_neg hnb, if_neg hnb]; exact Sim.err
      rw [if_pos hnb, if_pos hnb]
      refine Sim.ok' hc2 hlen2 ?_
      intro l hl
      simp only [Val.names, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hv l hl
      · exact hw l hl
    | mtch p tz y ts =>
      simp only [exec]
      apply Sim.bind (access_sim false _ _ hc)
      intro c' P' v hc' hlen hv
      cases v with
      | zero => have := ih c' P' tz hc'; rwa [hlen] at this
      | succ w => have := ih c' P' (ts.substVar y (.fst p)) hc'; rwa [hlen] at this
      | _ => simp only [Val.isNeutral]; first | exact Sim.stuck | exact Sim.err
    | call f args cc =>
      simp only [exec]
      cases hf : Pr.find f with
      | none => exact Sim.err
      | some d =>
        dsimp only
        by_cases hp : d.ret = .prop
        · rw [if_pos hp, if_pos hp]; exact Sim.ok hc (by simp [Val.names])
        · rw [if_neg hp, if_neg hp]
          apply Sim.bind (execArgs_frame ih args 0 c P hc)
          intro c1 P1 _ hc1 hlen1 _
          obtain ⟨t1, t2⟩ := takeTemps_frame (List.range args.length) c1 P1 hc1
          rw [t1]
          cases ht : takeTemps (List.range args.length) (c1.app [P1]) with
          | none => exact Sim.err
          | some q =>
            obtain ⟨ws, s2⟩ := q
            obtain ⟨c2, P2, rfl, hc2, hl2, _, hws⟩ := t2 ws s2 ht
            simp only [Option.map_some, St.frameMap_app]
            have := callWith_frame ih cc f d hc2 hws
            rwa [hl2, hlen1] at this

end

/-! ## Membership lemmas for the statement -/

theorem Val.names_cases {v : Val} {l : Nat} (h : l ∈ v.names) : l ∈ v.loans ∨ l ∈ v.borrows := by
  induction v <;> simp_all [Val.names, Val.loans, Val.borrows] <;> grind

theorem Frame.mem_borrows {F : Frame} {l : Nat} : l ∈ F.borrows ↔ ∃ b ∈ F, l ∈ b.2.borrows := by
  induction F with
  | nil => simp [Frame.borrows]
  | cons b F ih => obtain ⟨x, v⟩ := b; simp [Frame.borrows, ih]

theorem Frame.mem_loans' {F : Frame} {l : Nat} : l ∈ F.loans ↔ ∃ b ∈ F, l ∈ b.2.loans := by
  induction F with
  | nil => simp [Frame.loans]
  | cons b F ih => obtain ⟨x, v⟩ := b; simp [Frame.loans, ih]

theorem Env.mem_borrows {Ω : Env} {l : Nat} : l ∈ Ω.borrows ↔ ∃ F ∈ Ω, ∃ b ∈ F, l ∈ b.2.borrows := by
  induction Ω with
  | nil => simp [Env.borrows]
  | cons F Ω ih => simp [Env.borrows, ih, Frame.mem_borrows]

theorem Env.mem_loans' {Ω : Env} {l : Nat} : l ∈ Ω.loans ↔ ∃ F ∈ Ω, ∃ b ∈ F, l ∈ b.2.loans := by
  induction Ω with
  | nil => simp [Env.loans]
  | cons F Ω ih => simp [Env.loans, ih, Frame.mem_loans']

theorem Env.names_cases {Ω : Env} {l : Nat} (h : l ∈ Ω.names) : l ∈ Ω.loans ∨ l ∈ Ω.borrows := by
  rw [Env.mem_names] at h
  obtain ⟨F, hF, b, hb, hl⟩ := h
  rcases Val.names_cases hl with h | h
  · exact Or.inl (Env.mem_loans'.mpr ⟨F, hF, b, hb, h⟩)
  · exact Or.inr (Env.mem_borrows.mpr ⟨F, hF, b, hb, h⟩)

theorem Env.loans_sub_names {Ω : Env} {l : Nat} (h : l ∈ Ω.loans) : l ∈ Ω.names := by
  obtain ⟨F, hF, b, hb, hl⟩ := Env.mem_loans'.mp h
  exact Env.mem_names.mpr ⟨F, hF, b, hb, Val.loans_sub_names hl⟩

theorem Env.holds_sub_names {Ω : Env} {l : Nat} (h : Ω.holds l = true) : l ∈ Ω.names := by
  simp only [Env.holds, List.any_eq_true, Frame.holds] at h
  obtain ⟨F, hF, b, hb, hl⟩ := h
  rw [Env.mem_names]
  refine ⟨F, hF, b, hb, ?_⟩
  cases hv : b.2 <;> simp_all [Val.isBorrowOf, Val.names]

theorem lookup_portList (K : List Nat) :
    ∀ (n i : Nat), (List.map (fun p : Nat × Nat => (Var.port p.2, Val.loan p.1)) (K.zipIdx n)).lookup
      (Var.port (i + n)) = K[i]?.map Val.loan := by
  induction K with
  | nil => intro n i; simp
  | cons k K ih =>
    intro n i
    simp only [List.zipIdx_cons, List.map_cons, List.lookup_cons]
    cases i with
    | zero => simp
    | succ i =>
      have hne : (Var.port (i + 1 + n) == Var.port n) = false := by simp
      rw [hne]
      simp only [Bool.false_eq_true, if_false, List.getElem?_cons_succ]
      rw [show i + 1 + n = i + (n + 1) by omega]
      exact ih (n + 1) i

theorem portSub_portsOf (Ω : Env) (l : Nat) :
    portSub Ω.portKeys (Env.portsOf Ω) l = if l ∈ Ω.borrows then some (.loan l) else none := by
  simp only [portSub, Env.portsOf]
  by_cases hl : l ∈ Ω.borrows
  · rw [if_pos hl]
    have hK : l ∈ Ω.portKeys := hl
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hK)
    rw [hi]
    obtain ⟨hlt, hget, _⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [Option.bind_some]
    have := lookup_portList Ω.portKeys 0 i
    simp only [Nat.add_zero] at this
    rw [this, List.getElem?_eq_getElem hlt, hget]; rfl
  · rw [if_neg hl]
    have hK : l ∉ Ω.portKeys := hl
    rw [List.idxOf?_eq_none_iff.mpr hK]; rfl

theorem portsOf_nb (Ω : Env) : Frame.nb (Env.portsOf Ω) = 0 := by
  simp only [Env.portsOf]
  generalize Ω.portKeys = K
  suffices ∀ n, Frame.nb (List.map (fun p : Nat × Nat => (Var.port p.2, Val.loan p.1)) (K.zipIdx n)) = 0 from this 0
  induction K with
  | nil => intro n; rfl
  | cons k K ih => intro n; simp [List.zipIdx_cons, Frame.nb, Val.nb, ih]

theorem substPorts_portsOf (Ω₁ Ω₂ : Env) : Ω₂.substPorts Ω₁.portKeys (Env.portsOf Ω₁) = Ω₂ := by
  have hid : ∀ v : Val, v.substSim (portSub Ω₁.portKeys (Env.portsOf Ω₁)) = v := by
    apply Val.substSim_id
    intro l; rw [portSub_portsOf]; split <;> simp
  simp only [Env.substPorts, Env.mapVals]
  conv => rhs; rw [← List.map_id Ω₂]
  apply List.map_congr_left
  intro F _
  conv => rhs; rw [← List.map_id F]
  apply List.map_congr_left
  intro b _
  simp [hid]

/-! ## T2a: locality -/

/-- The initial port-side state satisfies the invariant. -/
theorem pinv_init {Ω₁ Ω₂ : Env} {next : Nat} (hne : Ω₁ ≠ [])
    (hheld : ∀ l ∈ Ω₁.names, Ω₂.holds l = false)
    (hshared : ∀ l ∈ Ω₁.loans, l ∈ Ω₂.loans → l ∈ Ω₁.borrows)
    (hfresh : ∀ l ∈ Ω₂.names, l < next) :
    PInv Ω₂ Ω₁.portKeys ⟨Ω₁, next⟩ (Env.portsOf Ω₁) where
  ne := hne
  pnb := portsOf_nb Ω₁
  keys := by
    intro l hl; rw [portSub_portsOf]
    simp only [Env.portKeys] at hl; simp [hl]
  good := by
    intro l hl
    refine ⟨hheld l hl, fun h2 => ?_⟩
    simp only [Env.portKeys]
    rcases Env.names_cases hl with h | h
    · exact hshared l h h2
    · exact h
  fresh := by
    intro l hl
    have hn : l ∉ Ω₂.names := fun h => by have := hfresh l h; simp at hl; omega
    refine ⟨?_, fun h2 => absurd (Env.loans_sub_names h2) hn⟩
    cases h : Ω₂.holds l
    · rfl
    · exact absurd (Env.holds_sub_names h) hn

/-- **T2a (frame lemma, locality).**  A run from `Ω₁ ++ Ω₂` is the run from `Ω₁` alone (over a
frame of *ports*, one per borrow of `Ω₁`, each initially holding its own loan), after which the
ports' final contents are substituted for the corresponding loans in `Ω₂` (`frameMap`); `stuck`,
`err` and `oof` are identical.  Hypotheses: `Ω₁` is non-empty (it contains the top frame); no
name of `Ω₁` is held in `Ω₂` (loan-closedness plus unique holders); a loan occurring in both
belongs to a borrow of `Ω₁`; the fresh-name counter is above every name of `Ω₂`. -/
theorem frame_local (Pr : Prog) (n : Nat) {Ω₁ Ω₂ : Env} {next : Nat} (t : Term)
    (hne : Ω₁ ≠ [])
    (hheld : ∀ l ∈ Ω₁.names, Ω₂.holds l = false)
    (hshared : ∀ l ∈ Ω₁.loans, l ∈ Ω₂.loans → l ∈ Ω₁.borrows)
    (hfresh : ∀ l ∈ Ω₂.names, l < next) :
    exec Pr n ⟨Ω₁ ++ Ω₂, next⟩ t = (exec Pr n ⟨Ω₁ ++ [Env.portsOf Ω₁], next⟩ t).map (frameMap Ω₁.portKeys Ω₂) := by
  have h := (exec_frame Pr n ⟨Ω₁, next⟩ (Env.portsOf Ω₁) t (pinv_init hne hheld hshared hfresh)).1
  rw [substPorts_portsOf] at h
  exact h

/-- T2a for `Eval`. -/
theorem frame_local_eval (Pr : Prog) {Ω₁ Ω₂ : Env} {next : Nat} (t : Term) (r : Res)
    (hne : Ω₁ ≠ [])
    (hheld : ∀ l ∈ Ω₁.names, Ω₂.holds l = false)
    (hshared : ∀ l ∈ Ω₁.loans, l ∈ Ω₂.loans → l ∈ Ω₁.borrows)
    (hfresh : ∀ l ∈ Ω₂.names, l < next) :
    Eval Pr ⟨Ω₁ ++ Ω₂, next⟩ t r ↔
      ∃ r₁, Eval Pr ⟨Ω₁ ++ [Env.portsOf Ω₁], next⟩ t r₁ ∧ r = r₁.map (frameMap Ω₁.portKeys Ω₂) := by
  constructor
  · rintro ⟨hr, n, hn⟩
    rw [frame_local Pr n t hne hheld hshared hfresh] at hn
    refine ⟨exec Pr n ⟨Ω₁ ++ [Env.portsOf Ω₁], next⟩ t, ⟨?_, n, rfl⟩, hn.symm⟩
    intro h; rw [h] at hn; exact hr hn.symm
  · rintro ⟨r₁, ⟨hr, n, hn⟩, rfl⟩
    refine ⟨?_, n, ?_⟩
    · cases r₁ <;> simp_all
    · rw [frame_local Pr n t hne hheld hshared hfresh, hn]

/-! ## T2b: the effect of a call -/

/-- A call run in isolation (the meta-model's `CallRun`): the body from the parameter frame
over one port per borrow argument (this is the generic call environment `G(d̄)`, the ports
being the owners `cᵢ`), then the frame pop.  An `ok` result leaves only the ports frame, whose
contents are the final contents of the borrowed places. -/
def callRun (Pr : Prog) (n : Nat) (d : FunDef) (b : Term) (ws : List Val) (next : Nat) : Res :=
  (exec Pr n ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], next⟩ b).bind fun s v =>
    match popFrame v s with
    | none => .err
    | some s' => .ok s' v

theorem paramFrame_mem {d : FunDef} {ws : List Val} (hlen : ws.length = d.params.length)
    {w : Val} (hw : w ∈ ws) : ∃ x, (x, w) ∈ paramFrame d ws := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hi' : i < (d.params.map Prod.fst).length := by simp; omega
  refine ⟨(d.params.map Prod.fst)[i], ?_⟩
  have : ((d.params.map Prod.fst).zip ws)[i]'(by simp; omega) = ((d.params.map Prod.fst)[i], ws[i]) := by
    simp
  rw [← this]
  exact List.getElem_mem _

/-- **T2b (call effect).**  After its arguments are evaluated (values `ws`, from state `s`), a
call whose body terminates affects its caller exactly as its isolated run `callRun` says: the
caller's environment with each borrow argument's loan replaced by that borrow's final content
(`frameMap s.env` substitutes the final ports into `s.env`).  A stuck body is closed off from
the call point `s` ([Close]).  Hypotheses: the argument values' names are not held by the
caller, a loan of an argument that also occurs in the caller belongs to a borrow argument, and
the counter is fresh for the caller. -/
theorem call_effect (Pr : Prog) (n : Nat) (cc : Bool) (f : String) {d : FunDef} {b : Term}
    (hb : d.body = some b) {ws : List Val} (hlen : ws.length = d.params.length) (s : St)
    (hheld : ∀ w ∈ ws, ∀ l ∈ w.names, s.env.holds l = false)
    (hshared : ∀ w ∈ ws, ∀ l ∈ w.loans, l ∈ s.env.loans → ∃ w' ∈ ws, l ∈ w'.borrows)
    (hfresh : ∀ l ∈ s.env.names, l < s.next) :
    callWith (exec Pr n) cc f d ws s =
      match callRun Pr n d b ws s.next with
      | .ok s' v => .ok (frameMap (Env.portKeys [paramFrame d ws]) s.env s') v
      | .stuck => if cc then closeCall f d ws s else .stuck
      | .err => .err
      | .oof => .oof := by
  have hne : ([paramFrame d ws] : Env) ≠ [] := by simp
  have hh : ∀ l ∈ Env.names [paramFrame d ws], s.env.holds l = false := by
    intro l hl
    rw [Env.mem_names] at hl
    obtain ⟨F, hF, bb, hbb, hl⟩ := hl
    simp at hF; subst hF
    exact hheld bb.2 (List.of_mem_zip hbb).2 l hl
  have hs : ∀ l ∈ Env.loans [paramFrame d ws], l ∈ s.env.loans → l ∈ Env.borrows [paramFrame d ws] := by
    intro l hl h2
    obtain ⟨F, hF, bb, hbb, hl⟩ := Env.mem_loans'.mp hl
    simp at hF; subst hF
    obtain ⟨w', hw', hlw⟩ := hshared bb.2 (List.of_mem_zip hbb).2 l hl h2
    obtain ⟨x, hx⟩ := paramFrame_mem hlen hw'
    exact Env.mem_borrows.mpr ⟨_, by simp, (x, w'), hx, hlw⟩
  have hinv := pinv_init (next := s.next) hne hh hs hfresh
  have hfr := exec_frame (Ω₂ := s.env) Pr n ⟨[paramFrame d ws], s.next⟩ (Env.portsOf [paramFrame d ws]) b hinv
  rw [substPorts_portsOf] at hfr
  obtain ⟨h1, h2⟩ := hfr
  unfold callWith callRun
  rw [hb]
  simp only [hlen, if_true]
  have e : s.push (paramFrame d ws) = (⟨[paramFrame d ws], s.next⟩ : St).app s.env := rfl
  have e2 : (⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], s.next⟩ : St) =
      (⟨[paramFrame d ws], s.next⟩ : St).app [Env.portsOf [paramFrame d ws]] := rfl
  rw [e, h1, e2]
  cases hr : exec Pr n ((⟨[paramFrame d ws], s.next⟩ : St).app [Env.portsOf [paramFrame d ws]]) b with
  | ok s' v =>
    rw [hr] at h2
    obtain ⟨c', P', rfl, hc', _, _⟩ := h2
    simp only [Res.map_ok, Res.bind_ok, St.frameMap_app]
    unfold popFrame
    have hhd : ∀ X : Env, (c'.app X).env.head? = c'.env.head? := by
      intro X; obtain ⟨Ω, m⟩ := c'; cases Ω with
      | nil => exact absurd rfl hc'.ne
      | cons F A => rfl
    rw [hhd, hhd, popFrameN_frame1 (Ω₂ := s.env) v _ c' P' hc']
    cases popFrameN v ((c'.env.head?.map List.length).getD 0) (c'.app [P']) <;> rfl
  | stuck => rfl
  | err => rfl
  | oof => rfl

end OchrMeta
