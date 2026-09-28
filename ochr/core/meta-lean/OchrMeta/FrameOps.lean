import OchrMeta.FrameAlg

/-! # Frame lemma, part 1: each primitive operation commutes with `frameMap` -/

namespace OchrMeta

/-! ## Occurrence lemmas -/

theorem Frame.mem_loans {F : Frame} {b : Var × Val} {m : Nat}
    (hb : b ∈ F) (hm : m ∈ b.2.loans) : m ∈ F.loans := by
  induction F with
  | nil => simp at hb
  | cons c F ihF =>
    obtain ⟨x, v⟩ := c
    simp only [Frame.loans, List.mem_append]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl hm
    · exact Or.inr (ihF hb)

theorem Env.mem_loans {Ω : Env} {F : Frame} {b : Var × Val} {m : Nat}
    (hF : F ∈ Ω) (hb : b ∈ F) (hm : m ∈ b.2.loans) : m ∈ Ω.loans := by
  induction Ω with
  | nil => simp at hF
  | cons G Ω ih =>
    simp only [Env.loans, List.mem_append]
    rcases List.mem_cons.mp hF with rfl | hF
    · exact Or.inl (Frame.mem_loans hb hm)
    · exact Or.inr (ih hF)

theorem Val.loans_sub_names {v : Val} {l : Nat} (h : l ∈ v.loans) : l ∈ v.names := by
  induction v <;> simp_all [Val.loans, Val.names] <;> grind

theorem Val.not_isBorrowOf_of_nb {v : Val} (h : v.nb = 0) (l : Nat) : v.isBorrowOf l = false := by
  cases v <;> simp_all [Val.nb, Val.isBorrowOf]

theorem Frame.holds_of_nb {P : Frame} (h : P.nb = 0) (l : Nat) : P.holds l = false := by
  induction P with
  | nil => rfl
  | cons b P ih =>
    obtain ⟨x, v⟩ := b
    simp only [Frame.nb] at h
    simp only [Frame.holds, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
    exact ⟨Val.not_isBorrowOf_of_nb (by omega) l, ih (by omega)⟩

theorem Frame.nb_of_lookup {P : Frame} (h : P.nb = 0) {x : Var} {p : Val} (hp : P.lookup x = some p) :
    p.nb = 0 := by
  induction P with
  | nil => simp at hp
  | cons b P ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.nb] at h
    simp only [List.lookup_cons] at hp
    split at hp
    · cases hp; omega
    · exact ih (by omega) hp

/-! ## Liveness below the core -/

theorem Env.holds_append (A X : Env) (l : Nat) : Env.holds l (A ++ X) = (A.holds l || X.holds l) := by
  simp [Env.holds, List.any_append]

theorem Env.holds_single (P : Frame) (l : Nat) : Env.holds l [P] = P.holds l := by
  simp [Env.holds]

theorem Val.isBorrowOf_substSim (σ : Nat → Option Val) (hσ : ∀ m p, σ m = some p → p.nb = 0)
    (v : Val) (l : Nat) : (v.substSim σ).isBorrowOf l = v.isBorrowOf l := by
  cases v with
  | loan m =>
    simp only [Val.substSim]
    cases h : σ m with
    | none => rfl
    | some p =>
      simp only [Option.getD_some]
      rw [Val.not_isBorrowOf_of_nb (hσ m p h) l]; rfl
  | _ => rfl

theorem Frame.holds_mapVals_substSim {σ : Nat → Option Val} (hσ : ∀ m p, σ m = some p → p.nb = 0)
    (F : Frame) (l : Nat) : Frame.holds l (F.mapVals (Val.substSim σ)) = F.holds l := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    simp only [Frame.holds, Frame.mapVals, List.map_cons, List.any_cons] at ih ⊢
    rw [ih, Val.isBorrowOf_substSim σ hσ]

theorem Env.holds_substPorts {P : Frame} (hP : P.nb = 0) (Ω : Env) (l : Nat) :
    Env.holds l (Ω.substPorts P) = Ω.holds l := by
  have hσ : ∀ m p, portSub P m = some p → p.nb = 0 := fun m p h => Frame.nb_of_lookup hP h
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.substPorts, Env.mapVals, Env.holds, List.map_cons, List.any_cons] at ih ⊢
    rw [ih, Frame.holds_mapVals_substSim hσ]

/-! ## Liveness only matters on the loans that are looked at -/

theorem Val.firstLive_congr {f g : Nat → Bool} :
    ∀ v : Val, (∀ l ∈ v.loans, f l = g l) → v.firstLive f = v.firstLive g := by
  intro v h
  induction v with
  | loan m => simp_all [Val.firstLive, Val.loans]
  | succ v ih => exact ih (by simpa [Val.loans] using h)
  | borrow m v ih => exact ih (by simpa [Val.loans] using h)
  | pair a b iha ihb =>
    simp only [Val.firstLive]
    rw [iha (fun l hl => h l (by simp [Val.loans, hl])), ihb (fun l hl => h l (by simp [Val.loans, hl]))]
  | sealed f a k x iha ihx =>
    simp only [Val.firstLive]
    rw [iha (fun l hl => h l (by simp [Val.loans, hl])), ihx (fun l hl => h l (by simp [Val.loans, hl]))]
  | _ => rfl

theorem Proj.step_loans {pr : Proj} {v w : Val} (h : pr.step v = .ok w) : ∀ l ∈ w.loans, l ∈ v.loans := by
  intro l hl
  cases pr <;> cases v <;> simp_all [Proj.step, Val.isNeutral, Val.loans]

theorem walk_congr {f g : Nat → Bool} (deep : Bool) :
    ∀ (π : List Proj) (v : Val), (∀ l ∈ v.loans, f l = g l) → walk f deep v π = walk g deep v π := by
  intro π
  induction π with
  | nil =>
    intro v h
    have hh : headLoan f v = headLoan g v := by
      cases v <;> simp_all [headLoan, Val.loans]
    simp only [walk, hh, Val.firstLive_congr v h]
  | cons pr ps ih =>
    intro v h
    have hh : headLoan f v = headLoan g v := by
      cases v <;> simp_all [headLoan, Val.loans]
    simp only [walk, hh]
    cases hs : pr.step v with
    | ok w => simp only; rw [ih w (fun l hl => h l (Proj.step_loans hs l hl))]
    | _ => rfl

/-! ## Names -/

theorem Val.names_substLoan {l : Nat} {w v : Val} {x : Nat} (h : x ∈ (Val.substLoan l w v).names) :
    x ∈ v.names ∨ x ∈ w.names := by
  induction v with
  | loan m => simp only [Val.substLoan] at h; split at h <;> simp_all [Val.names]
  | _ => simp_all [Val.substLoan, Val.names] <;> grind

theorem Val.names_clearB {l : Nat} {v : Val} {x : Nat} (h : x ∈ (Val.clearB l v).names) : x ∈ v.names := by
  unfold Val.clearB at h; split at h <;> simp_all [Val.names]

theorem Env.mem_names {Ω : Env} {x : Nat} : x ∈ Ω.names ↔ ∃ F ∈ Ω, ∃ b ∈ F, x ∈ b.2.names := by
  simp only [Env.names, List.mem_flatMap, List.mem_flatten]
  constructor
  · rintro ⟨b, ⟨F, hF, hb⟩, hx⟩; exact ⟨F, hF, b, hb, hx⟩
  · rintro ⟨F, hF, b, hb, hx⟩; exact ⟨b, ⟨F, hF, hb⟩, hx⟩

theorem Env.names_mapVals {g : Val → Val} {S : Nat → Prop}
    (hg : ∀ v x, x ∈ (g v).names → x ∈ v.names ∨ S x) {Ω : Env} {x : Nat}
    (h : x ∈ (Ω.mapVals g).names) : x ∈ Ω.names ∨ S x := by
  rw [Env.mem_names] at h ⊢
  obtain ⟨F, hF, b, hb, hx⟩ := h
  simp only [Env.mapVals, List.mem_map] at hF
  obtain ⟨F0, hF0, rfl⟩ := hF
  simp only [Frame.mapVals, List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  rcases hg b0.2 x hx with h | h
  · exact Or.inl ⟨F0, hF0, b0, hb0, h⟩
  · exact Or.inr h

theorem Env.names_append {A X : Env} {x : Nat} : x ∈ (A ++ X).names ↔ x ∈ A.names ∨ x ∈ X.names := by
  simp [Env.names]

theorem Frame.holderContent_names {F : Frame} {l : Nat} {w : Val} (h : F.holderContent l = some w)
    {x : Nat} (hx : x ∈ w.names) : ∃ b ∈ F, x ∈ b.2.names := by
  induction F with
  | nil => simp [Frame.holderContent] at h
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    cases v with
    | borrow m u =>
      simp only [Frame.holderContent] at h
      split at h
      · cases h; exact ⟨(y, .borrow m w), by simp, by simp [Val.names, hx]⟩
      · obtain ⟨b, hb, hx⟩ := ih h; exact ⟨b, List.mem_cons_of_mem _ hb, hx⟩
    | _ =>
      simp only [Frame.holderContent] at h
      obtain ⟨b, hb, hx⟩ := ih h; exact ⟨b, List.mem_cons_of_mem _ hb, hx⟩

theorem Env.holderContent_names {Ω : Env} {l : Nat} {w : Val} (h : Ω.holderContent l = some w)
    {x : Nat} (hx : x ∈ w.names) : x ∈ Ω.names := by
  rw [Env.mem_names]
  induction Ω with
  | nil => simp [Env.holderContent] at h
  | cons F Ω ih =>
    simp only [Env.holderContent] at h
    cases hF : F.holderContent l with
    | some u =>
      rw [hF] at h; cases h
      obtain ⟨b, hb, hx⟩ := Frame.holderContent_names hF hx
      exact ⟨F, by simp, b, hb, hx⟩
    | none =>
      rw [hF] at h
      obtain ⟨G, hG, b, hb, hx⟩ := ih h
      exact ⟨G, List.mem_cons_of_mem _ hG, b, hb, hx⟩

/-! ## Holders -/

theorem Env.holderContent_append (A X : Env) (l : Nat) :
    (A ++ X).holderContent l = (A.holderContent l).or (X.holderContent l) := by
  induction A with
  | nil => simp [Env.holderContent]
  | cons F A ih => simp [Env.holderContent, ih, Option.or_assoc]

theorem Frame.holderContent_of_holds {F : Frame} {l : Nat} (h : F.holds l = true) :
    ∃ w, F.holderContent l = some w := by
  induction F with
  | nil => simp [Frame.holds] at h
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.holds, List.any_cons, Bool.or_eq_true] at h
    cases v with
    | borrow m u =>
      simp only [Frame.holderContent]
      split
      · exact ⟨u, rfl⟩
      · rcases h with h | h
        · simp_all [Val.isBorrowOf]
        · exact ih h
    | _ =>
      simp only [Frame.holderContent]
      rcases h with h | h
      · simp [Val.isBorrowOf] at h
      · exact ih h

theorem Env.holderContent_of_holds {Ω : Env} {l : Nat} (h : Ω.holds l = true) :
    ∃ w, Ω.holderContent l = some w := by
  induction Ω with
  | nil => simp [Env.holds] at h
  | cons F Ω ih =>
    simp only [Env.holds, List.any_cons, Bool.or_eq_true] at h
    simp only [Env.holderContent]
    cases hF : F.holderContent l with
    | some u => exact ⟨u, rfl⟩
    | none =>
      rcases h with h | h
      · obtain ⟨u, hu⟩ := Frame.holderContent_of_holds h; simp_all
      · simpa using ih h

theorem Frame.clear_of_not_holds {F : Frame} {l : Nat} (h : F.holds l = false) :
    F.mapVals (Val.clearB l) = F := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.holds, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    rw [ih h.2, Val.clearB_eq_self h.1]

theorem Env.clearHolder_of_not_holds {X : Env} {l : Nat} (h : X.holds l = false) : X.clearHolder l = X := by
  induction X with
  | nil => rfl
  | cons F X ih =>
    simp only [Env.holds, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [Env.clearHolder, Env.mapVals, List.map_cons] at ih ⊢
    rw [ih h.2, Frame.clear_of_not_holds h.1]

/-! ## The invariant of a port-side state `c.app [P]` -/

/-- A name the run on the core may use without touching `Ω₂`: not held in `Ω₂`, and if it
occurs as a loan in `Ω₂` then it has a port. -/
def Good (Ω₂ : Env) (K : List Nat) (l : Nat) : Prop := Ω₂.holds l = false ∧ (l ∈ Ω₂.loans → l ∈ K)

structure PInv (Ω₂ : Env) (K : List Nat) (c : St) (P : Frame) : Prop where
  ne : c.env ≠ []
  pnb : P.nb = 0
  keys : ∀ l ∈ K, (portSub P l).isSome
  good : ∀ l ∈ c.env.names, Good Ω₂ K l
  fresh : ∀ l, c.next ≤ l → Good Ω₂ K l

theorem Env.substPorts_substLoan {Ω₂ : Env} {P : Frame} {l : Nat} (w : Val)
    (h : l ∈ Ω₂.loans → (portSub P l).isSome) :
    (Ω₂.substPorts P).substLoan l w = Ω₂.substPorts (P.mapVals (Val.substLoan l w)) := by
  simp only [Env.substLoan, Env.substPorts, Env.mapVals_mapVals]
  apply Env.mapVals_congr
  intro F hF b hb
  have hfun : portSub (Frame.mapVals (Val.substLoan l w) P) = fun m => (portSub P m).map (Val.substLoan l w) := by
    funext m; exact portSub_mapVals _ _ _
  simp only [Function.comp, hfun]
  apply Val.substSim_substLoan
  intro m hm hnone heq
  subst heq
  have := h (Env.mem_loans hF hb hm)
  simp [hnone] at this

theorem Env.substLoan_append (A X : Env) (l : Nat) (w : Val) :
    (A ++ X).substLoan l w = A.substLoan l w ++ X.substLoan l w := Env.mapVals_append _ _ _

theorem Env.substLoan_single (P : Frame) (l : Nat) (w : Val) :
    Env.substLoan l w [P] = [P.mapVals (Val.substLoan l w)] := rfl

theorem endWith_app (l : Nat) (w : Val) (c : St) (X : Env) :
    endWith l w (c.app X) =
      if w.nb = 0 then some ((⟨c.env.substLoan l w, c.next⟩ : St).app (X.substLoan l w)) else none := by
  unfold endWith
  split <;> simp [St.app, Env.substLoan_append]

theorem endWith_frame {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} {l : Nat} (w : Val)
    (hc : PInv Ω₂ K c P) (hg : Good Ω₂ K l) :
    endWith l w (c.app (Ω₂.substPorts P)) = (endWith l w (c.app [P])).map (frameMap Ω₂) := by
  rw [endWith_app, endWith_app]
  split
  · simp only [Option.map_some, Env.substLoan_single, St.frameMap_app]
    rw [Env.substPorts_substLoan w (fun h => hc.keys l (hg.2 h))]
  · rfl

theorem endBorrow_app {l : Nat} {c : St} {X : Env} (hA : c.env.holds l = true) (hX : X.holds l = false) :
    endBorrow l (c.app X) = (c.env.holderContent l).bind fun w =>
      if w.nb = 0 then
        some ((⟨(c.env.clearHolder l).substLoan l w, c.next⟩ : St).app (X.substLoan l w))
      else none := by
  obtain ⟨w, hw⟩ := Env.holderContent_of_holds hA
  unfold endBorrow
  simp only [St.app_env, Env.holderContent_append, hw, Option.some_or, Option.bind_some]
  unfold endWith
  split
  · simp [St.app, Env.clearHolder, Env.mapVals_append, Env.substLoan_append]
    rw [show Env.mapVals (Val.clearB l) X = X.clearHolder l from rfl, Env.clearHolder_of_not_holds hX]
  · rfl

theorem endBorrow_frame {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} {l : Nat}
    (hc : PInv Ω₂ K c P) (hA : c.env.holds l = true) (hg : Good Ω₂ K l) :
    endBorrow l (c.app (Ω₂.substPorts P)) = (endBorrow l (c.app [P])).map (frameMap Ω₂) := by
  have hXP : Env.holds l [P] = false := by rw [Env.holds_single, Frame.holds_of_nb hc.pnb]
  have hXB : Env.holds l (Ω₂.substPorts P) = false := by rw [Env.holds_substPorts hc.pnb]; exact hg.1
  rw [endBorrow_app hA hXP, endBorrow_app hA hXB]
  cases c.env.holderContent l with
  | none => rfl
  | some w =>
    simp only [Option.bind_some]
    split
    · simp only [Option.map_some, Env.substLoan_single, St.frameMap_app]
      rw [Env.substPorts_substLoan w (fun h => hc.keys l (hg.2 h))]
    · rfl

/-! ## Invariant preservation by [End] -/

@[simp] theorem Env.length_mapVals (g : Val → Val) (Ω : Env) : (Ω.mapVals g).length = Ω.length := by
  simp [Env.mapVals]
@[simp] theorem Env.length_substLoan (l : Nat) (w : Val) (Ω : Env) : (Ω.substLoan l w).length = Ω.length :=
  Env.length_mapVals _ _
@[simp] theorem Env.length_clearHolder (l : Nat) (Ω : Env) : (Ω.clearHolder l).length = Ω.length :=
  Env.length_mapVals _ _
theorem Env.ne_nil_of_length {A B : Env} (h : A.length = B.length) (hB : B ≠ []) : A ≠ [] := by
  intro hA; subst hA; exact hB (List.eq_nil_of_length_eq_zero h.symm)

theorem Env.names_substLoan {Ω : Env} {l : Nat} {w : Val} {x : Nat} (h : x ∈ (Ω.substLoan l w).names) :
    x ∈ Ω.names ∨ x ∈ w.names :=
  Env.names_mapVals (S := fun x => x ∈ w.names) (fun _ _ hx => Val.names_substLoan hx) h

theorem Env.names_clearHolder {Ω : Env} {l : Nat} {x : Nat} (h : x ∈ (Ω.clearHolder l).names) :
    x ∈ Ω.names := by
  have := Env.names_mapVals (S := fun _ => False) (fun _ _ hx => Or.inl (Val.names_clearB hx)) h
  simpa using this

theorem PInv.subst {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} (hc : PInv Ω₂ K c P)
    {l : Nat} {w : Val} (hw : w.nb = 0) (hwg : ∀ x ∈ w.names, Good Ω₂ K x) {A' : Env}
    (hA' : A' ≠ []) (hn : ∀ x ∈ A'.names, x ∈ c.env.names ∨ x ∈ w.names) :
    PInv Ω₂ K ⟨A', c.next⟩ (P.mapVals (Val.substLoan l w)) where
  ne := hA'
  pnb := by rw [Frame.nb_mapVals_substLoan l w hw]; exact hc.pnb
  keys := by intro m hm; rw [portSub_mapVals]; simpa using hc.keys m hm
  good := by
    intro x hx
    rcases hn x hx with h | h
    · exact hc.good x h
    · exact hwg x h
  fresh := hc.fresh

theorem endWith_pinv {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} {l : Nat} {w : Val}
    (hc : PInv Ω₂ K c P) (hwg : ∀ x ∈ w.names, Good Ω₂ K x) {s' : St}
    (h : endWith l w (c.app [P]) = some s') :
    ∃ c' P', s' = c'.app [P'] ∧ PInv Ω₂ K c' P' ∧ c'.env.length = c.env.length ∧ c'.next = c.next := by
  rw [endWith_app] at h
  split at h
  · rename_i hw
    cases h
    refine ⟨_, _, rfl, hc.subst hw hwg (Env.ne_nil_of_length (by simp) hc.ne) ?_, by simp, rfl⟩
    intro x hx; exact Env.names_substLoan hx
  · cases h

theorem endBorrow_pinv {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} {l : Nat}
    (hc : PInv Ω₂ K c P) (hA : c.env.holds l = true) {s' : St}
    (h : endBorrow l (c.app [P]) = some s') :
    ∃ c' P', s' = c'.app [P'] ∧ PInv Ω₂ K c' P' ∧ c'.env.length = c.env.length ∧ c'.next = c.next := by
  have hXP : Env.holds l [P] = false := by rw [Env.holds_single, Frame.holds_of_nb hc.pnb]
  rw [endBorrow_app hA hXP] at h
  cases hw : c.env.holderContent l with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i hw0
      cases h
      have hwn : ∀ x ∈ w.names, x ∈ c.env.names := fun x hx => Env.holderContent_names hw hx
      refine ⟨_, _, rfl, hc.subst hw0 (fun x hx => hc.good x (hwn x hx))
        (Env.ne_nil_of_length (by simp) hc.ne) ?_, by simp, rfl⟩
      intro x hx
      rcases Env.names_substLoan hx with h | h
      · exact Or.inl (Env.names_clearHolder h)
      · exact Or.inr h
    · cases h

/-! ## [Access] -/

theorem Proj.step_names {pr : Proj} {v w : Val} (h : pr.step v = .ok w) : ∀ l ∈ w.names, l ∈ v.names := by
  intro l hl
  cases pr <;> cases v <;> simp_all [Proj.step, Val.isNeutral, Val.names]

theorem Val.firstLive_mem {f : Nat → Bool} {v : Val} {l : Nat} (h : v.firstLive f = some l) :
    l ∈ v.names ∧ f l = true := by
  induction v with
  | loan m => simp only [Val.firstLive] at h; split at h <;> simp_all [Val.names]
  | succ v ih => exact (by simpa [Val.names] using ih h)
  | borrow m v ih => have := ih h; exact ⟨by simp [Val.names, this.1], this.2⟩
  | pair a b iha ihb =>
    simp only [Val.firstLive] at h
    cases ha : a.firstLive f with
    | some m => rw [ha] at h; cases h; have := iha ha; exact ⟨by simp [Val.names, this.1], this.2⟩
    | none => rw [ha] at h; have := ihb (by simpa using h); exact ⟨by simp [Val.names, this.1], this.2⟩
  | sealed g a k x iha ihx =>
    simp only [Val.firstLive] at h
    cases ha : a.firstLive f with
    | some m => rw [ha] at h; cases h; have := iha ha; exact ⟨by simp [Val.names, this.1], this.2⟩
    | none => rw [ha] at h; have := ihx (by simpa using h); exact ⟨by simp [Val.names, this.1], this.2⟩
  | _ => simp [Val.firstLive] at h

theorem walk_found {f : Nat → Bool} {deep : Bool} :
    ∀ (π : List Proj) (v : Val) (l : Nat), walk f deep v π = .found l → l ∈ v.names ∧ f l = true := by
  intro π
  induction π with
  | nil =>
    intro v l h
    simp only [walk] at h
    cases hh : headLoan f v with
    | some m =>
      rw [hh] at h; cases h
      cases v <;> simp [headLoan] at hh
      obtain ⟨h1, rfl⟩ := hh
      exact ⟨by simp [Val.names], h1⟩
    | none =>
      rw [hh] at h
      simp only at h
      split at h
      · split at h
        · rename_i m hm; cases h; exact Val.firstLive_mem hm
        · cases h
      · cases h
  | cons pr ps ih =>
    intro v l h
    simp only [walk] at h
    cases hh : headLoan f v with
    | some m =>
      rw [hh] at h; cases h
      cases v <;> simp [headLoan] at hh
      obtain ⟨h1, rfl⟩ := hh
      exact ⟨by simp [Val.names], h1⟩
    | none =>
      rw [hh] at h
      simp only at h
      cases hs : pr.step v with
      | ok w =>
        rw [hs] at h
        have := ih w l h
        exact ⟨Proj.step_names hs l this.1, this.2⟩
      | stuck => rw [hs] at h; cases h
      | err => rw [hs] at h; cases h

theorem walk_done {f : Nat → Bool} {deep : Bool} :
    ∀ (π : List Proj) (v c : Val), walk f deep v π = .done c → ∀ l ∈ c.names, l ∈ v.names := by
  intro π
  induction π with
  | nil =>
    intro v c h
    simp only [walk] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h; exact fun _ h => h
      · cases h; exact fun _ h => h
  | cons pr ps ih =>
    intro v c h
    simp only [walk] at h
    split at h
    · cases h
    · cases hs : pr.step v with
      | ok w =>
        rw [hs] at h
        intro l hl
        exact Proj.step_names hs l (ih w c h l hl)
      | stuck => rw [hs] at h; cases h
      | err => rw [hs] at h; cases h

theorem St.lookup_names {c : St} {x : Var} {v : Val} (h : c.lookup x = some v) :
    ∀ l ∈ v.names, l ∈ c.env.names := by
  intro l hl
  obtain ⟨Ω, n⟩ := c
  cases Ω with
  | nil => simp [St.lookup] at h
  | cons F Ω =>
    simp only [St.lookup, List.head?_cons, Option.bind_some] at h
    rw [Env.mem_names]
    have hb : (x, v) ∈ F := by
      clear hl
      induction F with
      | nil => simp at h
      | cons b F ih =>
        obtain ⟨y, w⟩ := b
        simp only [List.lookup_cons] at h
        split at h
        · rename_i hxy; cases h; simp at hxy; subst hxy; simp
        · exact List.mem_cons_of_mem _ (ih h)
    exact ⟨F, by simp, (x, v), hb, hl⟩

/-- Port-side result shape: `ok` results are again port-side states satisfying the invariant,
with the same number of core frames, and a value whose names are good. -/
def PRes (Ω₂ : Env) (K : List Nat) (len : Nat) : Res → Prop
  | .ok s v => ∃ c' P', s = c'.app [P'] ∧ PInv Ω₂ K c' P' ∧ c'.env.length = len ∧
      ∀ l ∈ v.names, Good Ω₂ K l
  | _ => True

theorem live_app_good {Ω₂ : Env} {K : List Nat} {c : St} {P : Frame} (hc : PInv Ω₂ K c P)
    {l : Nat} (hg : Good Ω₂ K l) :
    (c.app (Ω₂.substPorts P)).live l = (c.app [P]).live l := by
  simp only [St.live, St.app_env, Env.holds_append, Env.holds_single, Frame.holds_of_nb hc.pnb,
    Env.holds_substPorts hc.pnb, hg.1]

theorem live_app_port {c : St} {P : Frame} (hP : P.nb = 0) (l : Nat) :
    (c.app [P]).live l = c.env.holds l := by
  simp [St.live, Env.holds_append, Env.holds_single, Frame.holds_of_nb hP]

theorem access_frame {Ω₂ : Env} {K : List Nat} (deep : Bool) (x : Var) (π : List Proj) :
    ∀ (N : Nat) (c : St) (P : Frame), (c.app [P]).env.nb = N → PInv Ω₂ K c P →
      access deep x π (c.app (Ω₂.substPorts P)) = (access deep x π (c.app [P])).map (frameMap Ω₂) ∧
      PRes Ω₂ K c.env.length (access deep x π (c.app [P])) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro c P hN hc
  rw [access, access]
  simp only [St.lookup_app _ hc.ne]
  cases hl : c.lookup x with
  | none => exact ⟨rfl, trivial⟩
  | some v =>
    simp only
    have hvg : ∀ l ∈ v.names, Good Ω₂ K l := fun l hl' => hc.good l (St.lookup_names hl l hl')
    have hw : walk (c.app (Ω₂.substPorts P)).live deep v π = walk (c.app [P]).live deep v π :=
      walk_congr deep π v (fun l hl' => live_app_good hc (hvg l (Val.loans_sub_names hl')))
    rw [hw]
    cases hwk : walk (c.app [P]).live deep v π with
    | found l =>
      simp only
      obtain ⟨hln, hlive⟩ := walk_found π v l hwk
      rw [live_app_port hc.pnb] at hlive
      have hg := hvg l hln
      rw [endBorrow_frame hc hlive hg]
      cases he : endBorrow l (c.app [P]) with
      | none => exact ⟨rfl, trivial⟩
      | some s' =>
        simp only [Option.map_some]
        obtain ⟨c', P', rfl, hc', hlen, _⟩ := endBorrow_pinv hc hlive he
        have hlt := endBorrow_nb_lt he
        rw [St.frameMap_app]
        have := ih _ (hN ▸ hlt) c' P' rfl hc'
        rw [hlen] at this
        exact this
    | done c0 =>
      refine ⟨by simp [St.frameMap_app], c, P, rfl, hc, rfl, ?_⟩
      intro l hl'
      exact hvg l (walk_done π v c0 hwk l hl')
    | stuck => exact ⟨rfl, trivial⟩
    | err => exact ⟨rfl, trivial⟩

end OchrMeta
