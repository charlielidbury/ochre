import OchrMeta.Frame

/-! # Renaming equivariance of the machine

Loan names occur in values only as `borrow ℓ v` and `loan ℓ`; terms contain none.  The machine
consults loan names only through equality tests (preserved by an injective renaming `ρ`) and
liveness (`holds (ρ ℓ) (Ω.rename ρ) = holds ℓ Ω`), and it mints fresh names only from the counter
`next` ([Borrow], and the returned-borrow name `k` of [Close]).  So a run from a renamed state is
the renamed run, provided `ρ` is injective and shifts every name at or above the counter by the
same `d` (the counter condition `CC`), which is preserved because counters only grow.

The proof follows the architecture of the frame lemma (`Frame*.lean`): one commutation lemma per
machine operation, then one induction on fuel, with a `bind` combinator (`RSim.bind`) carrying
the counter condition through intermediate states. -/

namespace OchrMeta

def Env.rename (ρ : Nat → Nat) (Ω : Env) : Env := Ω.mapVals (Val.rename ρ)

/-- Rename a state: environment renamed, counter shifted by `d`. -/
def St.rename (ρ : Nat → Nat) (d : Nat) (s : St) : St := ⟨s.env.rename ρ, s.next + d⟩

/-- rename a result: state env and value renamed, counter shifted by d -/
def Res.rename (ρ : Nat → Nat) (d : Nat) : Res → Res
  | .ok s v => .ok ⟨s.env.rename ρ, s.next + d⟩ (v.rename ρ)
  | r => r

/-- The counter condition: `ρ` shifts every name at or above `n` by `d`. -/
def CC (ρ : Nat → Nat) (d : Nat) (n : Nat) : Prop := ∀ l, n ≤ l → ρ l = l + d

theorem CC.mono {ρ : Nat → Nat} {d n m : Nat} (h : CC ρ d n) (hm : n ≤ m) : CC ρ d m :=
  fun l hl => h l (Nat.le_trans hm hl)

section
variable {ρ : Nat → Nat} {d : Nat}

@[simp] theorem St.rename_env (s : St) : (s.rename ρ d).env = s.env.rename ρ := rfl
@[simp] theorem St.rename_next (s : St) : (s.rename ρ d).next = s.next + d := rfl
@[simp] theorem Res.rename_ok (s : St) (v : Val) :
    Res.rename ρ d (.ok s v) = .ok (s.rename ρ d) (v.rename ρ) := rfl
@[simp] theorem Res.rename_stuck : Res.rename ρ d .stuck = .stuck := rfl
@[simp] theorem Res.rename_err : Res.rename ρ d .err = .err := rfl
@[simp] theorem Res.rename_oof : Res.rename ρ d .oof = .oof := rfl

/-! ## Values -/

@[simp] theorem Val.nb_rename (v : Val) : (v.rename ρ).nb = v.nb := by
  induction v <;> simp_all [Val.rename, Val.nb]

@[simp] theorem Val.isNeutral_rename (v : Val) : (v.rename ρ).isNeutral = v.isNeutral := by
  cases v <;> rfl

theorem Val.rename_eq_moved (v : Val) : v.rename ρ = .moved ↔ v = .moved := by
  cases v <;> simp [Val.rename]

theorem Val.rename_substLoan (hρ : Function.Injective ρ) (l : Nat) (w : Val) :
    ∀ v : Val, (Val.substLoan l w v).rename ρ = Val.substLoan (ρ l) (w.rename ρ) (v.rename ρ) := by
  intro v
  induction v with
  | loan m =>
    simp only [Val.substLoan, Val.rename]
    by_cases h : m = l
    · subst h; simp
    · simp [h, hρ.ne h, Val.rename]
  | _ => simp_all [Val.substLoan, Val.rename]

theorem Val.isBorrowOf_rename (hρ : Function.Injective ρ) (l : Nat) (v : Val) :
    (v.rename ρ).isBorrowOf (ρ l) = v.isBorrowOf l := by
  cases v with
  | borrow m u =>
    simp only [Val.rename, Val.isBorrowOf]
    by_cases h : m = l
    · subst h; simp
    · rw [beq_false_of_ne h, beq_false_of_ne (hρ.ne h)]
  | _ => rfl

theorem Val.clearB_rename (hρ : Function.Injective ρ) (l : Nat) (v : Val) :
    Val.clearB (ρ l) (v.rename ρ) = (Val.clearB l v).rename ρ := by
  unfold Val.clearB
  rw [Val.isBorrowOf_rename hρ]
  split <;> rfl

theorem Val.firstLive_rename {f g : Nat → Bool} (hfg : ∀ l, g (ρ l) = f l) :
    ∀ v : Val, (v.rename ρ).firstLive g = (v.firstLive f).map ρ := by
  intro v
  induction v with
  | loan m => simp only [Val.rename, Val.firstLive, hfg]; split <;> rfl
  | pair a b iha ihb => simp only [Val.rename, Val.firstLive, iha, ihb, Option.map_or]
  | sealed h a k x iha ihx => simp only [Val.rename, Val.firstLive, iha, ihx, Option.map_or]
  | _ => simp_all [Val.rename, Val.firstLive]

theorem Val.ofList_rename (as : List Val) : Val.ofList (as.map (Val.rename ρ)) = (Val.ofList as).rename ρ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [Val.ofList, Val.rename, ih]

/-! ## Projections, paths and walks -/

def StepRes.rename (ρ : Nat → Nat) : StepRes → StepRes
  | .ok v => .ok (v.rename ρ)
  | r => r

theorem Proj.step_rename (pr : Proj) (v : Val) : pr.step (v.rename ρ) = (pr.step v).rename ρ := by
  cases pr <;> cases v <;> rfl

theorem Proj.put_rename (pr : Proj) (v new : Val) :
    pr.put (v.rename ρ) (new.rename ρ) = (pr.put v new).map (Val.rename ρ) := by
  cases pr <;> cases v <;> rfl

theorem Val.set_rename (π : List Proj) :
    ∀ (v new : Val), (v.rename ρ).set π (new.rename ρ) = (v.set π new).map (Val.rename ρ) := by
  induction π with
  | nil => intro v new; rfl
  | cons pr ps ih =>
    intro v new
    simp only [Val.set, Proj.step_rename]
    cases pr.step v with
    | ok w =>
      simp only [StepRes.rename, ih]
      cases w.set ps new with
      | none => rfl
      | some w' => simp only [Option.map_some, Option.bind_some, Proj.put_rename]
    | stuck => rfl
    | err => rfl

def WalkRes.rename (ρ : Nat → Nat) : WalkRes → WalkRes
  | .found l => .found (ρ l)
  | .done v => .done (v.rename ρ)
  | .stuck => .stuck
  | .err => .err

theorem headLoan_rename {f g : Nat → Bool} (hfg : ∀ l, g (ρ l) = f l) (v : Val) :
    headLoan g (v.rename ρ) = (headLoan f v).map ρ := by
  cases v with
  | loan m => simp only [Val.rename, headLoan, hfg]; split <;> rfl
  | _ => rfl

theorem walk_rename {f g : Nat → Bool} (hfg : ∀ l, g (ρ l) = f l) (deep : Bool) :
    ∀ (π : List Proj) (v : Val), walk g deep (v.rename ρ) π = (walk f deep v π).rename ρ := by
  intro π
  induction π with
  | nil =>
    intro v
    simp only [walk, headLoan_rename hfg, Val.firstLive_rename hfg]
    cases headLoan f v with
    | some l => rfl
    | none =>
      cases deep with
      | false => rfl
      | true => simp only [Option.map_none, if_true]; cases v.firstLive f <;> rfl
  | cons pr ps ih =>
    intro v
    simp only [walk, headLoan_rename hfg, Proj.step_rename]
    cases headLoan f v with
    | some l => rfl
    | none =>
      simp only [Option.map_none]
      cases pr.step v with
      | ok w => simp only [StepRes.rename, ih]
      | stuck => rfl
      | err => rfl

/-! ## Environments -/

theorem Frame.holds_rename (hρ : Function.Injective ρ) (l : Nat) (F : Frame) :
    Frame.holds (ρ l) (Frame.mapVals (Val.rename ρ) F) = F.holds l := by
  simp [Frame.holds, Frame.mapVals, List.any_map, Function.comp_def, Val.isBorrowOf_rename hρ]

theorem Env.holds_rename (hρ : Function.Injective ρ) (l : Nat) (Ω : Env) :
    (Ω.rename ρ).holds (ρ l) = Ω.holds l := by
  simp [Env.holds, Env.rename, Env.mapVals, List.any_map, Function.comp_def, Frame.holds_rename hρ]

theorem Frame.holderContent_rename (hρ : Function.Injective ρ) (l : Nat) (F : Frame) :
    Frame.holderContent (ρ l) (Frame.mapVals (Val.rename ρ) F) = (F.holderContent l).map (Val.rename ρ) := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    have e : Frame.mapVals (Val.rename ρ) ((y, v) :: F) = (y, v.rename ρ) :: Frame.mapVals (Val.rename ρ) F := rfl
    rw [e]
    cases v with
    | borrow m u =>
      simp only [Val.rename, Frame.holderContent]
      by_cases h : m = l
      · subst h; simp
      · simp [h, hρ.ne h, ih]
    | _ => simp only [Val.rename, Frame.holderContent, ih]

theorem Env.holderContent_rename (hρ : Function.Injective ρ) (l : Nat) (Ω : Env) :
    (Ω.rename ρ).holderContent (ρ l) = (Ω.holderContent l).map (Val.rename ρ) := by
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.rename, Env.mapVals, List.map_cons] at ih ⊢
    simp only [Env.holderContent, ih, Frame.holderContent_rename hρ, Option.map_or]

theorem Env.clearHolder_rename (hρ : Function.Injective ρ) (l : Nat) (Ω : Env) :
    (Ω.rename ρ).clearHolder (ρ l) = (Ω.clearHolder l).rename ρ := by
  simp only [Env.clearHolder, Env.rename, Env.mapVals_mapVals]
  congr 1
  funext v
  exact Val.clearB_rename hρ l v

theorem Env.substLoan_rename (hρ : Function.Injective ρ) (l : Nat) (w : Val) (Ω : Env) :
    (Ω.rename ρ).substLoan (ρ l) (w.rename ρ) = (Ω.substLoan l w).rename ρ := by
  simp only [Env.substLoan, Env.rename, Env.mapVals_mapVals]
  congr 1
  funext v
  exact (Val.rename_substLoan hρ l w v).symm

theorem Frame.lookup_rename (F : Frame) (x : Var) :
    (Frame.mapVals (Val.rename ρ) F).lookup x = (F.lookup x).map (Val.rename ρ) := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.mapVals, List.map_cons, List.lookup_cons] at ih ⊢
    split <;> simp_all

theorem Frame.set_rename (x : Var) (v : Val) (F : Frame) :
    Frame.set x (v.rename ρ) (Frame.mapVals (Val.rename ρ) F) = Frame.mapVals (Val.rename ρ) (Frame.set x v F) := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, w⟩ := b
    simp only [Frame.mapVals, List.map_cons, Frame.set] at ih ⊢
    split <;> simp_all

theorem Frame.remove_rename (x : Var) (F : Frame) :
    Frame.remove x (Frame.mapVals (Val.rename ρ) F) =
      (Frame.remove x F).map fun p => (p.1.rename ρ, Frame.mapVals (Val.rename ρ) p.2) := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨y, w⟩ := b
    have e : Frame.mapVals (Val.rename ρ) ((y, w) :: F) = (y, w.rename ρ) :: Frame.mapVals (Val.rename ρ) F := rfl
    rw [e]
    simp only [Frame.remove]
    split
    · rfl
    · rw [ih]; cases Frame.remove x F <;> rfl

/-! ## States -/

theorem St.lookup_rename (s : St) (x : Var) : (s.rename ρ d).lookup x = (s.lookup x).map (Val.rename ρ) := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => rfl
  | cons F Ω => exact Frame.lookup_rename F x

theorem St.live_rename (hρ : Function.Injective ρ) (s : St) (l : Nat) : (s.rename ρ d).live (ρ l) = s.live l :=
  Env.holds_rename hρ l s.env

theorem St.modTop_rename {g g' : Frame → Frame}
    (hg : ∀ F, g' (Frame.mapVals (Val.rename ρ) F) = Frame.mapVals (Val.rename ρ) (g F)) (s : St) :
    (s.rename ρ d).modTop g' = (s.modTop g).rename ρ d := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => rfl
  | cons F Ω =>
    show (⟨g' (Frame.mapVals (Val.rename ρ) F) :: Env.rename ρ Ω, n + d⟩ : St) = ⟨Frame.mapVals (Val.rename ρ) (g F) :: Env.rename ρ Ω, n + d⟩
    rw [hg]

theorem St.modTop_next (g : Frame → Frame) (s : St) : (s.modTop g).next = s.next := by
  obtain ⟨Ω, n⟩ := s; cases Ω <;> rfl

theorem St.setVar_rename (s : St) (x : Var) (v : Val) :
    (s.rename ρ d).setVar x (v.rename ρ) = (s.setVar x v).rename ρ d :=
  St.modTop_rename (fun F => Frame.set_rename x v F) s

theorem St.bind_rename (s : St) (x : Var) (v : Val) :
    (s.rename ρ d).bind x (v.rename ρ) = (s.bind x v).rename ρ d :=
  St.modTop_rename (g := ((x, v) :: ·)) (fun _ => rfl) s

theorem St.bind_next (s : St) (x : Var) (v : Val) : (s.bind x v).next = s.next := St.modTop_next _ s

theorem St.push_rename (s : St) (F : Frame) :
    (s.rename ρ d).push (Frame.mapVals (Val.rename ρ) F) = (s.push F).rename ρ d := rfl

theorem St.unbind_rename (s : St) (x : Var) :
    (s.rename ρ d).unbind x = (s.unbind x).map fun p => (p.1.rename ρ, p.2.rename ρ d) := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => rfl
  | cons F Ω =>
    show (Frame.remove x (Frame.mapVals (Val.rename ρ) F)).map _ = _
    rw [Frame.remove_rename]
    simp only [St.unbind, Option.map_map]
    cases Frame.remove x F <;> rfl

theorem St.unbind_next {s s' : St} {x : Var} {v : Val} (h : s.unbind x = some (v, s')) : s'.next = s.next := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => simp [St.unbind] at h
  | cons F Ω =>
    simp only [St.unbind] at h
    cases hr : Frame.remove x F with
    | none => rw [hr] at h; cases h
    | some p => rw [hr] at h; simp at h; obtain ⟨_, rfl⟩ := h; rfl

theorem St.setPlace_rename (s : St) (x : Var) (π : List Proj) (v : Val) :
    (s.rename ρ d).setPlace x π (v.rename ρ) = (s.setPlace x π v).map (St.rename ρ d) := by
  simp only [St.setPlace, St.lookup_rename]
  cases s.lookup x with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.bind_some, Val.set_rename]
    cases c.set π v with
    | none => rfl
    | some c' => simp only [Option.map_some, St.setVar_rename]

theorem St.setPlace_next {s s' : St} {x : Var} {π : List Proj} {v : Val} (h : s.setPlace x π v = some s') :
    s'.next = s.next := by
  simp only [St.setPlace] at h
  cases hl : s.lookup x with
  | none => rw [hl] at h; cases h
  | some c =>
    rw [hl] at h
    simp only [Option.bind_some] at h
    cases hs : c.set π v with
    | none => rw [hs] at h; cases h
    | some c' => rw [hs] at h; cases h; exact St.modTop_next _ s

/-! ## [End] -/

theorem endWith_rename (hρ : Function.Injective ρ) (l : Nat) (w : Val) (s : St) :
    endWith (ρ l) (w.rename ρ) (s.rename ρ d) = (endWith l w s).map (St.rename ρ d) := by
  unfold endWith
  rw [Val.nb_rename]
  split
  · simp only [Option.map_some, Option.some.injEq]
    show (⟨(s.env.rename ρ).substLoan (ρ l) (w.rename ρ), s.next + d⟩ : St) = ⟨(s.env.substLoan l w).rename ρ, s.next + d⟩
    rw [Env.substLoan_rename hρ]
  · rfl

theorem endWith_next {l : Nat} {w : Val} {s s' : St} (h : endWith l w s = some s') : s'.next = s.next := by
  unfold endWith at h; split at h
  · cases h; rfl
  · cases h

theorem endBorrow_rename (hρ : Function.Injective ρ) (l : Nat) (s : St) :
    endBorrow (ρ l) (s.rename ρ d) = (endBorrow l s).map (St.rename ρ d) := by
  unfold endBorrow
  simp only [St.rename_env, Env.holderContent_rename hρ]
  cases s.env.holderContent l with
  | none => rfl
  | some w =>
    simp only [Option.map_some]
    have e : ({ s.rename ρ d with env := (s.env.rename ρ).clearHolder (ρ l) } : St) =
        St.rename ρ d { s with env := s.env.clearHolder l } := by
      simp only [St.rename, Env.clearHolder_rename hρ]
    rw [e, endWith_rename hρ]

theorem endBorrow_next {l : Nat} {s s' : St} (h : endBorrow l s = some s') : s'.next = s.next := by
  unfold endBorrow at h; split at h
  · cases h
  · exact endWith_next h (s := { s with env := s.env.clearHolder l })

/-! ## Results: equation plus the counter condition on the unrenamed side -/

/-- The counter condition holds at an `ok` result. -/
def ROk (ρ : Nat → Nat) (d : Nat) : Res → Prop
  | .ok s _ => CC ρ d s.next
  | _ => True

/-- The renamed-side result `rf` is the renaming of `rp`, and the counter condition holds at `rp`. -/
def RSim (ρ : Nat → Nat) (d : Nat) (rf rp : Res) : Prop := rf = rp.rename ρ d ∧ ROk ρ d rp

theorem RSim.bind {rf rp : Res} (h : RSim ρ d rf rp) {kf kp : St → Val → Res}
    (hk : ∀ s v, CC ρ d s.next → RSim ρ d (kf (s.rename ρ d) (v.rename ρ)) (kp s v)) :
    RSim ρ d (rf.bind kf) (rp.bind kp) := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  cases rp with
  | ok s v => exact hk s v h2
  | _ => exact ⟨rfl, trivial⟩

theorem RSim.err : RSim ρ d .err .err := ⟨rfl, trivial⟩
theorem RSim.stuck : RSim ρ d .stuck .stuck := ⟨rfl, trivial⟩
theorem RSim.oof : RSim ρ d .oof .oof := ⟨rfl, trivial⟩
theorem RSim.ok {s : St} (hc : CC ρ d s.next) (v : Val) :
    RSim ρ d (.ok (s.rename ρ d) (v.rename ρ)) (.ok s v) := ⟨rfl, hc⟩

/-- An evaluator commutes with renaming. -/
def EvR (ρ : Nat → Nat) (d : Nat) (ev : St → Term → Res) : Prop :=
  ∀ (s : St) (t : Term), CC ρ d s.next → RSim ρ d (ev (s.rename ρ d) t) (ev s t)

/-! ## [Access] -/

theorem access_rename (hρ : Function.Injective ρ) (deep : Bool) (x : Var) (π : List Proj) :
    ∀ (N : Nat) (s : St), s.env.nb = N → CC ρ d s.next →
      RSim ρ d (access deep x π (s.rename ρ d)) (access deep x π s) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s hN hc
  rw [access, access]
  simp only [St.lookup_rename]
  cases hl : s.lookup x with
  | none => exact RSim.err
  | some v =>
    simp only [Option.map_some]
    rw [walk_rename (f := s.live) (fun l => St.live_rename hρ s l)]
    cases hwk : walk s.live deep v π with
    | found l =>
      simp only [WalkRes.rename]
      rw [endBorrow_rename hρ]
      cases he : endBorrow l s with
      | none => exact RSim.err
      | some s' =>
        simp only [Option.map_some]
        have hlt := endBorrow_nb_lt he
        have hn := endBorrow_next he
        exact ih _ (hN ▸ hlt) s' rfl (hn ▸ hc)
    | done c => exact RSim.ok hc c
    | stuck => exact RSim.stuck
    | err => exact RSim.err

/-! ## [Drop] and frame pops -/

theorem hasLive_rename (hρ : Function.Injective ρ) (s : St) (extra v : Val) :
    hasLive (s.rename ρ d) (extra.rename ρ) (v.rename ρ) = hasLive s extra v := by
  unfold hasLive
  rw [Val.firstLive_rename (f := fun l => s.live l || extra.isBorrowOf l)
    (fun l => by simp only [St.live_rename hρ, Val.isBorrowOf_rename hρ])]
  cases v.firstLive _ <;> rfl

theorem dropVal_rename (hρ : Function.Injective ρ) (extra v : Val) (s : St) :
    dropVal (extra.rename ρ) (v.rename ρ) (s.rename ρ d) = (dropVal extra v s).map (St.rename ρ d) := by
  have key := hasLive_rename (d := d) hρ s extra v
  cases v with
  | borrow l w => exact endWith_rename hρ l w s
  | _ =>
    simp only [Val.rename] at key ⊢
    simp only [dropVal, key]
    split <;> rfl

theorem dropVal_next {extra v : Val} {s s' : St} (h : dropVal extra v s = some s') : s'.next = s.next := by
  unfold dropVal at h
  split at h
  · exact endWith_next h
  · split at h
    · cases h
    · cases h; rfl

theorem popFrameN_rename (hρ : Function.Injective ρ) (extra : Val) :
    ∀ (n : Nat) (s : St), popFrameN (extra.rename ρ) n (s.rename ρ d) = (popFrameN extra n s).map (St.rename ρ d) := by
  intro n
  induction n with
  | zero =>
    intro s
    obtain ⟨Ω, m⟩ := s
    rcases Ω with _ | ⟨F, Ω⟩
    · rfl
    · cases F <;> rfl
  | succ n ih =>
    intro s
    obtain ⟨Ω, m⟩ := s
    rcases Ω with _ | ⟨F, Ω⟩
    · rfl
    · cases F with
      | nil => rfl
      | cons b F =>
        obtain ⟨y, c⟩ := b
        have e : St.rename ρ d ⟨((y, c) :: F) :: Ω, m⟩ =
            ⟨((y, c.rename ρ) :: Frame.mapVals (Val.rename ρ) F) :: Env.rename ρ Ω, m + d⟩ := rfl
        rw [e]
        simp only [popFrameN]
        have e2 : ({ env := Frame.mapVals (Val.rename ρ) F :: Env.rename ρ Ω, next := m + d } : St) =
            St.rename ρ d ⟨F :: Ω, m⟩ := rfl
        rw [e2, dropVal_rename hρ]
        cases dropVal extra c ⟨F :: Ω, m⟩ with
        | none => rfl
        | some s' => simp only [Option.map_some, Option.bind_some, ih]

theorem popFrameN_next (extra : Val) :
    ∀ (n : Nat) (s s' : St), popFrameN extra n s = some s' → s'.next = s.next := by
  intro n
  induction n with
  | zero =>
    intro s s' h
    obtain ⟨Ω, m⟩ := s
    rcases Ω with _ | ⟨F, Ω⟩
    · cases h
    · cases F with
      | nil => cases h; rfl
      | cons _ _ => cases h
  | succ n ih =>
    intro s s' h
    obtain ⟨Ω, m⟩ := s
    rcases Ω with _ | ⟨F, Ω⟩
    · cases h
    · cases F with
      | nil => cases h
      | cons b F =>
        obtain ⟨y, c⟩ := b
        simp only [popFrameN] at h
        cases hd : dropVal extra c ⟨F :: Ω, m⟩ with
        | none => rw [hd] at h; cases h
        | some s1 =>
          rw [hd] at h
          simp only [Option.bind_some] at h
          rw [ih s1 s' h, dropVal_next hd]

theorem popFrame_rename (hρ : Function.Injective ρ) (v : Val) (s : St) :
    popFrame (v.rename ρ) (s.rename ρ d) = (popFrame v s).map (St.rename ρ d) := by
  unfold popFrame
  have e : ((s.rename ρ d).env.head?.map List.length).getD 0 = (s.env.head?.map List.length).getD 0 := by
    obtain ⟨Ω, m⟩ := s
    cases Ω with
    | nil => rfl
    | cons F Ω => simp [St.rename, Env.rename, Env.mapVals, Frame.mapVals]
  rw [e, popFrameN_rename hρ]

theorem popFrame_next {v : Val} {s s' : St} (h : popFrame v s = some s') : s'.next = s.next :=
  popFrameN_next v _ s s' h

/-! ## Arguments and temporaries -/

theorem execArgs_rename {ev : St → Term → Res} (hev : EvR ρ d ev) :
    ∀ (args : List Term) (i : Nat) (s : St), CC ρ d s.next →
      RSim ρ d (execArgs ev i (s.rename ρ d) args) (execArgs ev i s args) := by
  intro args
  induction args with
  | nil => intro i s hc; exact RSim.ok hc .unit
  | cons a as ih =>
    intro i s hc
    simp only [execArgs]
    apply RSim.bind (hev s a hc)
    intro s' v hc'
    rw [St.bind_rename]
    exact ih (i + 1) _ (by rwa [St.bind_next])

theorem takeTemps_rename :
    ∀ (is : List Nat) (s : St), takeTemps is (s.rename ρ d) =
      (takeTemps is s).map fun p => (p.1.map (Val.rename ρ), p.2.rename ρ d) := by
  intro is
  induction is with
  | nil => intro s; rfl
  | cons i is ih =>
    intro s
    simp only [takeTemps, St.unbind_rename]
    cases s.unbind (.tmp i) with
    | none => rfl
    | some p =>
      obtain ⟨v, s1⟩ := p
      simp only [Option.map_some, Option.bind_some, ih]
      cases takeTemps is s1 <;> rfl

theorem takeTemps_next :
    ∀ (is : List Nat) (s s' : St) (vs : List Val), takeTemps is s = some (vs, s') → s'.next = s.next := by
  intro is
  induction is with
  | nil => intro s s' vs h; simp [takeTemps] at h; rw [h.2]
  | cons i is ih =>
    intro s s' vs h
    simp only [takeTemps] at h
    cases hu : s.unbind (.tmp i) with
    | none => rw [hu] at h; cases h
    | some p =>
      obtain ⟨v, s1⟩ := p
      rw [hu] at h
      simp only [Option.bind_some] at h
      cases ht : takeTemps is s1 with
      | none => rw [ht] at h; cases h
      | some q =>
        obtain ⟨vs', s2⟩ := q
        rw [ht] at h; simp at h; obtain ⟨_, rfl⟩ := h
        rw [ih s1 s2 vs' ht, St.unbind_next hu]

/-! ## [Close] -/

theorem sealArgs_rename :
    ∀ (i : Nat) (ps : List (Var × Ty)) (ws : List Val), sealArgs i ps (ws.map (Val.rename ρ)) =
      (sealArgs i ps ws).map fun p => (p.1.map (Val.rename ρ), p.2.map fun q => (q.1, ρ q.2)) := by
  intro i ps
  induction ps generalizing i with
  | nil => intro ws; cases ws <;> rfl
  | cons p ps ih =>
    intro ws
    obtain ⟨y, ty⟩ := p
    cases ws with
    | nil => cases ty <;> rfl
    | cons w ws =>
      cases ty with
      | ref T =>
        cases w with
        | borrow l u =>
          simp only [List.map_cons, Val.rename, sealArgs, ih]
          cases sealArgs (i + 1) ps ws <;> rfl
        | _ => rfl
      | _ =>
        simp only [List.map_cons, sealArgs, ih]
        cases sealArgs (i + 1) ps ws <;> rfl

theorem fillLoans_rename (hρ : Function.Injective ρ) :
    ∀ (fs : List (Nat × Val)) (s : St),
      fillLoans (fs.map fun p => (ρ p.1, p.2.rename ρ)) (s.rename ρ d) = (fillLoans fs s).map (St.rename ρ d) := by
  intro fs
  induction fs with
  | nil => intro s; rfl
  | cons p fs ih =>
    intro s
    obtain ⟨l, w⟩ := p
    simp only [List.map_cons, fillLoans, endWith_rename hρ]
    cases endWith l w s with
    | none => rfl
    | some s' => simp only [Option.map_some, Option.bind_some, ih]

theorem fillLoans_next :
    ∀ (fs : List (Nat × Val)) (s s' : St), fillLoans fs s = some s' → s'.next = s.next := by
  intro fs
  induction fs with
  | nil => intro s s' h; cases h; rfl
  | cons p fs ih =>
    intro s s' h
    obtain ⟨l, w⟩ := p
    simp only [fillLoans] at h
    cases he : endWith l w s with
    | none => rw [he] at h; cases h
    | some s1 =>
      rw [he] at h
      simp only [Option.bind_some] at h
      rw [ih s1 s' h, endWith_next he]

/-- The common tail of the three rows of [Close]. -/
theorem fillLoans_sim (hρ : Function.Injective ρ) {fs fs' : List (Nat × Val)}
    (hfs : fs' = fs.map fun p => (ρ p.1, p.2.rename ρ)) {s s' : St} (hs : s' = s.rename ρ d)
    (hc : CC ρ d s.next) {v v' : Val} (hv : v' = v.rename ρ) :
    RSim ρ d (match fillLoans fs' s' with | none => .err | some s2 => .ok s2 v')
      (match fillLoans fs s with | none => .err | some s2 => .ok s2 v) := by
  subst hfs hs hv
  rw [fillLoans_rename hρ]
  cases hf : fillLoans fs s with
  | none => exact RSim.err
  | some s2 => exact RSim.ok (by rw [fillLoans_next fs s s2 hf]; exact hc) v

theorem closeCall_rename (hρ : Function.Injective ρ) (f : String) (fd : FunDef) (ws : List Val) (s : St)
    (hc : CC ρ d s.next) :
    RSim ρ d (closeCall f fd (ws.map (Val.rename ρ)) (s.rename ρ d)) (closeCall f fd ws s) := by
  unfold closeCall
  rw [sealArgs_rename]
  cases sealArgs 0 fd.params ws with
  | none => exact RSim.err
  | some q =>
    obtain ⟨as, ls⟩ := q
    simp only [Option.map_some]
    rw [Val.ofList_rename]
    have hk : ρ s.next = s.next + d := hc s.next (Nat.le_refl _)
    have hfin : ∀ g : Nat → SealK,
        List.map (fun x => (x.snd, Val.sealed f (Val.rename ρ (Val.ofList as)) (g x.fst) Val.unit))
            (List.map (fun q => (q.fst, ρ q.snd)) ls) =
          (List.map (fun x => (x.snd, Val.sealed f (Val.ofList as) (g x.fst) Val.unit)) ls).map
            fun p => (ρ p.1, p.2.rename ρ) := by
      intro g; simp [List.map_map, Function.comp_def, Val.rename]
    cases fd.ret with
    | ref T =>
      dsimp only
      refine fillLoans_sim hρ ?_ (s := ⟨s.env, s.next + 1⟩) ?_ (hc.mono (Nat.le_succ _)) ?_
      · simp [List.map_map, Function.comp_def, Val.rename, hk]
      · simp only [St.rename]; congr 1; omega
      · simp [Val.rename, hk]
    | unit => exact fillLoans_sim hρ (hfin SealK.fin) rfl hc rfl
    | _ => exact fillLoans_sim hρ (hfin SealK.fin) rfl hc rfl

/-! ## [Call] -/

theorem paramFrame_rename (fd : FunDef) (ws : List Val) :
    paramFrame fd (ws.map (Val.rename ρ)) = Frame.mapVals (Val.rename ρ) (paramFrame fd ws) := by
  simp only [paramFrame, Frame.mapVals, List.zip_map_right]
  rfl

theorem callWith_rename (hρ : Function.Injective ρ) {run : St → Term → Res} (hrun : EvR ρ d run)
    (cc : Bool) (f : String) (fd : FunDef) (ws : List Val) (s : St) (hc : CC ρ d s.next) :
    RSim ρ d (callWith run cc f fd (ws.map (Val.rename ρ)) (s.rename ρ d)) (callWith run cc f fd ws s) := by
  unfold callWith
  cases fd.body with
  | none =>
    dsimp only
    split
    · exact closeCall_rename hρ f fd ws s hc
    · exact RSim.stuck
  | some b =>
    dsimp only
    rw [List.length_map]
    split
    · rw [paramFrame_rename, St.push_rename]
      obtain ⟨h1, h2⟩ := hrun (s.push (paramFrame fd ws)) b hc
      rw [h1]
      cases hr : run (s.push (paramFrame fd ws)) b with
      | ok s' v =>
        rw [hr] at h2
        simp only [Res.rename_ok]
        rw [popFrame_rename hρ]
        cases hp : popFrame v s' with
        | none => exact RSim.err
        | some s'' => exact RSim.ok (by rw [popFrame_next hp]; exact h2) v
      | stuck =>
        simp only [Res.rename_stuck]
        split
        · exact closeCall_rename hρ f fd ws s hc
        · exact RSim.stuck
      | err => exact RSim.err
      | oof => exact RSim.oof
    · exact RSim.err

/-! ## The machine: one induction on fuel -/

theorem exec_rsim (P : Prog) (hρ : Function.Injective ρ) : ∀ n, EvR ρ d (exec P n) := by
  intro n
  induction n with
  | zero => intro s t hc; exact RSim.oof
  | succ n ih =>
    intro s t hc
    cases t with
    | read p =>
      simp only [exec]
      apply RSim.bind (access_rename hρ true _ _ _ s rfl hc)
      intro s1 v hc1
      cases v with
      | moved => exact RSim.err
      | borrow l w =>
        dsimp only [Val.rename]
        have h := St.setPlace_rename (ρ := ρ) (d := d) s1 p.root p.path .moved
        simp only [Val.rename] at h
        rw [h]
        cases hop : s1.setPlace p.root p.path .moved with
        | none => exact RSim.err
        | some s2 => exact RSim.ok (by rw [St.setPlace_next hop]; exact hc1) (.borrow l w)
      | _ => exact RSim.ok hc1 _
    | borrow p =>
      simp only [exec]
      apply RSim.bind (access_rename hρ true _ _ _ s rfl hc)
      intro s1 c hc1
      by_cases hcond : c = .moved ∨ c.nb ≠ 0
      · have hcond' : c.rename ρ = .moved ∨ (c.rename ρ).nb ≠ 0 := by rwa [Val.rename_eq_moved, Val.nb_rename]
        rw [if_pos hcond, if_pos hcond']; exact RSim.err
      · have hcond' : ¬ (c.rename ρ = .moved ∨ (c.rename ρ).nb ≠ 0) := by rwa [Val.rename_eq_moved, Val.nb_rename]
        rw [if_neg hcond, if_neg hcond']
        have hk : ρ s1.next = s1.next + d := hc1 s1.next (Nat.le_refl _)
        have h := St.setPlace_rename (ρ := ρ) (d := d) s1 p.root p.path (.loan s1.next)
        simp only [Val.rename, hk] at h
        simp only [St.rename_next]
        rw [h]
        cases hop : s1.setPlace p.root p.path (.loan s1.next) with
        | none => exact RSim.err
        | some s2 =>
          refine ⟨?_, hc1.mono (Nat.le_succ _)⟩
          simp only [Option.map_some, Res.rename_ok, St.rename, Val.rename, hk]
          rw [Nat.add_right_comm s1.next d 1]
    | assign p t =>
      simp only [exec]
      apply RSim.bind (ih s t hc)
      intro s1 v hc1
      apply RSim.bind (access_rename hρ true _ _ _ s1 rfl hc1)
      intro s2 c hc2
      rw [St.setPlace_rename]
      cases hop : s2.setPlace p.root p.path v with
      | none => exact RSim.err
      | some s3 =>
        simp only [Option.map_some]
        have h := dropVal_rename (d := d) hρ .unit c s3
        simp only [Val.rename] at h
        rw [h]
        cases hd : dropVal .unit c s3 with
        | none => exact RSim.err
        | some s4 => exact RSim.ok (by rw [dropVal_next hd, St.setPlace_next hop]; exact hc2) .unit
    | letIn x t u =>
      simp only [exec]
      apply RSim.bind (ih s t hc)
      intro s1 v hc1
      rw [St.bind_rename]
      apply RSim.bind (ih (s1.bind x v) u (by rwa [St.bind_next]))
      intro s2 w hc2
      rw [St.unbind_rename]
      cases hu : s2.unbind x with
      | none => exact RSim.err
      | some q =>
        obtain ⟨cv, s3⟩ := q
        simp only [Option.map_some]
        rw [dropVal_rename hρ]
        cases hd : dropVal w cv s3 with
        | none => exact RSim.err
        | some s4 => exact RSim.ok (by rw [dropVal_next hd, St.unbind_next hu]; exact hc2) w
    | seq t u =>
      simp only [exec]
      apply RSim.bind (ih s t hc)
      intro s1 v hc1
      have h := dropVal_rename (d := d) hρ .unit v s1
      simp only [Val.rename] at h
      rw [h]
      cases hd : dropVal .unit v s1 with
      | none => exact RSim.err
      | some s2 => exact ih s2 u (by rw [dropVal_next hd]; exact hc1)
    | zero => exact RSim.ok hc .zero
    | unit => exact RSim.ok hc .unit
    | erase t => exact RSim.ok hc .star
    | succ t =>
      simp only [exec]
      apply RSim.bind (ih s t hc)
      intro s1 v hc1
      exact RSim.ok hc1 (.succ v)
    | pair t u =>
      simp only [exec]
      apply RSim.bind (ih s t hc)
      intro s1 v hc1
      apply RSim.bind (ih s1 u hc1)
      intro s2 w hc2
      exact RSim.ok hc2 (.pair v w)
    | mtch p tz y ts =>
      simp only [exec]
      apply RSim.bind (access_rename hρ false _ _ _ s rfl hc)
      intro s1 c hc1
      cases c with
      | zero => exact ih s1 tz hc1
      | succ w => exact ih s1 _ hc1
      | _ => first | exact RSim.stuck | exact RSim.err
    | call f args cc =>
      simp only [exec]
      cases P.find f with
      | none => exact RSim.err
      | some fd =>
        dsimp only
        by_cases hp : fd.ret = .prop
        · rw [if_pos hp, if_pos hp]; exact RSim.ok hc .star
        · rw [if_neg hp, if_neg hp]
          apply RSim.bind (execArgs_rename ih args 0 s hc)
          intro s1 _ hc1
          rw [takeTemps_rename]
          cases ht : takeTemps (List.range args.length) s1 with
          | none => exact RSim.err
          | some q =>
            obtain ⟨ws, s2⟩ := q
            simp only [Option.map_some]
            exact callWith_rename hρ ih cc f fd ws s2 (by rw [takeTemps_next _ _ _ _ ht]; exact hc1)

end

/-! ## Renaming equivariance -/

/-- **Renaming equivariance.**  Running from a renamed state (environment renamed by an injective
`ρ`, counter shifted by `d`) gives the renamed result, provided `ρ` shifts every name at or above
the counter by `d`.  `stuck`, `err` and `oof` are identical. -/
theorem exec_rename (P : Prog) (ρ : Nat → Nat) (hρ : Function.Injective ρ) (d : Nat) :
    ∀ (n : Nat) (s : St) (t : Term), (∀ l, s.next ≤ l → ρ l = l + d) →
      exec P n ⟨s.env.rename ρ, s.next + d⟩ t = (exec P n s t).rename ρ d :=
  fun n s t hc => (exec_rsim P hρ n s t hc).1

/-- Renaming equivariance for `Eval`. -/
theorem eval_rename (P : Prog) (ρ : Nat → Nat) (hρ : Function.Injective ρ) (d : Nat) (s : St) (t : Term) (r : Res)
    (hc : ∀ l, s.next ≤ l → ρ l = l + d) :
    Eval P s t r → Eval P ⟨s.env.rename ρ, s.next + d⟩ t (r.rename ρ d) := by
  rintro ⟨hr, n, hn⟩
  refine ⟨?_, n, ?_⟩
  · cases r <;> simp_all
  · rw [exec_rename P ρ hρ d n s t hc, hn]

end OchrMeta
