/-
  Ochr.Model.Safety: test 3 of `ochr/docs/18` (type safety: accepted programs never go wrong at
  runtime), on the toy machine of `Ochr/Model/State2.lean`. Standalone: imports Lean core only,
  is not imported by `Ochr.lean`, and is checked with `lake env lean Ochr/Model/Safety.lean` from
  `ochr/core/lean`. What it needs from `State2.lean` is copied.

  The *concrete runtime* has no unknowns. `σ_g` is a concrete function `G` whose backward function
  is injective. A call computes its forward value at once and fills the lent place with a pending
  backward computation over the hole. [End] then fills the hole and the computation runs
  (`normV`). The runtime's errors are explicit (`Except Err`).

  §1 values and meanings · §2 substitution, wholeness, normalisation · §3 the concrete runtime ·
  §4 error reflection (part 1) · §5 well-formedness preservation (part 2) · §6 runtime `J`
  (part 3) · §7 the drop at the join (part 4, D84).
-/
set_option autoImplicit false

namespace Ochr.Model.Safety

/-! ## §1. Values and meanings (as in `State2.lean`) -/

/-- An injective backward function with its forward value. -/
abbrev BackN : Type := {p : Nat × (Nat → Nat) // ∀ v w, p.2 v = p.2 w → v = w}

/-- An assignment: abstract numerals (none occur at runtime) and the meaning of `σ_g`. -/
structure Rho where
  σ : Nat → Nat
  g : Nat → BackN

abbrev Var := Nat
abbrev Label := Nat

inductive Val where
  | num (n : Nat)
  | abs (i : Nat)
  | bot
  | pair (a b : Val)
  | borrow (l : Label) (v : Val)
  | loan (l : Label)
  | gFwd (u : Val)
  | gBack (u h : Val)
  deriving Inhabited, DecidableEq

inductive SV where
  | num (n : Nat)
  | pair (a b : SV)
  | bot
  deriving DecidableEq

inductive SV.le : SV → SV → Prop
  | bot (a : SV) : SV.le .bot a
  | num (n : Nat) : SV.le (.num n) (.num n)
  | pair {a b a' b' : SV} : SV.le a a' → SV.le b b' → SV.le (.pair a b) (.pair a' b')

theorem SV.le_refl : ∀ a : SV, SV.le a a
  | .num n => .num n
  | .pair a b => .pair (SV.le_refl a) (SV.le_refl b)
  | .bot => .bot _

theorem SV.le_trans : ∀ {a b c : SV}, SV.le a b → SV.le b c → SV.le a c
  | _, _, _, .bot _, _ => .bot _
  | _, _, _, .num _, h => h
  | _, _, _, .pair h₁ h₂, .pair h₁' h₂' => .pair (SV.le_trans h₁ h₁') (SV.le_trans h₂ h₂')

abbrev Future : Type := Label → SV

def fupd (f : Future) (l : Label) (n : SV) : Future := fun l' => if l' = l then n else f l'

def backSV (ρ : Rho) : SV → SV → SV
  | .num d, .num v => .num ((ρ.g d).val.2 v)
  | _, _ => .bot

def fwdSV (ρ : Rho) : SV → SV
  | .num d => .num (ρ.g d).val.1
  | _ => .bot

def ev (ρ : Rho) (f : Future) : Val → SV
  | .num n => .num n
  | .abs i => .num (ρ.σ i)
  | .bot => .bot
  | .pair a b => .pair (ev ρ f a) (ev ρ f b)
  | .borrow _ v => ev ρ f v
  | .loan l => f l
  | .gFwd u => fwdSV ρ (ev ρ f u)
  | .gBack u h => backSV ρ (ev ρ f u) (ev ρ f h)

abbrev St : Type := Var → Val
abbrev Mean : Type := Future → Var → SV

def M (ρ : Rho) (Ω : St) : Mean := fun f x => ev ρ f (Ω x)

def upd (Ω : St) (x : Var) (v : Val) : St := fun y => if y = x then v else Ω y
def oupd (m : Var → SV) (x : Var) (o : SV) : Var → SV := fun y => if y = x then o else m y

def Below (m' m : Mean) : Prop := ∀ f', ∃ f, ∀ z, SV.le (m' f' z) (m f z)

theorem Below.refl (m : Mean) : Below m m := fun f => ⟨f, fun _ => SV.le_refl _⟩

theorem Below.trans {a b c : Mean} (h₁ : Below a b) (h₂ : Below b c) : Below a c := fun f => by
  obtain ⟨f₁, h₁⟩ := h₁ f
  obtain ⟨f₂, h₂⟩ := h₂ f₁
  exact ⟨f₂, fun z => SV.le_trans (h₁ z) (h₂ z)⟩

/-! ## §2. Substitution, wholeness, normalisation -/

def substV (l : Label) (w : Val) : Val → Val
  | .loan l' => if l' = l then w else .loan l'
  | .pair a b => .pair (substV l w a) (substV l w b)
  | .borrow l' v => .borrow l' (substV l w v)
  | .gFwd u => .gFwd (substV l w u)
  | .gBack u h => .gBack (substV l w u) (substV l w h)
  | v => v

def substSt (Ω : St) (l : Label) (w : Val) : St := fun y => substV l w (Ω y)

theorem ev_subst (ρ : Rho) (f : Future) (l : Label) (w : Val) :
    ∀ t, ev ρ f (substV l w t) = ev ρ (fupd f l (ev ρ f w)) t := by
  intro t
  induction t with
  | num _ => rfl
  | abs _ => rfl
  | bot => rfl
  | pair a b iha ihb => simp only [substV, ev, iha, ihb]
  | borrow _ v ih => simp only [substV, ev, ih]
  | loan l' =>
    by_cases h : l' = l
    · subst h; simp [substV, ev, fupd]
    · simp [substV, ev, fupd, h]
  | gFwd u ih => simp only [substV, ev, ih]
  | gBack u h ihu ihh => simp only [substV, ev, ihu, ihh]

def loans : Val → List Label
  | .loan l => [l]
  | .pair a b => loans a ++ loans b
  | .borrow _ v => loans v
  | .gFwd u => loans u
  | .gBack u h => loans u ++ loans h
  | _ => []

def ownedLoans : Val → List Label
  | .borrow _ _ => []
  | .pair a b => ownedLoans a ++ ownedLoans b
  | v => loans v

theorem ev_congr (ρ : Rho) (f f' : Future) :
    ∀ t, (∀ l, l ∈ loans t → f l = f' l) → ev ρ f t = ev ρ f' t := by
  intro t
  induction t with
  | num _ => intro _; rfl
  | abs _ => intro _; rfl
  | bot => intro _; rfl
  | pair a b iha ihb =>
    intro h; simp only [ev]
    rw [iha fun l hl => h l (by simp [loans, hl]), ihb fun l hl => h l (by simp [loans, hl])]
  | borrow _ v ih => intro h; simp only [ev]; exact ih h
  | loan l => intro h; simp [ev, h l (by simp [loans])]
  | gFwd u ih => intro h; simp only [ev]; rw [ih h]
  | gBack u k ihu ihk =>
    intro h; simp only [ev]
    rw [ihu fun l hl => h l (by simp [loans, hl]), ihk fun l hl => h l (by simp [loans, hl])]

/-- A value is whole when no `⊥` occurs in it. -/
def wholeV : Val → Bool
  | .bot => false
  | .pair a b => wholeV a && wholeV b
  | .borrow _ v => wholeV v
  | .gFwd u => wholeV u
  | .gBack u h => wholeV u && wholeV h
  | _ => true

def hasBot : SV → Bool
  | .bot => true
  | .pair a b => hasBot a || hasBot b
  | .num _ => false

/-- A value that is not whole means no information somewhere, under every future. No typing is
needed: `⊥` survives pairs and borrows, and a sealed program over a non-numeral means `bot`. -/
theorem notWhole_hasBot (ρ : Rho) (f : Future) : ∀ v, wholeV v = false → hasBot (ev ρ f v) = true := by
  intro v
  induction v with
  | num _ => intro h; simp [wholeV] at h
  | abs _ => intro h; simp [wholeV] at h
  | bot => intro _; rfl
  | pair a b iha ihb =>
    intro h
    simp only [wholeV, Bool.and_eq_false_iff] at h
    simp only [ev, hasBot, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (iha h)
    · exact Or.inr (ihb h)
  | borrow _ v ih => intro h; exact ih h
  | loan _ => intro h; simp [wholeV] at h
  | gFwd u ih =>
    intro h
    simp only [ev, fwdSV]
    split
    · next d hd => have := ih h; rw [hd] at this; simp [hasBot] at this
    · rfl
  | gBack u k ihu ihk =>
    intro h
    simp only [wholeV, Bool.and_eq_false_iff] at h
    simp only [ev, backSV]
    split
    · next d w hu hk =>
      rcases h with h | h
      · have := ihu h; rw [hu] at this; simp [hasBot] at this
      · have := ihk h; rw [hk] at this; simp [hasBot] at this
    · rfl

/-- The runtime runs a pending backward computation once its hole is filled with a numeral. -/
def normV (ρ : Rho) : Val → Val
  | .pair a b => .pair (normV ρ a) (normV ρ b)
  | .borrow l v => .borrow l (normV ρ v)
  | .gFwd u =>
    match normV ρ u with
    | .num d => .num (ρ.g d).val.1
    | u' => .gFwd u'
  | .gBack u h =>
    match normV ρ u, normV ρ h with
    | .num d, .num w => .num ((ρ.g d).val.2 w)
    | u', h' => .gBack u' h'
  | v => v

/-- Running a filled computation keeps the meaning. -/
theorem ev_normV (ρ : Rho) (f : Future) : ∀ v, ev ρ f (normV ρ v) = ev ρ f v := by
  intro v
  induction v with
  | num _ => rfl
  | abs _ => rfl
  | bot => rfl
  | pair a b iha ihb => simp only [normV, ev, iha, ihb]
  | borrow _ v ih => simp only [normV, ev, ih]
  | loan _ => rfl
  | gFwd u ih =>
    simp only [normV]
    split
    · next d hd => simp only [ev, ← ih, hd, fwdSV]
    · simp only [ev, ih]
  | gBack u k ihu ihk =>
    simp only [normV]
    split
    · next d w hu hk => simp only [ev, ← ihu, ← ihk, hu, hk, backSV]
    · simp only [ev, ihu, ihk]

/-! ## §3. The concrete runtime -/

/-- The runtime's errors. -/
inductive Err where
  | readBot          -- reading `⊥`, or a value partly moved out
  | endNotWhole      -- a borrow ends while its content is partly moved out
  | dropInFlight     -- a drop meets a borrower that is a value in flight
  | assignOverLoans  -- an assignment overwrites a value still lent
  | endedBorrow      -- an access through a borrow that has ended
  | illTyped         -- a path that does not fit the value (excluded by typing)
  | outOfFuel        -- undecided
  deriving DecidableEq

def holds (l : Label) : Val → Bool
  | .borrow l' _ => l' == l
  | _ => false

def findBorrow (N : Nat) (Ω : St) (l : Label) : Option Var := (List.range N).find? fun x => holds l (Ω x)
def live (N : Nat) (Ω : St) (l : Label) : Bool := (findBorrow N Ω l).isSome

inductive Step where
  | deref | fst | snd

/-- Following a path, with the runtime's errors. -/
def cFollow : Val → List Step → Except Err Val
  | v, [] => .ok v
  | .borrow _ v, .deref :: ss => cFollow v ss
  | .pair a _, .fst :: ss => cFollow a ss
  | .pair _ b, .snd :: ss => cFollow b ss
  | .bot, .deref :: _ => .error .endedBorrow
  | .bot, _ :: _ => .error .readBot
  | _, _ :: _ => .error .illTyped

/-- The meaning of a place: a borrow means its content, so `*` is transparent; projecting no
information gives no information; `none` is a path that does not fit (ill-typed). -/
def placeSV : SV → List Step → Option SV
  | v, [] => some v
  | v, .deref :: ss => placeSV v ss
  | .pair a _, .fst :: ss => placeSV a ss
  | .pair _ b, .snd :: ss => placeSV b ss
  | .bot, _ :: _ => some .bot
  | _, _ :: _ => none

theorem placeSV_bot : ∀ ss, placeSV .bot ss = some .bot
  | [] => rfl
  | .deref :: ss => by simp only [placeSV]; exact placeSV_bot ss
  | .fst :: _ => rfl
  | .snd :: _ => rfl

/-- What the runtime finds at a place is what the place means. -/
theorem cFollow_ok (ρ : Rho) (f : Future) :
    ∀ ps v w, cFollow v ps = .ok w → placeSV (ev ρ f v) ps = some (ev ρ f w) := by
  intro ps
  induction ps with
  | nil => intro v w h; simp only [cFollow] at h; cases h; rfl
  | cons s ss ih =>
    intro v w h
    cases s <;> cases v <;> simp only [cFollow] at h <;> (try cases h)
    all_goals first
      | (simp only [ev, placeSV]; exact ih _ _ h)
      | skip

/-- Error reflection for paths: an access through an ended borrow, or into a moved-out part,
is one whose place means no information, under every future. -/
theorem cFollow_err (ρ : Rho) (f : Future) :
    ∀ ps v, (cFollow v ps = .error .endedBorrow ∨ cFollow v ps = .error .readBot) →
      placeSV (ev ρ f v) ps = some .bot := by
  intro ps
  induction ps with
  | nil => intro v h; simp [cFollow] at h
  | cons s ss ih =>
    intro v h
    cases s <;> cases v <;> simp only [cFollow] at h
    all_goals first
      | (simp only [ev, placeSV]; exact ih _ h)
      | (simp only [ev, placeSV]; exact placeSV_bot _)
      | rfl
      | (simp at h)

/-- The runtime's [End]: refused when the content is partly moved out; then the hole is filled
and any pending computation that is now complete runs. -/
def normSt (ρ : Rho) (Ω : St) : St := fun x => normV ρ (Ω x)

def cEndL (ρ : Rho) (N : Nat) (Ω : St) (l : Label) : Except Err St :=
  match findBorrow N Ω l with
  | some r =>
    match Ω r with
    | .borrow _ c => if wholeV c then .ok (normSt ρ (upd (substSt Ω l c) r .bot)) else .error .endNotWhole
    | _ => .ok Ω
  | none => .ok Ω

/-- [End] on meanings, as in `State2.lean`. -/
def semEnd (Mn : Mean) (r : Var) (l : Label) : Mean := fun f =>
  oupd (Mn (fupd f l (Mn f r))) r .bot

theorem M_normSt (ρ : Rho) (Ω : St) : M ρ (normSt ρ Ω) = M ρ Ω :=
  funext fun f => funext fun x => ev_normV ρ f (Ω x)

theorem step_end (ρ : Rho) (Ω : St) (r : Var) (l : Label) (c : Val)
    (hr : Ω r = .borrow l c) : M ρ (upd (substSt Ω l c) r .bot) = semEnd (M ρ Ω) r l := by
  funext f z
  have hMr : M ρ Ω f r = ev ρ f c := by simp [M, hr, ev]
  simp only [semEnd, hMr, oupd]
  by_cases hz : z = r
  · subst hz; simp [M, upd, ev]
  · simp only [M, upd, hz, if_false, substSt]
    exact ev_subst ρ f l c (Ω z)

theorem semEnd_below (Mn : Mean) (r : Var) (l : Label) : Below (semEnd Mn r l) Mn := by
  intro f'
  refine ⟨fupd f' l (Mn f' r), fun z => ?_⟩
  simp only [semEnd, oupd]
  by_cases hz : z = r
  · simp only [hz, if_true]; exact .bot _
  · simp only [hz, if_false]; exact SV.le_refl _

theorem holds_find {N : Nat} {Ω : St} {l : Label} {r : Var} (h : findBorrow N Ω l = some r) :
    holds l (Ω r) = true := by
  have h' := List.find?_some (show (List.range N).find? (fun x => holds l (Ω x)) = some r from h)
  exact h'

/-- A successful runtime [End] loses only information. -/
theorem cEndL_ok (ρ : Rho) (N : Nat) (Ω Ω' : St) (l : Label) (h : cEndL ρ N Ω l = .ok Ω') :
    Below (M ρ Ω') (M ρ Ω) := by
  unfold cEndL at h
  split at h
  · next r hf =>
    split at h
    · next l' c hr =>
      have : l' = l := by simpa [holds, hr] using holds_find hf
      subst this
      split at h
      · cases h; rw [M_normSt, step_end ρ Ω r l' c hr]; exact semEnd_below _ _ _
      · cases h
    · cases h; exact Below.refl _
  · cases h; exact Below.refl _

/-- Error reflection for [End]: the runtime refuses an end exactly where the holder's current
content means no information somewhere, under every future, so the reference [End] errs too. -/
theorem cEndL_err (ρ : Rho) (N : Nat) (Ω : St) (l : Label) (e : Err) (h : cEndL ρ N Ω l = .error e) :
    e = .endNotWhole ∧ ∃ r, findBorrow N Ω l = some r ∧ ∀ f, hasBot (M ρ Ω f r) = true := by
  unfold cEndL at h
  split at h
  · next r hf =>
    split at h
    · next l' c hr =>
      split at h
      · cases h
      · next hw =>
        cases h
        refine ⟨rfl, r, hf, fun f => ?_⟩
        simp only [M, hr, ev]
        exact notWhole_hasBot ρ f c (by simpa using hw)
    · cases h
  · cases h

/-! ### [Access], as in `State2.lean`, with the runtime's [End] -/

def stepV : Step → Val → Option Val
  | .deref, .borrow _ v => some v
  | .fst, .pair a _ => some a
  | .snd, .pair _ b => some b
  | _, _ => none

def follow (v : Val) : List Step → Option Val
  | [] => some v
  | s :: ss => (stepV s v).bind (follow · ss)

def firstLiveOnPath (N : Nat) (Ω : St) : Val → List Step → Option Label
  | .loan l, _ => if live N Ω l then some l else none
  | v, s :: ss => (stepV s v).bind (firstLiveOnPath N Ω · ss)
  | _, [] => none

def isNeutral : Val → Bool
  | .abs _ | .gFwd _ | .gBack _ _ => true
  | _ => false

inductive Mode where
  | read | assign | matchHead

def accessStep (N : Nat) (Ω : St) (m : Mode) (x : Var) (ps : List Step) : Option Label :=
  match firstLiveOnPath N Ω (Ω x) ps with
  | some l => some l
  | none =>
    match follow (Ω x) ps with
    | none => none
    | some v =>
      match m with
      | .read => (loans v).find? (live N Ω)
      | .assign => (ownedLoans v).find? (live N Ω)
      | .matchHead => if isNeutral v then (loans v).find? (live N Ω) else none

def cAccess (ρ : Rho) (N : Nat) : Nat → St → Mode → Var → List Step → Except Err St
  | 0, _, _, _, _ => .error .outOfFuel
  | fuel + 1, Ω, m, x, ps =>
    match accessStep N Ω m x ps with
    | some l =>
      match cEndL ρ N Ω l with
      | .ok Ω' => cAccess ρ N fuel Ω' m x ps
      | .error e => .error e
    | none => .ok Ω

/-- A successful access loses only information, and leaves nothing for it to end. -/
theorem cAccess_ok (ρ : Rho) (N : Nat) :
    ∀ fuel Ω m x ps Ω', cAccess ρ N fuel Ω m x ps = .ok Ω' →
      Below (M ρ Ω') (M ρ Ω) ∧ accessStep N Ω' m x ps = none := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [cAccess] at h
  | succ fuel ih =>
    intro Ω m x ps Ω' h
    simp only [cAccess] at h
    split at h
    · split at h
      · next Ω₁ h₁ =>
        obtain ⟨hb, hp⟩ := ih _ _ _ _ _ h
        exact ⟨hb.trans (cEndL_ok ρ N Ω Ω₁ _ h₁), hp⟩
      · cases h
    · next hn => cases h; exact ⟨Below.refl _, hn⟩

/-- Error reflection for an access: it is undecided (out of fuel), or an [End] it makes is refused,
at a state below the start, where the reference [End] errs too. -/
theorem cAccess_err (ρ : Rho) (N : Nat) :
    ∀ fuel Ω m x ps e, cAccess ρ N fuel Ω m x ps = .error e →
      e = .outOfFuel ∨ (e = .endNotWhole ∧ ∃ Ω₁ l r, Below (M ρ Ω₁) (M ρ Ω) ∧
        findBorrow N Ω₁ l = some r ∧ ∀ f, hasBot (M ρ Ω₁ f r) = true) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ e h; simp only [cAccess] at h; cases h; exact Or.inl rfl
  | succ fuel ih =>
    intro Ω m x ps e h
    simp only [cAccess] at h
    split at h
    · next l _ =>
      split at h
      · next Ω₁ h₁ =>
        rcases ih _ _ _ _ _ h with h' | ⟨he, Ω₂, l', r, hb, hf, hbot⟩
        · exact Or.inl h'
        · exact Or.inr ⟨he, Ω₂, l', r, hb.trans (cEndL_ok ρ N Ω Ω₁ _ h₁), hf, hbot⟩
      · next e' h₁ =>
        obtain ⟨he, r, hf, hbot⟩ := cEndL_err ρ N Ω l e' h₁
        have hee : e' = e := by injection h
        subst hee
        exact Or.inr ⟨he, Ω, l, r, Below.refl _, hf, hbot⟩
    · cases h

/-! ## §4. Error reflection

The reference errs where the meaning says it must: a read whose place means no information
somewhere (`ReadErr`), an end whose holder's content does (`EndErr`), and a drop of a place whose
meaning depends on a borrow in flight (`DropErr`, below). For each runtime operation, an error is
out of fuel (undecided), an ill-typed path (excluded by typing, part of well-formedness), or a
reference error at a state below the start. -/

def ReadErr (Mn : Mean) (x : Var) (ps : List Step) : Prop :=
  ∀ f, ∃ s, placeSV (Mn f x) ps = some s ∧ hasBot s = true
def EndErr (Mn : Mean) : Prop := ∃ r, ∀ f, hasBot (Mn f r) = true

theorem cFollow_err_cases : ∀ ps v e, cFollow v ps = .error e →
    e = .endedBorrow ∨ e = .readBot ∨ e = .illTyped := by
  intro ps
  induction ps with
  | nil => intro v e h; simp [cFollow] at h
  | cons s ss ih =>
    intro v e h
    cases s <;> cases v <;> simp only [cFollow] at h
    all_goals first
      | exact ih _ _ h
      | (cases h; simp)

theorem cFollow_follow : ∀ ps v w, cFollow v ps = .ok w → follow v ps = some w := by
  intro ps
  induction ps with
  | nil => intro v w h; simp only [cFollow] at h; cases h; rfl
  | cons s ss ih =>
    intro v w h
    cases s <;> cases v <;> simp only [cFollow] at h
    all_goals first
      | (simp only [follow, stepV, Option.bind_some]; exact ih _ _ h)
      | cases h

/-- A read that copies: `dst := clone(p)`. -/
def cClone (ρ : Rho) (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (dst : Var) : Except Err St :=
  match cAccess ρ N fuel Ω .read x ps with
  | .error e => .error e
  | .ok Ω₁ =>
    match cFollow (Ω₁ x) ps with
    | .error e => .error e
    | .ok v => if wholeV v then .ok (upd Ω₁ dst v) else .error .readBot

/-- Error reflection for a read. -/
theorem cClone_reflect (ρ : Rho) (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (dst : Var)
    (e : Err) (h : cClone ρ N fuel Ω x ps dst = .error e) :
    e = .outOfFuel ∨ e = .illTyped ∨
      ∃ Ω₁, Below (M ρ Ω₁) (M ρ Ω) ∧ (EndErr (M ρ Ω₁) ∨ ReadErr (M ρ Ω₁) x ps) := by
  unfold cClone at h
  split at h
  · next e' ha =>
    have hee : e' = e := by injection h
    subst hee
    rcases cAccess_err ρ N fuel Ω .read x ps e' ha with h' | ⟨_, Ω₁, _, r, hb, _, hbot⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inr ⟨Ω₁, hb, Or.inl ⟨r, hbot⟩⟩)
  · next Ω₁ ha =>
    have hb := (cAccess_ok ρ N fuel Ω .read x ps Ω₁ ha).1
    split at h
    · next e' hf =>
      have hee : e' = e := by injection h
      subst hee
      rcases cFollow_err_cases ps _ e' hf with h' | h' | h'
      · subst h'
        exact Or.inr (Or.inr ⟨Ω₁, hb, Or.inr fun f =>
          ⟨.bot, cFollow_err ρ f ps _ (Or.inl hf), rfl⟩⟩)
      · subst h'
        exact Or.inr (Or.inr ⟨Ω₁, hb, Or.inr fun f =>
          ⟨.bot, cFollow_err ρ f ps _ (Or.inr hf), rfl⟩⟩)
      · exact Or.inr (Or.inl h')
    · next v hf =>
      split at h
      · cases h
      · next hw =>
        have hee : Err.readBot = e := by injection h
        subst hee
        exact Or.inr (Or.inr ⟨Ω₁, hb, Or.inr fun f =>
          ⟨ev ρ f v, cFollow_ok ρ f ps _ v hf, notWhole_hasBot ρ f v (by simpa using hw)⟩⟩)

/-- …and when it succeeds, `dst` means what the place meant, after an access that lost only
information. -/
theorem cClone_ok (ρ : Rho) (N fuel : Nat) (Ω Ω' : St) (x : Var) (ps : List Step) (dst : Var)
    (h : cClone ρ N fuel Ω x ps dst = .ok Ω') :
    ∃ Ω₁, Below (M ρ Ω₁) (M ρ Ω) ∧ Ω' = upd Ω₁ dst (Ω' dst) ∧
      ∀ f, placeSV (M ρ Ω₁ f x) ps = some (M ρ Ω' f dst) := by
  unfold cClone at h
  split at h
  · cases h
  · next Ω₁ ha =>
    split at h
    · cases h
    · next v hf =>
      split at h
      · cases h
        refine ⟨Ω₁, (cAccess_ok ρ N fuel Ω .read x ps Ω₁ ha).1, ?_, fun f => ?_⟩
        · funext y; simp [upd]
        · simp only [M, upd, if_true]; exact cFollow_ok ρ f ps _ v hf
      · cases h

/-! ### Assignment: overwriting a lent value is unreachable

After an assignment's (owned) access, the old content holds no live loan in the part it owns.
With no borrow inside data (WF1), that part is all of it, so the runtime's "assigning over
outer loans" error can only fire at a state that violates well-formedness. -/

def noBorrow : Val → Bool
  | .borrow _ _ => false
  | .pair a b => noBorrow a && noBorrow b
  | .gFwd u => noBorrow u
  | .gBack u h => noBorrow u && noBorrow h
  | _ => true

theorem ownedLoans_noBorrow : ∀ v, noBorrow v = true → ownedLoans v = loans v := by
  intro v
  induction v with
  | pair a b iha ihb =>
    intro h
    simp only [noBorrow, Bool.and_eq_true] at h
    simp only [ownedLoans, loans, iha h.1, ihb h.2]
  | borrow _ _ _ => intro h; simp [noBorrow] at h
  | _ => intro _; rfl

def updAt (w : Val) : List Step → Val → Option Val
  | [], _ => some w
  | .deref :: ss, .borrow l v => (updAt w ss v).map (.borrow l)
  | .fst :: ss, .pair a b => (updAt w ss a).map (.pair · b)
  | .snd :: ss, .pair a b => (updAt w ss b).map (.pair a ·)
  | _, _ => none

def setPlace (Ω : St) (x : Var) (ps : List Step) (w : Val) : Except Err St :=
  match updAt w ps (Ω x) with
  | some v' => .ok (upd Ω x v')
  | none => .error .illTyped

def cAssign (ρ : Rho) (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (w : Val) : Except Err St :=
  match cAccess ρ N fuel Ω .assign x ps with
  | .error e => .error e
  | .ok Ω₁ =>
    match cFollow (Ω₁ x) ps with
    | .error e => .error e
    | .ok old =>
      match old with
      | .borrow l _ =>
        match cEndL ρ N Ω₁ l with
        | .ok Ω₂ => setPlace Ω₂ x ps w
        | .error e => .error e
      | _ => if (loans old).any (live N Ω₁) then .error .assignOverLoans else setPlace Ω₁ x ps w

theorem setPlace_err (Ω : St) (x : Var) (ps : List Step) (w : Val) (e : Err)
    (h : setPlace Ω x ps w = .error e) : e = .illTyped := by
  unfold setPlace at h
  split at h
  · cases h
  · injection h with h; exact h.symm

theorem cAssign_overLoans (ρ : Rho) (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (w : Val)
    (h : cAssign ρ N fuel Ω x ps w = .error .assignOverLoans) :
    ∃ (Ω₁ : St) (old : Val), cFollow (Ω₁ x) ps = .ok old ∧ noBorrow old = false := by
  unfold cAssign at h
  split at h
  · next e ha =>
    have hee : e = .assignOverLoans := by injection h
    subst hee
    rcases cAccess_err ρ N fuel Ω .assign x ps _ ha with h' | ⟨h', _⟩ <;> cases h'
  · next Ω₁ ha =>
    have hpost := (cAccess_ok ρ N fuel Ω .assign x ps Ω₁ ha).2
    split at h
    · next e hf =>
      have hee : e = .assignOverLoans := by injection h
      subst hee
      rcases cFollow_err_cases ps _ _ hf with h' | h' | h' <;> cases h'
    · next old hf =>
      split at h
      · split at h
        · have := setPlace_err _ _ _ _ _ h; cases this
        · next e he =>
          have hee : e = .assignOverLoans := by injection h
          subst hee
          have := (cEndL_err ρ N Ω₁ _ _ he).1; cases this
      · next hnb =>
        split at h
        · next hany =>
          refine ⟨Ω₁, old, hf, ?_⟩
          cases hnb' : noBorrow old
          · rfl
          · exfalso
            have hfo := cFollow_follow ps _ old hf
            simp only [accessStep] at hpost
            split at hpost
            · cases hpost
            · simp only [hfo] at hpost
              rw [ownedLoans_noBorrow old hnb'] at hpost
              have hnone := List.find?_eq_none.mp hpost
              obtain ⟨l, hl, hlive⟩ := List.any_eq_true.mp hany
              exact hnone l hl hlive
        · have := setPlace_err _ _ _ _ _ h; cases this

/-! ### [Drop]: a borrower in flight, and why reflection needs injectivity

The runtime refuses a drop when a live loan in the dropped value is held by a value in flight. The
reference sees no loans, only meanings: it refuses a drop of a place whose meaning *depends* on a
label held in flight. These agree because a loan always sits where the meaning depends on it:
in pairs, behind a borrow, or as the hole of a chain of backward computations, each injective.
With a constant backward function, a fill's meaning would ignore its hole while the runtime still
saw the loan, and the reflection would fail. So the reflection uses R. -/

/-- Where a hole may sit: a chain of backward computations over numerals. -/
inductive Hole : Val → Prop
  | loan (l : Label) : Hole (.loan l)
  | num (n : Nat) : Hole (.num n)
  | gBack (d : Nat) {h : Val} : Hole h → Hole (.gBack (.num d) h)

/-- The runtime shape of values (part of well-formedness). -/
inductive Shaped : Val → Prop
  | num (n : Nat) : Shaped (.num n)
  | bot : Shaped .bot
  | loan (l : Label) : Shaped (.loan l)
  | pair {a b : Val} : Shaped a → Shaped b → Shaped (.pair a b)
  | borrow (l : Label) {v : Val} : Shaped v → Shaped (.borrow l v)
  | gBack (d : Nat) {h : Val} : Hole h → Shaped (.gBack (.num d) h)

theorem hole_inj (ρ : Rho) (l : Label) : ∀ {h : Val}, Hole h → l ∈ loans h → ∀ f,
    ∃ φ : Nat → Nat, (∀ a b, φ a = φ b → a = b) ∧ ∀ n, ev ρ (fupd f l (.num n)) h = .num (φ n) := by
  intro h hh
  induction hh with
  | loan l' =>
    intro hl f
    have : l = l' := by simpa [loans] using hl
    subst this
    exact ⟨id, fun _ _ e => e, fun n => by simp [ev, fupd]⟩
  | num _ => intro hl; simp [loans] at hl
  | gBack d _ ih =>
    intro hl f
    obtain ⟨φ, hφ, hev⟩ := ih (by simpa [loans] using hl) f
    refine ⟨fun n => (ρ.g d).val.2 (φ n), fun a b e => hφ a b ((ρ.g d).property _ _ e), fun n => ?_⟩
    simp only [ev, hev, backSV]

/-- In a shaped value, the meaning is injective in every loan it holds. -/
theorem shaped_dep (ρ : Rho) (l : Label) : ∀ {v : Val}, Shaped v → l ∈ loans v → ∀ f,
    ∀ a b : Nat, ev ρ (fupd f l (.num a)) v = ev ρ (fupd f l (.num b)) v → a = b := by
  intro v hv
  induction hv with
  | num _ => intro hl; simp [loans] at hl
  | bot => intro hl; simp [loans] at hl
  | loan l' =>
    intro hl f a b e
    have : l = l' := by simpa [loans] using hl
    subst this
    simpa [ev, fupd] using e
  | pair _ _ iha ihb =>
    intro hl f a b e
    simp only [ev, SV.pair.injEq] at e
    rcases List.mem_append.mp hl with hl | hl
    · exact iha hl f a b e.1
    · exact ihb hl f a b e.2
  | borrow _ _ ih => intro hl f a b e; exact ih hl f a b e
  | gBack d hh =>
    intro hl f a b e
    obtain ⟨φ, hφ, hev⟩ := hole_inj ρ l hh (by simpa [loans] using hl) f
    simp only [ev, hev, backSV, SV.num.injEq] at e
    exact hφ a b ((ρ.g d).property _ _ e)

/-- The reference refuses to drop `x` while its meaning depends on label `l`. -/
def DropErr (Mn : Mean) (x : Var) (l : Label) : Prop :=
  ∀ f, ∀ a b : Nat, Mn (fupd f l (.num a)) x = Mn (fupd f l (.num b)) x → a = b

def cDropLoop (ρ : Rho) (N : Nat) (temp : Var → Bool) : Nat → St → Var → Except Err St
  | 0, _, _ => .error .outOfFuel
  | fuel + 1, Ω, x =>
    match (loans (Ω x)).find? (live N Ω) with
    | some l =>
      match findBorrow N Ω l with
      | some hv =>
        if temp hv then .error .dropInFlight else
        match cEndL ρ N Ω l with
        | .ok Ω' => cDropLoop ρ N temp fuel Ω' x
        | .error e => .error e
      | none => .ok Ω
    | none => .ok Ω

/-- Error reflection for a drop meeting a borrower in flight: at a state below the start, the
dropped place holds a live loan held in flight; if that state is shaped there, the reference
refuses the drop too. -/
theorem cDropLoop_inFlight (ρ : Rho) (N : Nat) (temp : Var → Bool) :
    ∀ fuel Ω x, cDropLoop ρ N temp fuel Ω x = .error .dropInFlight →
      ∃ Ω₁ l hv, Below (M ρ Ω₁) (M ρ Ω) ∧ l ∈ loans (Ω₁ x) ∧ findBorrow N Ω₁ l = some hv ∧
        temp hv = true ∧ (Shaped (Ω₁ x) → DropErr (M ρ Ω₁) x l) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; simp only [cDropLoop] at h; cases h
  | succ fuel ih =>
    intro Ω x h
    simp only [cDropLoop] at h
    split at h
    · next l hl =>
      split at h
      · next hv hf =>
        split at h
        · next ht =>
          exact ⟨Ω, l, hv, Below.refl _, List.mem_of_find?_eq_some hl, hf, ht,
            fun hs f a b e => shaped_dep ρ l hs (List.mem_of_find?_eq_some hl) f a b e⟩
        · split at h
          · next Ω' h₁ =>
            obtain ⟨Ω₁, l', hv', hb, h1, h2, h3, h4⟩ := ih _ _ h
            exact ⟨Ω₁, l', hv', hb.trans (cEndL_ok ρ N Ω Ω' _ h₁), h1, h2, h3, h4⟩
          · next e he =>
            have hee : e = .dropInFlight := by injection h
            subst hee
            have := (cEndL_err ρ N Ω _ _ he).1; cases this
      · cases h
    · cases h

/-! ### A call of the concrete `σ_g`

`r := g(t)`, `t` holding `borrow_l u`: at runtime `u` must be a numeral `d`. The forward value is
computed at once, and the lent place gets the pending backward computation over the hole `k`. -/

def cCall (ρ : Rho) (Ω : St) (t r : Var) (l k : Label) : Except Err St :=
  match Ω t with
  | .borrow l' (.num d) =>
    if l' = l then
      .ok (upd (upd (substSt Ω l (.gBack (.num d) (.loan k))) t .bot) r (.borrow k (.num (ρ.g d).val.1)))
    else .error .illTyped
  | .borrow _ u => if wholeV u then .error .illTyped else .error .readBot
  | _ => .error .illTyped

/-- The reference call: apply `σ_g`'s meaning at what `t` reads. -/
def semCall (ρ : Rho) (Mn : Mean) (t r : Var) (l k : Label) : Mean := fun f =>
  oupd (oupd (Mn (fupd f l (backSV ρ (Mn f t) (f k)))) t .bot) r (fwdSV ρ (Mn f t))

/-- A successful call means the reference call. -/
theorem cCall_ok (ρ : Rho) (Ω Ω' : St) (t r : Var) (l k : Label) (htr : t ≠ r)
    (h : cCall ρ Ω t r l k = .ok Ω') : M ρ Ω' = semCall ρ (M ρ Ω) t r l k := by
  unfold cCall at h
  split at h
  · next l' d ht =>
    split at h
    · next hl =>
      subst hl
      cases h
      funext f z
      have hMt : M ρ Ω f t = .num d := by simp [M, ht, ev]
      simp only [semCall, hMt, oupd]
      by_cases hr : z = r
      · subst hr; simp [M, upd, ev, fwdSV]
      · by_cases hzt : z = t
        · subst hzt; simp [M, upd, ev, hr]
        · simp only [hr, hzt, if_false, M, upd, substSt]
          rw [ev_subst ρ f l' _ (Ω z)]
          rfl
    · cases h
  · split at h <;> cases h
  · cases h

/-- Error reflection for a call: a moved-out argument means no information, so the reference
call errs too; otherwise the error is ill-typed. -/
theorem cCall_err (ρ : Rho) (Ω : St) (t r : Var) (l k : Label) (e : Err)
    (h : cCall ρ Ω t r l k = .error e) :
    e = .illTyped ∨ (e = .readBot ∧ ∀ f, hasBot (M ρ Ω f t) = true) := by
  unfold cCall at h
  split at h
  · split at h
    · cases h
    · injection h with h; exact Or.inl h.symm
  · next l' u _ _ =>
    have ht : Ω t = .borrow l' u := by assumption
    split at h
    · injection h with h; exact Or.inl h.symm
    · next hw =>
      injection h with h
      refine Or.inr ⟨h.symm, fun f => ?_⟩
      simp only [M, ht, ev]
      exact notWhole_hasBot ρ f u (by simpa using hw)
  · injection h with h; exact Or.inl h.symm
