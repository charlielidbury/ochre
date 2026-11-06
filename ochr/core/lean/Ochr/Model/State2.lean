/-
  Ochr.Model.State2: the four residuals of `Ochr/Model/State.lean`, for test 2 of `ochr/docs/23`.
  Standalone: it imports Lean core only, is not imported by `Ochr.lean`, and is checked with
  `lake env lean Ochr/Model/State2.lean` from `ochr/core/lean`.

  Changes from `State.lean`.
  * Values include pairs, and places are paths (`*`, `.0`, `.1`) from a variable.
  * Meanings are semantic values with `bot` *inside* them (`SV`), so a value partly moved out
    still means something: no information at the moved part. An order `⊑` compares meanings.
  * [Access] is derived, not given: an access to a place ends, one at a time, every borrow whose
    loan is on the path or inside the content, as the checker's `accessPath`, `accessInside` and
    `accessNeutralHead` do. An assignment ends only the loans in the part the place owns (D67),
    and a match ends the loans anywhere inside a neutral head (D29). Each end is [End], which
    keeps the meaning and loses only information.

  §1 values and meanings · §2 substitution · §3 [End] · §4 [Access] · §5 pairs and reborrows
  (residual 1) · §6 nested holes (2) · §7 `⊥` inside a borrow (3) · §8 [Drop] (4).
-/
set_option autoImplicit false

namespace Ochr.Model.State2

/-! ## §1. Values and meanings -/

/-- An injective backward function with its forward value: an element of the restricted
`Π(x : &Nat). &Nat` at one argument (R is the carrier, `Ochr/Model/Slice.lean`). -/
abbrev BackN : Type := {p : Nat × (Nat → Nat) // ∀ v w, p.2 v = p.2 w → v = w}

/-- An assignment: a value for each abstract numeral, and `σ_g`'s meaning. -/
structure Rho where
  σ : Nat → Nat
  g : Nat → BackN

abbrev Var := Nat
abbrev Label := Nat

/-- Values: numerals, abstract numerals, `⊥`, pairs, borrows, loans, and the sealed programs
[Close] makes for `σ_g` (`gFwd u` the returned borrow's content, `gBack u h` the lent place's fill
with hole `h`). -/
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

/-- Semantic values: numerals, pairs, and `bot`, no information. -/
inductive SV where
  | num (n : Nat)
  | pair (a b : SV)
  | bot
  deriving DecidableEq

/-- The information order: `bot` is below everything, and pairs are compared componentwise. -/
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

/-- A future: the final content of each borrow label. -/
abbrev Future : Type := Label → SV

def fupd (f : Future) (l : Label) (n : SV) : Future := fun l' => if l' = l then n else f l'

/-- `σ_g`'s backward function at semantic values; `bot` when either is not a numeral. -/
def backSV (ρ : Rho) : SV → SV → SV
  | .num d, .num v => .num ((ρ.g d).val.2 v)
  | _, _ => .bot

/-- `σ_g`'s forward value at a semantic value. -/
def fwdSV (ρ : Rho) : SV → SV
  | .num d => .num (ρ.g d).val.1
  | _ => .bot

/-- The meaning of a value: a loan means its borrow's final content, a borrow its current
content, a sealed program its call under ρ, and `⊥` means no information. -/
def ev (ρ : Rho) (f : Future) : Val → SV
  | .num n => .num n
  | .abs i => .num (ρ.σ i)
  | .bot => .bot
  | .pair a b => .pair (ev ρ f a) (ev ρ f b)
  | .borrow _ v => ev ρ f v
  | .loan l => f l
  | .gFwd u => fwdSV ρ (ev ρ f u)
  | .gBack u h => backSV ρ (ev ρ f u) (ev ρ f h)

/-- A state: what each variable holds. Searches range over the variables below a bound `N`. -/
abbrev St : Type := Var → Val
abbrev Mean : Type := Future → Var → SV

def M (ρ : Rho) (Ω : St) : Mean := fun f x => ev ρ f (Ω x)

def upd (Ω : St) (x : Var) (v : Val) : St := fun y => if y = x then v else Ω y
def oupd (m : Var → SV) (x : Var) (o : SV) : Var → SV := fun y => if y = x then o else m y

/-- `m'` loses only information relative to `m`: in every future of `m'`, every variable means
something below what it means under some future of `m`. -/
def Below (m' m : Mean) : Prop := ∀ f', ∃ f, ∀ z, SV.le (m' f' z) (m f z)

theorem Below.refl (m : Mean) : Below m m := fun f => ⟨f, fun _ => SV.le_refl _⟩

theorem Below.trans {a b c : Mean} (h₁ : Below a b) (h₂ : Below b c) : Below a c := fun f => by
  obtain ⟨f₁, h₁⟩ := h₁ f
  obtain ⟨f₂, h₂⟩ := h₂ f₁
  exact ⟨f₂, fun z => SV.le_trans (h₁ z) (h₂ z)⟩

/-! ## §2. Substitution, and what a meaning depends on -/

/-- Replace `loan_l` by `w` everywhere in a value. -/
def substV (l : Label) (w : Val) : Val → Val
  | .loan l' => if l' = l then w else .loan l'
  | .pair a b => .pair (substV l w a) (substV l w b)
  | .borrow l' v => .borrow l' (substV l w v)
  | .gFwd u => .gFwd (substV l w u)
  | .gBack u h => .gBack (substV l w u) (substV l w h)
  | v => v

def substSt (Ω : St) (l : Label) (w : Val) : St := fun y => substV l w (Ω y)

/-- Filling `loan_l` with `w` is fixing `l`'s final content to `w`'s meaning. Unconditional: a
partial `w` (with `⊥` inside) just fixes a partial final content. -/
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

/-- All loan labels in a value. -/
def loans : Val → List Label
  | .loan l => [l]
  | .pair a b => loans a ++ loans b
  | .borrow _ v => loans v
  | .gFwd u => loans u
  | .gBack u h => loans u ++ loans h
  | _ => []

/-- D67: the loans in the part of a value its place owns, not behind a borrow it holds. -/
def ownedLoans : Val → List Label
  | .borrow _ _ => []
  | .pair a b => ownedLoans a ++ ownedLoans b
  | v => loans v

/-- A value's meaning depends on the future only at its loans. -/
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

/-! ## §3. [End]

[End ℓ] takes `borrow_ℓ c` out of the variable `r` holding it (leaving `⊥`) and fills every
`loan_ℓ` with `c`. Its content may hold other loans (a reborrow's), and may be partial; the
checker refuses a partial one outside observations (§7), the meaning does not need to. -/

/-- Semantically: `ℓ`'s final content is what `r` reads now, and `r` reads nothing. -/
def semEnd (Mn : Mean) (r : Var) (l : Label) : Mean := fun f =>
  oupd (Mn (fupd f l (Mn f r))) r .bot

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

/-- Whether a value is `borrow_l _`. -/
def holds (l : Label) : Val → Bool
  | .borrow l' _ => l' == l
  | _ => false

/-- The variable below `N` holding `borrow_l`, if any: the loan is live exactly then. -/
def findBorrow (N : Nat) (Ω : St) (l : Label) : Option Var := (List.range N).find? fun x => holds l (Ω x)
def live (N : Nat) (Ω : St) (l : Label) : Bool := (findBorrow N Ω l).isSome

/-- [End ℓ] in the checker's form: a loan whose borrow is not held is inert, and nothing happens. -/
def endL (N : Nat) (Ω : St) (l : Label) : St :=
  match findBorrow N Ω l with
  | some r =>
    match Ω r with
    | .borrow _ c => upd (substSt Ω l c) r .bot
    | _ => Ω
  | none => Ω

theorem endL_below (ρ : Rho) (N : Nat) (Ω : St) (l : Label) : Below (M ρ (endL N Ω l)) (M ρ Ω) := by
  unfold endL
  split
  · next r hfind =>
    have hl : holds l (Ω r) = true := by
      have h := List.find?_some (show (List.range N).find? (fun x => holds l (Ω x)) = some r from hfind)
      exact h
    split
    · next l' c hr =>
      have : l' = l := by simpa [holds, hr] using hl
      subst this
      rw [step_end ρ Ω r l' c hr]; exact semEnd_below _ _ _
    · exact Below.refl _
  · exact Below.refl _

/-! ## §4. [Access], derived

A place is a variable and a path of steps. An access ends borrows one at a time, as the checker
does (`accessPath`, then `accessInside` or its owned form, or `accessNeutralHead`), until no live
loan is left where it looks. Each end is [End], so an access keeps the meaning up to information
(`access_below`). Running out of fuel is undecided (`none`), never a result. -/

inductive Step where
  | deref | fst | snd

def stepV : Step → Val → Option Val
  | .deref, .borrow _ v => some v
  | .fst, .pair a _ => some a
  | .snd, .pair _ b => some b
  | _, _ => none

def follow (v : Val) : List Step → Option Val
  | [] => some v
  | s :: ss => (stepV s v).bind (follow · ss)

/-- The first live loan on the path to a place, the place itself included (`firstLiveLoanOnPath`). -/
def firstLiveOnPath (N : Nat) (Ω : St) : Val → List Step → Option Label
  | .loan l, _ => if live N Ω l then some l else none
  | v, s :: ss => (stepV s v).bind (firstLiveOnPath N Ω · ss)
  | _, [] => none

/-- A neutral: an abstract value or a sealed program. -/
def isNeutral : Val → Bool
  | .abs _ | .gFwd _ | .gBack _ _ => true
  | _ => false

/-- What the access is for: a read or borrow (every loan in the content), an assignment (the loans
in the part the place owns, D67), or a match (the loans inside a neutral head, D29). -/
inductive Mode where
  | read | assign | matchHead

/-- The next borrow an access ends, if any. -/
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

/-- [Access]: end the next borrow until none is left. -/
def access (N : Nat) : Nat → St → Mode → Var → List Step → Option St
  | 0, _, _, _, _ => none
  | fuel + 1, Ω, m, x, ps =>
    match accessStep N Ω m x ps with
    | some l => access N fuel (endL N Ω l) m x ps
    | none => some Ω

/-- An access keeps the meaning, up to information: it is a sequence of [End]s. -/
theorem access_below (ρ : Rho) (N : Nat) :
    ∀ fuel Ω m x ps Ω', access N fuel Ω m x ps = some Ω' → Below (M ρ Ω') (M ρ Ω) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [access] at h
  | succ fuel ih =>
    intro Ω m x ps Ω' h
    simp only [access] at h
    split at h
    · exact (ih _ _ _ _ _ h).trans (endL_below ρ N Ω _)
    · cases h; exact Below.refl _

/-- When an access finishes, nothing is left for it to end. -/
theorem access_post (N : Nat) :
    ∀ fuel Ω m x ps Ω', access N fuel Ω m x ps = some Ω' → accessStep N Ω' m x ps = none := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [access] at h
  | succ fuel ih =>
    intro Ω m x ps Ω' h
    simp only [access] at h
    split at h
    · exact ih _ _ _ _ _ h
    · next hn => cases h; exact hn

/-- After a read's access, no loan in the content is live. -/
theorem read_post_live (N : Nat) (Ω : St) (x : Var) (ps : List Step) (v : Val)
    (h : accessStep N Ω .read x ps = none) (hv : follow (Ω x) ps = some v) :
    ∀ l, l ∈ loans v → live N Ω l = false := by
  intro l hl
  simp only [accessStep] at h
  split at h
  · simp at h
  · simp only [hv] at h
    have := List.find?_eq_none.mp h l hl
    simpa using this

/-- So, with no dangling loans (every loan's borrow is held: WF2), what a read takes means the
same under every future: the access reached every borrow, reborrows included, whose loan was in
it. -/
theorem read_value_indep (ρ : Rho) (N : Nat) (Ω : St) (x : Var) (ps : List Step) (v : Val)
    (h : accessStep N Ω .read x ps = none) (hv : follow (Ω x) ps = some v)
    (wf2 : ∀ l, l ∈ loans v → live N Ω l = true) (f f' : Future) : ev ρ f v = ev ρ f' v :=
  ev_congr ρ f f' v fun l hl => by
    have h₁ := read_post_live N Ω x ps v h hv l hl
    rw [wf2 l hl] at h₁; cases h₁

/-! ## §5. Residual 1: pairs, reborrows, and how far an access reaches

The operations, each its access followed by its effect. `none` is an error or exhausted fuel. -/

def updAt (w : Val) : List Step → Val → Option Val
  | [], _ => some w
  | .deref :: ss, .borrow l v => (updAt w ss v).map (.borrow l)
  | .fst :: ss, .pair a b => (updAt w ss a).map (.pair · b)
  | .snd :: ss, .pair a b => (updAt w ss b).map (.pair a ·)
  | _, _ => none

def setPlace (Ω : St) (x : Var) (ps : List Step) (w : Val) : Option St :=
  (updAt w ps (Ω x)).map (upd Ω x)

/-- [Borrow] `dst := &p` with the fresh label `l`. -/
def opBorrow (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (dst : Var) (l : Label) :
    Option St := do
  let Ω ← access N fuel Ω .read x ps
  let v ← follow (Ω x) ps
  match v with
  | .bot | .borrow _ _ => none
  | _ =>
    let Ω ← setPlace Ω x ps (.loan l)
    pure (upd Ω dst (.borrow l v))

/-- `dst := clone(p)`: a read that copies. -/
def opClone (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (dst : Var) : Option St := do
  let Ω ← access N fuel Ω .read x ps
  let v ← follow (Ω x) ps
  pure (upd Ω dst v)

/-- [Assign] `p := w`: the owned access (D67), then the old content's borrow ends, or an old
content still lent is an error. -/
def opAssign (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (w : Val) : Option St := do
  let Ω ← access N fuel Ω .assign x ps
  let old ← follow (Ω x) ps
  let Ω ← match old with
    | .borrow l _ => some (endL N Ω l)
    | _ => if (loans old).any (live N Ω) then none else some Ω
  setPlace Ω x ps w

/-- `p` (0) holds the pair `(σ₀, σ₁)`. `x := &p` (label 0, `x` is 1), `y := &(*x).0` (label 1,
`y` is 2), `z := &(*x).1` (label 2, `z` is 3), `*y := 7`. Variable 4 receives reads. -/
def N₅ : Nat := 5
def q0 : St := fun v => if v = 0 then .pair (.abs 0) (.abs 1) else .bot
def q1 : Option St := opBorrow N₅ 10 q0 0 [] 1 0
def q2 : Option St := q1.bind fun Ω => opBorrow N₅ 10 Ω 1 [.deref, .fst] 2 1
def q3 : Option St := q2.bind fun Ω => opBorrow N₅ 10 Ω 1 [.deref, .snd] 3 2
def q4 : Option St := q3.bind fun Ω => opAssign N₅ 10 Ω 2 [.deref] (.num 7)

/-- Both reborrows are live, and their loans sit in the two fields of `x`'s content. -/
theorem q4_shape :
    q4.map (fun Ω => (Ω 0, Ω 1, Ω 2, Ω 3))
      = some (.loan 0, .borrow 0 (.pair (.loan 1) (.loan 2)), .borrow 1 (.num 7),
          .borrow 2 (.abs 1)) := by decide

/-- A shallow read: `clone((*x).0)` ends `y`, whose loan is on the path, and leaves `z`, whose loan
is in the other field, alive. -/
def q5 : Option St := q4.bind fun Ω => opClone N₅ 10 Ω 1 [.deref, .fst] 4
theorem q5_shape :
    q5.map (fun Ω => (Ω 0, Ω 1, Ω 2, Ω 3, Ω 4))
      = some (.loan 0, .borrow 0 (.pair (.num 7) (.loan 2)), .bot, .borrow 2 (.abs 1), .num 7) := by
  decide

/-- Then reading `p` ends `x` (its loan is at `p`), which brings `x`'s content, with `z`'s loan,
into `p`; the access goes on and ends `z`. Ending one borrow reaches every reborrow under it. -/
def q6 : Option St := q5.bind fun Ω => opClone N₅ 10 Ω 0 [] 4
theorem q6_shape :
    q6.map (fun Ω => (Ω 0, Ω 1, Ω 2, Ω 3, Ω 4))
      = some (.pair (.num 7) (.abs 1), .bot, .bot, .bot, .pair (.num 7) (.abs 1)) := by decide

/-- What the states mean along the run. At `q4`, `p` is lent and `x` reads its two fields' final
contents. At `q5`, `y`'s end fixed field 0 to `7`, what `y` held. At `q6`, `p` reads `(7, σ₁)` under
every future. -/
theorem q4_meaning (ρ : Rho) (f : Future) :
    q4.map (fun Ω => (M ρ Ω f 0, M ρ Ω f 1)) = some (f 0, .pair (f 1) (f 2)) := rfl
theorem q5_meaning (ρ : Rho) (f : Future) :
    q5.map (fun Ω => (M ρ Ω f 1, M ρ Ω f 3)) = some (.pair (.num 7) (f 2), .num (ρ.σ 1)) := rfl
theorem q6_meaning (ρ : Rho) (f : Future) :
    q6.map (fun Ω => M ρ Ω f 0) = some (.pair (.num 7) (.num (ρ.σ 1))) := rfl

/-- Reborrow-and-replace (D67): `x := &p; t := &(*x).0; x := t`. The assignment's access looks only
at what `x` owns, which is nothing behind its borrow, so the reborrow survives. Then `x`'s old
borrow ends, carrying the reborrow's loan back into `p`, where it stays live, now lent to `x`. -/
def r1 : Option St := q1.bind fun Ω => opBorrow N₅ 10 Ω 1 [.deref, .fst] 2 1
def r2 : Option St := r1.bind fun Ω => (opAssign N₅ 10 Ω 1 [] (Ω 2)).map (upd · 2 .bot)
theorem r2_shape :
    r2.map (fun Ω => (Ω 0, Ω 1, Ω 2)) = some (.pair (.loan 1) (.abs 1), .borrow 1 (.abs 0), .bot) := by
  decide

/-- `*x := 9`, then reading `p` ends `x` and `p` reads `(9, σ₁)`. -/
def r3 : Option St := r2.bind fun Ω => opAssign N₅ 10 Ω 1 [.deref] (.num 9)
def r4 : Option St := r3.bind fun Ω => opClone N₅ 10 Ω 0 [] 4
theorem r4_meaning (ρ : Rho) (f : Future) :
    r4.map (fun Ω => (M ρ Ω f 0, M ρ Ω f 1)) = some (.pair (.num 9) (.num (ρ.σ 1)), .bot) := rfl

/-! ## §6. Residual 2: nested holes

[Close] of `σ_g(t)`, `t` holding `borrow_l u`, result into `r` with label `k`, as in `State.lean`.
The step lemma no longer asks that the argument mean a fixed numeral: it holds for any `u`. -/

def closeG (Ω : St) (t r : Var) (l k : Label) (u : Val) : St :=
  upd (upd (substSt Ω l (.gBack u (.loan k))) t .bot) r (.borrow k (.gFwd u))

def semCloseG (ρ : Rho) (Mn : Mean) (t r : Var) (l k : Label) : Mean := fun f =>
  oupd (oupd (Mn (fupd f l (backSV ρ (Mn f t) (f k)))) t .bot) r (fwdSV ρ (Mn f t))

theorem step_closeG (ρ : Rho) (Ω : St) (t r : Var) (l k : Label) (u : Val)
    (ht : Ω t = .borrow l u) (htr : t ≠ r) :
    M ρ (closeG Ω t r l k u) = semCloseG ρ (M ρ Ω) t r l k := by
  funext f z
  have hMt : M ρ Ω f t = ev ρ f u := by simp [M, ht, ev]
  simp only [semCloseG, hMt, oupd]
  by_cases hr : z = r
  · subst hr; simp [M, closeG, upd, ev]
  · by_cases hzt : z = t
    · subst hzt; simp [M, closeG, upd, ev, hr]
    · simp only [hr, hzt, if_false, M, closeG, upd, substSt]
      rw [ev_subst ρ f l _ (Ω z)]
      rfl

/-- `a` (0) holds σ₀. `t := &a` (label 0, `t` is 1); `r := σ_g(t)` (label 1, `r` is 2); the
reborrow `s := &*r` (label 2, `s` is 1); `q := σ_g(s)` (label 3, `q` is 3), whose fill goes into
`r`'s content; `*q := v`. Reading `a` then ends `r`, which brings the second call's hole into
`a`'s fill, and goes on to end `q`. -/
def n0 : St := fun x => if x = 0 then .abs 0 else .bot
def n1 : Option St := opBorrow N₅ 10 n0 0 [] 1 0
def n2 : Option St := n1.map fun Ω => closeG Ω 1 2 0 1 (.abs 0)
def n3 : Option St := n2.bind fun Ω => opBorrow N₅ 10 Ω 2 [.deref] 1 2
def n4 : Option St := n3.map fun Ω => closeG Ω 1 3 2 3 (.gFwd (.abs 0))
def n5 (v : Nat) : Option St := n4.bind fun Ω => opAssign N₅ 10 Ω 3 [.deref] (.num v)
def n6 (v : Nat) : Option St := (n5 v).bind fun Ω => opClone N₅ 10 Ω 0 [] 4

/-- Before the read, `r`'s content is the second call's fill, with its hole `loan_3`. -/
theorem n4_shape :
    n4.map (fun Ω => (Ω 0, Ω 2, Ω 3))
      = some (.gBack (.abs 0) (.loan 1), .borrow 1 (.gBack (.gFwd (.abs 0)) (.loan 3)),
          .borrow 3 (.gFwd (.gFwd (.abs 0)))) := by decide

/-- The read takes the nested fill: `a`'s final content is
`back_{σ₀}(back_{fwd(σ₀)}(v))`, under every future. -/
theorem n6_meaning (ρ : Rho) (f : Future) (v : Nat) :
    (n6 v).map (fun Ω => M ρ Ω f 4)
      = some (.num ((ρ.g (ρ.σ 0)).val.2 ((ρ.g (ρ.g (ρ.σ 0)).val.1).val.2 v))) := rfl

/-- What the general lemma allows, and why WF5 still matters. If a call's argument held a live
loan, the semantic step would read that loan's *final* content at the call: what `r` reads now
would depend on what is written later. The lemma holds; the semantics it describes is acausal.
`t` (3) holds `borrow_5 (loan_0)` while `y` (1) still holds `borrow_0`. -/
def w0 : St := fun x =>
  if x = 0 then .loan 0 else if x = 1 then .borrow 0 (.num 3)
  else if x = 3 then .borrow 5 (.loan 0) else .bot

/-- `σ_g` whose forward value is its argument. -/
def rhoId : Rho := ⟨fun i => i, fun d => ⟨(d, fun v => v), fun _ _ h => h⟩⟩

theorem w0_acausal :
    M rhoId (closeG w0 3 4 5 6 (.loan 0)) (fun _ => .num 0) 4
      ≠ M rhoId (closeG w0 3 4 5 6 (.loan 0)) (fun _ => .num 1) 4 := by decide

/-- [Access] rules this out: borrowing a place whose content holds a live loan ends that loan's
borrow first, so the argument is loan-free. Variable 2 holds `(loan_0, 1)`. -/
def w1 : St := fun x => if x = 2 then .pair (.loan 0) (.num 1) else w0 x
theorem w1_borrow_ends_first :
    (opBorrow N₅ 10 w1 2 [] 3 7).map (fun Ω => (Ω 1, Ω 3))
      = some (.bot, .borrow 7 (.pair (.num 3) (.num 1))) := by decide

/-! ## §7. Residual 3: `⊥` inside a borrow's content

`p` (0) holds `(σ₀, σ₁)`; `x := &p` (label 0, `x` is 1); `d := (*x).0` moves field 0 out through the
borrow (`d` is 4). Every intermediate state means something, `⊥` meaning no information. -/

def opMove (N fuel : Nat) (Ω : St) (x : Var) (ps : List Step) (dst : Var) : Option St := do
  let Ω ← access N fuel Ω .read x ps
  let v ← follow (Ω x) ps
  match v with
  | .bot => none
  | _ =>
    let Ω ← setPlace Ω x ps .bot
    pure (upd Ω dst v)

def m1 : Option St := opBorrow N₅ 10 q0 0 [] 1 0
def m2 : Option St := m1.bind fun Ω => opMove N₅ 10 Ω 1 [.deref, .fst] 4

/-- Moved out: `x` reads `(no information, σ₁)`, `p` reads label 0's final content, `d` reads σ₀. -/
theorem m2_meaning (ρ : Rho) (f : Future) :
    m2.map (fun Ω => (M ρ Ω f 0, M ρ Ω f 1, M ρ Ω f 4))
      = some (f 0, .pair .bot (.num (ρ.σ 1)), .num (ρ.σ 0)) := rfl

/-- Refilled, then `p` read: `p` reads `(5, σ₁)` under every future. -/
def m3 : Option St := m2.bind fun Ω => opAssign N₅ 10 Ω 1 [.deref, .fst] (.num 5)
def m4 : Option St := m3.bind fun Ω => opClone N₅ 10 Ω 0 [] 4
theorem m4_meaning (ρ : Rho) (f : Future) :
    m4.map (fun Ω => M ρ Ω f 0) = some (.pair (.num 5) (.num (ρ.σ 1))) := rfl

/-- Whether a value is whole: no `⊥` inside. -/
def wholeV : Val → Bool
  | .bot => false
  | .pair a b => wholeV a && wholeV b
  | .borrow _ v => wholeV v
  | .gFwd u => wholeV u
  | .gBack u h => wholeV u && wholeV h
  | _ => true

/-- [End] as the checker runs it: a borrow ending while its content is partly moved out is an
error, except inside an observation (`obs`, D68), where it ends and the moved part reads `⊥`. -/
def endChecked (N : Nat) (Ω : St) (l : Label) (obs : Bool) : Option St :=
  match findBorrow N Ω l with
  | some r =>
    match Ω r with
    | .borrow _ c => if obs || wholeV c then some (endL N Ω l) else none
    | _ => some Ω
  | none => some Ω

/-- Not refilled: ending `x` is an error outside an observation; inside one, `p` reads
`(no information, σ₁)`. -/
theorem m2_end_error : m2.map (fun Ω => (endChecked N₅ Ω 0 false).isNone) = some true := by decide
theorem m2_end_observed (ρ : Rho) (f : Future) :
    m2.bind (fun Ω => (endChecked N₅ Ω 0 true).map fun Ω => M ρ Ω f 0)
      = some (.pair .bot (.num (ρ.σ 1))) := rfl

/-- `Eq` over meanings: stuck (`none`) when either side has no information somewhere. It is
monotone: on more information it never gives a different answer, which is (Mono) for `Eq`, the
checker's `Eq` staying stuck over `⊥`. -/
def hasBot : SV → Bool
  | .bot => true
  | .pair a b => hasBot a || hasBot b
  | .num _ => false

def eqSV (a b : SV) : Option Bool := if hasBot a || hasBot b then none else some (decide (a = b))

theorem le_eq_of_noBot : ∀ {a a' : SV}, SV.le a a' → hasBot a = false → a = a'
  | _, _, .bot _, h => by simp [hasBot] at h
  | _, _, .num _, _ => rfl
  | _, _, .pair h₁ h₂, h => by
    simp only [hasBot, Bool.or_eq_false_iff] at h
    rw [le_eq_of_noBot h₁ h.1, le_eq_of_noBot h₂ h.2]

theorem eqSV_mono {a b a' b' : SV} (ha : SV.le a a') (hb : SV.le b b') {t : Bool}
    (h : eqSV a b = some t) : eqSV a' b' = some t := by
  unfold eqSV at h
  split at h
  · cases h
  · next hn =>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    rw [← le_eq_of_noBot ha hn.1, ← le_eq_of_noBot hb hn.2]
    unfold eqSV
    simp [hn.1, hn.2, h]

/-! ## §8. Residual 4: [Drop]

Dropping a binding: a borrow it holds ends; otherwise each live loan in its value ends that
loan's borrower if the borrower is held in a binding, and is an error if the borrower is a value
in flight (`temp`), D65 amended. Then the binding is gone (`⊥`). -/

def dropLoop (N : Nat) (temp : Var → Bool) : Nat → St → Var → Option St
  | 0, _, _ => none
  | fuel + 1, Ω, x =>
    match (loans (Ω x)).find? (live N Ω) with
    | some l =>
      match findBorrow N Ω l with
      | some h => if temp h then none else dropLoop N temp fuel (endL N Ω l) x
      | none => none
    | none => some Ω

def drop (N : Nat) (temp : Var → Bool) (fuel : Nat) (Ω : St) (x : Var) : Option St :=
  match Ω x with
  | .borrow l _ => some (upd (endL N Ω l) x .bot)
  | _ => (dropLoop N temp fuel Ω x).map (upd · x .bot)

/-- Forgetting a variable loses only information. -/
theorem upd_bot_below (ρ : Rho) (Ω : St) (x : Var) : Below (M ρ (upd Ω x .bot)) (M ρ Ω) := by
  intro f
  refine ⟨f, fun z => ?_⟩
  by_cases hz : z = x
  · subst hz; simp only [M, upd, if_true, ev]; exact .bot _
  · simp only [M, upd, hz, if_false]; exact SV.le_refl _

theorem dropLoop_below (ρ : Rho) (N : Nat) (temp : Var → Bool) :
    ∀ fuel Ω x Ω', dropLoop N temp fuel Ω x = some Ω' → Below (M ρ Ω') (M ρ Ω) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [dropLoop] at h
  | succ fuel ih =>
    intro Ω x Ω' h
    simp only [dropLoop] at h
    split at h
    · split at h
      · split at h
        · cases h
        · exact (ih _ _ _ h).trans (endL_below ρ N Ω _)
      · cases h
    · cases h; exact Below.refl _

/-- [Drop] keeps the meaning up to information: a sequence of [End]s, then forgetting the
binding. -/
theorem drop_below (ρ : Rho) (N : Nat) (temp : Var → Bool) (fuel : Nat) (Ω : St) (x : Var)
    (Ω' : St) (h : drop N temp fuel Ω x = some Ω') : Below (M ρ Ω') (M ρ Ω) := by
  unfold drop at h
  split at h
  · cases h; exact (upd_bot_below ρ _ x).trans (endL_below ρ N Ω _)
  · cases hd : dropLoop N temp fuel Ω x with
    | none => simp [hd] at h
    | some Ω₁ =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      subst h
      exact (upd_bot_below ρ Ω₁ x).trans (dropLoop_below ρ N temp fuel Ω x Ω₁ hd)

/-- `p` (0) holds σ₀ and `x := &p` (label 0, `x` is 1). Dropping `p` ends `x` when `x` is a
binding; it is an error when `x` is a value in flight. -/
theorem drop_binding :
    m1.bind (fun Ω => (drop N₅ (fun _ => false) 10 Ω 0).map fun Ω => (Ω 0, Ω 1)) = some (.bot, .bot) := by
  decide
theorem drop_in_flight : m1.map (fun Ω => (drop N₅ (· = 1) 10 Ω 0).isNone) = some true := by decide

/-! ## §9. Matches (D29)

A match inspects only the head. A loan inside a neutral head ends, since where it sits inside the
neutral is unknown; a constructor head leaves its fields' loans alone. -/

/-- After a match's access, a neutral head holds no live loan, so (with no dangling loans) the
head means the same under every future. -/
theorem match_post_live (N : Nat) (Ω : St) (x : Var) (ps : List Step) (v : Val)
    (h : accessStep N Ω .matchHead x ps = none) (hv : follow (Ω x) ps = some v)
    (hn : isNeutral v = true) : ∀ l, l ∈ loans v → live N Ω l = false := by
  intro l hl
  simp only [accessStep] at h
  split at h
  · simp at h
  · simp only [hv, hn, if_true] at h
    have := List.find?_eq_none.mp h l hl
    simpa using this

/-- Matching on `a`'s fill `gBack σ₀ (loan_1)` (state `n2`) ends `r`. -/
theorem match_fill_ends :
    n2.bind (fun Ω => (access N₅ 10 Ω .matchHead 0 []).map fun Ω => (Ω 0, Ω 2))
      = some (.gBack (.abs 0) (.gFwd (.abs 0)), .bot) := by decide

/-- Matching on `*x` (state `q4`, content `(loan_1, loan_2)`) ends neither reborrow. -/
theorem match_ctor_keeps :
    q4.bind (fun Ω => (access N₅ 10 Ω .matchHead 1 [.deref]).map fun Ω => (Ω 2, Ω 3))
      = some (.borrow 1 (.num 7), .borrow 2 (.abs 1)) := by decide

end Ochr.Model.State2

#print axioms Ochr.Model.State2.ev_subst
#print axioms Ochr.Model.State2.ev_congr
#print axioms Ochr.Model.State2.step_end
#print axioms Ochr.Model.State2.endL_below
#print axioms Ochr.Model.State2.access_below
#print axioms Ochr.Model.State2.access_post
#print axioms Ochr.Model.State2.read_value_indep
#print axioms Ochr.Model.State2.q6_shape
#print axioms Ochr.Model.State2.q6_meaning
#print axioms Ochr.Model.State2.r2_shape
#print axioms Ochr.Model.State2.step_closeG
#print axioms Ochr.Model.State2.n6_meaning
#print axioms Ochr.Model.State2.w0_acausal
#print axioms Ochr.Model.State2.w1_borrow_ends_first
#print axioms Ochr.Model.State2.m2_meaning
#print axioms Ochr.Model.State2.m2_end_error
#print axioms Ochr.Model.State2.eqSV_mono
#print axioms Ochr.Model.State2.drop_below
#print axioms Ochr.Model.State2.drop_in_flight
#print axioms Ochr.Model.State2.match_post_live
#print axioms Ochr.Model.State2.match_fill_ends
