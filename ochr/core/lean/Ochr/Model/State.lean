/-
  Ochr.Model.State: a Lean check of the hardest piece of test 2 of `ochr/docs/23`. Does a symbolic
  state holding live borrows and holes have a meaning that the borrow steps keep? Standalone: it
  imports Lean core only, is not imported by `Ochr.lean`, and is checked with
  `lake env lean Ochr/Model/State.lean` from `ochr/core/lean`.

  A toy symbolic machine.
  * Variables hold values: numerals, abstract numerals σᵢ, `⊥`, `borrow_ℓ v`, `loan_ℓ`, and sealed
    programs for calls of two opaque functions. `σ_g : Π(x : &Nat). &Nat`, and
    `σ_p : Π(x y : &Nat). &Nat`, whose shape is `Pick`'s: one returned borrow, two lent places.
  * Under ρ, each opaque function is an element of its restricted function type
    (`Ochr/Model/Slice.lean`): its backward function is injective by construction.

  The meaning of a state (§2) is a function of a *future*: the final content of every borrow
  label. Under a future, a lent variable means its final content, and a variable holding a
  borrow means the borrow's *current* content (what the caller can still read). `⊥` means no
  information (`none`).

  Every step (§3) keeps the meaning: the meaning after the step is a semantic step, defined on
  meanings alone, applied to the meaning before. [End] also loses only information (`Below`).
  §4 runs `σ_g`'s observation, `Pick`'s early end and an `Id`-style equation over a live hole.
-/
set_option autoImplicit false

namespace Ochr.Model.State

/-- An injective backward function into `Fin`, with the forward value: what an opaque function
returning `&Nat` gives back at one argument, in the restricted encoding (R is the carrier). -/
abbrev BackN (Fin : Type) : Type := {p : Nat × (Nat → Fin) // ∀ v w, p.2 v = p.2 w → v = w}

/-- An assignment ρ: a value for each abstract numeral, and elements of the restricted types
`Π(x : &Nat). &Nat` (for `σ_g`) and `Π(x y : &Nat). &Nat` (for `σ_p`; the backward function
gives both lent places' final contents). -/
structure Rho where
  σ : Nat → Nat
  g : Nat → BackN Nat
  p : Nat → Nat → BackN (Nat × Nat)

abbrev Var := Nat
abbrev Label := Nat

/-- Values. The sealed programs are those [Close] makes for the two opaque functions, with `u` the
borrowed content at the call and `h` the hole: `gFwd u` is ⌈let c = u; let r = σ_g(&c); *r⌉ and
`gBack u h` is ⌈let c = u; let r = σ_g(&c); *r := h; c⌉, and likewise for `σ_p`, whose
`pBack₁` and `pBack₂` are the fills of its first and second lent places. -/
inductive Val where
  | num (n : Nat)
  | abs (i : Nat)
  | bot
  | borrow (l : Label) (v : Val)
  | loan (l : Label)
  | gFwd (u : Val)
  | gBack (u h : Val)
  | pFwd (u₁ u₂ : Val)
  | pBack₁ (u₁ u₂ h : Val)
  | pBack₂ (u₁ u₂ h : Val)
  deriving Inhabited

/-- A future: the final content of each borrow label. -/
abbrev Future : Type := Label → Nat

/-- The future that differs from `f` only in that label `l`'s final content is `n`. -/
def fupd (f : Future) (l : Label) (n : Nat) : Future := fun l' => if l' = l then n else f l'

/-- The meaning of a value under ρ and a future. A loan means its borrow's final content; a borrow
means its current content; a sealed program means its call's meaning under ρ; `⊥` means
nothing. -/
def ev (ρ : Rho) (f : Future) : Val → Option Nat
  | .num n => some n
  | .abs i => some (ρ.σ i)
  | .bot => none
  | .borrow _ v => ev ρ f v
  | .loan l => some (f l)
  | .gFwd u =>
    match ev ρ f u with
    | some d => some (ρ.g d).val.1
    | none => none
  | .gBack u h =>
    match ev ρ f u, ev ρ f h with
    | some d, some v => some ((ρ.g d).val.2 v)
    | _, _ => none
  | .pFwd u₁ u₂ =>
    match ev ρ f u₁, ev ρ f u₂ with
    | some d₁, some d₂ => some (ρ.p d₁ d₂).val.1
    | _, _ => none
  | .pBack₁ u₁ u₂ h =>
    match ev ρ f u₁, ev ρ f u₂, ev ρ f h with
    | some d₁, some d₂, some v => some ((ρ.p d₁ d₂).val.2 v).1
    | _, _, _ => none
  | .pBack₂ u₁ u₂ h =>
    match ev ρ f u₁, ev ρ f u₂, ev ρ f h with
    | some d₁, some d₂, some v => some ((ρ.p d₁ d₂).val.2 v).2
    | _, _, _ => none

/-- A state: what each variable holds. -/
abbrev St : Type := Var → Val

/-- A meaning: for each future, what each variable holds. -/
abbrev Mean : Type := Future → Var → Option Nat

/-- The meaning of a state under ρ. -/
def M (ρ : Rho) (Ω : St) : Mean := fun f x => ev ρ f (Ω x)

/-! ## §1. Substitution, and what a meaning depends on -/

/-- Replace `loan_l` by `w` everywhere in a value: how [End] and [Close] fill a loan. -/
def substV (l : Label) (w : Val) : Val → Val
  | .loan l' => if l' = l then w else .loan l'
  | .borrow l' v => .borrow l' (substV l w v)
  | .gFwd u => .gFwd (substV l w u)
  | .gBack u h => .gBack (substV l w u) (substV l w h)
  | .pFwd u₁ u₂ => .pFwd (substV l w u₁) (substV l w u₂)
  | .pBack₁ u₁ u₂ h => .pBack₁ (substV l w u₁) (substV l w u₂) (substV l w h)
  | .pBack₂ u₁ u₂ h => .pBack₂ (substV l w u₁) (substV l w u₂) (substV l w h)
  | v => v

/-- The substitution lemma: filling `loan_l` with a value meaning `n` is the same as fixing `l`'s
final content to `n`. No side condition: `w` is read under the old future. -/
theorem ev_subst (ρ : Rho) (f : Future) (l : Label) (w : Val) (n : Nat)
    (hw : ev ρ f w = some n) : ∀ t, ev ρ f (substV l w t) = ev ρ (fupd f l n) t := by
  intro t
  induction t with
  | num _ => rfl
  | abs _ => rfl
  | bot => rfl
  | borrow _ v ih => simp only [substV, ev, ih]
  | loan l' =>
    by_cases h : l' = l
    · subst h; simp [substV, ev, fupd, hw]
    · simp [substV, ev, fupd, h]
  | gFwd u ih => simp only [substV, ev, ih]
  | gBack u h ihu ihh => simp only [substV, ev, ihu, ihh]
  | pFwd u₁ u₂ ih₁ ih₂ => simp only [substV, ev, ih₁, ih₂]
  | pBack₁ u₁ u₂ h ih₁ ih₂ ihh => simp only [substV, ev, ih₁, ih₂, ihh]
  | pBack₂ u₁ u₂ h ih₁ ih₂ ihh => simp only [substV, ev, ih₁, ih₂, ihh]

/-- The loan labels occurring in a value: its live holes and lent places. -/
def loans : Val → List Label
  | .loan l => [l]
  | .borrow _ v => loans v
  | .gFwd u => loans u
  | .gBack u h => loans u ++ loans h
  | .pFwd u₁ u₂ => loans u₁ ++ loans u₂
  | .pBack₁ u₁ u₂ h => loans u₁ ++ loans u₂ ++ loans h
  | .pBack₂ u₁ u₂ h => loans u₁ ++ loans u₂ ++ loans h
  | _ => []

/-- A value's meaning depends on the future only at the loans occurring in it. -/
theorem ev_congr (ρ : Rho) (f f' : Future) :
    ∀ t, (∀ l, l ∈ loans t → f l = f' l) → ev ρ f t = ev ρ f' t := by
  intro t
  induction t with
  | num _ => intro _; rfl
  | abs _ => intro _; rfl
  | bot => intro _; rfl
  | borrow _ v ih => intro h; simp only [ev]; exact ih h
  | loan l => intro h; simp [ev, h l (by simp [loans])]
  | gFwd u ih => intro h; simp only [ev]; rw [ih h]
  | gBack u k ihu ihk =>
    intro h
    simp only [ev]
    rw [ihu fun l hl => h l (by simp [loans, hl]), ihk fun l hl => h l (by simp [loans, hl])]
  | pFwd u₁ u₂ ih₁ ih₂ =>
    intro h
    simp only [ev]
    rw [ih₁ fun l hl => h l (by simp [loans, hl]), ih₂ fun l hl => h l (by simp [loans, hl])]
  | pBack₁ u₁ u₂ k ih₁ ih₂ ihk =>
    intro h
    simp only [ev]
    rw [ih₁ fun l hl => h l (by simp [loans, hl]), ih₂ fun l hl => h l (by simp [loans, hl]),
      ihk fun l hl => h l (by simp [loans, hl])]
  | pBack₂ u₁ u₂ k ih₁ ih₂ ihk =>
    intro h
    simp only [ev]
    rw [ih₁ fun l hl => h l (by simp [loans, hl]), ih₂ fun l hl => h l (by simp [loans, hl]),
      ihk fun l hl => h l (by simp [loans, hl])]

/-- A loan-free value means the same under every future. -/
theorem ev_loanFree (ρ : Rho) (f f' : Future) (t : Val) (ht : loans t = []) :
    ev ρ f t = ev ρ f' t :=
  ev_congr ρ f f' t fun l hl => by simp [ht] at hl

/-! ## §2. Steps, symbolic and semantic

Each symbolic step acts on a state; its semantic counterpart acts on a meaning alone, using only
labels and ρ (never the state's representation). The step lemmas say that the meaning after the
symbolic step is the semantic step applied to the meaning before, for every ρ and every future. -/

def upd (Ω : St) (x : Var) (v : Val) : St := fun y => if y = x then v else Ω y
def substSt (Ω : St) (l : Label) (w : Val) : St := fun y => substV l w (Ω y)
def oupd (m : Var → Option Nat) (x : Var) (o : Option Nat) : Var → Option Nat :=
  fun y => if y = x then o else m y

/-- Filling a loan in the whole state is fixing that label's future. -/
theorem M_subst (ρ : Rho) (Ω : St) (f : Future) (l : Label) (w : Val) (n : Nat)
    (hw : ev ρ f w = some n) : M ρ (substSt Ω l w) f = M ρ Ω (fupd f l n) :=
  funext fun z => ev_subst ρ f l w n hw (Ω z)

/-- [Borrow] `y := &x` with label `l`: `x` is lent, `y` holds the borrow of `x`'s content. -/
def stBorrow (Ω : St) (x y : Var) (l : Label) : St := upd (upd Ω x (.loan l)) y (.borrow l (Ω x))
/-- Semantically: `y` now reads what `x` held, and `x` will hold `l`'s final content. -/
def semBorrow (Mn : Mean) (x y : Var) (l : Label) : Mean :=
  fun f => oupd (oupd (Mn f) x (some (f l))) y (Mn f x)

theorem step_borrow (ρ : Rho) (Ω : St) (x y : Var) (l : Label) (hxy : x ≠ y) :
    M ρ (stBorrow Ω x y l) = semBorrow (M ρ Ω) x y l := by
  funext f z
  by_cases hy : z = y
  · subst hy; simp [M, stBorrow, semBorrow, upd, oupd, ev]
  · by_cases hx : z = x
    · subst hx; simp [M, stBorrow, semBorrow, upd, oupd, ev, hy]
    · simp [M, stBorrow, semBorrow, upd, oupd, hx, hy]

/-- Writing `w` through the borrow `borrow_l _` that `y` holds. -/
def stWrite (Ω : St) (y : Var) (l : Label) (w : Val) : St := upd Ω y (.borrow l w)
/-- Semantically: only what `y` reads changes; no lender's final content does. -/
def semWrite (Mn : Mean) (y : Var) (o : Future → Option Nat) : Mean := fun f => oupd (Mn f) y (o f)

theorem step_write (ρ : Rho) (Ω : St) (y : Var) (l : Label) (w : Val) :
    M ρ (stWrite Ω y l w) = semWrite (M ρ Ω) y (fun f => ev ρ f w) := by
  funext f z
  by_cases hy : z = y
  · subst hy; simp [M, stWrite, semWrite, upd, oupd, ev]
  · simp [M, stWrite, semWrite, upd, oupd, hy]

/-- [Close] of `σ_g(t)`, `t` holding `borrow_l u`, result into `r` with the new label `k`: the loan
`l` is filled with `gBack u (loan k)`, `t` is moved into the call, `r` gets `borrow_k (gFwd u)`. -/
def stCloseG (Ω : St) (t r : Var) (l k : Label) (u : Val) : St :=
  upd (upd (substSt Ω l (.gBack u (.loan k))) t .bot) r (.borrow k (.gFwd u))
/-- Semantically: call `ρ(σ_g)` at what `t` reads. `r` reads the forward value, and `l`'s final
content becomes the backward function applied to `k`'s final content. -/
def semCloseG (ρ : Rho) (Mn : Mean) (t r : Var) (l k : Label) : Mean := fun f =>
  match Mn f t with
  | some d => oupd (oupd (Mn (fupd f l ((ρ.g d).val.2 (f k)))) t none) r (some (ρ.g d).val.1)
  | none => fun _ => none

theorem step_closeG (ρ : Rho) (Ω : St) (t r : Var) (l k : Label) (u : Val) (d : Nat)
    (ht : Ω t = .borrow l u) (hu : ∀ f, ev ρ f u = some d) (htr : t ≠ r) :
    M ρ (stCloseG Ω t r l k u) = semCloseG ρ (M ρ Ω) t r l k := by
  funext f z
  have hMt : M ρ Ω f t = some d := by simp [M, ht, ev, hu]
  have hW : ev ρ f (.gBack u (.loan k)) = some ((ρ.g d).val.2 (f k)) := by simp [ev, hu]
  simp only [semCloseG, hMt]
  by_cases hr : z = r
  · subst hr; simp [M, stCloseG, upd, oupd, ev, hu]
  · by_cases htz : z = t
    · subst htz; simp [M, stCloseG, upd, oupd, ev, hr]
    · simp only [oupd, hr, htz, if_false]
      show ev ρ f (upd (upd (substSt Ω l _) t .bot) r _ z) = _
      simp only [upd, hr, htz, if_false]
      exact ev_subst ρ f l _ _ hW (Ω z)

/-- [End] of the borrow `borrow_k v` that `r` holds: `loan_k` is filled with `v` everywhere. -/
def stEnd (Ω : St) (r : Var) (k : Label) (v : Val) : St := upd (substSt Ω k v) r .bot
/-- Semantically: `k`'s final content is what `r` reads now, and `r` reads nothing. -/
def semEnd (Mn : Mean) (r : Var) (k : Label) : Mean := fun f =>
  match Mn f r with
  | some c => oupd (Mn (fupd f k c)) r none
  | none => fun _ => none

/-- The borrow must be whole when it ends (its content means something under every future); its
content may still hold other loans. -/
theorem step_end (ρ : Rho) (Ω : St) (r : Var) (k : Label) (v : Val)
    (hr : Ω r = .borrow k v) (hv : ∀ f, ∃ c, ev ρ f v = some c) :
    M ρ (stEnd Ω r k v) = semEnd (M ρ Ω) r k := by
  funext f z
  obtain ⟨c, hc⟩ := hv f
  have hMr : M ρ Ω f r = some c := by simp [M, hr, ev, hc]
  simp only [semEnd, hMr]
  by_cases hz : z = r
  · subst hz; simp [M, stEnd, upd, oupd, ev]
  · simp only [oupd, hz, if_false]
    show ev ρ f (upd (substSt Ω k v) r .bot z) = _
    simp only [upd, hz, if_false]
    exact ev_subst ρ f k v c hc (Ω z)

/-- [Close] of `σ_p(t₁, t₂)` (`Pick`'s shape), result into `r` with the new label `k`: the fills of
both lent places share the one hole `loan_k`. -/
def stCloseP (Ω : St) (t₁ t₂ r : Var) (l₁ l₂ k : Label) (u₁ u₂ : Val) : St :=
  upd (upd (upd (substSt (substSt Ω l₁ (.pBack₁ u₁ u₂ (.loan k))) l₂ (.pBack₂ u₁ u₂ (.loan k)))
    t₁ .bot) t₂ .bot) r (.borrow k (.pFwd u₁ u₂))
/-- Semantically: call `ρ(σ_p)`; both lent places' final contents are the backward function applied
to `k`'s final content. -/
def semCloseP (ρ : Rho) (Mn : Mean) (t₁ t₂ r : Var) (l₁ l₂ k : Label) : Mean := fun f =>
  match Mn f t₁, Mn f t₂ with
  | some d₁, some d₂ =>
    let b := (ρ.p d₁ d₂).val.2 (f k)
    oupd (oupd (oupd (Mn (fupd (fupd f l₂ b.2) l₁ b.1)) t₁ none) t₂ none) r
      (some (ρ.p d₁ d₂).val.1)
  | _, _ => fun _ => none

theorem step_closeP (ρ : Rho) (Ω : St) (t₁ t₂ r : Var) (l₁ l₂ k : Label) (u₁ u₂ : Val)
    (d₁ d₂ : Nat) (ht₁ : Ω t₁ = .borrow l₁ u₁) (ht₂ : Ω t₂ = .borrow l₂ u₂)
    (hu₁ : ∀ f, ev ρ f u₁ = some d₁) (hu₂ : ∀ f, ev ρ f u₂ = some d₂)
    (hk : k ≠ l₂) (h₁₂ : t₁ ≠ t₂) (h₁r : t₁ ≠ r) (h₂r : t₂ ≠ r) :
    M ρ (stCloseP Ω t₁ t₂ r l₁ l₂ k u₁ u₂) = semCloseP ρ (M ρ Ω) t₁ t₂ r l₁ l₂ k := by
  funext f z
  have hM₁ : M ρ Ω f t₁ = some d₁ := by simp [M, ht₁, ev, hu₁]
  have hM₂ : M ρ Ω f t₂ = some d₂ := by simp [M, ht₂, ev, hu₂]
  simp only [semCloseP, hM₁, hM₂]
  by_cases hr : z = r
  · subst hr; simp [M, stCloseP, upd, oupd, ev, hu₁, hu₂]
  · by_cases hz₂ : z = t₂
    · subst hz₂; simp [M, stCloseP, upd, oupd, ev, hr]
    · by_cases hz₁ : z = t₁
      · subst hz₁; simp [M, stCloseP, upd, oupd, ev, hr, hz₂]
      · simp only [oupd, hr, hz₁, hz₂, if_false]
        show ev ρ f (upd (upd (upd (substSt (substSt Ω l₁ _) l₂ _) t₁ .bot) t₂ .bot) r _ z) = _
        simp only [upd, hr, hz₁, hz₂, if_false, substSt]
        have hW₂ : ev ρ f (.pBack₂ u₁ u₂ (.loan k)) = some ((ρ.p d₁ d₂).val.2 (f k)).2 := by
          simp [ev, hu₁, hu₂]
        rw [ev_subst ρ f l₂ _ _ hW₂]
        have hW₁ : ev ρ (fupd f l₂ ((ρ.p d₁ d₂).val.2 (f k)).2) (.pBack₁ u₁ u₂ (.loan k))
            = some ((ρ.p d₁ d₂).val.2 (f k)).1 := by
          simp [ev, hu₁, hu₂, fupd, hk]
        exact ev_subst ρ _ l₁ _ _ hW₁ (Ω z)

/-! ## §3. [End] loses only information

`Below m' m`: every reading `m'` gives under some future, `m` gives under some future. Ending a
borrow early, as `Pick`'s read does, fixes that borrow's future to its current content and stops
reading the borrow. That narrows the futures and forgets one variable, and nothing else. -/

def Below (m' m : Mean) : Prop := ∀ f', ∃ f, ∀ z n, m' f' z = some n → m f z = some n

theorem semEnd_below (Mn : Mean) (r : Var) (k : Label) : Below (semEnd Mn r k) Mn := by
  intro f'
  cases hc : Mn f' r with
  | none => exact ⟨f', fun z n h => by simp [semEnd, hc] at h⟩
  | some c =>
    refine ⟨fupd f' k c, fun z n h => ?_⟩
    simp only [semEnd, hc, oupd] at h
    by_cases hz : z = r
    · simp [hz] at h
    · simpa [hz] using h

/-! ## §4. Runs

### `σ_g`: the caller writes `v` through the returned borrow, then ends it

`a` is variable 0 and holds σ₀. `t := &a` (label 0, `t` is variable 1). `r := σ_g(t)` closes off
(label 1, `r` is variable 2). Then `*r := v`, then `r` ends. -/

def obs0 : St := fun z => if z = 0 then .abs 0 else .bot
def obs1 : St := stBorrow obs0 0 1 0
def obs2 : St := stCloseG obs1 1 2 0 1 (.abs 0)
def obs3 (v : Nat) : St := stWrite obs2 2 1 (.num v)
def obs4 (v : Nat) : St := stEnd (obs3 v) 2 1 (.num v)

/-- The run's meaning is the semantic steps applied to the start's meaning: computed from
meanings and ρ alone, never from the symbolic representation. -/
theorem obs_steps (ρ : Rho) (v : Nat) :
    M ρ (obs4 v) = semEnd (semWrite (semCloseG ρ (semBorrow (M ρ obs0) 0 1 0) 1 2 0 1) 2
      (fun _ => some v)) 2 1 := by
  rw [obs4, step_end ρ (obs3 v) 2 1 (.num v) rfl (fun _ => ⟨v, rfl⟩), obs3,
    step_write ρ obs2 2 1 (.num v), obs2,
    step_closeG ρ obs1 1 2 0 1 (.abs 0) (ρ.σ 0) rfl (fun _ => rfl) (by decide), obs1,
    step_borrow ρ obs0 0 1 0 (by decide)]
  rfl

/-- The observation: `a`'s final content is `back_{ρ(σ_g)}(ρ(σ₀))(v)`, under every future. -/
theorem obs_final (ρ : Rho) (f : Future) (v : Nat) :
    M ρ (obs4 v) f 0 = some ((ρ.g (ρ.σ 0)).val.2 v) := rfl

/-- The same from the semantic steps alone. -/
example (ρ : Rho) (f : Future) (v : Nat) :
    semEnd (semWrite (semCloseG ρ (semBorrow (M ρ obs0) 0 1 0) 1 2 0 1) 2 (fun _ => some v)) 2 1
      f 0 = some ((ρ.g (ρ.σ 0)).val.2 v) := rfl

/-- docs/18's `PF`: writing `0` and writing `1` through the returned borrow leave different final
contents in `a`, under every ρ. So `Id(Unit, *r := 0, *r := 1)` is false in the model, which is
why the meaning of `Π(x : &Nat). &Nat` must hold only injective backward functions. -/
theorem pf_distinct (ρ : Rho) (f : Future) : M ρ (obs4 0) f 0 ≠ M ρ (obs4 1) f 0 := by
  rw [obs_final, obs_final]
  intro h
  exact Nat.zero_ne_one ((ρ.g (ρ.σ 0)).property 0 1 (Option.some.inj h))

/-! ### `Pick`'s shape: two fills share one hole, and a read ends the returned borrow early

`a` (0) holds σ₀ and `b` (1) holds σ₁. `t₁ := &a` (label 0, variable 2) and `t₂ := &b` (label 1,
variable 3). `r := σ_p(t₁, t₂)` closes off (label 2, variable 4). Both fills hold the hole
`loan_2`, so reading `b` ends `r` early. -/

def pk0 : St := fun z => if z = 0 then .abs 0 else if z = 1 then .abs 1 else .bot
def pk1 : St := stBorrow (stBorrow pk0 0 2 0) 1 3 1
def pk2 : St := stCloseP pk1 2 3 4 0 1 2 (.abs 0) (.abs 1)
/-- Reading `b` meets `loan_2` in its fill, so [Access] ends `r`, whose content is `pFwd σ₀ σ₁`. -/
def pk3 : St := stEnd pk2 4 2 (.pFwd (.abs 0) (.abs 1))

/-- Before the read, both lent places' final contents are the backward function at the hole. -/
theorem pk2_a (ρ : Rho) (f : Future) :
    M ρ pk2 f 0 = some ((ρ.p (ρ.σ 0) (ρ.σ 1)).val.2 (f 2)).1 := rfl
theorem pk2_b (ρ : Rho) (f : Future) :
    M ρ pk2 f 1 = some ((ρ.p (ρ.σ 0) (ρ.σ 1)).val.2 (f 2)).2 := rfl

/-- An `Id`-style equation of the two final contents depends on the future only through the
value finally written through `r`: it is a fixed predicate of `f 2`. -/
theorem pk2_id (ρ : Rho) (f : Future) :
    (M ρ pk2 f 0 = M ρ pk2 f 1)
      ↔ ((ρ.p (ρ.σ 0) (ρ.σ 1)).val.2 (f 2)).1 = ((ρ.p (ρ.σ 0) (ρ.σ 1)).val.2 (f 2)).2 := by
  rw [pk2_a, pk2_b]
  exact ⟨Option.some.inj, congrArg some⟩

theorem pk2_id_hole (ρ : Rho) (f f' : Future) (h : f 2 = f' 2) :
    (M ρ pk2 f 0 = M ρ pk2 f 1) ↔ (M ρ pk2 f' 0 = M ρ pk2 f' 1) := by
  rw [pk2_id, pk2_id, h]

/-- The close-off step keeps the meaning on this run. -/
theorem pk2_step (ρ : Rho) : M ρ pk2 = semCloseP ρ (M ρ pk1) 2 3 4 0 1 2 :=
  step_closeP ρ pk1 2 3 4 0 1 2 (.abs 0) (.abs 1) (ρ.σ 0) (ρ.σ 1) rfl rfl (fun _ => rfl)
    (fun _ => rfl) (by decide) (by decide) (by decide) (by decide)

/-- The early end is an [End] step, so it keeps the meaning… -/
theorem pk3_step (ρ : Rho) : M ρ pk3 = semEnd (M ρ pk2) 4 2 :=
  step_end ρ pk2 4 2 (.pFwd (.abs 0) (.abs 1)) rfl (fun _ => ⟨_, rfl⟩)

/-- …and loses only information: every reading after it is a reading before it, in some future. -/
theorem pk3_below (ρ : Rho) : Below (M ρ pk3) (M ρ pk2) := by
  rw [pk3_step]; exact semEnd_below _ _ _

/-- After it, `b` reads the backward function at what `r` held (its forward value), under every
future, and `r` reads nothing. -/
theorem pk3_b (ρ : Rho) (f : Future) :
    M ρ pk3 f 1
      = some ((ρ.p (ρ.σ 0) (ρ.σ 1)).val.2 (ρ.p (ρ.σ 0) (ρ.σ 1)).val.1).2 := rfl
theorem pk3_r (ρ : Rho) (f : Future) : M ρ pk3 f 4 = none := rfl

/-- What the early end costs, at an instance where `Pick` returned `a`'s borrow: `σ_p`'s backward
function leaves `b` alone, `v ↦ (v, d₂)`. There `b`'s final content never depended on the hole,
so the early end lost nothing about `b`. It lost only `r`, which the checker then refuses to use.
There is no second run to agree with, so the `n = 0` instance is just one ρ. -/
def rhoX (σ : Nat → Nat) : Rho where
  σ := σ
  g := fun _ => ⟨(0, fun v => v), fun _ _ h => h⟩
  p := fun d₁ d₂ => ⟨(d₁, fun v => (v, d₂)), fun _ _ h => congrArg Prod.fst h⟩

theorem pk2_b_at_rhoX (σ : Nat → Nat) (f : Future) : M (rhoX σ) pk2 f 1 = some (σ 1) := rfl
theorem pk3_b_at_rhoX (σ : Nat → Nat) (f : Future) : M (rhoX σ) pk3 f 1 = some (σ 1) := rfl

end Ochr.Model.State

#print axioms Ochr.Model.State.ev_subst
#print axioms Ochr.Model.State.ev_congr
#print axioms Ochr.Model.State.M_subst
#print axioms Ochr.Model.State.step_borrow
#print axioms Ochr.Model.State.step_write
#print axioms Ochr.Model.State.step_closeG
#print axioms Ochr.Model.State.step_closeP
#print axioms Ochr.Model.State.step_end
#print axioms Ochr.Model.State.semEnd_below
#print axioms Ochr.Model.State.obs_steps
#print axioms Ochr.Model.State.obs_final
#print axioms Ochr.Model.State.pf_distinct
#print axioms Ochr.Model.State.pk2_id
#print axioms Ochr.Model.State.pk2_id_hole
#print axioms Ochr.Model.State.pk2_step
#print axioms Ochr.Model.State.pk3_below
#print axioms Ochr.Model.State.pk3_b
#print axioms Ochr.Model.State.pk2_b_at_rhoX
