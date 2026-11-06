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
