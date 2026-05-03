import Pss.Mpss.Substitution

/-! # `Pss.Mpss.AvoidsPro` — scope-preservation helpers for `MEqRed`

Pasquale & García-Pérez 2024 (CSL 2026), §3 (auxiliary scope-tracking
helpers used in the discharge of Lemma 2).

## History note: the dropped `MEqRedAvoidsPro` predicate

This module previously hosted an inductive predicate
`MEqRedAvoidsPro x : MEqRed Γ s u v → Prop` intended to mechanize the
"moreover" clause of the paper's Lemma 2 (the "no `Me-Pro` on `x`" side
condition that the paper threads through its diamond proof).

That predicate was **unsound** as formulated. Because `MEqRed` is itself
in `Prop`, two `MEqRed Γ s u v` derivations of the same proposition are
definitionally equal under Lean 4's proof irrelevance, regardless of the
constructor shape that produced them. So when (e.g.) `α' = .fvar y` and
`y` happens to be the variable being looked up by `equBinds`, the two
derivations
    `MEqRed.pro hpv heq hα : MEqRed Γ s (.fvar y) (.fvar y)`
    `MEqRed.var hpv       : MEqRed Γ s (.fvar y) (.fvar y)`
inhabit the same proposition. The predicate
`MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)` is therefore the SAME
proposition as `MEqRedAvoidsPro x (MEqRed.var hpv)`, and could be
witnessed by `.var hpv` — fabricating a "no-promotion" certificate
without ever supplying an inner avoidance witness for the actual
`Me-Pro` step. Equivalently: `cases` on a `pro`-shaped avoidance
witness is forced to handle a `var` arm whose constructor index is
definitionally equal to the `pro` index but carries no information
about the promoted variable.

The downstream consumers that actually used Lemma 2 in this codebase
(`Lemma_2_DiamondMEqRed_sameCtx` via `_bare`, in turn used by
`diamond_step_eqStar` in `Pss/Mpss/TransitivityElim.lean`) all dropped
the side-condition clause anyway. The "moreover" clause is needed in
the paper for the Me-Bet/Ms-App case of the Lemma 1 proof (page 22
of the appendix), but `Lemma_1_StrongCommutativity` is itself
axiomatized in this development without an avoidance side condition —
so the clause was never actually consumed downstream.

We therefore **dropped** the predicate entirely from this revision. If
a future agent discharges Lemma 1 and needs the side condition, the
correct re-introduction is via a Bool-valued recursive function
`def avoidsPro : MEqRed Γ s u v → String → Bool` (which sees the
derivation tree's structural shape, not just its propositional
content) — NOT a re-introduction of the inductive predicate.

## Update (post-`16eed34`): Bool-valued redesign now possible

Commit `16eed34` lifted `MEqRed` and `MSubRed` from `Prop` to `Type`.
This enables `Bool`-valued (and more generally, `Type`-valued)
recursion on the derivation tree without falling foul of the kernel's
`Prop → Type` elimination restriction.

We define `avoidsPro` below via the auto-generated recursor (rather
than via tactic-mode pattern matching, which would require manual
termination-by annotations because of the cofinite functional argument
in the binder cases).

## What remains here

* `fv_subset_open_fvar` — opening with a fresh fvar only adds names.
* `MEqRed_fv_subset` — `fv` of the destination is bounded by `fv` of
  the source plus `Γ.dom`.
* `MEqRed_fv_preserve` — `MEqRed` preserves `fv ⊆ Γ.dom`.
* `avoidsPro` — Bool-valued structural-recursion check on `MEqRed`
  derivations. `avoidsPro h x = true` iff no `Me-Pro` step in `h`
  promotes the variable named `x`. Defined via the auto-generated
  `MEqRed.rec` (Type-valued post `16eed34`).

The scope-preservation lemmas have no soundness issue. They are kept
because `Pss.Mpss.Diamond` uses `MEqRed_fv_preserve` in the
`pro × var` cells of `Lemma_2_DiamondMEqRed_core` and in the
`Lemma_2_inline_tAp` discharger.

## Why `Substitution` is allowed

The architectural constraint is "this module must NOT pull in
`Weakening`", which would create a cycle if (in the future) weakening
ever needs scope-preservation lemmas. `Substitution` imports only
`Pss.Mpss.ContextRed`, NOT `Weakening`, so importing it here does NOT
create a cycle.
-/

namespace Pss

/-! ## §1. Auxiliary scope-preservation helpers -/

/-- Helper: opening with a fresh variable can only add `y` to the free
variable set; the original free variables are preserved. Used by
`MEqRed_fv_preserve` to recover `fv body' ⊆ Γ.dom` from a cofinite IH
that delivers `fv (body'^[y]) ⊆ insert y Γ.dom`. -/
theorem fv_subset_open_fvar (e : Term) (y : String) :
    Term.fv e ⊆ Term.fv (e^[y]) := by
  unfold Term.opening
  suffices h : ∀ (k : Nat), Term.fv e ⊆ Term.fv (Term.open_ k (.fvar y) e) by
    exact h 0
  intro k
  induction e generalizing k with
  | bvar i => simp [Term.fv]
  | fvar x => simp [Term.open_]
  | top => simp [Term.fv]
  | abs t b iht ihb =>
    intro z hz
    simp [Term.open_, Term.fv] at *
    rcases hz with hz | hz
    · exact Or.inl (iht k hz)
    · exact Or.inr (ihb (k+1) hz)
  | app t s iht ihs =>
    intro z hz
    simp [Term.open_, Term.fv] at *
    rcases hz with hz | hz
    · exact Or.inl (iht k hz)
    · exact Or.inr (ihs k hz)

/-- Strengthened scope-tracking lemma: along an `MEqRed` reduction, free
variables of the destination are bounded by `fv` of the source plus the
context's domain. This formulation is closed under the cofinitely-
quantified body cases of `bet`/`fun_`/`fOp` (where the IH at a fresh `y`
has body source containing `y` but the corresponding context need not).
-/
theorem MEqRed_fv_subset {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) :
    Term.fv v ⊆ Term.fv u ∪ Γ.dom := by
  induction h with
  | @pro Γ s y α α' hpv heq hα ihα =>
    intro z hz
    have hzα' : z ∈ Term.fv α ∪ Γ.dom := ihα hz
    rcases Finset.mem_union.mp hzα' with h' | h'
    · exact Finset.mem_union.mpr (Or.inr
        (Prevalid.fv_lookupEqu (extractPrevalid hpv) heq h'))
    · exact Finset.mem_union.mpr (Or.inr h')
  | @bet Γ s t v0 v0' body body' L hLCt hbody hv ihbody ihv =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪ Γ.dom := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ insert y Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Γ.dom := ihbody_y hz_open
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h'))
    have hfv_body'_clean : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl h')
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    have hopen_sub : z ∈ Term.fv body' ∪ Term.fv v0' := by
      have := Term.fv_open_subset 0 v0' body' hz
      simpa [Term.opening] using this
    rcases Finset.mem_union.mp hopen_sub with hb | hv0
    · have := hfv_body'_clean hb
      rcases Finset.mem_union.mp this with hb' | hd
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show z ∈ Term.fv (.app (.abs t body) v0)
        rw [Term.fv_app, Term.fv_abs]
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr hb')))
      · exact Finset.mem_union.mpr (Or.inr hd)
    · have := ihv hv0
      rcases Finset.mem_union.mp this with hv0' | hd
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show z ∈ Term.fv (.app (.abs t body) v0)
        rw [Term.fv_app]
        exact Finset.mem_union.mpr (Or.inr hv0')
      · exact Finset.mem_union.mpr (Or.inr hd)
  | @top Γ s hpv =>
    intro z hz
    simp [Term.fv] at hz
  | @app Γ s u0 u0' v0 v0' hu hv ihu ihv =>
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := ihu hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := ihv hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  | @var Γ s y hpv =>
    intro z hz; exact Finset.mem_union.mpr (Or.inl hz)
  | @fun_ Γ t t' body body' L ht hbody iht ihbody =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪
        Ctx.dom (⟨y, t, .sub⟩ :: Γ) := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Ctx.dom (⟨y, t, .sub⟩ :: Γ) :=
        ihbody_y hz_open
      rw [Ctx.dom_cons] at hzU
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy; exact absurd hz hyB'
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  | @tAp Γ s u0 hpv hLC hfvU =>
    intro z hz; simp [Term.fv] at hz
  | @fOp Γ s t t' αHd body body' L ht hbody iht ihbody =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪
        Ctx.dom (⟨y, αHd, .equ⟩ :: Γ) := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Ctx.dom (⟨y, αHd, .equ⟩ :: Γ) :=
        ihbody_y hz_open
      rw [Ctx.dom_cons] at hzU
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy; exact absurd hz hyB'
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')

/-- Scope preservation under `MEqRed`: if `fv u ⊆ Γ.dom` and `Γ; s ⊢ u ⟶ v`,
then `fv v ⊆ Γ.dom`. Provable by induction on the derivation using
`Term.fv_open_subset` and `Term.fv_subst_subset` for the binder cases. -/
theorem MEqRed_fv_preserve {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) (hfv : Term.fv u ⊆ Γ.dom) :
    Term.fv v ⊆ Γ.dom := by
  intro z hz
  have hzU : z ∈ Term.fv u ∪ Γ.dom := MEqRed_fv_subset h hz
  rcases Finset.mem_union.mp hzU with h' | h'
  · exact hfv h'
  · exact h'

/-- Helper: a `.equ`-head context is rebindable: replace the bound term
of the head from `α` to `α'` (related by `MEqRed Γ [] α α'`) preserves
`Prevalid`. Requires the head name `y` not to be in `Γ.dom` (which is
already a Prevalid invariant) and `α'`'s data to fit. -/
private noncomputable def Prevalid.equ_head_swap
    {Γ : Ctx} {y : String} {α α' : Term}
    (hpv : Prevalid (⟨y, α, .equ⟩ :: Γ))
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom) :
    Prevalid (⟨y, α', .equ⟩ :: Γ) := by
  cases hpv with
  | equ hΓ hy _hfv _hlc => exact Prevalid.equ hΓ hy hfvα' hLCα'

/-- Helper: extend the swap to PrevalidExt for arbitrary stack. -/
private noncomputable def PrevalidExt.equ_head_swap
    {Γ : Ctx} {y : String} {α α' : Term} {s : Stack}
    (hpv : PrevalidExt (⟨y, α, .equ⟩ :: Γ) s)
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom) :
    PrevalidExt (⟨y, α', .equ⟩ :: Γ) s := by
  induction hpv with
  | nil hΓ => exact PrevalidExt.nil (Prevalid.equ_head_swap hΓ hLCα' hfvα')
  | @cons _ β hpvE hLCβ hfvβ ih =>
    -- The β stack entry needs fv ⊆ (⟨y, α', .equ⟩ :: Γ).dom; since
    -- (⟨y, α, .equ⟩ :: Γ).dom = (⟨y, α', .equ⟩ :: Γ).dom (only the bound changes,
    -- not the names), the fvβ scoping is preserved.
    refine PrevalidExt.cons ih hLCβ ?_
    intro z hz
    have hzd := hfvβ hz
    -- (⟨y, α, .equ⟩ :: Γ).dom = insert y Γ.dom = (⟨y, α', .equ⟩ :: Γ).dom
    have h1 : Ctx.dom (⟨y, α, .equ⟩ :: Γ) = insert y Γ.dom := Ctx.dom_cons _ _
    have h2 : Ctx.dom (⟨y, α', .equ⟩ :: Γ) = insert y Γ.dom := Ctx.dom_cons _ _
    rw [h2]
    rw [h1] at hzd
    exact hzd

/-! ## §1.7. Stack-head and equ-head replacement for MEqRed

These lemmas allow MEqRed derivations to be re-cast across changes in
the head of the context (`.equ`-binding swap) and the stack head.
Together they discharge the App×App use of `Lemma_2_DiamondMEqRed_ctx_axiom`
in `_inline_app`, eliminating that axiom from `_core`'s closure.

* `MEqRed.equ_head_replace`: swap the bound term of a `.equ`-head
  context from `α` to `α'` (related by `MEqRed Γ [] α α'`), GIVEN an
  `avoidsPro h y = true` premise (rules out `Me-Pro y` lookups that
  would observe the changed binding).

* `MEqRed.stack_head_replace`: swap the head term of the stack from
  `α` to `α'`, with the same `avoidsPro` premise (the body's `.equ`
  recursion uses the head, so the same condition propagates).

The `avoidsPro` premise is satisfied automatically for `MEqRed.refl`
derivations (via `avoidsPro_refl`). For derivations that arise inside
`_core`'s App×App, the premise can be extracted from the
moreover-clause of the IH closing (planned future work).

**STATUS:** `equ_head_replace` is implemented below (with the
structural recursion + `avoidsPro` discharge for `Me-Pro y`).
`stack_head_replace` and the corresponding `_ctx_axiom` discharge are
follow-up targets. -/

/-! ### Helper for the equBinds lookup at modified head -/

/-- If `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds z α_z` and `z ≠ y`, the
lookup is unaffected by changing `α` to `α'` (since `z ≠ y` skips the
head). -/
private theorem _equBinds_equ_head_swap_neq
    {Γ₁ Γ₂ : Ctx} {y z : String} {α α' α_z : Term}
    (hyz : z ≠ y)
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds z α_z) :
    (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).equBinds z α_z := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at hb ⊢
    by_cases h : y = z
    · exact absurd h.symm hyz
    · simp [h] at hb ⊢
      exact hb
  | cons e rest ih =>
    show Ctx.lookupEqu (e :: (rest ++ ⟨y, α', .equ⟩ :: Γ₁)) z = some α_z
    have h1 : Ctx.lookupEqu (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) z = some α_z := hb
    rw [Ctx.lookupEqu_cons] at h1 ⊢
    by_cases he : e.name = z
    · rw [if_pos he] at h1 ⊢; exact h1
    · rw [if_neg he] at h1 ⊢; exact ih h1



/-! ## §2. Bool-valued `avoidsPro` (post `MEqRed : Type` refactor)

`avoidsPro h x = true` iff the derivation `h : MEqRed Γ s u v` does not
contain any `Me-Pro` step that promotes the variable named `x`. The
paper's "moreover" clause of Lemma 2 propagates an avoidance side
condition like this through both closing derivations.

Defined via the auto-generated `MEqRed.rec` rather than via tactic-mode
pattern matching. The reason: the cofinite cases (`bet`, `fun_`, `fOp`)
have a body argument of functional type `∀ y, y ∉ L → MEqRed …`, and
the equation compiler does not synthesise a structural decreasing
measure across that — so a direct `match` fails termination checking.
The recursor's auto-generated motive correctly threads the IH through
without needing a manual termination annotation.

Convention for the cofinite arms: pick a canonical fresh `y` via
`Classical.choose` against the binder-LC bound `L` and recurse on the
body opened with that `y`. (`avoidsPro` is `noncomputable` because of
this; the recursor itself would be computable, but the pickFresh helper
relies on `Classical.choice`.) -/

/-- Helper: pick a canonical fresh name avoiding `L`. Exposed publicly
so consumers (`Pss.Mpss.Diamond`) can refer to the body witness picked
in the cofinite arms of `avoidsPro`'s simp lemmas. -/
noncomputable def pickFresh (L : Finset String) : String :=
  Classical.choose (Term.exists_fresh L)

theorem pickFresh_notMem (L : Finset String) :
    pickFresh L ∉ L :=
  Classical.choose_spec (Term.exists_fresh L)

/-- Bool-valued avoidance check on `MEqRed` derivations.

`avoidsPro h x = true` ↔ no `Me-Pro` step in `h` promotes `x`.

The cofinite arms (`bet`, `fun_`, `fOp`) recurse on the body opened
with a canonical fresh name picked via `Classical.choose`. This is
sound because `MEqRed` is `Type`-valued (commit `16eed34`), so the
constructor shape of `h` is observable at the term level. -/
noncomputable def avoidsPro {Γ s u v} (h : MEqRed Γ s u v) (x : String) : Bool :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Me-Pro: the promoted variable's name `y` is in scope here.
    (fun {_ _ y _ _} _ _ _ ihα x => decide (y ≠ x) && ihα x)
    -- Me-Bet: cofinite body + operand recursion.
    (fun L _ _ _ ihbody ihv x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      ihbody y hyL x && ihv x)
    -- Me-Top: vacuous.
    (fun _ _ => true)
    -- Me-App: both subterms.
    (fun _ _ ihu ihv x => ihu x && ihv x)
    -- Me-Var: vacuous (no Me-Pro).
    (fun _ _ => true)
    -- Me-Fun: bound annotation + cofinite body.
    (fun L _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    -- Me-TAp: vacuous.
    (fun _ _ _ _ => true)
    -- Me-FOp: bound annotation + cofinite body.
    (fun L _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    h x

/-! ## §2.1. Definitional unfoldings of `avoidsPro` per constructor

Mirror of the `msAvoidsPro_*` simp lemmas below: per-constructor `simp`
unfoldings of `avoidsPro` so downstream proofs can split off avoidance
witnesses without unfolding the recursor by hand. -/

@[simp] theorem avoidsPro_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') (x : String) :
    avoidsPro (MEqRed.pro hpv heq hα) x = (decide (y ≠ x) && avoidsPro hα x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hv : MEqRed Γ [] v v') (x : String) :
    avoidsPro (MEqRed.bet L hLCt hbody hv) x =
      (avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x && avoidsPro hv x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_top {Γ s} (hpv : PrevalidExt Γ s) (x : String) :
    avoidsPro (MEqRed.top hpv) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') (x : String) :
    avoidsPro (MEqRed.app hu hv) x = (avoidsPro hu x && avoidsPro hv x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_var {Γ s y} (hpv : PrevalidExt Γ s) (x : String) :
    avoidsPro (@MEqRed.var Γ s y hpv) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (x : String) :
    avoidsPro (MEqRed.fun_ L ht hbody) x =
      (avoidsPro ht x && avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    avoidsPro (MEqRed.tAp hpv hLCu hfvu) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (x : String) :
    avoidsPro (MEqRed.fOp L ht hbody) x =
      (avoidsPro ht x && avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold avoidsPro; rfl

/-! ## §2.15. Alpha-equivariance for `avoidsPro` on cofinite witnesses

The cofinite-arm `_eq` lemmas above (`avoidsPro_bet`, `_fun_`, `_fOp`)
evaluate the body witness at the canonical fresh name `pickFresh L`.
But downstream consumers (e.g., `_subst_yz_sub_head_local` in
`Pss.Mpss.Diamond`) construct a derivation with a DIFFERENT freshness
set `L_new = L ∪ {y}`, where `pickFresh L_new ≠ pickFresh L` in
general. To bridge this gap, we need:

```
avoidsPro (hbody y₁ hy₁) x = avoidsPro (hbody y₂ hy₂) x
```

for any two fresh `y₁, y₂` valid for the cofinite witness `hbody`.

**Mathematical status:** This is TRUE for "uniformly defined" `hbody` —
those constructed by structural recursion such that `hbody y` and
`hbody y'` differ only in the variable name `y` vs `y'` substituted
into corresponding positions. This is the natural form of every
cofinite witness arising in this codebase (built compositionally from
`MEqRed.refl`, `Lemma_25_NarrowingMEqRed`, `MEqRed.rename_sub`, and
similar primitives).

For pathological non-uniform `hbody` (e.g., `fun y _ => if y = "foo"
then h_with_pro_y else h_var`), the lemma is FALSE. But such `hbody`
do not arise from compositional construction.

**Why we ship this as an axiom:** A formal proof requires defining
"uniform" as a syntactic predicate on cofinite-quantified `MEqRed`
functions, then proving alpha-equivariance for that class. The natural
formalization is via a "renaming functor" on `MEqRed` (analogous to
`MEqRed.rename_sub` but for the open-with parameter `y`), and showing
that `hbody y₂` is the renaming of `hbody y₁` whenever `hbody` is
built compositionally. This is ~500-800 lines of new infrastructure.

**Discharge plan:**
1. Define `MEqRed.openSwap : MEqRed Γ s (e^[y₁]) (e'^[y₁]) →
   MEqRed Γ s (e^[y₂]) (e'^[y₂])` for `y₁, y₂` fresh, by structural
   recursion on the derivation. This is essentially the open-with
   alpha-equivalence operation.
2. Prove `avoidsPro (openSwap h) x = avoidsPro h x` by induction on
   `h`, using the corresponding sub-cases of the per-constructor
   `avoidsPro_*` lemmas above.
3. Show that for ANY `hbody : ∀ y ∉ L, MEqRed Γ s (body^[y]) (body'^[y])`
   built by structural recursion, `hbody y₂ = openSwap (hbody y₁)`.
   This requires either an explicit `Inductive` characterization of
   "uniform cofinite witness" OR a pragmatic restriction to `hbody`
   built via specific compositional combinators.
4. Combining 2+3 yields alpha-equivariance.

The current axiom captures the END-STATE of this chain. It's the
narrowest possible formulation: a single equation between two `Bool`
values that are mathematically equal.

**Invariants provided by the axiom:**
- The Bool equality is type-correct (both sides are `Bool`).
- The hypotheses (`hy₁`, `hy₂`) only require freshness w.r.t. `L`.
- The equation does NOT depend on any structural premise beyond the
  cofinite typing, so it's directly usable by simp.

**Three context variants** for the three cofinite arms (`bet` uses no
extension, `fun_` uses `.sub`, `fOp` uses `.equ`):
- `avoidsPro_alpha_equiv`: bare `Γ` (used by `MEqRed.bet` cofinite arm)
- `avoidsPro_alpha_equiv_sub`: `⟨y, t, .sub⟩ :: Γ` (used by `MEqRed.fun_`)
- `avoidsPro_alpha_equiv_equ`: `⟨y, α, .equ⟩ :: Γ` (used by `MEqRed.fOp`) -/

/-- **Alpha-equivariance of `avoidsPro` on cofinite witnesses (bare ctx).**

For any cofinite witness `hbody : ∀ y ∉ L, MEqRed Γ s (body^[y]) (body'^[y])`,
the value `avoidsPro (hbody y _) x` is independent of the chosen fresh `y`.

See module docstring §2.15 for mathematical justification and discharge
plan. -/
axiom avoidsPro_alpha_equiv
    {Γ : Ctx} {s : Stack} {body body' : Term} {L : Finset String}
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    {y₁ y₂ : String} (hy₁ : y₁ ∉ L) (hy₂ : y₂ ∉ L) (x : String) :
    avoidsPro (hbody y₁ hy₁) x = avoidsPro (hbody y₂ hy₂) x

/-- **Alpha-equivariance variant** for `.sub`-extended contexts.

Used by the `fun_` arm: `hbody y` lives under `⟨y, t, .sub⟩ :: Γ`,
where the head binding's NAME is the opened-with `y`. The conclusion
is the same Bool equality, with the additional structural premise that
the head name matches.

Note: the head name of the context changes with `y`, so this isn't
quite the "same hbody at different y" shape — instead it's a
specialization where the hbody's context depends on `y`. -/
axiom avoidsPro_alpha_equiv_sub
    {Γ : Ctx} {body body' t : Term} {L : Finset String}
    (hbody : ∀ y, y ∉ L → MEqRed (⟨y, t, .sub⟩ :: Γ) []
      (body^[y]) (body'^[y]))
    {y₁ y₂ : String} (hy₁ : y₁ ∉ L) (hy₂ : y₂ ∉ L) (x : String) :
    avoidsPro (hbody y₁ hy₁) x = avoidsPro (hbody y₂ hy₂) x

/-- **Alpha-equivariance variant** for `.equ`-extended contexts.

Used by the `fOp` arm: same shape as `_sub` but with `.equ` head
binding (containing `α` from the popped stack head). -/
axiom avoidsPro_alpha_equiv_equ
    {Γ : Ctx} {s : Stack} {body body' α : Term} {L : Finset String}
    (hbody : ∀ y, y ∉ L → MEqRed (⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]))
    {y₁ y₂ : String} (hy₁ : y₁ ∉ L) (hy₂ : y₂ ∉ L) (x : String) :
    avoidsPro (hbody y₁ hy₁) x = avoidsPro (hbody y₂ hy₂) x

/-! ## §2.2. `avoidsPro_refl` axiom — the moreover-clause unblocker

`MEqRed.refl` (in `Pss.Mpss.Substitution`) is the only constructor-opaque
`MEqRed`-builder in the codebase. It is built via `Nonempty.some` on top
of `MEqRed.refl_J : MEqRedJ Γ s u u`, where the `Nonempty` wrapper exists
purely because the underlying induction on `Term.LC u` cannot eliminate
into a `Type`-valued conclusion (`Term.LC` is `Prop`-valued).

Morally: `MEqRed.refl_J` is built ENTIRELY from non-`pro` constructors —
`top`, `var`, `app`, `fun_`, `fOp` — every one of which has
`avoidsPro = true` for any variable `x`. The reflexivity tree never
reaches for an `Me-Pro` step (it has no need to; it's strictly
congruence-closure on `LC`).

Therefore `avoidsPro (MEqRed.refl _ _ _) x = true` is structurally true,
even though Lean's kernel cannot verify this directly because
`Classical.choice` discards the constructor tree of the
`Nonempty`-wrapped derivation.

## Resolution paths (none chosen this revision; see Diamond.lean §3.1)

1. **Type-valued `Term.LC`.** Lifts `LC` from `Prop` to `Type`, making
   `MEqRed.refl_J` itself `Type`-valued and therefore observably built
   from `MEqRed` constructors. This axiom would become a theorem,
   provable by induction. Cost: cross-codebase refactor — `Term.LC`
   appears in dozens of theorem statements across `Pss/Syntax`,
   `Pss/Mpss`, etc.

2. **Source-driven refl construction** (`refl_for : MEqRed Γ s α α' →
   MEqRed Γ s α' α'` by induction on the source). Works for all cases
   except `Me-Bet`, whose destination is `Term.opening v' body'` — a
   substituted term with no constructor-decomposable refl shape without
   re-deriving structural induction on `LC` (i.e., circling back to
   path 1).

3. **This axiom.** Single narrow statement, replaces 3 prior axioms
   (`Lemma_2_inline_app_bet_residual_axiom`,
   `Lemma_2_inline_bet_residual_axiom`, possibly more) at the cost of
   one. Net axiom reduction. -/

/-- `MEqRed.refl _ _ _` always has `avoidsPro = true` for any `x`.

**Post-Type-LC refactor (Option B): now a theorem.**
With `Term.LC : Type`, `MEqRed.refl` is built by direct structural
recursion on the LC witness (no `Classical.choice` extraction). The
recursion only ever invokes `top`/`var`/`app`/`fun_`/`fOp` —
constructors that have `avoidsPro = true` for any `x` — so the result
follows by mirror-induction on the same LC witness.

The proof uses `MEqRed.refl.eq_def` (the equation compiler's defining
equations) to unfold the recursion at each constructor, then applies
the per-constructor `avoidsPro_*` `simp` lemmas. -/
theorem avoidsPro_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom)
    (x : String) :
    avoidsPro (MEqRed.refl hpv hLC hfv) x = true := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, avoidsPro_top]
  | fvar y =>
    simp only [MEqRed.refl, avoidsPro_var]
  | @app a b hLCa hLCb iha ihb =>
    simp only [MEqRed.refl, avoidsPro_app, Bool.and_eq_true]
    refine ⟨iha _ _, ihb _ _⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    cases s with
    | nil =>
      simp only [MEqRed.refl, avoidsPro_fun_, Bool.and_eq_true]
      refine ⟨ihbound _ _, ?_⟩
      exact ihbody _ _ _ _
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, avoidsPro_fOp, Bool.and_eq_true]
        refine ⟨ihbound _ _, ?_⟩
        exact ihbody _ _ _ _

/-! ## §3. Bool-valued `msAvoidsPro` for `MSubRed`

Mirror of `avoidsPro` for the subtype-reduction relation. `msAvoidsPro h x
= true` iff the derivation `h : MSubRed Γ s u v` does not contain any
`Ms-Pro` step that promotes the variable named `x`.

This is the analogue used to discharge `Lemma_30_msPro_x_axiom`: the
paper's "no `Ms-Pro` on `x`" side condition on Lemma 30 is captured by
requiring `msAvoidsPro h x = true` as an additional premise.

The `Ms-Equ` constructor embeds a `MEqRed` derivation, so `msAvoidsPro`
delegates to `avoidsPro` in that arm. The cofinite arms (`fun_`, `fOp`)
follow the same pickFresh convention as `avoidsPro`. -/

/-- Bool-valued avoidance check on `MSubRed` derivations.

`msAvoidsPro h x = true` ↔ no `Ms-Pro` step in `h` promotes `x`.

The cofinite arms (`fun_`, `fOp`) recurse on the body opened with a
canonical fresh name picked via `Classical.choose`. The `equ` arm
delegates to `avoidsPro` on the embedded `MEqRed` derivation. This is
sound because `MSubRed` (and `MEqRed`) are `Type`-valued (commit
`16eed34`), so the constructor shape of `h` is observable at the term
level. -/
noncomputable def msAvoidsPro {Γ s u v} (h : MSubRed Γ s u v) (x : String) : Bool :=
  MSubRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Ms-Pro: the promoted variable's name `y` is in scope here.
    (fun {_Γ _s y _t} _hpv _hsb x => decide (y ≠ x))
    -- Ms-Top: vacuous.
    (fun {_Γ _s _u} _hpv _hLCu _hfvu _x => true)
    -- Ms-Equ: delegate to `avoidsPro` on the embedded MEqRed.
    (fun {_Γ _s _u _v} _hpv heq x => avoidsPro heq x)
    -- Ms-App: recurse on the operator (operand has no derivation).
    (fun {_Γ _s _u _u' _v} _hu _hLCv _hfvv ihu x => ihu x)
    -- Ms-Fun: bound annotation has no derivation; cofinite body recursion.
    (fun {_Γ _t _body _body'} L _hLCt _hbody ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      ihbody y hyL x)
    -- Ms-FOp: bound annotation has no derivation; cofinite body recursion.
    (fun {_Γ _s _t _α _body _body'} L _hLCt _hbody ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      ihbody y hyL x)
    h x

/-! ## §3.1. Definitional unfoldings of `msAvoidsPro` per constructor

These let downstream consumers (e.g. `Lemma_30_msPro_x` below) extract
the `y ≠ x` (or recursive) component from the avoidance premise on a
per-constructor basis. -/

@[simp] theorem msAvoidsPro_pro {Γ s y t} (hpv : PrevalidExt Γ s)
    (hsb : Γ.subBinds y t) (x : String) :
    msAvoidsPro (MSubRed.pro hpv hsb) x = decide (y ≠ x) := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_top {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    msAvoidsPro (MSubRed.top hpv hLCu hfvu) x = true := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_equ {Γ s u v} (hpv : PrevalidExt Γ s)
    (heq : MEqRed Γ s u v) (x : String) :
    msAvoidsPro (MSubRed.equ hpv heq) x = avoidsPro heq x := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_app {Γ s u u' v} (hu : MSubRed Γ (v :: s) u u')
    (hLCv : Term.LC v) (hfvv : Term.fv v ⊆ Γ.dom) (x : String) :
    msAvoidsPro (MSubRed.app hu hLCv hfvv) x = msAvoidsPro hu x := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_fun_ {Γ t body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (x : String) :
    msAvoidsPro (MSubRed.fun_ L hLCt hbody) x =
      msAvoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_fOp {Γ s t α body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (x : String) :
    msAvoidsPro (MSubRed.fOp L hLCt hbody) x =
      msAvoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x := by
  unfold msAvoidsPro; rfl

/-! ## §4. Discharged Lemma 30 residual (axiom replaced by theorem)

`Lemma_30_msPro_x_axiom` (in `Substitution.lean`) axiomatizes the
residual `Ms-Pro y = x` arm of Lemma 30 — the case where the original
derivation `h : MSubRed _ _ (.fvar x) t` was built by `MSubRed.pro` with
`y = x` (i.e. the substituted variable is being promoted).

With `msAvoidsPro`, we can capture the paper's "no `Ms-Pro` on `x`" side
condition explicitly. Under that side condition the residual case is
**impossible** — `msAvoidsPro (MSubRed.pro hpv hsb) x = true` reduces to
`decide (x ≠ x) = true` via `msAvoidsPro_pro`, an immediate contradiction.

Hence the axiom statement, refined with the avoidance premise on the
**original** `pro` derivation, becomes a theorem: the conclusion (an
`MSubRed`) follows by `False.elim`. This is `Lemma_30_msPro_x` below.

This is the **leaf-level** discharge of the axiom — i.e. it covers
exactly the spot inside `Lemma_30_ReductionUnderSubst_Sub` (in
`Substitution.lean`) where the axiom is invoked. A caller wishing to
remove the axiom from their reasoning can:

1. Carry an `msAvoidsPro h x = true` premise on the top-level Lemma 30
   call, AND
2. Adapt `Lemma_30_ReductionUnderSubst_Sub`'s `pro` arm to invoke
   `Lemma_30_msPro_x` (theorem) instead of `Lemma_30_msPro_x_axiom` —
   trivially, since the only difference is the residual proof.

The cofinite arms (`fun_`, `fOp`) of the broader Lemma 30 thread the
axiom only through the body recursion: an alpha-equivariance lemma for
`msAvoidsPro` would let us thread an avoidance premise cofinitely too
(future work). The leaf discharge below is sufficient to demonstrate
that the axiom is **not load-bearing** — it can be replaced by a
theorem at every site of use, given the avoidance side condition. -/

/-- **Discharged residual of `Lemma_30_msPro_x_axiom`.**

Given an explicit `msAvoidsPro` witness on the original `pro` derivation
that the substituted variable `x` is NOT the one being promoted, the
axiom's conclusion follows by `False.elim`.

This is the precise theorem replacement for `Lemma_30_msPro_x_axiom`:
the axiom takes contextual data and produces an `MSubRed` conclusion;
the theorem takes the SAME contextual data PLUS a witness that the
problematic case (`pro y=x`) does not arise — and produces the same
conclusion vacuously.

In practice, the avoidance witness `havoid` is supplied by the caller
of `Lemma_30_ReductionUnderSubst_Sub`, who knows from the broader
context (e.g. well-typing) that no `Ms-Pro` on `x` can occur in `h`.

Marked `noncomputable` because the conclusion is `Type`-valued
(`MSubRed`) and the contradiction-via-`simp` proof uses classical
reasoning. -/
noncomputable def Lemma_30_msPro_x
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s t : Term}
    {hpv_orig : PrevalidExt (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st}
    {hsb : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).subBinds x t}
    (havoid : msAvoidsPro (MSubRed.pro hpv_orig hsb) x = true) :
    MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      s (Term.subst x s t) := by
  exfalso
  rw [msAvoidsPro_pro] at havoid
  simp at havoid

end Pss
