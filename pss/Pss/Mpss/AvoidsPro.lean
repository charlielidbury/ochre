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

/-- Helper: pick a canonical fresh name avoiding `L`. -/
private noncomputable def pickFresh (L : Finset String) : String :=
  Classical.choose (Term.exists_fresh L)

private theorem pickFresh_notMem (L : Finset String) :
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

end Pss
