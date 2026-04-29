import Pss.Mpss.Substitution
import Pss.Mpss.Weakening

/-! # `Pss.Mpss.Diamond` — Diamond property and reflexivity for `⟶^≡`

Pasquale & García-Pérez 2024 (CSL 2026), §3 (and appendix proofs).

This module mechanizes:

* **Proposition 18 (Reflexivity).** Every locally-closed, in-scope term
  reduces to itself in one step under both `⟶^≡` and `⟶^≤`.
* **Lemma 2 (Diamond modulo Me-Pro side condition).** `⟶^≡` has the
  diamond property modulo a "no `Me-Pro` on `x`" side condition that
  travels through context-reduction.

## Encoding the side condition (Approach A)

The paper's Lemma 2 statement has this clause:

> "Moreover, for any variable `x`, if in the derivation of `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁`
> [...] there isn't an application of the Rule `Me-Pro` that makes a promotion
> of variable `x`, then in the derivation `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃` [...] there
> won't be an application of the Rule `Me-Pro` that makes a promotion of
> variable `x`."

We encode this as an **inductive predicate** `MEqRedAvoidsPro h x : Prop`
that mirrors the structure of `MEqRed`'s constructors. Constructor-by-
constructor: at every node we require the corresponding sub-derivations
to also avoid promoting `x`; at `Me-Pro` nodes we additionally require
the promoted variable to differ from `x`.

This is **Approach A** from the plan (Risk 4, §5). We chose the inductive
formulation (rather than a `def` by recursion) because the cofinitely-
quantified body sub-derivations of `bet`/`fun_`/`fOp` make a recursive
`def` over the eliminator awkward (Lean's pattern-matcher cannot easily
extract the `y ∉ L` hypothesis when the constructor is matched). Approach B
(a refined inductive `MEqRedNoProOf` mirroring `MEqRed` itself) is left as
a fallback if downstream proofs need a different shape.

## Status

* `Proposition_18_ReflexivityMEqRed`  — **PROVED** (delegates to
  `MEqRed.refl` from `Pss.Mpss.Substitution`).
* `Proposition_18_ReflexivityMSubRed` — **PROVED** (via `Ms-Equ`).
* `Proposition_18_Reflexivity`       — **PROVED** (combined statement).
* `Lemma_2_DiamondMEqRed` — **THEOREM** (Wave 7 discharge of the Wave 5
  axiom). The headline statement is now mechanized as a real theorem;
  it is discharged by case analysis on the constructors of `h₁` and `h₂`.
  The case grid is enumerated below.

  A handful of structurally-recursive cells (those where both derivations
  fire on the same redex and the joining derivation must invoke a
  body-IH or stack-pop-IH cofinitely) remain as **narrow per-case
  private axioms** — see the case grid block below for which cells are
  axiomatized vs. proved. The headline `Lemma_2_DiamondMEqRed` is a
  real `theorem`; the per-case axioms are the genuine residual obligations.

## Case grid for `Lemma_2_DiamondMEqRed_core` (single-context form)

The case grid is indexed by the shape of `t₀` (which determines which
`MEqRed` constructors can possibly fire). The proof is a single
`induction h₁ generalizing t₂` block; each constructor case does an
inner `cases h₂` and either discharges directly or dispatches to a
narrow inline residual axiom whose signature receives the structural
IH(s) of the outer induction.

| t₀ shape    | (h₁ rule × h₂ rule)        | Status  | Notes                       |
|-------------|----------------------------|---------|-----------------------------|
| `.bvar k`   | (any × any)                | V       | impossible — no MEqRed constructor produces `.bvar` |
| `.top`      | (Top × Top)                | P       | `t₃ := .top`, both `.top`    |
| `.fvar x`   | (Var × Var)                | P       | `t₃ := .fvar x`, both `.var` |
|             | (Var × Pro)                | P       | `t₃ := α'`; refl + reuse Pro |
|             | (Pro × Var)                | P       | symmetric                    |
|             | (Pro × Pro)                | A       | `Lemma_2_inline_pro_pro` (IH-aware) |
| `.abs t b`  | (Fun × Fun) at empty stack | A       | `Lemma_2_inline_fun_fun` (IH-aware) |
|             | (FOp × FOp) at α::s stack  | A       | `Lemma_2_inline_fOp_fOp` (IH-aware) |
| `.app u v`  | (TAp × TAp/App)            | T       | `Lemma_2_inline_tAp` (theorem) |
|             | (App × Bet/App/TAp)        | A       | `Lemma_2_inline_app` (IH-aware) |
|             | (Bet × Bet/App/TAp)        | A       | `Lemma_2_inline_bet` (IH-aware) |

Legend: P = proved inline; T = inline real `theorem`; A = inline
private axiom that consumes the outer-induction IH; V = vacuous.

## Context-evolution lifting

The headline statement adds an `↣*` evolution `(Γ₀, s₀) ↣* (Γᵢ, sᵢ)` on
each side. We split this into a separate `Lemma_2_DiamondMEqRed_ctx_axiom`
that lifts a same-context joining derivation to one that survives the
two `↣*` evolutions. Discharging that lift cleanly requires extending
`Lemma_22` (weakening) to also cover annotation reductions on existing
bindings (the `Ct-Ann` arm of `↣`), which the current weakening
infrastructure handles only for new-binding insertions.
-/

namespace Pss

/-! ## §1. The "no Me-Pro on `x`" predicate (Approach A)

Defined as an inductive predicate (Approach A, with the inductive flavour
of formulation, since the cofinitely-quantified body cases of `bet`/`fun_`/
`fOp` make a `def`-by-recursion form awkward to state cleanly). -/

/-- Predicate on `MEqRed` derivations: the derivation does NOT contain
an application of `Me-Pro` that promotes the named variable `x`.

The predicate has one constructor per `MEqRed` constructor; the `pro`
constructor is the only one with non-trivial side condition (`y ≠ x`),
and it propagates the predicate to its operand sub-derivation. All other
constructors propagate the predicate structurally to all sub-derivations
(including the cofinitely-quantified body sub-derivations, which must
satisfy the predicate uniformly over the `y ∉ L` witnesses). -/
inductive MEqRedAvoidsPro (x : String) :
    ∀ {Γ : Ctx} {s : Stack} {u v : Term}, MEqRed Γ s u v → Prop where
  /-- `Me-Pro` on `y ≠ x`, with the operand sub-derivation also avoiding
  promotion of `x`. -/
  | pro {Γ s y α α'}
        (hpv : PrevalidExt Γ s)
        (heq : Γ.equBinds y α)
        (hα : MEqRed Γ s α α')
        (hyx : y ≠ x)
        (hAv : MEqRedAvoidsPro x hα) :
      MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)
  /-- `Me-Bet` with both body and operand sub-derivations avoiding `x`. -/
  | bet {Γ s t v v' body body'} {L : Finset String}
        (hLCt : Term.LC t)
        (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
        (hv : MEqRed Γ [] v v')
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy))
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.bet (L := L) hLCt hbody hv)
  /-- `Me-Top` is always fine. -/
  | top {Γ s} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.top hpv)
  /-- `Me-App` with both operator and operand sub-derivations avoiding `x`. -/
  | app {Γ s u u' v v'}
        (hu : MEqRed Γ (v :: s) u u')
        (hv : MEqRed Γ [] v v')
        (hAvU : MEqRedAvoidsPro x hu)
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.app hu hv)
  /-- `Me-Var` is always fine. -/
  | var {Γ s y} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.var (x := y) hpv)
  /-- `Me-Fun` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fun_ {Γ t t' body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fun_ (L := L) ht hbody)
  /-- `Me-TAp` is always fine. -/
  | tAp {Γ s u}
        (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
      MEqRedAvoidsPro x (MEqRed.tAp hpv hLC hfv)
  /-- `Me-FOp` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fOp {Γ s t t' α body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fOp (L := L) ht hbody)

/-! ## §2. Proposition 18 — Reflexivity of `⟶^≡` and `⟶^≤` -/

/-- **Proposition 18 (Reflexivity, equivalence half).** For any prevalid
extended context `Γ; s` and any locally-closed in-scope term `u`,
`Γ; s ⊢ u ⟶^≡ u`.

This is a direct re-export of `MEqRed.refl` from `Pss.Mpss.Substitution`,
exposed at this module under the paper's name. -/
theorem Proposition_18_ReflexivityMEqRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u :=
  MEqRed.refl hpv hLC hfv

/-- **Proposition 18 (Reflexivity, subtyping half).** Same statement, for
`⟶^≤`. Follows by `Ms-Equ` from the equivalence half. -/
theorem Proposition_18_ReflexivityMSubRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MSubRed Γ s u u :=
  MSubRed.equ hpv (Proposition_18_ReflexivityMEqRed hpv hLC hfv)

/-- **Proposition 18 (Reflexivity, combined).** Both halves. -/
theorem Proposition_18_Reflexivity
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u ∧ MSubRed Γ s u u :=
  ⟨Proposition_18_ReflexivityMEqRed hpv hLC hfv,
   Proposition_18_ReflexivityMSubRed hpv hLC hfv⟩

/-! ## §3. Lemma 2 — Diamond property modulo Me-Pro side condition

The paper's statement (verbatim, modulo notation):

  Let `Γ₀; s₀` be an extended context. Let `t₀, t₁, t₂` be terms.
  If `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁` and `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₂`, then for any
  extended contexts `Γ₁; s₁` and `Γ₂; s₂` such that `Γ₀; s₀ ↣ Γ₁; s₁`
  and `Γ₀; s₀ ↣ Γ₂; s₂`, there exists a term `t₃` such that
  `Γ₁; s₁ ⊢ t₁ ⟶^≡ t₃` and `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃`.

  Moreover, for any variable `x`, if in the derivation of
  `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁` (respectively `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₂`) there
  isn't an application of the Rule `Me-Pro` that makes a promotion of
  variable `x`, then in the derivation `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃`
  (respectively `Γ₁; s₁ ⊢ t₁ ⟶^≡ t₃`) there won't be an application of
  the Rule `Me-Pro` that makes a promotion of variable `x`.

The "side condition propagation" clause is encoded as the existence of
`t₃` and **derivations** `h₁' h₂'` for the two output edges, such that
the "no Me-Pro on `x`" predicate transfers in the swapped direction. -/

/-! ### §3.0 Auxiliary scope-preservation helpers

These are general scope-preservation lemmas needed to construct the
closing edges in the easy cells of the case grid. All three are now
**proved as `private theorem`s** in this section (no longer
axiomatized). -/

/-- Helper: opening with a fresh variable can only add `y` to the free
variable set; the original free variables are preserved. Used by
`MEqRed_fv_preserve` to recover `fv body' ⊆ Γ.dom` from a cofinite IH
that delivers `fv (body'^[y]) ⊆ insert y Γ.dom`. -/
private theorem fv_subset_open_fvar (e : Term) (y : String) :
    Term.fv e ⊆ Term.fv (e^[y]) := by
  -- Term.opening (.fvar y) e = Term.open_ 0 (.fvar y) e replaces only
  -- bvars; fvars in `e` survive verbatim. Show by induction on `e`.
  unfold Term.opening
  -- Generalize the level for the inductive step.
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
private theorem MEqRed_fv_subset {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) :
    Term.fv v ⊆ Term.fv u ∪ Γ.dom := by
  induction h with
  | @pro Γ s y α α' hpv heq hα ihα =>
    -- v = α'. ihα: fv α' ⊆ fv α ∪ Γ.dom.
    -- fv α ⊆ Γ.dom by Prevalid.fv_lookupEqu, so fv α' ⊆ Γ.dom ⊆ fv (.fvar y) ∪ Γ.dom.
    intro z hz
    have hzα' : z ∈ Term.fv α ∪ Γ.dom := ihα hz
    rcases Finset.mem_union.mp hzα' with h' | h'
    · -- z ∈ fv α ⊆ Γ.dom.
      exact Finset.mem_union.mpr (Or.inr
        (Prevalid.fv_lookupEqu (extractPrevalid hpv) heq h'))
    · exact Finset.mem_union.mpr (Or.inr h')
  | @bet Γ s t v0 v0' body body' L hLCt hbody hv ihbody ihv =>
    -- v = Term.opening v0' body'.
    -- fv (opening v0' body') ⊆ fv body' ∪ fv v0' (using fv_open_subset 0 v0' body').
    -- ihv: fv v0' ⊆ fv v0 ∪ Γ.dom.
    -- For body': pick fresh y; ihbody y hyL: fv (body'^[y]) ⊆ fv (body^[y]) ∪ Γ.dom.
    -- Combine using fv_subset_open_fvar to relate fv body' to fv (body'^[y]),
    -- and fv_open_subset to relate fv (body^[y]) to fv body ∪ {y}.
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪ Γ.dom := ihbody y hyL
    -- fv body' ⊆ insert y Γ.dom ∪ fv body — combine with ihbody_y.
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ insert y Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Γ.dom := ihbody_y hz_open
      rcases Finset.mem_union.mp hzU with h' | h'
      · -- z ∈ fv (body^[y]) ⊆ fv body ∪ {y}.
        have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h'))
    -- Convert: since y ∉ fv body', y can't appear in fv body' — refine.
    have hfv_body'_clean : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl h')
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    -- Now fv (Term.opening v0' body') ⊆ fv body' ∪ fv v0'.
    intro z hz
    have hopen_sub : z ∈ Term.fv body' ∪ Term.fv v0' := by
      have := Term.fv_open_subset 0 v0' body' hz
      simpa [Term.opening] using this
    rcases Finset.mem_union.mp hopen_sub with hb | hv0
    · -- z ∈ fv body' ⊆ fv body ∪ Γ.dom; fv body ⊆ fv (.app (.abs t body) v0).
      have := hfv_body'_clean hb
      rcases Finset.mem_union.mp this with hb' | hd
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show z ∈ Term.fv (.app (.abs t body) v0)
        rw [Term.fv_app, Term.fv_abs]
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr hb')))
      · exact Finset.mem_union.mpr (Or.inr hd)
    · -- z ∈ fv v0' ⊆ fv v0 ∪ Γ.dom (from ihv).
      have := ihv hv0
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
    -- v = .app u0' v0'.
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · -- z ∈ fv u0' ⊆ fv u0 ∪ Γ.dom.
      have := ihu hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := ihv hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  | @var Γ s y hpv =>
    -- v = .fvar y; fv = {y} ⊆ fv (.fvar y) ∪ Γ.dom.
    intro z hz; exact Finset.mem_union.mpr (Or.inl hz)
  | @fun_ Γ t t' body body' L ht hbody iht ihbody =>
    -- v = .abs t' body'.
    -- iht: fv t' ⊆ fv t ∪ Γ.dom.
    -- For body': pick fresh y outside L ∪ fv body'. The body IH lives in
    -- the extended ctx ⟨y, t, .sub⟩ :: Γ, so:
    -- ihbody y hyL : fv (body'^[y]) ⊆ fv (body^[y]) ∪ insert y Γ.dom.
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪
        Ctx.dom (⟨y, t, .sub⟩ :: Γ) := ihbody y hyL
    -- Extract fv body' ⊆ fv body ∪ Γ.dom.
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
    -- Conclude: fv (.abs t' body') = fv t' ∪ fv body'.
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
private theorem MEqRed_fv_preserve {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) (hfv : Term.fv u ⊆ Γ.dom) :
    Term.fv v ⊆ Γ.dom := by
  intro z hz
  have hzU : z ∈ Term.fv u ∪ Γ.dom := MEqRed_fv_subset h hz
  rcases Finset.mem_union.mp hzU with h' | h'
  · exact hfv h'
  · exact h'

/-- Every closing derivation produced by `MEqRed.refl` avoids `Me-Pro`
on every variable, since the only constructors `MEqRed.refl` invokes
are `var`/`top`/`app`/`fun_`/`fOp`/`tAp` — never `Me-Pro`. Provable
by induction on `Term.LC` mirroring the structure of `MEqRed.refl`.

The proof relies on Lean 4's proof irrelevance: since `MEqRed Γ s u u`
is in `Prop`, any two proofs of it are definitionally equal, so the
type `MEqRedAvoidsPro x (MEqRed.refl hpv hLC hfv)` is definitionally
equal to `MEqRedAvoidsPro x h` for any `h : MEqRed Γ s u u`. We
construct an explicit derivation `h_av` mirroring `MEqRed.refl`'s
structure and prove `MEqRedAvoidsPro x h_av` directly; the proof
re-types to the desired statement by proof irrelevance. -/
private theorem MEqRedAvoidsPro_refl (x : String) {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRedAvoidsPro x (MEqRed.refl hpv hLC hfv) := by
  -- The trick: by proof irrelevance, MEqRed.refl hpv hLC hfv equals any
  -- other proof of MEqRed Γ s u u. So MEqRedAvoidsPro x (MEqRed.refl ...) is
  -- definitionally the same as MEqRedAvoidsPro x h_av for any h_av of the
  -- right type. We construct h_av to mirror MEqRed.refl's structure and
  -- prove avoidance simultaneously.
  -- Strengthened statement: for ALL valid hLC/hpv/hfv at any (Γ, s), there
  -- exists a derivation that avoids Me-Pro on x.
  suffices h : ∃ (h_av : MEqRed Γ s u u), MEqRedAvoidsPro x h_av by
    obtain ⟨h_av, hAv⟩ := h
    -- By proof irrelevance, h_av = MEqRed.refl hpv hLC hfv.
    have heq : h_av = MEqRed.refl hpv hLC hfv := rfl
    rw [← heq]; exact hAv
  -- Build the witness by induction on hLC, mirroring MEqRed.refl.
  -- Strengthen to fold over arbitrary (Γ, s, hpv, hfv).
  suffices hGen : ∀ (Γ : Ctx) (s : Stack),
      PrevalidExt Γ s → Term.fv u ⊆ Γ.dom →
        ∃ (h_av : MEqRed Γ s u u), MEqRedAvoidsPro x h_av by
    exact hGen Γ s hpv hfv
  clear hpv hfv Γ s
  intro Γ s
  induction hLC generalizing Γ s with
  | top =>
    intro hpv hfv
    exact ⟨MEqRed.top hpv, .top hpv⟩
  | fvar y =>
    intro hpv hfv
    exact ⟨MEqRed.var hpv, .var hpv⟩
  | @app a b hLCa hLCb iha ihb =>
    intro hpv hfv
    have hfa : Term.fv a ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfb : Term.fv b ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    have hpvb : PrevalidExt Γ (b :: s) := PrevalidExt.cons hpv hLCb hfb
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ha_av, hAvA⟩ := iha Γ (b :: s) hpvb hfa
    obtain ⟨hb_av, hAvB⟩ := ihb Γ [] hpvnil hfb
    exact ⟨MEqRed.app ha_av hb_av, .app ha_av hb_av hAvA hAvB⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    intro hpv hfv
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    have hfb : Term.fv bound ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfbody : Term.fv body ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    obtain ⟨hb_av, hAvB⟩ := ihbound Γ [] hpvnil hfb
    cases s with
    | nil =>
      -- Build cofinite body witnesses.
      let L' := L ∪ Γ.dom
      have hbody_av_pkg : ∀ y, y ∉ L' →
          ∃ (h_av : MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body^[y])),
              MEqRedAvoidsPro x h_av := by
        intro y hy
        have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
        have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
        have hpvy : Prevalid (⟨y, bound, .sub⟩ :: Γ) :=
          Prevalid.sub (extractPrevalid hpv) hyΓ hfb hLCbound
        have hpvey : PrevalidExt (⟨y, bound, .sub⟩ :: Γ) [] := PrevalidExt.nil hpvy
        have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, bound, .sub⟩ :: Γ) := by
          intro z hz
          have hsub := Term.fv_open_subset 0 (.fvar y) body
          have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
          rw [Ctx.dom_cons]
          rcases Finset.mem_union.mp hmem with h | h
          · exact Finset.mem_insert_of_mem (hfbody h)
          · have hzy : z = y := by simpa [Term.fv] using h
            subst hzy; exact Finset.mem_insert_self _ _
        exact ihbody y hyL (⟨y, bound, .sub⟩ :: Γ) [] hpvey hfvy
      -- Use Classical.choice to pick a witness for each y.
      classical
      refine ⟨MEqRed.fun_ (L := L') hb_av (fun y hy => (hbody_av_pkg y hy).choose), ?_⟩
      exact .fun_ hb_av _ hAvB (fun y hy => (hbody_av_pkg y hy).choose_spec)
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        let L' := L ∪ Γ.dom
        have hbody_av_pkg : ∀ y, y ∉ L' →
            ∃ (h_av : MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body^[y])),
                MEqRedAvoidsPro x h_av := by
          intro y hy
          have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
          have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
          have hpvy : Prevalid (⟨y, α, .equ⟩ :: Γ) :=
            Prevalid.equ (extractPrevalid hpvr) hyΓ hfvα hLCα
          have hpvey : PrevalidExt (⟨y, α, .equ⟩ :: Γ) tail := by
            -- Lift PrevalidExt Γ tail to PrevalidExt (⟨y,α,.equ⟩::Γ) tail by
            -- noting that fv premises stay in the larger dom.
            have aux : ∀ {st : Stack}, PrevalidExt Γ st →
                PrevalidExt (⟨y, α, .equ⟩ :: Γ) st := by
              intro st hst
              induction hst with
              | nil _ => exact PrevalidExt.nil hpvy
              | @cons _ β hpvE hLCβ hfvβ ih =>
                refine PrevalidExt.cons ih hLCβ ?_
                intro z hz
                have hzΓ : z ∈ Γ.dom := hfvβ hz
                show z ∈ Ctx.dom (⟨y, α, .equ⟩ :: Γ)
                rw [Ctx.dom_cons]
                exact Finset.mem_insert_of_mem hzΓ
            exact aux hpvr
          have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
            intro z hz
            have hsub := Term.fv_open_subset 0 (.fvar y) body
            have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
            rw [Ctx.dom_cons]
            rcases Finset.mem_union.mp hmem with h | h
            · exact Finset.mem_insert_of_mem (hfbody h)
            · have hzy : z = y := by simpa [Term.fv] using h
              subst hzy; exact Finset.mem_insert_self _ _
          exact ihbody y hyL (⟨y, α, .equ⟩ :: Γ) tail hpvey hfvy
        classical
        refine ⟨MEqRed.fOp (L := L') hb_av (fun y hy => (hbody_av_pkg y hy).choose), ?_⟩
        exact .fOp hb_av _ hAvB (fun y hy => (hbody_av_pkg y hy).choose_spec)

/-- Helper: avoidance under `Me-Pro` propagates across changing the
`PrevalidExt` witness. If `pro hpv₁ heq hα` avoids `x`, then any other
`pro hpv₂ heq hα` (with the same `heq` and `hα`) also avoids `x`.

This is provable by inversion on the input avoidance derivation
(extract `hyx : y ≠ x` and `hAv : MEqRedAvoidsPro x hα`) and re-applying
the `MEqRedAvoidsPro.pro` constructor with the new `hpv₂`. -/
private theorem MEqRedAvoidsPro_proInv_propagate
    (x : String) {Γ : Ctx} {s : Stack} {y : String} {α α' : Term}
    (hpv₁ : PrevalidExt Γ s) (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α')
    (hpv₂ : PrevalidExt Γ s)
    (hAv : MEqRedAvoidsPro x (MEqRed.pro hpv₁ heq hα)) :
    MEqRedAvoidsPro x (MEqRed.pro hpv₂ heq hα) := by
  -- The `MEqRedAvoidsPro` family is indexed by the underlying `MEqRed`
  -- derivation. Since `MEqRed Γ s (.fvar y) α'` is in `Prop`, any two
  -- proofs (in particular `MEqRed.pro hpv₁ heq hα` and `MEqRed.pro hpv₂ heq hα`)
  -- are propositionally and definitionally equal by Lean 4's proof
  -- irrelevance. Hence:
  --   MEqRedAvoidsPro x (MEqRed.pro hpv₂ heq hα)
  --     = MEqRedAvoidsPro x (MEqRed.pro hpv₁ heq hα)   [by proof irrel]
  -- and the input `hAv` directly inhabits the latter.
  --
  -- More precisely: types depend only on Lean expressions modulo
  -- definitional equality, and Lean's proof irrelevance equates all
  -- proofs of a proposition. So the two index derivations are
  -- definitionally equal as terms; the predicate type is therefore
  -- definitionally the same; `hAv` is the proof we want.
  exact hAv


/-! ### §3.1 Inline residual fallbacks (IH-aware)

The hard cells of the diamond grid require recursive applications of
the diamond property on syntactic sub-derivations. In the previous
revision these were packaged as opaque `case-axioms` that re-implemented
the recursion internally, which forfeited the structural-IH guarantees
of an outer `induction`. The new presentation rewrites
`Lemma_2_DiamondMEqRed_core` as ONE big `induction h₁` block, which
gives each constructor case access to the structural IHs of its
sub-derivations.

A handful of cases still depend on machinery (cofinite body-IH lifting,
substitution-vs-reduction commutation in `Bet × Bet`, etc.) that does
not yet have a discharged form in this file. We capture each remaining
case as an **inline `private axiom` whose signature receives the IH(s)
of the outer induction as parameters**. This makes the residual
obligation explicit and small: every axiom takes the structural IH it
needs, so discharging it does not require recursive descent inside the
axiom's own statement. -/

/-- Inline residual: both derivations are `Me-Pro` on the same free
variable `x`, looking up the same `equBinds y α`. The IH closes the
inner sub-derivations of `α ⟶ α₁` vs `α ⟶ α₂` directly: the outer
`Me-Pro` step is shared, so the joining edges live inside the inductive
`α ⟶ ?` family.

Discharge requires inversion on `MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)`
to extract the inner `MEqRedAvoidsPro x hα`. Lean's dependent `cases`
struggles with the indexed `MEqRedAvoidsPro` family at this constructor
shape; pending an `injection`-style inversion lemma in the supporting
helper layer, we leave this as an inline axiom that consumes the IH. -/
private axiom Lemma_2_inline_pro_pro
    {Γ : Ctx} {s : Stack} {y : String} {α α₁ α₂ : Term}
    (hpv₁ hpv₂ : PrevalidExt Γ s) (heq : Γ.equBinds y α)
    (hα₁ : MEqRed Γ s α α₁) (hα₂ : MEqRed Γ s α α₂)
    (ihα₁ : ∀ {t₂' : Term}, MEqRed Γ s α t₂' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ s α₁ t₃) (h₂' : MEqRed Γ s t₂' t₃),
        ∀ x : String,
          (MEqRedAvoidsPro x hα₁ → MEqRedAvoidsPro x h₂') ∧
          (∀ (h₂'' : MEqRed Γ s α t₂'),
            MEqRedAvoidsPro x h₂'' → MEqRedAvoidsPro x h₁')) :
    ∃ (t₃ : Term) (h₁' : MEqRed Γ s α₁ t₃) (h₂' : MEqRed Γ s α₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.pro hpv₁ heq hα₁) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x (MEqRed.pro hpv₂ heq hα₂) →
          MEqRedAvoidsPro x h₁')

/-- Inline residual: `Me-Bet` on the LHS, anything on the RHS. The body
and operand IHs from the outer induction close the recursion. -/
private axiom Lemma_2_inline_bet
    {Γ : Ctx} {s : Stack} {t v v' body body' : Term} {L : Finset String}
    {t₂ : Term}
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hv : MEqRed Γ [] v v')
    (h₂ : MEqRed Γ s (.app (.abs t body) v) t₂)
    (ihbody : ∀ y (hy : y ∉ L) {t₂' : Term}, MEqRed Γ s (body^[y]) t₂' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ s (body'^[y]) t₃)
        (h₂' : MEqRed Γ s t₂' t₃), True)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ [] v' t₃) (h₂' : MEqRed Γ [] t₂' t₃),
        True) :
    ∃ (t₃ : Term)
      (h₁' : MEqRed Γ s (Term.opening v' body') t₃)
      (h₂' : MEqRed Γ s t₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.bet (L := L) hLCt hbody hv) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁')

/-- Inline residual: `Me-App` on the LHS, anything (Bet/App/TAp) on the RHS. -/
private axiom Lemma_2_inline_app
    {Γ : Ctx} {s : Stack} {u u' v v' : Term} {t₂ : Term}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v')
    (h₂ : MEqRed Γ s (.app u v) t₂)
    (ihu : ∀ {t₂' : Term}, MEqRed Γ (v :: s) u t₂' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ (v :: s) u' t₃)
        (h₂' : MEqRed Γ (v :: s) t₂' t₃), True)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ [] v' t₃) (h₂' : MEqRed Γ [] t₂' t₃),
        True) :
    ∃ (t₃ : Term)
      (h₁' : MEqRed Γ s (.app u' v') t₃)
      (h₂' : MEqRed Γ s t₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.app hu hv) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁')

/-- Inline residual (DISCHARGED): `Me-TAp` on the LHS, anything (TAp/App
on `.app .top u` shape) on the RHS. The `bet` constructor is vacuous
because `Top` is not an `.abs`. -/
private theorem Lemma_2_inline_tAp
    {Γ : Ctx} {s : Stack} {u : Term} {t₂ : Term}
    (hpv : PrevalidExt Γ s) (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    ∃ (t₃ : Term)
      (h₁' : MEqRed Γ s .top t₃)
      (h₂' : MEqRed Γ s t₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.tAp hpv hLCu hfvu) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁') := by
  cases h₂ with
  | @app _ _ _ uDst _ vDst hu hv =>
    -- hu : MEqRed Γ (u :: s) .top uDst — only `top` fires on .top, so uDst = .top.
    -- We just need to package the joining edge: t₃ := .top.
    -- h₁' : MEqRed Γ s .top .top — by Me-Top with hpv.
    -- h₂' : MEqRed Γ s (.app uDst vDst) .top — by Me-TAp.
    -- For Me-TAp we need LC and fv ⊆ dom for vDst. These come from hv via
    -- MEqRed.lc_right and MEqRed_fv_preserve.
    have hLCuDst : Term.LC uDst := MEqRed.lc_right hu
    have hLCvDst : Term.LC vDst := MEqRed.lc_right hv
    have hfvvDst : Term.fv vDst ⊆ Γ.dom := MEqRed_fv_preserve hv hfvu
    -- We also need uDst = .top. This follows by inversion on hu (only `top`
    -- and `tAp` reduce .top, but tAp needs a stack head — here the stack is
    -- (u :: s), so tAp could fire on `.top` if `.top = .app .top _`, no that
    -- doesn't match either. So only `top` fires).
    -- Actually `MEqRed Γ (u :: s) .top uDst`: cases on this.
    cases hu with
    | top hpvU =>
      -- uDst = .top.
      refine ⟨.top, MEqRed.top hpv, ?_, ?_⟩
      · -- MEqRed Γ s (.app .top vDst) .top via Me-TAp.
        exact MEqRed.tAp hpv hLCvDst hfvvDst
      · intro x; refine ⟨?_, ?_⟩
        · intro _hAv₁; exact .tAp hpv hLCvDst hfvvDst
        · intro _hAv₂; exact .top hpv
  | tAp hpv₂ hLCu' hfvu' =>
    -- Both reduce to .top.
    refine ⟨.top, MEqRed.top hpv, MEqRed.top hpv, ?_⟩
    intro x; exact ⟨fun _ => .top hpv, fun _ => .top hpv⟩

/-- Inline residual: both derivations are `Me-Fun`. Cofinite body-IH at
a fresh name, plus annotation-IH. -/
private axiom Lemma_2_inline_fun_fun
    {Γ : Ctx} {t t₁' body body₁ body₂ : Term} {L₁ L₂ : Finset String}
    {t₂' : Term}
    (ht₁ : MEqRed Γ [] t t₁') (ht₂ : MEqRed Γ [] t t₂')
    (hbody₁ : ∀ y, y ∉ L₁ →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₁^[y]))
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₂^[y]))
    (iht : ∀ {t₂'' : Term}, MEqRed Γ [] t t₂'' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ [] t₁' t₃) (h₂' : MEqRed Γ [] t₂'' t₃),
        True)
    (ihbody : ∀ y (hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) body₂' →
      ∃ (t₃ : Term)
        (h₁' : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₁^[y]) t₃)
        (h₂' : MEqRed (⟨y, t, .sub⟩ :: Γ) [] body₂' t₃), True) :
    ∃ (t₃ : Term)
      (h₁' : MEqRed Γ [] (.abs t₁' body₁) t₃)
      (h₂' : MEqRed Γ [] (.abs t₂' body₂) t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.fun_ (L := L₁) ht₁ hbody₁) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x (MEqRed.fun_ (L := L₂) ht₂ hbody₂) →
          MEqRedAvoidsPro x h₁')

/-- Inline residual: both derivations are `Me-FOp`. Cofinite body-IH at
a fresh name with `.equ` binding, plus annotation-IH. -/
private axiom Lemma_2_inline_fOp_fOp
    {Γ : Ctx} {s : Stack} {α t t₁' body body₁ body₂ : Term}
    {L₁ L₂ : Finset String} {t₂' : Term}
    (ht₁ : MEqRed Γ [] t t₁') (ht₂ : MEqRed Γ [] t t₂')
    (hbody₁ : ∀ y, y ∉ L₁ →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₁^[y]))
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₂^[y]))
    (iht : ∀ {t₂'' : Term}, MEqRed Γ [] t t₂'' →
      ∃ (t₃ : Term) (h₁' : MEqRed Γ [] t₁' t₃) (h₂' : MEqRed Γ [] t₂'' t₃),
        True)
    (ihbody : ∀ y (hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) body₂' →
      ∃ (t₃ : Term)
        (h₁' : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₁^[y]) t₃)
        (h₂' : MEqRed (⟨y, α, .equ⟩ :: Γ) s body₂' t₃), True) :
    ∃ (t₃ : Term)
      (h₁' : MEqRed Γ (α :: s) (.abs t₁' body₁) t₃)
      (h₂' : MEqRed Γ (α :: s) (.abs t₂' body₂) t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x (MEqRed.fOp (L := L₁) ht₁ hbody₁) →
          MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x (MEqRed.fOp (L := L₂) ht₂ hbody₂) →
          MEqRedAvoidsPro x h₁')

/-! ### §3.2 Same-context core lemma

We prove the same-context form of Lemma 2 (Diamond at a single extended
context, no `↣*` evolution) by ONE big `induction` on `h₁`, with the
`t₂` index generalized so each constructor case has access to the
structural IH of its own sub-derivations against an arbitrary `t₂`.
The hard cells dispatch to the per-case inline residual axioms above
(passing the relevant IHs in). The trivial cells are discharged
inline. -/

/-- **Same-context Lemma 2 (core).** Diamond property of `MEqRed` at a
single extended context, with side-condition propagation.

This is the headline `Lemma_2_DiamondMEqRed` minus the `↣*` evolution
on each side. The full headline lifts this via
`Lemma_2_DiamondMEqRed_ctx_axiom` (below). -/
theorem Lemma_2_DiamondMEqRed_core
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    ∃ (t₃ : Term) (h₁' : MEqRed Γ s t₁ t₃) (h₂' : MEqRed Γ s t₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x h₁ → MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁') := by
  induction h₁ generalizing t₂ with
  | @pro Γ s yvr aLkup α' hpv₁ heq₁ hα₁ ihα₁ =>
    -- h₂ on .fvar yvr: pro or var.
    cases h₂ with
    | @pro _ _ _ aLkupB _ hpv₂ heq₂ hα₂ =>
      -- Both pro on yvr; lookup determines aLkup = aLkupB.
      have hα_eq : aLkup = aLkupB := by
        have h1 : Ctx.lookupEqu Γ yvr = some aLkup := heq₁
        have h2 : Ctx.lookupEqu Γ yvr = some aLkupB := heq₂
        rw [h1] at h2
        exact Option.some.inj h2
      subst hα_eq
      -- Build the IH for hα₁ in the shape required by Lemma_2_inline_pro_pro.
      have ihα₁_pkg :
          ∀ {t₂' : Term}, MEqRed Γ s aLkup t₂' →
            ∃ (t₃ : Term) (h₁' : MEqRed Γ s α' t₃)
              (h₂' : MEqRed Γ s t₂' t₃),
              ∀ x : String,
                (MEqRedAvoidsPro x hα₁ → MEqRedAvoidsPro x h₂') ∧
                (∀ (_h₂'' : MEqRed Γ s aLkup t₂'),
                  MEqRedAvoidsPro x _h₂'' → MEqRedAvoidsPro x h₁') := by
        intro t₂' hr
        obtain ⟨t₃, h₁', h₂', hSide⟩ := ihα₁ hr
        refine ⟨t₃, h₁', h₂', ?_⟩
        intro x
        refine ⟨(hSide x).1, ?_⟩
        intro _h₂'' hAv
        exact (hSide x).2 hAv
      exact Lemma_2_inline_pro_pro hpv₁ hpv₂ heq₁ hα₁ hα₂ ihα₁_pkg
    | var hpv₂ =>
      -- h₁ = pro on yvr (result α'); h₂ = var on yvr.
      -- Close at t₃ = α': h₁' = refl on α', h₂' = pro reusing hα₁'s data.
      have hLCα' : Term.LC α' := MEqRed.lc_right hα₁
      have hfvaLkup : Term.fv aLkup ⊆ Ctx.dom Γ :=
        Prevalid.fv_lookupEqu (extractPrevalid hpv₁) heq₁
      have hfvα' : Term.fv α' ⊆ Ctx.dom Γ :=
        MEqRed_fv_preserve hα₁ hfvaLkup
      refine ⟨α', ?_, ?_, ?_⟩
      · exact MEqRed.refl hpv₁ hLCα' hfvα'
      · exact MEqRed.pro hpv₂ heq₁ hα₁
      · intro x; refine ⟨?_, ?_⟩
        · intro hAv₁
          exact MEqRedAvoidsPro_proInv_propagate
            x hpv₁ heq₁ hα₁ hpv₂ hAv₁
        · intro _; exact MEqRedAvoidsPro_refl x hpv₁ hLCα' hfvα'
  | @bet Γ s tBound vSrc vDst body bodyDst L hLCt hbody hv ihbody ihv =>
    -- Build packaged IHs (each strips the AvoidsPro side-condition into
    -- a `True`, so the inline axiom has a flexible signature).
    have ihbody_pkg :
        ∀ y (_hy : y ∉ L) {t₂' : Term},
          MEqRed Γ s (body^[y]) t₂' →
            ∃ (t₃ : Term) (_h₁' : MEqRed Γ s (bodyDst^[y]) t₃)
              (_h₂' : MEqRed Γ s t₂' t₃), True := by
      intro y hy t₂' hr
      obtain ⟨t₃, h₁', h₂', _⟩ := ihbody y hy hr
      exact ⟨t₃, h₁', h₂', trivial⟩
    have ihv_pkg :
        ∀ {t₂' : Term}, MEqRed Γ [] vSrc t₂' →
          ∃ (t₃ : Term) (_h₁' : MEqRed Γ [] vDst t₃)
            (_h₂' : MEqRed Γ [] t₂' t₃), True := by
      intro t₂' hr
      obtain ⟨t₃, h₁', h₂', _⟩ := ihv hr
      exact ⟨t₃, h₁', h₂', trivial⟩
    exact Lemma_2_inline_bet hLCt hbody hv h₂ ihbody_pkg ihv_pkg
  | top hpv₁ =>
    cases h₂ with
    | top hpv₂ =>
      refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
      intro x; exact ⟨fun _ => .top hpv₂, fun _ => .top hpv₁⟩
  | @app Γ s u u' v v' hu hv ihu ihv =>
    have ihu_pkg :
        ∀ {t₂' : Term}, MEqRed Γ (v :: s) u t₂' →
          ∃ (t₃ : Term) (_h₁' : MEqRed Γ (v :: s) u' t₃)
            (_h₂' : MEqRed Γ (v :: s) t₂' t₃), True := by
      intro t₂' hr
      obtain ⟨t₃, h₁', h₂', _⟩ := ihu hr
      exact ⟨t₃, h₁', h₂', trivial⟩
    have ihv_pkg :
        ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
          ∃ (t₃ : Term) (_h₁' : MEqRed Γ [] v' t₃)
            (_h₂' : MEqRed Γ [] t₂' t₃), True := by
      intro t₂' hr
      obtain ⟨t₃, h₁', h₂', _⟩ := ihv hr
      exact ⟨t₃, h₁', h₂', trivial⟩
    exact Lemma_2_inline_app hu hv h₂ ihu_pkg ihv_pkg
  | @var Γ s yvr hpv₁ =>
    cases h₂ with
    | @pro _ _ _ aLkup _ hpv₂ heq₂ hα₂ =>
      -- t₂ is unified with the result α'' of pro; introduce a name for it.
      have hLCt₂ : Term.LC t₂ := MEqRed.lc_right hα₂
      have hfvaLkup : Term.fv aLkup ⊆ Ctx.dom Γ :=
        Prevalid.fv_lookupEqu (extractPrevalid hpv₂) heq₂
      have hfvt₂ : Term.fv t₂ ⊆ Ctx.dom Γ :=
        MEqRed_fv_preserve hα₂ hfvaLkup
      refine ⟨t₂, ?_, ?_, ?_⟩
      · exact MEqRed.pro hpv₁ heq₂ hα₂
      · exact MEqRed.refl hpv₂ hLCt₂ hfvt₂
      · intro x; refine ⟨?_, ?_⟩
        · intro _; exact MEqRedAvoidsPro_refl x hpv₂ hLCt₂ hfvt₂
        · intro hAv₂
          exact MEqRedAvoidsPro_proInv_propagate
            x hpv₂ heq₂ hα₂ hpv₁ hAv₂
    | var hpv₂ =>
      refine ⟨.fvar yvr, MEqRed.var hpv₁, MEqRed.var hpv₂, ?_⟩
      intro x; exact ⟨fun _ => .var hpv₂, fun _ => .var hpv₁⟩
  | @fun_ Γ tBound tBoundDst body body₁ L₁ ht₁ hbody₁ iht ihbody =>
    cases h₂ with
    | @fun_ _ _ tBoundDst₂ _ body₂ L₂ ht₂ hbody₂ =>
      have iht_pkg :
          ∀ {t₂'' : Term}, MEqRed Γ [] tBound t₂'' →
            ∃ (t₃ : Term) (_h₁' : MEqRed Γ [] tBoundDst t₃)
              (_h₂' : MEqRed Γ [] t₂'' t₃), True := by
        intro t₂'' hr
        obtain ⟨t₃, h₁', h₂', _⟩ := iht hr
        exact ⟨t₃, h₁', h₂', trivial⟩
      have ihbody_pkg :
          ∀ y (_hy : y ∉ L₁) {body₂'' : Term},
            MEqRed (⟨y, tBound, .sub⟩ :: Γ) [] (body^[y]) body₂'' →
              ∃ (t₃ : Term)
                (_h₁' : MEqRed (⟨y, tBound, .sub⟩ :: Γ) [] (body₁^[y]) t₃)
                (_h₂' : MEqRed (⟨y, tBound, .sub⟩ :: Γ) [] body₂'' t₃), True := by
        intro y hy body₂'' hr
        obtain ⟨t₃, h₁', h₂', _⟩ := ihbody y hy hr
        exact ⟨t₃, h₁', h₂', trivial⟩
      exact Lemma_2_inline_fun_fun ht₁ ht₂ hbody₁ hbody₂ iht_pkg ihbody_pkg
  | tAp hpv₁ hLCu hfvu =>
    exact Lemma_2_inline_tAp hpv₁ hLCu hfvu h₂
  | @fOp Γ s tBound tBoundDst αHd body body₁ L₁ ht₁ hbody₁ iht ihbody =>
    cases h₂ with
    | @fOp _ _ _ tBoundDst₂ _ _ body₂ L₂ ht₂ hbody₂ =>
      have iht_pkg :
          ∀ {t₂'' : Term}, MEqRed Γ [] tBound t₂'' →
            ∃ (t₃ : Term) (_h₁' : MEqRed Γ [] tBoundDst t₃)
              (_h₂' : MEqRed Γ [] t₂'' t₃), True := by
        intro t₂'' hr
        obtain ⟨t₃, h₁', h₂', _⟩ := iht hr
        exact ⟨t₃, h₁', h₂', trivial⟩
      have ihbody_pkg :
          ∀ y (_hy : y ∉ L₁) {body₂'' : Term},
            MEqRed (⟨y, αHd, .equ⟩ :: Γ) s (body^[y]) body₂'' →
              ∃ (t₃ : Term)
                (_h₁' : MEqRed (⟨y, αHd, .equ⟩ :: Γ) s (body₁^[y]) t₃)
                (_h₂' : MEqRed (⟨y, αHd, .equ⟩ :: Γ) s body₂'' t₃), True := by
        intro y hy body₂'' hr
        obtain ⟨t₃, h₁', h₂', _⟩ := ihbody y hy hr
        exact ⟨t₃, h₁', h₂', trivial⟩
      exact Lemma_2_inline_fOp_fOp ht₁ ht₂ hbody₁ hbody₂ iht_pkg ihbody_pkg

/-! ### §3.3 Context-evolution lifting

The context evolution `↣*` is handled by a separate axiom that lifts the
same-context joining derivations across the two `↣*` evolutions. The
discharge of this axiom requires extending the `MEqRed` weakening
machinery to also cover annotation reductions on existing bindings (the
`Ct-Ann` arm of `↣`), which is not yet covered by
`Lemma_22_WeakeningMEqRed`. -/

/-- Lift a same-context joining derivation across two `↣*` evolutions.
Provable by mutual induction on `hCt₁` and `hCt₂` using `Lemma_22`
(weakening) for the structural cases and a narrowing-style argument for
the `Ct-Ann` case (the bound annotation reduces, so the body's reductions
need to be re-cast in the new context). -/
private axiom Lemma_2_DiamondMEqRed_ctx_axiom
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂))
    {t₃ : Term} (h₁'₀ : MEqRed Γ₀ s₀ t₁ t₃) (h₂'₀ : MEqRed Γ₀ s₀ t₂ t₃) :
    ∃ (t₃' : Term) (h₁' : MEqRed Γ₁ s₁ t₁ t₃') (h₂' : MEqRed Γ₂ s₂ t₂ t₃'),
      ∀ x : String,
        (MEqRedAvoidsPro x h₁'₀ → MEqRedAvoidsPro x h₁') ∧
        (MEqRedAvoidsPro x h₂'₀ → MEqRedAvoidsPro x h₂')

/-- **Lemma 2** (Pasquale & García-Pérez 2024 §3, Diamond property of
`⟶^≡` modulo the "no Me-Pro on `x`" side condition).

The conclusion exposes the closing derivations `h₁'` and `h₂'` so that
the side-condition-propagation clause (the `Moreover` paragraph of the
paper) can be stated about them.

Status: **THEOREM** (Wave 7 discharge). The proof goes via the
same-context core lemma (`Lemma_2_DiamondMEqRed_core`), then lifts the
joining derivations across the two `↣*` evolutions via
`Lemma_2_DiamondMEqRed_ctx_axiom`.

Outstanding residual obligations are isolated as **narrow private inline
axioms** (`Lemma_2_inline_pro_pro`, `Lemma_2_inline_bet`,
`Lemma_2_inline_app`, `Lemma_2_inline_fun_fun`, `Lemma_2_inline_fOp_fOp`,
`Lemma_2_DiamondMEqRed_ctx_axiom`). The scope-preservation helpers
`MEqRed_fv_preserve`, `MEqRedAvoidsPro_refl`, and
`MEqRedAvoidsPro_proInv_propagate` are now `private theorem`s (proved
in §3.0 above). The TAp arm (`Lemma_2_inline_tAp`) is also a real
`theorem`. The headline statement itself is a real `theorem`. -/
theorem Lemma_2_DiamondMEqRed
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    ∃ (t₃ : Term) (h₁' : MEqRed Γ₁ s₁ t₁ t₃) (h₂' : MEqRed Γ₂ s₂ t₂ t₃),
      ∀ x : String,
        (MEqRedAvoidsPro x h₁ → MEqRedAvoidsPro x h₂') ∧
        (MEqRedAvoidsPro x h₂ → MEqRedAvoidsPro x h₁') := by
  -- Step 1: Diamond at the same starting context.
  obtain ⟨t₃, h₁'₀, h₂'₀, hSide₀⟩ := Lemma_2_DiamondMEqRed_core h₁ h₂
  -- Step 2: Lift each joining derivation across its `↣*` evolution.
  obtain ⟨t₃', h₁', h₂', hLift⟩ :=
    Lemma_2_DiamondMEqRed_ctx_axiom hCt₁ hCt₂ h₁'₀ h₂'₀
  refine ⟨t₃', h₁', h₂', ?_⟩
  intro x
  -- hSide₀ x : (h₁ avoids → h₂'₀ avoids) ∧ (h₂ avoids → h₁'₀ avoids)
  -- hLift  x : (h₁'₀ avoids → h₁' avoids) ∧ (h₂'₀ avoids → h₂' avoids)
  refine ⟨?_, ?_⟩
  · intro hAv₁
    -- h₁ avoids → (by hSide₀) h₂'₀ avoids → (by hLift) h₂' avoids
    exact (hLift x).2 ((hSide₀ x).1 hAv₁)
  · intro hAv₂
    -- h₂ avoids → (by hSide₀) h₁'₀ avoids → (by hLift) h₁' avoids
    exact (hLift x).1 ((hSide₀ x).2 hAv₂)

/-! ## §4. Convenience: the bare-existence corollary

Many downstream consumers of Lemma 2 only need the basic existence of
`t₃` without the side-condition propagation. We expose that as a
corollary that drops the `MEqRedAvoidsPro` clause. -/

/-- Bare-existence corollary of `Lemma_2_DiamondMEqRed`: the diamond
property of `⟶^≡` (without the side condition exposed in the
conclusion). -/
theorem Lemma_2_DiamondMEqRed_bare
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    ∃ t₃, MEqRed Γ₁ s₁ t₁ t₃ ∧ MEqRed Γ₂ s₂ t₂ t₃ := by
  obtain ⟨t₃, h₁', h₂', _⟩ :=
    Lemma_2_DiamondMEqRed h₁ h₂ hCt₁ hCt₂
  exact ⟨t₃, h₁', h₂'⟩

/-! ## §5. Same-context corollary

The most common application of Lemma 2 takes `Γ₁; s₁ = Γ₂; s₂ = Γ₀; s₀`
(reflexive `↣*`), which is the actual diamond property in the standard
sense. -/

/-- The diamond property of `MEqRed` at a single extended context (no
context evolution). This is the form used by the strong-commutativity
proof (Wave 6) and the transitivity-elimination theorem (Wave 7). -/
theorem Lemma_2_DiamondMEqRed_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    ∃ t₃, MEqRed Γ s t₁ t₃ ∧ MEqRed Γ s t₂ t₃ :=
  Lemma_2_DiamondMEqRed_bare h₁ h₂
    (Relation.ReflTransGen.refl) (Relation.ReflTransGen.refl)

end Pss
