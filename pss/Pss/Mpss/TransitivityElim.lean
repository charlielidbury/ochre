import Pss.Mpss.Commutation
import Pss.Mpss.Diamond
import Pss.Mpss.WellFormed

set_option linter.unusedVariables false

/-! # `Pss.Mpss.TransitivityElim` — Theorem 3 (Transitivity is admissible)

Pasquale & García-Pérez 2024 (CSL 2026), §3 (statement on p. 9, proof
sketch on p. 25). The headline transitivity-elimination theorem of MPSS:
the closure under transitive composition `≤*` of the diagrammatic
subtyping relation `≤` is admissible — every `Γ; s ⊢ u ≤* v` derivation
collapses to a single `Γ; s ⊢ u ≤ v`.

## Definition shapes

The paper writes the diagrammatic subtyping relation `Γ; s ⊢ u ≤ v` as

```
                     ≡
                t        v
                         ≤
                ≤
                u
```

i.e. there exists `w` such that `Γ; s ⊢ u ⟶^≤* w` and `Γ; s ⊢ v ⟶^≡* w`.
We follow this definition exactly with `MSub`. The transitive closure
`≤*` is `MSubStar`, an instance of `Relation.ReflTransGen`.

## Proof outline of Theorem 3

The proof is a standard "lift diamond from steps to stars" exercise on
`MEqRed`/`MSubRed`, plus a `Relation.ReflTransGen` induction on the
`MSubStar` chain. The "lift" goes:

* `diamond_step_eqStar` — single `MEqRed` step closes against an
  `MEqRedStar` chain. By `head_induction_on` on the chain, applying
  single-step Lemma 2 at each head.
* `diamond_eqStar_eqStar` — two `MEqRedStar` chains close to a (star,star)
  square. By `head_induction_on` on the first chain, applying
  `diamond_step_eqStar` at each head.

A symmetric pair lifts strong commutativity (Lemma 1) from
single-`MSubRed` to `MSubRedStar`. Then Theorem 3 is a
`Relation.ReflTransGen` induction over `MSubStar`.

## Status

PROVED. No new axioms introduced. Reduces to the upstream
`Lemma_1_StrongCommutativity` and `Lemma_2_DiamondMEqRed` axioms.
-/

namespace Pss

/-! ## §1. The diagrammatic `≤` relation and its transitive closure -/

/-- **Definition of `≤` (paper §2).** `Γ; s ⊢ u ≤ v` iff there exists a
common reduct `w` such that `Γ; s ⊢ u ⟶^≤* w` and `Γ; s ⊢ v ⟶^≡* w`. -/
def MSub (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  ∃ w, MSubRedStar Γ s u w ∧ MEqRedStar Γ s v w

/-- The transitive closure `≤*` of `≤`. -/
abbrev MSubStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MSub Γ s)

/-! ## §2. Single-step lifters -/

/-- Lift a single `MEqRed` to `MEqRedStar` (via `MEqRedJ` wrap). -/
theorem MEqRedStar.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : MEqRedStar Γ s u v :=
  Relation.ReflTransGen.single ⟨h⟩

/-- Lift a single `MSubRed` to `MSubRedStar` (via `MSubRedJ` wrap). -/
theorem MSubRedStar.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : MSubRedStar Γ s u v :=
  Relation.ReflTransGen.single ⟨h⟩

/-- Lift a single `MEqRedJ` to `MEqRedStar`. -/
theorem MEqRedStar.singleJ {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) : MEqRedStar Γ s u v :=
  Relation.ReflTransGen.single h

/-- Lift a single `MSubRedJ` to `MSubRedStar`. -/
theorem MSubRedStar.singleJ {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) : MSubRedStar Γ s u v :=
  Relation.ReflTransGen.single h

/-! ## §3. Diamond of `MEqRedStar` (lifted from Lemma 2)

Standard "diamond ⇒ confluence on stars". Two helpers, each by
`head_induction_on` on a single chain. -/

/-- Step-vs-star diamond. By `head_induction_on` on the star chain.
At each head step of the chain, apply single-step Lemma 2 to combine
the input step with the head step.

The `hHead` provided by `head_induction_on` is `MEqRedJ` (Prop-wrapped)
since the chain is `ReflTransGen MEqRedJ`; we extract the underlying
Type-valued derivation via `.some` (uses `Classical.choice`). -/
theorem diamond_step_eqStar
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  -- Strengthen to a ∀-quantified version, then induct on h₂.
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₂),
      ∀ {x : Term}, MEqRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MEqRedStar Γ s t₂ t₃ from
    key h₂ h₁
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₂)
    (P := fun a (_ : MEqRedStar Γ s a t₂) =>
      ∀ {x : Term}, MEqRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MEqRedStar Γ s t₂ t₃) h ?_ ?_
  · -- refl case: a = t₂. Given input : MEqRed Γ s t₂ x, take t₃ = x.
    intro x hstep
    exact ⟨x, Relation.ReflTransGen.refl, MEqRedStar.single hstep⟩
  · -- head case: hHead : MEqRedJ a c; hTailStar : c →* t₂; ihC at c.
    intro a c hHead hTailStar ihC x hInput
    obtain ⟨y, hcy, hxy⟩ :=
      Lemma_2_DiamondMEqRed_sameCtx (h₁ := hHead.some) (h₂ := hInput)
    -- hcy : MEqRed Γ s c y; hxy : MEqRed Γ s x y.
    obtain ⟨t₃, hyT₃, hT₂T₃⟩ := ihC hcy
    refine ⟨t₃, ?_, hT₂T₃⟩
    exact Relation.ReflTransGen.head ⟨hxy⟩ hyT₃

/-- Star-vs-star diamond on `MEqRedStar`. By `head_induction_on` on the
first chain, applying `diamond_step_eqStar` at each head step. -/
theorem diamond_eqStar_eqStar
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRedStar Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₁),
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s z t₃ from
    key h₁ h₂
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₁)
    (P := fun a (_ : MEqRedStar Γ s a t₁) =>
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s z t₃) h ?_ ?_
  · -- refl case: a = t₁. Given any star : t₁ →* z, close trivially.
    intro z hStar
    exact ⟨z, hStar, Relation.ReflTransGen.refl⟩
  · -- head case: hHead : MEqRedJ a c (Prop wrap of MEqRed).
    intro a c hHead hTailStar ihC z hInputStar
    obtain ⟨y, hcy, hzy⟩ := diamond_step_eqStar hHead.some hInputStar
    obtain ⟨t₃, hT₁T₃, hyT₃⟩ := ihC hcy
    refine ⟨t₃, hT₁T₃, ?_⟩
    exact Relation.ReflTransGen.trans hzy hyT₃

/-! ## §4. Strong commutativity lifted from Lemma 1

Symmetric three-stage lift, covering single `MSubRed` × `MEqRedStar`,
then `MSubRedStar` × single `MEqRed`, and finally
`MSubRedStar` × `MEqRedStar`. -/

/-- Strong commutativity at (single MSubRed, MEqRedStar). By
`head_induction_on` on the equiv chain, applying single-step Lemma 1 at
each head step.

The closing right edge is now wrapped in `MSubRedJ` (Nonempty) since
`MSubRed` is `Type`-valued and we keep the Prop conclusion with `∃/∧`. -/
theorem commute_subStep_eqStar
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₂),
      ∀ {x : Term}, MSubRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MSubRedJ Γ s t₂ t₃ from
    key heqs hsub
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₂)
    (P := fun a (_ : MEqRedStar Γ s a t₂) =>
      ∀ {x : Term}, MSubRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MSubRedJ Γ s t₂ t₃) h ?_ ?_
  · -- refl: a = t₂. Given input : MSubRed Γ s t₂ x, take t₃ = x.
    intro x hsub
    exact ⟨x, Relation.ReflTransGen.refl, ⟨hsub⟩⟩
  · -- head: hHead : MEqRedJ Γ s a c, ihC at c.
    intro a c hHead hTailStar ihC x hInput
    obtain ⟨y, hxy, hcy⟩ :=
      Lemma_1_StrongCommutativity_sameCtx hInput hHead.some
    obtain ⟨t₃, hyT₃, hT₂T₃⟩ := ihC hcy
    refine ⟨t₃, ?_, hT₂T₃⟩
    exact Relation.ReflTransGen.head ⟨hxy⟩ hyT₃

/-- Strong commutativity at (single MSubRed, MEqRedStar) — variant returning
a closing edge that is itself a single MSubRed step on the right. The
lift produces an MSubRedStar on the right by chaining IH instances. We
need the version that gives a closing MSubRedStar. -/
theorem commute_subStep_eqStar_star
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  obtain ⟨t₃, h1, h2⟩ := commute_subStep_eqStar hsub heqs
  exact ⟨t₃, h1, MSubRedStar.singleJ h2⟩

/-- Strong commutativity at (MSubRedStar, MEqRedStar). By
`head_induction_on` on the sub chain, applying `commute_subStep_eqStar`
at each head step. -/
theorem commute_subStar_eqStar
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsubs : MSubRedStar Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MSubRedStar Γ s a t₁),
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s z t₃ from
    key hsubs heqs
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₁)
    (P := fun a (_ : MSubRedStar Γ s a t₁) =>
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s z t₃) h ?_ ?_
  · -- refl: a = t₁. Given heqs : MEqRedStar Γ s t₁ z, close with t₃ = z.
    intro z heqs
    exact ⟨z, heqs, Relation.ReflTransGen.refl⟩
  · -- head: hHead : MSubRedJ a c, hTailStar : c →* t₁, ihC at c.
    intro a c hHead hTailStar ihC z hEqStar
    obtain ⟨y, hcy, hzy⟩ := commute_subStep_eqStar_star hHead.some hEqStar
    obtain ⟨t₃, hT₁T₃, hyT₃⟩ := ihC hcy
    refine ⟨t₃, hT₁T₃, ?_⟩
    exact Relation.ReflTransGen.trans hzy hyT₃

/-! ## §5. Theorem 3 — transitivity is admissible -/

/-- Reflexivity of `MSub`: every `t` is a `MSub`-self at any prevalid
extended context with `t` LC-and-in-scope. -/
theorem MSub.refl
    {Γ : Ctx} {s : Stack} {t : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC t) (hfv : Term.fv t ⊆ Γ.dom) :
    MSub Γ s t t :=
  ⟨t,
    MSubRedStar.single (Proposition_18_ReflexivityMSubRed hpv hLC hfv),
    MEqRedStar.single (Proposition_18_ReflexivityMEqRed hpv hLC hfv)⟩

/-- Bare reflexivity of `MSub` from `MSubRed` reflexivity: take both
chains as `refl`. -/
theorem MSub.refl_simple {Γ : Ctx} {s : Stack} {t : Term} :
    MSub Γ s t t :=
  ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- Single-step composition for `MSub`: from `MSub Γ s t u` and
`MSub Γ s u v`, obtain `MSub Γ s t v`. The proof uses the diamond +
strong commutativity lifts. -/
theorem MSub.trans_step
    {Γ : Ctx} {s : Stack} {t u v : Term}
    (htu : MSub Γ s t u) (huv : MSub Γ s u v) :
    MSub Γ s t v := by
  obtain ⟨w₁, ht_w₁, hu_w₁⟩ := htu
  obtain ⟨w₂, hu_w₂, hv_w₂⟩ := huv
  -- ht_w₁ : MSubRedStar Γ s t w₁
  -- hu_w₁ : MEqRedStar Γ s u w₁
  -- hu_w₂ : MSubRedStar Γ s u w₂
  -- hv_w₂ : MEqRedStar Γ s v w₂
  -- Step 1: apply commute_subStar_eqStar at u between (hu_w₂ : sub*) and
  -- (hu_w₁ : eq*), getting common closing point z₁ with
  --   MEqRedStar Γ s w₂ z₁  and  MSubRedStar Γ s w₁ z₁.
  obtain ⟨z₁, hw₂_z₁, hw₁_z₁⟩ := commute_subStar_eqStar hu_w₂ hu_w₁
  -- Step 2: stitch ht_w₁ : t →^≤* w₁ with hw₁_z₁ : w₁ →^≤* z₁ to get
  --   t →^≤* z₁.
  have ht_z₁ : MSubRedStar Γ s t z₁ :=
    Relation.ReflTransGen.trans ht_w₁ hw₁_z₁
  -- Step 3: stitch hv_w₂ : v →^≡* w₂ with hw₂_z₁ : w₂ →^≡* z₁ to get
  --   v →^≡* z₁.
  have hv_z₁ : MEqRedStar Γ s v z₁ :=
    Relation.ReflTransGen.trans hv_w₂ hw₂_z₁
  -- Done.
  exact ⟨z₁, ht_z₁, hv_z₁⟩

/-- **Theorem 3 (Pasquale & García-Pérez 2024 §3, Transitivity Admissibility).**

If `Γ; s ⊢ u ≤* v`, then `Γ; s ⊢ u ≤ v`. Follows from Lemma 1 (strong
commutativity) and Lemma 2 (diamond) by induction on the `MSubStar` chain.

Proved (paper-faithful) using the `commute_subStar_eqStar` lift of
Lemma 1 to `*`-chains. -/
theorem Theorem_3_TransitivityIsAdmissible
    {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubStar Γ s u v) :
    MSub Γ s u v := by
  induction h with
  | refl => exact MSub.refl_simple
  | @tail u' v hStar hStep ih =>
    -- ih : MSub Γ s u u'; hStep : MSub Γ s u' v.
    exact MSub.trans_step ih hStep

end Pss
