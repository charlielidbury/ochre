import Pss.Mpss.DeBruijnTransitivityElim
import Pss.Mpss.DeBruijnOperationalSem
import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Aux.Propositions` — paper Theorem 11 + Propositions 12–14, 17–18 + Lemmas 15–16

Mechanizes the "small-Propositions batch" from Pasquale & García-Pérez
2024:

* **Theorem 11** (No supertype of `Top` is a function, p. 9:31) —
  diagrammatic-subtyping consequence: at any logical context, `Top` has
  no abstraction supertype under transitive well-subtyping.
* **Proposition 12** (Well-formedness extraction, p. 9:32) — both
  endpoints of a transitive well-subtyping derivation are well-formed.
* **Proposition 13** (From well-subtyping to subtyping, p. 9:32) — one
  well-subtyping derivation strips to one diagrammatic subtyping witness
  at the empty stack.
* **Proposition 14** (From well-equivalence to equivalence, p. 9:32) —
  mirror of Proposition 13 on the equivalence side.
* **Lemma 15** (Symmetry of `≡_wf`, p. 9:33) — well-equivalence is
  symmetric.
* **Lemma 16** (`≡_wf` ⊆ `≤_wf`, p. 9:33) — well-equivalence embeds into
  well-subtyping.
* **Proposition 17** (From reduction semantics to equivalence reduction,
  p. 9:33) — operational small-step reduction embeds into MPSS
  equivalence reduction at any prevalid extended context. Unconditional
  in de Bruijn (the LN axiom `Proposition_17_beta_axiom` is retired).
* **Proposition 18** (Reflexivity of equivalence reduction, p. 9:33) —
  `→ᵉᵠᵘ` and `→ˢᵘᵇ` are reflexive on well-formed terms at any prevalid
  extended context.

## De Bruijn translation

The paper writes `Γ ⊢ u wf` for well-formedness; in de Bruijn the
codebase carries this as `WfM Γ u`. The paper's free-variable scoping
conditions become de Bruijn `Term.Scoped` conditions tracked by the
context's `depth`. The paper's stacks `s` carry a `PrevalidExt Γ s`
witness in the de Bruijn working development (paper handwaves this as
"`Γ; s` is an extended context").

For Proposition 17 the paper says "for all extended context `Γ; s`"; in
de Bruijn the concrete statement is parameterised over `(hdepth :
Γ.depth = depth)` and `(hpv : PrevalidExt Γ s)` — the depth alignment is
needed because `StepAt` is depth-indexed. The empty-context closed
specialisation `MEqRed.of_Step` covers the paper's standalone use.

Theorem 11's paper proof flattens transitive subtyping via Theorem 3
(transitivity elimination) and then performs `Top`-inversion on the
diagrammatic chain. The de Bruijn discharge follows the same shape, with
`StrongCommutes` standing in for the conditional Theorem 3 use-site (so
the named entry `Theorem_11_NoTopAbstractionSupertypes_of` is conditional
on the transitivity-elimination residual `StrongCommutes`).

## Existing codebase counterparts (reused, not re-proved)

* **Theorem 11**: `NoTopAbstractionSupertypesAt_of` and
  `NoTopFunctionSupertypesAt_of` in
  `Pss/Mpss/DeBruijnTypeSafety.lean:41,61`.
* **Proposition 12**: `WSubMStar.wf_left`, `WSubMStar.wf_right`,
  `WSubMStar.wf_pair` at `Pss/Mpss/DeBruijnWellFormed.lean:441,461,481`.
* **Proposition 13**: `WSubM.toMSub` at
  `Pss/Mpss/DeBruijnTransitivityElim.lean:17703`.
* **Proposition 14**: `WEquM.toMSub` at
  `Pss/Mpss/DeBruijnTransitivityElim.lean:17781`.
* **Lemma 15**: `WEquM.symm` at
  `Pss/Mpss/DeBruijnWellFormed.lean:2187`. (`WEquMStar.symm` at line
  5627 for the chain version.)
* **Lemma 16**: `WEquM.toWSubM` at
  `Pss/Mpss/DeBruijnWellFormed.lean:2198`.
* **Proposition 17**: `MEqRed.of_StepAt` at
  `Pss/Mpss/DeBruijnOperationalSem.lean:116`.
* **Proposition 18**: `MEqRed.refl` and `MSubRed.refl` at
  `Pss/Mpss/DeBruijnReductions.lean:5675,5713`.
-/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Theorem 11 (No supertype of `Top` is a function), paper p. 9:31 -/

/-- **Theorem 11 (No supertype of `Top` is a function), paper p. 9:31.**

> *Statement.* Let `Γ; s` be an extended context. Let `λx ≤ t.u` be a
> term. We cannot have `Γ; s ⊢ Top ≤∗ λx ≤ t.u`.
>
> *Proof.* By Theorem 3 (transitivity elimination) the chain flattens
> to `Top ≤ λx ≤ t.u`, i.e. there exists `w` such that
> `Top →∗ˢᵘᵇ w` and `λx ≤ t.u →∗ᵉᵠᵘ w`. Only `Ms-Equ` and `Ms-Top`
> apply to `Top` so `w = Top`. Only `Me-Fun` or `Me-FOp` apply to
> `λx ≤ t.u` so `w` is an abstraction — contradicting `w = Top`.

The de Bruijn statement is the context-generic form: at any context
`Γ`, transitive well-subtyping `Top ≤∗_wf λx ≤ t.body` is impossible.
This is the shape progress and β-preservation actually consume.

Because the paper's proof flattens through Theorem 3, the de Bruijn
statement is conditional on `StrongCommutes Γ []` at every context (the
de Bruijn analogue of Theorem 3 at the empty stack). -/
noncomputable def Theorem_11_NoTopAbstractionSupertypes_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopAbstractionSupertypesAt :=
  NoTopAbstractionSupertypesAt_of hcomm

/-- **Theorem 11 (function-supertype specialization), paper p. 9:31.**

The function-bound specialization of Theorem 11: at any context, `Top`
has no abstraction supertype with `Top` body. This is the closed-shape
progress consumes when ruling out `Top` as a function. -/
noncomputable def Theorem_11_NoTopFunctionSupertypes_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopFunctionSupertypesAt :=
  NoTopFunctionSupertypesAt_of hcomm

/-- **Theorem 11 (closed shape), paper p. 9:31.**

Empty-context specialisation: at the empty context, transitive
well-subtyping `Top ≤∗_wf λx ≤ t.Top` is impossible. Conditional on
`StrongCommutes [] []` only. -/
noncomputable def Theorem_11_NoTopFunctionSupertypes_closed_of
    (hcomm : StrongCommutes [] []) :
    NoTopFunctionSupertypes :=
  NoTopFunctionSupertypes_of hcomm

/-! ## Proposition 12 (Well-formedness extraction), paper p. 9:32 -/

/-- **Proposition 12 (Well-formedness extraction), paper p. 9:32.**

> *Statement.* Let `Γ` be an extended context and `u, v` be terms. If
> `Γ ⊢ u ≤∗_wf v` then both derivations `Γ ⊢ u wf` and `Γ ⊢ v wf` exist
> in the derivation tree of `Γ ⊢ u ≤∗_wf v`.
>
> *Proof.* By induction on the `≤∗_wf` derivation. `Ws-Sub` carries the
> two `wf` premises directly; `Ws-Trs` extracts via the IHs.

In de Bruijn the two endpoints split into separate extractors because
the paper's "both" is a Type-valued conjunction. We expose `_left`,
`_right`, and `_pair` as named entry points. -/
noncomputable def Proposition_12_WfMExtraction_left
    {Γ : Ctx} {u v : Term} (h : WSubMStar Γ u v) : WfM Γ u :=
  h.wf_left

/-- **Proposition 12 (right endpoint), paper p. 9:32.** Mirror extractor
on the right endpoint. -/
noncomputable def Proposition_12_WfMExtraction_right
    {Γ : Ctx} {u v : Term} (h : WSubMStar Γ u v) : WfM Γ v :=
  h.wf_right

/-- **Proposition 12 (paired form), paper p. 9:32.** Both endpoints
together as a Type-valued pair, matching the paper's "both derivations
exist in the derivation tree" statement. -/
noncomputable def Proposition_12_WfMExtraction
    {Γ : Ctx} {u v : Term} (h : WSubMStar Γ u v) : WfM Γ u × WfM Γ v :=
  h.wf_pair

/-! ## Proposition 13 (From well-subtyping to subtyping), paper p. 9:32 -/

/-- **Proposition 13 (From well-subtyping to subtyping), paper p. 9:32.**

> *Statement.* Let `Γ` be a logical context and `u, v` be terms. If
> `Γ ⊢ u ≤_wf v` then `Γ; nil ⊢ u ≤ v`.
>
> *Proof.* By induction on `Γ ⊢ u ≤_wf v` by last rule (`Ws-Rfl`,
> `Ws-Lf1`, `Ws-Lf2`, `Ws-Rgh`). `Ws-Rfl` produces a reflexive
> diagrammatic chain via `MSub.refl`; `Ws-Lf1`/`Ws-Lf2`/`Ws-Rgh` extend
> the IH's diagrammatic witness with one extra step.

In de Bruijn the codebase carries the proof as `WSubM.toMSub`. The
empty stack `nil` of the paper is the empty list `[]` in the de Bruijn
encoding. -/
noncomputable def Proposition_13_FromWellSubtypingToSubtyping
    {Γ : Ctx} {u v : Term} (h : WSubM Γ u v) : MSub Γ [] u v :=
  h.toMSub

/-- **Proposition 13 (chain version), paper p. 9:32.** Star-closure
variant: a transitive well-subtyping chain strips to a transitive
diagrammatic subtyping chain. -/
noncomputable def Proposition_13_FromWellSubtypingToSubtyping_star
    {Γ : Ctx} {u v : Term} (h : WSubMStar Γ u v) : MSubStar Γ [] u v :=
  h.toMSubStar

/-! ## Proposition 14 (From well-equivalence to equivalence), paper p. 9:32 -/

/-- **Proposition 14 (From well-equivalence to equivalence), paper p. 9:32.**

> *Statement.* If `Γ ⊢ u ≡_wf v` then `Γ; nil ⊢ u ≡ v`.
>
> *Proof.* Mirror of Proposition 13.

In de Bruijn, well-equivalence-to-MSub factors through Lemma 16
(`WEquM.toWSubM`) followed by Proposition 13 (`WSubM.toMSub`). The
existing `WEquM.toMSub` is exactly that composition. -/
noncomputable def Proposition_14_FromWellEquivalenceToEquivalence
    {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) : MSub Γ [] u v :=
  h.toMSub

/-- **Proposition 14 (chain version), paper p. 9:32.** Star-closure
variant. -/
noncomputable def Proposition_14_FromWellEquivalenceToEquivalence_star
    {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) : MSubStar Γ [] u v :=
  h.toMSubStar

/-! ## Lemma 15 (Symmetry of `≡_wf`), paper p. 9:33 -/

/-- **Lemma 15 (Symmetry of `≡_wf`), paper p. 9:33.**

> *Statement.* If `Γ ⊢ u ≡_wf v` then `Γ ⊢ v ≡_wf u`.
>
> *Proof.* By induction on `Γ ⊢ u ≡_wf v` by last rule. `Ws-Rfl` is
> immediate; `Ws-Lf1` becomes `Ws-Rgh` and vice versa.

In de Bruijn the codebase ships `WEquM.symm` as a direct induction. The
paper's "by construction" symmetry intuition (audit note) is realized
as a 5-line inductive proof: `Ws-Rfl ↔ Ws-Rfl`, `Ws-Lf1 ↔ Ws-Rgh`. -/
noncomputable def Lemma_15_WEquMSymmetry
    {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) : WEquM Γ v u :=
  h.symm

/-- **Lemma 15 (chain version), paper p. 9:33.** Star-closure variant of
symmetry on transitive well-equivalence. The paper does not state this
explicitly but uses it implicitly when running symmetric chain
arguments. -/
noncomputable def Lemma_15_WEquMSymmetry_star
    {Γ : Ctx} {u v : Term} (h : WEquMStar Γ u v) : WEquMStar Γ v u :=
  h.symm

/-! ## Lemma 16 (`≡_wf` ⊆ `≤_wf`), paper p. 9:33 -/

/-- **Lemma 16 (`≡_wf` ⊆ `≤_wf`), paper p. 9:33.**

> *Statement.* If `Γ ⊢ u ≡_wf v` then `Γ ⊢ u ≤_wf v`.
>
> *Proof.* By induction on the derivation. `Ws-Rfl` becomes `Ws-Rfl`;
> `Ws-Lf1` becomes `Ws-Lf1`; `Ws-Rgh` becomes `Ws-Rgh`. There is no
> `Ws-Lf2` case because `≡_wf` disallows it.

Discharged in de Bruijn by `WEquM.toWSubM` (3-rule structural
induction). -/
noncomputable def Lemma_16_WEquMToWSubM
    {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) : WSubM Γ u v :=
  h.toWSubM

/-- **Lemma 16 (chain version), paper p. 9:33.** Star-closure variant:
transitive well-equivalence embeds into transitive well-subtyping. -/
noncomputable def Lemma_16_WEquMToWSubM_star
    {Γ : Ctx} {u v : Term} (h : WEquMStar Γ u v) : WSubMStar Γ u v :=
  h.toWSubMStar

/-! ## Proposition 17 (From reduction semantics to equivalence
reduction), paper p. 9:33 -/

/-- **Proposition 17 (From reduction semantics to equivalence reduction),
paper p. 9:33.**

> *Statement.* Let `u, v` be terms. If `u ↦ v` then `Γ; s ⊢ u →ᵉᵠᵘ v`
> for all extended context `Γ; s`.
>
> *Proof.* By induction on `u ↦ v` by last rule. Base: `Os-Bet` closes
> by `Me-Bet` and reflexivity (Proposition 18). Inductive: `Os-Con`
> closes by `Me-Fun`, `Me-FOp`, or `Me-App` depending on the
> surrounding evaluation context.

The de Bruijn version is **unconditional** — no axiom is required for
the β case (the body sub-derivation is built by `MEqRed.refl` under the
indexed binder context, without need for cofinite quantification). The
LN version's `Proposition_17_beta_axiom` is retired in this branch.

The de Bruijn statement carries an explicit depth alignment
`Γ.depth = depth` because `StepAt` is depth-indexed; in the closed
empty-context case this collapses to `rfl`. -- Paper writes "for all
extended context `Γ; s`"; mechanized as: parameterised over
`(hdepth : Γ.depth = depth)` and `(hpv : PrevalidExt Γ s)`. -/
noncomputable def Proposition_17_FromReductionToEquivalenceReduction
    {depth : Nat} {Γ : Ctx} {s : Stack} {t t' : Term}
    (hstep : StepAt depth t t') (hdepth : Γ.depth = depth)
    (hpv : PrevalidExt Γ s) :
    MEqRed Γ s t t' :=
  MEqRed.of_StepAt hstep hdepth hpv

/-- **Proposition 17 (closed shape), paper p. 9:33.** Empty-context
specialisation: a closed operational step embeds into empty-stack MPSS
equivalence reduction at the empty context. -/
noncomputable def Proposition_17_FromReductionToEquivalenceReduction_closed
    {t t' : Term} (hstep : Step t t') :
    MEqRed [] [] t t' :=
  MEqRed.of_Step hstep

/-- **Proposition 17 (Prop wrapper), paper p. 9:33.** `MEqRedJ`-shaped
form for callers that consume the Prop API. -/
theorem Proposition_17_FromReductionToEquivalenceReduction_J
    {depth : Nat} {Γ : Ctx} {s : Stack} {t t' : Term}
    (hstep : StepAt depth t t') (hdepth : Γ.depth = depth)
    (hpv : PrevalidExt Γ s) :
    MEqRedJ Γ s t t' :=
  ⟨MEqRed.of_StepAt hstep hdepth hpv⟩

/-! ## Proposition 18 (Reflexivity of equivalence reduction), paper p. 9:33 -/

/-- **Proposition 18 (Reflexivity of equivalence reduction — `→ᵉᵠᵘ`),
paper p. 9:33.**

> *Statement.* Let `Γ; s` be an extended context, `u` a term. We have
> `Γ; s ⊢ u →ᵉᵠᵘ u`.
>
> *Proof.* Straightforward induction on `u`'s structure.

In de Bruijn this is `MEqRed.refl`, a structural recursion on
`Term.Scoped` that splits on the stack at every binder so the body
context can be `.sub` (empty stack) or `.equ` (operand head). -/
noncomputable def Proposition_18_MEqRedReflexivity
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MEqRed Γ s u u :=
  MEqRed.refl hpv hu

/-- **Proposition 18 (Reflexivity of subtyping reduction — `→ˢᵘᵇ`),
paper p. 9:33.** Companion statement: subtyping reduction is also
reflexive. Discharged via `Ms-Equ` of `→ᵉᵠᵘ` reflexivity. -/
noncomputable def Proposition_18_MSubRedReflexivity
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MSubRed Γ s u u :=
  MSubRed.refl hpv hu

/-- **Proposition 18 (Prop wrapper, `→ᵉᵠᵘ`), paper p. 9:33.**
`MEqRedJ`-shaped form. -/
theorem Proposition_18_MEqRedReflexivity_J
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MEqRedJ Γ s u u :=
  ⟨MEqRed.refl hpv hu⟩

/-- **Proposition 18 (Prop wrapper, `→ˢᵘᵇ`), paper p. 9:33.**
`MSubRedJ`-shaped form. -/
theorem Proposition_18_MSubRedReflexivity_J
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MSubRedJ Γ s u u :=
  ⟨MSubRed.refl hpv hu⟩

end Paper
end DeBruijn
end Pss
