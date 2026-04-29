# Axioms

This formalization mechanizes Pasquale & García-Pérez (arXiv 2407.13882
v2, December 2025), the MPSS Krivine-style reformulation of Hutchins'
Pure Subtype Systems. Type safety (Theorems 4 and 5) is conditional on
the following axioms.

Total axiom count: **13** (1 permanent, 12 outstanding).

## Permanent axioms (paper-conjecture-status)

### `Conjecture_8_WellSubtypingContextIndependent`
- File: `Pss/Mpss/TypeSafety.lean`, line 106.
- Paper: Pasquale & García-Pérez 2024, §4 p. 13 (Conjecture 8).
- Statement: For `Γ ⊢ u ≤*_wf t`, any covariant context `Co` such that
  both `Co[u]` and `Co[t]` are well-formed in `Γ` satisfies
  `Γ ⊢ Co[u] ≤*_wf Co[t]`.
- Status: **Open conjecture in the source paper**; we mirror its open
  status here. Theorems 4 & 5 are stated and proved CONDITIONAL on this
  axiom. Closing this conjecture is a research-level metatheory result,
  not a proof-engineering exercise; it is therefore documented as
  permanent in this formalization.

## Outstanding axioms (would be discharged in a future polish wave)

### `Lemma_1_StrongCommutativity`
- File: `Pss/Mpss/Commutation.lean`, line 201.
- Paper: Pasquale & García-Pérez 2024, §3 (Lemma 1, Appendix A proof).
- The headline result of paper 2: `⟶^≤` and `⟶^≡` strongly commute,
  modulo the extended-context-stepping discipline `↣*`.
- Discharge plan: ~600-1500 lines. The case grid (6 × 8 = 48 cells) is
  documented in the file. Order: (i) prove Lemma 2 first; (ii) discharge
  diagonal cases (`app×app`, `fun_×fun_`, `fOp×fOp`); (iii) discharge
  substitution-using cells (`app×bet` via Lemma 30); (iv) discharge
  weakening-using cells (`pro×var` via Lemma 22); (v) discharge
  narrowing-using cells.

### `Lemma_2_DiamondMEqRed`
- File: `Pss/Mpss/Diamond.lean`.
- Paper: Pasquale & García-Pérez 2024, §3 (Lemma 2, Appendix A proof).
- Diamond property of MPSS equivalence reduction. Mechanized as a
  THEOREM (not an axiom) via a same-context core + a context-evolution
  lift; the core dispatches to 5 narrow per-case private inline axioms
  (one per recursive structural case) and the lift is one further
  private axiom.
- Note: the paper's "moreover" clause (no `Me-Pro` on `x` side condition)
  is dropped from this mechanization. The previous attempt
  (`MEqRedAvoidsPro`) was unsound under Lean 4's proof irrelevance,
  and no downstream consumer in this codebase actually used the side
  condition (see the module docstrings in `Pss/Mpss/AvoidsPro.lean`
  and `Pss/Mpss/Diamond.lean` for the full analysis).
- Discharge plan: discharge the 5 inline residual axioms + the
  context-evolution lift via the existing weakening / narrowing
  infrastructure.

### `Lemma_24_NarrowingMSubRed`
- File: `Pss/Mpss/Narrowing.lean`, line 317.
- Paper: Pasquale & García-Pérez 2024, Appendix Lemma 24.
- Narrowing for `MSubRed`. The Ms-Pro y=x case requires `MSubRedStar`
  glue not yet available at Wave 5.
- Discharge plan: introduce a refined `MSubRedNoProOf` predicate or
  manually unfold the Ms-Pro promotion.

### `Lemma_30_msPro_x_axiom`
- File: `Pss/Mpss/Substitution.lean`, line 701.
- Paper: Pasquale & García-Pérez 2024, Appendix Lemma 30 (Ms-Pro arm).
- Residual `Ms-Pro y=x` arm of Lemma 30 (substitution preserves
  `MSubRed`). Under the paper's "no promotion of `x`" side condition,
  this case is vacuous; mechanizing the side condition requires a
  refined `MSubRedNoProOf` predicate.
- Discharge plan: introduce a structurally-recursive `Bool`-valued
  function `avoidsPro : MSubRed Γ s u v → String → Bool` (NOT an
  inductive Prop predicate — see the analysis in
  `Pss/Mpss/AvoidsPro.lean` for why an indexed Prop predicate over a
  Prop-valued reduction is unsound under proof irrelevance), then
  discharge the case directly.

### `MEqRed.toScoped`
- File: `Pss/Mpss/Weakening.lean`, line 432.
- Bridge from the unscoped `MEqRed` inductive (in `Reductions.lean`) to
  the scope-aware wrapper used by the partitioned weakening lemmas.
- Discharge plan: refactor `MEqRedScoped.bet` to allow stray fvars in
  freshly-opened bodies, then prove by induction on `MEqRed`.

### `MSubRed.toScoped`
- File: `Pss/Mpss/Weakening.lean`, line 438.
- Companion of the previous, for the subtype reduction.
- Discharge plan: same as above.

### `Lemma_10_Inversion`
- File: `Pss/Mpss/WellFormed.lean`.
- Paper: Pasquale & García-Pérez 2024, Appendix Lemma 10.
- Full inversion of `WSubMStar` at `abs/abs`: returns
  `WEquM Γ t t'` (well-equivalence of the bound annotations), matching
  the paper's exact statement.
- Discharge plan: prove via Theorem 3 (transitivity elimination) plus a
  chain-shape argument on `MEqRedStar`/`MSubRedStar` reductions out of
  abstractions.

### `Lemma_10_InversionRestricted`
- File: `Pss/Mpss/WellFormed.lean`.
- Paper: Pasquale & García-Pérez 2024, Appendix Lemma 10.
- Restricted-form inversion of `WSubMStar` at `abs/abs`: returns a
  common `MEqRedStar` reduct of the bound annotations rather than the
  paper's `≡_wf`. Retained as a separate axiom because extracting a
  common reduct from a `WEquM` chain (the conclusion of
  `Lemma_10_Inversion`) requires diamond-style joining of the prepended
  / appended `MEqRed` steps.
- Discharge plan: same as `Lemma_10_Inversion`, then a diamond-style
  joining lemma to extract the common reduct.

### `Proposition_17_beta_axiom` *(new in Wave 7)*
- File: `Pss/Mpss/OperationalSem.lean`, line 81.
- Paper: Pasquale & García-Pérez 2024, Proposition 17 (β arm).
- The β-case of Proposition 17 (operational ↣ MPSS equiv-red).
  Required because `MEqRed.bet`'s body sub-derivation is at Γ;s without
  the binder added, which fails the fv-scope requirement of
  `MEqRed.refl` when the freshly opened body mentions a name outside
  `Γ.dom`.
- Discharge plan: write a custom reflexivity helper that walks `LC`
  using `MEqRed.var` (no fv-scope needed) at fvars; OR refine
  `MEqRed.bet`'s body premise to extend the context.

### `Lemma_11_TopHasNoFunctionSupertype` *(new in Wave 7)*
- File: `Pss/Mpss/TypeSafety.lean`, line 125.
- Paper: Pasquale & García-Pérez 2024, §4 appendix (Lemma 11, restricted).
- `Top` is not a transitive well-subtype of an abstraction. Used by
  Theorem 4 (Progress) to rule out the case where the operator of a
  redex is `Top`.
- Discharge plan: structural induction on `WSubMStar`, leveraging
  `Lemma_10_InversionRestricted` to argue function-shape preservation.

### `Lemma_6_EvaluationPreservesWf` *(new in Wave 7)*
- File: `Pss/Mpss/TypeSafety.lean`, line 143.
- Paper: Pasquale & García-Pérez 2024, §4 (Lemma 6).
- Evaluation preserves well-formedness: `WfM Γ t  →  Step t t'  →  WfM Γ t'`.
- The β-case of the paper's proof (p. 27) consumes Lemmas 10, 15, 16, 7.
  Lemmas 15/16 are out of scope (need `WEquM`); Lemma 10 is
  partially axiomatized (`Lemma_10_InversionRestricted`); Lemma 7 is
  axiomatized below.
- Discharge plan: extend `Pss/Mpss/WellFormed.lean` with `WEquM` + full
  Lemmas 10, 15, 16, then proceed by induction on `Step`.

### `Lemma_7_SubstitutionPreservesWf` *(new in Wave 7)*
- File: `Pss/Mpss/TypeSafety.lean`, line 163.
- Paper: Pasquale & García-Pérez 2024, §4 (Lemma 7).
- Restricted single-binder form: instead of the paper's
  `Γ, x ≤ t, Γ' ⊢ u wf  ⟹  Γ, Γ'[x\α] ⊢ u[x\α] wf`, we state the
  case `Γ' = ∅`.
- Discharge plan: induction on the well-formedness derivation, using
  `Conjecture_8_WellSubtypingContextIndependent` in the `app` case +
  `Lemma_28_SubstPreservesPrevalid` (already proved in
  `Pss/Mpss/Substitution.lean`).

## Lemmas the paper covers and we have proved

- **Lemma 15** (paper appendix): `Γ ⊢ u ≡_wf v  ⟹  Γ ⊢ v ≡_wf u`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_15_WEquM_symm`.
- **Lemma 16** (paper appendix): `Γ ⊢ u ≡_wf v  ⟹  Γ ⊢ u ≤_wf v`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_16_WEquM_to_WSubM`.

## Audit

Run `lake env lean Pss/Sanity.lean` (or build the full `Pss.Sanity`
module) to print the axiom dependencies of the headline theorems. The
expected baseline is `propext`, `Quot.sound`, `Classical.choice` plus
the relevant paper-level axioms above.
