# Progress

Current status of the Och mechanization. Updated by agents after each session.

## Status

- [x] Syntax representation finalized
- [x] Concrete evaluation correct (all §6.1 concrete tests pass)
- [x] Abstract evaluation correct (all §6.1/§6.4 abstract tests pass)
- [x] Subtyping decision procedure (`subCheck`) handles Church-encoded types
- [x] `true ⊑ Bool` works
- [x] `3 ⊑ Nat` works
- [x] Function subtyping (contravariant domain, covariant body) works
- [x] Subtyping tests (§6.1) uncommented and passing
- [x] Negative tests (§6.3) uncommented and passing
- [x] Transparency tests (§6.4) uncommented and passing
- [x] `Subtype'` inductive relation has function subtyping rules (lam_body, app_cong)
- [x] Closure-based evaluator (env extension instead of substitution for app)
- [x] `trans` removed from `Subtype'` — enables lambda inversion
- [x] `SubtypeTrans` defined — transitive closure for soundness
- [x] Lambda inversion proven — `Subtype'.lam_inv` and `Subtype'.lam_rhs_shape`
- [x] **Generalized monotonicity proven** — `absEval_mono` handles related exprs + envs
- [x] **Monotonicity COMPLETE** — 0 sorry!
- [x] **Type-app-returns-type** — evaluator returns `.type` when applying Type
- [x] **SubtypeTrans inversion lemmas** — lam_target_shape, app_target_shape, var_target, asc_target
- [x] **SubtypeTrans.app_cong** — congruence for app through transitive closure
- [x] **Generalized soundness proven** — `soundness_gen` handles related exprs via SubtypeTrans
- [x] **Soundness COMPLETE** — 0 sorry!
- [x] **Prop 5.2.9 regression test** formalized and passing

## Current sorry count

**ZERO.** All proofs are complete.

## What remains

1. **Scale to full Ochre** — The Och calculus proves the core semantic idea is
   sound. The next step is to extend it toward the full Ochre language (see
   `docs/why-och-matters-for-ochre.md`).

2. **More §6 tests** — Many spec tests from §6.2 (abstract instantiation) are
   not yet formalized. These would increase confidence in the evaluator.

## Key theorems proven

### Monotonicity (`absEval_mono` in Monotonicity.lean)
Given `Subtype' e₂ e₁` and `EnvSub Γ₂ Γ₁`:
if `absEval fuel Γ₁ e₁ = some τ₁` and `absEval fuel Γ₂ e₂ = some τ₂`,
then `Subtype' τ₂ τ₁`.

Standard monotonicity (same expression, different envs) is the corollary
with `Subtype'.refl`.

### Soundness (`soundness_gen` in Soundness.lean)
Given `SubtypeTrans e_c e_a` and `EnvConsistent γ Γ` and `WellTyped fuel Γ e_a`:
if `absEval fuel Γ e_a = some τ` and `concEval fuel γ e_c = some v`,
then `SubtypeTrans v τ`.

Standard soundness (same expression in both evaluators) is the corollary
with `SubtypeTrans.step (Subtype'.refl e)`.

## Key techniques

- **Trans-free Subtype'**: Removing `trans` from `Subtype'` enables lambda
  inversion (extracting body relation from `Subtype' (lam..) (lam..)`).
  `SubtypeTrans` provides transitivity where needed (soundness asc case).

- **SubtypeTrans target shape lemmas**: For each constructor shape (var, lam,
  app, asc), if `SubtypeTrans e (constructor ..)`, then `e` must have the same
  constructor shape. This is used in the generalized soundness to constrain the
  concrete expression's shape from the abstract expression's shape.

- **Type-app-returns-type**: When the function evaluates to `.type`, the app
  case returns `.type` instead of a stuck `(.app .type a)`. This eliminates the
  mixed lam/type case in monotonicity (since `Subtype'.top` handles it trivially).

- **Closure-based evaluation**: Using env extension instead of substitution
  keeps the SAME body expression in both sides of the proof, making the IH
  directly applicable.

## Session log

```
## 2026-03-31 ochre-lean-20260331-133412
What I did:
- Formalized the Prop 5.2.9 regression test in Tests.lean
- Defined Not' (boolean negation): λ(X: Bool). X Bool false true
- Verified Not' computes correctly: Not true = false, Not false = true, Not Bool = Bool
- Demonstrated the core of the counterexample: false ⊑ true fails (subCheck = false)
- Added safe-version tests: (Not true : Bool) and (Not false : Bool) pass subtyping
- All tests pass, build clean

What's next:
- Scale toward full Ochre (see docs/why-och-matters-for-ochre.md)
- Consider formalizing more §6.2 abstract tests from the spec

Blockers:
- None — Och milestone is essentially complete

## 2026-03-31 ochre-lean-20260331-131404
What I did:
- COMPLETED ALL PROOFS — zero sorry remaining!
- Eliminated 6 impossible mixed cases in monotonicity (Subtype' (lam..) (var/app/asc..)
  has no constructors, so `cases hf_sub` closes them)
- Added type-app-returns-type to both evaluators (absEval and concEval):
  when f evaluates to .type, app returns .type instead of stuck (.app .type a)
- This made the remaining 2 type mixed cases in monotonicity trivial (Subtype'.top)
- Added SubtypeTrans inversion lemmas to Subtyping.lean:
  - lam_target_shape: SubtypeTrans e (lam..) → e = lam.. with body relation
  - app_target_shape: SubtypeTrans e (app..) → e = app.. with component relations
  - var_target: SubtypeTrans e (var x) → e = var x
  - asc_target: SubtypeTrans e (asc..) → e = asc..
  - lam_inv: SubtypeTrans (lam x d b₂) (lam x d b₁) → SubtypeTrans b₂ b₁
  - app_cong: lift app congruence through SubtypeTrans
  - eq_of_rigid_target: general helper for shapes where only refl matches
- Proved generalized soundness (soundness_gen) taking SubtypeTrans e_c e_a:
  - Case-splits on e_a (abstract expression shape)
  - Uses target shape lemmas to constrain e_c
  - App-beta case: uses lam_target_shape + lam_inv to extract body relation,
    then recurses with SubtypeTrans body_c body_a
  - Asc case: chains IH with well-typedness via SubtypeTrans.trans
- Standard soundness is a corollary with SubtypeTrans.step (Subtype'.refl e)
- Added envConsistent_extend_sub for extending EnvConsistent with SubtypeTrans

What's next:
- Formalize and uncomment the Prop 5.2.9 regression test
- Consider scaling toward full Ochre

Blockers:
- None! All proofs complete.

## 2026-03-31 och-agent-20260331-124544
What I did:
- Removed `trans` from `Subtype'`, added `SubtypeTrans` (transitive closure)
- Proved lambda inversion lemmas (`lam_inv`, `lam_rhs_shape`)
- Added `SubtypeTrans.lam_body` (lift lam_body through transitive closure)
- Added `envSub_extend_sub` (extend EnvSub with related bindings)
- Proved generalized monotonicity `absEval_mono` taking `Subtype' e₂ e₁`
- Proved the lam-lam app case of monotonicity (PREVIOUSLY IMPOSSIBLE!)
- Proved the stuck-stuck app case of monotonicity
- Standard `monotonicity` is now a corollary of `absEval_mono`
- Fixed soundness to use `SubtypeTrans`, proved lam case
- Fixed `WellTyped` to use closure-based eval (matching evaluator)
- Attempted type-app-returns-type evaluator change but reverted due to
  match reduction issues with simp

What's next:
- Eliminate mixed lam/non-lam sorry (see "Recommended fix" above)
- Prove soundness app case via generalized soundness_gen

Blockers:
- simp can't reduce match hypotheses with the extra type-app arm
  (needs a different tactic approach)
- Mixed lam/non-lam cases need either evaluator change or proof that
  they're impossible given the Subtype' relation

## 2026-03-31 och-agent-20260331-120514
What I did:
- Implemented normalization under binders in absEval (key for succ 2 = 3)
- Implemented pointwise subCheck with inferType for neutral terms
- Added Subtype' rules: lam_body, app_cong (for monotonicity proof)
- Proved monotonicity for var, lam, type, asc, stuck-app cases
- Made concEval parallel to absEval (takes env, normalizes under binders)
- Defined WellTyped predicate for soundness precondition
- Proved soundness for var, type, lam, asc, stuck-app cases
- Switched from substitution to closure-based evaluation (env extension)
  in both absEval and concEval app cases. All tests pass.
- Added 25+ test examples (add, isZero, double, Church numerals, subtyping)
- Identified the path forward: remove trans from Subtype' to enable
  lambda inversion, then the app case proof goes through

What's next:
- Remove trans from Subtype', add SubtypeTrans (see "Critical path forward")
- Prove the generalized monotonicity (absEval_mono) using lambda inversion
- Prove soundness app case using the same technique
- Handle mixed lam/non-lam cases (may require proving they can't occur)

Blockers:
- trans in Subtype' prevents lambda inversion (the core issue)
- Mixed lam/non-lam app cases (minor, may be eliminable)
```
