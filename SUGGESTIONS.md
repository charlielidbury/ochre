# Suggestions

The current goal is proving soundness of Och. Here is the dependency chain
and priority order for the remaining `sorry`s.

## Phase 0: Fix annotation-trust soundness bug ← NEW, BLOCKING

**absEval's mu-app annotation-trust case (Eval.lean:183-188) is unsound.**

When a mu is applied and both the annotation and body are lams, absEval
uses the annotation's return type instead of evaluating the body:
```lean
| .lam _dom retBody, .lam _ _ =>
    absEval fuel ctx seen (retBody.subst 0 a'.val)
```

This trusts the annotation without validation. Counterexample:
```
app (mu (lam Type (lam Type (bvar 0))) (lam Type Type)) Type
```
absEval returns `lam Type (bvar 0)` (from annotation), concEval returns
`Type` (from body). These are incompatible.

**This MUST be fixed before the soundness theorem can be proved.**

### Option A: Validate annotations at mu creation (RECOMMENDED)

In absEval's `.mu` case (Eval.lean:164-167), add a check:
```lean
| .mu ann body => do
    let ann' ← absEval fuel ctx seen ann
    -- Check body against annotation with self having type ann'
    let bodyCtx := TyCtx.extend ctx ann'
    let body' ← absEval fuel bodyCtx seen body
    if subCheckNF fuel bodyCtx seen body'.val (ann'.val.shift 1 0)
    then .ok ⟨.mu ann'.val body⟩
    else .error "mu body doesn't match annotation"
```

This is the standard recursive-type checking rule: the body must have the
declared type when self has the declared type. The key risk is that this
might break appendArrays (body normalization might fail due to domain checks
on Church-encoded types). Test carefully.

**WARNING:** This changes absEval's behavior, which invalidates the
`absEval_fuel_mono` proof (Phase 1). The fuel monotonicity proof will need
updating to handle the new validation check.

### Option B: Remove annotation-trust, fix appendArrays

Remove the annotation-trust mu-app case entirely. The body-based path
(with seen set for cycle-breaking) should work for most cases. If
appendArrays breaks, it may need restructuring (e.g., using explicit
ascriptions to guide the type checker).

### Option C: WellAnnotated precondition (WEAKEST)

Add a precondition to the soundness theorem that all mu annotations are
correct. This is the weakest fix but allows progress on the proof.

## Phase 1: Foundation — fuel monotonicity ✅ COMPLETE

Both `absEval_fuel_mono` and `subCheckNF_fuel_mono` are proved. (May need
updating if Phase 0 changes absEval.)

## Phase 2: VCompat lemmas (Soundness.lean)

These three lemmas are needed by the main soundness theorem. They should be
tackled after Phase 0 is done.

### `VCompat.from_type_sub_gen` ✅ PROVED (Soundness.lean:178)

### `VCompat.from_self_intro_gen` (Soundness.lean:257)
When `subCheckNF` succeeds for `sigma <: mu ann body` and `sigma` is not
itself a mu, VCompat holds. The inner sorry is essentially adequacy.

### `VCompat.adequacy` (Soundness.lean:322)
The bridge lemma: if `VCompat n v sigma` and `subCheckNF` says `sigma <: tau`,
then `VCompat n v tau`. This is the key lemma connecting the logical relation
to the algorithmic checker.

**Known difficulty:** The lam-lam case requires showing that body compatibility
transfers across subtype-related bodies. The self-elim annotation path requires
VCompat v ann from VCompat v (mu ann body), which relies on the annotation
being correct (Phase 0 prerequisite).

Approach: generalize to arbitrary `seen` sets (needed for self-intro recursion).
Double induction on fuel and step index n. Case analysis on subCheckNF structure.

## Phase 3: Subtyping helper lemmas (Subtyping.lean)

- `subCheckNF_neutral_inferType` (line 194) — has app-app congruence bug

## Phase 4: Main soundness theorem (Soundness.lean:346)

Once Phases 0-2 are done, the main theorem should be approachable.

## Known hazards

- **VCompat must NOT have a general normalization disjunct.** A disjunct like
  `∃ nfuel nctx nseen τ', absEval nfuel nctx nseen τ = .ok τ' ∧ VCompat n v τ'.val`
  makes VCompat trivially true for ALL n, v, τ. This was discovered and fixed
  by agent ochre-20260404-204421. Use the targeted **normalized mu-right**
  disjunct instead (only for mu types).

- **subCheckNF transitivity is FALSE** (counterexample in Tests.lean). Do not
  assume it.

- **subCheckNF top-universality is FALSE**. `Type <: tau` does NOT mean all
  values inhabit `tau`.

- **Never weaken tests.** If a proof doesn't go through, the definitions or
  theorem statement may be wrong. Fix those, not the tests.

- **Check precondition satisfiability.** Any theorem change must be verified
  with `native_decide` witness tests on real programs.
