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
- [x] **`trans` removed from `Subtype'`** — enables lambda inversion
- [x] **`SubtypeTrans` defined** — transitive closure for soundness
- [x] **Lambda inversion proven** — `Subtype'.lam_inv` and `Subtype'.lam_rhs_shape`
- [x] **Generalized monotonicity proven** — `absEval_mono` handles related exprs + envs
- [x] **Lam-lam app case of monotonicity proven** — the previously impossible case!
- [x] **Stuck-stuck app case of monotonicity proven** — via `app_cong`
- [ ] Mixed lam/non-lam app case of monotonicity — **8 sorry, all same issue**
- [ ] Soundness app case — **1 sorry** (needs generalization like monotonicity)
- [ ] Prop 5.2.9 regression test formalized and passing

## Current sorry count

| File | sorry count | Cases remaining |
|------|-------------|-----------------|
| Monotonicity.lean | 8 | app: mixed lam/non-lam (f₂=lam, f₁≠lam) |
| Soundness.lean | 1 | app: entire case (needs generalized soundness) |

## Critical path forward: eliminate mixed lam/non-lam sorry

All 8 monotonicity sorry are the same issue: when `f` evaluates to a
non-lambda in Γ₁ (e.g., stuck var) but evaluates to a lambda in Γ₂
(more precise env). This means Γ₂ beta-reduces but Γ₁ doesn't.

We need `Subtype' (beta-reduced-result) (app f₁ a₁)`.

### Recommended fix: add type-app-returns-type to evaluator

Change absEval (and concEval) so that when `f` evaluates to `.type`,
the app case returns `.type` instead of a stuck `.app .type a`:

```lean
| some (.lam x _dom body), some aVal => absEval fuel ((x, aVal) :: Γ) body
| some .type, some _ => some .type  -- NEW: Type applied = Type
| some f', some a' => some (.app f' a')
| _, _ => none
```

This is semantically correct: applying the universe (top) to anything
gives the universe. It eliminates the f₁=type/f₂=lam mixed case (since
Subtype'.top covers it: τ₂ ⊑ type).

After this change, the remaining mixed cases (f₁=var/app, f₂=lam) can
be shown impossible: `Subtype' (lam ...) (var ...)` and `Subtype' (lam ...) (app ...)`
have no constructors in the trans-free `Subtype'`.

**Technical challenge**: The evaluator change adds a new match arm, and
Lean's `simp` currently struggles to reduce match hypotheses with the
extra arm. This was attempted in this session but reverted. The next agent
should either:
1. Use `dsimp` or explicit `show`/`change` tactics for match reduction
2. Write helper lemmas that reduce absEval one step (e.g., `absEval_app_lam`)
3. Restructure the proof to avoid hypothesis rewriting

### Soundness app case

The soundness app case needs the same generalization as monotonicity:
a `soundness_gen` that takes `Subtype' e_c e_a` for related expressions.
The structure would mirror `absEval_mono`. After beta-reduction,
body_c ≠ body_a (different normalized bodies), so the IH needs the
generalized form.

A `SubtypeTrans.lam_body` lemma has already been added to Subtyping.lean
(proven by induction on SubtypeTrans).

## Session log

```
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
