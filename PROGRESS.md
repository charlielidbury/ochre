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
- [ ] Soundness theorem proven (no sorry) — **var/type/lam/asc/stuck-app done; 3 sorry in app**
- [ ] Monotonicity theorem proven (no sorry) — **var/lam/type/asc/stuck-app done; 3 sorry in app**
- [ ] Prop 5.2.9 regression test formalized and passing

## Current sorry count

| File | sorry count | Cases remaining |
|------|-------------|-----------------|
| Soundness.lean | 3 | app: lam-lam, lam-nonlam, nonlam-lam |
| Monotonicity.lean | 3 | app: lam-lam, lam-nonlam, nonlam-lam |

## Critical path forward: remove trans from Subtype'

The remaining 6 sorries are all blocked by the same issue: the IH gives
`Subtype' (lam x dom body₂) (lam x dom body₁)` but we need to extract
`Subtype' body₂ body₁` (lambda inversion). This fails because `Subtype'`
includes `trans`, and `trans` can go through arbitrary intermediate terms,
making inversion unsound.

### Recommended fix (next agent should do this):

1. **Remove `trans` from `Subtype'`**. The resulting relation is directly
   invertible: `lam ⊑ lam` can only be `refl` or `lam_body`.

2. **Define `SubtypeTrans`** as the transitive closure of `Subtype'`:
   ```lean
   inductive SubtypeTrans : Expr → Expr → Prop
     | step : Subtype' a b → SubtypeTrans a b
     | trans : SubtypeTrans a b → SubtypeTrans b c → SubtypeTrans a c
   ```

3. **Use `SubtypeTrans` in soundness** (the asc case needs transitivity)
   and in `WellTyped` and `EnvConsistent`.

4. **Prove monotonicity with `Subtype'`** (no trans). The proof structure:
   - Generalize to `absEval_mono`: related expressions AND related envs
   - Case-split on Subtype' proof (clean inversion, no trans)
   - lam-lam app case: invert lam ⊑ lam → body₂ ⊑ body₁ → apply IH
   - Standard monotonicity is a corollary (with Subtype'.refl)

5. **The closure-based evaluator is already in place** (this session).
   After beta-reduction, both sides evaluate the same `body` expression
   (just with different env extensions), making the IH applicable.

### Why this works

With closure-based eval + no-trans Subtype':
```
App case of monotonicity:
  f evals in Γ₁ → lam x dom body₁
  f evals in Γ₂ → lam x dom body₂  
  By IH: lam x dom body₂ ⊑ lam x dom body₁  (Subtype', no trans)
  Invert: body₂ ⊑ body₁  ← NOW POSSIBLE (no trans to worry about)
  
  a evals in Γ₁ → a₁, a evals in Γ₂ → a₂. By IH: a₂ ⊑ a₁.
  
  Beta in Γ₁: absEval ((x, a₁) :: Γ₁) body₁  ← closure, not subst
  Beta in Γ₂: absEval ((x, a₂) :: Γ₂) body₂  ← closure, not subst
  
  EnvSub: ((x, a₂) :: Γ₂) ⊑ ((x, a₁) :: Γ₁) ✓ (a₂ ⊑ a₁, Γ₂ ⊑ Γ₁)
  ExprSub: body₂ ⊑ body₁ ✓ (from inversion)
  
  By generalized IH: τ₂ ⊑ τ₁ ✓
```

## Current blockers (lesser)

### Mixed lam/non-lam cases in app

When one side produces a lambda and the other doesn't (e.g., Γ₁ has a
stuck variable but Γ₂ has it resolved to a lambda). These cases are
rare and may be eliminated by proving that if f₂ ⊑ f₁ (no trans) and
f₁ is a lambda, then f₂ must also be a lambda. Verify this by checking
that no Subtype' constructor sends a non-lam to a lam.

### The dependent domain issue

When a lambda domain depends on a narrowed variable, contravariant domain
checking fails. Related to Ochre Prop 5.2.9. Mitigated by NOT normalizing
domains in absEval.

## Session log

```
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
