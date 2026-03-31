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
- [ ] Soundness theorem proven (no sorry) — **var/type/lam/asc/stuck-app done; beta-app sorry**
- [ ] Monotonicity theorem proven (no sorry) — **var/lam/type/asc/stuck-app done; beta-app sorry**
- [ ] Prop 5.2.9 regression test formalized and passing

## Current sorry count

| File | sorry count | Cases remaining |
|------|-------------|-----------------|
| Soundness.lean | 3 | app: lam-lam, lam-nonlam, nonlam-lam |
| Monotonicity.lean | 3 | app: lam-lam, lam-nonlam, nonlam-lam |

All sorries are the same structural issue: after beta-reduction, the two
evaluators (or two envs) produce different substituted expressions, and
the IH requires the same expression. See "Current blockers" below.

## Current blockers

### The app-after-beta problem (blocks both Soundness and Monotonicity)

When `f` evaluates to a lambda and we beta-reduce, the two sides of the
proof work with different substituted expressions:

**Monotonicity:** `body₁.subst x₁ a₁` vs `body₂.subst x₂ a₂` (same source f,
different envs produce different normalized bodies and args). The IH covers
the same expression in different envs, but not different expressions.

**Soundness:** `body_a.subst x_a a_a` vs `body_c.subst x_c a_c` (same source f,
but absEval and concEval diverge at ascriptions inside f's body, producing
different lambda bodies).

### Potential approaches

1. **Substitution monotonicity lemma:** Prove that if body₂ ⊑ body₁ and v₂ ⊑ v₁,
   then absEval Γ₂ (body₂.subst x v₂) ⊑ absEval Γ₁ (body₁.subst x v₁). This
   is essentially monotonicity generalized to different expressions.

2. **Substitution-environment equivalence:** Prove absEval Γ (body.subst x v) =
   absEval ((x,v)::Γ) body. Then the IH applies (same body, different env).
   Doesn't hold directly because substitution replaces x with v which then gets
   re-evaluated, while env-based just returns v.

3. **Closure-based evaluator:** Redesign absEval to use closures/environments
   instead of substitution. Then beta-reduction extends the env rather than
   substituting, and the IH applies (same body in both cases).

4. **Beta-subtyping rule:** Add Subtype' rules relating redexes to their reducts.
   E.g., `app (lam x dom body) a ⊑ body.subst x a`. Helps with mixed cases
   (one side beta-reduces, the other is stuck).

### The dependent domain issue

When a lambda domain depends on a narrowed variable, contravariant domain
checking fails. E.g., `λx:3. x ⊑ λx:Nat. x` fails because 3 ⊑ Nat but
Nat ⊑ 3 doesn't hold (contravariance). Related to Ochre Prop 5.2.9.
Mitigated by NOT normalizing domains in absEval.

## Session log

```
## 2026-03-31 och-agent-20260331-120514
What I did:
- Implemented normalization under binders in absEval (key for succ 2 = 3)
- Implemented pointwise subCheck with inferType for neutral terms
- Added Subtype' rules: lam_body, app_cong (for monotonicity proof)
- Proved monotonicity for var, lam, type, asc cases; partial app case
  (stuck-stuck sub-case proven, beta sub-case sorry)
- Made concEval parallel to absEval (takes env, normalizes under binders)
- Defined WellTyped predicate for soundness precondition
- Proved soundness for var, type, lam, asc, stuck-app cases
- Added extensive tests: add, isZero, double, Church numerals, subtyping
- All tests pass (25+ test examples)

What's next:
- Resolve the app-after-beta problem (see blockers above)
- Option 3 (closure-based evaluator) is most promising for provability
- Formalize the Prop 5.2.9 regression test
- Consider adding beta-subtyping rules to handle mixed lam/non-lam cases

Blockers:
- The substitution-based evaluator makes the app case unprovable without
  additional lemmas. A closure-based redesign would fix this structurally.
```
