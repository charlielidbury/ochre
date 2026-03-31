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
- [x] `Subtype'` inductive relation has function subtyping rule
- [ ] Soundness theorem proven (no sorry)
- [ ] Monotonicity theorem proven (no sorry)
- [ ] Prop 5.2.9 regression test formalized and passing

## Status of Proof Tasks (Task 4)

- [x] 4.3 Ascription soundness: PROVED (trivial from Asc rule)
- [x] 4.4 Transparency preservation: PROVED (induction on term structure)
- [~] 4.1 Soundness: Structure established, all cases except App done.
  App case reduces to Covariant Substitution lemma, which requires Monotonicity.
  Mutual dependency identified.
- [x] 4.2 Monotonicity: **SHOWN TO FAIL** in general. Concrete counterexample:
  `(λ(A:Type).λ(x:A).x) A` under A:Nat vs A:Type. Dependent domain
  instantiation + contravariant function subtyping = anti-monotonicity.
  This is Prop 5.2.9 in Och's setting.

## Current blockers

**Monotonicity fails for unapplied functions with dependent domains.**

The fundamental tension: function subtyping is contravariant in domains, but
narrowing a context variable NARROWS the domain (covariant in the context).
These two covariances conflict.

Candidate fixes investigated (see docs/tasks/4-proofs.md):
1. Restrict variables from appearing in lambda domains (kills dependent types)
2. Use pointwise function subtyping instead of S-Lam (promising, needs investigation)
3. Separate domain shape from behavior in subtyping
4. Restrict monotonicity to ground types / fully-applied results (most promising)
5. Modify App rule to preserve monotonicity

## Session log

```
## 2026-03-31 och-md-20260331-123613
What I did:
- Wrote complete proofs for Task 4 (Layer 4: Proofs)
- Proved ascription soundness (4.3) and transparency preservation (4.4)
- Established full proof structure for soundness (4.1), identifying the
  mutual dependency with monotonicity
- Identified and proved that monotonicity (4.2) FAILS in general:
  concrete counterexample with λ(A:Type).λ(x:A).x showing anti-monotone
  behavior when A is narrowed (dependent domain + contravariant subtyping)
- This is the Prop 5.2.9 phenomenon reproduced in the pure Och setting
- Analyzed 5 candidate fixes, with "monotonicity for ground types only"
  and "pointwise function subtyping" as most promising

What's next:
- Investigate whether pointwise function subtyping (replacing S-Lam) rescues
  monotonicity while preserving all Task 1 derivations
- Try proving soundness without full monotonicity (closed-term simulation
  lemma might be independent)
- Formalize what "ground type" means and whether restricted monotonicity
  suffices

Blockers:
- Monotonicity failure blocks the soundness proof's App case
- Need a design decision on how to resolve the domain contravariance issue
```
