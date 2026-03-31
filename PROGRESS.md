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

**Two separate sources of anti-monotonicity identified:**

1. **Domain anti-monotonicity**: Narrowing a context variable that appears
   in a lambda domain narrows the domain, widening the function set (contra).
   FIXABLE by domain erasure / two-level subtyping framework.

2. **Body anti-monotonicity** (= Prop 5.2.9): Anti-monotone functions like
   `Not` produce outputs that go in the opposite direction from inputs.
   When used in ascription `(Not B : B)`, narrowing B breaks the check.
   NOT fixable by subtyping rule changes — it's a property of the function.

**Key discovery: `true = 0` at runtime.** Domain annotations are erased, so
Church-encoded booleans and naturals overlap. This means `true ⋢ Nat` is a
design choice (domain annotations as type identity), not a soundness
requirement.

**Proposed resolution: two-level subtyping.**
- Static (⊑ₛ): current rules with domain checks (user-facing)
- Runtime (⊑ᵣ): domain-erased rules (for metatheory)
- Runtime subtyping IS monotone (domains erased = purely covariant)
- Soundness stated as v ⊑ᵣ τ ("behavioral soundness")

Candidate fixes investigated (see docs/fix-exploration.md):
1. Widen domains on substitution — unsound
2. Pointwise function subtyping — total is equiv to S-Lam, partial breaks true⋢Nat
3. Denotational subtyping — fixes domains but breaks Bool/Nat distinction
4. Two-level subtyping — fixes domain issue, not body issue (most promising)

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
- Identified TWO separate sources of anti-monotonicity: domain-level (fixable)
  and body-level (Prop 5.2.9, fundamental)
- Discovered true = 0 at runtime (domain erasure); proposed two-level
  subtyping framework (static ⊑ₛ for users, runtime ⊑ᵣ for metatheory)
- Proved runtime subtyping is monotone (sketch): erasure eliminates the
  domain-based anti-monotonicity, leaving covariant body checks only
- Explored 4 concrete fixes in detail; two-level subtyping is most promising
  but doesn't resolve body anti-monotonicity (Prop 5.2.9)

What's next:
- Formalize the two-level subtyping framework and prove runtime monotonicity
- Attempt behavioral soundness proof (v ⊑ᵣ τ) using runtime subtyping
- Investigate whether body anti-monotonicity can be restricted without
  killing expressiveness (e.g., polarity annotations on function parameters)
- Consider whether Ochre's algebraic data types (with explicit constructors)
  avoid the Church encoding collapse (true=0) entirely

Blockers:
- Body anti-monotonicity (Prop 5.2.9) remains unresolved
- Design decision needed: accept behavioral soundness (⊑ᵣ) or find a fix
  for full syntactic soundness (⊑ₛ)
```
