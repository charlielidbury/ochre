# Simple Och Research Synthesis

## The Calculus

**Proven (main branch, zero sorrys):** 8 rules
- Refl, Top, Var, Lam, App, Mu, Asc-L, Asc-R
- Call-by-name eval, μ always unfolds
- Full soundness: semanticSubst + evalPreservation

**Extended (research branches, 5 transitivity sorrys):** +2 rules
- muUnfoldL: `μs:A.b ⊑ c` if `b[s:=μs:A.b] ⊑ c` (unfold LHS)
- muR: `a ⊑ μs:A.b` if `a ⊑ A` and `a ⊑ b[s:=a]` (self-type intro)

## Research Findings

### A: Self-type intro
Sub.mu (annotation-based, LHS only) CANNOT handle `dtrue ⊑ dBool`.
Need muR + muUnfoldL. With these: dtrue ⊑ dBool, dfalse ⊑ dBool, dzero ⊑ dNat all proved.

### B: Transitivity with muR
Cut-formula elimination handles most cases. 5 edge cases where `hbc = muR`
are sorry'd. Root cause: `body[s:=a]` vs `body[s:=b]` — substitution not
covariant due to contravariant lambda domains. No counterexample found
(believed true). Alternative muR formulations explored but break self-type intro.

### C: CBV soundness
Fundamental gap: `Sub [] (eval a) a` is FALSE for ascriptions.
Counterexample: `a = (var 42 : var 99)`, eval gives `var 42`, but
`var 42 ⊑ (var 42 : var 99)` needs `var 42 ⊑ var 99`. Keep CBN.

### D: Algorithmic formulation
Decision procedure `check` works for 10/11 tests including self-types.
Soundness proof partial (13 sorrys). Key gap: algorithm trusts μ annotations
without checking body well-typedness. Fix: check `body ⊑ A↑` too.

### E: Simplification
175 lines removed. `termination_by` confirmed incompatible with transitivity
proof (narrow calls trans at same complexity with larger sizes from weakening).

## Key Architectural Insight (2026-04-10 overnight)

**Self-types are inherently circular.** `dtrue ⊑ dBool` requires
`dtrue ⊑ dBool` inside its own proof (via contravariant domain check).
This makes inductive Sub fundamentally incapable of self-type intro.

The full Och handles this with a **seen set** (cycle detection) in
the algorithmic checker. The declarative system needs either:
- Coinductive Sub (infinite proof trees)
- Step-indexed Sub (approximate at depth k)
- Algorithmic approach with proven soundness

**Current approach:** algorithmic checker with seen set, proving
it sound via step-indexed or coinductive argument.

## Open Questions

1. **Algorithm soundness for self-types**: The check function accepts
   dtrue ⊑ dBool via cycle detection. Proving this is sound requires
   showing the cycle-break assumptions are valid.

2. **BetaR recovery**: Same substitution-inflation issue as muUnfoldL.

3. **muR transitivity**: 5 edge cases with substitution covariance.
   Alternative muR (self=μA.body) has zero sorrys but doesn't enable
   self-types. The circularity IS the self-type mechanism.

## Delta to Full Och

| Feature | Simple Och | Full Och | Gap |
|---------|-----------|----------|-----|
| Self-types (μ) | ✓ (research) | ✓ | muR transitivity sorrys |
| BetaR | ✗ | ✓ | Needs norm-based trans |
| Call-by-value | ✗ (CBN) | ✓ (CBV) | Fundamental gap |
| Type synthesis | ✗ | ✓ (absEval) | Needed for ergonomics |
| Seen set | ✗ (fuel) | ✓ | Needed for precision |
| Normal forms | Implicit | Explicit | Architectural choice |
| Subtype on NF | ⊑ does all | Separate | Architectural choice |

## Aspirational Test Scorecard

| Category | Tests | Passing | Blocked on |
|----------|-------|---------|------------|
| A: Self-types | 8 | 3 | muR transitivity proof |
| B: BetaR | 5 | 0 | Norm-based transitivity |
| C: CBV | 3 | 0 | Fundamental gap (keep CBN) |
| D: Recursive | 4 | 0 | μ expressiveness |
| E: Larger | 3 | 0 | Combination |
| **Total** | **23** | **3** | |
