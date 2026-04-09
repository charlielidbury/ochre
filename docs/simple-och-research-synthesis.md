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

## Open Questions

1. **muR transitivity**: Step-indexed LR or coinductive argument needed.
   Currently being researched.

2. **BetaR recovery**: Would need normalization-based transitivity.
   Currently blocked on (1) — same fundamental issue.

3. **Full Och parity**: Missing BetaR, seen set for μ cycles,
   type synthesis. See delta analysis below.

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
