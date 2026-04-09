# Simple Och Research Synthesis

*Updated: 2026-04-10 overnight session*

## What We Built

A minimal dependently-typed calculus with a single `⊑` relation, machine-checked in Lean 4.

**Main branch (zero sorrys, fully proven):**
- 8 rules: Refl, Top, Var, Lam, App, Mu, Asc-L, Asc-R
- Call-by-name eval, μ always unfolds (not a value)
- Full soundness: semanticSubst + evalPreservation
- All properties: weakening, substitution, transitivity (cut-formula lex measure)
- Test suite: 80 passing tests, 23 aspirational

## Research Findings

### A: Self-type intro requires cycle detection

**Finding:** `dtrue ⊑ dBool` is inherently circular. The contravariant domain check inside the [Lam] comparison requires `dtrue ⊑ dBool` inside its own proof. This makes inductive Sub fundamentally incapable of self-type intro.

**Implication:** Self-types need either coinductive Sub, step-indexed Sub, or an algorithmic approach with a seen set. This matches how full Och works (seen set in absEval).

### B: muR transitivity

Two formulations explored:
- **muR (self=a):** `a ⊑ μA.b if a ⊑ A ∧ a ⊑ b[s:=a]`. Enables self-types. 5 transitivity sorrys (substitution covariance, believed true, no counterexample found).
- **muR (self=μ):** `a ⊑ μA.b if a ⊑ A ∧ a ⊑ b[s:=μA.b]`. Zero sorrys. But DOESN'T enable self-types (fixed substitution can't match dtrue's specific structure).

**muUnfoldL** (unfold μ on LHS) explored with well-typedness premise. Weakening/substitution/narrowing all proved. 1 transitivity sorry remains (trans(muR, muUnfoldL) — principal cut for μ-types).

### C: CBV soundness

**Finding:** CBV soundness has a fundamental gap. `Sub [] (eval a) a` is FALSE for ascriptions. Counterexample: `a = (var 42 : var 99)`, eval gives `var 42`, but `var 42 ⊑ (var 42 : var 99)` requires `var 42 ⊑ var 99`.

**Decision:** Keep CBN for formal semantics. CBV for practical eval only.

### D: Algorithmic formulation

Decision procedure `check` with seen set:
- 10/11 tests pass including dtrue ⊑ dBool (via cycle detection)
- Soundness proof: 9 engineering sorrys (synth/app plumbing), 2 fundamental sorrys (cycle detection needs coinductive reasoning)
- Agent working on closing the 9 engineering sorrys

### E: Simplification

Properties.lean: 988→893 lines. `termination_by` confirmed incompatible with transitivity proof (narrow calls trans at same complexity with larger sizes from weakening).

## Architecture Insights

### Why cut-formula elimination works (and where it breaks)

Transitivity uses lex measure `(b.complexity, derivation_sizes)` where `b` is the "cut formula." Going under constructors decreases complexity. Substitution can INCREASE complexity.

- **LHS substitution** ([App]): substituted term on LEFT, cut `b` unchanged. ✓
- **RHS substitution** (BetaR, Mu-R, muUnfoldL): substituted term becomes new cut. ✗

### Why self-types need cycles

Self-type intro: `dtrue ⊑ dBool` unfolds both sides to lambdas, then the contravariant domain check requires `dtrue ⊑ dBool` — the original goal. This is a PRODUCTIVE cycle (goes under a lambda binder each iteration). Inductive proofs can't handle productive cycles; coinductive or step-indexed proofs can.

### The two-system architecture

For full Och parity, the system needs two layers:
1. **Declarative Sub** (inductive, 8 rules): specification, provably sound, no cycles
2. **Algorithmic check** (with seen set): implementation, handles cycles, proven sound w.r.t. declarative Sub for non-cyclic cases + coinductively sound for cyclic cases

## Aspirational Test Scorecard

| Category | Tests | Passing | Blocked on |
|----------|-------|---------|------------|
| A: Self-types | 8 | 3 (algo) | Coinductive soundness proof |
| B: BetaR | 5 | 0 | RHS substitution in transitivity |
| C: CBV | 3 | 0 | Fundamental gap (keep CBN) |
| D: Recursive | 4 | 0 | μ expressiveness |
| E: Larger | 3 | 0 | Combination |
| **Total** | **23** | **3** | |

## Delta to Full Och

| Feature | Simple Och | Full Och | Status |
|---------|-----------|----------|--------|
| Core rules | 8 (proven) | ~12 | ✓ |
| Self-types (μ) | Algo only | ✓ | Needs coinductive soundness |
| BetaR | ✗ | ✓ | Needs norm-based trans |
| Call-by-value | ✗ (CBN) | ✓ (CBV) | Fundamental gap |
| Type synthesis | ✗ | ✓ (absEval) | Ergonomics |
| Seen set | ✓ (algo) | ✓ | ✓ |
| Cycle detection | ✓ (algo) | ✓ | ✓ |

## Research Branches

| Branch | Location | Purpose | Status |
|--------|----------|---------|--------|
| main | `/home/charlielidbury/repos/ochre` | Proven base (8 rules) | Zero sorrys ✓ |
| research-B | `/home/charlielidbury/repos/ochre-research-B` | muR (self=a) + muUnfoldL | 5 trans sorrys |
| research-D | `/home/charlielidbury/repos/ochre-research-D` | Algorithm + soundness | 11→? sorrys |
| research-step-idx | `/home/charlielidbury/repos/ochre-research-step-idx` | muR (self=μ) + muUnfoldL | 1 trans sorry |
| research-tests | `/home/charlielidbury/repos/ochre-research-tests` | Test suite | Merged to main ✓ |
| research-simplify | `/home/charlielidbury/repos/ochre-research-simplify` | Proof cleanup | Merged to main ✓ |
| option3-recovery | `/home/charlielidbury/repos/ochre-option3` | Trans as axiom | Zero sorrys ✓ |
| ochre-mu | `/home/charlielidbury/repos/ochre-mu` | μ exploration | Zero sorrys ✓ |

## Next Steps (for morning)

1. **Check agent result**: synth/app soundness sorrys in research-D
2. **Step-indexed soundness for cycle detection**: the 2 fundamental sorrys
3. **Decide architecture**: merge algorithm to main? Keep declarative + algo separate?
4. **BetaR**: explore normalization-based transitivity once μ is settled
