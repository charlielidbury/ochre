# Lemma 2 diagnosis — the real wall

## The wall, precisely

The wall is **specific to ProVar/VarPro** because of Me-Var's universal NP-triviality.

The bidirectional asymmetric Moreover predicate has shape:
```
∀ (x : Nat),
  (h₁.NP-x → d₂.NP-x) ∧
  (h₂.NP-x → d₁.NP-x)
```

When `h₂ = Me-Var`, `h₂.NP-x = True` for **all** x (Me-Var doesn't promote anything). The reverse direction `h₂.NP-x → d₁.NP-x` therefore demands `d₁.NP-x` universally over Nat.

In ProVar, `d₁` is built from a **constructed lifted derivation** via `equBinds_evolve + lift_empty_to_stack`. The lifted's Me-Pro indices come from the evolution's `ctAnn` carriers — arbitrary `MEqRed Γ_inner [] t t'` terms that can promote any index. So `lifted.NP-x` is **not** universally true.

In the named-binder version of the paper, alpha-equivariance picks a fresh x outside the evolution's carriers, making lifted.NP-x vacuously true. **De Bruijn has no fresh-x pump** — every Nat is in the same namespace as the carriers' indices.

## Why this isn't a problem for other cells

For FunFun, AppBet, BetBet, FOpFOp, AppApp, etc., **both sources are real sub-derivations with real NP profiles**. The reverse Moreover's `h₂.NP-x` decomposes via structural induction (e.g., `h₂ = Me-Fun` has NP-x = `hT.NP-x ∧ hBody.NP-(x+1)` which gives real witnesses). The recursive call's NP needs are then derivable.

ProVar/VarPro are the only cells where:
- One source (Me-Var) is universally NP-trivial.
- The other source (Me-Pro) requires constructing a synthetic second derivation (lifted) for the recursive IH.

The combination is what produces the wall.

## The "fresh-x pump" issue in detail

In named binders:
- Variables form a countable infinite set.
- For any finite context Γ, infinitely many variables x ∉ Γ.
- A derivation's Me-Pro promotions all reference variables ∈ Γ (Me-Pro looks up in context).
- So any x fresh from Γ is automatically NP-x for the derivation.

In de Bruijn:
- Variables are Nats.
- Me-Pro promotes index i where `Γ.equBinds i α` — i is bounded by Γ.depth.
- For x ≥ Γ.depth, the derivation can't promote x (no equ-binding at that index).
- For x < Γ.depth, the derivation might or might not promote x.

So de Bruijn DOES have a fresh-x analog: **x ≥ Γ_0.depth is NP-vacuous**. The catch is that the bundle's recursion at binder cells SHIFTS to x+1 in the body context (Γ.depth + 1), and the recursion's IH at body level operates over x where x ≥ body.depth. Pulling this back to outer levels via the binder shifts, the consumers ask for NP at various indices.

For the bundle's actual call site (UniformEqDiamonds at ctRefl/ctRefl), the lifted IS refl, so lifted.NP-x is universally True. No wall at top level.

The wall is **internal** to the bundle's recursion at non-trivial evolutions.

## Fix space

### Option 1: Restrict the predicate's ∀ x to x ≥ Γ₀.depth

The Moreover's universal claim becomes "for indices unreachable in this context," which lifted respects. But consumers (AppBet body IH) ask at x = 0, 1, ... (small indices) — incompatible with x ≥ depth.

**Verdict:** doesn't compose.

### Option 2: Drop reverse direction entirely

Use only `h₁.NP-x → d₂.NP-x`. AppBet (and others) use both directions; replacing with one breaks their inline proofs.

**Verdict:** can't drop without rewriting all cells.

### Option 3: Parametric x with consumer-specific obligations

Make x an outer parameter (not ∀): `MoreoverDiamond x h₁ h₂`. Consumers ask for Moreover at specific x's. Wall at ProVar disappears for the x's consumers actually ask.

**Verdict:** plausible. Substantial refactor (~1500 lines). Need to:
- Redesign predicate signature.
- Re-prove all 13 cells with x as parameter (some cells take x, some take x+1 via binder shifts).
- Restructure bundle recursion to track x.
- Update consumers (UniformEqDiamonds projection becomes x-erased).

### Option 4: Parallel reduction (Tait-Martin-Löf)

Define a parallel reduction relation `⟹` that's diamond-by-construction (no Moreover). Prove `→*ᵉᵠᵘ = ⟹*`. Standard confluence technique.

**Verdict:** sidesteps Moreover entirely. Deviates from paper structure. Possibly faster than Option 3.

### Option 5: Accept the 4 payloads as paper-faithful documentation

The paper's universal-x Moreover is genuinely too strong in de Bruijn. Document the gap. Wrapper remains conditional on 4 payloads.

**Verdict:** paper-faithful but doesn't close.

## Recommendation

**Option 3** if we want to close while keeping the paper's structural argument. **Option 4** if we're willing to deviate but want a cleaner close.
