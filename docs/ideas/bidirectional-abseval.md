# Bidirectional absEval: Consolidate 4 Mechanisms into 2

## Problem

Och currently has 4 separate mechanisms for type-level reasoning:

1. **absEval** `Γ ⊢ e ⇝ v` — normalization
2. **subCheckNF** `Γ ⊢ a ⊑ b` — subtype checking
3. **inferType** — type inference for neutral terms (bvar, app)
4. **isCallableNF** — checks if a neutral term is callable

These are ad-hoc and poorly connected. `inferType` is a one-hop context
lookup that can't chase variable chains. For example, this fails:

```
λ(not: Bool → Bool). λ(a: not). λ(b: a). b true
```

`b : a`, `a : not`, `not : Bool → Bool`. To see `b` is callable requires
3 hops through the context. `inferType` does 1.

`inferType` is also used as a fallback in `subCheckNF` — when structural
matching fails on a neutral LHS, it infers its type and retries. Same
one-hop limitation applies there.

## Proposal

Consolidate into 2 mechanisms by applying bidirectional type checking.

### 1. absEval returns (value, type): `Γ ⊢ e ⇝ v : τ`

Every evaluation produces both a normal form and its type. Since Och has
terms = types, the type is often the value itself:

```
Γ ⊢ x ⇝ x : Γ(x)                     -- type from context

Γ ⊢ ⊤ ⇝ ⊤ : ⊤                        -- self-typing

Γ ⊢ λx:D. b ⇝ λx:D'. b' : λx:D'. b'  -- self-typing

Γ ⊢ μs:A. b ⇝ μs:A. b : A             -- annotation is the type

Γ ⊢ (e : τ) ⇝ τ' : τ'                 -- ascription
  Γ ⊢ e ⇝ σ : _
  Γ ⊢ τ ⇝ τ' : _
  Γ ⊢ σ ⊑ τ'

Γ ⊢ f a ⇝ r : τ_r
  Γ ⊢ f ⇝ f' : τ_f
  Γ ⊢ a ⇝ a' : _
  -- τ_f determines what happens next:
  -- τ_f = λx:D. B  →  check a' ⊑ D, result type B[x↦a']
  -- τ_f = μ_._     →  existing mu app logic
  -- otherwise       →  error: not callable
```

The App case uses `τ_f` directly — **inferType is eliminated**. Its job is
done by the type component flowing through evaluation.

**isCallableNF is also eliminated** — just pattern match on `τ_f`.

### 2. subCheckNF gets a proper variable rule

Instead of the ad-hoc inferType fallback, add:

```
Γ ⊢ x ⊑ b
  Γ(x) = σ
  Γ ⊢ σ ⊑ b
```

A variable is a subtype of `b` if its declared type is. This naturally
chains through multiple variables — the multi-hop problem resolves by
recursion, no special handling needed.

The app fallback becomes:

```
Γ ⊢ f a ⊑ b
  Γ ⊢ f a ⇝ _ : τ
  Γ ⊢ τ ⊑ b
```

Synthesize the type, then check that against `b`.

## What Gets Eliminated

| Before | After |
|--------|-------|
| absEval | absEval (returns type too) |
| subCheckNF | subCheckNF (with variable rule) |
| inferType | **eliminated** |
| isCallableNF | **eliminated** |

## Precedent

This is standard in modern type checkers (GHC, Rust, Lean). The classic
reference is Dunfield & Krishnaswami, "Bidirectional Typing" (2021).

## Considerations

- **Overhead:** Minimal. In a terms=types system, the type of a value is
  often itself (lam, ⊤). Only variables and neutral apps carry genuinely
  different type info.
- **Proof impact:** The soundness proof currently has extensive case analysis
  for inferType fallbacks in subCheckNF. Replacing those with a single
  variable rule should simplify things significantly.
- **Context type:** `TyCtx` stays the same — still a list of domain types.
  The difference is that absEval *produces* types, not that the context
  stores more.
