# Och

## Syntax

```
e, τ ::=
  | x              — variable
  | λx:τ. e        — lambda (domain-annotated)
  | e₁ e₂          — application
  | (e : τ)        — ascription
  | ⊤              — top type / universe
  | μs:τ. e        — self-reference (s = self)
```

Terms and types share a single syntactic category — there is no separate type language.

## absEval: Γ ⊢ e ⇝ v : τ

Bidirectional judgment: in context Γ, expression e evaluates to normal form v with synthesized type τ. In a terms=types system, v and τ are often identical (e.g. for lambdas).

## Normal Form: nf(Γ, e)

An expression is in normal form relative to a context Γ when it is well-scoped, contains no ascriptions, and has no beta-redexes. Defined inductively:

```
nf(Γ, x)                       -- Var (x ∈ Γ)
  x : _ ∈ Γ

nf(Γ, ⊤)                    -- ⊤

nf(Γ, λx:D. b)                 -- Lam
  nf(Γ, D)
  nf(Γ, x:D, b)

nf(Γ, μs:A. b)                 -- Mu
  nf(Γ, A)
  nf(Γ, s:μs:A.b, b)

nf(Γ, f a)                     -- App (f not lam)
  nf(Γ, f)
  nf(Γ, a)
  f ≠ λ_._ 
```

Notes:
- **Var:** The scope check `x ∈ Γ` is critical. absEval returns variables verbatim without looking them up in Γ — if the variable is not in scope, the synthesized type would be meaningless. The check is not in absEval itself; it's an invariant on the input that must hold.
- **Asc:** No rule — ascriptions are erased by absEval, so normal forms never contain them.
- **App:** Excludes `f = λ_._` which would be a beta-redex. `f = μ_._` is allowed (mu in head position is not a redex — it may or may not unfold depending on the seen set).

## Context (Γ)

Γ is a list of bindings `x : D` where D is a normal form (output of absEval). `Γ(x)` denotes the domain type bound to variable x.

**Extend:** `Γ, x:D` adds a new binding. Every entry's type is a normal form.

## Var
```
Γ ⊢ x ⇝ x : Γ(x)
  x ∈ Γ
```

## ⊤
```
Γ ⊢ ⊤ ⇝ ⊤ : ⊤
```

## Lam
```
Γ ⊢ λx:D. b ⇝ λx:D'. b' : λx:D'. b'
  Γ ⊢ D ⇝ D' : _
  Γ, x:D' ⊢ b ⇝ b' : _
```
Self-typing: in a terms=types system, a lambda is its own type.

## Asc
```
Γ ⊢ (e : τ) ⇝ τ' : τ'
  Γ ⊢ e ⇝ σ : _
  Γ ⊢ τ ⇝ τ' : _
  Γ ⊢ σ ⊑ τ'
```
Ascription erases term, returns evaluated type. Subtype check must pass.

## Mu
```
Γ ⊢ μs:A. b ⇝ μs:A. b : A'
  Γ ⊢ A ⇝ A' : _          -- annotation well-formed
```
Mu returned verbatim. Annotation is the synthesized type.

## App-Lam
```
Γ ⊢ f a ⇝ r : τ_r
  Γ ⊢ f ⇝ λx:D. b : _
  Γ ⊢ a ⇝ a' : _
  Γ ⊢ a' ⊑ D              -- domain check
  Γ ⊢ b[x↦a'] ⇝ r : τ_r  -- beta-reduce then eval
```

## App-Mu (annotated function)
When mu has function-type annotation `λx:D. R` and lam body:
```
Γ ⊢ f a ⇝ r : τ_r
  Γ ⊢ f ⇝ μs:(λx:D. R). λy:_. _ : _
  Γ ⊢ a ⇝ a' : _
  Γ ⊢ R[x↦a'] ⇝ r : τ_r  -- use annotation's return type
```
Trusts annotation, avoids normalizing raw body.

## App-Mu (unannotated, lam body, not seen)
```
Γ ⊢ f a ⇝ r : τ_r
  Γ ⊢ f ⇝ μs:A. λx:D. b : _     -- where A not a lam
  Γ ⊢ a ⇝ a' : _
  μs:A. λx:D. b ∉ seen
  Γ ⊢ₛ b[s↦μs:A. λx:D. b][x↦a'] ⇝ r : τ_r
```
(⊢ₛ means seen list extended with the mu to break cycles)

## App-Mu (seen — cycle break)
```
Γ ⊢ f a ⇝ (μs:A. b) a' : ⊤
  Γ ⊢ f ⇝ μs:A. b : _
  Γ ⊢ a ⇝ a' : _
  μs:A. b ∈ seen              -- cycle detected, stop unfolding
```
Type is ⊤ (unknown) at cycle break.

## App-Mu (non-lam body)
```
Γ ⊢ f a ⇝ b[s↦μs:A. b] a' : ⊤
  Γ ⊢ f ⇝ μs:A. b : _        -- b not a lam
  Γ ⊢ a ⇝ a' : _
```
Substitute self-ref but don't beta-reduce. Type is ⊤ (unknown).

## App-Neutral
```
Γ ⊢ f a ⇝ f' a' : R[x↦a']
  Γ ⊢ f ⇝ f' : λx:D. R       -- τ_f must be a function type
  Γ ⊢ a ⇝ a' : _
```
Callability determined by synthesized type of f'. If τ_f is not a function type, error.

## App-⊤ (error)
```
Γ ⊢ ⊤ a ⇝ ✗            -- "⊤ is not callable"
```
