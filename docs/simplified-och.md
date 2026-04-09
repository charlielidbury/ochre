# Och

## Syntax

```
e, τ ::=
  | x              — variable
  | λx:τ. e        — lambda (domain-annotated)
  | e₁ e₂          — application
  | (e : τ)        — ascription
  | ⊤              — top type / universe
```

Terms and types share a single syntactic category — there is no separate type language.

## Normal Form: nf(Γ, e)

An expression is in normal form relative to a context Γ when it is well-scoped, contains no ascriptions, and has no beta-redexes. Defined inductively:

```
nf(Γ, x)                       -- Var (x ∈ Γ)
  x : _ ∈ Γ

nf(Γ, ⊤)                    -- ⊤

nf(Γ, λx:D. b)                 -- Lam
  nf(Γ, D)
  nf(Γ, x:D, b)

nf(Γ, f a)                     -- App (f not lam)
  nf(Γ, f)
  nf(Γ, a)
  f ≠ λ_._ 
```

Notes:
- **Var:** The scope check `x ∈ Γ` is critical. absEval returns variables verbatim without looking them up in Γ — if the variable is not in scope, the synthesized type would be meaningless. The check is not in absEval itself; it's an invariant on the input that must hold.
- **Asc:** No rule — ascriptions are erased by absEval, so normal forms never contain them.
- **App:** Excludes `f = λ_._` which would be a beta-redex.

## Context (Γ)

Γ is a list of bindings `x : D` where D is a normal form (output of absEval). `Γ(x)` denotes the domain type bound to variable x.

**Extend:** `Γ, x:D` adds a new binding. Every entry's type is a normal form.

## absEval: Γ ⊢ e ⇝ v

In context Γ, expression e evaluates to normal form v.

```
[Var]
Γ ⊢ x ⇝ x
  x ∈ Γ

[⊤]
Γ ⊢ ⊤ ⇝ ⊤

[Lam]
Γ ⊢ λx:D. b ⇝ λx:D'. b'
  Γ ⊢ D ⇝ D'
  Γ, x:D' ⊢ b ⇝ b'

[Asc]
Γ ⊢ (e : τ) ⇝ τ'
  Γ ⊢ e ⇝ σ
  Γ ⊢ τ ⇝ τ'
  Γ ⊢ σ ⊑ τ'

[App-Lam]
Γ ⊢ f a ⇝ r
  Γ ⊢ f ⇝ λx:D. b
  Γ ⊢ a ⇝ a'
  Γ ⊢ a' ⊑ D              -- domain check
  Γ ⊢ b[x↦a'] ⇝ r        -- beta-reduce then eval

[App-Neutral]
Γ ⊢ f a ⇝ f' a'
  Γ ⊢ f ⇝ f'
  f' ≠ λ_._                   -- not a redex
  Γ ⊢ a ⇝ a'
```

## Subtype: Γ ⊢ a ⊑ b

Both a and b are normal forms. Judgment holds when a is a subtype of b in context Γ.

```
[Refl]
Γ ⊢ a ⊑ a

[Var]
Γ ⊢ M ⊑ N
  x : T ∈ Γ
  Γ ⊢ M[x := T] ⇝ M'
  Γ ⊢ M' ⊑ N

[Top]
Γ ⊢ a ⊑ ⊤

[Lam]
Γ ⊢ λx:A. b₁ ⊑ λx:B. b₂
  Γ ⊢ B ⊑ A                    -- contravariant in domain
  Γ, x:B ⊢ b₁ ⊑ b₂            -- covariant in body
```

## Example: ID

```
BOOL  = λt:⊤. λa:t. λb:t. t
TRUE  = λt:⊤. λa:t. λb:t. a
FALSE = λt:⊤. λa:t. λb:t. b
ID    = λb:BOOL. (b BOOL TRUE FALSE : BOOL)
```

Goal: `∅ ⊢ ID ⇝ λb:BOOL. BOOL`

```
[Lam] ∅ ⊢ ID ⇝ λb:BOOL. BOOL
  ∅ ⊢ BOOL ⇝ BOOL                                        -- normal form
  [Asc] b:BOOL ⊢ (b BOOL TRUE FALSE : BOOL) ⇝ BOOL
    [App-Neutral] b:BOOL ⊢ b BOOL TRUE FALSE ⇝ b BOOL TRUE FALSE
      [App-Neutral] b:BOOL ⊢ (b BOOL) TRUE ⇝ (b BOOL) TRUE
        [App-Neutral] b:BOOL ⊢ b BOOL ⇝ b BOOL
          [Var] b:BOOL ⊢ b ⇝ b
          b:BOOL ⊢ BOOL ⇝ BOOL                            -- normal form
        b:BOOL ⊢ TRUE ⇝ TRUE                              -- normal form
      b:BOOL ⊢ FALSE ⇝ FALSE                              -- normal form
    b:BOOL ⊢ BOOL ⇝ BOOL                                  -- normal form
    [Var] b:BOOL ⊢ b BOOL TRUE FALSE ⊑ BOOL               -- b : BOOL ∈ Γ
      b:BOOL ⊢ BOOL BOOL TRUE FALSE ⇝ BOOL                -- see (A)
      [Refl] b:BOOL ⊢ BOOL ⊑ BOOL
```

**(A)** `b:BOOL ⊢ BOOL BOOL TRUE FALSE ⇝ BOOL`

```
[App-Lam] b:BOOL ⊢ ((BOOL BOOL) TRUE) FALSE ⇝ BOOL
  [App-Lam] b:BOOL ⊢ (BOOL BOOL) TRUE ⇝ λb:BOOL. BOOL
    [App-Lam] b:BOOL ⊢ BOOL BOOL ⇝ λa:BOOL. λb:BOOL. BOOL
      b:BOOL ⊢ BOOL ⇝ λt:⊤. λa:t. λb:t. t               -- normal form
      b:BOOL ⊢ BOOL ⇝ BOOL                                -- normal form
      [Top] b:BOOL ⊢ BOOL ⊑ ⊤                             -- domain check
      b:BOOL ⊢ (λa:t. λb:t. t)[t↦BOOL] ⇝ λa:BOOL. λb:BOOL. BOOL
    b:BOOL ⊢ TRUE ⇝ TRUE                                  -- normal form
    b:BOOL ⊢ TRUE ⊑ BOOL                                  -- domain check, see (B)
    b:BOOL ⊢ (λb:BOOL. BOOL)[a↦TRUE] ⇝ λb:BOOL. BOOL    -- a not free
  b:BOOL ⊢ FALSE ⇝ FALSE                                  -- normal form
  b:BOOL ⊢ FALSE ⊑ BOOL                                   -- domain check, see (C)
  b:BOOL ⊢ BOOL[b↦FALSE] ⇝ BOOL                          -- b shadowed by binder
```

**(B)** `b:BOOL ⊢ TRUE ⊑ BOOL` — i.e. `λt:⊤. λa:t. λb:t. a ⊑ λt:⊤. λa:t. λb:t. t`

```
[Lam] b:BOOL ⊢ TRUE ⊑ BOOL
  [Refl] ⊤ ⊑ ⊤
  [Lam] b:BOOL, t:⊤ ⊢ λa:t. λb:t. a ⊑ λa:t. λb:t. t
    [Refl] t ⊑ t
    [Lam] b:BOOL, t:⊤, a:t ⊢ λb:t. a ⊑ λb:t. t
      [Refl] t ⊑ t
      [Var] b:BOOL, t:⊤, a:t, b:t ⊢ a ⊑ t               -- a : t ∈ Γ
        a[a↦t] = t ⇝ t
        [Refl] t ⊑ t
```

**(C)** `b:BOOL ⊢ FALSE ⊑ BOOL` — i.e. `λt:⊤. λa:t. λb:t. b ⊑ λt:⊤. λa:t. λb:t. t`

```
[Lam] b:BOOL ⊢ FALSE ⊑ BOOL
  [Refl] ⊤ ⊑ ⊤
  [Lam] b:BOOL, t:⊤ ⊢ λa:t. λb:t. b ⊑ λa:t. λb:t. t
    [Refl] t ⊑ t
    [Lam] b:BOOL, t:⊤, a:t ⊢ λb:t. b ⊑ λb:t. t
      [Refl] t ⊑ t
      [Var] b:BOOL, t:⊤, a:t, b:t ⊢ b ⊑ t               -- b : t ∈ Γ (inner b shadows)
        b[b↦t] = t ⇝ t
        [Refl] t ⊑ t
```
