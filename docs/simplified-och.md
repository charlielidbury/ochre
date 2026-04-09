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

## Context (Γ)

Γ is a list of bindings `x : T`. Entry `x : T` means x is **at most** T. `Γ(x)` denotes the type bound to x.

## Subtype: Γ ⊢ a ⊑ b

Single relation: a is a subtype of b in context Γ.

```
[Refl]
Γ ⊢ a ⊑ a

[Top]
Γ ⊢ a ⊑ ⊤

[Var]
Γ ⊢ x ⊑ b
  Γ(x) = T
  Γ ⊢ T ⊑ b

[Lam]
Γ ⊢ λx:A. B ⊑ λx:A'. B'
  Γ ⊢ A' ⊑ A                   -- contravariant in domain
  Γ, x:A' ⊢ B ⊑ B'            -- covariant in body

[App]
Γ ⊢ f a ⊑ b
  Γ ⊢ f ⊑ λx:D. R              -- f is callable
  Γ ⊢ a ⊑ D                    -- domain check
  Γ ⊢ R[x := a] ⊑ b            -- result check

[Asc-L]
Γ ⊢ (e : τ) ⊑ b
  Γ ⊢ e ⊑ τ                    -- validate ascription
  Γ ⊢ τ ⊑ b                    -- reduce to type

[Asc-R]
Γ ⊢ a ⊑ (e : τ)
  Γ ⊢ e ⊑ τ                    -- validate ascription
  Γ ⊢ a ⊑ e                    -- check against the value, not the type
```

Notes:
- **[Var]** only unfolds variables on the LHS. The RHS stays opaque — widening the bound would be unsound. [App] handles decomposition of nested applications down to the head variable, so bare-variable [Var] suffices.
- **[App]** checks `f ⊑ λx:D. R` to determine callability and extract the domain/return type. D and R are existentially quantified — determined by whatever lambda f reduces to via [Var], [App], [Asc-L], or [Refl]. This is type synthesis embedded in subtyping.
- **[Asc]** erases the term, keeping the type.
- **Well-formedness** is not checked separately. The system is a checker: you always check a program against a type, e.g. `∅ ⊢ program ⊑ expected_type`.

## Example: ID

```
BOOL  = λt:⊤. λa:t. λb:t. t
TRUE  = λt:⊤. λa:t. λb:t. a
FALSE = λt:⊤. λa:t. λb:t. b
ID    = λb:BOOL. (b BOOL TRUE FALSE : BOOL)
```

Goal: `∅ ⊢ ID ⊑ λb:BOOL. BOOL`

```
[Lam] ∅ ⊢ ID ⊑ λb:BOOL. BOOL
  [Refl] ∅ ⊢ BOOL ⊑ BOOL
  [Asc-L] b:BOOL ⊢ (b BOOL TRUE FALSE : BOOL) ⊑ BOOL
    b:BOOL ⊢ b BOOL TRUE FALSE ⊑ BOOL                     -- see (A)
    [Refl] b:BOOL ⊢ BOOL ⊑ BOOL
```

**(A)** `b:BOOL ⊢ b BOOL TRUE FALSE ⊑ BOOL`

Each [App] checks the head is callable, checks the argument, and substitutes into the return type:

```
[App] b:BOOL ⊢ b BOOL TRUE FALSE ⊑ BOOL
  [App] b:BOOL ⊢ (b BOOL) TRUE ⊑ λb:BOOL. BOOL
    [App] b:BOOL ⊢ b BOOL ⊑ λa:BOOL. λb:BOOL. BOOL
      [Var] b:BOOL ⊢ b ⊑ BOOL                             -- b : BOOL ∈ Γ
        [Refl] b:BOOL ⊢ BOOL ⊑ BOOL
      [Top] b:BOOL ⊢ BOOL ⊑ ⊤                             -- a ⊑ D
      [Refl] b:BOOL ⊢ λa:BOOL. λb:BOOL. BOOL ⊑ λa:BOOL. λb:BOOL. BOOL
    b:BOOL ⊢ TRUE ⊑ BOOL                                  -- see (B)
    [Refl] b:BOOL ⊢ λb:BOOL. BOOL ⊑ λb:BOOL. BOOL
  b:BOOL ⊢ FALSE ⊑ BOOL                                   -- see (C)
  [Refl] b:BOOL ⊢ BOOL ⊑ BOOL
```

**(B)** `b:BOOL ⊢ TRUE ⊑ BOOL` — i.e. `λt:⊤. λa:t. λb:t. a ⊑ λt:⊤. λa:t. λb:t. t`

```
[Lam] b:BOOL ⊢ TRUE ⊑ BOOL
  [Refl] ⊤ ⊑ ⊤
  [Lam] b:BOOL, t:⊤ ⊢ λa:t. λb:t. a ⊑ λa:t. λb:t. t
    [Refl] t ⊑ t
    [Lam] b:BOOL, t:⊤, a:t ⊢ λb:t. a ⊑ λb:t. t
      [Refl] t ⊑ t
      [Var] b:BOOL, t:⊤, a:t, b:t ⊢ a ⊑ t                -- a : t ∈ Γ
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
      [Var] b:BOOL, t:⊤, a:t, b:t ⊢ b ⊑ t                -- b : t ∈ Γ (inner b shadows)
        [Refl] t ⊑ t
```

## Concrete Semantics: γ ⊢ e → v

Concrete evaluation under environment γ (mapping variables to closed values). Domain annotations and ascriptions are erased — no type checking at runtime.

```
[Var]
γ ⊢ x → γ(x)

[⊤]
γ ⊢ ⊤ → ⊤

[Lam]
γ ⊢ λx:D. b → λx. b[γ]          -- erase domain, close over environment

[App]
γ ⊢ f a → r
  γ ⊢ f → λx. body
  γ, x:a ⊢ body → r              -- call-by-name: substitute unevaluated a

[Asc]
γ ⊢ (e : τ) → v
  γ ⊢ e → v                      -- ascription erased, return the value
```

Note: `(e : τ)` returns the **value** of e concretely, but returns **τ** abstractly. The abstract system discards precision; concrete execution preserves it.

## Soundness (machine-checked in Lean 4)

All proofs are in `lean/Och/Simple/` with zero sorrys.

### Part 1: Semantic substitution

**Compatibility:** γ ⊨ Γ (inductively) if for each `x : T ∈ Γ`, `Γ_rest ⊢ γ(x) ⊑ T` where Γ_rest is the remaining context.

**Theorem:** If `Γ ⊢ e ⊑ τ` and `γ ⊨ Γ`, then `∅ ⊢ γ(e) ⊑ γ(τ)`.

*Proof:* Induction on compatibility, applying the substitution lemma at each step.

### Part 2: Eval preservation

**Theorem:** If `∅ ⊢ e ⊑ τ` and `eval fuel e = v` and `eval fuel' τ = w`, then `∅ ⊢ v ⊑ w`.

*Proof:* Strong induction on `fuel + fuel'`. Key techniques:
- **Lambda inversion** at empty context (only [Refl] and [Lam] produce Sub [] (lam..) (lam..))
- **Call-by-name** evaluation aligns concrete beta-reduction with the substitution lemma
- **Asymmetric fuel** allows e and τ to consume different amounts of fuel

### Prerequisites (all proved)
- *Substitution lemma*: If `T::Γ ⊢ a ⊑ b` and `Γ ⊢ v ⊑ T`, then `Γ ⊢ a[0:=v] ⊑ b[0:=v]`.
- *Transitivity*: If `Γ ⊢ a ⊑ b` and `Γ ⊢ b ⊑ c`, then `Γ ⊢ a ⊑ c`. (Via cut-formula lexicographic measure, mutual with narrowing.)
