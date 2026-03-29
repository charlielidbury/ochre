# Problem

Layer 1: Subtyping

Task 1.1: Define the subtyping relation ⊑ on terms. Given two terms τ₁ and τ₂, define when τ₁ ⊑ τ₂ holds. Must handle: reflexivity, transitivity, pointwise function subtyping (contravariant input, covariant output), and Type. Verification: the relation must satisfy true ⊑ Bool, false ⊑ Bool, 3 ⊑ Nat, true ⋢ Nat, succ 2 ⋢ 2, unit ⊑ Unit, and Pair Nat Bool ⋢ Pair Bool Nat (these are directly from the test case §6.3). Write out the derivation tree for each.

Task 1.2: Verify subtyping for compound types. Using the relation from 1.1, derive: emptyArray Nat ⊑ Array 0 Nat, consArray Nat 0 10 (emptyArray Nat) ⊑ Array 1 Nat, emptyArray Nat ⋢ Array 1 Nat, and consArray Nat 0 10 (emptyArray Nat) ⋢ Array 2 Nat. These require β-reduction of Array followed by subtyping. Verification: produce derivation trees. This task depends on 1.1.

Task 1.3: Verify subtyping for dependent types. Derive: dpair Nat (λ(n: Nat). Array n Nat) 2 arr ⊑ Vec Nat for a concrete arr : Array 2 Nat. This exercises dependent pair subtyping where the second component's type depends on the first. Verification: produce the derivation tree. Depends on 1.1 and 1.2.

# Solution

## Subtyping Rules

All terms are compared modulo β-equivalence. In derivations, we freely β-reduce
before applying rules.

```
[Refl]
Γ ⊢ e ⊑ e

[Var]
Γ ⊢ x ⊑ T
  x : T ∈ Γ

[Lam]
Γ ⊢ λ(x:A₁).B₁ ⊑ λ(x:A₂).B₂
  Γ ⊢ A₂ ⊑ A₁
  Γ, x:A₂ ⊢ B₁ ⊑ B₂

[App]
Γ ⊢ f a ⊑ B[x := a]
  Γ ⊢ f ⊑ λ(x:A).B
  Γ ⊢ a ⊑ A

[Trans]
Γ ⊢ A ⊑ C
  Γ ⊢ A ⊑ B
  Γ ⊢ B ⊑ C

[Top]
Γ ⊢ τ ⊑ Type
```

Notes:
- **Lam** uses `x : A₂` (the supertype's domain) in the context when checking
  bodies. This captures "for all x ⊑ A₂, B₁ ⊑ B₂". Since A₂ ⊑ A₁ (contra),
  B₁ remains well-formed under x : A₂.
- **App** is needed for irreducible applications like `s z` where `s` is a
  variable of function type. It lets us conclude `s z ⊑ X` from `s ⊑ λ(_:X).X`
  and `z ⊑ X`.
- **Refl** covers `Type ⊑ Type` as a special case (subsumed by Top, but
  Refl is still needed for non-Type reflexive judgments).
- **Top** says every term is a member of `Type`. This follows from the
  terms-as-types philosophy: every term is a type (at minimum a singleton set),
  so every term is in the universe.

## Task 1.1: Basic Subtyping

### true ⊑ Bool

Expanding: `λ(X:Type).λ(t:X).λ(f:X).t  ⊑  λ(X:Type).λ(t:X).λ(f:X).X`

```
λ(X:Type).λ(t:X).λ(f:X).t ⊑ λ(X:Type).λ(t:X).λ(f:X).X -- Lam
  Type ⊑ Type -- Refl
  λ(t:X).λ(f:X).t ⊑ λ(t:X).λ(f:X).X -- Lam [X:Type]
    X ⊑ X -- Refl
    λ(f:X).t ⊑ λ(f:X).X -- Lam [X:Type, t:X]
      X ⊑ X -- Refl
      t ⊑ X -- Var [X:Type, t:X, f:X]
```

### false ⊑ Bool

Expanding: `λ(X:Type).λ(t:X).λ(f:X).f  ⊑  λ(X:Type).λ(t:X).λ(f:X).X`

```
λ(X:Type).λ(t:X).λ(f:X).f ⊑ λ(X:Type).λ(t:X).λ(f:X).X -- Lam
  Type ⊑ Type -- Refl
  λ(t:X).λ(f:X).f ⊑ λ(t:X).λ(f:X).X -- Lam [X:Type]
    X ⊑ X -- Refl
    λ(f:X).f ⊑ λ(f:X).X -- Lam [X:Type, t:X]
      X ⊑ X -- Refl
      f ⊑ X -- Var [X:Type, t:X, f:X]
```

### 3 ⊑ Nat

Expanding: `λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s(s z))  ⊑  λ(X:Type).λ(z:X).λ(s:λ(_:X).X). X`

```
λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(s(s z)) ⊑ λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X -- Lam
  Type ⊑ Type -- Refl
  λ(z:X).λ(s:λ(_:X).X).s(s(s z)) ⊑ λ(z:X).λ(s:λ(_:X).X).X -- Lam [X:Type]
    X ⊑ X -- Refl
    λ(s:λ(_:X).X).s(s(s z)) ⊑ λ(s:λ(_:X).X).X -- Lam [X:Type, z:X]
      λ(_:X).X ⊑ λ(_:X).X -- Refl
      s(s(s z)) ⊑ X -- App [X:Type, z:X, s:λ(_:X).X]
        s ⊑ λ(_:X).X -- Var
        s(s z) ⊑ X -- App
          s ⊑ λ(_:X).X -- Var
          s z ⊑ X -- App
            s ⊑ λ(_:X).X -- Var
            z ⊑ X -- Var
```

### unit ⊑ Unit

Expanding: `λ(X:Type).λ(x:X).x  ⊑  λ(X:Type).λ(x:X).X`

```
λ(X:Type).λ(x:X).x ⊑ λ(X:Type).λ(x:X).X -- Lam
  Type ⊑ Type -- Refl
  λ(x:X).x ⊑ λ(x:X).X -- Lam [X:Type]
    X ⊑ X -- Refl
    x ⊑ X -- Var [X:Type, x:X]
```

### true ⋢ Nat

Expanding: `λ(X:Type).λ(t:X).λ(f:X).t  ⊑  λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X`

The only applicable rule is Lam. The first two parameters have identical
annotations (Type, then X), so the contra checks pass. At the third parameter:

- Subtype (true) has `f : X`
- Supertype (Nat) has `s : λ(_:X).X`

The contra check requires `λ(_:X).X ⊑ X`. No rule derives this:
- Not Refl (different terms)
- Not Var (`λ(_:X).X` is not a variable)
- Not Lam (`X` is not a lambda)
- Not App (`λ(_:X).X` is not an application)
- Trans cannot help: any intermediate term B would need both `λ(_:X).X ⊑ B`
  and `B ⊑ X`, but nothing in the context provides information about what is
  in `X` beyond what Var gives us.

Derivation gets stuck. ∎

### succ 2 ⋢ 2

β-reducing: `succ 2 =β 3 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s(s z))`

So this reduces to `3 ⊑ 2`:

`λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s(s z))  ⊑  λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s z)`

By Lam (three times, all contra checks pass by Refl), the body check under
context `[X:Type, z:X, s:λ(_:X).X]` requires:

`s(s(s z)) ⊑ s(s z)`

Both sides are irreducible applications. No rule applies:
- Not Refl (structurally different)
- Not Var (neither is a variable)
- Not Lam (neither is a lambda)
- App could derive `s(s(s z)) ⊑ X`, but we need `⊑ s(s z)`, not `⊑ X`
- Trans: any intermediate B would need `s(s(s z)) ⊑ B ⊑ s(s z)`. The only
  type we can derive for `s(s(s z))` via App is `X`, but `X ⊑ s(s z)` is not
  derivable (would need `s(s z)` to be a supertype of `X`, but `s(s z) ⊑ X`,
  not the reverse).

Derivation gets stuck. ∎

### Pair Nat Bool ⋢ Pair Bool Nat

β-reducing both sides:
- `Pair Nat Bool =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Bool).X).X`
- `Pair Bool Nat =β λ(X:Type).λ(k:λ(_:Bool).λ(_:Nat).X).X`

By Lam, the first parameter (Type) passes by Refl. The second parameter contra
check requires:

`λ(_:Bool).λ(_:Nat).X  ⊑  λ(_:Nat).λ(_:Bool).X`

Applying Lam, the contra check on the first parameter requires `Nat ⊑ Bool`:

`λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X  ⊑  λ(X:Type).λ(t:X).λ(f:X).X`

By Lam (first two params pass), the third parameter contra check requires
`X ⊑ λ(_:X).X`. No rule derives this:
- Not Refl (different terms)
- Not Var (derives `X ⊑ Type`, not `X ⊑ λ(_:X).X`)
- Not Lam (`X` is not a lambda)
- Not App (`X` is not an application)

Derivation gets stuck. ∎


## Task 1.2: Compound Type Subtyping

### emptyArray Nat ⊑ Array 0 Nat

β-reducing both sides:
- `emptyArray Nat =β unit = λ(X:Type).λ(x:X).x`
- `Array 0 Nat =β 0 Type Unit (λ(acc:Type). Pair Nat acc) =β Unit = λ(X:Type).λ(x:X).X`

This reduces to `unit ⊑ Unit`, derived in Task 1.1:

```
unit ⊑ Unit -- Lam (after β)
  Type ⊑ Type -- Refl
  λ(x:X).x ⊑ λ(x:X).X -- Lam [X:Type]
    X ⊑ X -- Refl
    x ⊑ X -- Var [X:Type, x:X]
```

### consArray Nat 0 10 (emptyArray Nat) ⊑ Array 1 Nat

β-reducing both sides:
- `consArray Nat 0 10 (emptyArray Nat)`
  `=β pair Nat (Array 0 Nat) 10 (emptyArray Nat)`
  `=β pair Nat Unit 10 unit`
  `=β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 10 unit`
- `Array 1 Nat =β Pair Nat Unit =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). X`

```
λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 10 unit
  ⊑ λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). X -- Lam
  Type ⊑ Type -- Refl
  λ(k:λ(_:Nat).λ(_:Unit).X). k 10 unit
    ⊑ λ(k:λ(_:Nat).λ(_:Unit).X). X -- Lam [X:Type]
    λ(_:Nat).λ(_:Unit).X ⊑ λ(_:Nat).λ(_:Unit).X -- Refl
    k 10 unit ⊑ X -- App [X:Type, k:λ(_:Nat).λ(_:Unit).X]
      k 10 ⊑ λ(_:Unit).X -- App
        k ⊑ λ(_:Nat).λ(_:Unit).X -- Var
        10 ⊑ Nat -- (same structure as 3 ⊑ Nat)
      unit ⊑ Unit -- (derived in 1.1)
```

### emptyArray Nat ⋢ Array 1 Nat

β-reducing:
- `emptyArray Nat =β unit = λ(X:Type).λ(x:X).x`
- `Array 1 Nat =β Pair Nat Unit =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X).X`

By Lam, the first parameter (Type) passes. The second parameter contra check
requires:

`λ(_:Nat).λ(_:Unit).X  ⊑  X`

No rule derives this: a lambda cannot be shown to be a subtype of an abstract
variable `X`. Same failure pattern as in `true ⋢ Nat`. ∎

### consArray Nat 0 10 (emptyArray Nat) ⋢ Array 2 Nat

β-reducing:
- LHS `=β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 10 unit`
- `Array 2 Nat =β Pair Nat (Pair Nat Unit) =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat Unit).X).X`

By Lam, the first parameter passes. The second parameter contra check requires:

`λ(_:Nat).λ(_:Pair Nat Unit).X  ⊑  λ(_:Nat).λ(_:Unit).X`

By Lam, the first inner parameter passes (Nat ⊑ Nat). The second inner
parameter contra check requires:

`Unit ⊑ Pair Nat Unit`

Expanding: `λ(X:Type).λ(x:X).X  ⊑  λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X).X`

By Lam, the first parameter passes. The second parameter contra check requires:

`λ(_:Nat).λ(_:Unit).X  ⊑  X`

Same failure as above: lambda ⋢ abstract variable. ∎


## Task 1.3: Dependent Type Subtyping

### dpair Nat (λ(n:Nat). Array n Nat) 2 arr ⊑ Vec Nat

where `arr : Array 2 Nat`.

β-reducing both sides:
- `dpair Nat (λ(n:Nat). Array n Nat) 2 arr`
  `=β λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 2 arr`
- `Vec Nat = Sigma Nat (λ(n:Nat). Array n Nat)`
  `=β λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X`

The key feature: the parameter annotation `λ(_:Array a Nat).X` depends on `a`.
When we apply `k` to `2`, the substitution `a := 2` produces `Array 2 Nat`.

```
λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 2 arr
  ⊑ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X -- Lam
  Type ⊑ Type -- Refl
  λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 2 arr
    ⊑ λ(k:λ(a:Nat).λ(_:Array a Nat).X). X -- Lam [X:Type]
    λ(a:Nat).λ(_:Array a Nat).X ⊑ λ(a:Nat).λ(_:Array a Nat).X -- Refl
    k 2 arr ⊑ X -- App [X:Type, k:λ(a:Nat).λ(_:Array a Nat).X]
      k 2 ⊑ λ(_:Array 2 Nat).X -- App (substituting a:=2)
        k ⊑ λ(a:Nat).λ(_:Array a Nat).X -- Var
        2 ⊑ Nat -- (same structure as 3 ⊑ Nat)
      arr ⊑ Array 2 Nat -- Var (arr : Array 2 Nat)
```

The dependent substitution is the critical step: App on `k 2` substitutes
`a := 2` into the return type `λ(_:Array a Nat).X`, yielding `λ(_:Array 2 Nat).X`.
This allows the second App to check `arr ⊑ Array 2 Nat`, which holds by Var.
