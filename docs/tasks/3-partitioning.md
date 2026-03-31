# Problem

Layer 3: Abstract Inputs and Partitioning
Task 3.1: Define the partitioning mechanism. Formalize how the abstract interpreter handles application of an abstract Church-encoded value to branch arguments. Specifically: when n : Nat (abstract) is applied as n Bool true (λ_. false), define how the interpreter partitions into the true and false branches with narrowed environments. Verification: show that the partition of Nat via isZero produces exactly {0} and {succ k | k : Nat}, and that these are exhaustive.
Task 3.2: Verify typing of abstract test cases. Using the rules from 2.1 and the partitioning from 3.1, derive the judgments for §6.2 (ascribed inputs). Key case: v1 Nat (λ(n: Nat). λ(arr: Array n Nat). n) ⇝ Nat where v1 : Vec Nat is abstract. Verification: derivation trees. Depends on 2.1, 3.1.

# Solution

## Task 3.1: The Partitioning Mechanism

### Motivation

With the rules from Task 2.1, evaluating `n e₁ e₂ e₃` for abstract `n : Nat`
proceeds through Nat's body. Since `Nat = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X`,
the body is just `X` — the type parameter. The App chain substitutes each
argument in turn, but `X`, `z`, and `s` don't appear in `X` (except `X` itself
as the first substitution), so the result is always `e₁'` (the evaluated first
argument). All constructor structure is lost.

For example, `isZero n = n Bool true (λ(_:Bool).false)` evaluates to `Bool`
regardless of whether `n` is `0` or `succ k`. This is sound but imprecise:
we lose the fact that the zero case returns `true` and the succ case returns
`false`.

More critically, `Array n Nat = n Type Unit (λ(acc:Type). Pair Nat acc)`
evaluates to `Type` for abstract `n : Nat`. This makes it impossible to
verify programs that use `Array n Nat` dependently when `n` is abstract.

Partitioning solves this by evaluating each constructor case separately,
with the environment narrowed to reflect which constructor applies.

### Church Type Form

**Definition.** A term `T` is in **Church type form** if:

```
T =β λ(X:Type).λ(c₁:C₁[X])...λ(cₙ:Cₙ[X]).X
```

where each `Cᵢ[X]` is a type that may reference `X` (for recursive positions),
and the body is exactly the first parameter `X`.

The parameters `c₁, ..., cₙ` are the **constructor parameters** of `T`.

Examples:
- `Bool = λ(X:Type).λ(t:X).λ(f:X).X` — two constructor params: `t:X`, `f:X`
- `Nat = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X` — two constructor params: `z:X`, `s:X→X`
- `Unit = λ(X:Type).λ(x:X).X` — one constructor param: `x:X`

**Non-example:** `λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s z` is NOT in Church type
form because the body is `s z`, not `X`.

### Constructors of a Church Type

Given a Church type `T = λ(X:Type).λ(c₁:C₁)...λ(cₙ:Cₙ).X`, each constructor
parameter `cᵢ` corresponds to a **constructor**: a term that, when fully applied,
selects the `cᵢ` parameter. The constructor's arguments are determined by `Cᵢ`.

**For Bool** (`λ(X:Type).λ(t:X).λ(f:X).X`):
- `true = λ(X:Type).λ(t:X).λ(f:X).t` — selects `t`
- `false = λ(X:Type).λ(t:X).λ(f:X).f` — selects `f`

**For Nat** (`λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X`):
- `0 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).z` — selects `z` (no arguments)
- `succ = λ(n:Nat).λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(n X z s)` — selects `s`
  applied to the recursive unfolding of `n`

The `s` parameter has type `λ(_:X).X` (i.e., `X → X`), indicating one recursive
position. The constructor `succ` takes one `Nat` argument (the predecessor) and
applies `s` to its recursive unfolding `n X z s`.

**For Unit** (`λ(X:Type).λ(x:X).X`):
- `unit = λ(X:Type).λ(x:X).x` — selects `x`

### Partitions

**Definition.** A **partition** of a Church type `T` is a finite set of pairs
`{(p₁, Δ₁), ..., (pₙ, Δₙ)}` where each `pᵢ` is a constructor pattern
(a term built from a constructor applied to fresh variables) and `Δᵢ` is the
set of fresh variable bindings introduced. The partition must satisfy:

1. **Soundness**: For each `(pᵢ, Δᵢ)` and for all valuations of the variables
   in `Δᵢ`, we have `pᵢ ⊑ T`.
2. **Exhaustiveness**: For every `v ⊑ T`, there exists some `(pᵢ, Δᵢ)` and
   a valuation of `Δᵢ` such that `v =β pᵢ` under that valuation.

**Partition of Bool:**
```
{(true, ∅), (false, ∅)}
```

- Soundness: `true ⊑ Bool` ✓ (Task 1.1), `false ⊑ Bool` ✓ (Task 1.1)
- Exhaustiveness: see below.

**Partition of Nat:**
```
{(0, ∅), (succ k, {k : Nat})}     where k is fresh
```

- Soundness: `0 ⊑ Nat` ✓ (same structure as 3 ⊑ Nat, Task 1.1),
  `succ k ⊑ Nat` for any `k : Nat` ✓ (by the typing of succ, Task 2.2)
- Exhaustiveness: see below.

### The Partition Rule

Partitioning extends abstract evaluation with a rule that applies when
a variable of Church type is fully applied (used as an eliminator). Instead
of evaluating through the type's body (which always returns the type
parameter `X`), the evaluator splits into constructor cases.

```
[Partition]
Γ ⊢ E ⇝ τ
  x : T ∈ Γ
  T is a Church type with partition {(p₁, Δ₁), ..., (pₙ, Δₙ)}
  x appears in E as an eliminand
  For each (pᵢ, Δᵢ):
    Γᵢ = Γ[x : pᵢ], Δᵢ                    -- narrow x, bind fresh vars
    Γᵢ ⊢ E ⇝ τᵢ                            -- evaluate E in narrowed env
  -- Join:
  If all τᵢ are β-equal: τ = τ₁
  Else if τᵢ ⊑ τⱼ for some j and all i: τ = τⱼ
  Else: τ = result of standard (non-partitioned) evaluation of E
```

where `Γ[x : v]` denotes the context obtained by replacing the binding
`x : T` with `x : v`, so that the Var rule gives `x ⇝ v` in the narrowed
context. Any later bindings in Γ that reference `x` are updated accordingly.

**Key properties:**

- **At least as precise as standard evaluation.** The fallback case returns the
  same result as the App chain. The first two cases can only be more precise.
- **Sound.** Each branch evaluates in a valid narrowing of Γ (by partition
  soundness), and the result contains all branch results (by the join rule).
- **Applicable to any enclosing expression.** The rule applies to the
  expression `E` containing the elimination, not just the elimination itself.
  This is crucial: it lets narrowing propagate through the continuation of a
  branch, not just through the elimination.

**Interaction with existing rules.** Partition is an ALTERNATIVE to evaluating
`E` using the standard rules. The evaluator may choose to apply it whenever a
Church-typed variable appears as an eliminand. Since Och accepts undecidability
of type checking (§7.6), non-determinism in strategy is acceptable. The key
invariant is: Partition never produces a LESS precise result than standard
evaluation, so it can always be safely applied.

**When Partition helps.** The standard App chain through a Church type always
returns the type parameter `X`. Partition improves on this when:
1. **Both branches agree:** If all `τᵢ` are β-equal, Partition returns that
   precise type instead of `X`. Example: `n Nat 0 (λ(_:Nat).0) ⇝ 0` via
   Partition (both cases give `0`), vs `⇝ Nat` via App.
2. **Downstream narrowing:** When `E` includes code after the elimination,
   each branch evaluates with a narrowed environment. This lets type-level
   computation proceed in each branch where the standard evaluation gets stuck.

### Example: isZero on Abstract Nat

`isZero = λ(n:Nat). n Bool true (λ(_:Bool).false)`

Consider evaluating `isZero n` for abstract `n : Nat` in context `Γ = [n : Nat]`.

**Standard evaluation (App chain):**
```
n ⇝ Nat = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X
n Bool ⇝ λ(z:Bool).λ(s:λ(_:Bool).Bool).Bool          -- X := Bool
n Bool true ⇝ λ(s:λ(_:Bool).Bool).Bool                -- z := true (trivial subst)
n Bool true (λ(_:Bool).false) ⇝ Bool                   -- s := (λ(_:Bool).false) (trivial subst)
```
Result: `Bool`. Sound but imprecise — no case information.

**Partitioned evaluation:**

Let `E = n Bool true (λ(_:Bool).false)`. Apply Partition on `n : Nat`:

**Zero case** (`Γ₀ = [n : 0]`):
```
Γ₀ ⊢ n Bool true (λ(_:Bool).false) ⇝ ?
  n ⇝ 0                                               -- Var (n : 0)
  0 Bool ⇝ λ(z:Bool).λ(s:λ(_:Bool).Bool).z            -- 0 selects z
  0 Bool true ⇝ λ(s:λ(_:Bool).Bool).true               -- z := true
  0 Bool true (λ(_:Bool).false) ⇝ true                  -- body is true, s unused
```
τ₀ = `true`

**Succ case** (`Γₛ = [k : Nat, n : succ k]`):
```
Γₛ ⊢ n Bool true (λ(_:Bool).false) ⇝ ?
  n ⇝ succ k = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(k X z s)
  (succ k) Bool ⇝ λ(z:Bool).λ(s:λ(_:Bool).Bool).s(k Bool z s)
  (succ k) Bool true ⇝ λ(s:λ(_:Bool).Bool).s(k Bool true s)
  (succ k) Bool true (λ(_:Bool).false) ⇝ (λ(_:Bool).false)(k Bool true (λ(_:Bool).false))
```

The recursive call `k Bool true (λ(_:Bool).false)` with `k : Nat` evaluates
via the standard App chain to `Bool` (same analysis as above, k abstract).

```
  (λ(_:Bool).false) Bool ⇝ false                       -- App (Bool ⊑ Bool ✓)
```
τₛ = `false`

**Join:** `τ₀ = true`, `τₛ = false`. Neither `true ⊑ false` nor `false ⊑ true`.
Fallback: `Bool` (same as standard evaluation).

**Result:** `isZero n ⇝ Bool`, same as without partition. However, the case
information `{(n=0, true), (n=succ k, false)}` is established and available
for downstream use via Partition on the enclosing expression.

### Example: Partition Improving Precision

Consider `constZero = λ(n:Nat). n Nat 0 (λ(_:Nat). 0)`.

**Standard evaluation** of the body under `n : Nat`:
```
n ⇝ Nat, Nat Nat 0 (λ(_:Nat).0) ⇝ Nat                 -- through Nat's body
```
Result: `Nat`.

**Partitioned evaluation:**

Zero case (`n : 0`): `0 Nat 0 (λ(_:Nat).0) ⇝ 0` (selects z = 0)
Succ case (`n : succ k`, `k : Nat`):
```
(succ k) Nat 0 (λ(_:Nat).0) ⇝ (λ(_:Nat).0)(k Nat 0 (λ(_:Nat).0))
  k Nat 0 (λ(_:Nat).0) ⇝ Nat                           -- k abstract, standard App
  (λ(_:Nat).0) Nat ⇝ 0                                  -- App (Nat ⊑ Nat ✓)
```
τₛ = `0`

**Join:** τ₀ = `0`, τₛ = `0`. Both β-equal. τ = `0`.

**Result:** `constZero ⇝ λ(n:Nat).constZero` where the body evaluates to `0`,
strictly more precise than the non-partitioned `Nat`. Partition reveals that
the function always returns `0` regardless of input.

### Example: Partition Enabling Downstream Narrowing

Consider checking the body of:
```
f = λ(n:Nat). (isZero n) (Array n Nat) (emptyArray Nat) (λ(rest:...). ...)
```

Without partition, `isZero n ⇝ Bool`, then `Bool (Array n Nat) ... ⇝ Array n Nat`.
But `Array n Nat ⇝ Type` for abstract `n`, so the domain checks on the branch
arguments use `Type` — too imprecise to verify dependent constraints.

With partition on `n`, let `E` be the entire body `(isZero n) (Array n Nat) ...`:

**Zero case** (`n : 0`):
```
Array 0 Nat =β Unit
(isZero 0) Unit (emptyArray Nat) ... ⇝ true Unit (emptyArray Nat) ... ⇝ emptyArray Nat ⇝ unit
```
Checks: `unit ⊑ Unit` ✓

**Succ case** (`n : succ k`, `k : Nat`):
```
Array (succ k) Nat =β Pair Nat (Array k Nat)
(isZero (succ k)) (Pair Nat (Array k Nat)) ... ⇝ false (Pair Nat (Array k Nat)) ... ⇝ succ_branch
```
The succ branch is evaluated under `k : Nat` with `Array (succ k) Nat` reduced to
`Pair Nat (Array k Nat)`, enabling dependent verification.

This is the core value of partitioning: it lets type-level computation proceed
in each branch by providing concrete constructor information.

### Exhaustiveness of Nat Partition

**Theorem.** Every `v ⊑ Nat` is either `0` or `succ k` for some `k ⊑ Nat`.
That is, `{0} ∪ {succ k | k ⊑ Nat} = Nat`.

**Proof.** We must show that every value `v ⊑ Nat` has one of the two forms.

Recall `Nat = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X`.

A value `v ⊑ Nat` means: for all `X`, `z ⊑ X`, `s ⊑ (X → X)`, we have
`v X z s ⊑ X`. Since `v` is a closed value (a lambda), it has the form
`λ(X:Type).λ(z:X).λ(s:λ(_:X).X).body` where `body` is built from `X`, `z`,
`s`, and lambda/application.

By the subtyping derivation `v ⊑ Nat` (Lam rule, three levels), we need
`body ⊑ X` under context `[X:Type, z:X, s:λ(_:X).X]`.

What terms `body` satisfy `body ⊑ X` in this context? By examining the
subtyping rules:

- `z ⊑ X` — by Var (z : X). This gives `body = z`, i.e., `v = 0`.
- `s e ⊑ X` — by App, if `s ⊑ λ(_:X).X` (Var) and `e ⊑ X`. This gives
  `body = s e` where `e ⊑ X`.
- Recursively, `e ⊑ X` is again either `z`, `s e'`, or a chain of `s`
  applications ending at `z`.

So `body` must be `s(s(...(s z)...))` — some number of applications of `s`
to `z`. This is exactly the body of a Church numeral.

- If `body = z`: `v = 0` ✓
- If `body = s e`: `v = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s e`. Define
  `k = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).e`. Then `k ⊑ Nat` (by the same
  argument, since `e ⊑ X`) and `v = succ k`:

  ```
  succ k = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(k X z s)
         = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s e          -- since k X z s = e
  ```

  The key step: `k X z s = e` because `k = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).e`
  and `k X z s =β e`. So `v = succ k` ✓

Therefore every `v ⊑ Nat` is either `0` or `succ k` for some `k ⊑ Nat`. ∎

**Corollary (exhaustiveness).** The partition `{(0, ∅), (succ k, {k:Nat})}` of
Nat is exhaustive: every value in Nat is covered by exactly one case.

**Exhaustiveness of Bool Partition.** By identical reasoning with
`Bool = λ(X:Type).λ(t:X).λ(f:X).X`: the body must satisfy `body ⊑ X` under
`[X:Type, t:X, f:X]`, giving `body = t` (i.e., `v = true`) or `body = f`
(i.e., `v = false`). There are no recursive positions, so the partition
`{(true, ∅), (false, ∅)}` is exhaustive. ∎


## Task 3.2: Abstract Test Cases (§6.2) with Partitioning

### Observation: §6.2 Cases Do Not Require Partitioning

All §6.2 derivations from Task 2.4 go through without partitioning. The reason
is structural: every §6.2 test eliminates an abstract `Vec Nat`, and

```
Vec Nat =β λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X
```

The body is `X`. When `v1 ⇝ Vec Nat` and we apply `v1 ResultType cont`, the
App chain substitutes X := ResultType and k := cont into the body `X`, giving
`ResultType`. The continuation `cont` is checked for domain compatibility but
never actually applied — the body doesn't reference `k`.

This means the abstract evaluator returns `ResultType` without needing to know
anything about the vector's length or contents. The continuation `cont` is
verified to have the right type (`cont ⊑ λ(a:Nat).λ(_:Array a Nat).ResultType`)
but its body is never entered during the abstract evaluation of the elimination.

Partitioning would only matter if:
1. The continuation were actually applied (impossible — Vec's body is `X`)
2. The result type depended on the vector's length (impossible — it's just `X`)

Therefore all §6.2 derivations are exactly as in Task 2.4.

### Re-verification of §6.2 Derivations

We re-derive each case, noting where partitioning could apply but doesn't change
the result. All derivations are in context `Γ = [v1 : Vec Nat, v2 : Vec Nat]`.

**len = v1 Nat (λ(n:Nat). λ(arr:Array n Nat). n)**

```
v1 ⇝ Vec Nat = λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X
v1 Nat ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). Nat     -- X := Nat
v1 Nat cont ⇝ Nat                                       -- body is Nat, k unused
  cont ⊑ λ(a:Nat).λ(_:Array a Nat).Nat ✓
```

Partitioning on v1 would split into every possible Vec Nat value (every
possible length and content). In each case, the body is still `X = Nat`.
No improvement. Result: `Nat` ✓

**rewrapped = v1 (Vec Nat) (λ(n:Nat). λ(arr:Array n Nat). mkVec Nat n arr)**

Same pattern. Body is `X = Vec Nat`, continuation unused. Result: `Vec Nat` ✓

**combinedLen = v1 Nat (λ(n1:Nat). λ(_:Array n1 Nat). v2 Nat (λ(n2:Nat). λ(_:Array n2 Nat). add n1 n2))**

Same pattern. v1 elimination gives `Nat` (body is X). The continuation involving
v2 and add is never entered during the abstract evaluation of `v1 Nat cont`.
Result: `Nat` ✓

**vec3 = mkVec Nat 3 arr_abstract** where `arr_abstract = (... : Array 3 Nat)`

```
mkVec Nat 3 arr_abstract
  ⇝ dpair Nat (λ(n:Nat). Array n Nat) 3 (Array 3 Nat)
  ⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 3 (Array 3 Nat)
```

This is a CONCRETE vector (length 3 is known), not abstract. No partitioning
needed — standard evaluation propagates the precise length. Result: `vec3` as
above ✓

**vec3_len = vec3 Nat (λ(n:Nat). λ(_:Array n Nat). n)**

```
vec3 Nat ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). k 3 (Array 3 Nat)
vec3 Nat cont ⇝ cont 3 (Array 3 Nat)
  cont 3 ⇝ λ(_:Array 3 Nat). 3
  cont 3 (Array 3 Nat) ⇝ 3
```

The body references `k` (unlike Vec Nat's body `X`), so the continuation IS
applied — but with CONCRETE values (3 and Array 3 Nat), so standard evaluation
gives the precise result. Result: `3` ✓

### Example Where Partitioning Is Essential

The §6.2 tests are designed to work without partitioning. Here is an example
that REQUIRES partitioning to verify:

```
safeHead = λ(n:Nat). λ(arr:Array (succ n) Nat).
             headArray Nat n arr
  -- safeHead ⊑ λ(n:Nat). λ(_:Array (succ n) Nat). Nat
```

The Lam well-formedness check evaluates the body under `n : Nat, arr : Array (succ n) Nat`.

`headArray Nat n arr` expands to `arr Nat (λ(x:Nat).λ(_:Array n Nat). x)`.

This requires `arr ⊑ Array (succ n) Nat`. By Var, `arr ⇝ Array (succ n) Nat`.

Now `Array (succ n) Nat = (succ n) Type Unit (λ(acc:Type). Pair Nat acc)`.

Without partitioning, `succ n ⇝ succ Nat`:
```
succ ⇝ succ, Nat ⊑ Nat ✓
body[n := Nat] = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(Nat X z s)
```

Evaluating `(succ Nat) Type Unit (λ(acc:Type). Pair Nat acc)`:
```
(succ Nat) Type ⇝ λ(z:Type).λ(s:λ(_:Type).Type).s(Nat Type z s)
```

`Nat Type z s = (λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X) Type z s = Type`

Hmm wait — `Nat ⇝ Nat` and then `Nat Type ⇝ λ(z:Type).λ(s:λ(_:Type).Type).Type`.
So `Nat Type z s ⇝ Type` and then `s Type = (λ(acc:Type). Pair Nat acc) Type ⇝ Pair Nat Type`.

So `Array (succ n) Nat ⇝ Pair Nat Type` for abstract `n : Nat`. This DOES
reduce (unlike `Array n Nat` which goes through `Nat` directly), because `succ n`
first applies `s`, giving `s(n Type Unit (λacc. Pair Nat acc))`. But the inner
`n Type Unit (λacc. Pair Nat acc) ⇝ Type` via abstract `n`, so we get
`Pair Nat Type` — usable but imprecise (the second component should be
`Array n Nat`, not `Type`).

With partitioning on `n`, in the zero case:
```
Array (succ 0) Nat = Array 1 Nat =β Pair Nat Unit
```

In the succ case:
```
Array (succ (succ k)) Nat = Pair Nat (Array (succ k) Nat) = Pair Nat (Pair Nat ...)
```

Each case has a precise structure, enabling verification of head/tail operations.

Here is a simpler example that directly demonstrates the precision improvement:

```
f = λ(b:Bool). b Nat 42 7
```

**Standard evaluation** under `b : Bool`:
```
b ⇝ Bool, Bool Nat 42 7 ⇝ Nat                          -- through Bool's body
```

**Partitioned evaluation:**
- b = true: `true Nat 42 7 ⇝ 42`
- b = false: `false Nat 42 7 ⇝ 7`

Join: `42` and `7` are different, neither is a subtype. Fallback: `Nat`.
Same result. No precision gain here because the branches disagree.

But consider:

```
g = λ(b:Bool). b Nat 0 0
```

**Standard evaluation:** `Bool Nat 0 0 ⇝ Nat`
**Partitioned evaluation:** true → `0`, false → `0`. Both β-equal. τ = `0`.

Partition gives `g ⇝ λ(b:Bool).g` with body type `0`, strictly more precise
than `Nat`. The partition reveals that `g` is a constant function returning `0`.

### Summary

Partitioning is a mechanism for recovering precision when abstract Church-encoded
values are eliminated. It works by:

1. Identifying that a variable `x : T` of Church type is being used as an eliminand
2. Splitting the evaluation into constructor cases, with each case narrowing `x`
   to a specific constructor (binding fresh variables for recursive components)
3. Evaluating the expression in each narrowed context using the standard rules
4. Joining the results: returning the common type if all cases agree, or falling
   back to the standard (non-partitioned) result otherwise

The mechanism is sound (each narrowing is valid by partition soundness), exhaustive
(every possible value is covered by some case), and at least as precise as standard
evaluation. It is essential for type-checking programs that branch on Church-encoded
data and use the discriminant dependently.