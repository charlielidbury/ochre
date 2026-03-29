# Problem

Layer 2: Typing Rules

Task 2.1: Define the abstract evaluation judgment Γ ⊢ e ⇝ τ. Write natural deduction rules for: variable, lambda, application, ascription, Type. Verification: the rules must be deterministic — given Γ and e, there is exactly one τ (the most precise type). State and verify this uniqueness property for each rule.

Task 2.2: Verify typing of concrete test cases. Using the rules from 2.1, derive the judgments for every line in §6.1 (concrete instantiation). Each EXPECT annotation becomes a specific judgment to derive. Verification: produce the derivation tree for each. This depends on 2.1 and 1.1.

Task 2.3: Verify typing of transparency tests. Derive the judgments for §6.4: id Nat 3 ⇝ 3 (not Nat), id_ascribed Nat 3 ⇝ Nat (not 3), double 3 ⇝ 6. These specifically test that transparency propagates precision and ascription blocks it. Verification: derivation trees showing the precise type in each case. Depends on 2.1.

Task 2.4: Verify typing of abstract test cases. Using the rules from 2.1, derive the judgments for every line in §6.2 (abstract instantiation). These test that the rules handle opaque/ascribed inputs correctly: extracting abstract lengths, repacking vectors, combining abstract values, and recovering precision from partially-known constructions. Verification: produce the derivation tree for each. Depends on 2.1 and 1.1.

Task 2.5: Verify rejection of failing tests. Show that each test in §6.3 cannot be given a type / results in a type error. For each BAD case, show where the derivation gets stuck or produces a contradiction. Verification: for each case, identify the exact rule that fails and why. Depends on 2.1 and 1.1.

# Solution

## Task 2.1: Abstract Evaluation Rules

All terms are compared modulo β-equivalence. In derivations, we freely β-reduce
before applying rules. The judgment `Γ ⊢ e ⇝ τ` means "in context Γ, expression
e abstractly evaluates to type τ."

```
[Var]
Γ ⊢ x ⇝ τ
  x : τ ∈ Γ

[Lam]
Γ ⊢ λ(x:A).e ⇝ λ(x:A).e
  Γ, x:A ⊢ e ⇝ e'              -- well-formedness check, e' discarded

[App]
Γ ⊢ f a ⇝ τ[x := a']
  Γ ⊢ f ⇝ λ(x:A).τ
  Γ ⊢ a ⇝ a'
  Γ ⊢ a' ⊑ A

[Asc]
Γ ⊢ (e : τ) ⇝ τ
  Γ ⊢ e ⇝ σ
  Γ ⊢ σ ⊑ τ

[Type]
Γ ⊢ Type ⇝ Type
```

Notes:
- **Lam** returns the lambda itself — it is its own most precise type. The premise
  checks that the body is well-formed under the declared domain, catching errors
  like `λ(x:Nat).(x:3)` at definition time (Asc checks `Nat ⊑ 3`, fails). The
  evaluated body `e'` is discarded — returning it would abstract variables and
  kill transparency.
- **App** evaluates both `f` and `a`, then substitutes the evaluated argument
  into the body of `f`'s result. The subtyping check `a' ⊑ A` ensures the
  argument is in the domain. The result `τ[x := a']` is the body with the
  *abstract value* of `a` substituted, not the syntactic `a`. This is the
  abstract evaluation step — it propagates precision through the body.
- **Asc** discards precision: it returns the ascribed type `τ`, not the more
  precise `σ`. The check `σ ⊑ τ` ensures soundness.
- **App** requires `f` to evaluate to a lambda. If `f` evaluates to a variable
  (e.g., `f ⇝ g` where `g : λ(x:A).B`), we need `f` to evaluate to a lambda
  form. Since Var returns the type `τ` from the context, and function-typed
  variables have lambda types, this works: if `g : λ(x:A).B` then `g ⇝ λ(x:A).B`.

### Uniqueness

Each rule is syntax-directed — exactly one rule applies per syntactic form:
- Variable → Var (unique: each variable has exactly one binding in Γ)
- Lambda → Lam (unique: returns the term itself; premise checks body well-formedness)
- Application → App (unique: recursively determined by f and a)
- Ascription → Asc (unique: returns the ascribed type)
- Type → Type (unique: returns Type)

Given Γ and e, there is exactly one τ such that Γ ⊢ e ⇝ τ. ∎


## Task 2.2: Concrete Test Cases (§6.1)

### Definitions

For reference, β-reduced forms used throughout:

```
Bool     = λ(X:Type).λ(t:X).λ(f:X).X
true     = λ(X:Type).λ(t:X).λ(f:X).t
false    = λ(X:Type).λ(t:X).λ(f:X).f
Nat      = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X
0        = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).z
Unit     = λ(X:Type).λ(x:X).X
unit     = λ(X:Type).λ(x:X).x
succ     = λ(n:Nat).λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s (n X z s)
add      = λ(n:Nat).λ(m:Nat). n Nat m succ
isZero   = λ(n:Nat). n Bool true (λ(_:Bool).false)
Pair A B = λ(X:Type).λ(k:λ(_:A).λ(_:B).X).X
pair A B = λ(a:A).λ(b:B).λ(X:Type).λ(k:λ(_:A).λ(_:B).X). k a b

Array 0 T         =β Unit
Array (succ k) T  =β Pair T (Array k T)
emptyArray T      =β unit
consArray T n x r =β pair T (Array n T) x r
headArray T n arr =β arr T (λ(x:T).λ(_:Array n T). x)
tailArray T n arr =β arr (Array n T) (λ(_:T).λ(rest:Array n T). rest)
```

### Notation conventions

- `⊢` means `∅ ⊢` (empty context) unless otherwise stated.
- Church numerals: `N` denotes the Church numeral for number N, e.g.,
  `10 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s(s(s(s(s(s(s(s(s z)))))))))`.
- `N ⊑ Nat` follows the same structure as `3 ⊑ Nat` from Task 1.1 for all N.
- When a derivation step is structurally identical to a previous one, we cite it.
- **Lam well-formedness:** Every lambda `λ(x:A).e` requires checking `Γ,x:A ⊢ e ⇝ e'`.
  For all standard definitions (Bool, Nat, true, false, succ, add, etc.), the bodies
  are well-formed — they consist of variables, lambdas, applications, and Type, all
  of which evaluate successfully under the declared domains. We omit these routine
  Lam premises unless the check is interesting (e.g., involves ascription).

### Helper: Typing a multi-argument application

Many test cases involve chains like `f A B C D`. We derive these left-to-right:

```
f A B C D ⇝ ?
  f ⇝ λ(a:...).body₁           -- Lam or prior result
  A ⇝ A                         -- Lam/Type
  A ⊑ ...                       -- domain check
  body₁[a:=A] = λ(b:...).body₂  -- β-reduce
  B ⇝ B                         -- ...continue
```

We'll compress these chains, showing only the interesting steps.

### arr1

`arr1 = consArray Nat 1 10 (consArray Nat 0 20 (emptyArray Nat))`

Working inside-out:

**emptyArray Nat:** `(λ(T:Type).unit) Nat`
```
emptyArray Nat ⇝ unit -- App
  emptyArray ⇝ λ(T:Type).unit -- Lam
  Nat ⇝ Nat -- Lam
  Nat ⊑ Type -- Top
  unit[T:=Nat] = unit -- (T unused in unit)
```

**consArray Nat 0 20 (emptyArray Nat):** Applying consArray step by step:

`consArray =β λ(T:Type).λ(n:Nat).λ(x:T).λ(rest:Array n T). pair T (Array n T) x rest`

```
consArray Nat ⇝ λ(n:Nat).λ(x:Nat).λ(rest:Array n Nat). pair Nat (Array n Nat) x rest -- App
  consArray ⇝ consArray -- Lam
  Nat ⇝ Nat -- Lam
  Nat ⊑ Type -- Top
```

```
consArray Nat 0 ⇝ λ(x:Nat).λ(rest:Array 0 Nat). pair Nat (Array 0 Nat) x rest -- App
  consArray Nat ⇝ (above)
  0 ⇝ 0 -- Lam
  0 ⊑ Nat -- (from 1.1, same structure as 3 ⊑ Nat)
```

Note: `Array 0 Nat =β Unit`, so the body is `λ(x:Nat).λ(rest:Unit). pair Nat Unit x rest`.

```
consArray Nat 0 20 ⇝ λ(rest:Unit). pair Nat Unit 20 rest -- App
  consArray Nat 0 ⇝ (above)
  20 ⇝ 20 -- Lam
  20 ⊑ Nat -- (same structure as 3 ⊑ Nat)
```

```
consArray Nat 0 20 (emptyArray Nat) ⇝ pair Nat Unit 20 unit -- App
  consArray Nat 0 20 ⇝ (above)
  emptyArray Nat ⇝ unit -- (above)
  unit ⊑ Unit -- (from 1.1)
```

β-reducing: `pair Nat Unit 20 unit =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 20 unit`

Call this `inner1`.

**consArray Nat 1 10 inner1:**

```
consArray Nat 1 ⇝ λ(x:Nat).λ(rest:Array 1 Nat). pair Nat (Array 1 Nat) x rest -- App (same pattern)
```

`Array 1 Nat =β Pair Nat Unit =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X).X`

```
consArray Nat 1 10 ⇝ λ(rest:Pair Nat Unit). pair Nat (Pair Nat Unit) 10 rest -- App
  10 ⊑ Nat -- (standard)
```

```
consArray Nat 1 10 inner1 ⇝ pair Nat (Pair Nat Unit) 10 inner1 -- App
  inner1 ⇝ inner1 -- Lam
  inner1 ⊑ Pair Nat Unit -- (same structure as 1.2: consArray Nat 0 20 (emptyArray Nat) ⊑ Array 1 Nat)
```

So `arr1 ⇝ λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat Unit).X). k 10 inner1`

where `inner1 = λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 20 unit`.

**Verification:** `arr1 ⊑ Array 2 Nat`

`Array 2 Nat =β Pair Nat (Pair Nat Unit)
=β λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat Unit).X).X`

This follows the same structure as Task 1.2 (consArray ⊑ Array). ✓

arr1 is its own most precise type (it's a lambda, returned by Lam). ✓

### arr2

`arr2 = consArray Nat 2 30 (consArray Nat 1 40 (consArray Nat 0 50 (emptyArray Nat)))`

Same pattern as arr1, one level deeper.

```
consArray Nat 0 50 (emptyArray Nat) ⇝ pair Nat Unit 50 unit -- (same as inner1 with 50)
```
Call this `inner2a = λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 50 unit`.

```
consArray Nat 1 40 inner2a ⇝ pair Nat (Pair Nat Unit) 40 inner2a -- (same pattern)
  inner2a ⊑ Pair Nat Unit -- (same as 1.2)
```
Call this `inner2b = λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat Unit).X). k 40 inner2a`.

```
consArray Nat 2 30 inner2b ⇝ pair Nat (Pair Nat (Pair Nat Unit)) 30 inner2b -- App
  inner2b ⊑ Pair Nat (Pair Nat Unit) -- (same structure, one more nesting level)
```

`arr2 ⇝ λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat (Pair Nat Unit)).X). k 30 inner2b`

**Verification:** `arr2 ⊑ Array 3 Nat =β Pair Nat (Pair Nat (Pair Nat Unit))` ✓

### h = headArray Nat 1 arr1

`headArray = λ(T:Type).λ(n:Nat).λ(arr:Array (succ n) T). arr T (λ(x:T).λ(_:Array n T). x)`

```
headArray Nat ⇝ λ(n:Nat).λ(arr:Array (succ n) Nat). arr Nat (λ(x:Nat).λ(_:Array n Nat). x) -- App
headArray Nat 1 ⇝ λ(arr:Array 2 Nat). arr Nat (λ(x:Nat).λ(_:Array 1 Nat). x) -- App
  1 ⊑ Nat ✓
```

`Array 2 Nat =β Pair Nat (Pair Nat Unit)`, so domain is `Pair Nat (Pair Nat Unit)`.

```
headArray Nat 1 arr1 ⇝ arr1 Nat (λ(x:Nat).λ(_:Pair Nat Unit). x) -- App
  arr1 ⇝ arr1 -- Lam
  arr1 ⊑ Pair Nat (Pair Nat Unit) -- (verified above)
```

Now evaluate `arr1 Nat (λ(x:Nat).λ(_:Pair Nat Unit). x)`:

`arr1 = λ(X:Type).λ(k:λ(_:Nat).λ(_:Pair Nat Unit).X). k 10 inner1`

```
arr1 Nat ⇝ λ(k:λ(_:Nat).λ(_:Pair Nat Unit).Nat). k 10 inner1 -- App
```

```
arr1 Nat (λ(x:Nat).λ(_:Pair Nat Unit). x) -- App
  ⇝ (λ(x:Nat).λ(_:Pair Nat Unit). x) 10 inner1
```

Wait — the App rule substitutes the *evaluated argument* into the body. Let me
be more careful.

```
arr1 Nat (λ(x:Nat).λ(_:Pair Nat Unit).x) -- App
  arr1 Nat ⇝ λ(k:λ(_:Nat).λ(_:Pair Nat Unit).Nat). k 10 inner1
  (λ(x:Nat).λ(_:Pair Nat Unit).x) ⇝ (λ(x:Nat).λ(_:Pair Nat Unit).x) -- Lam
  (λ(x:Nat).λ(_:Pair Nat Unit).x) ⊑ λ(_:Nat).λ(_:Pair Nat Unit).Nat -- (body x ⊑ Nat by Var)
  body[k := (λ(x:Nat).λ(_:Pair Nat Unit).x)] = (λ(x:Nat).λ(_:Pair Nat Unit).x) 10 inner1
```

Now evaluate `(λ(x:Nat).λ(_:Pair Nat Unit).x) 10 inner1`:

```
(λ(x:Nat).λ(_:Pair Nat Unit).x) 10 ⇝ λ(_:Pair Nat Unit).10 -- App
  (λ(x:Nat).λ(_:Pair Nat Unit).x) ⇝ itself -- Lam
  10 ⇝ 10 -- Lam
  10 ⊑ Nat ✓
```

```
(λ(_:Pair Nat Unit).10) inner1 ⇝ 10 -- App
  inner1 ⇝ inner1 -- Lam
  inner1 ⊑ Pair Nat Unit ✓
```

**Result:** `h ⇝ 10` ✓ (precise type is 10, and 10 ⊑ Nat ✓)

### t = tailArray Nat 1 arr1

Same structure as headArray, but the continuation extracts the second component.

`tailArray Nat 1 arr1 ⇝ arr1 (Array 1 Nat) (λ(_:Nat).λ(rest:Pair Nat Unit). rest)` -- App chain

Evaluating (same pattern as h):
```
arr1 (Pair Nat Unit) (λ(_:Nat).λ(rest:Pair Nat Unit). rest) -- App chain
  substitute k := (λ(_:Nat).λ(rest:Pair Nat Unit). rest)
  ⇝ (λ(_:Nat).λ(rest:Pair Nat Unit). rest) 10 inner1
  ⇝ (λ(rest:Pair Nat Unit). rest) inner1 -- App (10 ⊑ Nat ✓)
  ⇝ inner1 -- App (inner1 ⊑ Pair Nat Unit ✓)
```

**Result:** `t ⇝ inner1 = pair Nat Unit 20 unit` ✓

`inner1 ⊑ Array 1 Nat =β Pair Nat Unit` ✓ (from 1.2)

### vec1 = mkVec Nat 2 arr1

`mkVec = λ(T:Type).λ(n:Nat).λ(arr:Array n T). dpair Nat (λ(n:Nat). Array n T) n arr`

```
mkVec Nat ⇝ λ(n:Nat).λ(arr:Array n Nat). dpair Nat (λ(n:Nat). Array n Nat) n arr -- App
mkVec Nat 2 ⇝ λ(arr:Array 2 Nat). dpair Nat (λ(n:Nat). Array n Nat) 2 arr -- App
  2 ⊑ Nat ✓
mkVec Nat 2 arr1 ⇝ dpair Nat (λ(n:Nat). Array n Nat) 2 arr1 -- App
  arr1 ⊑ Array 2 Nat ✓
```

Now evaluate `dpair Nat (λ(n:Nat). Array n Nat) 2 arr1`:

`dpair = λ(A:Type).λ(B:λ(_:A).Type).λ(a:A).λ(b:B a). λ(X:Type).λ(k:λ(a:A).λ(_:B a).X). k a b`

Applying step by step, substituting A:=Nat, B:=λ(n:Nat).Array n Nat, a:=2, b:=arr1:

```
⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 2 arr1
```

**Result:** `vec1 ⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 2 arr1`

`vec1 ⊑ Vec Nat` — same structure as Task 1.3. ✓

### vec2 = mkVec Nat 3 arr2

Identical pattern. `vec2 ⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 3 arr2`

`vec2 ⊑ Vec Nat` ✓

### vecSum = vec1 Nat (λ(n:Nat). λ(arr:Array n Nat). n)

```
vec1 Nat ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). k 2 arr1 -- App
  vec1 ⇝ vec1 -- Lam
  Nat ⊑ Type ✓
```

Let `cont = λ(n:Nat).λ(arr:Array n Nat). n`.

```
vec1 Nat cont -- App
  vec1 Nat ⇝ (above)
  cont ⇝ cont -- Lam
  cont ⊑ λ(a:Nat).λ(_:Array a Nat).Nat -- Lam
    Nat ⊑ Nat ✓ -- Refl
    λ(arr:Array a Nat).a ⊑ λ(_:Array a Nat).Nat -- Lam [a:Nat]
      Array a Nat ⊑ Array a Nat ✓ -- Refl
      a ⊑ Nat -- Var [a:Nat]
  body[k:=cont] = cont 2 arr1
```

```
cont 2 ⇝ λ(arr:Array 2 Nat). 2 -- App
  2 ⊑ Nat ✓
cont 2 arr1 ⇝ 2 -- App
  arr1 ⊑ Array 2 Nat ✓
```

**Result:** `vecSum ⇝ 2` ✓

### vecHead = vec1 Nat (λ(n:Nat). λ(arr:Array n Nat). headArray Nat (pred n) arr)

Same App chain as vecSum. After substituting k:

```
⇝ (λ(n:Nat).λ(arr:Array n Nat). headArray Nat (pred n) arr) 2 arr1
```

```
(λ(n:Nat).λ(arr:Array n Nat). headArray Nat (pred n) arr) 2
  ⇝ λ(arr:Array 2 Nat). headArray Nat (pred 2) arr -- App
  2 ⊑ Nat ✓
```

Now `pred 2` must be evaluated. `pred = λ(n:Nat). ...` and `pred 2 =β 1`.

Actually, `pred` is defined as a complex Church encoding. Let me trace through
the abstract evaluation:

```
pred ⇝ pred -- Lam
pred 2 ⇝ pred-body[n:=2] -- App
```

`pred 2 =β 1` by the standard Church predecessor reduction (§8.4). The abstract
evaluator performs this β-reduction, yielding `1`.

```
(λ(arr:Array 2 Nat). headArray Nat 1 arr) arr1 ⇝ headArray Nat 1 arr1 -- App
  arr1 ⊑ Array 2 Nat ✓
```

We already derived `headArray Nat 1 arr1 ⇝ 10` above.

**Result:** `vecHead ⇝ 10` ✓

### five = add 2 3

```
add ⇝ add -- Lam
add 2 ⇝ λ(m:Nat). 2 Nat m succ -- App (2 ⊑ Nat ✓)
add 2 3 ⇝ 2 Nat 3 succ -- App (3 ⊑ Nat ✓)
```

Evaluate `2 Nat 3 succ`:

`2 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s z)`

```
2 Nat ⇝ λ(z:Nat).λ(s:λ(_:Nat).Nat). s(s z) -- App
2 Nat 3 ⇝ λ(s:λ(_:Nat).Nat). s(s 3) -- App (3 ⊑ Nat ✓)
2 Nat 3 succ ⇝ succ(succ 3) -- App (succ ⊑ λ(_:Nat).Nat ✓)
```

`succ 3 =β 4`, `succ 4 =β 5`.

**Result:** `five ⇝ 5` ✓

### A0 = Array 0 Nat

`Array = λ(n:Nat).λ(T:Type). n Type Unit (λ(acc:Type). Pair T acc)`

```
Array 0 ⇝ λ(T:Type). 0 Type Unit (λ(acc:Type). Pair T acc) -- App
Array 0 Nat ⇝ 0 Type Unit (λ(acc:Type). Pair Nat acc) -- App
```

`0 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). z`

```
0 Type ⇝ λ(z:Type).λ(s:λ(_:Type).Type). z -- App
0 Type Unit ⇝ λ(s:λ(_:Type).Type). Unit -- App (Unit ⊑ Type via Top)
0 Type Unit (λ(acc:Type). Pair Nat acc) ⇝ Unit -- App
```

**Result:** `A0 ⇝ Unit` ✓

### A2 = Array 2 Nat

Same pattern with `2 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s z)`:

```
2 Type Unit (λ(acc:Type). Pair Nat acc)
  ⇝ (λ(acc:Type). Pair Nat acc) ((λ(acc:Type). Pair Nat acc) Unit)
  ⇝ (λ(acc:Type). Pair Nat acc) (Pair Nat Unit)
  ⇝ Pair Nat (Pair Nat Unit)
```

**Result:** `A2 ⇝ Pair Nat (Pair Nat Unit)` ✓

### r1 = true Nat 10 20

```
true Nat ⇝ λ(t:Nat).λ(f:Nat). t -- App
true Nat 10 ⇝ λ(f:Nat). 10 -- App (10 ⊑ Nat ✓)
true Nat 10 20 ⇝ 10 -- App (20 ⊑ Nat ✓)
```

**Result:** `r1 ⇝ 10` ✓

### r2 = false Nat 10 20

```
false Nat ⇝ λ(t:Nat).λ(f:Nat). f -- App
false Nat 10 ⇝ λ(f:Nat). f -- App (10 ⊑ Nat ✓)
false Nat 10 20 ⇝ 20 -- App (20 ⊑ Nat ✓)
```

**Result:** `r2 ⇝ 20` ✓

### iz0 = isZero 0

`isZero = λ(n:Nat). n Bool true (λ(_:Bool).false)`

```
isZero 0 ⇝ 0 Bool true (λ(_:Bool).false) -- App (0 ⊑ Nat ✓)
```

`0 Bool ⇝ λ(z:Bool).λ(s:λ(_:Bool).Bool). z`

```
0 Bool true ⇝ λ(s:λ(_:Bool).Bool). true -- App (true ⊑ Bool from 1.1)
0 Bool true (λ(_:Bool).false) ⇝ true -- App ((λ(_:Bool).false) ⊑ λ(_:Bool).Bool ✓)
```

**Result:** `iz0 ⇝ true` ✓

### iz3 = isZero 3

```
isZero 3 ⇝ 3 Bool true (λ(_:Bool).false) -- App
```

`3 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(s(s z))`

```
3 Bool ⇝ λ(z:Bool).λ(s:λ(_:Bool).Bool). s(s(s z))
3 Bool true ⇝ λ(s:λ(_:Bool).Bool). s(s(s true))
3 Bool true (λ(_:Bool).false)
  ⇝ (λ(_:Bool).false)((λ(_:Bool).false)((λ(_:Bool).false) true))
```

Evaluating inside-out:
```
(λ(_:Bool).false) true ⇝ false -- App (true ⊑ Bool ✓)
(λ(_:Bool).false) false ⇝ false -- App (false ⊑ Bool ✓)
(λ(_:Bool).false) false ⇝ false -- App (false ⊑ Bool ✓)
```

**Result:** `iz3 ⇝ false` ✓

### branch = (isZero 0) Nat 100 200

```
isZero 0 ⇝ true -- (above)
true Nat 100 200 ⇝ 100 -- (same as r1 pattern)
```

**Result:** `branch ⇝ 100` ✓


## Task 2.3: Transparency Tests (§6.4)

### precise_3 = id Nat 3

`id = λ(T:Type).λ(x:T). x`

```
id Nat ⇝ λ(x:Nat). x -- App (Nat ⊑ Type ✓)
id Nat 3 ⇝ 3 -- App (3 ⊑ Nat ✓, body x[x:=3] = 3)
```

**Result:** `precise_3 ⇝ 3` (not Nat) ✓ — transparency preserves precision.

### imprecise_3 = id_ascribed Nat 3

`id_ascribed = λ(T:Type).λ(x:T). (x : T)`

Note: The inner lambda `λ(x:T).(x:T)` is well-formed — Lam premise checks
`T:Type, x:T ⊢ (x:T) ⇝ T` via Asc (`T ⊑ T` ✓). This is the "check once"
that validates the ascription at definition time.

```
id_ascribed Nat ⇝ λ(x:Nat). (x : Nat) -- App
id_ascribed Nat 3 -- App
  3 ⊑ Nat ✓
  body = (x : Nat)[x:=3] = (3 : Nat)
  evaluate (3 : Nat) ⇝ Nat -- Asc (3 ⊑ Nat ✓)
```

**Result:** `imprecise_3 ⇝ Nat` (not 3) ✓ — ascription blocks precision.

### precise_6 = double 3

`double = λ(x:Nat). add x x`

```
double 3 ⇝ add 3 3 -- App (3 ⊑ Nat ✓)
```

`add 3 3 ⇝ 3 Nat 3 succ` (same pattern as `add 2 3`).

`3 Nat 3 succ ⇝ succ(succ(succ 3)) =β succ(succ 4) =β succ 5 =β 6`

**Result:** `precise_6 ⇝ 6` ✓

### abstract_double = double (... : Nat)

```
(... : Nat) ⇝ Nat -- Asc
double (... : Nat) ⇝ add Nat Nat -- App (Nat ⊑ Nat ✓)
```

`add Nat Nat ⇝ Nat Nat Nat succ`

`Nat = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). X`

```
Nat Nat ⇝ λ(z:Nat).λ(s:λ(_:Nat).Nat). Nat -- App
Nat Nat Nat ⇝ λ(s:λ(_:Nat).Nat). Nat -- App (Nat ⊑ Nat ✓)
Nat Nat Nat succ ⇝ Nat -- App (succ ⊑ λ(_:Nat).Nat ✓)
```

**Result:** `abstract_double ⇝ Nat` ✓ — abstract input produces abstract output.


## Task 2.4: Abstract Test Cases (§6.2)

Context: `v1 : Vec Nat, v2 : Vec Nat` (introduced via ascription).

`Vec Nat =β Sigma Nat (λ(n:Nat). Array n Nat) =β λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X`

Since v1 and v2 are variables with type Vec Nat:

```
Γ ⊢ v1 ⇝ Vec Nat -- Var
Γ ⊢ v2 ⇝ Vec Nat -- Var
```

where `Γ = [v1 : Vec Nat, v2 : Vec Nat]`.

### len = v1 Nat (λ(n:Nat). λ(arr:Array n Nat). n)

```
v1 Nat ⇝ (Vec Nat body)[X:=Nat] -- App
  v1 ⇝ Vec Nat = λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). X
  Nat ⊑ Type ✓
  = λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). Nat
```

Let `cont = λ(n:Nat).λ(arr:Array n Nat). n`.

```
v1 Nat cont ⇝ Nat -- App
  v1 Nat ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). Nat
  cont ⇝ cont -- Lam
  cont ⊑ λ(a:Nat).λ(_:Array a Nat).Nat -- (same check as vecSum)
  body[k:=cont] = Nat
```

**Result:** `len ⇝ Nat` ✓ — abstract, not precise (the body of Vec Nat is `X`, which became `Nat`).

### rewrapped = v1 (Vec Nat) (λ(n:Nat). λ(arr:Array n Nat). mkVec Nat n arr)

```
v1 (Vec Nat) ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Vec Nat). Vec Nat -- App
  Vec Nat ⊑ Type ✓ (Top)
```

The body is `Vec Nat` (since Vec Nat's body is `X`, substituting X:=Vec Nat gives `Vec Nat`). The continuation is irrelevant — the body doesn't use `k`.

```
v1 (Vec Nat) cont ⇝ Vec Nat -- App
  cont ⊑ λ(a:Nat).λ(_:Array a Nat).Vec Nat ✓
  body = Vec Nat
```

**Result:** `rewrapped ⇝ Vec Nat` ✓

### combinedLen

```
combinedLen = v1 Nat (λ(n1:Nat). λ(_:Array n1 Nat).
               v2 Nat (λ(n2:Nat). λ(_:Array n2 Nat).
                 add n1 n2))
```

Same pattern: `v1 Nat cont ⇝ Nat` because the body of Vec Nat is X = Nat,
and the continuation is never applied (the body doesn't reference k).

**Result:** `combinedLen ⇝ Nat` ✓

### arr_abstract and vec3

```
arr_abstract = (... : Array 3 Nat)
  ⇝ Array 3 Nat -- Asc

vec3 = mkVec Nat 3 arr_abstract
```

```
mkVec Nat 3 ⇝ λ(arr:Array 3 Nat). dpair Nat (λ(n:Nat). Array n Nat) 3 arr -- App
mkVec Nat 3 arr_abstract -- App
  arr_abstract ⇝ Array 3 Nat
  Array 3 Nat ⊑ Array 3 Nat ✓ -- Refl
  body[arr := Array 3 Nat] = dpair Nat (λ(n:Nat). Array n Nat) 3 (Array 3 Nat)
```

Evaluating the dpair application:
```
⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 3 (Array 3 Nat)
```

**Result:** `vec3 ⇝ λ(X:Type).λ(k:λ(a:Nat).λ(_:Array a Nat).X). k 3 (Array 3 Nat)`

`vec3 ⊑ Vec Nat` ✓ (same structure as 1.3)

### vec3_len = vec3 Nat (λ(n:Nat). λ(_:Array n Nat). n)

```
vec3 Nat ⇝ λ(k:λ(a:Nat).λ(_:Array a Nat).Nat). k 3 (Array 3 Nat) -- App
```

```
vec3 Nat cont ⇝ cont 3 (Array 3 Nat) -- App (cont same as before)
  cont 3 ⇝ λ(_:Array 3 Nat). 3 -- App (3 ⊑ Nat ✓)
  cont 3 (Array 3 Nat) ⇝ 3 -- App (Array 3 Nat ⊑ Array 3 Nat ✓)
```

**Result:** `vec3_len ⇝ 3` ✓ — precision recovered because vec3 was transparently constructed with n=3.


## Task 2.5: Rejection of Failing Tests (§6.3)

### BAD1: (consArray Nat 0 10 (emptyArray Nat) : Array 2 Nat)

```
consArray Nat 0 10 (emptyArray Nat) ⇝ pair Nat Unit 10 unit -- (from 2.2)
```

This is `inner1 =β λ(X:Type).λ(k:λ(_:Nat).λ(_:Unit).X). k 10 unit`.

Asc requires `inner1 ⊑ Array 2 Nat =β Pair Nat (Pair Nat Unit)`.

This is exactly `consArray Nat 0 10 (emptyArray Nat) ⋢ Array 2 Nat` from Task 1.2.
Fails because `Unit ⊑ Pair Nat Unit` requires `λ(_:Nat).λ(_:Unit).X ⊑ X`, which is stuck. ∎

### BAD2: headArray Nat 0 (emptyArray Nat)

```
headArray Nat 0 ⇝ λ(arr:Array 1 Nat). arr Nat (λ(x:Nat).λ(_:Array 0 Nat). x) -- App
```

`Array 1 Nat =β Pair Nat Unit`. Domain is `Pair Nat Unit`.

```
emptyArray Nat ⇝ unit
unit ⊑ Pair Nat Unit?
```

This is `emptyArray Nat ⋢ Array 1 Nat` from Task 1.2. Fails. ∎

### BAD3: (true : Nat)

```
true ⇝ true -- Lam
Asc requires true ⊑ Nat
```

`true ⋢ Nat` from Task 1.1. Fails. ∎

### BAD4: (succ 2 : 2)

```
succ 2 ⇝ 3 -- App (via β-reduction)
Asc requires 3 ⊑ 2
```

`succ 2 ⋢ 2` (i.e., `3 ⋢ 2`) from Task 1.1. Fails. ∎

### BAD5: (emptyArray Nat : Array 1 Nat)

```
emptyArray Nat ⇝ unit
Asc requires unit ⊑ Array 1 Nat =β Pair Nat Unit
```

Same as BAD2. `emptyArray Nat ⋢ Array 1 Nat` from Task 1.2. Fails. ∎

### BAD6: (pair Nat Bool 10 true : Pair Bool Nat)

```
pair Nat Bool 10 true ⇝ λ(X:Type).λ(k:λ(_:Nat).λ(_:Bool).X). k 10 true
Asc requires this ⊑ Pair Bool Nat =β λ(X:Type).λ(k:λ(_:Bool).λ(_:Nat).X).X
```

`Pair Nat Bool ⋢ Pair Bool Nat` from Task 1.1. Fails. ∎

### BAD7: headArray Nat 1 (emptyArray Nat)

```
headArray Nat 1 ⇝ λ(arr:Array 2 Nat). arr Nat (λ(x:Nat).λ(_:Array 1 Nat). x)
```

Domain: `Array 2 Nat =β Pair Nat (Pair Nat Unit)`.

```
emptyArray Nat ⇝ unit
unit ⊑ Pair Nat (Pair Nat Unit)?
```

Same failure pattern: `Unit ⋢ Pair Nat (Pair Nat Unit)`. Lam contra check
requires `λ(_:Nat).λ(_:Pair Nat Unit).X ⊑ X`, which is stuck. ∎