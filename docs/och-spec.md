# Och: Specification and Test Suite

## 1. Purpose

Och is a minimal research calculus designed to answer the question:

> Can a language where terms are their own most precise types support a sound, monotone
> notion of typing via abstract interpretation, with Church encodings as the only data
> representation?

This document defines the syntax of Och, its intended semantic properties, and a
comprehensive test case. The goal is to provide enough information for a reader to
derive typing rules (as natural deduction judgments) such that the test case is
accepted and the core properties hold.

---

## 2. Core Philosophy

**Types are sets of values.** There is no separate type language. Terms and types share
a single syntactic category. The most precise type of a value is the value itself.
Type ascription is the only mechanism for deliberately losing precision.

**Typing is abstract interpretation.** Rather than syntax-directed typing rules in the
traditional sense, the system abstractly executes the program over sets of values.
A term's type is the set of values it could evaluate to, given what is known about
its free variables.

**Subtyping is set inclusion.** `A ⊑ B` means every value in the set `A` is also in
the set `B`.

**Transparency by default.** Function bodies are visible to the abstract interpreter
unless the programmer explicitly introduces an ascription `(e : T)` to discard
precision. This means the caller of a transparent function can see exactly what the
body computes, and the abstract interpreter propagates precise types through it.

**No native data types.** All data (booleans, naturals, pairs, etc.) is Church-encoded
using only lambda abstractions. The type system must handle anything a user can build
with functions, because Church encodings are just ordinary functional programs.

**A note on set language**. Throughout this document, phrases like "set of values,"
"set inclusion," and "member of the set" are used to communicate the semantic
intuition behind the type system. However, types in Och are not sets — they are
terms (lambda expressions and Type). The typing rules and proofs should operate
entirely on terms, using β-reduction and pointwise subtyping, not set operations.
For example, true ⊑ Bool is not checked by enumerating a set — it is checked by
comparing the bodies of true and Bool pointwise under their shared parameter
bindings. The set interpretation justifies why the rules are correct, but the
rules themselves are purely syntactic.

---

## 3. Syntax

### 3.1 Core Calculus

```
e, τ ::=
  | x                          -- variable
  | λ(x: τ). e                -- lambda abstraction
  | e₁ e₂                     -- application
  | (e : τ)                    -- ascription (deliberate precision loss)
  | Type                       -- universe of types
```

That's it. Five forms. Let bindings `x = e₁; e₂` are sugar for `(λ(x: _). e₂) e₁`.

### 3.2 What Is NOT in the Syntax

- No `match` or pattern matching (Church-encoded eliminators serve this role)
- No inductive type declarations
- No general recursion / fixpoint (future extension, see add-fix.md)
- No implicit arguments (future extension, see add-implicits.md)
- No CPS bind operator (future extension, see add-cps.md)
- No module system
- No mutation or references
- No separate "dependent function type" / `∀` former. In standard type theory,
  `λ(x: A). e` is a function (a value) and `∀(x: A). B` is the type of such
  functions (a set). In Och, these are unified: `λ(x: A). B` serves both roles.
  As a value, it is a specific function that computes `B` from `x`. As a type
  (a set to check membership against), it denotes the set of all functions `f`
  such that `f x ⊑ (λ(x: A). B) x = B` for all `x ⊑ A`. This is checked
  pointwise via function subtyping. For example, `succ ⊑ λ(_: Nat). Nat` holds
  because for any `x : Nat`, `succ x ⊑ Nat`. This eliminates the need for a
  separate type former and is consistent with the terms-as-types philosophy.

---

## 4. Semantics

### 4.1 Concrete Evaluation

Standard lambda calculus evaluation.

```
(λ(x: τ). e) v  ⟶  e[x := v]            -- β-reduction
(e : τ)          ⟶  e                     -- ascription erased at runtime
```

### 4.2 Abstract Evaluation (Typing)

The abstract interpreter evaluates programs over **sets of values** rather than
individual values. The "type" of an expression is the set of values it could produce.

Key behaviors:

1. **Variables:** If `x` has type `τ` in the environment, the abstract value of `x`
   is the set `τ`.

2. **Lambda:** `λ(x: τ). e` is its own most precise type — the singleton set
   containing this specific function. If ascribed, precision is reduced.

3. **Application:** To abstractly evaluate `f a`, the interpreter looks at `f`.
   - If `f` is **transparent** (no ascription on the output), the interpreter
     substitutes the abstract value of `a` into the body of `f` and abstractly
     evaluates the body. This propagates precision.
   - If `f` is **ascribed** (output has `(body : τ)`), the interpreter returns `τ`
     without looking through the body.

4. **Ascription:** `(e : τ)` abstractly evaluates to `τ`, discarding any precision
   from `e`. The interpreter must verify `e ⊑ τ` (soundness check).

5. **Branching / Church-encoded elimination:** When the interpreter encounters a
   Church-encoded boolean or natural being used as an eliminator with an abstract
   (unknown) value, it **partitions** the set of possible values and checks each
   branch with the appropriately narrowed environment.

   For example, `isZero n` where `n : Nat`:
   - True branch: `n` narrowed to `{0}`
   - False branch: `n` narrowed to `{succ k | k : Nat}`, with `k : Nat` bound

### 4.3 Subtyping

Subtyping is set inclusion. Core rules:

- `e ⊑ e` for any value `e` (reflexivity)
- If `A ⊑ B` and `B ⊑ C` then `A ⊑ C` (transitivity)
- `e ⊑ τ` if the value `e` is a member of the set `τ`
- `λ(x: A₁). B₁ ⊑ λ(x: A₂). B₂` if `A₂ ⊑ A₁` (contravariant) and
  `B₁[x] ⊑ B₂[x]` for all `x ⊑ A₂` (covariant). This is pointwise: a function
  `f` is in the set `λ(x: A). B` iff for every `x ⊑ A`, `f x ⊑ B[x]`.
- Singleton subtyping: the term `3` (a specific Church numeral) satisfies `3 ⊑ Nat`
  because the value `3` is in the set of all Church numerals.

### 4.4 Terms-as-Types

Since terms and types share a language:

- The numeral `3 = λ(X: Type). λ(z: X). λ(s: X → X). s (s (s z))` is simultaneously
  a value (a Church numeral) and a type (the singleton set containing exactly that
  Church numeral).
- `Nat = λ(X: Type). λ(z: X). λ(s: X → X). X` is both a type (the set of all Church
  numerals) and a term.
- `3 ⊑ Nat` because the value `3` is in the set `Nat`.
- If `n : 3` then the abstract interpreter knows `n` equals `3` definitionally.
  This means `Array n T` and `Array 3 T` are the same type.

---

## 5. Standard Library (Church Encodings)

All definitions below use only the core syntax. Each definition is annotated with its
intended type (which the abstract interpreter should be able to verify). All type
arguments are explicit.

### 5.1 Booleans

```
Bool = λ(X: Type). λ(t: X). λ(f: X). X;

true  = λ(X: Type). λ(t: X). λ(f: X). t;
false = λ(X: Type). λ(t: X). λ(f: X). f;

-- Subtyping: true ⊑ Bool, false ⊑ Bool
-- Precise types: true is the singleton {true}, false is the singleton {false}
```

### 5.2 Unit

```
Unit = λ(X: Type). λ(x: X). X;
unit = λ(X: Type). λ(x: X). x;

-- unit ⊑ Unit
-- Unit has exactly one inhabitant: unit
```

### 5.3 Natural Numbers

```
Nat = λ(X: Type). λ(z: X). λ(s: X → X). X;

0 = λ(X: Type). λ(z: X). λ(s: X → X). z;
1 = λ(X: Type). λ(z: X). λ(s: X → X). s z;
2 = λ(X: Type). λ(z: X). λ(s: X → X). s (s z);
3 = λ(X: Type). λ(z: X). λ(s: X → X). s (s (s z));

succ = λ(n: Nat). λ(X: Type). λ(z: X). λ(s: X → X). s (n X z s);
  -- succ : Nat → Nat
  -- Transparent: succ 2 has precise type 3

add = λ(n: Nat). λ(m: Nat). n Nat m succ;
  -- add : Nat → Nat → Nat
  -- Key reductions:
  --   add 0 m = m
  --   add (succ k) m = succ (add k m)

isZero = λ(n: Nat). n Bool true (λ(_: Bool). false);
  -- isZero : Nat → Bool
  -- Transparent body. For abstract n : Nat, the interpreter partitions:
  --   isZero n = true   ⟹   n = 0
  --   isZero n = false  ⟹   n = succ k for some k : Nat

pred = λ(n: Nat). λ(X: Type). λ(z: X). λ(s: X → X).
       n (X → X) (λ(_: X). z) (λ(g: X → X). λ(h: (X → X) → X). h (g s)) (λ(x: X). x);
  -- pred : Nat → Nat
  -- pred 0 = 0, pred (succ k) = k
```

### 5.4 Non-Dependent Pairs

```
Pair = λ(A: Type). λ(B: Type). λ(X: Type). λ(k: λ(_: A). B → X). X;

pair = λ(A: Type). λ(B: Type). λ(a: A). λ(b: B).
       λ(X: Type). λ(k: λ(_: A). B → X). k a b;
  -- pair ⊑ λ(A: Type). λ(B: Type). λ(_: A). λ(_: B). Pair A B

-- Elimination: given p : Pair Nat Bool, use p directly as an eliminator:
--   p ResultType (λ(a: Nat). λ(b: Bool). <body using a and b>)
```

### 5.5 Dependent Pairs (Σ-types)

```
Sigma = λ(A: Type). λ(B: λ(_: A). Type).
        λ(X: Type). λ(k: λ(a: A). λ(_: B a). X). X;

dpair = λ(A: Type). λ(B: λ(_: A). Type). λ(a: A). λ(b: B a).
        λ(X: Type). λ(k: λ(a: A). λ(_: B a). X). k a b;
  -- dpair ⊑ λ(A: Type). λ(B: λ(_: A). Type). λ(a: A). λ(_: B a). Sigma A B

-- Elimination: given s : Sigma Nat (λ(n: Nat). Array n T):
--   s ResultType (λ(n: Nat). λ(arr: Array n T). <body>)
-- Inside the body, arr's type depends on n. This is where Church-encoded
-- dependent pairs work: both components are in scope simultaneously.
```

### 5.6 Arrays (Length-Indexed Nested Pairs)

```
Array = λ(n: Nat). λ(T: Type). n Type Unit (λ(acc: Type). Pair T acc);
  -- Array : Nat → Type → Type
  -- Array 0 T = Unit
  -- Array 1 T = Pair T Unit
  -- Array 2 T = Pair T (Pair T Unit)
  -- Array (succ k) T = Pair T (Array k T)

emptyArray = λ(T: Type). unit;
  -- emptyArray ⊑ λ(T: Type). Array 0 T

consArray = λ(T: Type). λ(n: Nat). λ(x: T). λ(rest: Array n T).
            pair T (Array n T) x rest;
  -- consArray ⊑ λ(T: Type). λ(n: Nat). λ(_: T). λ(_: Array n T). Array (succ n) T
  -- Valid because Array (succ n) T = Pair T (Array n T)
```

### 5.7 Array Operations

```
headArray = λ(T: Type). λ(n: Nat). λ(arr: Array (succ n) T).
            arr T (λ(x: T). λ(_: Array n T). x);
  -- headArray ⊑ λ(T: Type). λ(n: Nat). λ(_: Array (succ n) T). T

tailArray = λ(T: Type). λ(n: Nat). λ(arr: Array (succ n) T).
            arr (Array n T) (λ(_: T). λ(rest: Array n T). rest);
  -- tailArray ⊑ λ(T: Type). λ(n: Nat). λ(_: Array (succ n) T). Array n T
```

### 5.8 Vectors

```
Vec = λ(T: Type). Sigma Nat (λ(n: Nat). Array n T);
  -- Vec T = ∃(n: Nat). Array n T

mkVec = λ(T: Type). λ(n: Nat). λ(arr: Array n T). dpair Nat (λ(n: Nat). Array n T) n arr;
  -- mkVec ⊑ λ(T: Type). λ(n: Nat). λ(_: Array n T). Vec T

-- Elimination: given v : Vec T:
--   v ResultType (λ(n: Nat). λ(arr: Array n T). <body>)

-- Note: mapVec and appendVec require general recursion (fix) and are
-- defined in add-fix.md. Without fix, vectors can be constructed,
-- packed, unpacked, and their components accessed, but not recursively
-- transformed.
```

---

## 6. Test Case

### 6.1 Concrete Instantiation (Full Precision)

```
-- Array construction
arr1 = consArray Nat 1 10 (consArray Nat 0 20 (emptyArray Nat));
  -- EXPECT: arr1 ⊑ Array 2 Nat
  -- EXPECT (precise): arr1 is its own most precise type

arr2 = consArray Nat 2 30 (consArray Nat 1 40 (consArray Nat 0 50 (emptyArray Nat)));
  -- EXPECT: arr2 ⊑ Array 3 Nat

-- Array access
h = headArray Nat 1 arr1;
  -- EXPECT: h ⊑ Nat
  -- EXPECT (precise): h = 10

t = tailArray Nat 1 arr1;
  -- EXPECT: t ⊑ Array 1 Nat
  -- EXPECT (precise): t = consArray Nat 0 20 (emptyArray Nat)

-- Vector construction
vec1 = mkVec Nat 2 arr1;
  -- EXPECT: vec1 ⊑ Vec Nat
  -- EXPECT (precise): length is 2

vec2 = mkVec Nat 3 arr2;
  -- EXPECT: vec2 ⊑ Vec Nat
  -- EXPECT (precise): length is 3

-- Vector elimination (unpack and use both components)
vecSum = vec1 Nat (λ(n: Nat). λ(arr: Array n Nat). n);
  -- EXPECT: vecSum ⊑ Nat
  -- EXPECT (precise): vecSum = 2

-- Dependent pair: arr's type depends on n inside the continuation
vecHead = vec1 Nat (λ(n: Nat). λ(arr: Array n Nat).
            headArray Nat (pred n) arr);
  -- EXPECT: vecHead ⊑ Nat
  -- EXPECT (precise): vecHead = 10
  -- Note: this requires the interpreter to see that n=2 in the
  -- transparent case, so pred n = 1, and arr : Array 2 Nat = Pair Nat (Pair Nat Unit)

-- Arithmetic at the type level
five = add 2 3;
  -- EXPECT (precise): five = 5

-- Type-level array computation
A0 = Array 0 Nat;
  -- EXPECT: A0 = Unit (by β-reduction of 0 Type Unit (λacc. Pair Nat acc))

A2 = Array 2 Nat;
  -- EXPECT: A2 = Pair Nat (Pair Nat Unit)

-- Church boolean as eliminator
r1 = true Nat 10 20;
  -- EXPECT (precise): r1 = 10

r2 = false Nat 10 20;
  -- EXPECT (precise): r2 = 20

-- isZero
iz0 = isZero 0;
  -- EXPECT (precise): iz0 = true

iz3 = isZero 3;
  -- EXPECT (precise): iz3 = false

-- Composing: isZero feeds into boolean elimination
branch = (isZero 0) Nat 100 200;
  -- EXPECT (precise): branch = 100
```

### 6.2 Abstract Instantiation (Ascribed Inputs)

```
v1 = (... : Vec Nat);    -- abstract, length unknown
v2 = (... : Vec Nat);    -- abstract, length unknown

-- Unpack abstract vector: extract length
len = v1 Nat (λ(n: Nat). λ(arr: Array n Nat). n);
  -- EXPECT: len ⊑ Nat
  -- NOT precise: n is abstract, so len is abstract Nat

-- Unpack abstract vector: head of abstract vector
-- Note: this should fail or require additional info, because we
-- don't know if the vector is non-empty!
-- See BAD2-style reasoning.

-- Unpack and repack: wrap in a new vector (identity on vectors)
rewrapped = v1 (Vec Nat) (λ(n: Nat). λ(arr: Array n Nat). mkVec Nat n arr);
  -- EXPECT: rewrapped ⊑ Vec Nat
  -- Transparent: caller can see this is just repacking with same n

-- Pair two abstract vectors' lengths
combinedLen = v1 Nat (λ(n1: Nat). λ(_: Array n1 Nat).
               v2 Nat (λ(n2: Nat). λ(_: Array n2 Nat).
                 add n1 n2));
  -- EXPECT: combinedLen ⊑ Nat
  -- Transparent: caller can see this is add n1 n2 for abstract n1, n2

-- Ascribe with partial precision: known length, unknown contents
arr_abstract = (... : Array 3 Nat);
vec3 = mkVec Nat 3 arr_abstract;
  -- EXPECT: vec3 ⊑ Vec Nat
  -- More precise: length is known to be 3

vec3_len = vec3 Nat (λ(n: Nat). λ(_: Array n Nat). n);
  -- EXPECT (precise): vec3_len = 3
  -- Because vec3 is transparent and was constructed with n=3
```

### 6.3 Tests That Must FAIL

```
BAD1 = (consArray Nat 0 10 (emptyArray Nat) : Array 2 Nat);
  -- MUST FAIL: this is an Array 1 Nat, not Array 2 Nat

BAD2 = headArray Nat 0 (emptyArray Nat);
  -- MUST FAIL: emptyArray Nat : Array 0 Nat = Unit
  -- headArray expects Array (succ n) T = Pair T (Array n T)

BAD3 = (true : Nat);
  -- MUST FAIL: true is not in the set Nat

BAD4 = (succ 2 : 2);
  -- MUST FAIL: succ 2 = 3, and 3 ∉ {2}

BAD5 = (emptyArray Nat : Array 1 Nat);
  -- MUST FAIL: emptyArray Nat : Unit, Array 1 Nat = Pair Nat Unit

BAD6 = (pair Nat Bool 10 true : Pair Bool Nat);
  -- MUST FAIL: Pair Nat Bool ≠ Pair Bool Nat

BAD7 = headArray Nat 1 (emptyArray Nat);
  -- MUST FAIL: emptyArray Nat : Array 0 Nat, expected Array (succ 1) Nat = Array 2 Nat
```

### 6.4 Transparency Tests

```
id = λ(T: Type). λ(x: T). x;

precise_3 = id Nat 3;
  -- EXPECT (precise): precise_3 = 3 (not just Nat)
  -- id is transparent, interpreter evaluates the body.

id_ascribed = λ(T: Type). λ(x: T). (x : T);

imprecise_3 = id_ascribed Nat 3;
  -- EXPECT: imprecise_3 : Nat (not 3)
  -- Ascription (x : T) with T=Nat discards the precision.

double = λ(x: Nat). add x x;

precise_6 = double 3;
  -- EXPECT (precise): precise_6 = 6
  -- Transparent, interpreter computes add 3 3 = 6.

abstract_double = double (... : Nat);
  -- EXPECT: abstract_double : Nat
```

---

## 7. Core Properties

### 7.1 Soundness

If the abstract interpreter says expression `e` has type `τ` in environment `Γ`,
and `e` concretely evaluates to value `v` under a concrete environment consistent
with `Γ`, then `v ∈ τ`.

```
If  Γ ⊢ e ⇝ τ  and  γ ⊨ Γ  and  γ ⊢ e ⇓ v,  then  v ∈ τ.
```

Where `Γ ⊢ e ⇝ τ` means "abstract evaluation of e in Γ yields τ", `γ ⊨ Γ` means
"concrete environment γ is consistent with abstract environment Γ" (for every
`x: σ` in `Γ`, `γ(x) ∈ σ`), and `γ ⊢ e ⇓ v` means "concrete evaluation of e
in γ produces v."

### 7.2 Monotonicity

Narrowing the abstract environment narrows (or preserves) the abstract result.

```
If  Γ₂ ⊑ Γ₁  then  (Γ₁ ⊢ e ⇝ τ₁)  and  (Γ₂ ⊢ e ⇝ τ₂)  implies  τ₂ ⊑ τ₁.
```

Where `Γ₂ ⊑ Γ₁` means Γ₂ is more precise (narrower) than Γ₁: for each
`x: σ₂` in `Γ₂` and `x: σ₁` in `Γ₁`, `σ₂ ⊑ σ₁`.

The practical use: if you typecheck a function body with `x : Nat` (wide) and
get result type `τ`, then any caller passing `x : 3` (narrow, since `3 ⊑ Nat`)
will get a result that is `⊑ τ`. The wide check covers all narrower inputs.

Note: this is equivalent to stating it in the widening direction ("widening the
environment widens the result"). Both are the same property — `⊑` is a preorder,
so `A ⊑ B ⟹ f(A) ⊑ f(B)` can be read from either end. The narrowing direction
is used here because it more directly matches the usage pattern: "typecheck once
at the declared type, reuse for all subtypes."

This is addressed by the transparency/ascription mechanism:
- **Transparent functions**: The interpreter evaluates the body directly with the
  abstract input. Monotonicity of abstract evaluation (not the type signature)
  is what matters.
- **Ascribed functions**: Output type is fixed, trivially monotone.

### 7.3 Ascription Soundness

Ascription only widens. `(e : τ)` is well-formed only if `e ⊑ τ`.

```
If  Γ ⊢ e ⇝ σ  and  (e : τ) is well-formed,  then  σ ⊑ τ.
```

### 7.4 Transparency Preservation

Without ascription, the abstract interpreter computes the most precise type
possible. For a closed term `e` that evaluates to `v`:

```
∅ ⊢ e ⇝ τ  implies  τ = {v}  (the singleton set).
```

### 7.5 Partition Correctness

When the abstract interpreter partitions on a Church-encoded eliminator, the
partition is exhaustive and each branch's narrowing is sound.

For `isZero`:
```
∀ n ∈ Nat:
  (isZero n = true  ⟹  n = 0)  ∧
  (isZero n = false ⟹  ∃k ∈ Nat. n = succ k)
∧ {0} ∪ {succ k | k ∈ Nat} = Nat
```

### 7.6 Subtyping and Type Checking Decidability (Non-Goal)

Both may be **undecidable**. This is accepted. Och is a theorem prover foundation.
Non-termination of the type checker is the user's responsibility to avoid.

---

## 8. Key Reductions

These equalities arise during type checking and must be established by β-reduction.

### 8.1 Arithmetic

```
add 0 m         = m               -- 0 m succ = m
add (succ k) m  = succ (add k m)  -- (succ k) m succ = succ (k m succ)
```

### 8.2 Array Structure

```
Array 0 T         = Unit
Array (succ k) T  = Pair T (Array k T)
```

Derivation:
```
Array 0 T = 0 Type Unit (λacc. Pair T acc) = Unit
Array (succ k) T = (λacc. Pair T acc) (Array k T) = Pair T (Array k T)
```

### 8.3 isZero

```
isZero 0         = true
isZero (succ k)  = false
```

### 8.4 Predecessor

```
pred 0         = 0
pred (succ k)  = k
```

---

## 9. Open Questions

### 9.1 Universe Consistency

`Type : Type` is assumed for simplicity, introducing Girard's paradox. A universe
hierarchy is needed for a real theorem prover but is orthogonal to the core ideas.

### 9.2 Membership Checking

How does the abstract interpreter verify `true ⊑ Bool`? Both are lambda terms.
Formalizing "value v is in the set denoted by type τ" for Church-encoded types
requires a precise semantics of set membership for lambda terms. This is one of
the central challenges.

---

## 10. What Is Needed

A reader of this document should derive:

1. **Judgment forms:** Suggested starting point: `Γ ⊢ e ⇝ τ`.

2. **Typing rules:** Natural deduction rules for each of the 5 syntactic forms
   (variable, lambda, application, ascription, Type).

3. **Subtyping rules:** Function subtyping (contravariant/covariant), singleton
   subtyping (term as precise type), Church-encoded type membership.

4. **Partition/narrowing rules:** How the abstract interpreter narrows the
   environment when a Church-encoded eliminator branches. Must be formalized for
   at least Bool elimination and Nat elimination via isZero.

5. **Proofs** that the derived rules satisfy: soundness (§7.1), monotonicity (§7.2),
   ascription soundness (§7.3), and transparency preservation (§7.4).

The test case in §6 is the acceptance criterion: accept §6.1, §6.2, §6.4; reject §6.3.