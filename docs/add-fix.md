# Och Extension: General Recursion (`fix`)

## Prerequisites

This extension builds on the core Och calculus defined in och-spec.md. All typing
rules, properties, and test cases from that document are assumed to be solved.
This extension adds one syntactic form and the associated typing/soundness machinery.

Unlike the `?` and implicit argument extensions, `fix` is NOT pure sugar — it adds
genuine expressiveness (recursive functions) and requires its own typing rule and
soundness proof.

---

## 1. Motivation

Without `fix`, Och is strongly normalizing — every well-typed term terminates.
This means you cannot write recursive functions like `mapArray` or `appendArrays`.
Church-encoded nats provide *bounded iteration* (folds), but the dependent
elimination problem prevents using folds when the return type changes at each step.

`fix` provides general recursion, allowing recursive functions that case-split
on Church-encoded data and recurse on substructure.

---

## 2. Syntax Extension

Add one syntactic form:

```
e ::= ... | fix e              -- general recursion (fixpoint)
```

The calculus becomes 7 forms total.

---

## 3. Semantics

### 3.1 Concrete Evaluation

```
fix (λf. e)  ⟶  e[f := fix (λf. e)]    -- fixpoint unrolling
```

### 3.2 Abstract Evaluation

The abstract interpreter checks `fix (λ(f: τ). e)` as follows:

1. The programmer provides (via the type annotation on `f`) the contract `τ` that
   the recursive function should satisfy.
2. The interpreter assumes `f : τ` holds for structurally smaller arguments
   (the inductive hypothesis).
3. The interpreter checks that the body `e` satisfies `τ` under this assumption.
4. The interpreter verifies that every recursive call `f x` uses an argument `x`
   that is structurally smaller than the original input.

This is essentially an induction principle: prove the base case, prove the step
case assuming the inductive hypothesis, conclude the property holds for all inputs.

### 3.3 Interaction with Partitioning

`fix` works together with the partitioning mechanism from the core spec. A typical
pattern is:

```
fix (λ(self: ...). λ(n: Nat). λ(arr: Array n T).
  (isZero n) ResultType
    base_case
    (... self (pred n) ... ))
```

The interpreter partitions on `isZero n`:
- Branch n=0: checks the base case, no recursive call
- Branch n=succ k: checks the step case with `self` assumed at `k = pred n`,
  which is structurally smaller

---

## 4. Evaluation Strategy

`fix` introduces potential non-termination. The evaluation strategy matters:

- **Call-by-value:** `fix (λf. e)` diverges unless `e` is a lambda (the fixpoint
  must be "guarded"). In practice, `fix` is always applied to a lambda.
- **Call-by-name:** `fix` can be unfolded lazily.
- **Abstract interpreter:** Operates by induction, not by unfolding. The interpreter
  never actually unfolds `fix` — it checks the contract via the inductive hypothesis
  pattern described above.

---

## 5. Properties

### 5.1 `fix` Soundness

`fix (λ(f: τ). e)` is well-typed with type `τ` if, assuming `f` satisfies `τ` at
structurally smaller arguments, the body `e` also satisfies `τ`.

Formally, this needs:
- A definition of "structurally smaller" for Church-encoded data
- A proof that the inductive hypothesis is sound: if the recursive call is at a
  smaller argument, the assumption `f : τ` at that argument is justified

### 5.2 Structural Descent for Church Encodings

For Church-encoded naturals, "structurally smaller" means: in the `isZero n = false`
branch (where `n = succ k`), the value `pred n = k` is smaller than `n`. The
interpreter must:
- Recognize that `isZero` partitions `Nat` into `{0}` and `{succ k | k : Nat}`
- Track that `pred n` in the successor branch yields `k`
- Accept recursive calls on `k` as structurally smaller than `succ k`

This is non-trivial because `pred` is itself a Church-encoded function, not a
primitive destructor. The interpreter needs to understand that `pred (succ k) = k`
by β-reduction.

### 5.3 Impact on Core Properties

- **Soundness:** Must be re-proved with the `fix` rule included. The inductive
  hypothesis pattern must be shown to be sound.
- **Monotonicity:** Must be checked for `fix`. If the contract `τ` is widened,
  the inductive hypothesis is widened, and the body must still check. This
  should hold if the core monotonicity property holds.
- **Transparency preservation:** `fix` terms are transparent unless ascribed.
  For concrete arguments, the interpreter can unfold and compute precisely.
  For abstract arguments, it uses the inductive hypothesis.

---

## 6. Definitions Enabled by `fix`

The following definitions become possible with `fix` and should be added to the
standard library.

### 6.1 mapArray

```
mapArray = fix (λ(self: λ(T: Type). λ(U: Type). λ(_: T → U). λ(n: Nat). λ(_: Array n T). Array n U).
           λ(T: Type). λ(U: Type). λ(f: T → U). λ(n: Nat). λ(arr: Array n T).
           (isZero n) (Array n U)
             (emptyArray U)
             (arr (Array n U)
               (λ(x: T). λ(rest: Array (pred n) T).
                 consArray U (pred n) (f x) (self T U f (pred n) rest))));
  -- mapArray ⊑ λ(T: Type). λ(U: Type). λ(_: T → U). λ(n: Nat). λ(_: Array n T). Array n U
  --
  -- Verification for abstract n : Nat:
  --   isZero n partitions into {0} and {succ k | k : Nat}
  --   Branch n=0:
  --     emptyArray U : Array 0 U = Array n U  ✓ (n=0)
  --   Branch n=succ k:
  --     arr : Array (succ k) T = Pair T (Array k T)
  --     Eliminate arr: x : T, rest : Array k T
  --     pred n = k in this branch
  --     self T U f k rest : Array k U  (inductive hypothesis)
  --     consArray U k (f x) (self T U f k rest) : Array (succ k) U = Array n U  ✓
  --   Termination: k < succ k  ✓
```

### 6.2 appendArrays

```
appendArrays = fix (λ(self: λ(T: Type). λ(n: Nat). λ(m: Nat). λ(_: Array n T). λ(_: Array m T). Array (add n m) T).
               λ(T: Type). λ(n: Nat). λ(m: Nat).
               λ(a: Array n T). λ(b: Array m T).
               (isZero n) (Array (add n m) T)
                 b
                 (a (Array (add n m) T)
                   (λ(x: T). λ(rest: Array (pred n) T).
                     consArray T (add (pred n) m) x (self T (pred n) m rest b))));
  -- appendArrays ⊑ λ(T: Type). λ(n: Nat). λ(m: Nat). λ(_: Array n T). λ(_: Array m T). Array (add n m) T
  --
  -- Verification for abstract n, m : Nat:
  --   Branch n=0:
  --     Need: Array (add 0 m) T.  Reduce: add 0 m = m.
  --     Have: b : Array m T  ✓
  --   Branch n=succ k:
  --     a : Pair T (Array k T).  Eliminate: x : T, rest : Array k T.
  --     pred n = k in this branch.
  --     self T k m rest b : Array (add k m) T  (inductive hypothesis)
  --     consArray T (add k m) x (self T k m rest b)
  --       : Array (succ (add k m)) T
  --     Need: Array (add (succ k) m) T
  --     Reduce: add (succ k) m = succ (add k m)  ✓
  --   Termination: k < succ k  ✓
```

### 6.3 mapVec and appendVec

```
mapVec = λ(T: Type). λ(U: Type). λ(f: T → U). λ(v: Vec T).
         v (Vec U) (λ(n: Nat). λ(arr: Array n T).
           mkVec U n (mapArray T U f n arr));
  -- mapVec ⊑ λ(T: Type). λ(U: Type). λ(_: T → U). λ(_: Vec T). Vec U
  -- Transparent: caller can see output length = input length (same n)

appendVec = λ(T: Type). λ(v1: Vec T). λ(v2: Vec T).
            v1 (Vec T) (λ(n1: Nat). λ(arr1: Array n1 T).
              v2 (Vec T) (λ(n2: Nat). λ(arr2: Array n2 T).
                mkVec T (add n1 n2) (appendArrays T n1 n2 arr1 arr2)));
  -- appendVec ⊑ λ(T: Type). λ(_: Vec T). λ(_: Vec T). Vec T
  -- Transparent: caller can see output length = add n1 n2
```

---

## 7. Test Cases (Require `fix`)

These tests should be added to the acceptance criteria once `fix` is implemented.

### 7.1 Concrete

```
arr1 = consArray Nat 1 10 (consArray Nat 0 20 (emptyArray Nat));
arr2 = consArray Nat 2 30 (consArray Nat 1 40 (consArray Nat 0 50 (emptyArray Nat)));
vec1 = mkVec Nat 2 arr1;
vec2 = mkVec Nat 3 arr2;

result = appendVec Nat vec1 vec2;
  -- EXPECT: result ⊑ Vec Nat
  -- EXPECT (precise): length is 5

doubled = mapVec Nat Nat (λ(x: Nat). add x x) vec1;
  -- EXPECT: doubled ⊑ Vec Nat
  -- EXPECT (precise): length is 2
```

### 7.2 Abstract

```
v1 = (... : Vec Nat);
v2 = (... : Vec Nat);

result = appendVec Nat v1 v2;
  -- EXPECT: result ⊑ Vec Nat
  -- Transparent: output length = add n1 n2 for abstract n1, n2

mapped = mapVec Nat Nat (λ(x: Nat). add x x) v1;
  -- EXPECT: mapped ⊑ Vec Nat
  -- Length preserved: same abstract n
```

### 7.3 Failures

```
BAD_FIX1 = appendArrays Nat 2 3 (emptyArray Nat) arr2;
  -- MUST FAIL: emptyArray Nat : Array 0 Nat, but expected Array 2 Nat
```

---

## 8. Open Questions

### 8.1 Termination Checking Strategy

Options for verifying structural descent:
- **Syntactic:** Require recursive calls to use `pred` on a variable that was
  partitioned by `isZero`. Simple but brittle.
- **Semantic:** Track a well-founded ordering on abstract values. More general
  but harder to formalize for Church-encoded data.
- **Trust the user:** Accept any `fix` and let non-termination be the user's
  problem. Consistent with the "decidability is a non-goal" philosophy but
  weakens the theorem prover guarantees.

### 8.2 Dependent Elimination via Fold

An alternative to `fix` for some cases: define a dependent fold for Church nats
that carries a type-level motive. This would avoid `fix` for cases like `mapArray`
but is itself a non-trivial addition. If the core system's abstract interpretation
is powerful enough, it may be able to verify fold-based definitions without `fix`.

### 8.3 Interaction with Transparency

For concrete arguments, the abstract interpreter could unfold `fix` finitely and
compute the precise result. For example, `mapArray Nat Nat f 2 arr` could be
unfolded twice to produce the precise mapped array. This is sound but potentially
expensive. A practical interpreter might limit unfolding depth.