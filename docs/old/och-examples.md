# Och Test Suite

Conformance tests for the Och₀ typing rules. Each test specifies
a program, the expected result, and whether the current rules agree.

See ./och.md for the typing rules.

## Definitions

```
Bool  = (T: ⊤) → (x: T) → (y: T) → T
True  = (T: ⊤) → (x: T) → (y: T) → x
False = (T: ⊤) → (x: T) → (y: T) → y

Pick  = (b: Bool) → b ((x: ⊤) → ⊤) ((x: ⊤) → x) ((x: ⊤) → ⊤)
```

## Group 1: Basics

| #  | Program                           | Expected | Current rules | Notes              |
|----|-----------------------------------|----------|---------------|--------------------|
| 1  | `· ⊢ ⊤ ⇒ ⊤`                     | Accept   | ✓             | T-Top              |
| 2  | `· ⊢ (x: ⊤) → x ⇒ (x: ⊤) → x` | Accept   | ✓             | T-Fun              |
| 3  | `· ⊢ ((x: ⊤) → x) ⊤ ⇒ ⊤`       | Accept   | ✓             | T-App, subst x ≔ ⊤ |
| 4  | `· ⊢ ⊤ ⊤ ⇒ ⊤`                   | Reject   | ✓             | ⊤ is not a function type; T-App can't fire |

## Group 2: Subtyping

| #  | Program                      | Expected | Current rules | Notes                              |
|----|------------------------------|----------|---------------|------------------------------------|
| 5  | `· ⊢ (x: ⊤) → x ⊑ (x: ⊤) → ⊤` | Accept | ✓           | S-Fun + S-Top on body              |
| 6  | `· ⊢ (x: ⊤) → ⊤ ⊑ (x: ⊤) → x` | Reject | ✓           | Would need ⊤ ⊑ x, no rule for it  |
| 7  | `· ⊢ True ⊑ Bool`                | Accept | ✓           | S-Var at leaf: x ⊑ T              |
| 8  | `· ⊢ False ⊑ Bool`               | Accept | ✓           | Symmetric, y ⊑ T at leaf          |
| 9  | `· ⊢ False ⊑ True`               | Reject | ✓           | Fails at y ⊑ x                    |
| 10 | `· ⊢ Bool ⊑ True`                | Reject | ✓           | Fails at T ⊑ x                    |

## Group 3: Ascription

| #  | Program                                            | Expected | Current rules | Notes             |
|----|----------------------------------------------------|----------|---------------|-------------------|
| 11 | `· ⊢ True : Bool ⇒ Bool`                          | Accept   | ✓             | True ⊑ Bool       |
| 12 | `· ⊢ True : False ⇒ False`                        | Reject   | ✓             | True ⋢ False      |
| 13 | `· ⊢ ((x: ⊤) → x) : ((x: ⊤) → ⊤) ⇒ (x: ⊤) → ⊤` | Accept  | ✓             | Id ⊑ const-⊤     |

## Group 4: Dependent application (Pick)

| #  | Program                          | Expected          | Current rules | Notes                          |
|----|----------------------------------|--------------------|---------------|--------------------------------|
| 14 | `· ⊢ Pick True ⇒ (x: ⊤) → x`  | Accept             | ✓             | Church bool selects 1st branch |
| 15 | `· ⊢ Pick False ⇒ (x: ⊤) → ⊤` | Accept             | ✓             | Church bool selects 2nd branch |
| 16 | `b: Bool ⊢ Pick b ⇒ (x: ⊤) → ⊤` | Accept           | ✓             | Bool returns T, T = (x:⊤)→⊤   |

## Group 5: Monotonicity

The desired property:

> If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then `Γ' ⊢ M ⇒ A'`
> where `Γ' ⊢ A' ⊑ A`.

These tests check specific instances.

| #  | Program                            | Expected | Current rules | Notes                          |
|----|------------------------------------|----------|---------------|--------------------------------|
| 17 | `b: Bool ⊢ b ⇒ Bool`             | Accept   | ✓             | T-Var                          |
| 18 | `b: True ⊢ b ⇒ True`             | Accept   | ✓             | T-Var, more precise            |
| 19 | `True ⊑ Bool`                     | Accept   | ✓             | Monotonicity: 18 refines 17    |
| 20 | `b: Bool ⊢ Pick b ⇒ (x: ⊤) → ⊤` | Accept  | ✓             | = test 16                      |
| 21 | `b: True ⊢ Pick b ⇒ (x: ⊤) → x` | Accept  | ✓             | More precise input → output    |
| 22 | `(x: ⊤) → x ⊑ (x: ⊤) → ⊤`      | Accept  | ✓             | Monotonicity: 21 refines 20   |

## Group 6: The Original Bug (Already Fixed)

The Ochre monotonicity bug (Prop. 5.2.9) involved ascription to a
variable: `False : b`. In the current Och₀ rules, this is already
rejected in both environments, so there is no monotonicity violation.

| #  | Program                            | Expected | Current rules | Notes                          |
|----|------------------------------------|----------|---------------|--------------------------------|
| 23 | `b: Bool ⊢ False : b ⇒ b`        | Reject   | ✓             | No rule derives False ⊑ b      |
| 24 | `b: True ⊢ False : b ⇒ b`        | Reject   | ✓             | No rule derives False ⊑ b      |

The key insight: T-Asc checks `M' ⊑ A` (raw target). `False ⊑ b` is not
derivable because S-Var only goes left-to-right. Even if the old rule
(checking against evaluated target) were used, `False ⊑ Bool` would hold
but narrowing y would break it — this is exactly sharp edge #10.

## Group 7: T-Asc raw target check (sharp edge #10)

These tests verify that T-Asc checks against the raw target, not the
evaluated target. The counterexample `(x : y)` demonstrates that checking
against evaluated targets breaks monotonicity.

| #  | Program                                    | Expected | Current rules | Notes                              |
|----|--------------------------------------------|----------|---------------|------------------------------------|
| 25 | `x: Bool, y: Bool ⊢ (x : y) ⇒ ???`      | Reject   | ✓             | Bool ⋢ y (raw), no rule derives it |
| 26 | `x: Bool, y: True ⊢ (x : y) ⇒ ???`      | Reject   | ✓             | Bool ⋢ y (raw), same reason        |
| 27 | `x: True, y: Bool ⊢ (x : y) ⇒ ???`      | Reject   | ✓             | True ⋢ y (raw), same reason        |
| 28 | `x: T ⊢ (x : T) ⇒ ⊤`                     | Accept   | ✓             | T ⊑ T (S-Refl), T ⇒ ⊤ (T: ⊤)    |
| 29 | `x: T ⊢ (x : ⊤) ⇒ ⊤`                     | Accept   | ✓             | T ⊑ ⊤ (S-Top)                     |

## Group 8: Application typing without T-App-Top (sharp edge #12)

T-App is the only rule for typing applications. If the head does not
normalize to a function type, or the argument is untypeable or
incompatible with the domain, the application is rejected.

| #  | Program                                              | Expected | Current rules | Notes                              |
|----|------------------------------------------------------|----------|---------------|--------------------------------------|
| 30 | `f: ⊤ ⊢ f ((⊤ : (x: ⊤) → x)) ⇒ ⊤`               | Reject   | ✓             | f: ⊤, ⊤ ⇓ ⊤ (not a function), T-App can't fire |
| 31 | `f: (y: ⊤) → ⊤ ⊢ f ((⊤ : (x: ⊤) → x)) ⇒ ⊤`     | Reject   | ✓             | Arg (⊤ : (x:⊤)→x): T-Asc needs ⊤ ⊑ (x:⊤)→x, fails (⊤ not ⊑ function type). Arg untypeable, T-App fails at premise 3. |
| 32 | `· ⊢ ((x: ⊤) → x) ⊤ ⇒ ⊤`                          | Accept   | ✓             | T-App: head is function, ⊤ ⊑ ⊤, body evals to ⊤ |
| 33 | `g: (x: ⊤) → x, f: g ⊢ f ⊤ ⇒ ⊤`                  | Accept   | ✓             | T-App: f ⇒ g, g ⇓ (x:⊤)→x via HN-Var, ⊤ ⊑ ⊤, body evals to ⊤ |

## Group 9: S-App congruence

S-App says application is monotone: if M₁ ⊑ M₂ and N₁ ⊑ N₂, then
M₁ N₁ ⊑ M₂ N₂. Needed for the domain erasure lemma.

| #  | Program                                                          | Expected | Current rules | Notes                        |
|----|------------------------------------------------------------------|----------|---------------|------------------------------|
| 34 | `· ⊢ ((x: ⊤) → x) ⊤ ⊑ ((x: ⊤) → ⊤) ⊤`                      | Accept   | ✓             | S-App + S-Fun on fn, S-Refl |
| 35 | `· ⊢ ((x: ⊤) → ⊤) ⊤ ⊑ ((x: ⊤) → x) ⊤`                      | Reject   | ✓             | S-App needs fn ⊑, (x:⊤)→⊤ ⋢ (x:⊤)→x |

## Group 10: Deep domain erasure soundness (sharp edge #14)

These tests verify that the soundness counterexample from sharp edge #14
is resolved by deep domain erasure in E-Fun.

| #  | Program                                                          | Expected | Current rules | Notes                        |
|----|------------------------------------------------------------------|----------|---------------|------------------------------|
| 36 | `· ⊢ ((x: ⊤) → (y: ⊤) → (z: x) → z) (((w: ⊤) → w) : (w: ⊤) → ⊤) ⇒ (y: ⊤) → (z: ⊤) → z` | Accept | ✓ | T-App erases body: (z: x) becomes (z: ⊤) |
| 37 | (soundness: V ⊑ R for test 36)                                  | Accept   | ✓             | V = (y:⊤)→(z:⊤)→z = R; S-Refl |

## Group 11: HN-Eval — head normalization through applications (sharp edge #15)

These tests verify that ⇓ can see through application and ascription
terms in the environment via HN-Eval.

| #  | Program                                                          | Expected | Current rules | Notes                        |
|----|------------------------------------------------------------------|----------|---------------|------------------------------|
| 38 | `z: ((f: ⊤) → (x: ⊤) → (y: ⊤) → y) ⊤ ⊢ z ⊤ ⇒ (y: ⊤) → y` | Accept   | ✓             | HN-Eval: app ⇒ fun type, T-App fires |
| 39 | `z: (x: ⊤) → (y: ⊤) → y ⊢ z ⊤ ⇒ (y: ⊤) → y`                | Accept   | ✓             | Direct function type, T-App  |
| 40 | Tests 38 & 39 are a monotonicity pair: 38 refines 39            | Accept   | ✓             | (y:⊤)→y ⊑ (y:⊤)→y by S-Refl |

## Group 12: Abstract domain erasure in T-App (sharp edge #16)

T-App erases domains in the body before substitution, mirroring E-Fun's
deep erasure. Without this, the argument type lands in contravariant
positions, breaking monotonicity.

| #  | Program                                                          | Expected | Current rules | Notes                        |
|----|------------------------------------------------------------------|----------|---------------|------------------------------|
| 41 | `a: (w: ⊤) → ⊤ ⊢ ((x: ⊤) → (y: x) → y) a ⇒ (y: ⊤) → y`    | Accept   | ✓             | T-App erases domain x to ⊤  |
| 42 | `a: (w: ⊤) → w ⊢ ((x: ⊤) → (y: x) → y) a ⇒ (y: ⊤) → y`    | Accept   | ✓             | Same result: domain erased   |
| 43 | Tests 41 & 42 are a monotonicity pair: 42 refines 41            | Accept   | ✓             | (y:⊤)→y ⊑ (y:⊤)→y by S-Refl |

## Group 13: Church-encoded pairs and domain erasure

### Definitions

```
MkPair = (a: ⊤) → (b: ⊤) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b
Fst    = (p: ⊤) → p ⊤ ((x: ⊤) → (y: ⊤) → x)
Snd    = (p: ⊤) → p ⊤ ((x: ⊤) → (y: ⊤) → y)
```

A pair is a function that takes a handler `f` and applies it to both
components. `K` is the return type of the handler (Church-style type
parameter). `Fst` and `Snd` instantiate K = ⊤ and pass a handler that
returns the first or second argument.

### Typing MkPair True False — step by step

`MkPair True False` applies MkPair to True, then to False. Each T-App
erases the body before substituting.

**Step 1: MkPair True**

```
MkPair = (a: ⊤) → (b: ⊤) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b
                    ↑ body ↑
```

T-App erases body:

```
erase((b: ⊤) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b)
     = (b: ⊤) → (K: ⊤) → (f: ⊤) → f a b
                            ^^^
```

Note: the domain of `f` was `(x: ⊤) → (y: ⊤) → K` — erased to ⊤.
The body `f a b` survives (covariant position).

Substitute a ≔ True:

```
(b: ⊤) → (K: ⊤) → (f: ⊤) → f True b
```

T-Fun returns as-is. So `MkPair True ⇒` this term.

**Step 2: (MkPair True) False**

Body to erase: `(K: ⊤) → (f: ⊤) → f True b`

```
erase((K: ⊤) → (f: ⊤) → f True b)
     = (K: ⊤) → (f: ⊤) → erase(f) erase(True) erase(b)
     = (K: ⊤) → (f: ⊤) → f True† b
```

where `True† = erase(True) = (T: ⊤) → (x: ⊤) → (y: ⊤) → x`.

Erasure reached inside True (which was substituted into the body
at step 1) and replaced its inner domains `T` with `⊤`. The body
positions (`x` return) survived. This is an important observation:
**each T-App re-erases the entire body, including previously
substituted values.**

Substitute b ≔ False:

```
(K: ⊤) → (f: ⊤) → f True† False
```

(False appears in body position, so it survives this erasure step.
It will be erased when this term is itself used as a body in a
future T-App.)

**Result type of `MkPair True False`:**

```
· ⊢ MkPair True False ⇒ (K: ⊤) → (f: ⊤) → f True† False
```

### What the pair remembers and forgets

The pair's type `(K: ⊤) → (f: ⊤) → f True† False` tells us:
- ✓ It contains True† and False (body positions, survived erasure)
- ✓ True† still returns its first argument (`→ x` in body position)
- ✗ True†'s inner domains are ⊤ — it lost `(x: T)` becoming `(x: ⊤)`
- ✗ The handler type is ⊤ — we lost that f is a two-argument function
- ✗ K (the return type) is still present but disconnected from f's domain

The pair remembers **what** was stored (the values) but forgets the
**contract** on the handler (that it takes two arguments of specific
types). This is the cost of domain erasure: type-level constraints
that live in domain positions are erased.

### Fst and Snd

| #  | Program                                              | Expected | Current rules | Notes                        |
|----|------------------------------------------------------|----------|---------------|------------------------------|
| 44 | `· ⊢ MkPair True False ⇒ (K: ⊤) → (f: ⊤) → f True† False` | Accept | ✓ | True† = erase(True) |
| 45 | `· ⊢ Fst (MkPair True False) ⇒ ⊤`                  | Accept   | ✓             | See derivation below |
| 46 | `· ⊢ Snd (MkPair True False) ⇒ ⊤`                  | Accept   | ✓             | Symmetric |

**Derivation for test 45 (Fst):**

```
Fst = (p: ⊤) → p ⊤ ((x: ⊤) → (y: ⊤) → x)

Fst (MkPair True False):
  p ≔ MkPair True False
  body: p ⊤ ((x: ⊤) → (y: ⊤) → x)
  erase(body) = p ⊤ ((x: ⊤) → (y: ⊤) → x)  — already erased
  subst p ≔ (K: ⊤) → (f: ⊤) → f True† False:
    ((K: ⊤) → (f: ⊤) → f True† False) ⊤ ((x: ⊤) → (y: ⊤) → x)

  Now type this — two nested T-App calls:

  Step A: ((K: ⊤) → (f: ⊤) → f True† False) ⊤
    erase(body) = (f: ⊤) → f True† False
                  (True† gets re-erased, but it's already erased: True†† = True†)
    subst K ≔ ⊤: (f: ⊤) → f True† False
    Result: (f: ⊤) → f True† False

  Step B: ((f: ⊤) → f True† False) ((x: ⊤) → (y: ⊤) → x)
    erase(body) = erase(f True† False) = f True†† False†
                = f True† False†
    where False† = erase(False) = (T: ⊤) → (x: ⊤) → (y: ⊤) → y
    subst f ≔ (x: ⊤) → (y: ⊤) → x:
      ((x: ⊤) → (y: ⊤) → x) True† False†

  Now type this — two more T-App calls:

  Step C: ((x: ⊤) → (y: ⊤) → x) True†
    erase(body) = erase((y: ⊤) → x) = (y: ⊤) → x
    subst x ≔ True†: (y: ⊤) → True†
    Result: (y: ⊤) → True†

  Step D: ((y: ⊤) → True†) False†
    erase(body) = erase(True†) = True†  (idempotent)
    subst y ≔ False†: True†  (y not free in True†)
    Type True†: T-Fun → True† itself

  Final result: True† = (T: ⊤) → (x: ⊤) → (y: ⊤) → x
```

Wait — the result is True†, not ⊤. Let me reconsider.

Actually: `True† ⇒ True†` by T-Fun (it's a function literal). So
`Fst (MkPair True False) ⇒ True†`, which is `(T: ⊤) → (x: ⊤) → (y: ⊤) → x`.

This is more precise than ⊤! The pair actually does preserve the
first component's identity — just with erased inner domains.

| #  | Program                                              | Expected | Current rules | Notes                        |
|----|------------------------------------------------------|----------|---------------|------------------------------|
| 44 | `· ⊢ MkPair True False ⇒ (K: ⊤) → (f: ⊤) → f True† False` | Accept | ✓ | True† = erase(True) |
| 45 | `· ⊢ Fst (MkPair True False) ⇒ True†`              | Accept   | ✓             | Pair preserves values! |
| 46 | `· ⊢ Snd (MkPair True False) ⇒ False†`             | Accept   | ✓             | Symmetric |
| 47 | `· ⊢ True† ⊑ Bool`                                  | Accept   | ✓             | S-Fun; inner ⊤ ⊑ ⊤, x ⊑ T |
| 48 | `· ⊢ True ⊑ True†`                                  | Reject   | ✓             | Would need T ⊑ ⊤ in domain (wrong direction for S-Fun) |

Test 47: True† ⊑ Bool still holds — erasing inner domains only makes
things less precise, and Bool already expects T (which is ⊤-bounded).

Test 48: True ⊑ True† fails. True has domain `T` where True† has `⊤`.
S-Fun is contravariant in domains: need `⊤ ⊑ T`, which is not derivable.
So **erasure loses precision irreversibly** — you can go from precise
to erased (True ⊑ Bool ⊑ True†... no, that's wrong too). Actually
True† ⊑ Bool (test 47) and True ⊑ Bool (test 7), but True and True†
are incomparable: neither is ⊑ the other.

Correction — let me re-examine test 48. True = (T: ⊤) → (x: T) → (y: T) → x.
True† = (T: ⊤) → (x: ⊤) → (y: ⊤) → x. For True ⊑ True† by S-Fun:
- Outer domain: ⊤ ⊑ ⊤ ✓
- Body under T: ⊤: (x: T) → (y: T) → x ⊑ (x: ⊤) → (y: ⊤) → x
  S-Fun: need ⊤ ⊑ T — not derivable. ✗

So True is NOT more precise than True†, even though True "has more
information." The extra domain annotation T makes True *less* accepting
of arguments (only T-typed args, not all ⊤-typed args), and S-Fun's
contravariance treats this as incomparable, not more precise.

| #  | Program                                              | Expected | Current rules | Notes                        |
|----|------------------------------------------------------|----------|---------------|------------------------------|
| 48 | `· ⊢ True ⊑ True†`                                  | Reject   | ✓             | Contravariance: ⊤ ⊑ T fails |
| 49 | `· ⊢ True† ⊑ True`                                  | Reject   | ✓             | T ⊑ ⊤ in domain, but body: need x ⊑ x ✓ ... actually let me check |

For True† ⊑ True: S-Fun on outer:
- Domain: ⊤ ⊑ ⊤ ✓
- Body under T: ⊤: (x: ⊤) → (y: ⊤) → x ⊑ (x: T) → (y: T) → x
  S-Fun: need T ⊑ ⊤ ✓ (S-Top... wait, S-Var: T: ⊤, so T ⊑ ⊤)
  Body under x: T: (y: ⊤) → x ⊑ (y: T) → x
  S-Fun: need T ⊑ ⊤ ✓ (same)
  Body under y: T: x ⊑ x ✓

So True† ⊑ True DOES hold! The erased version is less precise (wider
domains accept more), which is exactly what ⊑ means.

Let me correct the table. True† ⊑ True holds, and True ⊑ True† does not.
This means erase(M) ⊑ M — which is exactly the Erase-Sub lemma!

## Group 14: Pairs with invariants — the equal-pair

### Definitions

```
EqPair = (a: Bool) → (b: a) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b
```

Here `b: a` means "b has the singleton type of a." If a = True,
then b must satisfy `b ⊑ True`. This encodes the invariant
"both components are equal."

### What happens when we construct EqPair True True

**Step 1: EqPair True**

```
EqPair = (a: Bool) → (b: a) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b
```

T-App: True ⊑ Bool ✓. Body:

```
(b: a) → (K: ⊤) → (f: (x: ⊤) → (y: ⊤) → K) → f a b
```

erase(body):

```
(b: ⊤) → (K: ⊤) → (f: ⊤) → f a b
```

The domain `a` on parameter `b` was erased to ⊤. **The invariant
"b has the same type as a" is lost at this point.** After erasure,
b can be anything.

Substitute a ≔ True:

```
(b: ⊤) → (K: ⊤) → (f: ⊤) → f True b
```

This is the same result we'd get from `MkPair True` — the equal-pair
invariant has been completely erased.

**Step 2: (EqPair True) True**

Same as MkPair — we get `(K: ⊤) → (f: ⊤) → f True† True`.

### The invariant is NOT checked

You might expect T-App to check `True ⊑ a` (the domain of b) which
after substituting a ≔ True would become `True ⊑ True`. But this
check **never happens**: T-App erases the body before substituting,
so `(b: a)` becomes `(b: ⊤)` before `a ≔ True` is applied. The
domain check in step 2 is just `True ⊑ ⊤` (S-Top).

This means `EqPair True False` also type-checks — the "invariant"
is never enforced! The domain `a` on parameter `b` was meant to
express "b must have the same type as a," but erasure removes it
before the argument is checked.

This mirrors what happens at runtime: E-Fun erases `(b: a)` to `(b: ⊤)`,
so the runtime function accepts any second argument. The type system
is sound (it doesn't promise something the runtime doesn't deliver),
but the constraint was never actually enforced on either side.

### Can we do better?

No — not in Och₀. The invariant `b: a` lives in a domain position,
and domain erasure is fundamental to both soundness and monotonicity
(sharp edges #14, #16). Any encoding where the relationship between
components is expressed as a domain constraint will lose that
relationship after application.

To preserve such invariants, you'd need them expressed in **body**
(covariant) positions — e.g., a proof term in the body that witnesses
the equality. But Och₀ has no way to express equality proofs yet
(no identity type, no atoms/match).

| #  | Program                                                          | Expected | Current rules | Notes                        |
|----|------------------------------------------------------------------|----------|---------------|------------------------------|
| 44 | `· ⊢ MkPair True False ⇒ (K: ⊤) → (f: ⊤) → f True† False`   | Accept   | ✓             | True† = erase(True) |
| 45 | `· ⊢ Fst (MkPair True False) ⇒ True†`                          | Accept   | ✓             | Pair preserves component values |
| 46 | `· ⊢ Snd (MkPair True False) ⇒ False†`                         | Accept   | ✓             | Symmetric |
| 47 | `· ⊢ True† ⊑ Bool`                                              | Accept   | ✓             | Erased is less precise than Bool |
| 48 | `· ⊢ True† ⊑ True`                                              | Accept   | ✓             | Erase-Sub lemma: erase(M) ⊑ M |
| 49 | `· ⊢ True ⊑ True†`                                              | Reject   | ✓             | Contravariance: ⊤ ⊑ T fails |
| 50 | `· ⊢ EqPair True True ⇒ (K: ⊤) → (f: ⊤) → f True† True`     | Accept   | ✓             | Same result as MkPair True True |
| 51 | `· ⊢ EqPair True False ⇒ (K: ⊤) → (f: ⊤) → f True† False`   | Accept   | ✓             | "Invariant" not enforced: domain erased before check |
