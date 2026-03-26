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
| 4  | `· ⊢ ⊤ ⊤ ⇒ ⊤`                   | Accept   | ✓             | T-App-Top          |

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

## Group 8: Unconditional T-App-Top (sharp edge #12)

T-App-Top has no premises — any application types to ⊤ as a fallback.
These tests verify the new behavior and its interaction with monotonicity.

| #  | Program                                              | Expected | Current rules | Notes                              |
|----|------------------------------------------------------|----------|---------------|--------------------------------------|
| 30 | `f: ⊤ ⊢ f ((⊤ : (x: ⊤) → x)) ⇒ ⊤`               | Accept   | ✓             | T-App-Top, arg unchecked             |
| 31 | `f: (y: ⊤) → ⊤ ⊢ f ((⊤ : (x: ⊤) → x)) ⇒ ⊤`     | Accept   | ✓             | T-App-Top fallback (arg untypeable)  |
| 32 | `· ⊢ ((x: ⊤) → x) ⊤ ⇒ ⊤`                          | Accept   | ✓             | T-App (precise), also T-App-Top (⊤) |
| 33 | `g: (x: ⊤) → x, f: g ⊢ f ⊤ ⇒ ⊤`                  | Accept   | ✓             | T-App-Top (f ⇒ g, variable type)    |

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
