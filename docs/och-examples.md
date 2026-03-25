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

The key insight: S-Var only gives `b ⊑ Bool` (variable on the left of ⊑).
No rule puts anything on the left of `⊑ b` (variable on the right) except
S-Refl (`b ⊑ b`). So `False ⊑ b` is simply not derivable, regardless of
what type `b` has in the environment. The bug cannot occur.
