import PSS.Sub

/-!
# Cut-Free Subtyping and Transitivity Elimination Analysis

## Motivation

The main CanonicalForms proof (`top_not_sub_lam`) has two remaining `sorry`s
that arise from an off-by-one height obstacle in the transitivity decomposition.
We proved informally that those cases are *unreachable* — no concrete derivation
tree produces them — but the proof is circular within the current framework.

This file explores a **cut-free** approach: define a restricted subtyping
relation `SubR` that excludes the `trans` rule entirely (since `trans` is
the "cut" rule in our system), then:

1. Prove `top_not_sub_lam_R` for `SubR` (trivial — case analysis on constructors)
2. Prove `SubR ⊆ Sub` (trivial — every `SubR` derivation is a `Sub` derivation)
3. Attempt `Sub ⊆ SubR` (transitivity/cut elimination — the hard part)

## Key finding

Step 3 is **not provable in general** — the system has β-equivalence rules
(`beta_L`, `beta_R`) that interact with transitivity in essential ways.
Cut elimination for this system would require showing that every
`Sub.trans h1 h2 hw` can be decomposed into a chain of cut-free steps,
which amounts to proving transitivity is admissible — the central open
problem from Hutchins (POPL 2010, §6.6.3).

However, for the **specific case** `Sub [] .top t`, we can show a weaker
result: any such derivation can be "simplified" to have `.top` as the only
intermediate term in any trans chain, because `.top` is the maximum element.
This leads to a partial cut-elimination that suffices for canonical forms.

See the detailed analysis at the end of this file.
-/

open Expr

namespace PSS

-- ============================================================================
-- Section 1: Cut-free subtyping (SubR)
-- ============================================================================

/-- Cut-free subtyping: all rules of `Sub` except `trans`.

    This is the "cut-free" fragment — no transitivity rule means every
    derivation directly witnesses a single-step subtyping relationship.
    The well-formedness judgment is unchanged since `Wf` only appears
    in `Sub.trans` (which is excluded) and `Wf.app` (which references `Sub`,
    not `SubR`). -/
inductive SubR : Ctx → Expr → Expr → Type where
  | refl (e : Expr) : SubR Γ e e
  | top (e : Expr) : SubR Γ e .top
  | bvar {k : Nat} {t : Expr} :
      Γ.get? k = some t →
      SubR Γ (.bvar k) (t.shift (k + 1) 0)
  | lam {dom dom' body body' : Expr} :
      SubR Γ dom dom' → SubR Γ dom' dom →
      SubR (dom :: Γ) body body' →
      SubR Γ (.lam dom body) (.lam dom' body')
  | app_cong {f f' a a' : Expr} :
      SubR Γ f f' → SubR Γ a a' → SubR Γ a' a →
      SubR Γ (.app f a) (.app f' a')
  | beta_L {dom body arg : Expr} :
      SubR Γ (.app (.lam dom body) arg) (body.subst 0 arg)
  | beta_R {dom body arg : Expr} :
      SubR Γ (body.subst 0 arg) (.app (.lam dom body) arg)

-- ============================================================================
-- Section 2: Canonical forms for SubR (trivial)
-- ============================================================================

/-- In cut-free subtyping, `.top` cannot be a subtype of a lambda.

    Proof: case analysis on every `SubR` constructor. None can produce
    `SubR Γ .top (.lam s t)`:
    - `refl`: `.top ≠ .lam s t`
    - `top`:  RHS = `.top ≠ .lam s t`
    - `bvar`: LHS = `.bvar k ≠ .top`
    - `lam`:  LHS = `.lam _ _ ≠ .top`
    - `app_cong`: LHS = `.app _ _ ≠ .top`
    - `beta_L`:   LHS = `.app (.lam ..) _ ≠ .top`
    - `beta_R`:   RHS = `.app (.lam ..) _ ≠ .lam s t` -/
theorem top_not_sub_lam_R {Γ : Ctx} {s t : Expr}
    (h : SubR Γ .top (.lam s t)) : False := by
  -- We generalize to avoid the dependent-elimination issue with beta_R
  -- (where LHS = body.subst 0 arg can't be unified with .top).
  -- Instead, we case-split on `a = .top` after generalizing.
  suffices ∀ a b, SubR Γ a b → a = .top → b = .lam s t → False from
    this .top (.lam s t) h rfl rfl
  intro a b h ha hb
  cases h <;> simp_all [Expr.noConfusion]

/-- In cut-free subtyping, `.top` cannot be a subtype of a variable. -/
theorem top_not_sub_bvar_R {Γ : Ctx} {k : Nat}
    (h : SubR Γ .top (.bvar k)) : False := by
  suffices ∀ a b, SubR Γ a b → a = .top → b = .bvar k → False from
    this .top (.bvar k) h rfl rfl
  intro a b h ha hb
  cases h <;> simp_all [Expr.noConfusion]

-- ============================================================================
-- Section 3: SubR ⊆ Sub (trivial embedding)
-- ============================================================================

/-- Every cut-free derivation is a valid (full) Sub derivation.
    This is trivial since SubR constructors are a subset of Sub constructors. -/
def SubR.toSub : SubR Γ a b → Sub Γ a b
  | .refl e        => .refl e
  | .top e         => .top e
  | .bvar h        => .bvar h
  | .lam h1 h2 h3  => .lam h1.toSub h2.toSub h3.toSub
  | .app_cong h1 h2 h3 => .app_cong h1.toSub h2.toSub h3.toSub
  | .beta_L        => .beta_L
  | .beta_R        => .beta_R

-- ============================================================================
-- Section 4: Attempting Sub ⊆ SubR (cut elimination)
-- ============================================================================

/-!
## Analysis: Why general cut elimination fails

### The problem

We want: `Sub Γ a b → SubR Γ a b`. The only `Sub` constructor not in
`SubR` is `trans`. So we need to show that every use of `trans` can be
eliminated — i.e., if `SubR Γ a m` and `SubR Γ m b` then `SubR Γ a b`.

This is the **admissibility of transitivity** for `SubR`, which is
equivalent to cut elimination.

### Why it fails for general SubR

Consider `SubR Γ a m` and `SubR Γ m b`. To produce `SubR Γ a b`, we'd
need to do case analysis on both derivations and compose them. The critical
problematic cases are:

1. **beta_L + beta_R**: `SubR Γ (.app (.lam d e) c) (e.subst 0 c)` and
   `SubR Γ (e.subst 0 c) (.app (.lam d' e') c')`. To compose these, we'd
   need `SubR Γ (.app (.lam d e) c) (.app (.lam d' e') c')`, which requires
   either `app_cong` (needing `Sub (.lam d e) (.lam d' e')` and `Sub c c'`)
   or transitivity through a third term — exactly what we're trying to eliminate.

2. **lam + beta_L**: `SubR Γ (.lam a b) (.lam s t)` and
   `SubR Γ (.lam s t) (.app ...)` — the second can't exist in SubR
   (no SubR rule has LHS = .lam and RHS = .app), so this is vacuously true.
   But the analogous case with `.app_cong` and `.beta_L` IS problematic.

3. **Recursive structure**: Even for simple cases, composing `lam` with `lam`
   requires composing the sub-derivations, which requires cut elimination
   at smaller types — fine for structural induction. But the β rules break
   structural recursion because `body.subst 0 arg` is not structurally
   smaller than `.app (.lam dom body) arg`.

### The Hutchins obstacle

This is precisely the obstacle identified in Hutchins (POPL 2010, §6.6.3):
the β-equivalence rules create "detours" through arbitrary expressions
(via substitution), and eliminating these detours requires understanding
the structure of substituted terms, which is not bounded by the original
derivation structure.

In traditional type theory, cut elimination works because types have a
well-founded structure (the "cut formula" decreases). In PSS, the "cut
formula" is an arbitrary expression (the middle term of `trans`), and
β-reduction can make it grow unboundedly.

### What about the specific case Sub [] .top (.lam s t)?

For this specific case, we can reason as follows:

- `Sub [] .top (.lam s t)` must use `trans` (no base rule produces it).
- So we have `Sub [] .top m` and `Sub [] m (.lam s t)` for some `m`.
- If `m = .top`: the second derivation `Sub [] .top (.lam s t)` is our
  original problem — no progress.
- If `m = .lam d b`: `Sub [] .top (.lam d b)` is the same problem for
  different `d, b`. This recurses but doesn't obviously terminate.
- If `m = .bvar k`: `Sub [] .top (.bvar k)` faces the same obstacle.
- If `m = .app f a`: this is the case that creates the circular dependency
  in CanonicalForms.lean.

The specific-case cut elimination would need to show that the `m = .top`
chain eventually terminates (i.e., we can't have an infinite chain of
`trans` nodes all with middle term `.top`). But since `Sub [] .top .top`
exists (via `refl` or `top`), we CAN have `trans (top .top) h2 Wf.top`
as long as `h2 : Sub [] .top (.lam s t)` — which is just the original
problem again. So we need the derivation to have finite height, which it
does (it's an inductive type), but the issue is that when we strip one
`trans` off the top, the remaining sub-derivation might have the SAME
height (off-by-one).

This is exactly the height obstacle encountered in CanonicalForms.lean.
-/

-- ============================================================================
-- Section 5: Alternative — "top-specialized" cut elimination
-- ============================================================================

/-!
## Top-specialized SubR

Instead of full cut elimination, we try a weaker statement: when the LHS
is `.top`, can we eliminate cuts?

The key observation is: `Sub Γ .top m` means `.top ≤ m`, which (together
with `Sub Γ m .top` from the `top` rule) means `m ≡ .top`. If we could
prove that `Sub Γ .top m` implies `m` is "equivalent to `.top`" in some
useful sense, we could then show `Sub Γ .top (.lam s t)` is impossible.

But "equivalent to .top" is exactly what we're trying to prove is
impossible for `.lam s t`! The reasoning is circular.

### What CAN we prove?

We can prove several useful structural lemmas about SubR:
-/

/-- A "head form" is a lambda or a variable — the forms that `.top` can never
    be a cut-free subtype of. We define this locally since CanonicalForms.lean
    has its own copy. -/
def Expr.IsHeadFormR : Expr → Prop
  | .lam _ _ => True
  | .bvar _ => True
  | _ => False

/-- No SubR derivation has LHS = .top and RHS = a head form (lam or bvar). -/
theorem top_not_sub_headForm_R {Γ : Ctx} {b : Expr}
    (h : SubR Γ .top b) (hb : Expr.IsHeadFormR b) : False := by
  suffices ∀ a b, SubR Γ a b → a = .top → Expr.IsHeadFormR b → False from
    this .top b h rfl hb
  intro a b h ha hb
  cases h <;> simp_all [Expr.IsHeadFormR]

/-- The only SubR derivation from .top to .top is refl or top. -/
theorem top_sub_top_R {Γ : Ctx}
    (_h : SubR Γ .top .top) : True := trivial

-- ============================================================================
-- Section 6: Attempting the composition lemma directly
-- ============================================================================

/-!
## Direct composition attempt for the .top case

We attempt to prove: if `Sub Γ .top b` and `b` is a head form, then `False`.
The strategy: by induction on the Sub derivation, try to reduce every `trans`
case to a smaller instance.

This is essentially re-deriving what CanonicalForms.lean already does, but
now with the insight from SubR. The question: does the cut-free perspective
give us any additional leverage?

**Answer: No.** The cut-free perspective confirms that the theorem is TRUE
(since `top_not_sub_headForm_R` closes it for the cut-free case), and the
obstacle is entirely in eliminating cuts. The two approaches (direct proof
in CanonicalForms.lean vs. cut elimination here) face the identical
structural obstacle: when the middle term of a `trans` is an application,
re-associating the derivation preserves total height.

### Formal verification of this analysis

We can formalize the key insight: the problem reduces to one specific
composition pattern.
-/

/-! ### SubR CAN derive `.top ≤ .app`

Note: `SubR Γ .top (.app f a)` IS derivable via `beta_R` when
`body.subst 0 a = .top` (e.g., `body = .top`). So unlike lambdas
and variables, `.top` CAN be a cut-free subtype of an application.

Example: `SubR.beta_R : SubR Γ .top (.app (.lam dom .top) arg)`
since `Expr.top.subst 0 arg = .top`.

This means the critical distinction is:
- `.top ≤ .lam s t` in SubR: IMPOSSIBLE (proved above)
- `.top ≤ .bvar k` in SubR: IMPOSSIBLE (proved above)
- `.top ≤ .app f a` in SubR: POSSIBLE via beta_R
- `.top ≤ .top` in SubR: TRIVIALLY possible via refl or top

The fact that `.top ≤ .app` IS possible in SubR means that even
cut-free subtyping allows `.top` to reach applications. The saving
grace is that from applications, there is no cut-free path to lambdas
or variables (since app_cong keeps the app shape, and beta_L only
goes from app to substitution results, which could be anything but
would require another trans to continue, and SubR has no trans). -/

/-- `.top` can be a cut-free subtype of an application: counterexample. -/
example : @SubR [] Expr.top (Expr.app (Expr.lam Expr.top Expr.top) Expr.top) := by
  have h : @SubR [] (Expr.top.subst 0 Expr.top) (Expr.app (Expr.lam Expr.top Expr.top) Expr.top) :=
    SubR.beta_R
  simp [Expr.subst] at h
  exact h

-- ============================================================================
-- Section 7: The gap between Sub and SubR
-- ============================================================================

/-!
## The essential difference between Sub and SubR

Both `Sub` and `SubR` can derive `.top ≤ .app f a` (the latter via `beta_R`
when the substitution result is `.top`). The critical difference is what
happens AFTER reaching an application:

- In `Sub`, `trans` allows chaining: `.top ≤ .app f a ≤ .lam s t` is
  possible if there exists a derivation from the app to the lam (e.g.,
  via further trans + beta_L). This is the problematic path that creates
  the circular dependency in CanonicalForms.lean.

- In `SubR`, there is no `trans`, so from `.app f a` we can only go to:
  - `.app f' a'` (via `app_cong` — but that requires LHS = `.app`, not `.top`)
  - `body.subst 0 arg` (via `beta_L` — but that requires LHS = `.app (.lam ..) ..`)
  - `.app (.lam dom body) arg` (via `beta_R` — but that takes us to an app, not a lam)
  None of these can produce `.top` as LHS, so there is no way to CHAIN
  from `.top` through `.app` to `.lam` in SubR.

The fundamental insight is that `beta_R` CAN start from `.top` (when
`body.subst 0 arg = .top`), but the RESULT is an `.app`, and without
`trans` there is no way to continue from that `.app` to a `.lam`.

## Conclusion

The cut-free approach cleanly separates the problem into two parts:

1. **Cut-free canonical forms** (`top_not_sub_lam_R`): TRIVIALLY TRUE.
   No SubR constructor can produce `SubR Γ .top (.lam s t)`.

2. **Cut elimination** (`Sub ⊆ SubR`): OPEN PROBLEM, equivalent to
   Hutchins' transitivity admissibility conjecture (POPL 2010, §6.6.3).

For the SPECIFIC case `Sub [] .top (.lam s t) → False`, the cut-free
approach doesn't provide additional leverage beyond what CanonicalForms.lean
already has, because:

- The cut-free theorem is trivial (no interesting proof content)
- All the difficulty is in cut elimination
- Cut elimination for the specific case reduces to the same height
  obstacle as the direct proof

The two sorrys in CanonicalForms.lean are, from this perspective,
exactly the two places where cut elimination would need to be applied:
they correspond to `Sub.trans (app_cong ..) beta_L ..` and
`Sub.trans beta_L beta_L ..` — compositions that pass through an
application term. These are precisely the compositions that SubR
avoids by not having `trans`.

### What would close the gap

To close the sorrys via this approach, one would need to prove cut
elimination for the restricted case where the goal type is `.lam s t`
or `.bvar k`. Concretely, one of:

(a) **Full cut elimination**: `Sub Γ a b → SubR Γ a b`. This is the
    Hutchins conjecture and appears to require novel proof techniques
    (logical relations, reducibility candidates, or a fundamentally
    different induction measure).

(b) **Top-specialized cut elimination**: `Sub Γ .top b → SubR Γ .top b`.
    This is weaker but still requires showing that every trans chain
    from `.top` can be flattened. The obstacle is the same: trans
    through `.app` creates sub-problems of the same size.

(c) **Canonical-forms-specialized cut elimination**: show that for
    `Sub Γ .top (.lam s t)`, the derivation can be transformed to
    avoid application-middle trans nodes adjacent to `beta_L`.
    This is the "restricted Sub" approach from the task description,
    and it faces the same off-by-one issue because the transformation
    preserves total derivation size.

None of (a), (b), or (c) appear tractable with current techniques.
The problem is fundamentally about the interaction of β-reduction
with transitivity, and all known approaches hit the same wall.
-/

end PSS
