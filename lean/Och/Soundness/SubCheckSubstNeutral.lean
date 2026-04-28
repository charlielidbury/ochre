import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll

/-!
# C7: soundness of the engine's neutral-spine + ascent arm

This module attempts to prove that `subCheckSubst`'s neutral-arm
(spine compare + `neutralAscent` fallback) is sound w.r.t. the
declarative `Subtype'` relation.  The exact statement we want is:

```
theorem subCheckSubst_sound_arm_neutral
    {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : SubstEval.subCheckSubst fuel tyCtx seen a b = .ok true)
    (h_a_neutral : SubstEval.isNeutral a = true) :
    Subtype' (??? seen tyCtx.size) (??? tyCtx) a b
```

with the gaps `???` filled by a *seen-list bridge* and a *tyCtx →
Ctx translator*.  This file documents how far we got and why the
construction walls.

**Wall description.** See `docs/ideas/c7-wall.md` for the full
post-mortem.  In short:

  * The engine encodes free variables as `bvar (levelOffset + lvl)`
    (a "level-bvar" trick).  The declarative `Subtype'.bvar` rule
    looks up `Γ.get? k = some τ` for ordinary de-Bruijn-INDEX `k`
    and concludes `Subtype' S Γ (.bvar k) (τ.shift (k+1) 0)`.  The
    two indexings are not compatible — there is no `Γ : Ctx` of
    realistic length such that `Γ.get? (levelOffset + lvl) = some τ`.

  * Hence the bridge must either translate level-vars away (close
    them into ordinary de-Bruijn indices) or extend `Subtype'` with
    a level-aware bvar rule.  Both options are research-grade.

This file holds the proof shape we attempted — a straight-line
recursion on fuel that case-splits on `subCheckSubstMatch` — and
flags the level-var step as a `sorry` with the exact obligation.
This makes the wall *machine-checkable* (the obligation is a
proper Lean goal, not prose).
-/

namespace Och.Soundness

open SubstEval

/-! ## Bridge primitives (best-effort)

The engine carries `tyCtx : Array Expr` indexed by *level* (entry
`tyCtx[lvl]` is the type of `freshLevelVar lvl = bvar (levelOffset +
lvl)`).  A naive translation to `Subtype'`'s `Ctx = List Expr` (de
Bruijn index, innermost-first) is to reverse the array:

```
def tyCtxToCtx (tyCtx : Array Expr) : Ctx := tyCtx.toList.reverse
```

This places the level-`(tyCtx.size - 1)` entry at de-Bruijn index 0
(innermost), which matches how `subCheckSubst` opens binders (each
`openFresh` increases `tyCtx.size` by one, corresponding to crossing
one binder).  However, **the level-var encoding in `a, b` does not
match this Γ**: under `Γ = tyCtxToCtx tyCtx`, the level-var
`bvar (levelOffset + lvl)` has *index* `levelOffset + lvl` in `a, b`,
but the corresponding context entry is at *index* `tyCtx.size - 1 -
lvl` in `Γ`.

To bridge, we'd need either to (a) rewrite `a, b` so that level-vars
become de-Bruijn-indexed (a multi-level `closeLevelVar`-like
operation) or (b) add a new `Subtype'.lvar` rule.  Both are
substantial.

The function below is the level-by-level closure (option (a)).  It
is *not used* in the proof attempt — included as a marker for the
work needed to make the bridge go through. -/

-- `tyCtxToCtx` moved to `Och/Soundness/CloseAll.lean` so that the
-- arithmetic between `closeAll`'s output indices and `tyCtxToCtx`'s
-- lookup can be developed there.  This module imports it.

/-- Lift the engine's seen-list (no depth tag) to a declarative
seen-set, tagging each entry with the *current* depth `tyCtx.size`.

This is the "shallow" lift; it's correct only at the depth where the
entry was recorded.  Once the engine descends through a binder,
`tyCtx.size` grows but the seen-list entries don't shift, while
declarative `.hyp` re-shifts entries to the use-depth.  This
divergence is wall-2 of `docs/ideas/soundness-strategy.md §4`. -/
def liftSeenList (depth : Nat) (seen : List (Expr × Expr)) : Seen :=
  seen.map (fun (a, b) => (depth, a, b))

theorem liftSeenList_nil (depth : Nat) :
    liftSeenList depth [] = [] := rfl

theorem liftSeenList_cons (depth : Nat) (a b : Expr)
    (seen : List (Expr × Expr)) :
    liftSeenList depth ((a, b) :: seen)
    = (depth, a, b) :: liftSeenList depth seen := rfl

/-! ## Proof attempt

We state the C7 obligation as it would need to be invoked by the
mutual recursion on `(fuel, sizeOf a + sizeOf b)`.  The body is
`sorry` because the level-var encoding renders the natural-looking
case analysis unprovable: the `.bvar (levelOffset + lvl)` arm of
`subCheckSpine` cannot be discharged with `Subtype'.refl _` (since
the engine *can* return `true` after the top-level `a == b`
short-circuit only if it reached the spine path through a different
shape, which means `a` and `b` aren't structurally equal — but
they share an equal head, which collapses to `Subtype'.refl` in the
base spine case modulo `app_cong` for the spine).

The wall isn't in this base case — it's in `neutralAscent`'s call
to `synthNeutralType`, whose `.bvar (levelOffset + lvl)` arm
returns `tyCtx[lvl]?`; converting this to a declarative
`Subtype'.bvar` derivation requires the bvar-index/level-index
translation flagged above. -/

/-! ### Sub-arm 1: spine bvar-bvar base case (CLOSED)

When `subCheckSpine` returns `true` on `(.bvar k1, .bvar k2)`, we
have `k1 == k2 ∧ isLevelIdx k1`.  The corresponding declarative
conclusion `Subtype' S Γ (.bvar k1) (.bvar k1)` closes with
`Subtype'.refl _` — independent of any bvar-index/level-index
translation.

This is the *only* part of C7 that closes without the level-var
translation; everything else hits the wall described in
`docs/ideas/c7-wall.md`. -/

theorem subCheckSpine_sound_bvar_bvar
    {S : Seen} {Γ : Ctx} {k1 k2 : Nat}
    (h : k1 == k2 ∧ isLevelIdx k1) :
    Subtype' S Γ (.bvar k1) (.bvar k2) := by
  obtain ⟨heq, _⟩ := h
  have heq' : k1 = k2 := by simpa using heq
  subst heq'
  exact .refl _

/-! ### Sub-arm 2: spine app-app inductive step (CLOSED — modulo IH)

Given the engine's spine recursion accepts `(.app f1 v1, .app f2
v2)`, we obtain three sub-results:
  * `subCheckSpine fuel tyCtx seen f1 f2 = .ok true`
  * `subCheckSubst fuel tyCtx seen v1 v2 = .ok true`
  * `subCheckSubst fuel tyCtx seen v2 v1 = .ok true`

Combining with appropriate IH hypotheses (which we package as
parameters since the full mutual block isn't built yet), the
`Subtype'.app_cong` rule closes the goal.  This *does not* invoke
the level-var translation — `app_cong` is structural in the
arguments. -/

theorem app_cong_from_spine_ih
    {S : Seen} {Γ : Ctx} {f1 f2 v1 v2 : Expr}
    (ih_head : Subtype' S Γ f1 f2)
    (ih_v12 : Subtype' S Γ v1 v2)
    (ih_v21 : Subtype' S Γ v2 v1) :
    Subtype' S Γ (.app f1 v1) (.app f2 v2) := by
  -- `app_cong : Subtype' S Γ f₂ f₁ → Subtype' S Γ a₂ a₁ →
  --             Subtype' S Γ a₁ a₂ → Subtype' S Γ (.app f₂ a₂) (.app f₁ a₁)`
  -- Match: f₂ := f1, f₁ := f2, a₂ := v1, a₁ := v2.
  -- Premises: f1 ⊑ f2, v1 ⊑ v2, v2 ⊑ v1.
  exact .app_cong ih_head ih_v12 ih_v21

/-! ### Sub-arm 3: neutralAscent / synthNeutralType

The engine's `neutralAscent fuel tyCtx seen a b` returns true iff
  `synthNeutralType fuel tyCtx a = .ok (some ty)`
and
  `subCheckSubst fuel tyCtx seen ty b = .ok true`.

The level-var representation gap that historically walled this
arm is now bridged by `Subtype'_lvar_via_tyCtx` in
`CloseAll.lean` (Proposal A, closed via the `closeAll`
translation).  Soundness of the neutral arm is composed in the
dispatch in `SubCheckSubstSoundness.lean` rather than here; the
documentation walls (formerly three sorried theorems mirroring
the obligation) have been removed in favour of the actual
dispatch and the wall analysis in `docs/ideas/c7-wall.md`. -/

end Och.Soundness
