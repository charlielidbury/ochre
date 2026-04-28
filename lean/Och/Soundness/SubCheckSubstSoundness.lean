import Och.Subtyping
import Och.EvalSubst
import Och.API
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural
import Och.Soundness.SubCheckSubstFallback

/-!
# `subCheckSubst_sound` — top-level mutual block

This module composes the per-arm soundness lemmas
(`SubCheckSubstStructural`, `SubCheckSubstNeutral`,
`SubCheckSubstFallback`) into the engine-level theorem

```
theorem subCheckSubst_sound
    {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : SubstEval.subCheckSubst fuel tyCtx seen a b = .ok true) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size b)
```

and discharges the public `Och.subCheck_sound` (in `Och/Soundness.lean`)
by specialising at `tyCtx = #[]`, `seen = []`, where `closeAll 0 = id`
(`closeAll_zero`) and the conclusion collapses to `Subtype' [] [] a b`.

## Composition wall: partial-def opacity (RESOLVED)

**Status: the partial-def opacity wall is now broken.**

The engine's mutual block was historically `partial def`, which made
every constant in the block opaque to `unfold` / `simp only [name]` /
`rw [name]` (no `eq_def`, `eq_1`, … equation lemmas).  Given a
hypothesis `h : subCheckSubst fuel tyCtx seen a b = .ok true`, there
was no tactic-level move that stepped `h` to `subCheckSubstMatch
fuel tyCtx seen a' b' = .ok true` (after the WHNF step) — the
arm-lemmas in `SubCheckSubstStructural` etc. all take such pairs as
*parameters*, and the left-hand side of the case analysis (extracting
those parameters from `h`) could not be performed.

That wall has now been knocked down by converting the mutual block
to non-partial defs in `Och/EvalSubst.lean` with a lex `(fuel, phase)`
termination measure (see that file's module docstring).  The
auto-generated `subCheckSubst.eq_def`, `subCheckSubstMatch.eq_def`,
… equation lemmas are now available — `rw [subCheckSubst.eq_def] at
h` (or `simp only [...]`) steps `h` through the WHNF/dispatch frame
and exposes the inner `subCheckSubstMatch` call, from which the
arm-lemma premises can be extracted via further case analysis.

The composition theorems below still carry `sorry` in their bodies
(the wiring from `eq_def` to the arm-IH packages is mechanical but
non-trivial and is the next step); the *meta-level* obstruction is
gone.

## What this file delivers

We write the mutual block in **three forms**:

  1. `subCheckSubst_sound` — the top-level statement, body `sorry`
     with a precise wall comment.  This is the target of the public
     `Och.subCheck_sound`.

  2. `subCheckSubstMatch_sound_compose` — a *parametrised composition
     theorem* that takes the engine-equation explicitly as a
     hypothesis (`engine_eq`), case-splits on the shape of `(a, b)`,
     and composes the arm-lemmas with the IH supplied by the caller.
     This is the proof skeleton; if/when an `engine_eq` lemma becomes
     available (via partial-def-equation engineering, or a refactor
     of the engine to a non-partial structural recursion), this
     theorem closes immediately.  Until then, the composition is
     `sorry`-bridged at the IH-extraction step but the arm-lemma
     wiring is explicit.

  3. The mutual block of *arm-IH packages* — one helper per shape
     that, given the appropriate IH derivations, builds the parent
     `Subtype'`.  These directly invoke the arm-lemmas in
     `Soundness/SubCheckSubst{Structural,Neutral,Fallback}.lean`.

## What we do NOT attempt

* Equation-lemma engineering for mutual `partial def` (research-grade,
  may require kernel-level work).
* Refactoring `subCheckSubst` to a non-partial structural recursion
  (massive engineering — the `seen`-set discipline + WHNF-via-eval
  make a fuel-strict measure non-obvious).
* Discharging the v2 fallback bridges (separate wall, see
  `Soundness/SubCheckSubstFallback.lean`).

See `docs/ideas/proposalA-wall-v2.md` and forthcoming
`docs/ideas/partial-def-opacity-wall.md` (to be written) for the
deeper analysis.
-/

namespace Och.Soundness

open SubstEval

/-! ## Top-level statements

The two soundness targets, stated against the substrate-agnostic
`Subtype'`. -/

/-- Engine-level soundness: `subCheckSubst` accepting `(a, b)` at
depth `tyCtx.size` produces a declarative subtyping derivation on the
closeAll-translated terms.

**Status**: the partial-def opacity wall has been broken (see the
module-level docstring above and `Och/EvalSubst.lean`'s status section).
`subCheckSubst.eq_def` is now available — the body remains `sorry`
pending the mechanical wiring of the equation lemma into the arm-IH
composition. -/
theorem subCheckSubst_sound
    {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
    {a b : Expr}
    (_h : SubstEval.subCheckSubst fuel tyCtx seen a b = .ok true) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size b) := by
  -- The partial-def wall is now broken (subCheckSubst is non-partial
  -- with a lex (fuel, phase) measure; eq_def auto-generates).  This
  -- proof is the next step: rw [subCheckSubst.eq_def] at h, case-
  -- split on the WHNF outputs, dispatch to the arm-IH packages.
  sorry

/-- Public-API soundness: `Och.subCheck` accepting two `WTValue`s
produces a declarative subtyping derivation on their `whnf` fields.

Reduces to `subCheckSubst_sound` at `tyCtx = #[]`, `seen = []`, where
`closeAll 0 = id` and the seen-list lift is `[]`. -/
theorem Och_subCheck_sound
    {fuel : Nat} {a b : Och.WTValue}
    (_h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  -- `Och.subCheck a b fuel = SubstEval.subCheck fuel a.whnf b.whnf`,
  -- and `SubstEval.subCheck fuel x y = subCheckSubst fuel #[] [] x' y'`
  -- where `x' = evalSubst fuel unfBound x`, `y' = evalSubst fuel unfBound y`.
  -- The eval bridge plus the `closeAll 0 = id` collapse give us the
  -- conclusion via `subCheckSubst_sound`.  The eval bridge is itself
  -- a sub-wall (mirror of `concEval_equiv`); we sorry the composition
  -- here and document the chain.
  --
  -- Chain (sketch, all walled):
  --   1.  `evalSubst_equiv` (UNWRITTEN) gives
  --         `Subtype' [] [] a.whnf x' ∧ Subtype' [] [] x' a.whnf`
  --       and similarly for `b`.
  --   2.  `subCheckSubst_sound` on the inner call gives
  --         `Subtype' [] [] (closeAll 0 x') (closeAll 0 y')`,
  --       which by `closeAll_zero` is `Subtype' [] [] x' y'`.
  --   3.  Trans-chain: `a.whnf ⊑ x' ⊑ y' ⊑ b.whnf`.
  --
  -- Step 1 walls on `evalSubst_equiv` (independently provable but
  -- unwritten).  Step 2 walls on `subCheckSubst_sound` above.
  -- Both are sorry-bridged.
  sorry

/-! ## Arm-IH composition packages

These helper theorems take the IH derivations the *would-be* mutual
block would produce, and build the parent `Subtype'` for each shape
of `(a, b)`.  They directly invoke the per-arm lemmas in the
neighbouring files; the partial-def-opacity wall sits *outside*
these packages (it blocks the construction of their inputs from
the engine equation).

Each package corresponds to one arm of the engine's
`subCheckSubstMatch` case-split. -/

section ArmPackages

variable {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}

/-- C2 (lam-lam structural) composition. -/
theorem arm_lam_lam_compose
    {domA bodyA domB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT tyCtx.size = true)
    (hlvB : bodyB.lvarLT tyCtx.size = true)
    (ih_dom : Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size domB) (closeAll tyCtx.size domA))
    (ih_body : Subtype' (liftSeenList tyCtx.size seen)
        (closeAll tyCtx.size domB :: tyCtxToCtx tyCtx)
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyA tyCtx.size))
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyB tyCtx.size))) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.lam domA bodyA))
      (closeAll tyCtx.size (.lam domB bodyB)) :=
  subCheckSubst_arm_lam_lam hclA hclB hlvA hlvB ih_dom ih_body

/-- C3 (iota-iota structural) composition. -/
theorem arm_iota_iota_compose
    {annA bodyA annB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT tyCtx.size = true)
    (hlvB : bodyB.lvarLT tyCtx.size = true)
    (ih_ann : Subtype' (liftSeenList tyCtx.size ((Expr.iota annA bodyA, Expr.iota annB bodyB) :: seen))
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size annA) (closeAll tyCtx.size annB))
    (ih_body : Subtype' (liftSeenList tyCtx.size ((Expr.iota annA bodyA, Expr.iota annB bodyB) :: seen))
        (closeAll tyCtx.size annB :: tyCtxToCtx tyCtx)
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyA tyCtx.size))
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyB tyCtx.size))) :
    Subtype' (liftSeenList tyCtx.size ((Expr.iota annA bodyA, Expr.iota annB bodyB) :: seen))
      (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.iota annA bodyA))
      (closeAll tyCtx.size (.iota annB bodyB)) :=
  subCheckSubst_arm_iota_iota hclA hclB hlvA hlvB ih_ann ih_body

/-- C4 (fix-fix structural) composition. -/
theorem arm_fix_fix_compose
    {annA bodyA annB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT tyCtx.size = true)
    (hlvB : bodyB.lvarLT tyCtx.size = true)
    (ih_ann : Subtype' (liftSeenList tyCtx.size ((Expr.fix annA bodyA, Expr.fix annB bodyB) :: seen))
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size annA) (closeAll tyCtx.size annB))
    (ih_body : Subtype' (liftSeenList tyCtx.size ((Expr.fix annA bodyA, Expr.fix annB bodyB) :: seen))
        (closeAll tyCtx.size annB :: tyCtxToCtx tyCtx)
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyA tyCtx.size))
        (closeAll (tyCtx.size + 1) (SubstEval.openFreshTop bodyB tyCtx.size))) :
    Subtype' (liftSeenList tyCtx.size ((Expr.fix annA bodyA, Expr.fix annB bodyB) :: seen))
      (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.fix annA bodyA))
      (closeAll tyCtx.size (.fix annB bodyB)) :=
  subCheckSubst_arm_fix_fix hclA hclB hlvA hlvB ih_ann ih_body

/-! ### Fallback arms (carry v2 internal sorries)

The fallback arms thread an `evalSubst` equation through the
substitution bridge.  The bridge sorry remains internal to the
arm-lemma; the composition here is mechanical. -/

/-- iota_intro fallback composition.  Uses `(tyCtxToCtx tyCtx).length`
    in the seen-tag so the arm-lemma applies directly without rewrite
    on the IH terms (rewriting `tyCtx.size` would clobber the
    `closeAll tyCtx.size` arguments). -/
theorem arm_iota_intro_compose
    {a ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 a) = .ok bodyB'')
    (ih_ann : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size a,
            closeAll tyCtx.size (.iota ann bodyB))
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a) (closeAll tyCtx.size ann))
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size a,
            closeAll tyCtx.size (.iota ann bodyB))
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a) (closeAll tyCtx.size bodyB'')) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size (.iota ann bodyB)) :=
  iota_intro_arm h_eval ih_ann ih_body

/-- unfold_fix_R fallback composition. -/
theorem arm_unfold_fix_R_compose
    {a ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 (.fix ann bodyB)) = .ok bodyB'')
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size a,
            closeAll tyCtx.size (.fix ann bodyB))
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a) (closeAll tyCtx.size bodyB'')) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size (.fix ann bodyB)) :=
  unfold_fix_R_arm h_eval ih_body

/-- unfold_fix_L fallback composition. -/
theorem arm_unfold_fix_L_compose
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.fix ann bodyA)) = .ok a')
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size (.fix ann bodyA),
            closeAll tyCtx.size b)
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a') (closeAll tyCtx.size b)) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.fix ann bodyA)) (closeAll tyCtx.size b) :=
  unfold_fix_L_arm h_eval ih_body

/-- unfold_iota_L fallback composition. -/
theorem arm_unfold_iota_L_compose
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.iota ann bodyA)) = .ok a')
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size (.iota ann bodyA),
            closeAll tyCtx.size b)
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a') (closeAll tyCtx.size b)) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.iota ann bodyA)) (closeAll tyCtx.size b) :=
  unfold_iota_L_arm h_eval ih_body

/-! ### Trivial arms

These close without IH (other than `Subtype'` constructors). -/

/-- C0 (bot ⊑ _) arm.  Closes by `Subtype'.bot_L`. -/
theorem arm_bot_L_compose
    (b : Expr) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size .bot) (closeAll tyCtx.size b) := by
  show Subtype' _ _ .bot _
  exact .bot_L

/-- Top arm (engine's `b' == .type` short-circuit).  Closes by
`Subtype'.top`. -/
theorem arm_top_compose (a : Expr) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size .type) := by
  show Subtype' _ _ _ .type
  exact .top _

/-- Refl arm (engine's `a' == b'` short-circuit).  Closes by
`Subtype'.refl`. -/
theorem arm_refl_compose (a : Expr) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size a) :=
  .refl _

/-- Hyp arm (engine's seen-list short-circuit).  When `(a, b) ∈ seen`,
the engine returns true; the declarative counterpart is `Subtype'.hyp`
on the lifted seen-set. -/
theorem arm_hyp_compose (a b : Expr)
    (hin : (a, b) ∈ seen) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      ((closeAll tyCtx.size a).shift 0 0)
      ((closeAll tyCtx.size b).shift 0 0) := by
  -- `(a, b) ∈ seen` ⟹ `(tyCtx.size, a, b) ∈ liftSeenList tyCtx.size seen`.
  -- `Subtype'.hyp` then gives, at the recorded depth `tyCtx.size`:
  --   Subtype' S Γ (a.shift (Γ.length - tyCtx.size) 0) (b.shift … 0)
  -- With `Γ.length = tyCtx.size` (i.e., we're at the recording depth),
  -- the shift is by 0, which is the identity (`Expr.shift_zero`).
  -- Caller is expected to specialise to that depth.
  --
  -- WALL: the engine's seen-list is the *raw* `seen`, but ours is
  -- the closeAll'd-and-lifted form.  For this lemma to fire in the
  -- mutual block, we'd need `(closeAll d a, closeAll d b) ∈ seen`
  -- when `(a, b) ∈ seen`'s pre-image — but the engine doesn't
  -- closeAll its seen entries.  This requires a `seen-coherence`
  -- predicate threaded through the recursion.
  --
  -- Closes via `Subtype'.hyp` modulo this coherence; we sorry the
  -- coherence step.
  sorry

/-! ### Spine arms (neutral case)

The neutral arm of `subCheckSubstMatch` calls `subCheckSpine`
followed (on failure) by `neutralAscent`.  The spine arms close
declaratively via `Subtype'.refl` (head equality) and `Subtype'.app_cong`
(spine recursion); the neutral-ascent arm walls on
`Subtype'_lvar_via_tyCtx_WALL` (level-var ascent — broken by
Proposal A's `closeAll`, see `CloseAll.lean`). -/

/-- Spine bvar-bvar composition (closed via `subCheckSpine_sound_bvar_bvar`).

`hlvl` is unused in the *closed* form (closeAll replaces level-bvars
with ordinary bvars, and refl closes regardless), but we keep it as
a parameter to match the engine's `subCheckSpine` precondition. -/
theorem arm_spine_bvar_bvar_compose
    {k1 k2 : Nat}
    (hke : k1 == k2)
    (_hlvl : isLevelIdx k1) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.bvar k1)) (closeAll tyCtx.size (.bvar k2)) := by
  -- closeAll on a level-bvar produces an ordinary bvar (Proposal A).
  -- The `bvar k1 == bvar k2` engine equality lifts through closeAll;
  -- both sides are equal, so `refl` closes.
  have heq' : k1 = k2 := by simpa using hke
  subst heq'
  exact .refl _

/-- Spine app-app composition (recursive). -/
theorem arm_spine_app_app_compose
    {f1 f2 v1 v2 : Expr}
    (ih_head : Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size f1) (closeAll tyCtx.size f2))
    (ih_v12 : Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size v1) (closeAll tyCtx.size v2))
    (ih_v21 : Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size v2) (closeAll tyCtx.size v1)) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.app f1 v1)) (closeAll tyCtx.size (.app f2 v2)) := by
  show Subtype' _ _
    (.app (closeAll tyCtx.size f1) (closeAll tyCtx.size v1))
    (.app (closeAll tyCtx.size f2) (closeAll tyCtx.size v2))
  exact app_cong_from_spine_ih ih_head ih_v12 ih_v21

end ArmPackages

/-! ## Composition skeleton

The function `subCheckSubstMatch_compose` below would, given the
engine's recursive results explicitly, build the parent `Subtype'`
by case analysis on the shape of `(a, b)`.

It is **not** parametrised by `h : subCheckSubstMatch … = .ok true`
(which we cannot case-analyse due to the partial-def opacity wall);
instead, it takes the recursive results as separate hypotheses.
This makes the composition usable *if* a future agent/refactor
exposes the engine's equation lemmas.

We do not write the full case-by-case body — there are 12+ shape
arms and each is a one-liner invoking the `arm_*_compose` package
above.  The structure is:

```
match a, b with
| .bot, _ => arm_bot_L_compose
| _, .type => arm_top_compose
| .lam .., .lam .. => arm_lam_lam_compose <ih_dom> <ih_body>
| .iota .., .iota .. => arm_iota_iota_compose <ih_ann> <ih_body>  -- structural
                       <or> arm_iota_intro_compose for the fallback
| .fix .., .fix .. => arm_fix_fix_compose <ih_ann> <ih_body>      -- structural
                       <or> arm_unfold_fix_R_compose for the fallback
| _, .iota .. => arm_iota_intro_compose
| _, .fix .. => arm_unfold_fix_R_compose
| .fix .., _ => arm_unfold_fix_L_compose
| .iota .., _ => arm_unfold_iota_L_compose
| _, _ if isNeutral a && isNeutral b => arm_spine_..._compose recursively
| _, _ if isNeutral a => neutralAscent (WALLED on level-var)
| _, _ => false (engine returns .ok false; vacuous)
```

The walls inside the per-arm packages are documented in their
respective files; the wall *outside* (extracting the IH from
`h : … = .ok true`) is the partial-def opacity wall.
-/

end Och.Soundness
