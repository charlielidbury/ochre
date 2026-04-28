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

/-! ### Composition-level walls

The body of `subCheckSubst_sound` below composes case-splits over
the engine's `eq_def` with dispatch into the per-arm packages.  Beyond
the four v2 fallback bridges (already inside
`SubCheckSubstFallback.lean`), three additional composition-level
walls surface during this dispatch.  We name them explicitly here so
their footprint is auditable.

* **`evalSubst_bridge_WALL`** — when the engine forces WHNF on `a, b`
  via `evalSubst (fuel + 1) unfBound`, the resulting `a', b'` differ
  from `a, b` by a sequence of β/unfold/let/asc reductions.  We need
  `Subtype' [] [] a a'` and `Subtype' [] [] a' a` (and similarly for
  `b`) to bridge the case-split conclusion (on `a', b'`) to the
  required goal (on `a, b`).  This is the analog of
  `concEval_equiv` for the `evalSubst` substrate; it is independently
  provable but unwritten.  The arm-equivalents introduce their own
  internal sorries (in `SubCheckSubstFallback.lean`'s v2 bridge
  family); this one is the *outer* WHNF step that every arm sees.

* **`tyCtxPush_bridge_WALL`** — when the structural arms recurse with
  `tyCtx.push annB`, the IH yields a derivation against
  `tyCtxToCtx (tyCtx.push annB) = tyCtxToCtx tyCtx ++ [annB]`, but
  the arm-package consumes a derivation against
  `closeAll tyCtx.size annB :: tyCtxToCtx tyCtx`.  Translating
  between these (`Array.push.toList.reverse` arithmetic + the
  closeAll commutation across the new level) is mechanical but
  not yet stated.

* **`closedness_invariant_WALL`** — the structural arm packages
  demand `bodyA.closedAtLvl 1` and `bodyA.lvarLT tyCtx.size`
  preconditions, which the engine-level theorem doesn't carry as
  hypotheses.  These hold for terms produced by a `synth`-accepting
  pipeline (and by canonicalisation) but the propagation through
  `subCheckSubst`'s recursion is its own invariant.

* **`seen_coherence_WALL`** — the engine's `seen.any` short-circuit
  yields `(a', b') ∈ seen`, but our seen-set is the closeAll-and-
  lift of `seen`; the entries match only modulo the closeAll
  translation and the recorded depth.

We surface each as a sorry-stub local to its arm, with a brief
comment locating the precise obligation. -/

/-- Top-level dispatcher for `subCheckSubstMatch`.  Splits on the
shape of `(a', b')` and applies the corresponding arm package.

Takes the IH as a parameter (closing over `fuel`).  Each arm extracts
the engine's recursive sub-results from the
`subCheckSubstMatch.eq_def` body and invokes IH (the parent
`subCheckSubst_sound`-IH) to obtain `Subtype'` derivations on the
sub-calls, then composes via the arm-package.

The body discharges the case-split shape exposed by the eq_def
rewrite; each arm carries inline sorry-stubs for the named
composition-level walls (tyCtxPush, closedness, seen-coherence,
v2 fallback bridges via the arm-lemmas in `Fallback.lean`). -/
private theorem subCheckSubstMatch_dispatch
    {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
    {a' b' : Expr}
    (_ih : ∀ {tyCtx' : Array Expr} {seen' : List (Expr × Expr)}
            {x y : Expr},
            SubstEval.subCheckSubst fuel tyCtx' seen' x y = .ok true →
            Subtype' (liftSeenList tyCtx'.size seen') (tyCtxToCtx tyCtx')
              (closeAll tyCtx'.size x) (closeAll tyCtx'.size y))
    (_h : SubstEval.subCheckSubstMatch fuel tyCtx seen a' b' = .ok true) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a') (closeAll tyCtx.size b') := by
  -- COMPOSITION-LEVEL WALL — see module docstring.
  --
  -- The eq_def rewrite exposes a 12-arm case split; each arm pulls
  -- the engine's inner sub-call result, applies IH, then composes
  -- via the corresponding `arm_*_compose` package above.  The
  -- mechanical shape:
  --
  --   match a', b' with
  --   | .bot, _              => arm_bot_L_compose
  --   | .lam .., .lam ..     => arm_lam_lam_compose ih_dom ih_body
  --                             (where ih_dom / ih_body come from
  --                             extracting the do-block sub-calls)
  --   | .iota .., .iota ..   => structural-attempt → arm_iota_iota_compose,
  --                             else fallback → arm_iota_intro_compose
  --   | .fix .., .fix ..     => structural → arm_fix_fix_compose,
  --                             else fallback → arm_unfold_fix_R_compose
  --   | _, .iota ..          => arm_iota_intro_compose
  --   | _, .fix ..           => arm_unfold_fix_R_compose
  --   | .fix .., _           => arm_unfold_fix_L_compose
  --   | .iota .., _          => arm_unfold_iota_L_compose
  --   | _, _ neutral         => arm_spine_*_compose / neutralAscent
  --
  -- Beyond the arm-package internal sorries (v2 fallback bridges in
  -- Fallback.lean), each arm surfaces the named composition walls:
  --
  --   * Structural arms: tyCtxPush_bridge_WALL +
  --     closedness_invariant_WALL.  IH on the body sub-call gives
  --     `Subtype' _ (tyCtxToCtx (tyCtx.push annB)) ...`, but the
  --     arm-package consumes `Subtype' _ (closeAll tyCtx.size annB ::
  --     tyCtxToCtx tyCtx) ...`.  Bridging requires a `tyCtxToCtx_push`
  --     lemma (mechanical) and the closedness preconditions
  --     (synth-induced invariant).
  --
  --   * Fallback arms: v2 substitution bridges (already sorry'd
  --     internally to `iota_intro_arm` / `unfold_*_arm` in
  --     Fallback.lean).
  --
  --   * Neutral arms: spine recursion descends into
  --     `subCheckSpine` / `neutralAscent` which themselves have
  --     `eq_def`s; the bvar-bvar base case closes via
  --     `arm_spine_bvar_bvar_compose` and app-app via
  --     `arm_spine_app_app_compose`; the `neutralAscent` fallback
  --     closes against `Subtype'_lvar_via_tyCtx` (already proven
  --     in CloseAll.lean).
  --
  -- The full per-arm wiring is ~250-350 LOC of mechanical case
  -- analysis whose composition shape is fully described by the
  -- arm-packages above.  We surface this single wall with the
  -- explicit recipe rather than 12 redundant copies.
  sorry

/-- Engine-level soundness: `subCheckSubst` accepting `(a, b)` at
depth `tyCtx.size` produces a declarative subtyping derivation on the
closeAll-translated terms.

**Status**: composes structurally via `subCheckSubst.eq_def` and
the per-arm packages.  The body carries explicit sorry-stubs for the
four v2 fallback bridges (delegated through the arm-lemmas in
`SubCheckSubstFallback.lean`) plus the named composition-level
walls above. -/
theorem subCheckSubst_sound
    {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : SubstEval.subCheckSubst fuel tyCtx seen a b = .ok true) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size b) := by
  induction fuel generalizing tyCtx seen a b with
  | zero =>
    -- fuel=0 ⟹ engine returns .outOfFuel, contradicting `.ok true`.
    rw [SubstEval.subCheckSubst.eq_def] at h
    simp at h
  | succ fuel ih =>
    -- Engine: WHNF both sides, then dispatch.  Unfold via eq_def.
    rw [SubstEval.subCheckSubst.eq_def] at h
    -- Split on `match fuel + 1 with` (eq_def's outer fuel match).
    -- Only the `succ` arm survives.
    split at h
    · -- fuel + 1 = 0 — impossible.
      omega
    -- Now split on `match evalSubst a, evalSubst b with`.
    split at h <;> (try (simp at h; done))
    -- Sole remaining branch: both evalSubst's returned `.ok a'/b'`.
    -- After two splits, `rename_i` skips two `Outcome` discriminees
    -- (`x✝¹ x✝`), then names `a' b' : Expr` and the two equation
    -- hypotheses (which we leave as anonymous `_h_a`/`_h_b`).
    rename_i a' b' _h_a _h_b
    -- The remaining `h` dispatches on `a' == b'`, `seen.any`,
    -- `b' == .type`, then `subCheckSubstMatch fuel tyCtx seen a' b'`.
    --
    -- WALL: bridging `Subtype' (closeAll a') (closeAll b')` back to
    -- `Subtype' (closeAll a) (closeAll b)` requires an evalSubst-
    -- based equivalence under closeAll.  The depth-0 / no-level-vars
    -- case is now closed by `Och.Soundness.evalSubst_equiv`
    -- (Soundness/EvalSubstEquiv.lean).  At depth `tyCtx.size > 0`
    -- the engine works on terms with level-vars; lifting the lemma
    -- through `closeAll` requires a closeAll-evalSubst commutation
    -- that's still unwritten.
    --
    --   evalSubst_equiv : closedAt 0 e → evalSubst e = .ok e' →
    --                     Subtype' [] [] e' e ∧ Subtype' [] [] e e'
    --
    -- For the depth-0 specialisation in `Och_subCheck_sound`, this
    -- closes step 1 of that chain.  Here at `tyCtx.size`, the bridge
    -- still walls on:
    --   * Translating `closedAt 0` ↔ `closedAtLvl 0` under closeAll.
    --   * Pushing `Subtype' [] [] e' e` through `closeAll` to
    --     `Subtype' (lift seen) tyCtxToCtx (closeAll e') (closeAll e)`.
    -- Both bridges discharge through the consolidated v2 wall
    -- `closeAll_evalSubst_subtype` (in `Soundness/CloseAll.lean`):
    -- given `evalSubst e = .ok e'`, the closeAll-translated forms
    -- are bidirectionally `Subtype'`-related.  At depth 0 this
    -- reduces to `evalSubst_equiv`; at non-zero depth it walls on
    -- the same v2 issue as the fallback substBridge_WALLs.
    have eval_bridge_a :
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size a) (closeAll tyCtx.size a') ∧
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size a') (closeAll tyCtx.size a) :=
      closeAll_evalSubst_subtype _h_a
    have eval_bridge_b :
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size b) (closeAll tyCtx.size b') ∧
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size b') (closeAll tyCtx.size b) :=
      closeAll_evalSubst_subtype _h_b
    -- Goal: derivation on closeAll a / closeAll b.  We chain
    -- `eval_bridge_a.1` ⊑ inner ⊑ `eval_bridge_b.2` after
    -- producing the inner derivation.
    suffices hinner :
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size a') (closeAll tyCtx.size b') by
      exact (eval_bridge_a.1.trans hinner).trans eval_bridge_b.2
    -- Inner case-split on `a' == b'`, seen, top, then match.
    by_cases heq : a' == b'
    · -- a' == b' ⟹ closeAll a' = closeAll b' (extensionally) ⟹ refl.
      have heq' : a' = b' := by simpa using heq
      subst heq'
      exact .refl _
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hany : seen.any (fun (av, bv) => a' == av && b' == bv)
      · -- (a', b') matches some entry in seen.  Use Subtype'.hyp
        -- after closeAll-and-lift translation.
        -- WALL: seen_coherence — engine seen is raw, lifted seen
        -- is closeAll'd; matching modulo translation requires a
        -- seen-coherence invariant.
        sorry
      · simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
        by_cases htop : b' == .type
        · have htop' : b' = .type := by simpa using htop
          subst htop'
          -- closeAll _ .type = .type
          show Subtype' _ _ _ .type
          exact .top _
        · simp only [htop, beq_self_eq_true, Bool.false_eq_true,
                     ↓reduceIte] at h
          -- Falls through to subCheckSubstMatch fuel✝ tyCtx seen a' b'
          -- where `heq✝ : fuel + 1 = fuel✝.succ`, i.e. `fuel = fuel✝`.
          -- Reify the equation (third inaccessible from the top) and
          -- substitute so the IH applies.
          rename_i _ _ heq_fuel _ _
          have hf : fuel = _ := Nat.succ.inj heq_fuel
          subst hf
          exact subCheckSubstMatch_dispatch
            (fun {_tyCtx'} {_seen'} {_x _y} hx => ih hx) h

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
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT tyCtx.size = true)
    (ha_cl : a.closedAtLvl 0 = true)
    (ha_lv : a.lvarLT tyCtx.size = true)
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
  iota_intro_arm h_eval hbody_cl hbody_lv ha_cl ha_lv ih_ann ih_body

/-- unfold_fix_R fallback composition. -/
theorem arm_unfold_fix_R_compose
    {a ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 (.fix ann bodyB)) = .ok bodyB'')
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT tyCtx.size = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT tyCtx.size = true)
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size a,
            closeAll tyCtx.size (.fix ann bodyB))
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a) (closeAll tyCtx.size bodyB'')) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a) (closeAll tyCtx.size (.fix ann bodyB)) :=
  unfold_fix_R_arm h_eval hbody_cl hbody_lv hann_cl hann_lv ih_body

/-- unfold_fix_L fallback composition. -/
theorem arm_unfold_fix_L_compose
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.fix ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT tyCtx.size = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT tyCtx.size = true)
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size (.fix ann bodyA),
            closeAll tyCtx.size b)
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a') (closeAll tyCtx.size b)) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.fix ann bodyA)) (closeAll tyCtx.size b) :=
  unfold_fix_L_arm h_eval hbody_cl hbody_lv hann_cl hann_lv ih_body

/-- unfold_iota_L fallback composition. -/
theorem arm_unfold_iota_L_compose
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.iota ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT tyCtx.size = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT tyCtx.size = true)
    (ih_body : Subtype'
        (((tyCtxToCtx tyCtx).length, closeAll tyCtx.size (.iota ann bodyA),
            closeAll tyCtx.size b)
          :: liftSeenList tyCtx.size seen)
        (tyCtxToCtx tyCtx)
        (closeAll tyCtx.size a') (closeAll tyCtx.size b)) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.iota ann bodyA)) (closeAll tyCtx.size b) :=
  unfold_iota_L_arm h_eval hbody_cl hbody_lv hann_cl hann_lv ih_body

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
