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

/-! ## Seen-coherence weakening across a depth bump

Under Design A, `liftSeenList d seen` translates each entry `(a, b)`
to `(d, closeAll d a, closeAll d b)`.  When the dispatch's IH
recurses under a binder (`tyCtx' = tyCtx.push x`, `d' = d + 1`), the
yielded derivation is against `liftSeenList (d + 1) seen`, but the
arm-package consumes `liftSeenList d seen`.  The `(d+1)` and `(d)`
forms are equi-derivable at the *current* (post-binder) Γ, modulo a
`shift 1 0` on every entry's terms — which `closeAll_succ_d_eq_shift`
provides under `closedAtLvl 0`/`lvarLT d` on each entry of `seen`.

The lemma below makes this translation explicit: a derivation in
`liftSeenList (d + 1) seen` (with seen entries well-formed at depth
`d`) re-translates to a derivation in `liftSeenList d seen` at the
same Γ.  The substantive case is `Subtype'.hyp`: a `(d+1)`-tagged
entry used at Γ.length `≥ d+1` re-emits as a `(d)`-tagged entry at
the same Γ, with the conclusion's shifts cancelling via
`shift_shift_same`.

The generalised form takes an arbitrary prefix `Sextra : Seen` (used
to thread through the `iota_intro`/`unfold_*` rules that grow `S`
with `(Γ.length, _, _)` entries while we descend).

This is the "seen-coherence under depth bump" wall named in the
module preamble; closing it required `closeAll_succ_d_eq_shift` (in
`Och/Soundness/CloseAll.lean`) plus a routine induction. -/

private theorem Subtype'_liftSeen_succ_to_d_aux
    {seen : List (Expr × Expr)} {d : Nat}
    (hseen_wf : ∀ p ∈ seen,
      p.1.closedAtLvl 0 = true ∧ p.1.lvarLT d = true ∧
      p.2.closedAtLvl 0 = true ∧ p.2.lvarLT d = true) :
    ∀ {Sextra : Seen} {Γ : Ctx} {x y : Expr},
      Subtype' (Sextra ++ liftSeenList (d + 1) seen) Γ x y →
      Subtype' (Sextra ++ liftSeenList d seen) Γ x y := by
  intro Sextra Γ x y h
  generalize hSeq : Sextra ++ liftSeenList (d + 1) seen = S at h
  induction h generalizing Sextra with
  | @hyp _ Γ d' a b hin hle =>
    subst hSeq
    -- `(d', a, b) ∈ Sextra ++ liftSeenList (d+1) seen`.
    rw [List.mem_append] at hin
    rcases hin with hL | hR
    · -- Entry from Sextra: same membership in the target.
      have hin' : (d', a, b) ∈ Sextra ++ liftSeenList d seen :=
        List.mem_append.mpr (Or.inl hL)
      exact Subtype'.hyp hin' hle
    · -- Entry from liftSeenList (d+1) seen.
      simp only [liftSeenList, List.mem_map] at hR
      obtain ⟨⟨a₀, b₀⟩, hp_in, hp_eq⟩ := hR
      -- hp_eq : (d+1, closeAll (d+1) a₀, closeAll (d+1) b₀) = (d', a, b)
      simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hd'_eq, ha_eq, hb_eq⟩ := hp_eq
      subst hd'_eq
      subst ha_eq
      subst hb_eq
      -- The corresponding (d, closeAll d a₀, closeAll d b₀) is in liftSeenList d seen.
      have hin_d : (d, closeAll d a₀, closeAll d b₀) ∈ liftSeenList d seen := by
        simp only [liftSeenList, List.mem_map]
        exact ⟨(a₀, b₀), hp_in, rfl⟩
      have hin_d' : (d, closeAll d a₀, closeAll d b₀) ∈
          Sextra ++ liftSeenList d seen :=
        List.mem_append.mpr (Or.inr hin_d)
      have hd_le : d ≤ Γ.length := by omega
      have hpwf := hseen_wf (a₀, b₀) hp_in
      obtain ⟨ha_cl, ha_lv, hb_cl, hb_lv⟩ := hpwf
      -- Apply hyp at the (d, ...) entry.
      have hsub :
          Subtype' (Sextra ++ liftSeenList d seen) Γ
            ((closeAll d a₀).shift (Γ.length - d) 0)
            ((closeAll d b₀).shift (Γ.length - d) 0) :=
        Subtype'.hyp hin_d' hd_le
      -- Need to rewrite to match the original conclusion shape.
      -- closeAll (d+1) a₀ = (closeAll d a₀).shift 1 0.
      have hca_a : closeAll (d + 1) a₀ = (closeAll d a₀).shift 1 0 :=
        closeAll_succ_d_eq_shift d a₀ ha_cl ha_lv
      have hca_b : closeAll (d + 1) b₀ = (closeAll d b₀).shift 1 0 :=
        closeAll_succ_d_eq_shift d b₀ hb_cl hb_lv
      rw [hca_a, hca_b]
      -- Goal: Subtype' ... ((closeAll d a₀).shift 1 0).shift (Γ.length - (d+1)) 0
      --                      ((closeAll d b₀).shift 1 0).shift (Γ.length - (d+1)) 0
      -- And hsub gives shift (Γ.length - d) on closeAll d a₀.
      have hshift_a :
          ((closeAll d a₀).shift 1 0).shift (Γ.length - (d + 1)) 0
            = (closeAll d a₀).shift (Γ.length - d) 0 := by
        rw [Expr.shift_shift_same]
        congr 1; omega
      have hshift_b :
          ((closeAll d b₀).shift 1 0).shift (Γ.length - (d + 1)) 0
            = (closeAll d b₀).shift (Γ.length - d) 0 := by
        rw [Expr.shift_shift_same]
        congr 1; omega
      rw [hshift_a, hshift_b]
      exact hsub
  | refl e => subst hSeq; exact .refl e
  | top e => subst hSeq; exact .top e
  | trans _ _ ih1 ih2 => subst hSeq; exact .trans (ih1 rfl) (ih2 rfl)
  | bvar h_get => subst hSeq; exact .bvar h_get
  | lam _ _ ih_d ih_b => subst hSeq; exact .lam (ih_d rfl) (ih_b rfl)
  | app_cong _ _ _ ihf iha iha' =>
    subst hSeq; exact .app_cong (ihf rfl) (iha rfl) (iha' rfl)
  | iota_body _ ih => subst hSeq; exact .iota_body (ih rfl)
  | fix_body _ ih => subst hSeq; exact .fix_body (ih rfl)
  | iota_cong _ _ ih_a ih_b => subst hSeq; exact .iota_cong (ih_a rfl) (ih_b rfl)
  | fix_cong _ _ ih_a ih_b => subst hSeq; exact .fix_cong (ih_a rfl) (ih_b rfl)
  | letE_cong _ _ ih_v ih_b => subst hSeq; exact .letE_cong (ih_v rfl) (ih_b rfl)
  | @iota_intro _ Γ a ann body _ _ ih1 ih2 =>
    subst hSeq
    refine .iota_intro ?_ ?_
    · have := ih1 (Sextra := (Γ.length, a, .iota ann body) :: Sextra)
      simpa [List.cons_append] using this rfl
    · have := ih2 (Sextra := (Γ.length, a, .iota ann body) :: Sextra)
      simpa [List.cons_append] using this rfl
  | @unfold_iota_L _ Γ ann body c _ ih =>
    subst hSeq
    refine .unfold_iota_L ?_
    have := ih (Sextra := (Γ.length, .iota ann body, c) :: Sextra)
    simpa [List.cons_append] using this rfl
  | @unfold_iota_R _ Γ a ann body _ ih =>
    subst hSeq
    refine .unfold_iota_R ?_
    have := ih (Sextra := (Γ.length, a, .iota ann body) :: Sextra)
    simpa [List.cons_append] using this rfl
  | @unfold_fix_L _ Γ ann body c _ ih =>
    subst hSeq
    refine .unfold_fix_L ?_
    have := ih (Sextra := (Γ.length, .fix ann body, c) :: Sextra)
    simpa [List.cons_append] using this rfl
  | @unfold_fix_R _ Γ a ann body _ ih =>
    subst hSeq
    refine .unfold_fix_R ?_
    have := ih (Sextra := (Γ.length, a, .fix ann body) :: Sextra)
    simpa [List.cons_append] using this rfl
  | beta_L _ ih => subst hSeq; exact .beta_L (ih rfl)
  | beta_R _ ih => subst hSeq; exact .beta_R (ih rfl)
  | letE_L _ ih => subst hSeq; exact .letE_L (ih rfl)
  | letE_R _ ih => subst hSeq; exact .letE_R (ih rfl)
  | asc_L _ ih => subst hSeq; exact .asc_L (ih rfl)
  | asc_R _ ih => subst hSeq; exact .asc_R (ih rfl)
  | bot_L => subst hSeq; exact .bot_L

/-- Public-facing form: a derivation in `liftSeenList (d + 1) seen`
re-translates to one in `liftSeenList d seen` at the same Γ, given
`seen` entries are well-formed at depth `d`.

Direct corollary of `Subtype'_liftSeen_succ_to_d_aux` at `Sextra = []`. -/
theorem Subtype'_liftSeen_succ_to_d
    {seen : List (Expr × Expr)} {d : Nat} {Γ : Ctx} {x y : Expr}
    (hseen_wf : ∀ p ∈ seen,
      p.1.closedAtLvl 0 = true ∧ p.1.lvarLT d = true ∧
      p.2.closedAtLvl 0 = true ∧ p.2.lvarLT d = true)
    (h : Subtype' (liftSeenList (d + 1) seen) Γ x y) :
    Subtype' (liftSeenList d seen) Γ x y := by
  have h' : Subtype' ([] ++ liftSeenList (d + 1) seen) Γ x y := by
    simpa using h
  have := Subtype'_liftSeen_succ_to_d_aux (Sextra := []) hseen_wf h'
  simpa using this

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
            (∀ p ∈ seen',
              p.1.closedAtLvl 0 = true ∧ p.1.lvarLT tyCtx'.size = true ∧
              p.2.closedAtLvl 0 = true ∧ p.2.lvarLT tyCtx'.size = true) →
            x.closedAtLvl 0 = true → x.lvarLT tyCtx'.size = true →
            y.closedAtLvl 0 = true → y.lvarLT tyCtx'.size = true →
            SubstEval.subCheckSubst fuel tyCtx' seen' x y = .ok true →
            Subtype' (liftSeenList tyCtx'.size seen') (tyCtxToCtx tyCtx')
              (closeAll tyCtx'.size x) (closeAll tyCtx'.size y))
    (_hseen_wf : ∀ p ∈ seen,
      p.1.closedAtLvl 0 = true ∧ p.1.lvarLT tyCtx.size = true ∧
      p.2.closedAtLvl 0 = true ∧ p.2.lvarLT tyCtx.size = true)
    (_ha_cl : a'.closedAtLvl 0 = true) (_ha_lv : a'.lvarLT tyCtx.size = true)
    (_hb_cl : b'.closedAtLvl 0 = true) (_hb_lv : b'.lvarLT tyCtx.size = true)
    (_h : SubstEval.subCheckSubstMatch fuel tyCtx seen a' b' = .ok true) :
    Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size a') (closeAll tyCtx.size b') := by
  -- 12-arm dispatch, inlined as an explicit `match a', b'` skeleton.
  --
  -- Each arm names the engine arm it discharges and the per-arm wall
  -- it surfaces.  Arms split into three groups:
  --
  --   * **Trivial** (no IH, no walls): C0 (.bot, _), and the engine's
  --     dispatch never actually reaches `b' = .type` because
  --     `subCheckSubst` short-circuits that case before invoking
  --     `subCheckSubstMatch`.  So the `_, .type` arms below are
  --     vacuous-from-`_h` (engine takes the catch-all neutral arm
  --     and returns `.ok false`).  We discharge them via
  --     `Subtype'.top` (declaratively still valid).
  --
  --   * **Structural** (lam-lam, iota-iota, fix-fix): arm-package
  --     calls require closedness invariants we don't carry here.
  --     WALLS: closedness_invariant_WALL + tyCtxPush_bridge_WALL
  --     (see module docstring).
  --
  --   * **Fallback** (iota_intro, unfold_*): route through the v2
  --     substitution bridges in `SubCheckSubstFallback.lean`.
  --     WALLS: v2 substitution bridges (already sorry'd internally).
  --
  --   * **Neutral** (bvar/app catch-all): spine-compare or ascent.
  --     WALLS: spine recursion (closes via app_cong + IH);
  --     `Subtype'_lvar_via_tyCtx` for the ascent fallback (closed
  --     in CloseAll.lean).
  --
  -- We surface ONE sorry per non-trivial arm (instead of one
  -- collapsed sorry for the whole dispatch).  Each per-arm sorry
  -- is a precise wall whose discharge is independent of the others.
  match a', b' with
  -- C0: bot ⊑ anything.  Engine returns `.ok true` unconditionally.
  | .bot, _ =>
    show Subtype' _ _ .bot _
    exact .bot_L
  -- _ ⊑ .type (RHS top): the engine's `subCheckSubstMatch` doesn't
  -- short-circuit `b' = .type` itself (that's done by
  -- `subCheckSubst` before it dispatches), but `Subtype'.top` closes
  -- the goal regardless of `_h`.
  | _, .type =>
    show Subtype' _ _ _ .type
    exact .top _
  -- C2: lam-lam structural.  Engine:
  --   contra ← subCheckSubst fuel tyCtx seen domB domA  (contravariant)
  --   bodyA' := openFresh bodyA depth, bodyB' := openFresh bodyB depth
  --   subCheckSubst fuel (tyCtx.push domB) seen bodyA' bodyB'
  -- IH composition via `subCheckSubst_arm_lam_lam` requires
  -- `bodyA.closedAtLvl 1`, `bodyA.lvarLT tyCtx.size` (and same for B);
  -- we extract these from `_ha_cl`/`_ha_lv`/`_hb_cl`/`_hb_lv`.
  --
  -- We extract both engine sub-results from `_h` and feed them
  -- through `_ih` (with closedness/lvarLT preconditions) to obtain
  -- `Subtype'` derivations on the domain and body sub-calls.  The
  -- body sub-call is recursed under `tyCtx.push domB`, so the IH
  -- yields a derivation against `liftSeenList (tyCtx.size + 1) seen`
  -- and `tyCtxToCtx (tyCtx.push domB) = tyCtxToCtx tyCtx ++ [domB]`,
  -- which `arm_lam_lam_compose` consumes as `liftSeenList tyCtx.size
  -- seen` and `closeAll tyCtx.size domB :: tyCtxToCtx tyCtx`.  The
  -- bridge between these is `tyCtxPush_bridge_WALL`.
  | .lam _domA _bodyA, .lam _domB _bodyB =>
    -- Decompose closedness on the LHS/RHS lams.
    have hclA_dom : _domA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hclB_dom : _domB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvA_dom : _domA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    have hlvB_dom : _domB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    -- Unfold the engine to expose the do-block on the lam-lam arm.
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    -- `_h` is now the do-block; extract `contra ← subCheckSubst fuel tyCtx seen domB domA`.
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨contra, h_dom_call, _h⟩ := _h
    -- `_h : (if !contra then pure false else …) = .ok true`.
    by_cases hcontra : contra
    · -- contra = true: `_h` reduces to the body sub-call.
      simp only [hcontra, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      -- `h_dom_call : subCheckSubst fuel tyCtx seen domB domA = .ok true`.
      have h_dom : SubstEval.subCheckSubst fuel tyCtx seen _domB _domA
          = .ok true := by
        rw [h_dom_call]; rw [hcontra]
      -- Apply `_ih` to the domain (contravariant) call.
      have ih_dom :
          Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
            (closeAll tyCtx.size _domB) (closeAll tyCtx.size _domA) :=
        _ih _hseen_wf hclB_dom hlvB_dom hclA_dom hlvA_dom h_dom
      -- The body sub-call is `subCheckSubst fuel (tyCtx.push _domB)
      -- seen (openFresh _bodyA tyCtx.size) (openFresh _bodyB
      -- tyCtx.size) = .ok true`.  Apply `_ih` to obtain a derivation
      -- against `liftSeenList (tyCtx.size + 1) seen` and
      -- `tyCtxToCtx (tyCtx.push _domB) = closeAll tyCtx.size _domB
      -- :: tyCtxToCtx tyCtx`; then translate the Seen via
      -- `Subtype'_liftSeen_succ_to_d`.
      have h_body_call :
          SubstEval.subCheckSubst fuel (tyCtx.push _domB) seen
            (SubstEval.openFreshTop _bodyA tyCtx.size)
            (SubstEval.openFreshTop _bodyB tyCtx.size)
            = .ok true := _h
      -- Closedness/lvarLT for openFreshTop bodyA/bodyB at depth tyCtx.size.
      have h_open_a_cl : (SubstEval.openFreshTop _bodyA tyCtx.size).closedAtLvl 0
          = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclA_body
      have h_open_b_cl : (SubstEval.openFreshTop _bodyB tyCtx.size).closedAtLvl 0
          = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclB_body
      have hlvA_body_succ : _bodyA.lvarLT (tyCtx.push _domB).size = true := by
        rw [Array.size_push]
        exact lvarLT_mono hlvA_body (Nat.le_succ _)
      have hlvB_body_succ : _bodyB.lvarLT (tyCtx.push _domB).size = true := by
        rw [Array.size_push]
        exact lvarLT_mono hlvB_body (Nat.le_succ _)
      have h_depth_lt : tyCtx.size < (tyCtx.push _domB).size := by
        rw [Array.size_push]; omega
      have h_open_a_lv :
          (SubstEval.openFreshTop _bodyA tyCtx.size).lvarLT
            (tyCtx.push _domB).size = true := by
        rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
        refine substL_lvarLT _bodyA 0 _ _ hlvA_body_succ
          (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
        exact lvarLT_freshLevelVar _ _ h_depth_lt
      have h_open_b_lv :
          (SubstEval.openFreshTop _bodyB tyCtx.size).lvarLT
            (tyCtx.push _domB).size = true := by
        rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
        refine substL_lvarLT _bodyB 0 _ _ hlvB_body_succ
          (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
        exact lvarLT_freshLevelVar _ _ h_depth_lt
      -- Seen-wf at the new depth (tyCtx.size + 1) follows by lvarLT_mono.
      have h_seen_wf_succ : ∀ p ∈ seen,
          p.1.closedAtLvl 0 = true ∧
          p.1.lvarLT (tyCtx.push _domB).size = true ∧
          p.2.closedAtLvl 0 = true ∧
          p.2.lvarLT (tyCtx.push _domB).size = true := by
        intro p hp
        obtain ⟨h1, h2, h3, h4⟩ := _hseen_wf p hp
        rw [Array.size_push]
        refine ⟨h1, ?_, h3, ?_⟩
        · exact lvarLT_mono h2 (Nat.le_succ _)
        · exact lvarLT_mono h4 (Nat.le_succ _)
      -- Apply IH at the body call.
      have ih_body_succ :
          Subtype' (liftSeenList (tyCtx.push _domB).size seen)
              (tyCtxToCtx (tyCtx.push _domB))
              (closeAll (tyCtx.push _domB).size
                (SubstEval.openFreshTop _bodyA tyCtx.size))
              (closeAll (tyCtx.push _domB).size
                (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
        _ih h_seen_wf_succ h_open_a_cl h_open_a_lv h_open_b_cl h_open_b_lv
          h_body_call
      -- Rewrite Γ via tyCtxToCtx_push and the Seen tag via
      -- Subtype'_liftSeen_succ_to_d.
      rw [tyCtxToCtx_push] at ih_body_succ
      rw [Array.size_push] at ih_body_succ
      have ih_body :
          Subtype' (liftSeenList tyCtx.size seen)
              (closeAll tyCtx.size _domB :: tyCtxToCtx tyCtx)
              (closeAll (tyCtx.size + 1)
                (SubstEval.openFreshTop _bodyA tyCtx.size))
              (closeAll (tyCtx.size + 1)
                (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
        Subtype'_liftSeen_succ_to_d _hseen_wf ih_body_succ
      -- Apply the lam-lam composition arm (from SubCheckSubstStructural).
      exact subCheckSubst_arm_lam_lam hclA_body hclB_body
        hlvA_body hlvB_body ih_dom ih_body
    · -- contra = false: `_h` reduces to `pure false = .ok true`,
      -- contradicting the premise.
      simp only [hcontra, Bool.not_false, ↓reduceIte,
                 pure, Outcome.ok.injEq] at _h
      cases _h
  -- C3 (iota-iota): structural-attempt → `subCheckSubst_arm_iota_iota`,
  -- else fallback → `iota_intro_arm`.
  -- After the engine refactor (commit 7b506eb), the structural attempt
  -- uses bare `seen` (no `(a,b)` extension); the seen extension is
  -- moved into the fallback only.  This means the structural success
  -- path threads `liftSeenList tyCtx.size seen` directly with no
  -- Seen-shrinking step, mirroring the lam-lam template.
  | .iota _annA _bodyA, .iota _annB _bodyB =>
    -- Decompose closedness on the LHS/RHS iotas.
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    -- Unfold the engine.
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    -- `_h` is `match structural with | .ok true => .ok true | _ => fallback`,
    -- where structural is the bare-seen do-block.
    -- Split on the structural's outcome.
    split at _h
    · -- structural = .ok true: extract the do-block.
      rename_i hstruct
      -- `hstruct : (do …structural body…) = .ok true`
      rw [Outcome.bind_eq_ok] at hstruct
      obtain ⟨annOk, h_ann_call, hstruct⟩ := hstruct
      by_cases hannOk : annOk
      · -- annOk = true: hstruct reduces to body sub-call.
        simp only [hannOk, Bool.not_true, Bool.false_eq_true,
                   ↓reduceIte] at hstruct
        have h_ann : SubstEval.subCheckSubst fuel tyCtx seen _annA _annB
            = .ok true := by
          rw [h_ann_call]; rw [hannOk]
        have ih_ann :
            Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
              (closeAll tyCtx.size _annA) (closeAll tyCtx.size _annB) :=
          _ih _hseen_wf hclA_ann hlvA_ann hclB_ann hlvB_ann h_ann
        -- Body sub-call: under tyCtx.push annB, bare seen.
        have h_body_call :
            SubstEval.subCheckSubst fuel (tyCtx.push _annB) seen
              (SubstEval.openFreshTop _bodyA tyCtx.size)
              (SubstEval.openFreshTop _bodyB tyCtx.size)
              = .ok true := hstruct
        have h_open_a_cl : (SubstEval.openFreshTop _bodyA tyCtx.size).closedAtLvl 0
            = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclA_body
        have h_open_b_cl : (SubstEval.openFreshTop _bodyB tyCtx.size).closedAtLvl 0
            = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclB_body
        have hlvA_body_succ : _bodyA.lvarLT (tyCtx.push _annB).size = true := by
          rw [Array.size_push]
          exact lvarLT_mono hlvA_body (Nat.le_succ _)
        have hlvB_body_succ : _bodyB.lvarLT (tyCtx.push _annB).size = true := by
          rw [Array.size_push]
          exact lvarLT_mono hlvB_body (Nat.le_succ _)
        have h_depth_lt : tyCtx.size < (tyCtx.push _annB).size := by
          rw [Array.size_push]; omega
        have h_open_a_lv :
            (SubstEval.openFreshTop _bodyA tyCtx.size).lvarLT
              (tyCtx.push _annB).size = true := by
          rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
          refine substL_lvarLT _bodyA 0 _ _ hlvA_body_succ
            (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
          exact lvarLT_freshLevelVar _ _ h_depth_lt
        have h_open_b_lv :
            (SubstEval.openFreshTop _bodyB tyCtx.size).lvarLT
              (tyCtx.push _annB).size = true := by
          rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
          refine substL_lvarLT _bodyB 0 _ _ hlvB_body_succ
            (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
          exact lvarLT_freshLevelVar _ _ h_depth_lt
        have h_seen_wf_succ : ∀ p ∈ seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT (tyCtx.push _annB).size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT (tyCtx.push _annB).size = true := by
          intro p hp
          obtain ⟨h1, h2, h3, h4⟩ := _hseen_wf p hp
          rw [Array.size_push]
          refine ⟨h1, ?_, h3, ?_⟩
          · exact lvarLT_mono h2 (Nat.le_succ _)
          · exact lvarLT_mono h4 (Nat.le_succ _)
        have ih_body_succ :
            Subtype' (liftSeenList (tyCtx.push _annB).size seen)
                (tyCtxToCtx (tyCtx.push _annB))
                (closeAll (tyCtx.push _annB).size
                  (SubstEval.openFreshTop _bodyA tyCtx.size))
                (closeAll (tyCtx.push _annB).size
                  (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
          _ih h_seen_wf_succ h_open_a_cl h_open_a_lv h_open_b_cl h_open_b_lv
            h_body_call
        rw [tyCtxToCtx_push] at ih_body_succ
        rw [Array.size_push] at ih_body_succ
        have ih_body :
            Subtype' (liftSeenList tyCtx.size seen)
                (closeAll tyCtx.size _annB :: tyCtxToCtx tyCtx)
                (closeAll (tyCtx.size + 1)
                  (SubstEval.openFreshTop _bodyA tyCtx.size))
                (closeAll (tyCtx.size + 1)
                  (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
          Subtype'_liftSeen_succ_to_d _hseen_wf ih_body_succ
        exact subCheckSubst_arm_iota_iota hclA_body hclB_body
          hlvA_body hlvB_body ih_ann ih_body
      · -- annOk = false: hstruct collapses to `pure false = .ok true`,
        -- contradicting the structural success.
        simp only [hannOk, Bool.not_false, ↓reduceIte,
                   pure, Outcome.ok.injEq] at hstruct
        cases hstruct
    · -- structural = NOT .ok true: fallback path (iota_intro).
      -- Engine: let seen' := (a, b) :: seen
      --        let okAnn ← subCheckSubst fuel tyCtx seen' a annB
      --        if !okAnn then .ok false
      --        else do
      --          let bodyB' := substL bodyB 0 a
      --          match evalSubst (fuel + 1) unfBound bodyB' with
      --          | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
      --          | _ => .ok false
      rw [Outcome.bind_eq_ok] at _h
      obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
      by_cases hokAnn : okAnn
      · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                   ↓reduceIte] at _h
        split at _h
        · rename_i bodyB'' h_eval
          -- h_eval : evalSubst (fuel + 1) unfBound (substL _bodyB 0 (.iota _annA _bodyA)) = .ok bodyB''
          -- _h : subCheckSubst fuel tyCtx seen' (.iota _annA _bodyA) bodyB'' = .ok true
          -- where seen' = (.iota _annA _bodyA, .iota _annB _bodyB) :: seen.
          have h_okAnn :
              SubstEval.subCheckSubst fuel tyCtx
                  ((Expr.iota _annA _bodyA, Expr.iota _annB _bodyB) :: seen)
                  (Expr.iota _annA _bodyA) _annB = .ok true := by
            rw [h_okAnn_call]; rw [hokAnn]
          -- seen' well-formedness: the new entry uses (.iota _annA _bodyA) and
          -- (.iota _annB _bodyB), both of which inherit closedAtLvl 0 / lvarLT
          -- tyCtx.size from the original `_ha_cl/_hb_cl/_ha_lv/_hb_lv`.
          have h_seen'_wf : ∀ p ∈
              (Expr.iota _annA _bodyA, Expr.iota _annB _bodyB) :: seen,
              p.1.closedAtLvl 0 = true ∧
              p.1.lvarLT tyCtx.size = true ∧
              p.2.closedAtLvl 0 = true ∧
              p.2.lvarLT tyCtx.size = true := by
            intro p hp
            rcases List.mem_cons.mp hp with heq | hin
            · subst heq
              exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
            · exact _hseen_wf p hin
          -- IH on the okAnn call: yields Subtype' over liftSeenList tyCtx.size seen'.
          have ih_ann :
              Subtype'
                  (liftSeenList tyCtx.size
                    ((Expr.iota _annA _bodyA, Expr.iota _annB _bodyB) :: seen))
                  (tyCtxToCtx tyCtx)
                  (closeAll tyCtx.size (Expr.iota _annA _bodyA))
                  (closeAll tyCtx.size _annB) :=
            _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
          -- Body sub-call closedness for the IH.
          have h_substL_cl :
              (SubstEval.substL _bodyB 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
                = true :=
            SubstEval.substL_closedAtLvl hclB_body _ha_cl
          have h_substL_lv :
              (SubstEval.substL _bodyB 0 (Expr.iota _annA _bodyA)).lvarLT
                tyCtx.size = true :=
            substL_lvarLT _bodyB 0 tyCtx.size (Expr.iota _annA _bodyA)
              hlvB_body _ha_cl _ha_lv
          have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
          have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
            evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
          have ih_body :
              Subtype'
                  (liftSeenList tyCtx.size
                    ((Expr.iota _annA _bodyA, Expr.iota _annB _bodyB) :: seen))
                  (tyCtxToCtx tyCtx)
                  (closeAll tyCtx.size (Expr.iota _annA _bodyA))
                  (closeAll tyCtx.size bodyB'') :=
            _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
          -- Convert `liftSeenList tyCtx.size (cons … seen)` into the form
          -- `((tyCtxToCtx tyCtx).length, closeAll …, closeAll …) :: liftSeenList tyCtx.size seen`
          -- expected by `arm_iota_intro_compose`.
          have h_seen_unfold :
              liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.iota _annB _bodyB) :: seen)
                = ((tyCtxToCtx tyCtx).length,
                    closeAll tyCtx.size (Expr.iota _annA _bodyA),
                    closeAll tyCtx.size (Expr.iota _annB _bodyB))
                  :: liftSeenList tyCtx.size seen := by
            simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
          rw [h_seen_unfold] at ih_ann ih_body
          -- `iota_intro_arm` is now fuel-polymorphic (wall 2a, option 2):
          -- `h_eval` from the engine has shape
          -- `evalSubst (fuel + 1) unfBound … = .ok bodyB''` and unifies
          -- directly with the arm-lemma's `{fuel unf : Nat}` binders.
          exact iota_intro_arm h_eval hclB_body hlvB_body
            _ha_cl _ha_lv ih_ann ih_body
        · cases _h
      · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
        cases _h
  -- C4 (fix-fix): structural-attempt → `subCheckSubst_arm_fix_fix`,
  -- else fallback → `unfold_fix_R_arm`.
  -- Same shape as iota-iota.  After the engine refactor, structural
  -- attempt uses bare seen.
  | .fix _annA _bodyA, .fix _annB _bodyB =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · -- structural success.
      rename_i hstruct
      rw [Outcome.bind_eq_ok] at hstruct
      obtain ⟨annOk, h_ann_call, hstruct⟩ := hstruct
      by_cases hannOk : annOk
      · simp only [hannOk, Bool.not_true, Bool.false_eq_true,
                   ↓reduceIte] at hstruct
        have h_ann : SubstEval.subCheckSubst fuel tyCtx seen _annA _annB
            = .ok true := by
          rw [h_ann_call]; rw [hannOk]
        have ih_ann :
            Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
              (closeAll tyCtx.size _annA) (closeAll tyCtx.size _annB) :=
          _ih _hseen_wf hclA_ann hlvA_ann hclB_ann hlvB_ann h_ann
        have h_body_call :
            SubstEval.subCheckSubst fuel (tyCtx.push _annB) seen
              (SubstEval.openFreshTop _bodyA tyCtx.size)
              (SubstEval.openFreshTop _bodyB tyCtx.size)
              = .ok true := hstruct
        have h_open_a_cl : (SubstEval.openFreshTop _bodyA tyCtx.size).closedAtLvl 0
            = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclA_body
        have h_open_b_cl : (SubstEval.openFreshTop _bodyB tyCtx.size).closedAtLvl 0
            = true := SubstEval.openFreshTop_closedAtLvl_zero _ _ hclB_body
        have hlvA_body_succ : _bodyA.lvarLT (tyCtx.push _annB).size = true := by
          rw [Array.size_push]
          exact lvarLT_mono hlvA_body (Nat.le_succ _)
        have hlvB_body_succ : _bodyB.lvarLT (tyCtx.push _annB).size = true := by
          rw [Array.size_push]
          exact lvarLT_mono hlvB_body (Nat.le_succ _)
        have h_depth_lt : tyCtx.size < (tyCtx.push _annB).size := by
          rw [Array.size_push]; omega
        have h_open_a_lv :
            (SubstEval.openFreshTop _bodyA tyCtx.size).lvarLT
              (tyCtx.push _annB).size = true := by
          rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
          refine substL_lvarLT _bodyA 0 _ _ hlvA_body_succ
            (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
          exact lvarLT_freshLevelVar _ _ h_depth_lt
        have h_open_b_lv :
            (SubstEval.openFreshTop _bodyB tyCtx.size).lvarLT
              (tyCtx.push _annB).size = true := by
          rw [SubstEval.openFreshTop_eq_substL_freshLevelVar]
          refine substL_lvarLT _bodyB 0 _ _ hlvB_body_succ
            (SubstEval.closedAtLvl_freshLevelVar _ _) ?_
          exact lvarLT_freshLevelVar _ _ h_depth_lt
        have h_seen_wf_succ : ∀ p ∈ seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT (tyCtx.push _annB).size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT (tyCtx.push _annB).size = true := by
          intro p hp
          obtain ⟨h1, h2, h3, h4⟩ := _hseen_wf p hp
          rw [Array.size_push]
          refine ⟨h1, ?_, h3, ?_⟩
          · exact lvarLT_mono h2 (Nat.le_succ _)
          · exact lvarLT_mono h4 (Nat.le_succ _)
        have ih_body_succ :
            Subtype' (liftSeenList (tyCtx.push _annB).size seen)
                (tyCtxToCtx (tyCtx.push _annB))
                (closeAll (tyCtx.push _annB).size
                  (SubstEval.openFreshTop _bodyA tyCtx.size))
                (closeAll (tyCtx.push _annB).size
                  (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
          _ih h_seen_wf_succ h_open_a_cl h_open_a_lv h_open_b_cl h_open_b_lv
            h_body_call
        rw [tyCtxToCtx_push] at ih_body_succ
        rw [Array.size_push] at ih_body_succ
        have ih_body :
            Subtype' (liftSeenList tyCtx.size seen)
                (closeAll tyCtx.size _annB :: tyCtxToCtx tyCtx)
                (closeAll (tyCtx.size + 1)
                  (SubstEval.openFreshTop _bodyA tyCtx.size))
                (closeAll (tyCtx.size + 1)
                  (SubstEval.openFreshTop _bodyB tyCtx.size)) :=
          Subtype'_liftSeen_succ_to_d _hseen_wf ih_body_succ
        exact subCheckSubst_arm_fix_fix hclA_body hclB_body
          hlvA_body hlvB_body ih_ann ih_body
      · simp only [hannOk, Bool.not_false, ↓reduceIte,
                   pure, Outcome.ok.injEq] at hstruct
        cases hstruct
    · -- structural fail: fallback path (unfold_fix_R).
      -- Engine: let seen' := (a, b) :: seen
      --        let unfolded := substL bodyB 0 b
      --        match evalSubst (fuel + 1) unfBound unfolded with
      --        | .ok b' => subCheckSubst fuel tyCtx seen' a b'
      --        | _ => .ok false
      split at _h
      · rename_i b' h_eval
        -- h_eval : evalSubst (fuel + 1) unfBound (substL _bodyB 0 (.fix _annB _bodyB)) = .ok b'
        -- _h : subCheckSubst fuel tyCtx seen' (.fix _annA _bodyA) b' = .ok true
        -- where seen' = (.fix _annA _bodyA, .fix _annB _bodyB) :: seen.
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.fix _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        -- Closedness for substL bodyB 0 (fix annB bodyB).
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _hb_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.fix _annB _bodyB)
            hlvB_body _hb_cl _hb_lv
        have h_b'_cl : b'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_b'_lv : b'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.fix _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.fix _annA _bodyA))
                (closeAll tyCtx.size b') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_b'_cl h_b'_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.fix _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.fix _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        -- `unfold_fix_R_arm` is now fuel-polymorphic (wall 2a, option 2);
        -- the engine's `h_eval : evalSubst (fuel + 1) unfBound … = .ok b'`
        -- unifies directly with the arm-lemma's `{fuel unf : Nat}` binders.
        exact unfold_fix_R_arm h_eval hclB_body hlvB_body
          hclB_ann hlvB_ann ih_body
      · cases _h
  -- _ ⊑ ι : iotaIntro fallback.  Routes through
  -- `iota_intro_arm` (fuel-polymorphic post wall 2a).
  -- We enumerate every non-iota, non-bot LHS.  Each arm has the same
  -- engine shape — the LHS pattern is ignored and the engine takes
  -- the `_, .iota ann bodyB` catch-all.
  | .bvar _k, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    -- Engine flow for `_, .iota`:
    --   let seen' := (a, b) :: seen
    --   let okAnn ← subCheckSubst fuel tyCtx seen' a annB
    --   if !okAnn then .ok false
    --   else match evalSubst (fuel + 1) unfBound (substL bodyB 0 a) with
    --        | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
    --        | _ => .ok false
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.bvar _k, Expr.iota _annB _bodyB) :: seen)
                (Expr.bvar _k) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.bvar _k, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.bvar _k, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.bvar _k))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.bvar _k)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.bvar _k)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.bvar _k)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.bvar _k, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.bvar _k))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.bvar _k, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.bvar _k),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  | .app _f _v, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.app _f _v, Expr.iota _annB _bodyB) :: seen)
                (Expr.app _f _v) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.app _f _v, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.app _f _v, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.app _f _v))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.app _f _v)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.app _f _v)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.app _f _v)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.app _f _v, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.app _f _v))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.app _f _v, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.app _f _v),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  | .lam _domA _bodyA, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.lam _domA _bodyA, Expr.iota _annB _bodyB) :: seen)
                (Expr.lam _domA _bodyA) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.lam _domA _bodyA, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.lam _domA _bodyA, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.lam _domA _bodyA))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.lam _domA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.lam _domA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.lam _domA _bodyA)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.lam _domA _bodyA, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.lam _domA _bodyA))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.lam _domA _bodyA, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.lam _domA _bodyA),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  | .fix _annA _bodyA, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.fix _annA _bodyA, Expr.iota _annB _bodyB) :: seen)
                (Expr.fix _annA _bodyA) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.fix _annA _bodyA))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.fix _annA _bodyA))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  | .asc _t _ty, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.asc _t _ty, Expr.iota _annB _bodyB) :: seen)
                (Expr.asc _t _ty) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.asc _t _ty, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.asc _t _ty, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.asc _t _ty))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.asc _t _ty)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.asc _t _ty)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.asc _t _ty)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.asc _t _ty, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.asc _t _ty))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.asc _t _ty, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.asc _t _ty),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  | .letE _v _b, .iota _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    rw [Outcome.bind_eq_ok] at _h
    obtain ⟨okAnn, h_okAnn_call, _h⟩ := _h
    by_cases hokAnn : okAnn
    · simp only [hokAnn, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at _h
      split at _h
      · rename_i bodyB'' h_eval
        have h_okAnn :
            SubstEval.subCheckSubst fuel tyCtx
                ((Expr.letE _v _b, Expr.iota _annB _bodyB) :: seen)
                (Expr.letE _v _b) _annB = .ok true := by
          rw [h_okAnn_call]; rw [hokAnn]
        have h_seen'_wf : ∀ p ∈
            (Expr.letE _v _b, Expr.iota _annB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have ih_ann :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.letE _v _b, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.letE _v _b))
                (closeAll tyCtx.size _annB) :=
          _ih h_seen'_wf _ha_cl _ha_lv hclB_ann hlvB_ann h_okAnn
        have h_substL_cl :
            (SubstEval.substL _bodyB 0 (Expr.letE _v _b)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclB_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyB 0 (Expr.letE _v _b)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyB 0 tyCtx.size (Expr.letE _v _b)
            hlvB_body _ha_cl _ha_lv
        have h_bodyB''_cl : bodyB''.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_bodyB''_lv : bodyB''.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.letE _v _b, Expr.iota _annB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size (Expr.letE _v _b))
                (closeAll tyCtx.size bodyB'') :=
          _ih h_seen'_wf _ha_cl _ha_lv h_bodyB''_cl h_bodyB''_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.letE _v _b, Expr.iota _annB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.letE _v _b),
                  closeAll tyCtx.size (Expr.iota _annB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_ann ih_body
        exact iota_intro_arm h_eval hclB_body hlvB_body
          _ha_cl _ha_lv ih_ann ih_body
      · cases _h
    · simp only [hokAnn, Bool.not_false, ↓reduceIte] at _h
      cases _h
  -- _ ⊑ fix : unfoldFixR fallback.  Routes through `unfold_fix_R_arm`.
  -- Non-neutral LHS (lam/asc/letE): engine takes the `else` branch
  -- (no `isNeutral` short-circuit), giving the clean fallback shape.
  -- Neutral LHS (bvar/app): engine enters the `if isNeutral` branch
  -- with a `synthNeutralType` lookup and a `ty == b` short-circuit.
  -- The `ty == b` true case demands a Subtype' derivation from a
  -- type ascent (essentially `Subtype'_lvar_via_tyCtx`'s territory),
  -- which is a separate open wall (neutral-ascent fallback).  We
  -- leave these 2 arms `sorry` with a pointer; they unblock alongside
  -- the spine bvar-bvar arm at line 2278-2280.
  | .bvar _k, .fix _ann _bodyB => sorry
  | .app _f _v, .fix _ann _bodyB => sorry
  | .lam _domA _bodyA, .fix _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only [SubstEval.isNeutral, Bool.false_eq_true,
               ↓reduceIte] at _h
    -- LHS is .lam, not neutral, so engine takes the `else` branch.
    -- After simp, `_h` is the match-on-evalSubst directly.
    split at _h
    · rename_i b' h_eval
      have h_seen'_wf : ∀ p ∈
          (Expr.lam _domA _bodyA, Expr.fix _annB _bodyB) :: seen,
          p.1.closedAtLvl 0 = true ∧
          p.1.lvarLT tyCtx.size = true ∧
          p.2.closedAtLvl 0 = true ∧
          p.2.lvarLT tyCtx.size = true := by
        intro p hp
        rcases List.mem_cons.mp hp with heq | hin
        · subst heq
          exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
        · exact _hseen_wf p hin
      have h_substL_cl :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).closedAtLvl 0
            = true :=
        SubstEval.substL_closedAtLvl hclB_body _hb_cl
      have h_substL_lv :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).lvarLT
            tyCtx.size = true :=
        substL_lvarLT _bodyB 0 tyCtx.size (Expr.fix _annB _bodyB)
          hlvB_body _hb_cl _hb_lv
      have h_b'_cl : b'.closedAtLvl 0 = true :=
        SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
      have h_b'_lv : b'.lvarLT tyCtx.size = true :=
        evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
      have ih_body :
          Subtype'
              (liftSeenList tyCtx.size
                ((Expr.lam _domA _bodyA, Expr.fix _annB _bodyB) :: seen))
              (tyCtxToCtx tyCtx)
              (closeAll tyCtx.size (Expr.lam _domA _bodyA))
              (closeAll tyCtx.size b') :=
        _ih h_seen'_wf _ha_cl _ha_lv h_b'_cl h_b'_lv _h
      have h_seen_unfold :
          liftSeenList tyCtx.size
              ((Expr.lam _domA _bodyA, Expr.fix _annB _bodyB) :: seen)
            = ((tyCtxToCtx tyCtx).length,
                closeAll tyCtx.size (Expr.lam _domA _bodyA),
                closeAll tyCtx.size (Expr.fix _annB _bodyB))
              :: liftSeenList tyCtx.size seen := by
        simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
      rw [h_seen_unfold] at ih_body
      exact unfold_fix_R_arm h_eval hclB_body hlvB_body
        hclB_ann hlvB_ann ih_body
    · cases _h
  | .asc _t _ty, .fix _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only [SubstEval.isNeutral, Bool.false_eq_true,
               ↓reduceIte] at _h
    split at _h
    · rename_i b' h_eval
      have h_seen'_wf : ∀ p ∈
          (Expr.asc _t _ty, Expr.fix _annB _bodyB) :: seen,
          p.1.closedAtLvl 0 = true ∧
          p.1.lvarLT tyCtx.size = true ∧
          p.2.closedAtLvl 0 = true ∧
          p.2.lvarLT tyCtx.size = true := by
        intro p hp
        rcases List.mem_cons.mp hp with heq | hin
        · subst heq
          exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
        · exact _hseen_wf p hin
      have h_substL_cl :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).closedAtLvl 0
            = true :=
        SubstEval.substL_closedAtLvl hclB_body _hb_cl
      have h_substL_lv :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).lvarLT
            tyCtx.size = true :=
        substL_lvarLT _bodyB 0 tyCtx.size (Expr.fix _annB _bodyB)
          hlvB_body _hb_cl _hb_lv
      have h_b'_cl : b'.closedAtLvl 0 = true :=
        SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
      have h_b'_lv : b'.lvarLT tyCtx.size = true :=
        evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
      have ih_body :
          Subtype'
              (liftSeenList tyCtx.size
                ((Expr.asc _t _ty, Expr.fix _annB _bodyB) :: seen))
              (tyCtxToCtx tyCtx)
              (closeAll tyCtx.size (Expr.asc _t _ty))
              (closeAll tyCtx.size b') :=
        _ih h_seen'_wf _ha_cl _ha_lv h_b'_cl h_b'_lv _h
      have h_seen_unfold :
          liftSeenList tyCtx.size
              ((Expr.asc _t _ty, Expr.fix _annB _bodyB) :: seen)
            = ((tyCtxToCtx tyCtx).length,
                closeAll tyCtx.size (Expr.asc _t _ty),
                closeAll tyCtx.size (Expr.fix _annB _bodyB))
              :: liftSeenList tyCtx.size seen := by
        simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
      rw [h_seen_unfold] at ih_body
      exact unfold_fix_R_arm h_eval hclB_body hlvB_body
        hclB_ann hlvB_ann ih_body
    · cases _h
  | .letE _v _b, .fix _annB _bodyB =>
    have hclB_ann : _annB.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.1
    have hclB_body : _bodyB.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _hb_cl
      exact _hb_cl.2
    have hlvB_ann : _annB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.1
    have hlvB_body : _bodyB.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _hb_lv
      exact _hb_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only [SubstEval.isNeutral, Bool.false_eq_true,
               ↓reduceIte] at _h
    split at _h
    · rename_i b' h_eval
      have h_seen'_wf : ∀ p ∈
          (Expr.letE _v _b, Expr.fix _annB _bodyB) :: seen,
          p.1.closedAtLvl 0 = true ∧
          p.1.lvarLT tyCtx.size = true ∧
          p.2.closedAtLvl 0 = true ∧
          p.2.lvarLT tyCtx.size = true := by
        intro p hp
        rcases List.mem_cons.mp hp with heq | hin
        · subst heq
          exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
        · exact _hseen_wf p hin
      have h_substL_cl :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).closedAtLvl 0
            = true :=
        SubstEval.substL_closedAtLvl hclB_body _hb_cl
      have h_substL_lv :
          (SubstEval.substL _bodyB 0 (Expr.fix _annB _bodyB)).lvarLT
            tyCtx.size = true :=
        substL_lvarLT _bodyB 0 tyCtx.size (Expr.fix _annB _bodyB)
          hlvB_body _hb_cl _hb_lv
      have h_b'_cl : b'.closedAtLvl 0 = true :=
        SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
      have h_b'_lv : b'.lvarLT tyCtx.size = true :=
        evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
      have ih_body :
          Subtype'
              (liftSeenList tyCtx.size
                ((Expr.letE _v _b, Expr.fix _annB _bodyB) :: seen))
              (tyCtxToCtx tyCtx)
              (closeAll tyCtx.size (Expr.letE _v _b))
              (closeAll tyCtx.size b') :=
        _ih h_seen'_wf _ha_cl _ha_lv h_b'_cl h_b'_lv _h
      have h_seen_unfold :
          liftSeenList tyCtx.size
              ((Expr.letE _v _b, Expr.fix _annB _bodyB) :: seen)
            = ((tyCtxToCtx tyCtx).length,
                closeAll tyCtx.size (Expr.letE _v _b),
                closeAll tyCtx.size (Expr.fix _annB _bodyB))
              :: liftSeenList tyCtx.size seen := by
        simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
      rw [h_seen_unfold] at ih_body
      exact unfold_fix_R_arm h_eval hclB_body hlvB_body
        hclB_ann hlvB_ann ih_body
    · cases _h
  -- fix ⊑ _ : unfoldFixL fallback (LHS = fix; already handled
  -- fix-fix and fix-iota above).
  -- Engine: `let seen' := (a, b) :: seen; …; match evalSubst …`
  --        `with | .ok a' => if a' == a then .ok false else …`
  -- Per arm: extract hclA_ann/hclA_body, run evalSubst, handle the
  -- `a' == a` short-circuit (false ⟹ contradicts `_h`), recurse via
  -- `unfold_fix_L_arm`.
  | .fix _annA _bodyA, .bvar _k =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.fix _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.bvar _k) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.bvar _k) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.bvar _k)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.bvar _k) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.bvar _k))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_fix_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .fix _annA _bodyA, .app _f _v =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.fix _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.app _f _v) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.app _f _v) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.app _f _v)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.app _f _v) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.app _f _v))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_fix_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .fix _annA _bodyA, .lam _domB _bodyB =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.fix _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.lam _domB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.lam _domB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.lam _domB _bodyB)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.lam _domB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.lam _domB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_fix_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .fix _annA _bodyA, .asc _t _ty =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.fix _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.asc _t _ty) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.asc _t _ty) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.asc _t _ty)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.asc _t _ty) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.asc _t _ty))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_fix_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .fix _annA _bodyA, .letE _v _b =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.fix _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.fix _annA _bodyA, Expr.letE _v _b) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.fix _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.fix _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.fix _annA _bodyA, Expr.letE _v _b) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.letE _v _b)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.fix _annA _bodyA, Expr.letE _v _b) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.fix _annA _bodyA),
                  closeAll tyCtx.size (Expr.letE _v _b))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_fix_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  -- ι ⊑ _ : unfoldIotaL fallback.
  -- Same engine shape as unfoldFixL but with iota.
  | .iota _annA _bodyA, .bvar _k =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.iota _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.iota _annA _bodyA, Expr.bvar _k) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.iota _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.bvar _k) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.bvar _k)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.iota _annA _bodyA, Expr.bvar _k) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.iota _annA _bodyA),
                  closeAll tyCtx.size (Expr.bvar _k))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_iota_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .iota _annA _bodyA, .app _f _v =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.iota _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.iota _annA _bodyA, Expr.app _f _v) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.iota _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.app _f _v) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.app _f _v)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.iota _annA _bodyA, Expr.app _f _v) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.iota _annA _bodyA),
                  closeAll tyCtx.size (Expr.app _f _v))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_iota_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .iota _annA _bodyA, .lam _domB _bodyB =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.iota _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.iota _annA _bodyA, Expr.lam _domB _bodyB) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.iota _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.lam _domB _bodyB) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.lam _domB _bodyB)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.iota _annA _bodyA, Expr.lam _domB _bodyB) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.iota _annA _bodyA),
                  closeAll tyCtx.size (Expr.lam _domB _bodyB))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_iota_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .iota _annA _bodyA, .asc _t _ty =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.iota _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.iota _annA _bodyA, Expr.asc _t _ty) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.iota _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.asc _t _ty) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.asc _t _ty)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.iota _annA _bodyA, Expr.asc _t _ty) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.iota _annA _bodyA),
                  closeAll tyCtx.size (Expr.asc _t _ty))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_iota_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  | .iota _annA _bodyA, .letE _v _b =>
    have hclA_ann : _annA.closedAtLvl 0 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.1
    have hclA_body : _bodyA.closedAtLvl 1 = true := by
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at _ha_cl
      exact _ha_cl.2
    have hlvA_ann : _annA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.1
    have hlvA_body : _bodyA.lvarLT tyCtx.size = true := by
      simp only [Expr.lvarLT, Bool.and_eq_true] at _ha_lv
      exact _ha_lv.2
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp only at _h
    split at _h
    · rename_i a' h_eval
      by_cases haa : a' == Expr.iota _annA _bodyA
      · simp only [haa, ↓reduceIte] at _h
        cases _h
      · simp only [haa, Bool.false_eq_true, ↓reduceIte] at _h
        have h_seen'_wf : ∀ p ∈
            (Expr.iota _annA _bodyA, Expr.letE _v _b) :: seen,
            p.1.closedAtLvl 0 = true ∧
            p.1.lvarLT tyCtx.size = true ∧
            p.2.closedAtLvl 0 = true ∧
            p.2.lvarLT tyCtx.size = true := by
          intro p hp
          rcases List.mem_cons.mp hp with heq | hin
          · subst heq
            exact ⟨_ha_cl, _ha_lv, _hb_cl, _hb_lv⟩
          · exact _hseen_wf p hin
        have h_substL_cl :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).closedAtLvl 0
              = true :=
          SubstEval.substL_closedAtLvl hclA_body _ha_cl
        have h_substL_lv :
            (SubstEval.substL _bodyA 0 (Expr.iota _annA _bodyA)).lvarLT
              tyCtx.size = true :=
          substL_lvarLT _bodyA 0 tyCtx.size (Expr.iota _annA _bodyA)
            hlvA_body _ha_cl _ha_lv
        have h_a'_cl : a'.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl h_substL_cl h_eval
        have h_a'_lv : a'.lvarLT tyCtx.size = true :=
          evalSubst_lvarLT h_substL_cl h_substL_lv h_eval
        have ih_body :
            Subtype'
                (liftSeenList tyCtx.size
                  ((Expr.iota _annA _bodyA, Expr.letE _v _b) :: seen))
                (tyCtxToCtx tyCtx)
                (closeAll tyCtx.size a')
                (closeAll tyCtx.size (Expr.letE _v _b)) :=
          _ih h_seen'_wf h_a'_cl h_a'_lv _hb_cl _hb_lv _h
        have h_seen_unfold :
            liftSeenList tyCtx.size
                ((Expr.iota _annA _bodyA, Expr.letE _v _b) :: seen)
              = ((tyCtxToCtx tyCtx).length,
                  closeAll tyCtx.size (Expr.iota _annA _bodyA),
                  closeAll tyCtx.size (Expr.letE _v _b))
                :: liftSeenList tyCtx.size seen := by
          simp only [liftSeenList, List.map_cons, tyCtxToCtx_length]
        rw [h_seen_unfold] at ih_body
        exact unfold_iota_L_arm h_eval hclA_body hlvA_body
          hclA_ann hlvA_ann ih_body
    · cases _h
  -- Neutral arms (LHS ∈ {bvar, app}, RHS ∈ {bvar, app}, plus all
  -- non-neutral RHS shapes for non-neutral LHS where the engine
  -- catch-all kicks in).
  -- Spine bvar-bvar: closes via `arm_spine_bvar_bvar_compose`.  Engine
  -- `_, _` catch-all does `subCheckSpine` then (on failure)
  -- `neutralAscent`.  The clean path: spine returns `.ok true` iff
  -- `k1 == k2 && isLevelIdx k1`.  In that case the closed terms are
  -- equal and `refl` closes.  The neutralAscent fallback walls on
  -- the lvar-via-tyCtx ascent (existing CloseAll wall).
  | .bvar k1, .bvar k2 =>
    by_cases hkk : k1 == k2
    · have heq' : k1 = k2 := by simpa using hkk
      subst heq'
      exact .refl _
    · -- k1 ≠ k2 ⟹ engine spine returns false ⟹ neutralAscent.
      -- This is the real neutral-ascent fallback wall.
      sorry
  -- Spine bvar-app: spine compare returns false on shape mismatch;
  -- engine then falls to `neutralAscent`.
  | .bvar _k, .app _f _v => sorry
  -- Spine app-bvar: same.
  | .app _f _v, .bvar _k => sorry
  -- Spine app-app: closes via `arm_spine_app_app_compose`.
  | .app _f1 _v1, .app _f2 _v2 => sorry
  -- Remaining catch-all shapes where engine returns `.ok false`
  -- (vacuous from `_h`):  one-sided neutrals + non-neutral RHS,
  -- type-on-LHS, etc.  We sorry these — they're all unreachable
  -- under `_h : ... = .ok true` but extracting the contradiction
  -- requires unfolding `subCheckSubstMatch.eq_def` and reasoning
  -- about the catch-all branch.
  | .bvar _k, .bot => sorry
  | .bvar _k, .asc _t _ty => sorry
  | .bvar _k, .letE _v _b => sorry
  | .app _f _v, .bot => sorry
  | .app _f _v, .asc _t _ty => sorry
  | .app _f _v, .letE _v' _b => sorry
  -- These arms hit the engine's catch-all (`_, _ =>` with
  -- `isNeutral a && isNeutral b` — false here since `.lam`/`.type`
  -- are not neutral).  Engine returns `.ok false`, so `_h` is
  -- contradictory; discharging requires unfolding through the
  -- catch-all guard.
  -- `.lam, *` (catch-all): `.lam` is not neutral, so engine returns
  -- `.ok false`, contradicting `_h`.
  | .lam _domA _bodyA, .bvar _k =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .lam _domA _bodyA, .app _f _v =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .lam _domA _bodyA, .bot =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .lam _domA _bodyA, .asc _t _ty =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .lam _domA _bodyA, .letE _v _b =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .bvar _k =>
    -- Engine takes the catch-all `_, _` arm.  `.type` is not neutral,
    -- so `isNeutral a && isNeutral b` and `isNeutral a` are both
    -- false; engine returns `.ok false`, contradicting `_h`.
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .app _f _v =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .lam _domB _bodyB =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .bot =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .asc _t _ty =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .type, .letE _v _b =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  -- LHS `.asc` / `.letE`: not neutral; engine catch-all returns
  -- `.ok false`.  In a fully-reduced WHNF setting these never appear,
  -- but discharging vacuously is sound regardless.  We dispatch on the
  -- RHS shape to fully reduce the engine's match.
  | .asc _t _ty, .bvar _k =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .asc _t _ty, .app _f _v =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .asc _t _ty, .lam _domB _bodyB =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .asc _t _ty, .bot =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .asc _t _ty, .asc _t' _ty' =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .asc _t _ty, .letE _v _b =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .bvar _k =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .app _f _v' =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .lam _domB _bodyB =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .bot =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .asc _t _ty =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .letE _v _b, .letE _v' _b' =>
    rw [SubstEval.subCheckSubstMatch.eq_def] at _h
    simp [SubstEval.isNeutral] at _h
  | .iota _annA _bodyA, .bot => sorry
  | .fix _annA _bodyA, .bot => sorry
  -- Cross-shape combinations missed above:
  -- iota-fix: engine takes ι ⊑ _ (unfoldIotaL) arm.
  | .iota _annA _bodyA, .fix _ann _bodyB => sorry
  -- type as LHS with iota/fix RHS: engine returns false.
  | .type, .iota _ann _bodyB => sorry
  | .type, .fix _ann _bodyB => sorry
  -- bvar/app LHS with .lam RHS: engine returns false (no arm matches).
  | .bvar _k, .lam _domB _bodyB => sorry
  | .app _f _v, .lam _domB _bodyB => sorry

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
    (hseen_wf : ∀ p ∈ seen,
      p.1.closedAtLvl 0 = true ∧ p.1.lvarLT tyCtx.size = true ∧
      p.2.closedAtLvl 0 = true ∧ p.2.lvarLT tyCtx.size = true)
    (ha_cl : a.closedAtLvl 0 = true) (ha_lv : a.lvarLT tyCtx.size = true)
    (hb_cl : b.closedAtLvl 0 = true) (hb_lv : b.lvarLT tyCtx.size = true)
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
    -- The closeAll-evalSubst bridge is now closed via
    -- `closeAll_evalSubst_subtype_strong` using the `closedAtLvl 0` /
    -- `lvarLT tyCtx.size` preconditions threaded through `subCheckSubst_sound`.
    -- These preconditions hold for terms produced by a `synth`-validated
    -- pipeline (closedness invariant from typechecking).
    have eval_bridge_a :
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size a) (closeAll tyCtx.size a') ∧
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size a') (closeAll tyCtx.size a) :=
      closeAll_evalSubst_subtype_strong ha_cl ha_lv _h_a
    have eval_bridge_b :
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size b) (closeAll tyCtx.size b') ∧
        Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
          (closeAll tyCtx.size b') (closeAll tyCtx.size b) :=
      closeAll_evalSubst_subtype_strong hb_cl hb_lv _h_b
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
      · -- (a', b') matches some entry in seen.  Under Design A,
        -- `liftSeenList tyCtx.size seen` contains
        -- `(tyCtx.size, closeAll tyCtx.size av, closeAll tyCtx.size bv)`
        -- for each `(av, bv) ∈ seen`.  Since `a' = av` and `b' = bv`,
        -- the goal closes via `Subtype'.hyp_here`.
        rw [List.any_eq_true] at hany
        obtain ⟨⟨av, bv⟩, hin, hmatch⟩ := hany
        have ha_eq : a' = av := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
          exact hmatch.1
        have hb_eq : b' = bv := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
          exact hmatch.2
        -- Goal: `Subtype' (liftSeenList tyCtx.size seen) (tyCtxToCtx tyCtx)
        --                  (closeAll tyCtx.size a') (closeAll tyCtx.size b')`.
        rw [ha_eq, hb_eq]
        have hin_lifted :
            ((tyCtxToCtx tyCtx).length, closeAll tyCtx.size av,
                closeAll tyCtx.size bv)
              ∈ liftSeenList tyCtx.size seen := by
          rw [tyCtxToCtx_length]
          simp only [liftSeenList, List.mem_map]
          exact ⟨(av, bv), hin, rfl⟩
        exact Subtype'.hyp_here hin_lifted
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
          -- Derive a' / b' invariants from the originals via evalSubst
          -- preservation lemmas (`evalSubst_closedAtLvl` and
          -- `evalSubst_lvarLT`).  These feed the dispatch arms that
          -- need component-wise closedness for `subCheckSubst_arm_*`.
          have ha'_cl : a'.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl ha_cl _h_a
          have ha'_lv : a'.lvarLT tyCtx.size = true :=
            evalSubst_lvarLT ha_cl ha_lv _h_a
          have hb'_cl : b'.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl hb_cl _h_b
          have hb'_lv : b'.lvarLT tyCtx.size = true :=
            evalSubst_lvarLT hb_cl hb_lv _h_b
          exact subCheckSubstMatch_dispatch
            (fun {_tyCtx'} {_seen'} {_x _y} hsw' hx_cl hx_lv hy_cl hy_lv hx =>
              ih hsw' hx_cl hx_lv hy_cl hy_lv hx)
            hseen_wf ha'_cl ha'_lv hb'_cl hb'_lv h

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
  -- conclusion via `subCheckSubst_sound`.  Sorried because:
  --
  -- Chain:
  --   1.  `evalSubst_equiv` (closed at depth 0; see EvalSubstEquiv.lean)
  --       gives `Subtype' [] [] a.whnf x' ∧ Subtype' [] [] x' a.whnf`
  --       provided `a.whnf.closedAt 0 = true`.  Same for `b`.
  --   2.  `subCheckSubst_sound` on the inner call gives
  --         `Subtype' [] [] (closeAll 0 x') (closeAll 0 y')`,
  --       which by `closeAll_zero` is `Subtype' [] [] x' y'`.
  --   3.  Trans-chain: `a.whnf ⊑ x' ⊑ y' ⊑ b.whnf`.
  --
  -- The remaining gap is the **closedness invariant on WTValue**:
  -- `WTValue.whnf.closedAt 0 = true` is true of all values produced
  -- by `Och.synth` (which now validates closedAt at entry; closedness
  -- preservation through `synthCore`'s arms is provable by induction
  -- but unproven), but not currently a structural invariant on the
  -- WTValue type.  Two paths:
  --   (a) Add `whnf_closedAt` field to `WTValue` (touches `API.lean`).
  --   (b) Prove `Och.synth e fuel = .ok v → v.whnf.closedAt 0` and
  --       hoist as hypothesis on `subCheck_sound` callers.
  --
  -- Step 2 also remains walled (`subCheckSubst_sound` is sorry'd
  -- internally, transitively on the dispatch and v2 fallback bridges).
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

-- Hyp arm (engine's seen-list short-circuit) is handled inline
-- in `subCheckSubst_sound`'s `by_cases hany : seen.any …` branch
-- (the seen_coherence wall lives there).  No standalone arm-
-- package is needed; the previously-stubbed `arm_hyp_compose`
-- was unused and conflated raw seen entries with their closeAll-
-- translated counterparts in the goal.

/-! ### Spine arms (neutral case)

The neutral arm of `subCheckSubstMatch` calls `subCheckSpine`
followed (on failure) by `neutralAscent`.  The spine arms close
declaratively via `Subtype'.refl` (head equality) and `Subtype'.app_cong`
(spine recursion); the neutral-ascent arm uses
`Subtype'_lvar_via_tyCtx` (level-var ascent, broken by
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
