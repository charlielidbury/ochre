import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubCheckSubstNeutral

/-!
# C2/C3/C4: structural arms of `subCheckSubst_sound`

This module proves the **structural arms** of the engine soundness
theorem `subCheckSubst_sound`:

  * **C2 (lam-lam)**: `subCheckSubst fuel tyCtx seen (.lam domA bodyA)
    (.lam domB bodyB) = .ok true` ⟹ `Subtype'.lam` derivation in
    closed form.
  * **C3 (iota-iota structural)**: same for the `.iota,.iota`
    structural sub-arm (before the iotaIntro fallback) ⟹
    `Subtype'.iota_cong`.
  * **C4 (fix-fix structural)**: same for `.fix,.fix` structural ⟹
    `Subtype'.fix_cong`.

## Strategy

These three arms share an identical *structural* shape: each engine
arm calls `subCheckSubst` on (1) the annotation/domain (with appropriate
variance) and (2) the body opened under a fresh level-var, with `tyCtx`
extended.  After translation by `closeAll`, the engine's sub-results
correspond to declarative `Subtype'` derivations on the closed sub-terms.

The key bridge is `closeAll_openFresh` (`Soundness/CloseAll.lean`):
it converts the engine's `openFresh body depth` recursive shape into the
structural `closeAllAt 1 depth body` shape that `Subtype'.{lam,iota_cong,
fix_cong}` natively consumes.

## Form of the arm lemmas

We package each arm as a **"cong-from-IH"** lemma, parameterized by the
IH derivations the eventual mutual block will supply.  This is the same
pattern used by `app_cong_from_spine_ih` in `SubCheckSubstNeutral.lean`.
The arm-lemma is purely structural — it constructs the parent
`Subtype'` from the assumed sub-derivations, applying `closeAll_openFresh`
at the binder transition.

## Out of scope (v2 wall)

The fallback arms — iotaIntro (when `.iota,.iota` structural fails),
unfold-Fix-R, unfold-Fix-L, unfold-Iota-L — substitute the *term itself*
(not a level-var) into the body, requiring `closeAllAt_substL` for
arbitrary substituees.  That commutation lemma is provably false as
naively stated and remains a v2 wall (see
`docs/ideas/proposalA-wall-v2.md`).  We do NOT attempt the fallback
arms here.
-/

namespace Och.Soundness

open SubstEval

/-! ## C2: lam-lam structural arm

Engine code (`SubstEval.subCheckSubst` on `.lam, .lam`):
```
let contra ← subCheckSubst fuel tyCtx seen domB domA
if !contra then return false
let bodyA' := openFresh bodyA depth
let bodyB' := openFresh bodyB depth
subCheckSubst fuel (tyCtx.push domB) seen bodyA' bodyB'
```
where `depth = tyCtx.size`.

The two sub-results we receive (from IH, via `closeAll_openFresh` on the
body call) are:
  * `Subtype' S Γ (closeAll d domB) (closeAll d domA)` — contravariant,
  * `Subtype' S' (closeAll d domB :: Γ) (closeAllAt 1 d bodyA)
                                        (closeAllAt 1 d bodyB)`
    — body, in the extended context.

The conclusion is a `.lam` derivation matching `closeAll d (.lam domA
bodyA)` ⊑ `closeAll d (.lam domB bodyB)`.
-/

/-- C2: lam-lam structural arm.  Given IH derivations on the engine's
    contravariant-domain and body-under-fresh sub-calls, build the
    parent `Subtype'.lam` in closed form.

    The IH on the body is stated against `closeAllAt 1 d bodyA/B`
    — the `closeAll_openFresh` image — and against the *translated*
    domain `domB'` lifted into the context.  Callers will use
    `closeAll_openFresh` to discharge the body IH from the engine's
    `openFresh`-shape result.

    No mention of fuel/seen/tyCtx structure: this is the pure
    `Subtype'`-structural step. -/
theorem subCheckSubst_arm_lam_lam_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {domA bodyA domB bodyB : Expr}
    (ih_dom : Subtype' S Γ (closeAll d domB) (closeAll d domA))
    (ih_body : Subtype' S (closeAll d domB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.lam domA bodyA))
      (closeAll d (.lam domB bodyB)) := by
  -- `closeAll d (.lam dom body) = .lam (closeAllAt 0 d dom) (closeAllAt 1 d body)`
  -- and `closeAllAt 0 = closeAll`.
  show Subtype' S Γ
    (.lam (closeAllAt 0 d domA) (closeAllAt 1 d bodyA))
    (.lam (closeAllAt 0 d domB) (closeAllAt 1 d bodyB))
  exact .lam ih_dom ih_body

/-! ## C3: iota-iota structural arm

Engine code (`SubstEval.subCheckSubst` on `.iota, .iota`):
```
let structural := do
  let annOk ← subCheckSubst fuel tyCtx seen' annA annB
  if !annOk then return false
  let bodyA' := openFresh bodyA depth
  let bodyB' := openFresh bodyB depth
  subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
match structural with
| .ok true => .ok true
| _ => ... iotaIntro fallback ...
```
The structural sub-arm is **covariant** on the annotation (in contrast
to `.lam, .lam`'s contravariance) and pushes `annB` (the target
annotation) into `tyCtx`.

We package the structural arm only — the `iotaIntro` fallback hits the
v2 wall.
-/

/-- C3: iota-iota structural arm. -/
theorem subCheckSubst_arm_iota_iota_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.iota annA bodyA))
      (closeAll d (.iota annB bodyB)) := by
  -- `closeAll d (.iota ann body) = .iota (closeAllAt 0 d ann) (closeAllAt 1 d body)`.
  -- `Subtype'.iota_cong` matches the closed shape directly.
  show Subtype' S Γ
    (.iota (closeAllAt 0 d annA) (closeAllAt 1 d bodyA))
    (.iota (closeAllAt 0 d annB) (closeAllAt 1 d bodyB))
  exact .iota_cong ih_ann ih_body

/-! ## C4: fix-fix structural arm

Engine code (`SubstEval.subCheckSubst` on `.fix, .fix`):
```
let structural := do
  let annOk ← subCheckSubst fuel tyCtx seen' annA annB
  if !annOk then return false
  let bodyA' := openFresh bodyA depth
  let bodyB' := openFresh bodyB depth
  subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
match structural with
| .ok true => .ok true
| _ => ... unfold-Fix-R fallback ...
```
Same shape as C3 but with `Subtype'.fix_cong`. -/

theorem subCheckSubst_arm_fix_fix_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.fix annA bodyA))
      (closeAll d (.fix annB bodyB)) := by
  show Subtype' S Γ
    (.fix (closeAllAt 0 d annA) (closeAllAt 1 d bodyA))
    (.fix (closeAllAt 0 d annB) (closeAllAt 1 d bodyB))
  exact .fix_cong ih_ann ih_body

/-! ## Bridge: convert engine `openFresh` IH to structural body IH

When the eventual mutual block invokes IH on the engine's recursive
call `subCheckSubst fuel (tyCtx.push annB) seen' (openFresh bodyA d)
(openFresh bodyB d)`, the IH yields a `Subtype'` derivation on the
*opened* bodies.  The arm lemmas above demand a derivation on
`closeAllAt 1 d bodyA/B` instead.

`closeAll_openFresh` (in `CloseAll.lean`) provides the translation:
```
closeAll (d + 1) (openFreshTop body d) = closeAllAt 1 d body
```
under preconditions:
  * `body.closedAtLvl 1 = true` — only `bvar 0` allowed in body;
  * `body.lvarLT d = true` — every level-var in body has index `< d`.

The lemma below packages the use of `closeAll_openFresh` to convert an
"opened-form" IH into the "closed-form" needed by the arm lemmas. -/

theorem subCheckSubst_body_IH_translate
    {S : Seen} {Γ : Ctx} {d : Nat}
    {bodyA bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT d = true)
    (hlvB : bodyB.lvarLT d = true)
    (h_open : Subtype' S Γ
        (closeAll (d + 1) (SubstEval.openFreshTop bodyA d))
        (closeAll (d + 1) (SubstEval.openFreshTop bodyB d))) :
    Subtype' S Γ (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB) := by
  rw [closeAll_openFresh bodyA d hclA hlvA] at h_open
  rw [closeAll_openFresh bodyB d hclB hlvB] at h_open
  exact h_open

/-! ## Composed arm lemmas

The arm lemmas plus the body translator combine into a single statement
that consumes the engine's actual IH shape (an `openFresh`-form
derivation on the body) and produces the parent `Subtype'`.

These are the cleanest "engine-arm-IH ⟹ Subtype'-parent" packages,
suitable for direct invocation in the mutual block. -/

/-- C2 (lam-lam) composed: takes the engine's openFresh-shaped body IH,
    produces the closed parent. -/
theorem subCheckSubst_arm_lam_lam
    {S : Seen} {Γ : Ctx} {d : Nat}
    {domA bodyA domB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT d = true)
    (hlvB : bodyB.lvarLT d = true)
    (ih_dom : Subtype' S Γ (closeAll d domB) (closeAll d domA))
    (ih_body : Subtype' S (closeAll d domB :: Γ)
        (closeAll (d + 1) (SubstEval.openFreshTop bodyA d))
        (closeAll (d + 1) (SubstEval.openFreshTop bodyB d))) :
    Subtype' S Γ
      (closeAll d (.lam domA bodyA))
      (closeAll d (.lam domB bodyB)) :=
  subCheckSubst_arm_lam_lam_struct ih_dom
    (subCheckSubst_body_IH_translate hclA hclB hlvA hlvB ih_body)

/-- C3 (iota-iota structural) composed. -/
theorem subCheckSubst_arm_iota_iota
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT d = true)
    (hlvB : bodyB.lvarLT d = true)
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAll (d + 1) (SubstEval.openFreshTop bodyA d))
        (closeAll (d + 1) (SubstEval.openFreshTop bodyB d))) :
    Subtype' S Γ
      (closeAll d (.iota annA bodyA))
      (closeAll d (.iota annB bodyB)) :=
  subCheckSubst_arm_iota_iota_struct ih_ann
    (subCheckSubst_body_IH_translate hclA hclB hlvA hlvB ih_body)

/-- C4 (fix-fix structural) composed. -/
theorem subCheckSubst_arm_fix_fix
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (hclA : bodyA.closedAtLvl 1 = true)
    (hclB : bodyB.closedAtLvl 1 = true)
    (hlvA : bodyA.lvarLT d = true)
    (hlvB : bodyB.lvarLT d = true)
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAll (d + 1) (SubstEval.openFreshTop bodyA d))
        (closeAll (d + 1) (SubstEval.openFreshTop bodyB d))) :
    Subtype' S Γ
      (closeAll d (.fix annA bodyA))
      (closeAll d (.fix annB bodyB)) :=
  subCheckSubst_arm_fix_fix_struct ih_ann
    (subCheckSubst_body_IH_translate hclA hclB hlvA hlvB ih_body)

/-! ## Status of the v2-walled fallback arms

These remain unproven (sorry) because they require
`closeAllAt_substL` for arbitrary substituees, which is a v2 wall.
See `docs/ideas/proposalA-wall-v2.md`.

  * **iotaIntro fallback** (when `.iota,.iota` structural fails):
    engine substitutes `a` (the LHS, not a level-var) into bodyB.
    Needs `closeAllAt_substL` for `s = a`.

  * **unfold-Fix-R**: engine substitutes `b` (the RHS) into bodyB,
    where `b = .fix _ _`.  Same wall.

  * **unfold-Fix-L**: engine substitutes `a` into bodyA.  Same wall.

  * **unfold-Iota-L**: engine substitutes `a` into bodyA.  Same wall.

We do NOT introduce sorries here for these arms — they live in the
mutual block, not as standalone lemmas.  The mutual block is in
`Soundness.lean` (top-level `subCheck_sound`); these fallback arms
are still encapsulated as a single `sorry` there.
-/

end Och.Soundness
