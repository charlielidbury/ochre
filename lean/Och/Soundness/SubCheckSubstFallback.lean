import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubtypeSteps
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural

/-!
# Fallback arms of `subCheckSubst_sound` (sidestep attempt)

This module attempts the **sidestep** strategy from `docs/ideas/
proposalA-wall-v2.md` for the four fallback arms of the engine's
`subCheckSubstMatch`:

  * **iota_intro** — `_, .iota ann bodyB` (LHS non-iota, RHS iota).
  * **unfold-Fix-R** — `_, .fix _ bodyB` (LHS non-fix, RHS fix).
  * **unfold-Fix-L** — `.fix _ bodyA, _` (LHS fix, RHS non-fix).
  * **unfold-Iota-L** — `.iota _ bodyA, _` (LHS iota, RHS non-iota).

The sidestep **idea**: instead of matching the engine's syntactic
`substL bodyB 0 a` (which requires `closeAllAt_substL` for arbitrary
substituees — provably false in general — see v2 wall), reason about
the engine's substitution as a **β-reduction step on which `Subtype'`
is closed by hypothesis**.  Concretely: the engine's
`evalSubst (substL bodyB 0 a)` produces a value `bodyB''` whose
declarative subtype-equivalence to `(bodyB.subst 0 a)` (via the
`unfold_iota_R`/`unfold_fix_R` etc. step lemmas in
`Soundness/SubtypeSteps.lean`) chains with the IH to give us the
parent.

## Scope and current status

Each arm-lemma below takes:
  * IH on the engine's annotation/check sub-call (already in
    closed form via `closeAll`),
  * IH on the engine's **post-substitution-and-eval** sub-call (in
    closed form on `closeAll d bodyB''`),
  * a **substitution bridge** hypothesis that asserts
    `Subtype' (closeAll d bodyB'') (...closeAll d (body.subst 0 a)...)`
    — which is what the v2 wall blocks.

The arm-lemma proper closes by `iota_intro` / `unfold_*_R` /
`unfold_*_L` plus `Subtype'.trans` with the substitution bridge.

The substitution bridges are **stated** as bidirectional `Subtype'`
equivalences (not raw `Eq`); this is the sidestep contract.  Closing
them is what the v2 wall blocks; we document each bridge precisely
so the wall is machine-checkable.

## Structure

  * `iota_intro_arm` — fallback arm-lemma (consumes substitution bridge).
  * `unfold_fix_R_arm` — fallback arm-lemma (consumes substitution bridge).
  * `unfold_fix_L_arm` — fallback arm-lemma (consumes substitution bridge).
  * `unfold_iota_L_arm` — fallback arm-lemma (consumes substitution bridge).
  * `iota_intro_substBridge_WALL` etc. — the substitution bridges,
    `sorry`'d.

This gives us composable progress: the **arm structure** is
proven; the wall is localised to the substitution bridges.
-/

namespace Och.Soundness

open SubstEval

/-! ## Helper: `closeAllAt c 0` is the identity.

At depth 0, `closeAll` cannot match any level-var (`lvl < 0` is
never true), so the translation is a no-op.  This lets us
*specialise* the substitution bridges to the d=0 (top-level)
regime, where the v2 wall does not bite. -/

theorem closeAllAt_zero (c : Nat) (e : Expr) : closeAllAt c 0 e = e := by
  induction e generalizing c with
  | bvar k =>
    simp only [closeAllAt]
    by_cases h : k ≥ levelOffset
    · simp only [h, ↓reduceIte]
      have : ¬ (k - levelOffset) < 0 := by omega
      simp [this]
    · simp [h]
  | type => rfl
  | bot => rfl
  | lam _ _ ih_dom ih_body => simp [closeAllAt, ih_dom, ih_body]
  | app _ _ ih_f ih_a => simp [closeAllAt, ih_f, ih_a]
  | asc _ _ ih_t ih_y => simp [closeAllAt, ih_t, ih_y]
  | iota _ _ ih_ann ih_body => simp [closeAllAt, ih_ann, ih_body]
  | fix _ _ ih_ann ih_body => simp [closeAllAt, ih_ann, ih_body]
  | letE _ _ ih_val ih_body => simp [closeAllAt, ih_val, ih_body]

theorem closeAll_zero (e : Expr) : closeAll 0 e = e :=
  closeAllAt_zero 0 e

/-! ## Substitution bridges — the v2 wall localised

Each bridge asserts that the engine's substituted-and-evalSubst'd
body is `Subtype'`-equivalent to the declarative-style
`body.subst 0 self`.  In closed form (under `closeAll d`), the
bridge is

```
Subtype' S Γ
  (closeAll d (engineResult))   -- output of `evalSubst (substL body 0 self)`
  ((closeAllAt 1 d body).subst 0 (closeAll d self))   -- declarative form
```

(plus the reverse direction — the bidirectional contract).

Closing this requires three sub-steps:
  1. `evalSubst`'s reduction is captured by `unfold_iota_R` /
     `unfold_fix_R` / `beta_R` etc. — this part is OK in principle.
  2. `substL body 0 self` translates under `closeAll` to
     `(closeAllAt 1 d body).subst 0 (closeAll d self)` — this is the
     **v2 wall** (`closeAllAt_substL` for arbitrary substituees).
  3. Connecting the two via `Subtype'.trans`.

Step 2 is the open obstacle.  We `sorry` each bridge and tag with
the specific wall instance. -/

/-! ## Substitution bridges — derivation via `closeAll_substL_subst`
    plus the consolidated `closeAll_evalSubst_subtype` wall.

The four bridges below all share a common shape:
1. The engine performs `bodyB' := substL body 0 self`.
2. evalSubst reduces it to `bodyB''`.
3. We need to relate `bodyB''` to `body.subst 0 self` in closed form.

The two-step derivation is:
* By `closeAll_substL_subst`: `closeAll d bodyB' = (closeAllAt 1 d body).subst 0 (closeAll d self)`.
* By `closeAll_evalSubst_subtype` (consolidated wall): `Subtype'`
  bidirectionally relates `closeAll d bodyB'` and `closeAll d bodyB''`.

Each bridge takes the engine's evalSubst step plus closedness/lvarLT
preconditions sufficient to invoke `closeAll_substL_subst`. -/

/-- Substitution bridge for `iota_intro` fallback.

    Engine: `bodyB' = substL bodyB 0 a`, `bodyB'' = evalSubst bodyB'`. -/
theorem iota_intro_substBridge_WALL
    {S : Seen} {Γ : Ctx} {d : Nat}
    {a bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 a) = .ok bodyB'')
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT d = true)
    (ha_cl : a.closedAtLvl 0 = true)
    (ha_lv : a.lvarLT d = true) :
    Subtype' S Γ
      (closeAll d bodyB'')
      ((closeAllAt 1 d bodyB).subst 0 (closeAll d a)) := by
  -- Bridge: closeAll d (substL bodyB 0 a) = (closeAllAt 1 d bodyB).subst 0 (closeAll d a).
  have heq : closeAll d (SubstEval.substL bodyB 0 a)
           = (closeAllAt 1 d bodyB).subst 0 (closeAll d a) :=
    closeAll_substL_subst bodyB d a hbody_cl hbody_lv ha_cl ha_lv
  rw [← heq]
  -- Now goal: Subtype' (closeAll d bodyB'') (closeAll d (substL bodyB 0 a)).
  -- Use closeAll_evalSubst_subtype on h_eval (in reverse direction).
  exact (closeAll_evalSubst_subtype h_eval).2

/-- Substitution bridge for `unfold_fix_R` fallback. -/
theorem unfold_fix_R_substBridge_WALL
    {S : Seen} {Γ : Ctx} {d : Nat}
    {ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 (.fix ann bodyB)) = .ok bodyB'')
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true) :
    Subtype' S Γ
      (closeAll d bodyB'')
      ((closeAllAt 1 d bodyB).subst 0 (closeAll d (.fix ann bodyB))) := by
  have hself_cl : (Expr.fix ann bodyB).closedAtLvl 0 = true := by
    simp [Expr.closedAtLvl, hann_cl, hbody_cl]
  have hself_lv : (Expr.fix ann bodyB).lvarLT d = true := by
    simp [Expr.lvarLT, hann_lv, hbody_lv]
  have heq : closeAll d (SubstEval.substL bodyB 0 (.fix ann bodyB))
           = (closeAllAt 1 d bodyB).subst 0 (closeAll d (.fix ann bodyB)) :=
    closeAll_substL_subst bodyB d (.fix ann bodyB)
      hbody_cl hbody_lv hself_cl hself_lv
  rw [← heq]
  exact (closeAll_evalSubst_subtype h_eval).2

/-- Substitution bridge for `unfold_fix_L` fallback. -/
theorem unfold_fix_L_substBridge_WALL
    {S : Seen} {Γ : Ctx} {d : Nat}
    {ann bodyA a' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.fix ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true) :
    Subtype' S Γ
      ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.fix ann bodyA)))
      (closeAll d a') := by
  have hself_cl : (Expr.fix ann bodyA).closedAtLvl 0 = true := by
    simp [Expr.closedAtLvl, hann_cl, hbody_cl]
  have hself_lv : (Expr.fix ann bodyA).lvarLT d = true := by
    simp [Expr.lvarLT, hann_lv, hbody_lv]
  have heq : closeAll d (SubstEval.substL bodyA 0 (.fix ann bodyA))
           = (closeAllAt 1 d bodyA).subst 0 (closeAll d (.fix ann bodyA)) :=
    closeAll_substL_subst bodyA d (.fix ann bodyA)
      hbody_cl hbody_lv hself_cl hself_lv
  rw [← heq]
  -- Need: Subtype' (closeAll d (substL ...)) (closeAll d a').
  exact (closeAll_evalSubst_subtype h_eval).1

/-- Substitution bridge for `unfold_iota_L` fallback. -/
theorem unfold_iota_L_substBridge_WALL
    {S : Seen} {Γ : Ctx} {d : Nat}
    {ann bodyA a' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.iota ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true) :
    Subtype' S Γ
      ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.iota ann bodyA)))
      (closeAll d a') := by
  have hself_cl : (Expr.iota ann bodyA).closedAtLvl 0 = true := by
    simp [Expr.closedAtLvl, hann_cl, hbody_cl]
  have hself_lv : (Expr.iota ann bodyA).lvarLT d = true := by
    simp [Expr.lvarLT, hann_lv, hbody_lv]
  have heq : closeAll d (SubstEval.substL bodyA 0 (.iota ann bodyA))
           = (closeAllAt 1 d bodyA).subst 0 (closeAll d (.iota ann bodyA)) :=
    closeAll_substL_subst bodyA d (.iota ann bodyA)
      hbody_cl hbody_lv hself_cl hself_lv
  rw [← heq]
  exact (closeAll_evalSubst_subtype h_eval).1

/-! ## Arm lemmas

Each arm consumes the engine's IH-shape and the substitution bridge,
produces the parent `Subtype'`. -/

/-- **iota_intro** fallback arm (engine: `_, .iota ann bodyB`).

    The IH from the engine's first sub-call gives us
    `Subtype' a ann` (in closed form, with the seen-set extended).
    The IH from the second sub-call gives us
    `Subtype' a bodyB''` where `bodyB''` is the engine's evalSubst
    of `substL bodyB 0 a`.

    The substitution bridge converts `Subtype' a bodyB''` to
    `Subtype' a (bodyB.subst 0 a)` (in closed form), which feeds
    directly into `Subtype'.iota_intro`. -/
theorem iota_intro_arm
    {S : Seen} {Γ : Ctx} {d : Nat}
    {a ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 a) = .ok bodyB'')
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT d = true)
    (ha_cl : a.closedAtLvl 0 = true)
    (ha_lv : a.lvarLT d = true)
    (ih_ann : Subtype'
        ((Γ.length, closeAll d a, closeAll d (.iota ann bodyB)) :: S)
        Γ (closeAll d a) (closeAll d ann))
    (ih_body : Subtype'
        ((Γ.length, closeAll d a, closeAll d (.iota ann bodyB)) :: S)
        Γ (closeAll d a) (closeAll d bodyB'')) :
    Subtype' S Γ (closeAll d a) (closeAll d (.iota ann bodyB)) := by
  -- closeAll d (.iota ann bodyB) = .iota (closeAllAt 0 d ann) (closeAllAt 1 d bodyB)
  show Subtype' S Γ (closeAll d a)
    (.iota (closeAllAt 0 d ann) (closeAllAt 1 d bodyB))
  -- Apply iota_intro: needs (a ⊑ ann) and (a ⊑ bodyB[a/0]).
  apply Subtype'.iota_intro
  · -- ann case: from ih_ann.  closeAllAt 0 d = closeAll d (definitional).
    show Subtype' _ Γ (closeAll d a) (closeAll d ann)
    exact ih_ann
  · -- body case: ih_body gives a ⊑ closeAll d bodyB''.
    -- Bridge to a ⊑ (closeAllAt 1 d bodyB).subst 0 (closeAll d a) via trans.
    have bridge : Subtype'
        ((Γ.length, closeAll d a, closeAll d (.iota ann bodyB)) :: S)
        Γ (closeAll d bodyB'')
        ((closeAllAt 1 d bodyB).subst 0 (closeAll d a)) :=
      iota_intro_substBridge_WALL h_eval hbody_cl hbody_lv ha_cl ha_lv
    exact ih_body.trans bridge

/-- **unfold_fix_R** fallback arm (engine: `_, .fix ann bodyB`).

    The IH gives us `Subtype' a bodyB''` where `bodyB'' = evalSubst (substL bodyB 0 (.fix ann bodyB))`.
    We need `Subtype' a (.fix ann bodyB)`.

    Apply `Subtype'.unfold_fix_R`: it needs
    `Subtype' a (bodyB.subst 0 (.fix ann bodyB))`, with the seen-set
    extended by `(a, .fix ann bodyB)`. -/
theorem unfold_fix_R_arm
    {S : Seen} {Γ : Ctx} {d : Nat}
    {a ann bodyB bodyB'' : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyB 0 (.fix ann bodyB)) = .ok bodyB'')
    (hbody_cl : bodyB.closedAtLvl 1 = true)
    (hbody_lv : bodyB.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true)
    (ih_body : Subtype'
        ((Γ.length, closeAll d a, closeAll d (.fix ann bodyB)) :: S)
        Γ (closeAll d a) (closeAll d bodyB'')) :
    Subtype' S Γ (closeAll d a) (closeAll d (.fix ann bodyB)) := by
  show Subtype' S Γ (closeAll d a)
    (.fix (closeAllAt 0 d ann) (closeAllAt 1 d bodyB))
  apply Subtype'.unfold_fix_R
  have bridge : Subtype'
      ((Γ.length, closeAll d a, closeAll d (.fix ann bodyB)) :: S)
      Γ (closeAll d bodyB'')
      ((closeAllAt 1 d bodyB).subst 0 (closeAll d (.fix ann bodyB))) :=
    unfold_fix_R_substBridge_WALL h_eval hbody_cl hbody_lv hann_cl hann_lv
  show Subtype' _ Γ (closeAll d a)
    ((closeAllAt 1 d bodyB).subst 0 (closeAll d (.fix ann bodyB)))
  exact ih_body.trans bridge

/-- **unfold_fix_L** fallback arm (engine: `.fix ann bodyA, _`).

    Engine: unfolds `bodyA[fix/self]`, evals to `a'`, recurses on
    `subCheckSubst a' b`.  IH: `Subtype' (closeAll d a') (closeAll d b)`.
    We need `Subtype' (closeAll d (.fix ann bodyA)) (closeAll d b)`.

    Apply `Subtype'.unfold_fix_L`: it needs
    `Subtype' (bodyA.subst 0 (.fix ann bodyA)) b`. -/
theorem unfold_fix_L_arm
    {S : Seen} {Γ : Ctx} {d : Nat}
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.fix ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true)
    (ih_body : Subtype'
        ((Γ.length, closeAll d (.fix ann bodyA), closeAll d b) :: S)
        Γ (closeAll d a') (closeAll d b)) :
    Subtype' S Γ (closeAll d (.fix ann bodyA)) (closeAll d b) := by
  show Subtype' S Γ
    (.fix (closeAllAt 0 d ann) (closeAllAt 1 d bodyA))
    (closeAll d b)
  apply Subtype'.unfold_fix_L
  show Subtype' _ Γ
    ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.fix ann bodyA)))
    (closeAll d b)
  have bridge : Subtype'
      ((Γ.length, closeAll d (.fix ann bodyA), closeAll d b) :: S)
      Γ
      ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.fix ann bodyA)))
      (closeAll d a') :=
    unfold_fix_L_substBridge_WALL h_eval hbody_cl hbody_lv hann_cl hann_lv
  exact bridge.trans ih_body

/-- **unfold_iota_L** fallback arm (engine: `.iota ann bodyA, _`).

    Engine: unfolds `bodyA[iota/self]`, evals to `a'`, recurses on
    `subCheckSubst a' b`.  IH: `Subtype' (closeAll d a') (closeAll d b)`.
    We need `Subtype' (closeAll d (.iota ann bodyA)) (closeAll d b)`.

    Apply `Subtype'.unfold_iota_L`. -/
theorem unfold_iota_L_arm
    {S : Seen} {Γ : Ctx} {d : Nat}
    {ann bodyA a' b : Expr}
    (h_eval : SubstEval.evalSubst (SubstEval.unfBound + 1) SubstEval.unfBound
        (SubstEval.substL bodyA 0 (.iota ann bodyA)) = .ok a')
    (hbody_cl : bodyA.closedAtLvl 1 = true)
    (hbody_lv : bodyA.lvarLT d = true)
    (hann_cl : ann.closedAtLvl 0 = true)
    (hann_lv : ann.lvarLT d = true)
    (ih_body : Subtype'
        ((Γ.length, closeAll d (.iota ann bodyA), closeAll d b) :: S)
        Γ (closeAll d a') (closeAll d b)) :
    Subtype' S Γ (closeAll d (.iota ann bodyA)) (closeAll d b) := by
  show Subtype' S Γ
    (.iota (closeAllAt 0 d ann) (closeAllAt 1 d bodyA))
    (closeAll d b)
  apply Subtype'.unfold_iota_L
  show Subtype' _ Γ
    ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.iota ann bodyA)))
    (closeAll d b)
  have bridge : Subtype'
      ((Γ.length, closeAll d (.iota ann bodyA), closeAll d b) :: S)
      Γ
      ((closeAllAt 1 d bodyA).subst 0 (closeAll d (.iota ann bodyA)))
      (closeAll d a') :=
    unfold_iota_L_substBridge_WALL h_eval hbody_cl hbody_lv hann_cl hann_lv
  exact bridge.trans ih_body

/-! ## Sidestep status

Each arm-lemma above is **structurally complete** modulo the
substitution bridge sorry.  The structure is:

  1. Apply the corresponding declarative rule (`iota_intro`,
     `unfold_*_R`, `unfold_*_L`).
  2. Use the substitution bridge to convert the IH's closed form
     (which uses the engine's `substL+evalSubst` shape) into the
     declarative form (`(closeAllAt 1 d body).subst 0 (closeAll d self)`).
  3. Compose with `Subtype'.trans`.

The substitution bridges are walled by the v2 wall (closeAll-substL
commutation for arbitrary substituees, see
`docs/ideas/proposalA-wall-v2.md`).

### Why the sidestep does NOT eliminate the wall as advertised

The original sidestep recommendation was to "prove iota/unfoldFix
arms via β-reduction bisimulation rather than syntactic
`closeAllAt_substL` commutation".  The plan was to use an
`evalSubst_equiv` analog of `concEval_equiv` to bridge the engine's
substitution result back to the source term.

But the **β-reduction bisimulation only handles the `evalSubst` step**;
it does NOT bridge the `substL → Expr.subst` gap, which is needed
to translate `closeAll d (substL body 0 a)` into
`(closeAllAt 1 d body).subst 0 (closeAll d a)`.

Concretely: even with `evalSubst_equiv`, we'd still need

    closeAll d (substL bodyB 0 a) ≡_{Subtype'}
      (closeAllAt 1 d bodyB).subst 0 (closeAll d a)

which is the v2 wall on closeAll-substL commutation, restated
without the eval step.  The wall is **substrate-arithmetic**,
not eval-related.

### Where the sidestep WOULD work

At **depth 0** (no level-vars, top-level subCheck_sound), `closeAll 0`
is the identity (`closeAllAt_zero` above), and `substL = Expr.subst`
(via `substL_eq_subst_no_levelvars`).  In that regime the
substitution bridge reduces to the eval-step bridge alone, which is
just the (yet-unwritten) `evalSubst_equiv` analog.

A future agent could:
  1. Write `evalSubst_equiv` (mirror of `concEval_equiv` but for
     evalSubst — independently provable).
  2. Specialise these arm-lemmas to d=0.
  3. Use them to discharge `subCheck_sound`'s depth-0 fallback case.

This still leaves the recursive (depth>0) case as the standing
wall, since structural arms (lam, iota-iota, fix-fix) descend
through binders and create level-vars before reaching the
fallback arms again. -/

/-! ## Substrate gap to evalSubst_equiv

The intended sidestep would prove:

```
theorem evalSubst_equiv {fuel unf : Nat} {e e' : Expr}
    (hcl : e.closedAtLvl 0 = true)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' [] [] e' e ∧ Subtype' [] [] e e'
```

mirroring `concEval_equiv`.  This piece is **independently provable**
— each evalSubst arm has a corresponding declarative step rule (β,
unfold_iota, unfold_fix, letE, asc, refl on canonicals).  Adding it
would not by itself close the fallback arms, since the substL→subst
gap remains, but it would simplify the bridge proofs.

We do NOT include `evalSubst_equiv` here — it's an independent
piece of work.  See `Soundness/ConcEvalPreservation.lean` for the
concEval template. -/

end Och.Soundness
