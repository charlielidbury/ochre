import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Conjecture8
import Pss.Paper.Aux.Propositions

/-! # `Pss.Paper.Aux.PromotionUnderSubst` — paper Lemmas 29, 30

Mechanizes the "Promotion under substitution" lemma pair from Pasquale &
García-Pérez 2024:

* **Lemma 29** (Promotion under substitution OUTSIDE of covariant
  contexts, paper p. 9:41–42) — for any covariant context `Co`, the
  canonical promotion-under-`Co` derivation
  `Γ, x ≤ t, Γ'; s ⊢ Co[x] →ˢᵘᵇ Co[t]` exists and survives the prefix
  substitution `[x\α]`.
* **Lemma 30** (Promotion under substitution INSIDE of covariant
  contexts, paper p. 9:42–43) — if `Γ, x ≤ t, Γ'; s ⊢ u →ˢᵘᵇ v` is a
  derivation that does NOT take the form `Co[x] →ˢᵘᵇ Co[t]` for any
  covariant context, then `Γ, Γ'[x\α]; s[x\α] ⊢ u[x\α] →ˢᵘᵇ v[x\α]`.

Both lemmas appear together in the paper because the proof of
**Lemma 9** (Promotion under substitution outside of covariant contexts,
p. 9:30) splits its case grid into "is the derivation of the form
`Co[x] →ˢᵘᵇ Co[t]`?" — covered by Lemma 29 + Conjecture 8 — versus "is
it not?" — covered by Lemma 30. The pairing is paper-structural.

## De Bruijn translation

The paper writes `Γ, x ≤ t, Γ'` as a context with a `.sub`-headed entry
between `Γ'` (innermost heads) and `Γ` (outermost). In de Bruijn there
are no names — the `x` position becomes a de Bruijn index (the level
corresponding to `Γ'.length`). The closed-prefix surface (paper's
`Γ' = nil`) collapses the de Bruijn level to `0`.

We expose Lemma 29 in a fully generic form parameterised on a context
`Γ`, a de Bruijn index `i`, and a bound `t` such that
`Γ.subBinds i t` — this generality covers the general-`Γ'` form. The
closed-prefix specialisation is recovered by setting
`Γ = ({bound := t_outer, .sub} :: Γ_outer)` and `i = 0`.

## Mechanization divergences

### Lemma 29

Paper presents the lemma as transforming a *given* derivation
`Γ, x ≤ t, Γ'; s ⊢ Co[x] →ˢᵘᵇ Co[t]` into a derivation in the
substituted context. In our formulation, the input "derivation" is
canonical — at each `Co` constructor case there is a forced last rule
(`Co = hole` → `Ms-Pro`, `Co = abs t Co'` → `Ms-Fun`/`Ms-FOp`,
`Co = app Co' v` → `Ms-App`), so we *build* it by structural induction
on `Co`.

The bound annotation on the `Ms-Fun` case is the same on both source
and target (paper p. 9:41: "Because this derivation makes a promotion
of `x` to `t`, it doesn't do a promotion of `y` to its type
annotation"); the codebase's `Ms-Fun` rule still requires
`MEqRed Γ [] t t'` for the bound, so we discharge with reflexivity
(paper Proposition 18).

-- Paper presents Lemma 29's input as a derivation; mechanized as: a
covariant-context `Co` from which the (uniquely determined) derivation
is constructed. The closed-prefix substituted-context output is
recovered by setting `Γ` to the outer context with the dropped slot
preserved as a `.sub` head.

### Lemma 30

The paper's statement targets a single `→ˢᵘᵇ` step in the substituted
context. The de Bruijn formulation discharges the `Ms-Pro` head case
(at the dropped `.sub` slot) via `WSubMStar.toMSubStar` plus a
diagrammatic stack-append. That reroute produces an `MSubStar`
(reflexive-transitive closure) rather than a single `MSubRed` step. The
existing codebase form
(`BetaInstantiationPreservesMSubRedStackMSubStar_of_stack_append` in
`Pss/Mpss/DeBruijnTypeSafety.lean:5641`) targets `MSubStar`, conditional
on the residual `MSubStarStackAppendPayload`.

-- Paper conclusion is `→ˢᵘᵇ` (single step); mechanized as: `MSubStar`
(reflexive-transitive closure), discharging the `Ms-Pro` head case via
`WSubMStar.toMSubStar` rather than the paper's "NOT covariant context"
exclusion. The two forms of "NOT covariant context" are equivalent at
the conclusion-shape level: the paper's exclusion ensures the
single-step output exists; the de Bruijn form admits a chain.
Downstream consumers (Theorem 4 / Theorem 5) compose chains regardless.

The `MSubStarStackAppendPayload` carries through this aliasing exactly
the same way `BetaInstantiationPreservesMSubRedMSubStar_of_stack_append`
does — i.e. the residual is paper-structural, not an artefact of the
aliasing.

### Conjecture 8

Per a careful re-reading of the paper proof (p. 9:42–43): Lemma 30's
`Ms-Pro` case discharges by case-splitting on whether `y ∈ Γ` (no `x`
in `t_y`, so `t_y[x\α] = t_y`) or `y ∈ Γ'` (substitution is the prefix
operation, `Ms-Pro` reassembles directly). Conjecture 8 enters in the
**proof of Lemma 9** (the "if Co[x] →ˢᵘᵇ Co[t]" branch which uses
Lemma 29 then Conjecture 8) — not in Lemma 30 itself.

Hence the paper-faithful aliasing of Lemma 30 here does NOT consume
Conjecture 8. The `#print axioms` output for Lemma 30 should list
only the kernel three (`propext`, `Quot.sound`, `Classical.choice`) plus
any residual carried by `MSubStarStackAppendPayload`. Conjecture 8 will
appear only in the `#print axioms` of Lemma 9 (or any caller that
combines Lemma 29 with Conjecture 8 to bridge `→ˢᵘᵇ` to `≤*_wf`).

The Lemma 29 + Conjecture 8 combination IS exposed in this file as
`Lemma_9_Bridge_via_Conjecture8` for callers wishing the paper's
"covariant-context" branch of Lemma 9 in one entry point.

## Imports

Imports `Pss.Paper.Conjecture8` for `CovariantContext` and
`Conjecture_8_WellSubtypingContextIndependent`,
`Pss.Paper.Aux.Propositions` for `Proposition_18_MEqRedReflexivity`,
and `Pss.Mpss.DeBruijnTypeSafety` for the
`BetaInstantiationPreservesMSubRedStackMSubStar` family that backs
Lemma 30. -/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Substitution through a covariant context

Paper notation `Co_{[x\α]}` substitutes `[x\α]` through the bound
annotations of `abs` and the operands of `app` of `Co`, while
preserving the hole structure. -/

/-- de Bruijn analogue of paper's `Co_{[x\α]}`: substitute the de
Bruijn substitution `[k\v]` through `Co`'s bound annotations and
operands while preserving the hole. Under an `abs` constructor, the
substitution argument is shifted (mirroring `Term.instantiate` on
`.abs`). -/
def CovariantContext.instantiate (k : Nat) (v : Term) :
    CovariantContext → CovariantContext
  | .hole => .hole
  | .abs t Co' =>
      .abs (Term.instantiate k v t)
        (Co'.instantiate (k + 1) (Term.shift 0 v))
  | .app Co' t => .app (Co'.instantiate k v) (Term.instantiate k v t)

@[simp] theorem CovariantContext.instantiate_hole (k : Nat) (v : Term) :
    CovariantContext.instantiate k v .hole = .hole := rfl

@[simp] theorem CovariantContext.instantiate_abs_eq (k : Nat) (v t : Term)
    (Co' : CovariantContext) :
    CovariantContext.instantiate k v (.abs t Co') =
      .abs (Term.instantiate k v t)
        (Co'.instantiate (k + 1) (Term.shift 0 v)) := rfl

@[simp] theorem CovariantContext.instantiate_app_eq (k : Nat) (v : Term)
    (Co' : CovariantContext) (t : Term) :
    CovariantContext.instantiate k v (.app Co' t) =
      .app (Co'.instantiate k v) (Term.instantiate k v t) := rfl

/-! ## Lemma 29 — Promotion under substitution OUTSIDE of covariant
contexts (paper p. 9:41–42)

Paper statement (p. 9:41):

> *Statement.* Let `Γ; s` be an extended context, `Γ'` a logical
> context, such that `Γ, Γ'[x\α]; nil` is prevalid. Let `t` and `α` be
> terms. Let `x` be a variable. If `Γ, x ≤ t, Γ'; s ⊢ Co[x] →ˢᵘᵇ Co[t]`
> is a derivation for some covariant context `Co`, then we have
> `Γ, Γ'[x\α]; s[x\α] ⊢ Co_{[x\α]}[x] →ˢᵘᵇ Co_{[x\α]}[t]`.

Paper proof (p. 9:41–42): induction on `u`'s shape (the term filling
`Co`'s hole) — equivalently, on `Co`'s shape.

* `u = y` (`Co = □`): `y` is `x`. `Ms-Pro` reassembles directly in the
  substituted context.
* `u = λy ≤ z.u'` (`Co = λy ≤ z.Co'`): IH on `Co'`'s body (under the
  added preserved head `y ≤ z`); `Ms-Fun` reassembles. By alpha
  conversion `y ≠ x`, so the binder annotation `z` doesn't promote
  `x`.
* `u = u' u''` (`Co = Co' u''`): IH on `Co'` with `u''` pushed onto the
  stack; `Ms-App` reassembles. -/

/-- **Lemma 29 (Promotion under substitution outside of covariant
contexts), paper p. 9:41–42 — generic context form.**

The generic form: given a context `Γ` with a `.sub` entry at de Bruijn
index `i` whose lifted bound is `t`, for any covariant context `Co` and
any stack `s`, we have a `MSubRed` derivation
`Γ; s ⊢ Co.fill (.bvar i) →ˢᵘᵇ Co.fill t`.

The closed-prefix surface (paper's `Γ' = nil`) is recovered by
`Γ = {bound := t_outer, .sub} :: Γ_outer` and `i = 0`; the substituted
target then equals `Term.shift 0 t_outer`.

The proof is structural induction on `Co`. The `abs` case fires either
`Ms-Fun` (when the stack is empty) or `Ms-FOp` (when non-empty); the
former requires `MEqRed Γ [] t t` for the bound, discharged via
Proposition 18 reflexivity. The `app` case pushes the operand onto the
stack before recursing.

**Premises (de Bruijn shape):**

* `hpv : PrevalidExt Γ s` — the source context's prevalidity.
* `hb : Γ.subBinds i t` — the dropped slot's lookup at level `i`.
* `hCoFillScoped : Term.Scoped Γ.depth (Co.fill (.bvar i))` — paper's
  "Co[x] is well-formed in `Γ, x ≤ t, Γ'`".
* `hCoFillTargetScoped : Term.Scoped Γ.depth (Co.fill t)` — paper's
  "Co[t] is well-formed in `Γ, x ≤ t, Γ'`".
* `hAbsBoundScoped : Co.absBoundsScopedAt Γ.depth` — bounds and operands
  inside `Co` are scoped at `Γ.depth`. We extract these on the fly via
  the recursive scope premise.
-/
private noncomputable def CovariantContext.promote_at_subBinds_aux
    (Co : CovariantContext) :
    ∀ {Γ : Ctx} {s : Stack} {i : Nat} {t : Term},
      PrevalidExt Γ s →
      Γ.subBinds i t →
      Term.Scoped Γ.depth (Co.fill (.bvar i)) →
      Term.Scoped Γ.depth (Co.fill t) →
      MSubRed Γ s (Co.fill (.bvar i)) (Co.fill t) := by
  induction Co with
  | hole =>
      intro Γ s i t hpv hb _ _
      -- Hole: Co.fill (.bvar i) = .bvar i, Co.fill t = t
      simpa [CovariantContext.fill] using MSubRed.pro hpv hb
  | abs tBound Co' ih =>
      intro Γ s i t hpv hb hSrcScoped hTgtScoped
      -- Co.fill (.bvar i) = .abs tBound (Co'.fill (Term.shift 0 (.bvar i)))
      --                  = .abs tBound (Co'.fill (.bvar (i+1)))
      -- Co.fill t = .abs tBound (Co'.fill (Term.shift 0 t))
      have hShiftBvar : Term.shift 0 (.bvar i) = (.bvar (i + 1) : Term) := by
        simp [Term.shift, Term.shiftBy]
      have hSrcEq :
          Co'.fill (Term.shift 0 (.bvar i)) = Co'.fill (.bvar (i + 1)) := by
        rw [hShiftBvar]
      -- Extract scoping invariants from the source's abs structure.
      have hSrcAbs :
          Term.Scoped Γ.depth
              (.abs tBound (Co'.fill (Term.shift 0 (.bvar i)))) := by
        simpa [CovariantContext.fill] using hSrcScoped
      have htBoundScoped : Term.Scoped Γ.depth tBound := by
        cases hSrcAbs with
        | abs hb _ => exact hb
      have hCo'SrcBodyScoped :
          Term.Scoped (Γ.depth + 1) (Co'.fill (Term.shift 0 (.bvar i))) := by
        cases hSrcAbs with
        | abs _ hbody => exact hbody
      have hTgtAbs :
          Term.Scoped Γ.depth (.abs tBound (Co'.fill (Term.shift 0 t))) := by
        simpa [CovariantContext.fill] using hTgtScoped
      have hCo'TgtBodyScoped :
          Term.Scoped (Γ.depth + 1) (Co'.fill (Term.shift 0 t)) := by
        cases hTgtAbs with
        | abs _ hbody => exact hbody
      -- The body's lookup: subBinds (head :: Γ) (i+1) (Term.shift 0 t).
      -- Two cases on the stack: empty → `Ms-Fun`; non-empty → `Ms-FOp`.
      cases s with
      | nil =>
          -- Empty stack: `Ms-Fun` with `.sub`-headed body context.
          have hpvOuter : Prevalid Γ := hpv.ctx
          have hpvBody :
              PrevalidExt
                ({ bound := tBound, kind := .sub } :: Γ) [] :=
            PrevalidExt.nil (Prevalid.sub hpvOuter htBoundScoped)
          have hbBody :
              Ctx.subBinds
                ({ bound := tBound, kind := .sub } :: Γ) (i + 1)
                (Term.shift 0 t) := by
            show Ctx.lookupSub
                ({ bound := tBound, kind := .sub } :: Γ) (i + 1) =
              some (Term.shift 0 t)
            show (Ctx.lookupSub Γ i).map (Term.shift 0) =
              some (Term.shift 0 t)
            rw [hb]; rfl
          have hSrcBody' :
              Term.Scoped
                (Ctx.depth ({ bound := tBound, kind := .sub } :: Γ))
                (Co'.fill (.bvar (i + 1))) := by
            simpa [Ctx.depth, Nat.succ_eq_add_one]
              using (hSrcEq ▸ hCo'SrcBodyScoped)
          have hTgtBody' :
              Term.Scoped
                (Ctx.depth ({ bound := tBound, kind := .sub } :: Γ))
                (Co'.fill (Term.shift 0 t)) := by
            simpa [Ctx.depth, Nat.succ_eq_add_one] using hCo'TgtBodyScoped
          have hStep :
              MSubRed ({ bound := tBound, kind := .sub } :: Γ) []
                (Co'.fill (.bvar (i + 1))) (Co'.fill (Term.shift 0 t)) :=
            ih hpvBody hbBody hSrcBody' hTgtBody'
          have hStepCast :
              MSubRed ({ bound := tBound, kind := .sub } :: Γ) []
                (Co'.fill (Term.shift 0 (.bvar i)))
                (Co'.fill (Term.shift 0 t)) :=
            hSrcEq ▸ hStep
          have hBoundRefl : MEqRed Γ [] tBound tBound :=
            Proposition_18_MEqRedReflexivity (PrevalidExt.nil hpvOuter)
              htBoundScoped
          simpa [CovariantContext.fill] using
            MSubRed.fun_ htBoundScoped hBoundRefl hStepCast
      | cons α tail =>
          -- Non-empty stack `α :: tail`: `Ms-FOp` with `.equ`-headed body
          -- context and stack `Stack.shift 0 tail`.
          have hαScoped : Term.Scoped Γ.depth α :=
            PrevalidExt.head_scoped hpv
          have hpvTail : PrevalidExt Γ tail :=
            PrevalidExt.tail hpv
          have hpvOuter : Prevalid Γ := hpv.ctx
          have hpvHeadEqu : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
            Prevalid.equ hpvOuter hαScoped
          have hpvBody :
              PrevalidExt
                ({ bound := α, kind := .equ } :: Γ) (Stack.shift 0 tail) :=
            PrevalidExt.weaken_head hpvTail hpvHeadEqu
          -- Helper: lookup transports under one preserved head with shifted
          -- target.
          have hbBody :
              Ctx.subBinds
                ({ bound := α, kind := .equ } :: Γ) (i + 1)
                (Term.shift 0 t) := by
            show Ctx.lookupSub
                ({ bound := α, kind := .equ } :: Γ) (i + 1) =
              some (Term.shift 0 t)
            show (Ctx.lookupSub Γ i).map (Term.shift 0) =
              some (Term.shift 0 t)
            rw [hb]; rfl
          have hSrcBody' :
              Term.Scoped
                (Ctx.depth ({ bound := α, kind := .equ } :: Γ))
                (Co'.fill (.bvar (i + 1))) := by
            simpa [Ctx.depth, Nat.succ_eq_add_one]
              using (hSrcEq ▸ hCo'SrcBodyScoped)
          have hTgtBody' :
              Term.Scoped
                (Ctx.depth ({ bound := α, kind := .equ } :: Γ))
                (Co'.fill (Term.shift 0 t)) := by
            simpa [Ctx.depth, Nat.succ_eq_add_one] using hCo'TgtBodyScoped
          have hStep :
              MSubRed ({ bound := α, kind := .equ } :: Γ)
                (Stack.shift 0 tail)
                (Co'.fill (.bvar (i + 1))) (Co'.fill (Term.shift 0 t)) :=
            ih hpvBody hbBody hSrcBody' hTgtBody'
          have hStepCast :
              MSubRed ({ bound := α, kind := .equ } :: Γ)
                (Stack.shift 0 tail)
                (Co'.fill (Term.shift 0 (.bvar i)))
                (Co'.fill (Term.shift 0 t)) :=
            hSrcEq ▸ hStep
          -- `Ms-FOp` keeps the bound on both sides; that matches our shape.
          simpa [CovariantContext.fill] using
            MSubRed.fOp htBoundScoped hαScoped hStepCast
  | app Co' v ih =>
      intro Γ s i t hpv hb hSrcScoped hTgtScoped
      -- Co.fill (.bvar i) = .app (Co'.fill (.bvar i)) v
      -- Co.fill t = .app (Co'.fill t) v
      have hSrcApp :
          Term.Scoped Γ.depth (.app (Co'.fill (.bvar i)) v) := by
        simpa [CovariantContext.fill] using hSrcScoped
      have hCo'SrcScoped : Term.Scoped Γ.depth (Co'.fill (.bvar i)) := by
        cases hSrcApp with
        | app hf _ => exact hf
      have hvScoped : Term.Scoped Γ.depth v := by
        cases hSrcApp with
        | app _ hv => exact hv
      have hTgtApp :
          Term.Scoped Γ.depth (.app (Co'.fill t) v) := by
        simpa [CovariantContext.fill] using hTgtScoped
      have hCo'TgtScoped : Term.Scoped Γ.depth (Co'.fill t) := by
        cases hTgtApp with
        | app hf _ => exact hf
      -- IH on Co' with operand v pushed onto the stack.
      have hpvCons : PrevalidExt Γ (v :: s) :=
        PrevalidExt.cons hpv hvScoped
      have hStep :
          MSubRed Γ (v :: s) (Co'.fill (.bvar i)) (Co'.fill t) :=
        ih hpvCons hb hCo'SrcScoped hCo'TgtScoped
      simpa [CovariantContext.fill] using MSubRed.app hStep hvScoped

/-- **Lemma 29 (Promotion under substitution outside of covariant
contexts), paper p. 9:41–42 — generic form.**

For any context `Γ` with `subBinds i t` (the dropped slot's lookup at
level `i`), any stack `s`, and any covariant context `Co` such that
`Co.fill (.bvar i)` and `Co.fill t` are scoped at `Γ.depth`, we have
`MSubRed Γ s (Co.fill (.bvar i)) (Co.fill t)`.

The general form encompasses paper's `Γ' = nil` and `Γ' ≠ nil` cases
uniformly via the de Bruijn level encoding.

The "post-substitution" content of paper's statement is recovered by
viewing the input `Γ` as paper's `Γ, x ≤ t, Γ'[x\α]` and `Co` as
paper's `Co_{[x\α]}` — the lemma then transports the canonical
promotion derivation through any prefix substitution as long as the
witness `Γ.subBinds i t` survives. -/
noncomputable def Lemma_29_PromotionUnderSubst_OutsideCovariant
    {Γ : Ctx} {s : Stack} {i : Nat} {t : Term}
    (Co : CovariantContext)
    (hpv : PrevalidExt Γ s)
    (hb : Γ.subBinds i t)
    (hSrcScoped : Term.Scoped Γ.depth (Co.fill (.bvar i)))
    (hTgtScoped : Term.Scoped Γ.depth (Co.fill t)) :
    MSubRed Γ s (Co.fill (.bvar i)) (Co.fill t) :=
  Co.promote_at_subBinds_aux hpv hb hSrcScoped hTgtScoped

/-- **Lemma 29, closed-prefix specialisation (paper's `Γ' = nil`).**

Paper's closed-prefix form: `Γ, x ≤ t; s ⊢ Co[x] →ˢᵘᵇ Co[t]`. In de
Bruijn this is `Γ = {bound := t_outer, .sub} :: Γ_outer` and `i = 0`,
so the substituted target is `Term.shift 0 t_outer`. -/
noncomputable def Lemma_29_PromotionUnderSubst_OutsideCovariant_closed
    {Γ : Ctx} {s : Stack} {tOuter : Term}
    (Co : CovariantContext)
    (hpv : PrevalidExt
      ({ bound := tOuter, kind := .sub } :: Γ) s)
    (hSrcScoped :
      Term.Scoped (Ctx.depth ({ bound := tOuter, kind := .sub } :: Γ))
        (Co.fill (.bvar 0)))
    (hTgtScoped :
      Term.Scoped (Ctx.depth ({ bound := tOuter, kind := .sub } :: Γ))
        (Co.fill (Term.shift 0 tOuter))) :
    MSubRed ({ bound := tOuter, kind := .sub } :: Γ) s
      (Co.fill (.bvar 0)) (Co.fill (Term.shift 0 tOuter)) :=
  Lemma_29_PromotionUnderSubst_OutsideCovariant
    (i := 0) (t := Term.shift 0 tOuter) Co hpv
    (by simp [Ctx.subBinds, Ctx.lookupSub])
    hSrcScoped hTgtScoped

/-- Prop-wrapper variant of Lemma 29 for callers that consume `MSubRedJ`. -/
theorem Lemma_29_PromotionUnderSubst_OutsideCovariant_J
    {Γ : Ctx} {s : Stack} {i : Nat} {t : Term}
    (Co : CovariantContext)
    (hpv : PrevalidExt Γ s)
    (hb : Γ.subBinds i t)
    (hSrcScoped : Term.Scoped Γ.depth (Co.fill (.bvar i)))
    (hTgtScoped : Term.Scoped Γ.depth (Co.fill t)) :
    MSubRedJ Γ s (Co.fill (.bvar i)) (Co.fill t) :=
  ⟨Lemma_29_PromotionUnderSubst_OutsideCovariant Co hpv hb hSrcScoped hTgtScoped⟩

/-! ## Lemma 30 — Promotion under substitution INSIDE of covariant
contexts (paper p. 9:42–43)

Paper statement (p. 9:42):

> *Statement.* Let `Γ; s` be an extended context. Let `Γ'` be a logical
> context, such that `Γ, Γ'[x\α]; s[x\α]` is prevalid. Let `u, v, t, α`
> be terms; `x` a variable. If `Γ, x ≤ t, Γ'; s ⊢ u →ˢᵘᵇ v`, such that
> this derivation is NOT of the form
> `Γ, x ≤ t, Γ'; s ⊢ Co[x] →ˢᵘᵇ Co[t]` for some covariant context `Co`,
> then `Γ, Γ'[x\α]; s[x\α] ⊢ u[x\α] →ˢᵘᵇ v[x\α]`.

Paper proof (p. 9:42–43): induction on the `→ˢᵘᵇ` derivation by last
rule. The "NOT covariant context" exclusion is used in the `Ms-Pro`
case: the derivation's only available shape with a covariant context is
`Co = □` and lookup at the dropped slot, which is excluded by
hypothesis. So the `Ms-Pro` case reduces to the `y ≠ x` and `y ∈ Γ'`
sub-cases, both of which reassemble structurally.

In de Bruijn the "NOT covariant context" exclusion translates to a
specific lookup-shape exclusion at `bvar 0`. The codebase's existing
machinery
(`BetaInstantiationPreservesMSubRedStackMSubStar_of_stack_append`)
discharges the `Ms-Pro` head case via `WSubMStar.toMSubStar` plus
diagrammatic stack-append, producing an `MSubStar` (chain) instead of a
single `MSubRed` step. See file docstring "Mechanization divergences /
Lemma 30" for the trade-off. -/

/-- **Lemma 30 (Promotion under substitution inside of covariant
contexts), paper p. 9:42–43 — closed-prefix form, conditional on
`MSubStarStackAppendPayload`.**

Paper's closed-prefix `Γ' = nil` specialisation. Conclusion targets
`MSubStar` (reflexive-transitive closure of `MSubRed`) instead of
paper's single `→ˢᵘᵇ` step; see file docstring for the rationale.

The `MSubStarStackAppendPayload` premise is the codebase's residual for
the `Ms-Pro` head substitution case. Downstream consumers supply this
payload from `MSubStarStackAppendPayload.of_body_transports`. -/
noncomputable def Lemma_30_PromotionUnderSubst_InsideCovariant
    {Γ : Ctx} {s : Stack} {t α u v : Term}
    (hAppend : MSubStarStackAppendPayload)
    (hAlphaBound : WSubMStar Γ α t)
    (h : MSubRed ({ bound := t, kind := .sub } :: Γ) s u v) :
    MSubStar Γ (Stack.instantiate 0 α s)
      (Term.instantiate 0 α u) (Term.instantiate 0 α v) :=
  BetaInstantiationPreservesMSubRedStackMSubStar_of_stack_append
    hAppend hAlphaBound h

/-- **Lemma 30 (empty-stack form), paper p. 9:42–43 — `s = nil`.**

Specialisation to the empty stack. Conditional on the same residual
`MSubStarStackAppendPayload`. -/
noncomputable def Lemma_30_PromotionUnderSubst_InsideCovariant_nilStack
    {Γ : Ctx} {t α u v : Term}
    (hAppend : MSubStarStackAppendPayload)
    (hAlphaBound : WSubMStar Γ α t)
    (h : MSubRed ({ bound := t, kind := .sub } :: Γ) [] u v) :
    MSubStar Γ [] (Term.instantiate 0 α u) (Term.instantiate 0 α v) :=
  BetaInstantiationPreservesMSubRedMSubStar_of_stack_append
    hAppend hAlphaBound h

/-! ## Lemma 9 — Promotion under substitution (paper p. 9:30)

Combining Lemma 29 with Conjecture 8 yields the "covariant context"
branch of paper's Lemma 9. The "non-covariant context" branch reduces
to Lemma 30. We expose the bridge at this combination point so callers
can use one entry point. -/

/-- **Lemma 9 bridge via Conjecture 8.**

Paper proof of Lemma 9 (p. 9:31), "Co[x] →ˢᵘᵇ Co[t]" branch: by Lemma
19 (weakening) on `Γ ⊢ α ≤*_wf t`, then **Conjecture 8** to lift
through `Co_{[x\α]}`. We replicate that proof structure exactly:

* Lemma 29 produces the canonical promotion derivation
  `MSubRed (Γ_x_t) s (Co.fill (.bvar 0)) (Co.fill (Term.shift 0 t))`
  (or in `Γ`-substituted form, the appropriate transported version).
* Conjecture 8 then bridges from `WSubMStar Γ α t` to
  `WSubMStar Γ (Co_{[x\α]}.fill α) (Co_{[x\α]}.fill t)`.

We expose the bridge as a single application that consumes both
ingredients. The well-formedness premises `Co.fill α wf` and
`Co.fill t wf` are paper's "both `Co_{[x\α]}[α]` and
`Co_{[x\α]}[t]` are well-formed" requirement (paper p. 9:30 Lemma 9
hypothesis). -/
noncomputable def Lemma_9_Bridge_via_Conjecture8
    {Γ : Ctx} {α t : Term}
    (Co : CovariantContext)
    (h : WSubMStar Γ α t)
    (hCoα : WfM Γ (Co.fill α))
    (hCot : WfM Γ (Co.fill t)) :
    WSubMStar Γ (Co.fill α) (Co.fill t) :=
  Conjecture_8_WellSubtypingContextIndependent h Co hCoα hCot

end Paper
end DeBruijn
end Pss
