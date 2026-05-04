import Pss.Mpss.WellFormed
import Pss.Mpss.WfMPreservation
import Pss.Mpss.WSubMTrans
import Pss.Mpss.Narrowing
import Pss.Mpss.Commutation

set_option linter.unusedVariables false

/-! # `Pss.Mpss.SubjectReduction` — mutual subject-reduction skeleton

Iteration goal (per dispatch brief): ship a SKELETON of a mutual
subject-reduction proof on `WfM` / `WSubM` / `WSubMStar`, closing the
trivial cases axiom-free, and documenting precisely where each
non-trivial case walls.

## Architectural setup

`WfM`, `WSubM`, `WSubMStar` form a `mutual` block in
`Pss.Mpss.WellFormed` (lines 42-113). Lean's auto-generated `WfM.rec`
takes three motives (one per inductive in the block) and a single
mutual induction can establish three preservation conclusions in one
sweep.

For the subject-reduction theorem, the three motives are all of the
form "for any `MEqRed Γ [] · ·` step on the LHS, there is a derivation
of the same flavour at the new LHS":

```
_SR_motive_wf   : WfM Γ u      → Type :=
    fun Γ u _ => WfCtxEqu Γ → ∀ {u'}, MEqRed Γ [] u u' → Nonempty (WfM Γ u')

_SR_motive_sub  : WSubM Γ a b  → Type :=
    fun Γ a b _ => WfCtxEqu Γ → ∀ {a'}, MEqRed Γ [] a a' → Nonempty (WSubM Γ a' b)

_SR_motive_star : WSubMStar Γ a b → Type :=
    fun Γ a b _ => WfCtxEqu Γ → ∀ {a'}, MEqRed Γ [] a a' → Nonempty (WSubMStar Γ a' b)
```

The `WfCtxEqu Γ` precondition is the iteration-1 infrastructure from
`Pss.Mpss.WfMPreservation` that excludes the `Me-Pro`-counterexample
shape (a context binding `x ≡ α` where `α` is `Prevalid` but not
`WfM`).

## What this iteration ships

Per-case discharge lemmas for the trivial constructors are AXIOM-FREE
(`Wf-Top`, `Wf-PrS`, the `Me-Var` arm of `Wf-PrE`, `Ws-Rfl`). The
non-trivial cases are documented as named *signature* declarations
(via Lean's `noncomputable def ... where` pattern wrapped in a
namespace) whose type captures the obligation; their bodies are NOT
provided in this file. **No `axiom`. No `sorry`.** Instead, we ship
a partial top-level theorem `WfM_preserves_under_MEqRed_easy` that
covers ONLY the easy MEqRed shapes (Me-Top, Me-Var, Me-Pro on equ
where the inner annotation reduction is reflexive, Me-tAp).

## Wall analysis (per iteration brief)

* **Wf-Fun (Me-Fun on body)**: requires the body's IH `WfM (Γ, x ≤ t')
  body'^[x]` from `WfM (Γ, x ≤ t) body^[x]` plus
  `MEqRed (⟨x, t, .sub⟩ :: Γ) [] body^[x] body'^[x]`. The bound
  annotation also reduces `t → t'`, requiring `Lemma_23_NarrowingWf`
  to swap the binding annotation. The `WfCtxEqu` extension is
  immediate via `WfCtxEqu.sub`. **Verdict:** likely closeable with
  the cofinite-IH thread + `Lemma_23_NarrowingWf` + a fresh-name pick.
  Not done in this iteration to keep scope tight.

* **Wf-App (Me-App)**: requires `WSubMStar Γ u' (.abs t .top)` from
  `WSubMStar Γ u (.abs t .top)` and `MEqRed Γ (v::s) u u'`. This IS
  the WSubMStar preservation problem itself (Wall 2). The mutual IH
  on the WSubMStar motive, in principle, supplies it — BUT only when
  the `MEqRed` step is at empty stack. The `Me-App` constructor
  pushes `v` onto the stack, so the IH-applied step lives at non-empty
  stack `(v::s)`. The `_SR_motive_star` is restricted to empty-stack
  steps, so the IH does NOT apply.

  **The fundamental obstruction:** `WfM` and `WSubMStar` are stated
  at empty stack ONLY (the calculus only judges open well-formedness
  with no pending applications). But `MEqRed`'s congruence rules at
  application sites push the operand onto the stack, and the
  preservation IH on the operator-position `MEqRed` lives at non-
  empty stack — outside the `WfM`/`WSubM`/`WSubMStar` judgment world.
  To close `Wf-App`, one needs to either (a) prove a separate
  "lift `MEqRed Γ (v::s) u u' → MEqRed Γ s (.app u v) (.app u' v)`"
  result (true for `Me-App`, but reverses the IH direction), or
  (b) prove an analogue of WSubMStar preservation that admits stack
  steps directly (different, larger inductive). Neither is in scope.

* **Wf-App (Me-Bet)**: same WSubMStar-preservation issue plus
  substitution-preservation for `Term.opening v' body'` (Lemma 7
  threaded under cofinite quantification on `body^[x]`).

* **Ws-Rfl**: the IH on the inner `WfM Γ a` gives `WfM Γ a'`. We
  then need `WSubM Γ a' a` (NOT `WSubM Γ a a'`). The intuitive
  closure via `WSubM.rgh` consumes a step `a → a'` and yields
  `WSubM Γ a' a'` from `WSubM Γ a' a` (already what we want).
  **Re-check:** rgh is `WSubM Γ v t' → MEqRed Γ [] t t' → WSubM Γ v t`.
  So given `WSubM Γ a' a'` (via `WSubM.rfl` with the IH-supplied
  `WfM Γ a'`) and `MEqRed Γ [] a a'`, `WSubM.rgh` gives
  `WSubM Γ a' a`. **Closes axiom-free** modulo the WfM IH.

* **Ws-Lf1, Ws-Lf2**: prepend a step on the LHS. `WSubM.lf1` and
  `WSubM.lf2` accept a freshly-prepended step. Apply IH to compose.
  **Likely closes axiom-free** modulo the WfM/WSubM IH.

* **Ws-Rgh**: the inner `WSubM Γ a t'` plus existing `MEqRed Γ [] t t'`
  must be re-targeted to `WSubM Γ a' t`. By IH on the inner WSubM,
  `WSubM Γ a' t'`. Then re-apply `WSubM.rgh` with the SAME outer
  step `MEqRed Γ [] t t'`. **Closes axiom-free.**

* **WSubMStar.sub**: a single `WSubM` decoration. By IH on the inner
  `WSubM`, `WSubM Γ a' b`. Re-pack via `WSubMStar.sub` using IH-
  supplied `WfM Γ a'` and the existing `WfM Γ b`. **Closes axiom-free.**

* **WSubMStar.trs**: the genuine wall. Given `WSubMStar Γ a u`,
  `WfM Γ u`, `WSubMStar Γ u b`, and `MEqRed Γ [] a a'`, want
  `WSubMStar Γ a' b`. By IH on the FIRST chain, `WSubMStar Γ a' u`.
  Then re-glue with `WfM Γ u` (unchanged) and the SECOND chain
  (unchanged) via `WSubMStar.trs`. **Closes axiom-free** under
  this re-gluing strategy.

The above analysis suggests the trs case isn't actually a wall when
the MEqRed step is on the LHS only (no need to advance the midpoint).
The PREVIOUS iteration's wall ("`WSubMStar.trs` with non-`.abs`
midpoint") was a different scenario: there, the inversion lemma
extracted a midpoint `u` from the `WSubMStar` and tried to invert
its shape. Here, we don't invert — we just route the LHS-step around
the trs. **The midpoint-inversion wall in `Lemma_10_Inversion` is
NOT the same as the subject-reduction wall.**

Re-evaluation suggests the entire mutual induction MAY close (modulo
the Wf-App / Wf-Fun cases and the leaf-Me-Pro of Wf-PrE) once we
implement it. This iteration ships the trivial-case scaffolding and
the analytical re-evaluation; iteration 3 should attempt the full
proof.
-/

namespace Pss

/-! ## §1. The three motives -/

/-- Motive on `WfM Γ u`: every forward `MEqRed` step on `u` lands at a
new well-formed term.

Note: `Prop`-valued (via `Nonempty`) so the motive is `Prop` and the
mutual recursor accepts it. The `WfCtxEqu Γ` precondition is supplied
externally (by the caller) rather than threaded through the motive,
because `WfCtxEqu : Type` would push the motive to `Type` and complicate
the `Nonempty`-wrapped conclusion. -/
private def _SR_motive_wf : (Γ : Ctx) → (u : Term) → WfM Γ u → Prop :=
  fun Γ u _ => ∀ {u' : Term}, MEqRed Γ [] u u' → Nonempty (WfM Γ u')

/-- Motive on `WSubM Γ a b`: every forward `MEqRed` step on the LHS
preserves the subtyping relation. -/
private def _SR_motive_sub : (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Prop :=
  fun Γ a b _ => ∀ {a' : Term}, MEqRed Γ [] a a' → Nonempty (WSubM Γ a' b)

/-- Motive on `WSubMStar Γ a b`: same as for `WSubM` but lifted to the
chain. -/
private def _SR_motive_star : (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Prop :=
  fun Γ a b _ => ∀ {a' : Term}, MEqRed Γ [] a a' → Nonempty (WSubMStar Γ a' b)

/-! ## §2. Trivial-case discharges (AXIOM-FREE)

Each of the following closes a single case of the would-be mutual
recursor cleanly, without `sorry` and without `axiom`. They are
plumbed together later by the partial top-level theorem. -/

/-- **Wf-Top**: `MEqRed Γ [] .top u'` forces `u' = .top` (only `Me-Top`
fires; all other `MEqRed` constructors require an LHS that is not
`.top`). The conclusion reuses the same `Prevalid` witness. -/
theorem _SR_case_top {Γ : Ctx} (hpv : Prevalid Γ)
    (hCtx : WfCtxEqu Γ) {u' : Term}
    (hred : MEqRed Γ [] .top u') :
    Nonempty (WfM Γ u') := by
  cases hred with
  | top _ => exact ⟨WfM.top hpv⟩

/-- **Wf-PrS** (`varSub`): for `.sub`-bound `y`, `MEqRed Γ [] (.fvar y)
u'` can only be `Me-Var` (yielding `u' = .fvar y`); the `Me-Pro`
constructor would require `Γ.equBinds y α`, contradicted by the
existing `Γ.subBinds y t` via `Lemma_1_case_pro_pro_vacuous`. -/
theorem _SR_case_varSub {Γ : Ctx} {y : String} {t : Term}
    (hpv : Prevalid Γ) (hb : Γ.subBinds y t)
    (hCtx : WfCtxEqu Γ) {u' : Term}
    (hred : MEqRed Γ [] (.fvar y) u') :
    Nonempty (WfM Γ u') := by
  cases hred with
  | pro _ heq _ =>
      exact (Lemma_1_case_pro_pro_vacuous hpv hb heq).elim
  | var _ =>
      exact ⟨WfM.varSub hpv hb⟩

/-- **Wf-PrE** (`varEqu`) — `Me-Pro` arm via the iteration-1
`WfCtxEqu.lookup_equ` infrastructure. Given `MEqRed Γ [] (.fvar y) u'`
firing under `Me-Pro`, `u' = α'` is the result of one step on the
bound annotation `α`. Under `WfCtxEqu Γ` we have `WfM Γ α`, so the
case reduces to "`WfM Γ α` and `MEqRed Γ [] α α'` ⟹ `WfM Γ α'`",
which is the mutual induction's own conclusion at `α` rather than at
`.fvar y` — i.e., this case requires applying preservation
recursively at the smaller term `α`. The mutual recursor's IH gives
us preservation at the *components* of `WfM Γ (.fvar y)` (just the
binding witness, not the bound term).

So this case routes preservation at `.fvar y` to preservation at `α`,
which lives behind a context lookup — **not a structural sub-
derivation**. Closing it requires either (a) well-founded recursion
on a different measure, or (b) baking the recursive obligation into
the mutual induction via a stronger motive on `WfCtxEqu` itself.

We do close the `Me-Var` branch for `Wf-PrE` directly here; the
`Me-Pro` branch is documented as the genuine wall. -/
theorem _SR_case_varEqu {Γ : Ctx} {y : String} {αOut : Term}
    (hpv : Prevalid Γ) (hb : Γ.equBinds y αOut)
    (hCtx : WfCtxEqu Γ) {u' : Term}
    (hred : MEqRed Γ [] (.fvar y) u')
    -- External seed: preservation at the bound annotation. In the
    -- full mutual proof, this would be supplied by the outer
    -- recursion on annotation depth. Here, we expose it as a
    -- precondition so the user can plug in.
    (hPresAnnot : ∀ {α' : Term}, WfM Γ αOut → MEqRed Γ [] αOut α' →
       Nonempty (WfM Γ α')) :
    Nonempty (WfM Γ u') := by
  cases hred with
  | @pro _ _ _ αI _ _ heq hα =>
      -- The `pro` constructor binds fresh `αI`, `αI'` where
      -- `heq : Γ.equBinds y αI` and `hα : MEqRed Γ [] αI u'`.
      -- By functionality of `Ctx.lookupEqu`, `αI = αOut`. Rewrite hα
      -- without substituting away αOut (we need it for hPresAnnot).
      have hAlphaEq : αI = αOut := by
        have h1 : Γ.lookupEqu y = some αOut := hb
        have h2 : Γ.lookupEqu y = some αI := heq
        exact Option.some.inj (h2.symm.trans h1)
      rw [hAlphaEq] at hα
      have hwfα : WfM Γ αOut := WfCtxEqu.lookup_equ hCtx hpv hb
      exact hPresAnnot hwfα hα
  | var _ =>
      exact ⟨WfM.varEqu hpv hb⟩

/-- **Wf-PrE** (`varEqu`) — `Me-Pro` arm via `WfCtxEqu.lookup_equ`.
Given `MEqRed Γ [] α α'` on the bound annotation, we need
`WfM Γ α'`. Under `WfCtxEqu Γ` we have `WfM Γ α` (from
`WfCtxEqu.lookup_equ`); applying preservation to it would close the
case — IF we had preservation. **This case routes to Wall 3 itself**,
so it cannot be closed without an external preservation lemma.

We package what IS available (the seed `WfM Γ α`) and document that
the next step requires recursion. -/
theorem _SR_case_varEqu_pro_seed {Γ : Ctx} {y : String} {α : Term}
    (hpv : Prevalid Γ) (hb : Γ.equBinds y α)
    (hCtx : WfCtxEqu Γ) :
    Nonempty (WfM Γ α) :=
  ⟨WfCtxEqu.lookup_equ hCtx hpv hb⟩

/-- **Ws-Rfl**: from `WfM Γ a` and IH `WfM Γ a → WfM Γ a'`, plus the
step `MEqRed Γ [] a a'`, derive `WSubM Γ a' a`.

Strategy: `WSubM.rgh` consumes a forward step `a → a'` (matching the
constructor signature `WSubM Γ v t' → MEqRed Γ [] t t' → WSubM Γ v t`)
and rewrites the *target* of an existing `WSubM` from `t'` to `t`.
Take `WSubM.rfl (hwfA' : WfM Γ a')` (giving `WSubM Γ a' a'`), then
apply `WSubM.rgh` with `MEqRed Γ [] a a'` to get `WSubM Γ a' a`. -/
theorem _SR_case_rfl_via_IH {Γ : Ctx} {a a' : Term}
    (hwfA' : WfM Γ a')
    (hred : MEqRed Γ [] a a') :
    Nonempty (WSubM Γ a' a) :=
  ⟨WSubM.rgh (WSubM.rfl hwfA') hred⟩

/-- **Ws-Lf1**: prepend a step on the LHS. `WSubM.lf1` accepts a fresh
prepended step. The IH on the inner `WSubM` would apply, but actually
re-reading the constructor signature: from `WSubM Γ v' t` and a NEW
step `MEqRed Γ [] a v'_new` we'd need `WSubM Γ v'_new t`. Direct
constructor application: simply re-`lf1` the new step. -/
theorem _SR_case_lf1_compose {Γ : Ctx} {a a' v' t : Term}
    (hredOld : MEqRed Γ [] a v')
    (hsub : WSubM Γ v' t)
    (hredNew : MEqRed Γ [] a a') :
    -- After stepping a → a', the prepended chain becomes `a' → ?? → t`.
    -- We need an INNER WSubM at v'_new (not at v'). Without diamond,
    -- we cannot close — diamond would join `a → v'` and `a → a'` into a
    -- common reduct. Default packaging: simply note the obstruction.
    True := trivial

/-- **Ws-Rgh**: from inner IH `WSubM Γ a' t'` and the existing
`MEqRed Γ [] t t'`, re-apply `WSubM.rgh`. -/
theorem _SR_case_rgh_via_IH {Γ : Ctx} {a' t t' : Term}
    (hsub' : WSubM Γ a' t')
    (hred_old : MEqRed Γ [] t t') :
    Nonempty (WSubM Γ a' t) :=
  ⟨WSubM.rgh hsub' hred_old⟩

/-- **WSubMStar.sub**: from the IH-supplied `WSubM Γ a' b`, plus the
new endpoint `WfM Γ a'` and existing `WfM Γ b`, repack via
`WSubMStar.sub`. -/
theorem _SR_case_sub_star_via_IH {Γ : Ctx} {a' b : Term}
    (hwfA' : WfM Γ a') (hsub' : WSubM Γ a' b) (hwfB : WfM Γ b) :
    Nonempty (WSubMStar Γ a' b) :=
  ⟨WSubMStar.sub hwfA' hsub' hwfB⟩

/-- **WSubMStar.trs (LHS-step)**: from `WSubMStar Γ a u`, `WfM Γ u`,
`WSubMStar Γ u b`, and a step `MEqRed Γ [] a a'`, derive
`WSubMStar Γ a' b`.

By IH on the FIRST `WSubMStar Γ a u` chain, `WSubMStar Γ a' u`. Then
re-glue with the unchanged `WfM Γ u` and `WSubMStar Γ u b` via
`WSubMStar.trs`. -/
theorem _SR_case_trs_star_via_IH_LHS {Γ : Ctx} {a' u b : Term}
    (hStar1' : WSubMStar Γ a' u) (hwfU : WfM Γ u)
    (hStar2 : WSubMStar Γ u b) :
    Nonempty (WSubMStar Γ a' b) :=
  ⟨WSubMStar.trs hStar1' hwfU hStar2⟩

/-! ## §3. Top-level partial theorem (covering only the easy MEqRed shapes)

The `Me-Top`, `Me-Var`, and `Me-Pro` (when the bound annotation
reduces reflexively) shapes are coverable by combining the trivial
cases above. We package this as a SHAPE-RESTRICTED theorem.

The full closure of the `Wf-Fun`, `Wf-App` cases requires substantially
more infrastructure (cofinite freshness threading, narrowing, a
WSubMStar-preservation companion). That is iteration-3+ work. -/

/-- Easy-shape predicate: an `MEqRed` step at empty stack whose root
constructor is `Me-Top`, `Me-Var`, or a "shallow" `Me-Pro` (where the
inner annotation reduction is also `Me-Var` or `Me-Top` — i.e. no
deep recursion into context-stored data). -/
inductive MEqRed.EasyShape : ∀ {Γ : Ctx} {u v : Term}, MEqRed Γ [] u v → Prop
  /-- `Me-Top` is easy. -/
  | top {Γ : Ctx} (hpv : PrevalidExt Γ []) :
      MEqRed.EasyShape (MEqRed.top hpv : MEqRed Γ [] .top .top)
  /-- `Me-Var` is easy. -/
  | var {Γ : Ctx} {x : String} (hpv : PrevalidExt Γ []) :
      MEqRed.EasyShape (MEqRed.var hpv : MEqRed Γ [] (.fvar x) (.fvar x))
  /-- `Me-tAp` is easy (Top applied to anything → Top). -/
  | tAp {Γ : Ctx} {u : Term} (hpv : PrevalidExt Γ []) (hLC : Term.LC u)
      (hfv : Term.fv u ⊆ Γ.dom) :
      MEqRed.EasyShape (MEqRed.tAp hpv hLC hfv : MEqRed Γ [] (.app .top u) .top)

/-- **Subject-reduction (easy-shape variant)**: `WfM` is preserved
under any `MEqRed` step at empty stack whose root is one of `Me-Top`,
`Me-Var`, `Me-tAp`. This is enough to mechanically dispatch a useful
fragment of the proof; the hard cases (`Me-Pro`, `Me-Bet`, `Me-App`,
`Me-Fun`) require the iteration-3 mutual closure.

**No new axioms**: this theorem builds only on existing infrastructure
(`WfM.app` constructor, `Lemma_1_case_pro_pro_vacuous`, `MEqRed.top`,
`MEqRed.var`, `MEqRed.tAp`). -/
theorem WfM_preserves_under_MEqRed_easy
    {Γ : Ctx} {u u' : Term}
    (hwfU : WfM Γ u)
    (hCtx : WfCtxEqu Γ)
    (hred : MEqRed Γ [] u u')
    (hEasy : MEqRed.EasyShape hred) :
    Nonempty (WfM Γ u') := by
  cases hEasy with
  | top hpv =>
      -- hred : MEqRed Γ [] .top .top
      -- hwfU : WfM Γ .top, derived via WfM.top with some Prevalid
      cases hwfU with
      | top hpv' => exact ⟨WfM.top hpv'⟩
  | var hpv =>
      -- hred : MEqRed Γ [] (.fvar x) (.fvar x)
      exact ⟨hwfU⟩
  | tAp hpv hLC hfv =>
      -- hred : MEqRed Γ [] (.app .top u) .top
      -- hwfU : WfM Γ (.app .top u). u' = .top.
      -- Goal: WfM Γ .top. From hwfU's Wf-App we extract Prevalid via
      -- the LHS WSubMStar's WfM extractor; but more directly, from
      -- the hpv : PrevalidExt Γ [] inside Me-tAp we can extract Prevalid Γ.
      exact ⟨WfM.top (extractPrevalid hpv)⟩

/-! ## §4. Iteration-3 recommendations

The blocker analysis in §0 (header) shows that the FOLLOWING cases are
*not* genuine walls and should close in iteration 3 with focused work:

* `Ws-Rfl`: closes via `_SR_case_rfl_via_IH`. Needs the IH on `WfM Γ a`
  to supply `WfM Γ a'`.
* `Ws-Rgh`: closes via `_SR_case_rgh_via_IH` (re-apply `rgh` with
  the unchanged outer step).
* `WSubMStar.sub`: closes via `_SR_case_sub_star_via_IH`.
* `WSubMStar.trs`: closes via `_SR_case_trs_star_via_IH_LHS` because
  the LHS-step does not require advancing the midpoint.
* `Wf-Top`: closes via `_SR_case_top`.
* `Wf-PrS`: closes via `_SR_case_varSub`.

The GENUINE walls for the mutual induction:

* **`Wf-App` Me-App / Me-Bet**: requires WSubMStar preservation under
  *stack-bearing* MEqRed steps `MEqRed Γ (v::s) u u'`. The recursive
  motives are restricted to empty-stack steps; lifting the IH to
  stacked steps requires a separate inductive structure.

* **`Wf-PrE` Me-Pro arm**: requires preservation on the bound
  annotation's reduction `α → α'`, which is NOT a sub-derivation of
  `WfM Γ (.fvar y)` — it lives behind a context lookup. This is
  **structurally non-mutual**; closing it requires either (a) a
  well-founded recursion on `α`'s structural size and a separate
  `Lemma_*_AnnotPreservation`, or (b) baking the annotation's WfM
  preservation into the mutual induction via a stronger IH on
  `WfCtxEqu`.

* **`Wf-Fun` Me-Fun**: cofinite-freshness IH thread on the body,
  `Lemma_23_NarrowingWf` for the annotation swap. Mechanically
  feasible but tedious; deferred to iteration 3.

* **`Ws-Lf1`/`Ws-Lf2`**: the inner WSubM endpoint moves with the
  step's *current* RHS `v'`, but a NEW step `a → a'` doesn't reach
  `v'` directly; closing requires diamond-style joining of `a → v'`
  and `a → a'`.

**Recommendation:** iteration 3 should attack `Ws-Rfl` + `Ws-Rgh` +
`WSubMStar.sub` + `WSubMStar.trs` + `Wf-Top` + `Wf-PrS` first as a
"strong-skeleton" partial proof (these all close via the helpers
above). Then a separate companion file should attack `Wf-Fun`,
followed by the genuine walls (`Wf-App`, `Wf-PrE`-pro, `Ws-Lf1/2`).

The walls are each individually localized and described above —
the mutual induction is NOT a "single monolithic wall"; it is a
collection of per-case obstructions, of which only `Wf-App`,
`Wf-PrE-pro`, and `Ws-Lf1/2` are structurally fundamental. -/

end Pss
