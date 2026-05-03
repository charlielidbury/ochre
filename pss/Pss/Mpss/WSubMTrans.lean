import Pss.Mpss.WellFormed
import Pss.Mpss.TransitivityElim

set_option linter.unusedVariables false

/-! # `Pss.Mpss.WSubMTrans` — transitivity helpers for `WSubM`/`WSubMStar`

This module collects transitivity-style composition lemmas for the
well-subtyping judgment(s) `WSubM` / `WSubMStar` from
`Pss.Mpss.WellFormed`.

## Why these are not "just `WSubMStar.trs`"

`WSubMStar.trs` exists already but requires a `WfM Γ u` decoration at the
joining point. Some downstream uses (notably `Lemma_24_NarrowingMSubRed`'s
discharge plan) want to compose two `WSubM`s into a single `WSubM` (no
`*`), which the four `WSubM` constructors do **not** support directly:

* `WSubM.rfl`/`WSubM.lf1`/`WSubM.lf2` cases compose by induction on the
  *first* argument: each prepends a step on the left and recurses.
* `WSubM.rgh hsub (hred : MEqRed Γ [] b b')` requires going the other
  way: given `WSubM Γ b c`, build `WSubM Γ b' c`. That is "subject
  reduction along an MEqRed step on the LHS of `≤_wf`" — a non-trivial
  property requiring infrastructure (Lemma 6 / 7 style preservation)
  beyond the present scope.

So the *single*-`WSubM` transitivity does not collapse without further
machinery. What we *can* prove cleanly:

* **`WSubMStar.WSubM_trans`** (PROVED) — compose two `WSubM`s into a
  `WSubMStar` via `.sub` + `.trs`. Trivial; requires `WfM` at the three
  endpoints.
* **`WSubMStar.trans`** (PROVED) — compose two `WSubMStar`s into a
  single `WSubMStar` via `.trs`. Requires `WfM` at the joining point.
* **`WSubM.left_lf1_chain`** (PROVED) — prepend an `MEqRedStar` chain
  on the LHS of a `WSubM` via repeated `lf1`. No `WfM` needed.
* **`WSubM.right_rgh_chain`** (PROVED) — append an `MEqRedStar` chain
  on the RHS of a `WSubM` (running backward from RHS) via repeated
  `rgh`. No `WfM` needed.

These four are sufficient for the `Lemma_24_NarrowingMSubRed` discharge
plan provided the surrounding context can supply the `WfM` decorations
(which it does: see `Lemma_24_sound` shape in `Pss.Mpss.Narrowing`).

The *single*-`WSubM` form `WSubM.trans` would require a subject-reduction
property and is not proven here.
-/

namespace Pss

/-! ## §1. WSubMStar transitivity (trivial bridges) -/

/-- **Compose two `WSubM`s into a `WSubMStar`.** Trivial via
`WSubMStar.sub` + `WSubMStar.trs`. Requires `WfM` decorations at the
three endpoints (left, joining, right).

This is the "lifted" form of `WSubM` transitivity — the result is a
`WSubMStar` of length 2 rather than a single `WSubM`. Sufficient for
downstream consumers that ultimately strip back to `MSub` or that can
finish via `Theorem_3_TransitivityIsAdmissible`.

PROVED. -/
def WSubMStar.WSubM_trans
    {Γ : Ctx} {a b c : Term}
    (hwfA : WfM Γ a) (hwfB : WfM Γ b) (hwfC : WfM Γ c)
    (h₁ : WSubM Γ a b) (h₂ : WSubM Γ b c) :
    WSubMStar Γ a c :=
  WSubMStar.trs (WSubMStar.sub hwfA h₁ hwfB) hwfB (WSubMStar.sub hwfB h₂ hwfC)

/-- **Star-on-star transitivity** of `WSubMStar`. Direct application of
`WSubMStar.trs`. Convenience wrapper. -/
def WSubMStar.trans
    {Γ : Ctx} {a b c : Term}
    (hwfB : WfM Γ b)
    (h₁ : WSubMStar Γ a b) (h₂ : WSubMStar Γ b c) :
    WSubMStar Γ a c :=
  WSubMStar.trs h₁ hwfB h₂

/-! ## §2. Chain-extension lemmas on `WSubM` (no `WfM` needed)

These lift the single-step constructors `lf1`/`rgh` to `MEqRedStar`
chains, by `head_induction_on` on the chain. Useful downstream when one
side of a transitivity is itself a chain of equivalence reductions
(e.g. when stripping back from `MSub` toward `WSubM`). -/

/-- **Prepend an `MEqRedStar` chain on the LHS of a `WSubM`.**

Given `MEqRedStar Γ [] a a'` and `WSubM Γ a' c`, derive `WSubM Γ a c`
by repeated application of `WSubM.lf1`. By induction on the chain.

PROVED. No `WfM` premises needed (mirrors `lf1`'s lack of `WfM`
decoration). -/
noncomputable def WSubM.left_lf1_chain
    {Γ : Ctx} {a a' c : Term}
    (hChain : MEqRedStar Γ [] a a')
    (hSub : WSubM Γ a' c) :
    WSubM Γ a c := by
  -- Strengthen so we can induct on the chain endpoint.
  -- The chain is Prop-valued; conclusion is Type. Wrap in Nonempty for
  -- induction, then extract via .some at the end.
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x a'),
      Nonempty (WSubM Γ a' c → WSubM Γ x c) from (key hChain).some hSub
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := a')
    (P := fun x (_ : MEqRedStar Γ [] x a') =>
      Nonempty (WSubM Γ a' c → WSubM Γ x c)) h ?_ ?_
  · exact ⟨fun hSub' => hSub'⟩
  · intro x y hHead hTail ihY
    classical
    refine ⟨fun hSubA' => ?_⟩
    have hSubY : WSubM Γ y c := ihY.some hSubA'
    exact WSubM.lf1 hHead.some hSubY

/-- **Append an `MEqRedStar` chain on the RHS of a `WSubM`** — the
chain is read as `c → c'` (forward), and `rgh` recovers `WSubM Γ a c`
from `WSubM Γ a c'` and the chain. So this is "given `WSubM Γ a c'`
and `MEqRedStar Γ [] c c'`, derive `WSubM Γ a c`".

Note the asymmetry with `left_lf1_chain`: there, the chain runs from
`a` *to* `a'` (toward the WSubM); here, the chain runs *away from* `c`
(toward `c'` which is what the WSubM already has).

PROVED. No `WfM` premises needed. -/
noncomputable def WSubM.right_rgh_chain
    {Γ : Ctx} {a c c' : Term}
    (hSub : WSubM Γ a c')
    (hChain : MEqRedStar Γ [] c c') :
    WSubM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x c'),
      Nonempty (WSubM Γ a c' → WSubM Γ a x) from (key hChain).some hSub
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := c')
    (P := fun x (_ : MEqRedStar Γ [] x c') =>
      Nonempty (WSubM Γ a c' → WSubM Γ a x)) h ?_ ?_
  · exact ⟨fun hSub' => hSub'⟩
  · intro x y hHead hTail ihY
    classical
    refine ⟨fun hSubC' => ?_⟩
    have hSubAY : WSubM Γ a y := ihY.some hSubC'
    exact WSubM.rgh hSubAY hHead.some

/-! ## §3. Note on single-step `WSubM.trans`

Collapsing two `WSubM`s into a single `WSubM` (the "headline"
transitivity-elimination form for `≤_wf`) is **not** provable from the
infrastructure currently in the repository. Sketch of the obstruction:

Inducting on `h₁ : WSubM Γ a b`, the four cases are:
* `rfl`: trivial (return `h₂`).
* `lf1 hred h₁'`: by IH on `h₁'`, then re-apply `lf1`.
* `lf2 wfA hred wfA' h₁'`: by IH on `h₁'`, then re-apply `lf2`.
* `rgh (h₁' : WSubM Γ a b') (hred : MEqRed Γ [] b b')`: We have
  `WSubM Γ a b'` and need `WSubM Γ a c`. The IH on `h₁'` would
  finish if we had `WSubM Γ b' c`; producing it from the available
  `MEqRed Γ [] b b'` and `WSubM Γ b c` is "subject reduction for
  `WSubM` along `MEqRed` on the LHS", which the calculus does *not*
  enjoy as a one-step result without WfM-preservation along `MEqRed`
  (cf. the discharge-blocker discussion attached to
  `Lemma_10_Inversion` in `Pss.Mpss.WellFormed`, and the FALSITY
  finding documented in `Pss.Mpss.WfMPreservation` —
  the natural preservation lemma is refuted by a Lean-checked
  counterexample exploiting the `Me-Pro` rule plus the gap between
  `Prevalid` and `WfM`).

The `WSubMStar` form proven above is sufficient for all current
downstream uses and avoids this blocker. -/

end Pss
