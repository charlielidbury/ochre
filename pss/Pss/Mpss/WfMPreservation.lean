import Pss.Mpss.TypeSafety

set_option linter.unusedVariables false

/-! # `Pss.Mpss.WfMPreservation` — `WfM`-preservation under `MEqRed`

## Headline finding (agent_id: `pss-2026-05-04-WfM-preservation-counterexample`)

The natural lemma

```
Lemma_WfM_preservation_MEqRed
  {Γ u v} (hwf : WfM Γ u) (h : MEqRed Γ [] u v) : WfM Γ v
```

— which `Lemma_10_Inversion`'s discharge plan (see
`Pss.Mpss.WellFormed`) treats as a "substantial new mutual-recursive
proof" — **is mathematically FALSE in this calculus.** This module
exhibits a closed-form counterexample (Lean-checked).

The counterexample exploits the asymmetry between the structural
context-validity judgment `Prevalid` and the typing judgment `WfM`:

* `Prevalid Γ` only requires that `≡`-bound annotations have closed
  terms with `fv ⊆ prefix.dom` and are locally closed. It does **not**
  require those annotations to be themselves `WfM`-well-formed.
* `WfM Γ (.fvar x)` (rule `Wf-PrE`) is satisfied by any
  `≡`-bound `x`, regardless of the well-formedness of the bound
  annotation.
* `MEqRed.pro` promotes `.fvar x` to *exactly* the bound annotation
  (after one MEqRed step on it).

So the witness is:

* `Γ = [⟨"x", .app .top .top, .equ⟩]` — Prevalid (closed app-of-top),
  but `.app .top .top` is *not* `WfM Γ` (Lemma 11: Top has no function
  supertype).
* `u = .fvar "x"` — WfM via `varEqu`.
* `v = .app .top .top` — the result of `.pro` + `.app(.top, .top)`
  congruence (the body reduces reflexively to itself).
* `WfM Γ v` is false (Lemma 11).

## What this means for `Lemma_10_Inversion` discharge

The proposal in `Pss.Mpss.WellFormed` (line 614-625 docstring) — close
the inversion lemma by invoking `WfM Γ t_w` via "preservation of `WfM`
under `MEqRed` at empty stack" — cannot be realized by the proposed
lemma. Specifically:

* `Lemma_6_EvaluationPreservesWf` (the `Step`-based analogue) is
  provable because the operational `Step` relation has no
  variable-promotion rule. `Step` is a purely syntactic rewrite that
  never consults the context. So the counterexample we exhibit here
  has no `Step`-analogue.
* `MEqRed`, in contrast, *does* consult the context (the `pro`
  constructor reads off an `≡`-binding). The bound term may have been
  validated only by `Prevalid` (structural), not by `WfM` (typing).

## Possible recovery strategies (none realized yet)

To make a preservation lemma true, one of the following structural
shifts must occur. Each is a substantial refactor:

1. **Strengthen `Prevalid` to `WfCtx`.** Require `≡`-bound annotations
   to be `WfM`-well-formed in the prefix. Mutually inductive with
   `WfM`. This makes context construction strictly harder (`Prevalid`
   currently only needs `fv` + `LC`); every existing `Prevalid` builder
   in the codebase would need a `WfM` payload.

2. **Strengthen the WfM rule `Wf-PrE`.** Require, in addition to
   `Γ.equBinds x α`, a witness that `WfM Γ α`. This is paper-non-faithful
   (paper Figure 4 only requires Prevalid + binding) and again forces
   the `WfM` recursion to recurse into stored annotations, breaking
   termination.

3. **Restrict the lemma's domain.** Only assert preservation under
   `MEqRed` derivations whose `pro` rule applications target an
   already-`WfM` bound term. This is a *predicate* on derivations
   ("pro-preserving derivations"), and is provable. But all the
   existing call sites of `Lemma_10_Inversion` would need to thread
   such a predicate through their inputs — non-trivial because
   `WSubMStar` does not expose its internal `MEqRed` derivations
   directly (only their endpoints).

4. **Bypass `WfM Γ t_w` entirely.** Find a different proof of
   `Lemma_10_Inversion` that does not require seeding the `WEquM` chain
   from `WEquM Γ t_w t_w` (rfl). E.g., a Church-Rosser-style
   confluence argument that produces `WEquM Γ t t'` directly from
   joinable annotation reducts without an intermediate WfM. The
   existing `WSubMStar.toMSub` strip already lands in a confluence
   diagram; what's missing is a proof that `MEqRedStar Γ [] t t_w` and
   `MEqRedStar Γ [] t' t_w` together yield `WEquM Γ t t'` *without* the
   WfM seed. This direction has not been investigated in detail.

## Status of `Lemma_10_Inversion`

Remains AXIOMATIZED. The blocker analysis in
`Pss.Mpss.WellFormed.Lemma_10_Inversion` should be updated to point at
this file: the natural discharge plan (preservation of `WfM` under
`MEqRed`) is structurally unavailable. The four recovery strategies
above are the only known paths forward; (4) (Church-Rosser bypass) is
the most promising because it does not require touching the `Prevalid`
/ `WfM` interface.

### Update (2026-05-04, agent_id `pss-20260504-strategy-a-audit`)

Strategy 4 (Church-Rosser bypass) was attempted as *Strategy A* —
direct induction on the `WSubMStar` derivation with `WEquM` chain
helpers. Result: **the `_sub` (single-`WSubM`) direction is fully
provable** (see `_Lemma_10_Inversion_sub_partial` in
`Pss.Mpss.WellFormed`, axiom-free), but the `_star`-`trs` case requires
`WEquM.trans`, which is **structurally isomorphic to the diamond /
confluence property of MEqRed at empty stack** — that property is
itself the source of the `Lemma_2_*` β-residuals.

Therefore Strategy 4 *also* requires β-residuals (just routed through
a different decomposition), and is not net-positive over the paper's
own proof (which goes through `Theorem 3 = transitivity elimination`).

The remaining viable paths:

* **Discharge the β-residuals first**, then the paper's proof becomes
  a clean discharge of `Lemma_10_Inversion`. (Strategy 5 in the AXIOMS.md
  entry for axiom #3.)
* **Restrict call sites to provide `trs`-free WSubMStar derivations**,
  then `_Lemma_10_Inversion_sub_partial` covers them. Requires
  auditing every `WSubMStar.trs` construction in the codebase.
* **Strategies 1-3 from the original list** (touching the `Prevalid` /
  `WfM` interface).

See the audit notes in `Pss.Mpss.WellFormed` §7.4 for the detailed
analysis of why Strategy A's `WEquM.trans` is impossible without
confluence.

## Related blockers

The same counterexample obstructs:

* **`Lemma_24_NarrowingMSubRed`** (in `Pss.Mpss.Narrowing`) — its
  Phase-B discharge plan also routes through a "WfM under MSubRed/MEqRed
  step" intermediate.
* **`Lemma_30_msPro_x_axiom`** (in `Pss.Mpss.Substitution`) — analogous
  preservation under variable promotion.
* **`Proposition_17_beta_axiom`** (in `Pss.Mpss.OperationalSem`) — the
  bridging lemma from `Step` to `MEqRed`. Although `Step` itself has no
  pro rule, the *image* in `MEqRed` may invoke pro along the way; the
  image-construction's well-formedness must therefore avoid the
  counterexample shape.

These three axioms are NOT independent — they share this fundamental
context-validity gap. A single recovery (e.g. strategy 1: `WfCtx`)
would unblock all three. Strategy 4 (Church-Rosser bypass) is
specific to `Lemma_10_Inversion`.
-/

namespace Pss

/-! ## §1. The witness context, term, and reduction -/

/-- The witness term: `(.app .top .top)`. Closed, locally closed, but
**not** `WfM` in any context (by Lemma 11). -/
private def _badTerm : Term := .app .top .top

/-- Local closure of the witness term. -/
private noncomputable def _badTerm_LC : Term.LC _badTerm :=
  Term.LC.app Term.LC.top Term.LC.top

/-- The witness context: a single `≡`-binding to the non-`WfM` term. -/
private def _badCtx : Ctx := [⟨"x", _badTerm, .equ⟩]

/-- The witness context is `Prevalid`. Only `fv ⊆ ∅` and `LC` are
required for `≡`-bindings; both are trivially satisfied because the
bound term is closed. -/
private noncomputable def _badCtx_Prevalid : Prevalid _badCtx :=
  Prevalid.equ Prevalid.empty
    (by simp [Ctx.dom])
    (by simp [_badTerm, Term.fv])
    _badTerm_LC

/-- The bound name `"x"` is bound to `_badTerm` via `≡`. -/
private theorem _badCtx_equBinds : _badCtx.equBinds "x" _badTerm := by
  simp [_badCtx]
  exact Ctx.equBinds_cons_self

/-- The empty stack is prevalid in the witness context. -/
private noncomputable def _badPrevalidExt : PrevalidExt _badCtx [] :=
  PrevalidExt.nil _badCtx_Prevalid

/-- The witness source term `u = .fvar "x"`. **Is `WfM`** via `varEqu`. -/
private noncomputable def _u_WfM : WfM _badCtx (.fvar "x") :=
  WfM.varEqu _badCtx_Prevalid _badCtx_equBinds

/-- Trivial reduction `MEqRed _badCtx [.top] .top .top`. -/
private noncomputable def _top_red_top_under_topStack :
    MEqRed _badCtx [.top] .top .top :=
  MEqRed.top
    (PrevalidExt.cons _badPrevalidExt Term.LC.top
      (by simp [Term.fv]))

/-- Trivial reduction `MEqRed _badCtx [] .top .top`. -/
private noncomputable def _top_red_top_empty :
    MEqRed _badCtx [] .top .top :=
  MEqRed.top _badPrevalidExt

/-- Reflexive reduction of `_badTerm` to itself via `app`-congruence. -/
private noncomputable def _badTerm_red_self :
    MEqRed _badCtx [] _badTerm _badTerm :=
  MEqRed.app _top_red_top_under_topStack _top_red_top_empty

/-- The witness reduction: `.fvar "x"` reduces to `_badTerm` via `pro`. -/
private noncomputable def _u_red_v :
    MEqRed _badCtx [] (.fvar "x") _badTerm :=
  MEqRed.pro _badPrevalidExt _badCtx_equBinds _badTerm_red_self

/-- **The witness target is NOT `WfM`.** From `WfM _badCtx _badTerm` we
would need (by `Wf-App` inversion) `WSubMStar _badCtx .top (.abs t .top)`
for some `t` — i.e. `Top` is a transitive well-subtype of an
abstraction. This contradicts `Lemma_11_TopHasNoFunctionSupertype`. -/
private theorem _v_NotWfM : WfM _badCtx _badTerm → False := by
  intro hwf
  -- Inversion on Wf-App: hwf : WfM Γ (.app .top .top) gives WSubMStar
  -- Γ .top (.abs t .top) for some t.
  cases hwf with
  | app hStarFn _hStarArg =>
    -- hStarFn : WSubMStar _badCtx .top (.abs _ .top)
    exact Lemma_11_TopHasNoFunctionSupertype hStarFn

/-! ## §2. The counterexample theorem

`Lemma_WfM_preservation_MEqRed` (the lemma proposed in the
`Lemma_10_Inversion` discharge plan) is FALSE. We exhibit
`Γ`, `u`, `v` such that `WfM Γ u`, `MEqRed Γ [] u v`, but `¬ WfM Γ v`. -/

/-- **Counterexample to the natural `WfM`-preservation lemma under
`MEqRed`.**

There exist `Γ`, `u`, `v` with:
1. `WfM Γ u`,
2. `MEqRed Γ [] u v`,
3. but `¬ WfM Γ v`.

Witness: `Γ = [⟨"x", .app .top .top, .equ⟩]`, `u = .fvar "x"`,
`v = .app .top .top`. The `≡`-binding stores a non-`WfM` (but
`Prevalid`-OK) term, and `MEqRed.pro` promotes `u` to that term.

Lean-checked. -/
noncomputable def Lemma_WfM_preservation_MEqRed_counterexample :
    Σ' (Γ : Ctx) (u v : Term),
      PProd (WfM Γ u) (PProd (MEqRed Γ [] u v) (WfM Γ v → False)) :=
  ⟨_badCtx, .fvar "x", _badTerm,
    ⟨_u_WfM, ⟨_u_red_v, _v_NotWfM⟩⟩⟩

end Pss
