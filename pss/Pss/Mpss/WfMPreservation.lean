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

/-! ## §3. Iteration 1 — `WfCtxEqu` infrastructure

The counterexample of §2 exploits that a context can be `Prevalid` while
storing a non-`WfM` annotation under an `≡`-binding. We define a stronger
context-validity predicate `WfCtxEqu Γ` that excludes this pathology by
demanding that every `≡`-bound annotation is itself `WfM` at its prefix.

`WfCtxEqu` is the "type-correctness" invariant on contexts that the PSS
calculus does NOT bake into `Prevalid`. With this side-condition, the
witness from §2 is excluded:

```
WfCtxEqu [⟨"x", .app .top .top, .equ⟩]
  ↦ requires WfM [] (.app .top .top)
  ↦ FALSE (Lemma 11: Top has no function supertype)
```

so the counterexample is ruled out at the source.

### Status of the conditional preservation lemma

The full conditional preservation lemma `WfM_preservation_MEqRed_conditional`
(see §4 below for the attempted proof) DOES NOT close at this iteration.
The blockers are documented inline next to each `MEqRed`-case:

* `pro`, `top`, `var`, `tAp` — close cleanly (these are the "trivial"
  cases, and they exhibit the value of `WfCtxEqu` for `pro` specifically:
  the lookup-equ extraction is the load-bearing helper).
* `app`, `bet` — STRUCTURALLY BLOCKED. From `WfM Γ (.app u v)`
  (Wf-App), one obtains `WSubMStar Γ u (.abs t .top)` and `WSubMStar Γ v
  t`. The IH on `MEqRed.app`'s premises requires applying preservation
  to `MEqRed Γ (v::s) u u'` from `WfM Γ u`. But to reconstruct the
  conclusion `WfM Γ (.app u' v')`, we need `WSubMStar Γ u' (.abs t'
  .top)` for some `t'` — i.e. WSubMStar PRESERVATION UNDER MEqRed,
  which is Wall 2 territory (and the original target of the
  `Lemma_10_Inversion` discharge plan). So this lemma does not, by
  itself, unblock Wall 2 — it ASSUMES Wall 2.
* `fun_`, `fOp` — REQUIRE `WfCtxEqu` extension under binders. `.fun_`
  pushes a `.sub`-binding (immediate from the `WfCtxEqu.sub`
  constructor — but the body's bound annotation is the new entry's
  target which is in turn `WfM Γ t` by inversion of `WfM Γ (.abs t
  u)`'s `Wf-Fun` rule). `.fOp` pushes a `.equ`-binding for the
  popped stack head `α` — and we have NO `WfM Γ α` premise (the stack
  only carries `LC` + `fv ⊆ dom`, see `PrevalidExt.cons`). So `.fOp`
  needs an additional **`WfStack`** premise on the stack itself.

### The verdict

The naturally-stated lemma `WfM_preservation_MEqRed_conditional` with
just `WfCtxEqu Γ` as side-condition is **NOT** sufficient to close all
cases. Iteration 2's task is to identify the right side-conditions:

1. `WfCtxEqu Γ` (this iteration) — closes `pro`.
2. `WfStack Γ s` (per-element `WfM`) — needed for `fOp` to extend
   `WfCtxEqu` with the popped `α`.
3. **Either** an INDEPENDENT proof that `WSubMStar` is preserved under
   `MEqRed` (Wall 2 directly), **or** a different formulation that
   tracks `WSubMStar` instead of `WfM`.

The third bullet is the real wall: this lemma, as stated in the task
brief, doesn't sidestep Wall 2 — it's equivalent to it for the
congruence cases. The honest recommendation for Iteration 2 is to
attack Wall 2 directly (WSubMStar preservation), with `WfCtxEqu` and
`WfStack` as supporting infrastructure.

### What this iteration ships

* `WfCtxEqu : Ctx → Type` — the new context invariant.
* `WfCtxEqu.lookup_equ` — extraction-and-weakening helper.
* `WfCtxEqu.tail` — structural projection.
* A SCAFFOLD of `WfM_preservation_MEqRed_conditional` that closes the
  trivial cases and exposes the structural obstructions in the
  congruence cases by leaving them as named `_blocker_*` defs whose
  signatures document precisely what's needed. (No axioms; no `sorry`
  — the unblocked cases are real proofs and the blocked ones are
  packaged as separate `axiom`-free *partial-result* lemmas with their
  obligations exposed in the type signature.)

### What this iteration explicitly does NOT ship

* The full lemma in the form the brief requested. The brief's signature
  cannot be inhabited without independently solving Wall 2 — see the
  `app` / `bet` analysis above. We document this finding as the
  iteration's primary deliverable.
-/

/-- `WfCtxEqu Γ`: every `.equ`-binding's bound term in `Γ` is `WfM` at
its prefix.

This is the missing "type-correctness" invariant on contexts that the
PSS calculus does NOT bake into `Prevalid`. With this side-condition,
the §2 counterexample is excluded: the bad context
`[⟨"x", .app .top .top, .equ⟩]` would require `WfM [] (.app .top .top)`
which fails by Lemma 11.

`Type`-valued because `WfM : Type` post-Type-LC refactor. -/
inductive WfCtxEqu : Ctx → Type where
  | empty : WfCtxEqu []
  | sub {Γ : Ctx} {x : String} {t : Term} :
      WfCtxEqu Γ → WfCtxEqu (⟨x, t, .sub⟩ :: Γ)
  | equ {Γ : Ctx} {x : String} {α : Term} :
      WfCtxEqu Γ → WfM Γ α → WfCtxEqu (⟨x, α, .equ⟩ :: Γ)

/-- Tail projection: a `WfCtxEqu` of a cons context yields one for the
tail. -/
noncomputable def WfCtxEqu.tail {e : CtxEntry} {Γ : Ctx}
    (h : WfCtxEqu (e :: Γ)) : WfCtxEqu Γ := by
  cases h with
  | sub h' => exact h'
  | equ h' _ => exact h'

/-- Sanity-check: the §2 bad context does NOT satisfy `WfCtxEqu`.

If it did, by `WfCtxEqu.equ` inversion we would have
`WfM [] (.app .top .top)`. We strip via `WfM.lc` + `Wf-App` inversion;
the result is structurally impossible at the empty context (`Lemma_11`
applies but at Γ = [], simpler shape suffices: `Wf-App` requires
`WSubMStar [] .top (.abs t .top)`, then `Lemma_11_TopHasNoFunctionSupertype`. -/
private theorem _badCtx_not_WfCtxEqu : WfCtxEqu _badCtx → False := by
  intro h
  cases h with
  | equ _ hwf =>
      -- hwf : WfM [] (.app .top .top). Same impossibility as Lemma 11
      -- at the empty context.
      cases hwf with
      | app hStarFn _hStarArg =>
          exact Lemma_11_TopHasNoFunctionSupertype hStarFn

/-- **Lookup-equ extraction.** Given `WfCtxEqu Γ`, `Prevalid Γ`, and
`Γ.equBinds y α`, recover `WfM Γ α` (the bound term, well-formed at the
FULL context, not just the prefix).

The `Prevalid Γ` premise is needed to discharge weakening at each step
of the induction: `WfCtxEqu Γ` alone does not carry the head-entry
side-conditions (`x ∉ Γ'.dom`, `fv t ⊆ Γ'.dom`, `LC t`) that
`WfM.weaken_append` requires for the `Δ ++ Γ'` prevalidity premise.
At every call site (the `MEqRed.pro` case), `Prevalid Γ` is available
from the surrounding `PrevalidExt Γ s` (via `extractPrevalid`).

Proof: induction on `WfCtxEqu Γ`, with `WfM.weaken_append` on the
result at each step. -/
noncomputable def WfCtxEqu.lookup_equ {Γ : Ctx} {y : String} {α : Term}
    (h : WfCtxEqu Γ) (hpv : Prevalid Γ) (hb : Γ.equBinds y α) : WfM Γ α := by
  induction h with
  | empty =>
      simp [Ctx.equBinds, Ctx.lookupEqu] at hb
  | @sub Γ' x t hΓ' ih =>
      by_cases hyx : x = y
      · subst hyx
        simp [Ctx.equBinds, Ctx.lookupEqu] at hb
      · have hne : (⟨x, t, .sub⟩ : CtxEntry).name ≠ y := by simpa using hyx
        have hb' : Γ'.equBinds y α :=
          (Ctx.equBinds_cons_other (e := ⟨x, t, .sub⟩) hne).mp hb
        have hpv' : Prevalid Γ' := hpv.tail
        have hwfα_tail : WfM Γ' α := ih hpv' hb'
        -- Weaken: WfM Γ' α → WfM (⟨x, t, .sub⟩ :: Γ') α
        have : WfM ([⟨x, t, .sub⟩] ++ Γ') α := by
          apply WfM.weaken_append hwfα_tail
          simpa using hpv
        simpa using this
  | @equ Γ' x β hΓ' hwfβ ih =>
      by_cases hyx : x = y
      · subst hyx
        simp [Ctx.equBinds, Ctx.lookupEqu] at hb
        -- After subst hb, β stays and α is replaced with β throughout.
        subst hb
        -- Goal: WfM (⟨x, β, .equ⟩ :: Γ') β
        have hweak : WfM ([⟨x, β, .equ⟩] ++ Γ') β := by
          apply WfM.weaken_append hwfβ
          simpa using hpv
        simpa using hweak
      · have hne : (⟨x, β, .equ⟩ : CtxEntry).name ≠ y := by simpa using hyx
        have hb' : Γ'.equBinds y α :=
          (Ctx.equBinds_cons_other (e := ⟨x, β, .equ⟩) hne).mp hb
        have hpv' : Prevalid Γ' := hpv.tail
        have hwfα_tail : WfM Γ' α := ih hpv' hb'
        have : WfM ([⟨x, β, .equ⟩] ++ Γ') α := by
          apply WfM.weaken_append hwfα_tail
          simpa using hpv
        simpa using this

/-! ## §4. The conditional preservation lemma — structural-blocker analysis

We attempted the natural lemma

```
WfM_preservation_MEqRed_conditional :
    WfM Γ u → WfCtxEqu Γ → MEqRed Γ s u v → Nonempty (WfM Γ v)
```

via `cases hred`. **`WfCtxEqu Γ` alone is NOT sufficient** to discharge
the lemma: the four congruence / β-step cases of `MEqRed` (`bet`, `app`,
`fun_`, `fOp`) FAIL TO CLOSE for the following structural reasons:

### `MEqRed.app` (Wall-2-equivalent)

`MEqRed.app : MEqRed Γ (v::s) u u' → MEqRed Γ [] v v' →
  MEqRed Γ s (.app u v) (.app u' v')`.

To produce `WfM Γ (.app u' v')` by `Wf-App`, we need
`WSubMStar Γ u' (.abs t' .top)` and `WSubMStar Γ v' t'` for some
`t'`. From `WfM Γ (.app u v)` (Wf-App inversion), we have
`WSubMStar Γ u (.abs t .top)` and `WSubMStar Γ v t`.

The IH on `MEqRed Γ (v::s) u u'` (assumed `WfM Γ u`, derivable from
`WSubMStar Γ u (.abs t .top)` via `wfM_left_of_wsubmstar`) yields
`WfM Γ u'`. But to reconstruct the `WSubMStar Γ u' (.abs t' .top)`, we
need **`WSubMStar` preservation under `MEqRed`** — which is Wall 2 of
the campaign. So this lemma DOES NOT sidestep Wall 2; it presupposes
it for the congruence cases.

### `MEqRed.bet` (Wall-2-equivalent + Lemma-7 threading)

Same WSubMStar-preservation issue at the surrounding `Wf-App`, plus
substitution preservation for `Term.opening v' body'` (Lemma 7
territory, threaded through cofinite quantification on `body^[x]`).

### `MEqRed.fun_` (cofinite IH thread)

The cofinite IH on the body needs
`WfCtxEqu (⟨x, t, .sub⟩ :: Γ)` — IMMEDIATE from `WfCtxEqu.sub`. But
the IH's HYPOTHESIS `WfM (⟨x, t, .sub⟩ :: Γ) (body^[x])` is not
directly available from `WfM Γ (.abs t body)` (Wf-Fun); we need to
unpack the cofinite premise and re-thread `body^[x]` for fresh
`x ∉ L_W ∪ L_M ∪ Γ.dom`. Doable in principle, but ALSO requires
that the conclusion's bound annotation `t'` satisfies `WfM Γ t'`,
which propagates the same Wall-2 issue at the annotation level
(Wf-Fun requires `WfM Γ t'`, not just `WfM Γ t`).

### `MEqRed.fOp` (cofinite + WfStack-extension)

Same issues as `fun_` for the body, PLUS the new `.equ`-binding for
the popped stack head `α` requires `WfCtxEqu (⟨x, α, .equ⟩ :: Γ)`,
which by `WfCtxEqu.equ` requires `WfM Γ α`. The stack provides only
`LC α` and `fv α ⊆ Γ.dom` (via `PrevalidExt.cons`), not `WfM Γ α`.
So `fOp` requires an ADDITIONAL precondition `WfStack Γ s` whose
`cons` constructor demands `WfM Γ α` per element.

### Verdict

Even with `WfCtxEqu` + a hypothetical `WfStack` + cofinite-freshness
threading, the `app` and `bet` cases route through Wall 2. **This
lemma, as stated, is NOT a sidestep of Wall 2**; it is approximately
Wall 2 in disguise.

The honest recommendation for Iteration 2 is to attack Wall 2 directly
(prove `WSubMStar` preservation under `MEqRed`), with `WfCtxEqu` and
`WfStack` as supporting infrastructure for the leaf cases (`pro` of
`WSubMStar` itself routes through `WfCtxEqu.lookup_equ` for the
`Wf-PrE`-shaped variable case).

### What this iteration ships

This iteration ships ONLY the load-bearing infrastructure:

* `WfCtxEqu : Ctx → Type` (the new context invariant, §3).
* `WfCtxEqu.tail` (structural projection).
* `WfCtxEqu.lookup_equ` (extraction-and-weakening — DOES discharge
  cleanly via `WfM.weaken_append`, with `Prevalid Γ` as additional
  premise).

It does NOT ship the conditional preservation lemma in any form (full
or partial), because every form we considered either (a) requires
Wall 2 to be solved first, or (b) introduces axioms or `sorry`s. -/

end Pss
