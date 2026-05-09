# PSS / MPSS Lean 4 Formalization Plan

> Authoritative plan for this formalization. All sub-agents must read this file before starting work and follow the conventions below verbatim.
>
> **SCOPE UPDATE (post-Wave-5 dispatch):** This plan was originally written to mechanize BOTH Hutchins' declarative+algorithmic system AND the MPSS Krivine reformulation. After confirming MPSS supersedes all of Hutchins' algorithmic machinery and metatheory (see README.md "Scope" section), we have **trimmed to KAM-only**. The following modules listed below have been DELETED and should not be re-introduced: `Pss/Algo/*` (all six files), `Pss/Decl/*` (all three files), `Pss/Bridge/*`. Sub-agents should ignore §3 entries for those paths and treat the corresponding waves (4C, 5D, 7C, and the Hutchins parts of 3D) as out of scope. Wave 7 retains only `TransitivityElim`, `MPSS TypeSafety`, and polish.

---

## CAMPAIGN ENDPOINT STATE (post-iter pss-20260506-130802)

> **All eight de Bruijn `_proved` headlines have shipped.** This section
> captures the campaign's current endpoint: the headline theorems are in
> their final structural form on the de Bruijn side; what remains is to
> discharge the named `Prop`/`Type` residual hypotheses they take as
> arguments. The de Bruijn `_proved` endpoints depend only on kernel
> axioms (`propext`, `Quot.sound`, `Classical.choice`) plus those named
> hypotheses — there are no de-Bruijn-side custom `axiom` declarations.

### The eight de Bruijn `_proved` headlines (PRIMARY)

`Pss/Sanity.lean` audits the following as the campaign's primary
proof-status endpoints. Each is a `noncomputable def` / `theorem` taking
the listed named residual hypotheses as explicit arguments and producing
the headline conclusion modulo the kernel three.

| Endpoint | Residual hypotheses |
|---|---|
| `Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityStar_proved` | `UniformStrongCommutes` |
| `Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityChain_proved` | `UniformStrongCommutes` |
| `Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedStar_proved` | `MEqRedArgTransportPayload`, `MEqRedOpStackHeadTransportPayload`, `MEqRedSubBridgePayload`, `UniformEqDiamonds` |
| `Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedChain_proved` | `MEqRedArgTransportPayload`, `MEqRedOpStackHeadTransportPayload`, `MEqRedSubBridgePayload`, `UniformEqDiamonds` |
| `Pss.DeBruijn.Theorem_3_DeBruijn_TransitivityIsAdmissible_proved` | `UniformStrongCommutes` |
| `Pss.DeBruijn.Theorem_4_DeBruijn_Progress_proved` | `UniformStrongCommutes` |
| `Pss.DeBruijn.Theorem_5_DeBruijn_Preservation_proved` | `BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`, `WfMSubHeadReplaceOfNewWf` |
| `Pss.DeBruijn.Theorem_5_DeBruijn_ClosedPreservation_proved` | `BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`, `WfMSubHeadReplaceOfNewWf` |

`#print axioms` on each of the above produces the kernel-three baseline
only; the residual hypothesis names appear in the theorem signature, not
in the axiom closure. This is the structural shape `AXIOMS.md` describes
under "De Bruijn primary headlines".

### Residual hypothesis taxonomy

The named residuals partition into three sources by what closes them.

#### A. Standing transitivity-elimination residuals

These are the open metatheoretic problems on which the headline closures
are conditional — the universal single-step companion of the relation
the headline lifts to chain output.

* `UniformStrongCommutes : Prop` — universal single-step `StrongCommutes
  Γ s` at every extended context. Defined in
  `DeBruijnTypeSafety.lean:21202`. Consumed by Lemma 1 / Theorem 3 /
  Theorem 4 closures.
* `UniformEqDiamonds : Prop` — universal single-step `EqDiamonds Γ s` at
  every extended context. Defined in `DeBruijnTypeSafety.lean:20215`.
  Consumed by Lemma 2 closures.

These are the hardest residuals; their discharge requires closing the
single-step case grid (~36 cells per side after `app × app` /
`bet × bet` / `app × bet` / `bet × app` are unblocked by per-cell
transports below).

#### B. Theorem 5 operational residuals (subject-reduction-class)

Independent of the transitivity-elimination problem. Each is needed
specifically to propagate well-formedness across a single operational
step.

* `BetaInstantiationPreservesWfM : Type` — de Bruijn analogue of paper
  Lemma 7. Defined in `DeBruijnTypeSafety.lean:193`. Substituting an
  argument into an abstraction body preserves well-formedness when the
  argument is a well-subtype of the abstraction bound.
* `AbsFunctionBoundInversion : Type` — function-bound inversion: if
  `WSubMStar Γ (.abs bound body) (.abs result .top)`, then bounds are
  transitively well-equivalent. Defined in
  `DeBruijnTypeSafety.lean:4043`.
* `WfMSubHeadReplaceOfNewWf : Type` — sharpened `.sub`-head replacement,
  carrying the assumption that the replacement bound is already
  well-formed. Defined in `DeBruijnTypeSafety.lean:10890`.

#### C. Per-cell transport residuals (unblock A above)

These are not consumed by any headline directly — they are consumed by
the per-cell `EqDiamonds.*_chain_of` and `StrongCommutes.*_chain_of`
helpers that case-split inside `UniformEqDiamonds` /
`UniformStrongCommutes`. Discharging them shrinks the per-cell residual
list inside the case grid.

* `MEqRedArgTransportPayload` — argument-position transport across
  argument chain. Restricted form `MEqRedArgTransportPayloadRestricted_proved`
  proved for `Term.NoBinders` argument + `Term.AbsFree` body shape;
  newer `MEqRedArgTransportPayloadNoBinders_proved` removes the body-side
  `AbsFree` condition when the argument is `NoBinders`.
* `MEqRedOpStackHeadTransportPayload` — operator stack-head transport
  for `MEqRed`. Restricted form `MEqRedOpStackHeadTransportPayloadRestricted_proved`
  proved.
* `MEqRedSubBridgePayload` — `.equ → .sub` head bridge for `MEqRed`
  bodies. Restricted form `MEqRedSubBridgePayloadNoBinders_proved`
  proved for `Term.NoBinders` body sources.
* `MSubRedOpStackHeadTransportPayload` — analogous operator stack-head
  transport for `MSubRed`. Restricted form
  `MSubRedOpStackHeadTransportPayloadRestricted_proved` proved (commit
  `20614` line of `DeBruijnTypeSafety.lean`).
* `MSubBridgePayload` — cross-relation, cross-head bridge: `MSubRed`
  body step under `.equ`-head into `MEqRed` body step under `.sub`-head
  with the original abstraction bound. NoBinders-as-Sub variant
  `MSubBridgePayloadNoBindersAsSub_proved` proved; equivalence-side
  variant `MSubBridgePayloadEquNoBinders_proved` proved.
* `MSubBodyNarrowPayload` — `.sub`-head abstraction-bound narrowing for
  `MSubRed` bodies. NoBinders variant `MSubBodyNarrowPayloadNoBinders_proved`
  proved.

### Partial discharges shipped (this iteration cluster)

The following named `_proved` / `_partial` payloads ship the
restricted-form discharges for the per-cell residuals above and some
constructor-level discharges for `BetaInstantiationPreservesWfM`. They
are reachable from `Pss/DeBruijnSanity.lean`'s `#print axioms` audit.

| Payload | Status |
|---|---|
| `MEqRedArgTransportPayloadRestricted_proved` | proved (`NoBinders` arg + `AbsFree` body) |
| `MEqRedArgTransportPayloadNoBinders_proved` | proved (`NoBinders` arg, drops body condition) |
| `MEqRedOpStackHeadTransportPayloadRestricted_proved` | proved |
| `MEqRedSubBridgePayloadNoBinders_proved` | proved (`NoBinders` body) |
| `MSubRedOpStackHeadTransportPayloadRestricted_proved` | proved |
| `MSubRedSubBridgePayloadNoBinders_proved` | proved (`NoBinders` body, MSubRed side) |
| `MSubBridgePayloadEquNoBinders_proved` | proved |
| `MSubBridgePayloadNoBindersAsSub_proved` | proved |
| `MSubBodyNarrowPayloadNoBinders_proved` | proved |
| `MEqRedPreservesWfM_partial` | proved-with-hypotheses; `top`/`var`/`tAp` arms unconditional, `pro`/`bet`/`app`/`fun_` arms left as named hypotheses (commit `4b547d0`) |
| `MEqRedStarArgTransportRestricted_proved` | proved |
| `MEqRedFusedKindNarrowedBetaSubstStack_proved` | proved (commit `98a62a2`) |
| `MEqRedRespectsBetaInstantiateStack_proved` | proved (commit `a5aaf59`) |
| `BetaInstantiationPreservesMEqRedStack_proved` | proved (commit `7ec6954`) |
| Per-cell `EqDiamonds.*_chain_NoBinders_of`, `EqDiamonds.*_chain_AbsFree_of`, `EqDiamonds.*_chain_ArgNoBinders_of`, `EqDiamonds.*_chain_ArgBodyNoBinders_of` | proved per their preconditions |
| Per-cell `StrongCommutes.equ_bet_chain_ArgNoBinders_of`, `.app_bet_chain_ArgNoBinders_of`, `.equ_bet_chain_ArgBodyNoBinders_of` | proved per their preconditions |

Search `git log --oneline --all --grep="_NoBinders_\|_AbsFree_\|_partial\|_Restricted_proved"` for the full audit
trail of partial-discharge commits.

### Next concrete attacks (hardest case first)

Per CLAUDE.md §5a "Hardest case first", the priority order for further
discharge is:

1. **`UniformStrongCommutes` (Lemma 1 / Theorem 3 / Theorem 4 single-step).**
   The hardest standing residual: closing the full `MSubRed × MEqRed`
   case grid as an unconditional `StrongCommutes Γ s` at every extended
   context. The `app × app`, `bet × bet`, `app × bet`, `bet × app`
   binder cases reduce to: (i) the per-cell transport residuals in
   group C above, and (ii) inner recursive calls to the same
   `StrongCommutes` at deeper-stack contexts. The de Bruijn switch
   eliminated the alpha-equivariance wall here; what remains is
   structural recursion plus the open per-cell payloads. Discharging
   this falls Theorem 3 and Theorem 4 in lockstep.
   Current fine-grained blocker in the `fun/fun` body `Ms-App × Me-App`
   branch: the exposed changed-head and stable-successor `Ms-Pro`
   app-spine leaves have now been routed through the generic spine
   wrappers and wired into
   `StrongCommutes_proved_of_split_chain_fun_app_sub_cases_nested_app_handlers`.
   Direct leaf calls to `changedHeadProAppSpineJoin` and
   `stableSuccProAppSpineJoin` are gone; only their helper-layer
   implementations still call the lower-level joins. The next visible
   residual in that handler is the deeper recursive
   `Ms-App` payload
   `StrongCommutesFunFunBodyAppAppSubAppAppAppAppAppAppAppAppAppAppAppAppAppAppChainPayload`,
   plus the remaining `Ms-FOp` payload family. The next productive local
   proof step is to discharge the remaining constructor-local leaves of the
   generic nonempty app-spine split
   `StrongCommutesFunFunBodyAppAppSubAppSpineConsChainPayload.of_nested_cases_pro_split`.
   This split avoids extending the fixed-depth ladder again: the changed-
   head lookup, stable-successor lookup, `Ms-Top`, `Ms-Equ`, recursive
   `Ms-App`, and `Ms-FOp` obligations are now exposed as separate cons-
   spine payloads. The changed-head leaf is structurally reduced to
   `StrongCommutesFunFunBodyAppAppSubAppSpineConsProHeadBodyJoinPayload`,
   which isolates the missing generic inversion/transport of the right
   `MEqRed` app-spine step into body-level joins. The previous direct
   generic split over a stack written as `args ++ [v]` failed in the
   `Ms-FOp` arm, because `MSubRed.fOp` consumes the stack head as its
   operand (`α :: s`); the active split uses the explicit-head shape needed
   by that constructor.

2. **`UniformEqDiamonds` (Lemma 2 single-step).** Same shape as (1) on
   the `MEqRed × MEqRed` side. Smaller case grid; many cells already
   shipped (`top`, `var`, `pro_pro`, `tAp_*`, `appTop_*`, `app_app`,
   `fun_fun`, `fOp_fOp`). The cross-β cells (`bet × bet`, `bet × app`,
   `app × bet`) consume `MEqRedArgTransportPayload` /
   `MEqRedSubBridgePayload`; restricted variants are shipped per the
   table above.

3. **Per-cell transport residuals (group C).** Each of
   `MEqRedArgTransportPayload`, `MEqRedOpStackHeadTransportPayload`,
   `MEqRedSubBridgePayload`, `MSubRedOpStackHeadTransportPayload`,
   `MSubBridgePayload`, `MSubBodyNarrowPayload` has a restricted form
   shipped; widening each to the full general statement is the path to
   removing the restricted-vs-general gap on the binder cells of (1)
   and (2). Hardest-first within this group: `MSubBridgePayload`
   (cross-relation cross-head bridge collapsing `Ms-Pro` / `Ms-Top` /
   `Ms-FOp` into `MEqRed`).

4. **`BetaInstantiationPreservesWfM` (Theorem 5).**
   `MEqRedPreservesWfM_partial` ships the trivial three constructor
   arms; the four named hypotheses (`pro`, `bet`, `app`, `fun_`) are
   left explicit. The `bet` arm is the hardest — it requires the
   subject-reduction-class substitution lemma. The `pro` and `app`
   arms reduce to chain-IH composition once `MEqRedPreservesWfM` is
   itself proved at the recursive call site.

5. **`AbsFunctionBoundInversion`, `WfMSubHeadReplaceOfNewWf`
   (Theorem 5).** Independent of (1)–(4); each is its own structural
   discharge. Less load-bearing than (4) for the headline closure
   shape.

The campaign's success metric is each `_proved` headline becoming
unconditional in lockstep as residuals are discharged — no downstream
call sites change because the residual hypotheses are explicit
arguments, not axioms or implicit instances.

---

## DISCHARGE CAMPAIGN STATUS (post-Wave-7)

> **All seven waves are complete.** The project is now in a sustained
> discharge campaign aimed at peeling residual axioms off the headline
> theorems. This section captures where we started, where we are now,
> and the two unblocking options that the campaign has identified.

> **Strategic pivot 2026-05-06 (iter pss-20260506-130802):** A degenerate
> per-depth ladder pattern (`BetaInstantiationPreservesMEqRedUnderNHeadsStack`
> for N = 1..37, ~30k+ lines) was halted and replaced with one universal
> theorem `BetaInstantiationPreservesMEqRedUnderHeadsStack_universal :
> ∀n, ...` (commit `327ae8e`). The 36-depth concrete ladder was deleted
> in commit `da6fedd`; the closed surface
> `BetaInstantiationPreservesMEqRedStack_proved` is now unconditional
> (commit `7ec6954`). `Pss/Mpss/DeBruijnTypeSafety.lean` shrunk
> 51,125 → 14,812 lines. The diagnosis (binder cases recurse to depth N+1,
> so per-depth proofs are divergent by construction) and the fix (induct
> on the derivation with `heads`/`n` generalized in the IH) are documented
> in feedback_no_per_depth_ladders.md.
>
> **Subsequent dispatches in same iter:** Symmetric β-substitution
> `MEqRedRespectsBetaInstantiateStack_proved` shipped (commit `a5aaf59`,
> 518 lines). Asymmetric variant walls at `var i = heads.length` because
> stack-extension is not generally valid for `fun_`-rooted derivations.
> EqDiamonds and StrongCommutes binder cells `fun_×fun_` and `fOp×fOp`
> shipped (commits `c4c18ac`, `fe241b0`).
>
> **Wall identified 2026-05-06:** Both `EqDiamonds.app_app_of` and the β
> cells need **stack-head replacement** for `MEqRed`: `MEqRed Γ (old::s) u u'`
> + `MEqRed Γ [] old new` → `MEqRed Γ (new::s) u u'`. Investigation
> (agent `a07fa798dfbd8fb0e`) shows this is NOT a free-standing structural
> theorem in de Bruijn — the `fOp` case (where stack head is consumed into
> a `.equ` binder) requires diamond-joining `α → α'` against `α → new → new'`,
> a confluence-shaped recursion. **The wall is structurally distinct from
> LN's wall** (which was CAPSU/cofinite); de Bruijn's wall is the
> equ-bound-replacement-confluence. Recommended path forward: D3 from
> investigation report — restructure `EqDiamonds_core` with a term-size
> outer induction (matching the LN-era `_inline_app`'s `ihu`/`ihv` pattern,
> which LN couldn't use because of CAPSU but de Bruijn can since body
> sub-derivations are single proof trees). Estimate: 700-900 lines,
> 4-6 dispatches.
>
> **Subtlety:** Paper's Lemma 32 uses `.equ` head (`Γ, x ≡ v, Γ'`); MPSS
> Me-Bet body lives in `.sub` head (`Γ, x ≤ t`). The bet × bet diamond
> closure has an unaccounted-for sub-to-equ binder kind transition that
> needs a separate helper. The kind-narrowing helper
> `MEqRed.sub_to_equ_head_replace` shipped in commit `8e72b12`
> (`Pss/Mpss/DeBruijnReductions.lean:1953`) provides this bridge for
> the MEqRed side. The MSubRed-side variant is genuinely false in
> general (counterexample documented in AXIOMS.md).
>
> **Parallel reduction is not a backup architecture** (investigation
> agent `a78d8da4b2d52d871`, 2026-05-06). The de Bruijn `MEqRed` is
> already a Tait-Martin-Löf parallel reduction — its `bet` rule's body
> sub-derivation is an `MEqRed` and can fire arbitrary nested redexes
> in one step. Introducing a separate `MParRed` would re-derive the
> same walls (stack-head replacement, `var i=0` stack-extension for
> `fun_`-rooted `arg`) with renamed identifiers — ~2.5-4.5k lines of
> zero-progress work. The walls are properties of the constructor
> signatures (`fun_` requires empty stack, `app` shares `v` between
> operator stack head and operand source). **If Path B walls, the
> recommended fallback is Path A (change `MEqRed.bet`'s body context
> from `.sub t` to `.equ v`), not parallel reduction.** Past planning
> at `Pss/Util/ParRed.lean` recognized this — generic Takahashi
> sandwich infrastructure exists but was never instantiated for
> `MEqRed` because the paper's relation is already parallel.
>
> **Fused β-substitution shipped (commit `98a62a2`, +514 lines):**
> `MEqRedFusedKindNarrowedBetaSubstStack_proved` is the kind-narrowed
> (sub→equ + uniform substitution by `arg'`) single-MEqRed-step
> β-substitution. **The fully asymmetric form (LHS by `arg`, RHS by
> `arg'`) is mathematically foreclosed** at single MEqRed step:
> `MEqRed.fOp` requires the body-binder `α` and stack-head `α` to be
> syntactically identical, but asymmetric substitution forces them
> to be `α[arg/n]` vs `α[arg'/n]` when `α` references the discharged
> binder. Same blocker at `Me-Pro`. The shipped lemma uniformly
> substitutes by `arg'` on both sides, with the dropped `.sub` head's
> bound `arg` decoupled from the substitution.
>
> **Implication for the case grid:** `bet × bet`, `bet × app`, and
> `app × bet` cells require `MEqRedStar` (chain) output, NOT
> single-step `MEqRedJ`. This contradicts the current `EqDiamonds Γ s`
> definition's single-step shape. The LN axiom
> `Lemma_2_inline_bet_residual_axiom` is also stated at single-step
> output and unproven for the same reason. Three resolution paths
> for the next major work: (i) restate `EqDiamonds` with chain
> output (downstream `diamond_eqStar_eqStar_of` consumers change);
> (ii) use `MSub`-style chain abstraction directly for these cells;
> (iii) future analysis finds unforeseen single-step closure.
>
> LN-side headline axioms are unchanged because the de Bruijn proofs
> don't yet bridge to LN; the bridge is post-Phase-5 work per CLAUDE.md
> "NEXT MAJOR WORK".

### Where we started

Waves 0–7 landed the full module hierarchy (per §3 below) with
Lemma 1, Lemma 2, and several Wave-7 lemmas as **monolithic axioms**.
Headline theorems (Theorems 3, 4, 5) were stated as conditional theorems
on those monoliths plus on `Conjecture_8`.

### Where we are now (12 remaining axioms, all narrow)

Lemma 1 and Lemma 2 are now **theorems**. The monolithic axioms have
been replaced by:

* **3 narrow per-cell β-residual axioms** (Lemma 2): one ctx-axiom +
  two `inline_*_bet_residual_axiom`s for the β-step diagonal;
* **2 narrow per-cell β-residual axioms** (Lemma 1): one ctx-axiom +
  one `inline_app_bet_residual` for Ms-App × Me-Bet.

Plus the pre-existing axioms that did not change shape:

* `Conjecture_8` (paper-permanent, now UNUSED by headline closure);
* `Lemma_24_NarrowingMSubRed` (cycle-blocked, see file analysis);
* `Lemma_10_Inversion` (blocked on `WfM`-preservation under `MEqRed`);
* `Lemma_10_InversionRestricted` (legacy, inactive);
* `Lemma_30_msPro_x_axiom` (leaf discharged via `msAvoidsPro`; awaits
  threading through `TypeSafety._S_lf2`);
* `Lemma_32_AsymmetricEqu` (inactive asymmetric substitution bridge);
* `Proposition_17_beta_axiom` (LN-encoding obstacle on `MEqRed.refl`).

12 total. See `AXIOMS.md` for per-axiom statements, paper refs, blocker
analyses, complexity estimates, and discharge plans.

### The 12 axioms by category

* **1 permanent (paper-conjecture status):** `Conjecture_8_*`.
* **9 active outstanding (in headline closures):**
  `Lemma_24_NarrowingMSubRed`, `Lemma_10_Inversion`,
  `Lemma_30_msPro_x_axiom`, `Proposition_17_beta_axiom`,
  `Lemma_1_ctx_axiom`, `Lemma_1_inline_app_bet_residual`,
  `Lemma_2_DiamondMEqRed_ctx_axiom`,
  `Lemma_2_inline_app_bet_residual_axiom`,
  `Lemma_2_inline_bet_residual_axiom`.
* **2 inactive outstanding (no headline depends on these):**
  `Lemma_10_InversionRestricted`, `Lemma_32_AsymmetricEqu`.

`Pss.Sanity` additionally audits the conditional WfCtx preservation
endpoints. Those are public preservation variants, but they are not part
of the five-headline count above; their current closures inherit the
subject-reduction residuals `_SR_axiom_app_meApp` and `_SR_v2_bet_residual`
instead of `Lemma_10_Inversion`.

### Unblocking options — historical (now superseded by de Bruijn pivot)

The campaign explored several paths through iter-32. All walled at the
same fundamental obstacle: **the cofinite quantifier on
`MEqRed.bet`/`fun_`/`fOp`'s body is a function with no a priori
uniformity guarantee, and `MEqRed.tAp`/`app` constructors require
`fv ⊆ Γ.dom` premises that fail for stray cofinite witnesses.**

The historical paths attempted:

1. **Option A — keep grinding** (Phases 1–28). Each axiom required
   multiple sessions. Walled on alpha-equivariance and term-size
   induction.
2. **Option B — Type-LC refactor** (commit `64162c2`). Lifted `Term.LC`
   from `Prop` to `Type`. Discharged `avoidsPro_refl` (axiom #12). Did
   NOT move the 5 β-residuals — they require restructuring `_core`'s
   induction scheme, which depends on machinery still walled by
   alpha-equivariance.
3. **AvoidsProUniv (Phase 5a–5g)** — `Type`-valued universal
   alpha-equivariance predicate. Phase 5g.3b proved structurally
   impossible (Lean rejects mutual `Type`/`Prop` blocks; mutual indices
   can't reference neighbors).
4. **Lever A — open-target descent functor (iter-29 through iter-32).**
   Built `Term.openInverse` infrastructure and `MEqRed.openInverse_descend`
   skeleton with 3 honest arms (`top`, `var`, `pro`). **Walled at the
   `tAp` arm (commit `5f2c58c`)** with a Lean-checked counterexample:
   the output requires `MEqRed Γ s (.app .top (.fvar z)) .top` for stray
   `z ∉ Γ.dom`, which `MEqRed.tAp`'s `fv u ⊆ Γ.dom` premise makes
   uninhabitable. Same wall affects `app`/`bet`/`fun_`/`fOp` arms.
5. **Lever B — alpha-equivariance renaming functor.** Audit at iter-31
   (commit `bad6651`) found it has the same structural wall as Lever A
   in disguise. Dispreferred and not attempted.

### Decision (iter-32 — sealed): switch to de Bruijn

The five β-residual axioms are **provably not closeable** in the current
encoding without a major refactor. Three remaining options were on the
table:

1. **Existence-form composition (Lever A continuation)** — DEAD per
   iter-32 counterexample.
2. **Setoid quotient on derivations** — experimental viability,
   speculative.
3. **De Bruijn re-encoding** — well-understood, eliminates the cofinite
   quantifier wall by collapsing `∀ y ∉ L, MEqRed Γ s (body^[y])
   (body'^[y])` to a single `MEqRed (β :: Γ) s body body'`.

**The user's authoritative direction (iter-32):** commit to de Bruijn.
"de Bruijn indices are a more organised approach which leads to cleaner
codebases and will reduce our tech debt."

See `CLAUDE.md` "NEXT MAJOR WORK — de Bruijn refactor" for the phase
plan, scope estimate (35–60 dispatches), atomic-switch constraint, and
hard caveats.

### Recommended order (post-iter-32)

1. **Phase 1 — DeBruijn.lean syntax core.** Ship the new `Term`
   inductive (`bvar (Nat)`, `top`, `app`, `abs`) plus
   `instantiate`/`shift` operations and 4–6 algebraic lemmas. No
   `MEqRed` work yet. Branch `db-refactor` from `pss`.
   * **Started 2026-05-04 on `db-refactor`:** `Pss/Syntax/DeBruijn.lean`
     now provides the standalone `Pss.DeBruijn.Term` core, `size`,
     `shiftBy`, one-step `shift`, `instantiate`, and five named algebraic
     lemmas. It also provides Type-valued `Scoped`/`Closed` plus
     preservation lemmas for shift and instantiate, shift composition,
     scoped-shift identity, closed β-instantiation, scoped
     constructor/inversion helpers (`bvar`, `abs`, `app`), instantiation
     freshness/no-op lemmas, and raw scoped weakening. `Scoped : Type`
     is intentional, matching the existing `Term.LC : Type` design
     needed by Type-valued MPSS reductions. The module is imported by
     `Pss.lean`; the
     locally-nameless development remains untouched until the downstream
     atomic switch.
2. **Phase 2 — substitution machinery.** Index-shifting lemmas, lift,
   strengthen. Replaces named `Term.subst`.
   * **Started 2026-05-04 on `db-refactor`:** `Pss/Syntax/DeBruijn.lean`
     now includes the first shift/substitution interaction lemmas:
     cancellation of one shift unit by instantiation, binder-lift
     commutation, and `shiftBy_instantiate`.
     `Pss/Reduction/DeBruijnOperational.lean` now ports the plain
     operational small-step relation as depth-indexed `StepAt`, with
     closed alias `Step`, β via `Term.instantiate 0`, direct
     abstraction-body stepping at `depth + 1`, source/target scoping
     accessors, application inversion, and star closures.
     `Pss/Mpss/DeBruijnOperationalSem.lean` proves the de Bruijn
     Proposition 17 bridge `MEqRed.of_StepAt` / `.of_Step`, including
     the β case via `MEqRed.bet` under the indexed subtype head.
3. **Phase 3 — context + reductions.** Rewrite `Reductions.lean`,
   delete most of `Renaming.lean`, port `Prevalid` / `Weakening` /
   `ContextRed` to indices.
   * **Seeded 2026-05-04 on `db-refactor`:** `Pss/Context/DeBruijn.lean`
     defines nameless context entries, index-based `.sub` / `.equ`
     lookup, binding predicates, stacks, and extended contexts. This is
     standalone and does not alter the locally-nameless context modules.
     It also now includes Type-valued `Prevalid` / `PrevalidExt`,
     successful-lookup depth lemmas, scoped lookup lemmas, and stack
     prevalidity destructors.
   * **Reduction skeleton seeded 2026-05-04 on `db-refactor`:**
     `Pss/Mpss/DeBruijnReductions.lean` defines standalone de Bruijn
     `MEqRed` / `MSubRed`, Prop wrappers, star closures, and basic
     source/target scoping invariants. Binder rules use single body
     derivations under extended nameless contexts rather than cofinite
     fresh-name functions.
     `MEqRed.refl` is now a direct structural recursion on
     Type-valued `Term.Scoped`; `MSubRed.refl` follows by `Ms-Equ`.
     Head-context extension now shifts outer stack operands under the
     new innermost binding (`Stack.shift 0 s`) in the binder rules.
     Context lookup now returns bounds lifted into the current context;
     raw stored bounds remain scoped in each entry's tail.
     Lookup weakening under a new head is available for raw, `.sub`, and
     `.equ` lookups.
     Context insertion under an existing binder head is now started:
     `CtxEntry.shift`, `Ctx.insertUnderHeadIndex`,
     `Prevalid.weaken_tail_head`, `PrevalidExt.weaken_tail_head`, and
     `.sub` / `.equ` lookup weakening under that insertion shape are
     available. Full reduction weakening still needs the term-level
     shift/substitution equalities that connect the β result across this
     insertion; the first such equality,
     `Term.instantiate_shift_succ` / `instantiate_zero_shift_one`, and
     stack shift commutation lemmas have now been seeded.
     Attempting the next `MEqRed` weakening helper exposed the expected
     nested-binder generalization: after descending through another
     abstraction, insertion happens under two preserved heads, so
     `Prevalid.weaken_second_tail_head`,
     `PrevalidExt.weaken_second_tail_head`, and the corresponding
     index-shift descriptions are now available. The remaining lookup
     transport should be generalized as insertion-at-depth rather than
     accumulated one-off lemmas. The first generalized piece is now in
     place as `Ctx.insertAtIndex` and `Ctx.shift_bvar_insertAtIndex`,
     with the one- and two-head index translations reduced to that common
     definition. The matching context transformer `Ctx.insertAt` is also
     in place, with simp lemmas for the zero/one/two-head shapes and
     `Ctx.depth_insertAt_of_le`; raw lookup now has
     `Ctx.lookup_insertAt_self` for finding the inserted entry at the
     insertion cutoff. Lookup transport for bindings at or outside the
     insertion cutoff is now available as `Ctx.lookup_insertAt_after`,
     `Ctx.subBinds_insertAt_after`, and `Ctx.equBinds_insertAt_after`.
     The complementary raw preserved-head fact
     `Ctx.lookup_insertAt_before` is available. The kind-specific
     preserved-head transports are also available as
     `Ctx.subBinds_insertAt_before` and `Ctx.equBinds_insertAt_before`;
     they preserve the original index and shift the returned bound at
     the insertion cutoff. General prevalid context insertion is now
     available as `Prevalid.insertAt`, taking a prevalid witness for the
     inserted entry over the actual insertion tail. Extended-context
     insertion is available as `PrevalidExt.insertAt`, shifting stack
     operands at the same cutoff. Reduction-facing lookup transport is
     now seeded via `Ctx.subBinds_insertAt_after_shift` and
     `Ctx.equBinds_insertAt_after_shift`, which present after-cutoff
     bindings as `Term.shift cutoff` rather than only `Term.shift 0`.
     `Ctx.insertAtIndex_lt_depth` handles shifted variable bounds.
     Syntax now has `Term.shiftBy_instantiate_lt`,
     `Term.shift_instantiate_lt`, and `Term.shift_instantiate_zero`,
     covering the β-target rewrite needed when weakening reductions under
     inserted context entries. One-step aliases `Term.shift_shift_zero`
     and `Stack.shift_shift_zero` name the corresponding binder-stack
     commutation shape.
     The de Bruijn `MEqRed.fOp` / `MSubRed.fOp` constructors now carry
     an explicit `Term.Scoped Γ.depth α` operand premise, which is needed
     to rebuild the `.equ` head when reductions are weakened through
     `Ctx.insertAt`.
     Constructor-level insertion wrappers are now available for the
     non-recursive and one-recursive cases of de Bruijn reductions:
     `MEqRed.var_insertAt`, `pro_insertAt`, `top_insertAt`,
     `tAp_insertAt`, `app_insertAt`, `fun_insertAt`, `bet_insertAt`,
     `fOp_insertAt`, and matching `MSubRed` wrappers for
     `pro`/`top`/`equ`/`app`/`fun`/`fOp`. The remaining full weakening
     theorem is now a prevalidity-threading induction over these wrappers.
     An initial fixed-outer-`Γ` attempt at `MEqRed.insertAt` exposed the
     correct theorem shape: `Γ`, `s`, and the `PrevalidExt Γ s` witness
     must be generalized with each constructor case, rather than held as
     outer fixed parameters. A second pass showed that the proof also
     needs explicit `@constructor` patterns (e.g. `@pro Γp sp ...`) to
     keep Lean from resolving helper applications against stale outer
     implicit names.
     `MEqRed.insertAt` is now proved with that shape: it weakens an
     equivalence reduction through `Ctx.insertAt`, shifting the stack and
     both terms at the insertion cutoff.
     `MSubRed.insertAt` is also proved, reusing `MEqRed.insertAt` for the
     `Ms-Equ` and bound-equivalence premises.
     Common corollaries are available as `MEqRed.weaken_head`,
     `MSubRed.weaken_head`, `MEqRed.weaken_tail_head`, and
     `MSubRed.weaken_tail_head`.
     The Prop wrappers and reflexive-transitive closures also transport
     through `Ctx.insertAt` as `MEqRedJ.insertAt`, `MSubRedJ.insertAt`,
     `MEqRedStar.insertAt`, and `MSubRedStar.insertAt`, so future
     well-formed-judgment ports can reuse the same generalized context
     insertion API at the one-step and multi-step levels. Head and
     one-preserved-head specializations are also available for both
     wrapper and closure layers (`*_weaken_head`, `*_weaken_tail_head`).
     Context-prevalidity extractors are available for raw de Bruijn
     reductions as `MEqRed.prevalid` and `MSubRed.prevalid`. Scoping
     extractors are available for Prop wrappers and star closures as
     `MEqRedJ.scoped_*`, `MSubRedJ.scoped_*`,
     `MEqRedStar.scoped_*`, and `MSubRedStar.scoped_*`; backwards
     star-scoping extractors are available in Prop-safe `Nonempty` form
     as `MEqRedStar.scoped_left_nonempty`,
     `MEqRedStar.scoped_pair_from_right_nonempty`,
     `MSubRedStar.scoped_left_nonempty`, and
     `MSubRedStar.scoped_pair_from_right_nonempty`. Named closure
     helpers are available as `MEqRedStar.single`,
     `MSubRedStar.single`, `MEqRedStar.trans`, and
     `MSubRedStar.trans`; equivalence chains embed into subtype chains
     through `MSubRedStar.of_MEqRedStar` under a fixed `PrevalidExt`.
     Shape inversions are available as
     `MEqRed.top_inv`, `MSubRed.top_inv`, `MEqRedStar.top_inv`,
     `MSubRedStar.top_inv`, `MEqRed.abs_inv`, and
     `MEqRedStar.abs_inv`.
     De Bruijn extended-context reduction is now ported in
     `Pss/Mpss/DeBruijnContextRed.lean` as `ExtCtxRed` /
     `ExtCtxRedStar`, with nameless `Ct-Ann` / `Ct-Stk`, structural
     preservation lemmas, de Bruijn `lemma_36`, and single-step closure
     helpers. The star layer also has named `refl`, `single`, `trans`,
     structural preservation, and star-level `lemma_36` helpers.
     Logical-context prevalidity transport is available at both layers
     as `*.prevalid_ctx_right_nonempty` and `*.prevalid_ctx_right`.
4. **Phase 4 — well-formed judgments.** `WfM`, `WSubM`, `WSubMStar`,
   `WEquM` re-stated in indices.
   * **Seeded 2026-05-04 on `db-refactor`:**
     `Pss/Mpss/DeBruijnWellFormed.lean` defines the de Bruijn
     well-formed judgment layer: mutual `WfM` / `WSubM` / `WSubMStar`,
     separate `WEquM` / `WEquMStar`, reflexive star helpers, scoped
     endpoint invariants for all five judgments, `WEquM.symm`, and
     `WEquM.toWSubM`. The `Wf-Fun` rule now has a single body premise
     under `{ bound := t, kind := .sub } :: Γ`, matching the de Bruijn
     reduction binder shape and avoiding the locally-nameless cofinite
     body function. Generalized context insertion weakening is now
     proved for all five judgments as `WfM.insertAt`, `WSubM.insertAt`,
     `WSubMStar.insertAt`, `WEquM.insertAt`, and `WEquMStar.insertAt`,
     with head and one-preserved-head corollaries available as
     `*_weaken_head` and `*_weaken_tail_head`. The first chain helpers
     are also available: `WSubMStar.WSubM_trans`, `WSubMStar.trans`,
     `WSubM.left_lf1_chain`, `WSubM.right_rgh_chain`,
     `WEquM.left_chain`, `WEquM.right_chain_back`,
     `WSubMStar.of_WSubM`, `WEquMStar.of_WEquM`,
     `WEquMStar.WEquM_trans`, and `WEquMStar.trans`. Context
     prevalidity extractors are available for all five judgments as
     `*.prevalid`, plus derived-prevalid insertion wrappers
     `*.insertAt'`. Transitive well-equivalence now has symmetry and
     an embedding into transitive well-subtyping:
     `WEquMStar.symm` and `WEquMStar.toWSubMStar`. Endpoint
     well-formedness extractors are available as
     `WSubMStar.wf_left` / `.wf_right` and
     `WEquMStar.wf_left` / `.wf_right`, plus paired forms
     `WSubMStar.wf_pair` and `WEquMStar.wf_pair`. Well-formed terms now provide
     reflexive empty-stack reductions through `WfM.MEqRed_refl` and
     `WfM.MSubRed_refl`. De Bruijn `WSubMStar` can now
     absorb single empty-stack equivalence steps at either endpoint via
     `extend_left_via_MEqRed_fwd` and `extend_right_via_MEqRed_back`;
     matching `WEquMStar` endpoint helpers are available under the same
     names. De Bruijn `WSubMStar` can also absorb a single empty-stack
     subtype step at its left endpoint via
     `extend_left_via_MSubRed_fwd`. Well-formed empty-stack reduction
     steps can be embedded directly into the transitive well-formed
     relations with `WSubMStar.of_MEqRed_fwd` / `.of_MEqRed_back`,
     `WSubMStar.of_MSubRed_fwd`, and `WEquMStar.of_MEqRed_fwd` /
     `.of_MEqRed_back`. Empty-stack reduction chains can also be
     embedded conditionally via `WSubMStar.of_MEqRedStar_fwd`,
     `WSubMStar.of_MEqRedStar_back`, `WSubMStar.of_MSubRedStar_fwd`,
     `WEquMStar.of_MEqRedStar_fwd`, and
     `WEquMStar.of_MEqRedStar_back` when the caller supplies stepwise
     `WfM` preservation for that restricted chain. The same restricted
     preservation premise also gives endpoint well-formedness propagation
     through `MEqRedStar.wf_right_of`, `MSubRedStar.wf_right_of`, and
     the corresponding `*.wf_pair_of` helpers. Transitive
     well-subtyping/equivalence can absorb restricted empty-stack
     equivalence chains at either endpoint through
     `WSubMStar.extend_left_via_MEqRedStar_fwd`,
     `WSubMStar.extend_right_via_MEqRedStar_back`,
     `WEquMStar.extend_left_via_MEqRedStar_fwd`, and
     `WEquMStar.extend_right_via_MEqRedStar_back`. Transitive
     well-subtyping can also absorb restricted empty-stack subtype
     chains at its left endpoint through
     `WSubMStar.extend_left_via_MSubRedStar_fwd`. For equivalence
     chains specifically, endpoint-only variants are available with the
     `_of_wf` suffix at the transitive layers and as
     `WSubM.of_MEqRedStar_*` / `WEquM.of_MEqRedStar_*` at the one-step
     layers; these require only the relevant endpoint well-formedness
     because the underlying `WSubM`/`WEquM` chain constructors absorb
     intermediate equivalence-reduction steps. Single empty-stack
     equivalence steps also embed at the one-step layers through
     `WSubM.of_MEqRed_fwd` / `.of_MEqRed_back` and
     `WEquM.of_MEqRed_fwd` / `.of_MEqRed_back`; single empty-stack
     subtype steps embed into one-step well-subtyping through
     `WSubM.of_MSubRed_fwd`. De Bruijn operational steps can be routed
     into one-step and transitive well-subtyping/equivalence through the
     `*.of_StepAt_fwd` / `*.of_StepAt_back` helpers.
5. **Phase 5 — headline theorems.** Re-prove Lemmas 1, 2; Theorems 3,
   4, 5. The 5 β-residuals discharge here.
   * **Seeded 2026-05-04 on `db-refactor`:**
     `Pss/Mpss/DeBruijnTransitivityElim.lean` now defines the de Bruijn
     diagrammatic `MSub` / `MSubStar` layer and strips `WSubM` to `MSub`
     plus `WSubMStar` to `MSubStar`. Collapsing `MSubStar` to `MSub`
     remains the de Bruijn Theorem 3 port and should be driven by the
     future de Bruijn Lemma 1 / Lemma 2 proofs. The layer also has named
     closure helpers `MSub.to_star`, `MSubStar.refl`,
     `MSubStar.single`, `MSubStar.trans`, and `WSubM.toMSubStar`.
     Diagram endpoint scoping is available in Prop-safe `Nonempty` form
     through `MSub.scoped_right_nonempty`,
     `MSub.scoped_pair_nonempty`, `MSubStar.scoped_right_nonempty`, and
     `MSubStar.scoped_pair_nonempty`; the right-to-left variants are
     `MSub.scoped_left_nonempty`,
     `MSub.scoped_pair_from_right_nonempty`,
     `MSubStar.scoped_left_nonempty`, and
     `MSubStar.scoped_pair_from_right_nonempty`.
     The `MSubStar` layer has matching reduction adapters
     `MSubStar.of_MSubRedStar`, `.of_MSubRed`, and `.of_MEqRed`.
     Well-equivalence strips are also available as `WEquM.toMSub`,
     `WEquM.toMSubStar`, and `WEquMStar.toMSubStar`.
     Diagram introduction helpers `MSub.intro`, `MSub.of_MSubRedStar`,
     `MSub.of_MSubRed`, and `MSub.of_MEqRed` package common-reduct
     witnesses and one-step reductions. Chain-level equivalence
     adapters are available as `MSub.of_MEqRedStar_left`,
     `MSub.of_MEqRedStar_right`, and matching `MSubStar` variants.
     The conditional Theorem 3 lifting skeleton is now present:
     `StrongCommutes`, `commute_subStep_eqStar_of`,
     `commute_subStar_eqStar_of`, `MSub.trans_step_of`, and
     `MSubStar.collapse_of` collapse `MSubStar` to `MSub` from a
     de Bruijn single-step strong-commutativity premise. Use-site
     aliases `Lemma_1_DeBruijn_step_eqStar_of` and
     `Lemma_1_DeBruijn_StrongCommutativityStar_of` name the Lemma-1
     chain-lifting shapes. Use-site adapters `WSubMStar.toMSub_of` and
     `WEquMStar.toMSub_of` now combine stripping and collapse at the
     empty stack. Named
     theorem-style aliases are available as
     `Theorem_3_DeBruijn_TransitivityIsAdmissible_of`,
     `Theorem_3_DeBruijn_WSubMStar_toMSub_of`, and
     `Theorem_3_DeBruijn_WEquMStar_toMSub_of`.
     The conditional Lemma 2 star-lifting skeleton is also present:
     `EqDiamonds`, `diamond_step_eqStar_of`, and
     `diamond_eqStar_eqStar_of` lift a single-step equivalence diamond
     to equivalence-reduction chains. Named aliases
     `Lemma_2_DeBruijn_step_eqStar_of` and
     `Lemma_2_DeBruijn_DiamondMEqRedStar_of` mirror the paper milestone.
     Single-step premise aliases `Lemma_1_DeBruijn_StrongCommutativity`
     and `Lemma_2_DeBruijn_DiamondMEqRed` mark the future full case-grid
     audit points.
     The first actual single-step cells are closed:
     `EqDiamonds.top` and `StrongCommutes.top` discharge the `Top` source
     cases by shape inversion.
     The corresponding direct star-level `Top` cases are also available:
     `diamond_step_eqStar_top`, `diamond_eqStar_eqStar_top`,
     `commute_subStep_eqStar_top`, and `commute_subStar_eqStar_top`.
     Simple constructor-specific variable cells are also closed:
     `EqDiamonds.var_var`, `EqDiamonds.pro_var`,
     `EqDiamonds.var_pro`, `StrongCommutes.pro_var`, and
     `StrongCommutes.equ_var`.
     The first `Top`-headed application cells are closed:
     `EqDiamonds.tAp_tAp`, `EqDiamonds.tAp_app`,
     `EqDiamonds.app_tAp`, `StrongCommutes.appTop_top_tAp`,
     `StrongCommutes.appTop_top_app`, and
     `StrongCommutes.appTop_app_tAp`.
     Lookup uniqueness/disjointness helpers now support variable-grid
     cells: `EqDiamonds.pro_pro_of` closes `Me-Pro × Me-Pro`
     recursively, and `StrongCommutes.pro_pro_vacuous` closes the
     impossible `Ms-Pro × Me-Pro` clash. Both directions of sub/equ
     binding disjointness are named.
     Reusable single-step case combinators are in place:
     `EqDiamonds.refl_left`, `EqDiamonds.refl_right`,
     `StrongCommutes.equ_of`, and `StrongCommutes.top_of`.
     Direct star-level helpers `diamond_refl_eqStar` and
     `commute_topStep_eqStar` close reflexive equivalence and `Ms-Top`
     against arbitrary equivalence chains.
     The star-level `Ms-Equ` branch is named as
     `commute_equStep_eqStar_of`; it lifts the local equivalence diamond
     and embeds the resulting right equivalence chain through
     `MSubRedStar.of_MEqRedStar`. Its chain analogue
     `commute_equStar_eqStar_of` handles subtype chains made only of
     `Ms-Equ` steps the same way.
     `Top`-headed application/`TAp` cells are consolidated through
     `EqDiamonds.tAp_any`, `EqDiamonds.any_tAp`, and
     `StrongCommutes.appTop_any_tAp`, with
     `StrongCommutes.appTop_any_tAp_of` retained as a compatibility
     wrapper.
     The full one-step equivalence diamond for `Top`-headed application
     sources is named `EqDiamonds.appTop_any`.
     The full one-step `Top`-headed application strong-commutativity
     cell is named `StrongCommutes.appTop_any`;
     `StrongCommutes.appTop_any_of` is retained as a conditional-wrapper
     compatibility alias.
     `Top`-headed application shape inversions are available for
     one-step and star equivalence/subtype reductions, and the direct
     star-level joins `diamond_tAp_eqStar` and
     `commute_appTop_subStar_tAp` close the corresponding `TAp` targets.
     The full equivalence-chain diamond for `Top`-headed sources is
     named `diamond_appTop_eqStar_eqStar`.
     Normalization corollaries `appTop_eqStar_to_top` and
     `appTop_subStar_to_top` expose the resulting target-to-`Top`
     chains directly. Diagrammatic packaging adapters
     `msub_appTop_eqStar_to_top` and `msub_appTop_subStar_to_top` view
     those targets as `MSub Γ s _ .top`; matching transitive wrappers
     are available as `msubStar_appTop_eqStar_to_top` and
     `msubStar_appTop_subStar_to_top`. The source-normalization helper
     itself is named `appTop_to_top`, with diagrammatic wrappers
     `msub_appTop_to_top` and `msubStar_appTop_to_top`.
     The full star-level `Top`-headed source cell is also available as
     `commute_appTop_subStar_eqStar`, joining arbitrary subtype and
     equivalence chains from that source at `Top`; its single-subtype-step
     specialization is named `commute_appTop_subStep_eqStar`.
     Abstraction subtype shape inversions are available through
     `MSubRed.abs_inv` and `MSubRedStar.abs_inv`, and
     `commute_abs_to_top_eqStar` closes the branch where the subtype side
     reaches `Top`. The generalized helper
     `commute_subStar_to_top_eqStar` handles any scoped source whose
     subtype side reaches `Top`; `eqStar_to_top_of_subStar_top` exposes
     the resulting target-to-`Top` subtype chain directly, and
     `msub_eqStar_to_top_of_subStar_top` packages that target as
     diagrammatically below `Top`; the matching transitive wrapper is
     `msubStar_eqStar_to_top_of_subStar_top`. The abstraction-specific
     corollary is named `abs_eqStar_to_top_of_subStar_top`, with
     diagram wrappers `msub_abs_eqStar_to_top_of_subStar_top` and
     `msubStar_abs_eqStar_to_top_of_subStar_top`.
     Abstraction-headed application inversions `MEqRed.app_abs_inv` and
     `MSubRed.app_abs_inv` separate β, `Top`, `Top`-headed application,
     and abstraction-headed application targets. Their chain-level
     counterparts `MEqRedStar.app_abs_inv` and `MSubRedStar.app_abs_inv`
     record β branches as chains from the β target to the final target.
     The abstraction-headed application target-to-`Top` specializations
     are named `commute_appAbs_to_top_eqStar`,
     `appAbs_eqStar_to_top_of_subStar_top`,
     `msub_appAbs_eqStar_to_top_of_subStar_top`, and
     `msubStar_appAbs_eqStar_to_top_of_subStar_top`.
     The corresponding one-step `Top` branch is named
     `commute_appAbs_subStep_to_top_eqStar`.
     The β branch of an abstraction-headed application equivalence chain
     is packaged diagrammatically by
     `msub_appAbs_eqStar_beta_or_appAbs` and
     `msubStar_appAbs_eqStar_beta_or_appAbs`.
     The subtype-chain split is packaged by
     `msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs` and
     `msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`.
     One-step specializations are available as
     `msub_appAbs_eqStep_beta_or_appAbs`,
     `msubStar_appAbs_eqStep_beta_or_appAbs`,
     `msub_appAbs_subStep_beta_or_top_or_appTop_or_appAbs`, and
     `msubStar_appAbs_subStep_beta_or_top_or_appTop_or_appAbs`.
     The `Top`-headed target branch of an abstraction-headed application
     subtype chain closes at `Top` through
     `appAbs_subStar_appTop_to_top`,
     `msub_appAbs_subStar_appTop_to_top`, and
     `msubStar_appAbs_subStar_appTop_to_top`; one-step variants are
     `appAbs_subStep_appTop_to_top`,
     `msub_appAbs_subStep_appTop_to_top`, and
     `msubStar_appAbs_subStep_appTop_to_top`.
     The composed source-to-`Top` package for this branch is named
     `appAbs_subStar_to_top_of_appTop`,
     `msub_appAbs_to_top_of_subStar_appTop`, and
     `msubStar_appAbs_to_top_of_subStar_appTop`; one-step variants are
     `appAbs_subStep_to_top_of_appTop`,
     `msub_appAbs_to_top_of_subStep_appTop`, and
     `msubStar_appAbs_to_top_of_subStep_appTop`.
     The corresponding commutation branch is named
     `commute_appAbs_subStar_appTop_eqStar`, joining such subtype
     branches against arbitrary equivalence chains from the same source
     at `Top`; the single-subtype-step specialization is
     `commute_appAbs_subStep_appTop_eqStar`.
     The combined `Top` / `Top`-headed target branch is named
     `commute_appAbs_subStar_topOrAppTop_eqStar`, with one-step
     specialization `commute_appAbs_subStep_topOrAppTop_eqStar`.
     The compressed subtype-chain split
     `msub_appAbs_subStar_beta_or_toTop_or_appAbs` /
     `msubStar_appAbs_subStar_beta_or_toTop_or_appAbs` combines the raw
     `Top` and `Top`-headed target branches into one target-to-`Top`
     diagrammatic branch; the one-step specializations are
     `msub_appAbs_subStep_beta_or_toTop_or_appAbs` and
     `msubStar_appAbs_subStep_beta_or_toTop_or_appAbs`.
     De Bruijn well-formedness now has constructor inversions
     `WfM.fun_inv` and `WfM.app_inv`; the application inversion uses a
     `Sigma` witness because the star judgments are Type-valued.
6. **Phase 6 — cleanup, axiom audit.** Confirm 9 → 4 active axioms
   (just the Wf-inversion cluster + Prop-17 + Lemma 24). Update
   `AXIOMS.md` to reflect.

`Lemma_24_NarrowingMSubRed`, `Lemma_10_Inversion`, `Lemma_30_msPro_x_axiom`,
`Proposition_17_beta_axiom` may also discharge under de Bruijn but the
walls there were not purely encoding-shaped (e.g. Lemma 24 has a cycle
through `TypeSafety.lean`'s import order). Prioritize the β-residual
cluster discharge as the campaign's success metric for the de Bruijn
refactor; the others can be reassessed after Phase 5.

The campaign artifacts to read before diving in:

* This file's discharge-campaign section + AXIOMS.md.
* `pss/MEQRED-BET-AUDIT.md` — established that `MEqRed.bet`'s body
  context is paper-faithful and should NOT be modified. Future agents
  who attempt to change it are repeating a falsified hypothesis.
* `pss/CHECKER-PORT-INVESTIGATION.md` — orthogonal but useful: a
  read-only feasibility study of porting the PPDP'25 Emacs/Lisp
  PSS-checker artifact to Lean. Recommends "Option B" (port pure logic
  + Scott encodings + replay interpreter). NOT part of the discharge
  campaign; archived for future reference.

---

## 0. Reading-derived facts that drive the design

These come from a careful read of both PDFs in `papers/`. They are load-bearing for everything below.

**From Hutchins 2010 (paper 1, `papers/hutchins-2010-pss.pdf`):**

- Single syntactic category. `t, u ::= x | Top | λx ≤ t. u | t(u)`. Values are `Top` and `λx ≤ t. u`. (Fig. 1.)
- Contexts `Γ ::= ∅ | Γ, x ≤ t`. The `≤` here is **the same** as the subtype relation symbol — bound entries record an upper bound, not a "type" in the traditional sense.
- Two declarative judgments with shared shape, abbreviated via meta-variable `◁ ∈ {≤, ≡}`: `Γ ⊢ t ◁ u`. The DS-* rules in Fig. 1 are schemas over `◁`. There is also `wf` and `≤_wf`.
- Reduction `t ⟶ t'` (the small operational reduction) is plain `β` plus context closure (E-CONG, E-APP). System is **not strongly normalizing** (Theorem 4.4, Girard's paradox via Top).
- Algorithmic system (Fig. 2) replaces transitivity with two reductions on terms-in-context:
  - `Γ ⊢_A t ⟶^≡ t'` — **equivalence reduction**: SRE-APP (β where the operand is shown to be a subtype of the bound, via `≤*`), SRE-TOPAPP (`Top(t) ⟶ Top`), plus congruence anywhere.
  - `Γ ⊢_A t ⟶^≤ t'` — **subtype reduction**: SRS-PROM (`x ⟶^≤ t` when `x ≤ t ∈ Γ`), SRS-TOP (`t ⟶^≤ Top`), congruence only in **positive** evaluation contexts.
  - Subtyping is then `≤*` = refl-trans of single-step `t ⟶ s ⟵ u` (Fig. 2 AS-* rules); equivalence likewise.
- Proven theorems in paper 1: confluence of `⟶^≡` (Thm 6.1, Takahashi style); local commutativity (Lemma 6.4); Lemma 6.3 "commutativity ⇒ transitivity"; Lemma 5.2 inversion; Lemma 5.3 reduction implies equivalence; Lemma 5.4 substitution; Theorem 5.5 progress; Theorem 5.6 preservation. **Conjecture 5.1** (transitivity elimination) and **Conjecture 6.2** (global commutativity) are open.

**From Pasquale & García-Pérez 2024 (paper 2, `papers/pasquale-garcia-perez-2024-mpss.pdf`):**

- MPSS has the SAME term syntax `t ::= x | Top | (λx ≤ t. u) | (u v) | α` (where `α` is a metavariable for stack-popped operands — for Lean's purposes it just lives in the same `Term` inductive; there's no separate syntactic class once you mechanize).
- Logical contexts `Γ ::= ε | Γ, x ≤ t | Γ, x ≡ α`. **Crucial difference from PSS**: contexts now contain BOTH subtype bindings (`x ≤ t`) and equivalence bindings (`x ≡ α`). The latter is what `Me-FOp` introduces.
- Stacks `s ::= nil | α :: s`. Extended context `Γ ; s`.
- Two reductions on extended contexts: `Γ; s ⊢ u ⟶^≡ v` (Fig. 2, 8 rules: Me-Pro, Me-Bet, Me-Top, Me-App, Me-Var, Me-Fun, Me-TAp, Me-FOp) and `Γ; s ⊢ u ⟶^≤ v` (6 rules: Ms-Pro, Ms-Top, Ms-Equ, Ms-App, Ms-Fun, Ms-FOp).
- "Reduction of extended context" `Γ; s ↣ Γ'; s'` (Ct-Ann, Ct-Stk).
- **Lemma 1** (`⟶^≤` and `⟶^≡` strongly commute): main result.
- **Lemma 2** (`⟶^≡` has the diamond property), with a "no Me-Pro on `x` in subderivations" side condition.
- **Theorem 3** (transitivity admissible) follows from Lemma 1 + Lemma 2.
- §4 well-formedness `wf`, `≤_wf`, `≤*_wf` (Fig. 4); operational semantics `↦` (Os-Bet + Os-Con); **Theorems 4 & 5** (progress, preservation) — both **conditional on Conjecture 8**.

---

## 1. Lakefile / dependencies

### 1.1 Toolchain

Pin **`leanprover/lean4:v4.16.0`** in `lean-toolchain`.

`lean-toolchain`:
```
leanprover/lean4:v4.16.0
```

### 1.2 Mathlib pin

`lakefile.lean`:
```lean
import Lake
open Lake DSL

package «pss» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]
  moreServerOptions := #[⟨`linter.unusedVariables, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

@[default_target]
lean_lib «Pss» where
  srcDir := "."
  globs := #[.andSubmodules `Pss]
```

---

## 2. Binding representation: **locally-nameless with cofinite quantification**

This is **the** load-bearing decision.

```lean
inductive Term where
  | bvar : Nat → Term
  | fvar : String → Term
  | top  : Term
  | abs  : (bound : Term) → (body : Term) → Term
  | app  : Term → Term → Term
deriving DecidableEq
```

Why locally-nameless and not the alternatives:

- **Locally nameless** ✅: Substitution lemma is a 5-line `induction` after the open/close framework is in place. Cofinite quantification gives the right induction principle for free for `wf`.
- Pure de Bruijn: MPSS commutativity case-splits on whether `Me-Pro` promotes a specific variable `x` — this is a NAME-tracking property; raw de Bruijn forces shift bookkeeping every diagram.
- Well-scoped de Bruijn: same problem, plus `ReflTransGen` of typed reductions doesn't fit Mathlib's untyped `Relation.ReflTransGen`.
- PHOAS: cannot express `Me-Pro`'s context lookup. Wrong tool.

### Infrastructure agents must build (`Pss.Syntax.LocallyNameless`)

```lean
def open_ (k : Nat) (u : Term) : Term → Term
def opening (u : Term) : Term → Term := open_ 0 u
def close_ (k : Nat) (x : String) : Term → Term
def fv : Term → Finset String
def subst (x : String) (u : Term) : Term → Term

inductive LC : Term → Prop
  | top : LC .top
  | fvar : LC (.fvar x)
  | app : LC u → LC v → LC (.app u v)
  | abs : LC bound → (∀ x ∉ L, LC (opening (.fvar x) body)) → LC (.abs bound body)
```

Standard locally-nameless lemmas:
- `subst_open_var : x ≠ y → subst x u (opening (.fvar y) e) = opening (.fvar y) (subst x u e)`
- `subst_intro : x ∉ fv e → opening u e = subst x u (opening (.fvar x) e)`
- `open_lc : LC e → opening u e = e`
- `subst_lc : LC u → LC e → LC (subst x u e)`
- round-trips `open_close`, `close_open`.

Reference: Aydemir et al. 2008 "Engineering Formal Metatheory" (POPLmark).

### Convention for context entries

Contexts store `fvar`-named entries. Bound bodies in `abs` use `bvar 0`. A judgment `Γ ⊢ t ◁ u` is only stated when `t` and `u` are `LC` and `fv t ∪ fv u ⊆ dom Γ`. Carry this as a side condition on every relation (in `prevalid`) — do NOT make `Term` an indexed type.

---

## 3. Module hierarchy

All paths under `pss/`. Lean modules under `pss/Pss/`. The root file `pss/Pss.lean` re-exports everything.

```
pss/
├── lakefile.lean
├── lean-toolchain
├── lake-manifest.json           [generated]
├── README.md                    [hand-written orientation]
├── PLAN.md                      [this file]
├── papers/                      [PDFs]
├── Pss.lean                     [umbrella import]
└── Pss/
    ├── Syntax/
    │   ├── Term.lean
    │   ├── LocallyNameless.lean
    │   └── FreeVars.lean
    ├── Context/
    │   ├── Logical.lean
    │   ├── Stack.lean
    │   └── Prevalid.lean
    ├── Reduction/
    │   └── Operational.lean
    ├── Decl/                     -- Hutchins 2010 §3 declarative
    │   ├── Subtyping.lean
    │   ├── WellFormed.lean
    │   └── Theorems.lean
    ├── Algo/                     -- Hutchins 2010 §6 algorithmic
    │   ├── EqRed.lean
    │   ├── SubRed.lean
    │   ├── Subtyping.lean
    │   ├── Confluence.lean
    │   ├── LocalCommute.lean
    │   └── PartialSafety.lean
    ├── Mpss/                     -- Pasquale & García-Pérez 2024
    │   ├── EqRed.lean
    │   ├── SubRed.lean
    │   ├── ContextRed.lean
    │   ├── Substitution.lean
    │   ├── Weakening.lean
    │   ├── Narrowing.lean
    │   ├── Diamond.lean
    │   ├── Commutation.lean
    │   ├── TransitivityElim.lean
    │   ├── WellFormed.lean
    │   ├── OperationalSem.lean
    │   └── TypeSafety.lean
    ├── Bridge/                   -- relating systems
    │   ├── DeclAlgo.lean
    │   └── AlgoMpss.lean
    └── Util/
        ├── ParRed.lean
        └── Tactic.lean
```

### Module-by-module specification

**`Pss.Syntax.Term`** — `inductive Term` (locally-nameless). Pretty-printer + DecidableEq.

**`Pss.Syntax.LocallyNameless`** — `open_`, `opening`, `close_`, `subst`, `LC`. Notation `e^[x]` for `opening (.fvar x) e`. Plus the round-trip and substitution-vs-opening lemmas listed in §2.

**`Pss.Syntax.FreeVars`** — `fv : Term → Finset String`, `bv : Term → Finset Nat`. Monotonicity / set-containment lemmas.

**`Pss.Context.Logical`** — `inductive CtxEntry := sub (x : String) (t : Term) | equ (x : String) (α : Term)`. `Ctx := List CtxEntry` (innermost-last). `dom`, `lookupSub`, `lookupEqu`. SUPERSET so PSS can ignore `equ` and MPSS uses both.

**`Pss.Context.Stack`** — `Stack := List Term`. `ExtCtx := Ctx × Stack`. Used by `Mpss/*`; PSS-side, the stack is implicitly `nil`.

**`Pss.Context.Prevalid`** — `inductive Prevalid : Ctx → Prop` (Pv-Emp, Pv-Ctx, Pv-EqA from MPSS Fig. 1). `inductive PrevalidExt : Ctx → Stack → Prop` (Pv-Nil, Pv-Sta).

**`Pss.Reduction.Operational`** — `inductive Step : Term → Term → Prop` — `Os-Bet`, `Os-Con`. Evaluation contexts `EvalCtx`. Notation `t ↦ t'`.

**`Pss.Decl.Subtyping`** — Mutually inductive `DSub` and `DEq`. Cofinite quantification on DS-FUN:
```lean
| dsFun : DEq Γ t t' →
    (∀ x ∉ L, DSub ((.sub x t) :: Γ) (u^[x]) (u'^[x])) →
    DSub Γ (.abs t u) (.abs t' u')
```

**`Pss.Decl.WellFormed`** — `WF` (W-Var, W-Top, W-Fun, W-App). `WSub Γ t u := WF Γ t ∧ WF Γ u ∧ DSub Γ t u`.

**`Pss.Decl.Theorems`** — Hutchins §5 lemmas/theorems. `axiom Conjecture_5_1_TransitivityElim` (discharged in Wave 7).

**`Pss.Algo.EqRed`** — `AEqRed`: Hutchins Fig. 2 SRE-* + congruence SR-Cong + SR-Fun. Notation `Γ ⊢_A t ⟶^≡ t'`.

**`Pss.Algo.SubRed`** — `ASubRed`: SRS-Prom, SRS-Top, congruence in **positive** contexts only. Helper `inductive PosCtx`.

**`Pss.Algo.Subtyping`** — `AEq`, `ASub` (per Fig. 2). `AS-Left`/`AS-Right` derived.

**`Pss.Algo.Confluence`** — `Theorem_6_1_ConfluenceOfEqRed : Confluent (AEqRed Γ)`, via diamond of Takahashi `ParEqRed`.

**`Pss.Algo.LocalCommute`** — `Lemma_6_4_LocalCommutativity` from Hutchins §6.6.

**`Pss.Algo.PartialSafety`** — Bridges Hutchins §5 and §6 under `Conjecture_5_1` axiom.

**`Pss.Mpss.EqRed`** — `MEqRed`: 8 rules (Me-Pro, Me-Bet, Me-Top, Me-App, Me-Var, Me-Fun, Me-TAp, Me-FOp).

**`Pss.Mpss.SubRed`** — `MSubRed`: 6 rules (Ms-Pro, Ms-Top, Ms-Equ, Ms-App, Ms-Fun, Ms-FOp). Mutual with `MEqRed`.

**`Pss.Mpss.ContextRed`** — `ExtCtxRed` (Ct-Ann, Ct-Stk). **Lemma 36** (extraction).

**`Pss.Mpss.Substitution`** — Lemmas 28, 29, 30, 31, 32 from MPSS appendix.

**`Pss.Mpss.Weakening`** — Lemmas 19, 20, 21, 22.

**`Pss.Mpss.Narrowing`** — Lemmas 23, 24, 25, 26.

**`Pss.Mpss.Diamond`** — `Lemma_2_DiamondMEqRed` + `Proposition_18_ReflexivityMEqRed`. Side condition encoded as a `Prop` predicate on derivations OR a refined inductive (see Risk 4).

**`Pss.Mpss.Commutation`** — `Lemma_1_StrongCommutativity`. Heart of the formalization. ~600-900 lines.

**`Pss.Mpss.TransitivityElim`** — `Theorem_3_TransitivityIsAdmissible`.

**`Pss.Mpss.WellFormed`** — `WfM`, `WSubM`, `WSubMStar` (Fig. 4).

**`Pss.Mpss.OperationalSem`** — Lifts `Step` to MPSS terminology. `Proposition_17`.

**`Pss.Mpss.TypeSafety`** — `axiom Conjecture_8_WellSubtypingContextIndependent`. `Theorem_4_Progress`, `Theorem_5_Preservation`. Lemmas 6, 7, 10, 11, 15, 16.

**`Pss.Bridge.DeclAlgo`** — `decl_to_algo`, `algo_to_decl`.

**`Pss.Bridge.AlgoMpss`** — `mpss_to_algo`, `algo_to_mpss`. **Headline:** `Conjecture_5_1_proven` — discharges the axiom from `Pss.Decl.Theorems` by transferring through MPSS.

**`Pss.Util.ParRed`** — Generic Takahashi parallel reduction.

**`Pss.Util.Tactic`** — `pick_fresh` tactic for cofinite quantification.

---

## 4. Dispatch waves

Each wave has 3-6 agents that can run in parallel with **no shared writes**. Agents inside a wave never edit the same file. Each agent's deliverables = the signatures it must produce; bodies can use `sorry` if blocked, with a `TODO` comment, to unblock downstream.

### Wave 0 — bootstrap (1 agent)
- Agent 0: `lean-toolchain`, `lakefile.lean`, empty `Pss.lean`, empty subdirs, `lake update`, `README.md`.

### Wave 1 — syntax & infrastructure (4 agents)
- 1A: `Pss/Syntax/Term.lean` + `Pss/Syntax/LocallyNameless.lean`
- 1B: `Pss/Syntax/FreeVars.lean`
- 1C: `Pss/Util/ParRed.lean`
- 1D: `Pss/Util/Tactic.lean`

### Wave 2 — contexts & operational semantics (3 agents)
- 2A: `Pss/Context/{Logical,Stack,Prevalid}.lean`
- 2B: `Pss/Reduction/Operational.lean`
- 2C: `Pss/Decl/{Subtyping,WellFormed}.lean`

### Wave 3 — algorithmic system + MPSS reductions (4 agents)
- 3A: `Pss/Algo/{EqRed,SubRed,Subtyping}.lean`
- 3B: `Pss/Mpss/{EqRed,SubRed}.lean`
- 3C: `Pss/Mpss/ContextRed.lean`
- 3D: `Pss/Decl/Theorems.lean` (Hutchins §5 with `Conjecture_5_1` axiom)

### Wave 4 — MPSS substitution / weakening + Algo confluence (3 agents)
- 4A: `Pss/Mpss/Weakening.lean`
- 4B: `Pss/Mpss/Substitution.lean`
- 4C: `Pss/Algo/Confluence.lean`

### Wave 5 — narrowing, diamond, local commute (4 agents)
- 5A: `Pss/Mpss/WellFormed.lean`
- 5B: `Pss/Mpss/Narrowing.lean`
- 5C: `Pss/Mpss/Diamond.lean`
- 5D: `Pss/Algo/LocalCommute.lean`

### Wave 6 — main commutation theorem (1 agent — too central to parallelize)
- Agent 6: `Pss/Mpss/Commutation.lean`. Estimate 600-900 lines. **Enumerate the case grid before starting the proof.**

### Wave 7 — type safety & bridges (3 agents)
- 7A: `Pss/Mpss/{TransitivityElim,OperationalSem}.lean`
- 7B: `Pss/Mpss/TypeSafety.lean`
- 7C: `Pss/Bridge/{DeclAlgo,AlgoMpss}.lean` — discharges `Conjecture_5_1`.

### Wave 8 — polish (1 agent)
- Agent 8: `Pss.lean` umbrella, `AXIOMS.md`, `Pss/Sanity.lean` with `#print axioms`, README update.

**Total:** 8 waves, 22 agent-slots. Wave 6 single-threaded; all other waves parallel 3-4 wide.

---

## 5. Risk register

### Risk 1: The substitution-and-opening swamp (HIGH)

Mitigation: Wave 1 Agent 1A copies the lemma list verbatim from Aydemir et al. 2008. Each lemma name in this plan must be honored by downstream citations. Wave 1 ends with a `lake build Pss.Syntax.LocallyNameless` gate before Wave 2 starts.

### Risk 2: Mathlib's `Confluent` doesn't match context-indexed reductions (MEDIUM)

Mitigation: `Pss/Util/ParRed.lean` takes a `Ctx` parameter and re-bundles the ternary relation as an unindexed family `r Γ : α → α → Prop`. State `Confluent (r Γ)` directly; don't fight Mathlib's bundlings.

### Risk 3: MPSS commutation has more cases than the appendix admits (MEDIUM-HIGH)

Mitigation: Wave 6 (one agent) is given a generous time budget. The agent's first task: enumerate all `(MEqRed.constructor, MSubRed.constructor)` pairs. Mark vacuous, paper-covered, missing. **Do not start the proof until the case grid is filled in.** If a case proves intractable, axiomatize precisely (`axiom Mpss_Commute_Case_FOp_App : ...`) — max 2 escape hatches before escalating.

### Risk 4: "no Me-Pro on x" side condition awkward to state (REALIZED — and dropped)

The first attempt (`MEqRedAvoidsPro` as an indexed `Prop` predicate over
`MEqRed`) was unsound under Lean 4's proof irrelevance: two `MEqRed`
derivations of the same proposition are definitionally equal, so the
`pro`-vs-`var` constructor distinction collapses for any source/target
where both rules can fire. The predicate has been dropped (see
`Pss/Mpss/AvoidsPro.lean` history note for the analysis); no downstream
consumer in the current codebase actually used the side condition.

Future mitigation: when discharging Lemma 1, re-introduce the side
condition as a structurally-recursive `Bool`-valued function on the
derivation tree (`def avoidsPro : MEqRed Γ s u v → String → Bool`),
which sees the constructor shape rather than just the propositional
content. Do NOT re-introduce as an indexed `Prop`-predicate — that
form is fundamentally incompatible with `Prop`-valued `MEqRed`.

### Risk 5: Hutchins 2009 thesis missing from `papers/` (CONFIRMED)

The thesis download failed (Edinburgh repository redirect issue). The two PoP/POPL papers are present. Mitigation:
- For Hutchins proofs that reference the thesis "for full details", reconstruct from first principles using:
  - Pierce TAPL Ch 26 (Higher-Order Subtyping) for proof shape.
  - Takahashi 1995 directly for confluence.
  - Paper 2 §1's worked example for the Lemma 6.4 case 2 diagram.
- Wave 0 README should note the thesis is missing and recommend fetching it manually.

---

## 6. What to mechanize vs. axiomatize

### 6.1 Permanent axioms

- **`Conjecture_8_WellSubtypingContextIndependent`** (in `Pss.Mpss.TypeSafety`) — paper 2 explicitly leaves this open; we mirror that. Theorems 4 and 5 are stated and proved CONDITIONAL on this axiom.

### 6.2 Temporary axioms (discharged in later waves)

- **`Conjecture_5_1_TransitivityElim`** (in `Pss.Decl.Theorems`) — Hutchins' open conjecture. Used as axiom in Wave 3 to unblock parallel work. **Discharged in Wave 7** by `Pss.Bridge.AlgoMpss.Conjecture_5_1_proven`.

### 6.3 Tactical escape hatch (max 2)

If Wave 6 hits a sub-case taking >1 day, add `TODO_axiom` with exact statement + paper reference. Each escape hatch listed in `AXIOMS.md`. Max two before escalating.

### 6.4 Things we mechanize even though tempting to axiomatize

- Locally-nameless substitution lemmas — 5-10 lines each given LN infra.
- Confluence of `⟶^≡` — standard Takahashi.
- Lemma 36 — promote it to a named lemma.

### 6.5 Things we explicitly do NOT formalize

- Hutchins §3.6 multi-universe extension.
- Hutchins §4 PTS embedding.
- MPSS §4 type-checking algorithms / decidability.

---

## 7. Definition-of-done

The artifact is "done" when:

1. `lake build` succeeds.
2. `#print axioms Theorem_3_TransitivityIsAdmissible` lists only `propext`, `Quot.sound`, `Classical.choice`.
3. `#print axioms Theorem_4_Progress` and `#print axioms Theorem_5_Preservation` list those plus `Conjecture_8_WellSubtypingContextIndependent` — no `Conjecture_5_1_TransitivityElim`.
4. `#print axioms Conjecture_5_1_proven` lists only the standard three.
5. `AXIOMS.md` documents the residual `Conjecture_8` axiom with paper citation.
6. Every theorem named in §3 of this plan exists at the path indicated.

---

## 8. Sketch signatures

```lean
-- Pss.Syntax.Term
inductive Term where
  | bvar : Nat → Term
  | fvar : String → Term
  | top  : Term
  | abs  : Term → Term → Term
  | app  : Term → Term → Term

-- Pss.Syntax.LocallyNameless
def Term.opening : Term → Term → Term
def Term.subst   : String → Term → Term → Term
def Term.fv      : Term → Finset String
inductive Term.LC : Term → Prop

-- Pss.Context
inductive CtxEntryKind | sub | equ
structure CtxEntry where
  name : String
  bound : Term
  kind : CtxEntryKind
abbrev Ctx := List CtxEntry
abbrev Stack := List Term

-- Pss.Decl.Subtyping  (mutually inductive)
inductive DSub : Ctx → Term → Term → Prop
inductive DEq  : Ctx → Term → Term → Prop

-- Pss.Algo
inductive AEqRed : Ctx → Term → Term → Prop
inductive ASubRed : Ctx → Term → Term → Prop
def ASub (Γ : Ctx) (t u : Term) : Prop :=
  ∃ s, ASubRed.Star Γ t s ∧ AEqRed.Star Γ u s

-- Pss.Mpss
inductive MEqRed : Ctx → Stack → Term → Term → Prop
inductive MSubRed : Ctx → Stack → Term → Term → Prop
inductive ExtCtxRed : Ctx × Stack → Ctx × Stack → Prop

-- Headline theorems
theorem Theorem_6_1_ConfluenceOfEqRed (Γ : Ctx) :
    Confluent (AEqRed Γ)

theorem Lemma_6_4_LocalCommutativity {Γ t₀ t₁ t₂} :
    AEqRed Γ t₀ t₁ → ASubRed Γ t₀ t₂ →
    ∃ t₃, AEqRedRefl Γ t₂ t₃ ∧ ASubStar Γ t₁ t₃

theorem Lemma_1_StrongCommutativity {Γ s t₀ t₁ t₂} :
    MSubRed Γ s t₀ t₁ → MEqRed Γ s t₀ t₂ →
    ∀ Γ' s', ExtCtxRed (Γ, s) (Γ', s') →
    ∃ t₃, MEqRed Γ s t₂ t₃ ∧ MSubRed Γ' s' t₁ t₃

theorem Theorem_3_TransitivityIsAdmissible {Γ s u v} :
    MSubStar Γ s u v → MSub Γ s u v

theorem Theorem_4_Progress
    [h : Conjecture_8] {Γ t} (hwf : WfM Γ t) :
    NormalForm t ∨ ∃ t', Step t t'

theorem Theorem_5_Preservation
    [h : Conjecture_8] {Γ t t' u} :
    WSubMStar Γ t u → Step t t' → WSubMStar Γ t' u

theorem Conjecture_5_1_proven {Γ v w} :
    WSubStar Γ v w → DSub Γ v w
```

---

## Critical files

These five files, if any one is wrong, derail everything:

- `pss/Pss/Syntax/LocallyNameless.lean` — binding convention. Risk 1.
- `pss/Pss/Mpss/Commutation.lean` — the single hardest proof. Risk 3.
- `pss/Pss/Mpss/{EqRed,SubRed}.lean` — MPSS rules; downstream meta-theory cites them constantly.
- `pss/Pss/Bridge/AlgoMpss.lean` — discharges `Conjecture_5_1`.
- `pss/lakefile.lean` — Mathlib pin.
