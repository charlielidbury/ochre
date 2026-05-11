# STOP — Verdict C reformulation analysis: wall at AppBet → Me-FOp → ProVar(i=0) at NP≥1

**Status:** Verdict C as described in the previous dispatch
(`STOP-PAPER-GAP-LEMMA-2-PROVAR.md`) does **not** fully eliminate
the ProVar/VarPro residual. Restricting Moreover to "body-fresh
indices only" or to "NP-0 only" walls at deeper nestings. This
dispatch documents the wall structurally and recommends a different
strategic approach.

**No code changes were shipped.** The build remains green at the
state from the previous dispatch (commit `2554bb2`).

## The structural NP-0 rescue (genuine, but insufficient)

The `equBinds_evolve`-built `hLifted` derivation HAS a genuine
structural rescue at NP-0:

* `hLifted` is constructed as a sequence of `weaken_head` applications
  on `MEqRed.insertAt`.
* `Term.shift cutoff (.bvar i) = .bvar (insertAtIndex cutoff i)` where
  `insertAtIndex 0 i = i + 1` (Lean: `Pss/Context/DeBruijn.lean:1129`).
* Every `weaken_head` (cutoff = 0) shifts ALL `Me-Pro` indices UP by 1.
* `equBinds_evolve` at depth `i+1` applies `weaken_head` at least `i+1`
  times.
* **Conclusion:** `hLifted`'s Me-Pro indices are all `≥ 1` (in fact
  `≥ i + 1` where `i` is the variable being looked up).
* Therefore `hLifted.NoPromotionOf 0` holds structurally.

This is a real rescue for the ProVar/VarPro at NP-0 specifically.

## Why NP-0-only Moreover doesn't suffice

The dispatch's plan was to restrict `MoreoverDiamondGeneral` to NP-0
only. But internal cells require Moreover at higher indices to
satisfy their OUTER Moreover at NP-0:

**FunFun:** outer NP-0 of `MEqRed.fun_ hT hBody` =
`(hT.NP-0) ∧ (hBody.NP-1)`. Body IH at NP-1, not NP-0.

**FOpFOp:** same shift — body IH at NP-1.

**BetBet:** outer NP-0 of `MEqRed.bet ht hBody hArg` =
`(hBody.NP-1) ∧ (hArg.NP-0)`. Body IH at NP-1.

So if a bundle internally needs to ship NP-0 of d_1 (for AppBet
bridges), and the source descends through a binder, the body IH must
deliver NP-1 of body's d_1. Which requires the bundle to be
**index-parametric**, not NP-0-only.

## Why index-parametric Moreover walls at ProVar(i=0) at NP≥1

With index-parametric Moreover `MoreoverDiamond_at x`, recursive
binder-shifts propagate the index downward (`x` becomes `x+1` under a
binder).

At a ProVar cell with variable `i` requested at index `y`:

* hLifted's Me-Pro indices are `≥ i + 1` (structural argument above).
* Bound IH's reverse crossing `hLifted.NP-y → d_1_bound.NP-y` needs
  `hLifted.NP-y`.
* For `y ≤ i`: `hLifted.NP-y` is structurally TRUE. ✓
* For `y > i`: `hLifted.NP-y` may be FALSE. ✗ **Wall.**

The wall is hit when the recursion's index `y` exceeds ProVar's
variable `i`. Specifically, this occurs at:

* **AppBet → Me-FOp(body) → ProVar(i=0) at NP-1.** AppBet's body
  context is `{v_0, .equ}::Γ_0; shift 0 s_0`. If `s_0` is non-empty,
  body source can have an abstraction reducing via Me-FOp. Me-FOp's
  body context is `{shift 0 α, .equ}::body_context`, with slot 0
  `.equ`-bound. ProVar at i=0 is structurally possible (Me-Pro CAN
  fire on equ-bound slot 0). AppBet's body IH demands NP-0 of body
  diamond's d_1 in body context, which decomposes via Me-FOp's d_1 =
  `fOp d_1_bound hα d_1_body` to require `d_1_body.NP-1` in
  body-of-body. So the recursive call is at NP-1 in body-of-body,
  and ProVar at i=0 there walls.

* **AppBet → Me-FOp → Me-FOp → ... → ProVar(i=0) at NP-k.** Nested
  Me-FOps create a stack of `.equ` binders, each with slot 0 = the
  popped stack head. ProVar at i=0 deep in the nesting is reachable.
  The recursion's index propagates `+1` at each Me-FOp, eventually
  reaching arbitrary `y`.

This wall is **structural**, not an artifact of how the bundle is
written: any predicate that requires `hLifted.NP-y` for arbitrary `y`
will hit this wall, because `hLifted` can have Me-Pro at arbitrary
indices `≥ i+1`.

## Why the paper's claim is not refuted (but not proved either)

The paper STATES Moreover universally (p. 9:9): "*for any variable x,
if in the derivation of t_0 → t_1 there isn't an application of
Me-Pro that makes a promotion of x*, then ..."

But the paper's PROOF of Lemma 2 doesn't trace through Moreover for
each case. The ProVar case (p. 9:21) only proves the diamond
conclusion; it doesn't establish Moreover at the case level.

The paper's RECURSIVE USE of Moreover (p. 9:23, Me-App × Me-Bet) is
at ONE specific x (the body-fresh binder), which corresponds in de
Bruijn to body context's index 0. The paper's proof goes through at
this single index because the corresponding `hLifted` (synthesized
via Lemma 36 + Lemma 19) has the right NP-0 property structurally —
which IS provable.

But the paper's UNIVERSAL Moreover claim is not rigorously
established by the paper's case-by-case argument. The paper implicitly
relies on alpha-equivariance ("x is fresh, no instance of x appears")
which doesn't transport directly to de Bruijn — in de Bruijn, the
"fresh" binder is bvar 0 at the new context, and other variables can
mention it.

## Recommended next strategic move

The dispatch's premise — that Verdict C salvages ProVar/VarPro at NP-0
— is partially right (NP-0 works), but the full bundle needs NP at
higher indices to propagate internally, and those higher indices wall
at ProVar.

Three strategic options:

### Option (1): Accept ProVar/VarPro at higher indices as residuals

Restructure the bundle to track Moreover index-parametrically. Ship:

* `Lemma_2_DiamondGeneral_at0 (h₁ h₂)` — diamond + NP-0 Moreover. The
  NP-0 case is FULLY provable using the structural rescue (`hLifted`
  has Me-Pro indices ≥ 1).
* `Lemma_2_DiamondGeneral_at_succ (h₁ h₂) (x : Nat)` — diamond at NP-(x+1).
  Conditional on a `ProVar_at_succ_payload` (the wall case).

For `UniformEqDiamonds` we only need the diamond conclusion, no
Moreover. So `UniformEqDiamonds` follows from `Lemma_2_DiamondGeneral_at0`
applied vacuously.

But the BUNDLE's INTERNAL recursion at AppBet/BetApp body IH needs
Moreover at NP-0 in body context (which is index 0 from body POV).
Inside the body recursion, if body source is FunFun/FOpFOp/BetBet,
the cell needs Moreover at NP-1 from sub-IH. That's NP-(0+1).

So the body IH internally needs `Lemma_2_DiamondGeneral_at_succ`,
which is conditional on the wall payload. The bundle thus reduces
ONE payload (ProVar/VarPro at NP-0 dispatched via rescue) but
introduces another (at NP-succ).

**Net: no payload reduction.** This option doesn't improve the count.

### Option (2): Switch to a stronger NP-tracking infrastructure

Track NP at a STRUCTURAL CARRIER (e.g., "the index of the v_0-binding
relative to the current context") rather than a numeric index. Each
binder-extension preserves the carrier's identity (its position
shifts but it's "the same binding").

This requires new infrastructure for tracking specific bindings
through context evolutions. Substantial design effort.

### Option (3): Accept the universal-x Moreover as the residual

The current state has 4 explicit payloads as Prop residuals:
* `MoreoverDiamondGeneral_ProVarVarPro_Payload`
* `MoreoverDiamondGeneral_VarPro_Payload`
* `Lemma_32_PreservesNP_Payload`
* `Lemma_32_EquHead_PreservesNP_Payload`

These are all (mathematically true or possibly true) UNIVERSAL-x
claims about Moreover propagation. They mirror the paper's universal-x
Moreover statement.

The first two are blocked by the structural wall (universal-x is too
strong because `hLifted.NP-x` fails for x > i). The latter two are
plausibly provable by substantial structural induction (~500-1000 lines
each).

The cleanest path may be: **accept that Lemma 2's universal-x Moreover
matches the paper's stated claim (with the same gap) and ship the
payloads as paper-faithful axioms**. The diamond conclusion (= what
`UniformEqDiamonds` actually consumes) is provable without these
payloads — but only IF the bundle's recursion is restructured to NOT
propagate universal-x Moreover internally.

That restructuring is itself substantial: it requires re-doing the
~1500 lines of `Lemma_2_DiamondGeneral.lean`'s assembly to use the
existing `Lemma_2_Case_*_proved` theorems (which already have the
right "diamond + specific-NP" shape) directly, rather than via the
Moreover bundle.

## Concrete next dispatch recommendation

**Build a new file `Pss/Paper/Lemma_2_PlainBundle.lean` that:**

1. Performs structural induction on h₁ (well-founded on
   `MEqRedDepth h₁`).
2. Case-splits on h₁'s constructor + h₂'s constructor.
3. Dispatches each case to the existing `Lemma_2_Case_*_proved`
   theorem.
4. For ProVar/VarPro: uses `Lemma_2_Case_ProVar_proved` (plain diamond).
5. For AppBet/BetApp: needs body IH at the "diamond + NP-0 of d_1"
   shape. This is the only Moreover requirement.

**To satisfy the AppBet/BetApp body IH:** recursively call the bundle
with an EXTRA Moreover NP-0 guarantee, derived structurally.
Specifically:

* If body source `u_0` is at `.sub`-head bound (the bridged case for
  one side), `d_1.NP-0` is structurally derivable from the bridged
  source's NP-0.
* Otherwise (body source at `.equ`-head bound), we DO need Moreover
  crossing — which is precisely the unavoidable Moreover.

A potential rescue: structurally analyze the body source's shape. If
it's NOT an abstraction (no FunFun/FOpFOp/BetBet recursion), the
NP-0 propagation may close cleanly. If it IS, the wall fires.

The wall's structural inevitability for `.equ`-head body source
with deeply nested abstractions remains.

## Files referenced (no modifications)

* `Pss/Paper/Lemma_2_DiamondGeneral.lean` — current bundle with
  universal-x Moreover + 4 payloads.
* `Pss/Paper/Lemma_2_DiamondClosure.lean` — per-case theorems already
  proved with the right shape (plain diamond + specific NP-0 for
  cross-β).
* `Pss/Paper/Lemma_2_Diamond.lean` — per-case obligation definitions
  (`Lemma_2_Case_*` shape).
* `Pss/Paper/Aux/EvolutionTransport.lean:247` — `equBinds_evolve` with
  `weaken_head` chain.
* `Pss/Mpss/DeBruijnReductions.lean:1107` — `MEqRed.weaken_head`
  cutoff = 0 + `Pss/Context/DeBruijn.lean:1129` — `insertAtIndex 0 i
  = i + 1`.

## Cross-references

* `STOP-PAPER-GAP-LEMMA-2-PROVAR.md` — previous Verdict B/C analysis.
* `STOP-PAPER-BUG-LEMMA-32.md` — earlier paper-bug false alarm (rescued
  by a structural lemma).
* Paper Lemma 2 statement: p. 9:9.
* Paper Lemma 2 proof appendix: p. 9:21-25.
* Paper recursive use of Moreover: p. 9:23 (Me-App × Me-Bet).

## Lessons

The Verdict C restructuring was partially right: NP-0 is structurally
rescued. But the bundle's INTERNAL recursion requires Moreover at
arbitrary indices to propagate through binders, and the wall at
ProVar at NP > i is real.

The next strategic move should either:
* Restructure the bundle to NOT propagate universal-x Moreover (the
  `Lemma_2_PlainBundle.lean` approach above), accepting that
  AppBet/BetApp's body IH at deep binder nesting has its own structural
  challenges. OR
* Switch to a structural-carrier-based NP tracking. OR
* Accept the 4 payloads as paper-faithful axioms documenting the
  same gap the paper has.
