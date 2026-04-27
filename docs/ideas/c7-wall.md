# C7 wall: neutral-spine + ascent arm — substrate-bridge dealbreaker

**Status:** walled.  Predicted by `docs/ideas/soundness-strategy.md
§4 wall-2`; encountered with a *different* shape than the typed-NbE
predecessor (see comparison §3 below).

**Lean artefact:** `lean/Och/Soundness/SubCheckSubstNeutral.lean`.
Two precise sorries:
  * `Subtype'_lvar_via_tyCtx_WALL` (line ~206) — the missing
    declarative-side lookup rule.
  * `subCheckSubst_sound_arm_neutral_walled` (line ~230) — the C7
    statement, reducible to the above via the per-arm closures
    in the same file.

The base spine cases (`bvar`–`bvar`, `app`–`app`) DO close in this
file:

  * `subCheckSpine_sound_bvar_bvar` — closes via `Subtype'.refl`.
  * `app_cong_from_spine_ih` — closes via `Subtype'.app_cong` from
    head + bidirectional argument IH.

The wall is *only* in `neutralAscent`'s ascent step.

## 1. The lemma that doesn't go through

```lean
theorem Subtype'_lvar_via_tyCtx_WALL
    {S : Seen} {tyCtx : Array Expr} {lvl : Nat} {ty : Expr}
    (h : tyCtx[lvl]? = some ty) :
    Subtype' S (tyCtxToCtx tyCtx)
      (.bvar (SubstEval.levelOffset + lvl)) ty
```

This says: a level-var `bvar (levelOffset + lvl)` whose type the
engine looks up at `tyCtx[lvl]` is declaratively a subtype of that
type, in the de-Bruijn-translated context `tyCtxToCtx tyCtx :=
tyCtx.toList.reverse`.

`tyCtxToCtx tyCtx` has length `tyCtx.size`.  `Subtype'.bvar` is the
*only* constructor producing `.bvar k` on the LHS; it requires
`(tyCtxToCtx tyCtx).get? k = some τ`.  At `k = levelOffset + lvl`
(say `100_000_005`) and `tyCtx.size` typically `≤ 100`, this is
**always `none`**.  Hence the lemma cannot be discharged with the
current `Subtype'` schema.

## 2. Why the substitution substrate hit a *different* wall

The prior typed-NbE attempt (`docs/ideas/sorry-closure-plan.md`)
walled on:

  (a) `Val.fullyQuotable d v → ∃ q, quote fuelω d v = some q`
      — formally impossible (Halting Problem reduction).
  (b) `Subtype'.unshift_head` at cutoff 0 — research-grade
      structural induction with seen-set rewiring.
  (c) `quoteClosure_realises` termination — Lean's lex prover
      rejected every measure.

The substitution substrate **eliminates (a) and (c)** (no closures,
no quoting).  It was reasonable to hope (b) would also collapse.

But the substitution substrate introduces a *new* obstacle that
the NbE substrate did not have: the **level-var encoding**.  In NbE,
`Val.var lvl` was a constructor; the bridge from the engine's `lvl`
to the declarative `Subtype'.bvar k` was a translation `lvl ↦
Γ.length - 1 - lvl` applied to a `Val`-level relation, with
unambiguous semantics.

In the substitution substrate, level-vars are encoded *inside*
`Expr` as `bvar (levelOffset + lvl)` — sharing the AST node with
ordinary de-Bruijn-indexed bvars but with a different intended
meaning.  Any `Subtype'` derivation about an engine term has to
either (i) reverse this encoding or (ii) accommodate it.

**Same wall family, different shape.**  Both walls are about a
representation gap between the engine and the declarative spec.
The NbE wall was at the *Val-level* (`SubV` ↔ `Subtype'`); this
wall is at the *Expr-level* (level-var-bvar ↔ index-bvar).  In both
cases the gap is bridged by a representation translation that is
itself a substantial proof effort.

## 3. Concrete proposals to break the wall

### Proposal A — translate the engine inputs into de-Bruijn-indexed
form before stating the theorem (i.e., pre-translation)

Define `closeAll : Nat → Expr → Expr` that, given `depth =
tyCtx.size`, replaces every `bvar (levelOffset + lvl)` by `bvar
(depth - 1 - lvl)` and shifts other bvars accordingly.  Then state
soundness as

```lean
Subtype' (translatedSeen ...) (tyCtxToCtx tyCtx)
  (closeAll tyCtx.size a) (closeAll tyCtx.size b)
```

**Pros:** keeps `Subtype'` unchanged; matches Simple's de-Bruijn-
only style.

**Cons:** every operation in the engine must be shown to commute
with `closeAll`.  Specifically:

  * `evalSubst f u (closeAll d e) = closeAll d (evalSubst' …)` —
    a substantial agreement lemma between the substitution-engine
    on level-bvar terms and a hypothetical de-Bruijn-pure variant.
  * `closeAll d (substL e j s) = subst (closeAll d e) j (closeAll
    d s)` — substitution commutation.
  * `subCheckSubst` itself needs to be re-stated against the
    pre-translated form, which would mean *two* engines.

A cleaner phrasing: prove `subCheckSubst tyCtx seen a b = .ok true
↔ subCheckSubst' (tyCtxToCtx tyCtx) seen' (closeAll d a) (closeAll
d b) = .ok true` where `subCheckSubst'` is a hypothetical
de-Bruijn-only mirror.  This is approximately doubling the engine's
proof obligation.

**Verdict:** feasible but expensive.  Estimate 2–3 days of focused
work for the agreement + commutation infrastructure, before the
neutral-arm proof can begin.

### Proposal B — extend `Subtype'` with a level-var rule

Add a new constructor:

```lean
| lvar {S Γ tyCtx lvl τ} :
    tyCtx.get? lvl = some τ →
    Subtype' S Γ (.bvar (levelOffset + lvl)) τ
```

This requires `Subtype'` to additionally carry a `tyCtx`, or to
admit the level-var rule independent of Γ (treating `tyCtx` as a
ghost parameter).  Either way, it's a **schema change**:

  * `Subtype'.weaken`, `narrow_at`, `ctx_extend_at` need new cases.
  * Existing proofs (especially `ctx_extend_at`'s `bvar` case)
    need to be re-validated against the new constructor.
  * Worst: existing applications of `Subtype'` (the `synth_sound`,
    `concEval_preservation` statements) need to be reformulated
    to thread `tyCtx`, which they don't currently.

**Pros:** the soundness proof's neutral-arm becomes one line.

**Cons:** invasive; affects every `Subtype'`-based lemma.
Estimate 3–5 days.

### Proposal C — restate C7 to match the engine's natural
boundary

Observe: at the engine's *top-level* entry (`subCheck a b` with
`tyCtx = #[]` and `seen = []`), there are no level-vars in `a, b`
(closed user terms).  The neutral-arm fires only after recursing
through `lam`/`iota`/`fix` binders that introduce level-vars via
`openFresh`.

So the C7 obligation can be restated as:

```lean
theorem subCheckSubst_sound_arm_neutral_top
    {fuel a b}
    (h : SubstEval.subCheck fuel a b = .ok true)
    (h_a_neutral : isNeutral a = true) :  -- impossible at top
    Subtype' [] [] a b
```

The premise `isNeutral a = true` at the empty tyCtx is **vacuously
false** (no level-vars in `a` ⟹ no neutral head).  So the
top-level statement is *trivial*.

**Verdict:** moves the obligation but doesn't eliminate it.  The
real C7 is the *recursive* call that fires under binders, where
`tyCtx` is non-empty.  The recursive call cannot be stated
without addressing the level-var representation.

### Proposal D — pre-existing `closeLevelVar` (single-level)

`SubstEval.closeLevelVar` already converts a single level-var into
`bvar 0`.  An iterative application closes all of them.  This is
essentially Proposal A with the operation already in hand for one
step; the substantive work is the commutation proofs.

### Recommendation

**Proposal A (with B as a fallback)** is the most defensible
direction.  Proposal B's schema change risks invalidating B1-B3
preservation work in flight, while Proposal A's extra
infrastructure is additive.  The hidden cost in Proposal A is the
`closeAll` ↔ engine-operations agreement infrastructure — but this
mirrors the `evalSubst_concEval_agree` work that Layer 2 of the
strategy doc already calls for.

If the user wants to move past C7 without a 2-3 day investment,
the realistic path is to **axiomatise**
`Subtype'_lvar_via_tyCtx_WALL` as an admitted lemma with the
explanation above, and continue with C8 (stitching) and B1-B3
(preservation) which don't depend on this gap.  The existing four
`sorry`s in `Soundness.lean` would then become five, but the
failure mode would be precisely localised.

## 4. Comparison to the typed-NbE wall — verdict

**Same family, different shape, slightly better.**

* The typed-NbE wall was *three* simultaneous obstacles ((a), (b),
  (c) above) — closing soundness required all three to give.  The
  substitution-substrate wall is *one* obstacle (the level-var
  representation gap).
* The typed-NbE wall (a) was provably impossible.  The
  substitution-substrate wall is *engineering-hard* but provably
  possible (under either Proposal A or B).
* The typed-NbE wall (c) was a Lean termination-checker rejection
  — a tooling wall.  The substitution-substrate wall is a
  representation wall — pure math, no tooling.

**Net:** the substrate change *did* help.  The wall is now a
single, localised, engineering obstacle rather than a
multi-pronged research-grade dead end.  But it is still real
enough to block C7 today.

## 5. What this means for the overnight effort

* C7 is walled until Proposal A or B is executed.  Continuing
  with C2-C6 (lam/iota/fix arms) is still useful — those don't
  need the level-var bridge (they decompose binders structurally).
* B1-B3 (preservation) are *fully independent* of this wall —
  proceed with them.
* `synth_sound` is unaffected — the level-var trick is internal
  to `subCheck`; `synth`'s top-level statement can be discharged
  via `Subtype'.refl` (or the strengthened form) without
  invoking the engine's neutral arm.

**Recommendation for the parent agent:** unblock with axiomatised
`Subtype'_lvar_via_tyCtx_WALL` + comment, OR commit to a
research-grade Proposal A/B in a separate PR.  Either way, do not
let this hold up B1-B3.
