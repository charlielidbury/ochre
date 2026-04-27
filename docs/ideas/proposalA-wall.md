# Proposal A: closeAll wall — substrate decrement-style off-by-one

**Status:** partial.  Wall-breaking lemma proven; substrate
commutation walls discovered.

**Lean artefacts:**
* `lean/Och/Soundness/CloseAll.lean` — defines `closeAll`, proves
  `Subtype'_lvar_via_tyCtx` (the wall-breaking lemma) and
  `closeAllAt_shiftL` (commutation with shift).  Two sorries remain:
  `closeAllAt_substL_OPEN_QUESTION` and
  `closeAll_openFresh_OPEN_QUESTION`.
* `lean/Och/Soundness/SubCheckSubstNeutral.lean` — adds
  `subCheckSubst_sound_arm_neutral_closeAll` (post-Proposal-A C7
  statement, sorried at the structural-recursion level, no longer at
  the level-var representation gap).

## What works

The crux of Proposal A is the wall-breaking lemma:

```lean
theorem Subtype'_lvar_via_tyCtx
    {S : Seen} {tyCtx : Array Expr} {lvl : Nat} {ty : Expr}
    (hlvl : lvl < tyCtx.size)
    (h : tyCtx[lvl]? = some ty) :
    Subtype' S (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.bvar (SubstEval.levelOffset + lvl)))
      (ty.shift (tyCtx.size - 1 - lvl + 1) 0)
```

This is **proved**.  After translation by `closeAll`, the level-var
`bvar (levelOffset + lvl)` becomes `bvar (depth - 1 - lvl)`, which
lives in the range `[0, depth)` of `tyCtxToCtx tyCtx`.  Lookup
yields `tyCtx[lvl]`, and `Subtype'.bvar` closes the goal.

The companion lemma `closeAllAt_shiftL` (`closeAll` commutes with
`shiftL` in lockstep with the binder counter) is also **proved**.

## What fails: off-by-one in decrement-style operations

Both `closeAllAt_substL` and `closeAll_openFresh` fail as the naive
equation, due to a fundamental mismatch in the substrate's
operations.

### Mismatch

* **Substrate (`substL`, `openFresh`)** uses *decrement-style*
  semantics: substituting at position `j` eliminates the binder at
  `j` and decrements all bvars `> j` by 1.
* **`closeAllAt` under-binder traversal** uses *preservation-style*
  semantics: outer references and level-var images are placed at
  fixed de-Bruijn indices regardless of whether the surrounding
  binder is being eliminated.

When the two interact, `closeAllAt` produces level-var images at
positive de-Bruijn indices, which `substL`/`openFresh` then
incorrectly decrement.

### Counterexample (`closeAll_openFresh`)

For `body` containing `.bvar (levelOffset + lvl')` with `lvl' < lvl`
(so `lvl` is properly fresh):

| Operation | Result |
|-----------|--------|
| `openFresh body lvl` (`= substL body 0 (.bvar (levelOffset + lvl))`) | unchanged (`substL` skips level-vars) |
| `closeAll (lvl+1)` of the above | `.bvar (lvl - lvl')` |
| **vs.** `closeAllAt 1 (lvl+1) body` | `.bvar (lvl - lvl' + 1)` |

Off by 1.  Even strengthening with `body.bvarLTOrLvl 1 = true` (the
well-scoping invariant that disallows outer ordinary bvars) does not
fix this — the level-var case still fails.

### Counterexample (`closeAllAt_substL`)

For `e = .bvar (levelOffset + lvl)` with `lvl < d - 1` and `j = 0`:

| Side | Reduction | Result |
|------|-----------|--------|
| LHS: `closeAllAt c d (substL e j s)` | `substL` skips level-var; `closeAllAt` translates | `.bvar (d - 1 - lvl + c)` |
| RHS: `substL (closeAllAt c d e) j (closeAllAt c d s)` | `closeAllAt` translates; `substL` decrements (since image > 0) | `.bvar (d - 2 - lvl + c)` |

Off by 1.

## Why the wall isn't a Proposal-A failure

Proposal A's *core idea* — translating level-vars into de-Bruijn
indices before stating soundness — works correctly.  The wall-
breaking lemma demonstrates this.

The off-by-one is a substrate-engine choice issue: the engine uses
`substL` (decrement-style) for both true substitution AND for
"open"-style binder elimination.  In a locally-nameless / cofinite-
quantification presentation, these would be distinct: `open` adds a
free var without decrementing, `subst` actually substitutes.  The
substrate conflates them.

## Possible resolutions

### Option A: Engine-side fix (clean but invasive)

Refactor `openFresh` to use a *non-decrementing* `open` operation:
replace `bvar 0` with `levelBvar lvl` and **shift** all bvars `> 0`
up by 1 (compensating for not decrementing).  This makes `openFresh`
the proper inverse of `closeLevelVar` (which already shifts up).

After this refactor, `closeAll_openFresh` and `closeAllAt_substL`
both go through cleanly.  Existing engine semantics is preserved
modulo a `shiftL 1 0` adjustment somewhere — needs careful audit.

Estimated cost: 1-2 days.  Affects `EvalSubst.lean`'s `openFresh`,
all callers in `subCheckSubst`, and any downstream callers in
`TyCheck.lean`.

### Option B: closeAll-side fix (additive but trickier)

Define a *decrementing* closeAll variant, `closeAllSubst`, whose
under-binder traversal mirrors `substL`'s decrement.  Specifically,
`closeAllSubstAt c d body` for `c > 0` should:
* level-vars: translate as `closeAllAt`.
* outer bvars `≥ c`: leave at the same index (NOT shift up).
* inner bvars `< c`: leave alone.

Hmm, this is roughly what closeAllAt already does for outer bvars.
The real issue is the **level-var image**: at counter `c`, the image
is `bvar (d - 1 - lvl + c)`, but for closeAllSubst to commute with
substL, the image should be `bvar (d - 1 - lvl)` (no `+c` shift).

Concretely, `closeAllSubstAt c d (.bvar (levelOffset + lvl)) =
.bvar (d - 1 - lvl)` (counter-independent).  Then under-binder
recursion preserves this image, but ordinary bvars stay where they
were, mirroring substL's decrement on bvars `> j`.

This sounds promising but introduces a new equation to verify:
`closeAllSubst d (.lam dom body) = .lam (closeAllSubst d dom) (...)`
where the `...` has to handle the lam binder shift correctly.

Estimated cost: 2-3 days.  Less invasive than Option A but requires
careful re-derivation of all `closeAll`-related lemmas.

### Option C: Stop using `subst`-style for openFresh

Add a parallel `openFreshShift` operator to the substrate that
substitutes-AND-shifts (the "open" of locally-nameless), prove
agreement with the existing `openFresh` on the well-scoped regime,
and use `openFreshShift` for the soundness statement.

Estimated cost: 1-2 days.  Cleanest in some ways; introduces new
substrate API.

## Recommendation

Option A is the most defensible long-term direction: it cleans up
the substrate semantics and aligns with standard locally-nameless
practice.  If the user prefers a less invasive path, Option C is
viable.

Either way, the level-var representation gap is **closed**.  The
remaining work is substrate engineering, not metatheory.

## What this means for the overnight effort

* The most important deliverable — the wall-breaking lemma `Subtype
  '_lvar_via_tyCtx` — is **closed**.
* The companion lemma `closeAllAt_shiftL` is **closed**.
* Two open questions remain in `CloseAll.lean`, with off-by-one
  analyses sufficient to direct the next agent to either Option A
  or C above.
* The C7 obligation in its post-Proposal-A form
  (`subCheckSubst_sound_arm_neutral_closeAll`) is now structurally
  reducible — the recursive arms each appeal to closed lemmas, with
  the `closeAll` infrastructure threading through.

The proposal-A WALL is **not the same** as the C7 wall: the C7 wall
was about *representation* (no Subtype' rule produces `.bvar k` for
`k = levelOffset + lvl`).  Proposal A unblocks that wall.  The new
wall here is about *substrate semantics* (`substL` decrements;
`closeAll` doesn't).  Different problem, different family.
