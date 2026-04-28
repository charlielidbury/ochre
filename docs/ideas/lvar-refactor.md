# Strategic option: `.lvar` constructor refactor

**Status:** unactioned, needs user decision.

## The proposal

Replace the current "level-variable as `.bvar k` with `k ≥ levelOffset`"
encoding in `Och.Syntax.Expr` with a separate constructor:

```lean
inductive Expr
  | bvar : Nat → Expr      -- de Bruijn index (always < some depth)
  | lvar : Nat → Expr      -- free level variable (NEW)
  | lam  : Expr → Expr → Expr
  ...
```

The current encoding shares `.bvar` for both kinds, distinguished
by a magic threshold:

```lean
def levelOffset : Nat := 100_000_000
def isLevelIdx  (k : Nat) : Bool := k ≥ levelOffset
def asLevelVar  (e : Expr) : Option Nat := ...
```

## What this closes

* **`WALL_substL_depth`** (`EvalSubstEquiv.lean:209`).  The current
  bridge between `substL` and `Expr.subst` requires
  `body.depth + s.depth + 1 ≤ levelOffset` to ensure the `.bvar k`
  decrement doesn't accidentally produce a `k ≥ levelOffset`.  With
  `.lvar` as a separate constructor, `substL = subst` is
  unconditional on the `.bvar` arms — no depth budget needed.

* **The "10^8 is enough" hack.**  No more magic number.  `.lvar lvl`
  is a typed semantic concept, not a numeric encoding.

## What this does NOT close

* **v2 substrate decrement off-by-one** (`proposalA-wall-v2.md`).
  The wall is fundamental to `substL`'s decrement-style semantics
  vs `closeAllAt`'s preservation-style — independent of how level-
  vars are encoded.  After `.lvar`, the LHS of
  `closeAllAt_substL` still translates `.lvar` to `.bvar (d-1-lvl+c)`,
  and `substL` still decrements that `.bvar` because `c > 0`.

* **Proposal A's `closeAll` translation** itself.  Still needed —
  declarative `Subtype'` doesn't have an `.lvar` rule, so the
  translation `.lvar lvl ↦ .bvar (d - 1 - lvl)` remains the
  bridge.

So `.lvar` closes 1 wall (depth budget) of ~5 in the substrate
family; the rest are about substitution semantics, not level-var
encoding.

## Cost

* **324 references** to `levelOffset` / `isLevelIdx` / `asLevelVar`
  across 8 files (per `grep -rn ... | wc -l` on och-refactor as
  of commit 6e62784):
  - `Och/EvalSubst.lean`
  - `Och/TyCheck.lean`
  - `Och/Soundness/{EvalSubstLemmas,EvalSubstEquiv,CloseAll,SubCheckSubstNeutral,SubCheckSubstSoundness,SubCheckSubstFallback}.lean`

* **Pattern matches** on `.bvar k` need partner `.lvar lvl` arms
  added everywhere — likely 50+ match sites.

* **Substrate semantics changes**:
  - `substL`, `shiftL`: leave `.lvar` alone (no isLevelIdx check needed).
  - `closedAt n e`, `closedAtLvl n e`: `.lvar` is trivially closed.
  - `lvarLT d e`: `.lvar lvl ↦ lvl < d`; cleaner than the current
    `match | .bvar k => if isLevelIdx k then ... else ...`.
  - `evalSubst`: `.lvar` arm returns the lvar unchanged.

* **Tests**: must run the full property-test suite after the
  refactor to catch any subtle semantic drift.  Risk: silent
  regressions.

## Estimated effort

  * 1 day focused work to update the 324 references and add
    `.lvar` arms throughout.
  * 1 day to verify no test regressions and tidy soundness lemmas.
  * Total: 2 days.

## Recommendation

The `.lvar` refactor is **net positive but not urgent**.  It closes
one wall directly and improves structural cleanliness, but doesn't
collapse the v2 family.  The cost is moderate (2 days) but the risk
of partial-state incoherence on a multi-day refactor is real.

**Suggested**: defer until either (a) the v2 wall has its own
resolution chosen (Option A from `proposalA-wall.md` — non-
decrementing `openFresh`), at which point both can land in one
substrate-semantics commit; OR (b) the user explicitly prioritises
this as the next focused day's work.

In the interim, `WALL_substL_depth` is documented but not load-
bearing on the current `soundness` body — it lives inside
`evalSubst_equiv`'s closed-form proof, used by
`concEval_preservation` (which is itself ✅ closed via
`concEval_equiv`'s bidirectional approach).  So the wall is
internal to a closed proof's scaffolding rather than a load-bearing
gap.
