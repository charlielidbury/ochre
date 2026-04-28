# Proposal A wall v2: closeAllAt_substL remains open

**Status:** v1 wall (closeAll_openFresh) **CLOSED** via Option D —
"correct the equation, not the operator."  v2 wall now exposed:
`closeAllAt_substL_OPEN_QUESTION` for arbitrary substituees.

## What happened in this session

### v1 wall: closeAll_openFresh — CLOSED

The originally-stated `closeAll_openFresh_OPEN_QUESTION`
   `closeAll (lvl+1) (openFresh body lvl) = closeAllAt 1 (lvl+1) body`
is provably **false**.  On a level-var `levelBvar lvl'` (`lvl' < lvl`),
LHS produces `bvar (lvl - lvl')` but RHS produces `bvar (lvl - lvl' + 1)`.

But this equation is also **not what soundness needs**.  The post-
Proposal-A C7 recursion needs the engine's `openFresh` recursive call
to match the structural lam/iota/fix subterm of `closeAll d (.lam dom
body)`, which expands to `.lam (closeAllAt 0 d dom) (closeAllAt 1 d
body)`.  When the engine opens at level=depth and pushes onto tyCtx
(new size = depth+1), the lemma we want is

   closeAll (depth+1) (openFresh body depth) = closeAllAt 1 depth body

i.e., RHS is `closeAllAt 1 depth body`, **not** `closeAllAt 1 (depth+1)
body`.  This corrected equation **holds** under

  * `body.closedAtLvl 1 = true` — only `bvar 0` allowed;
  * `body.lvarLT lvl = true` — every level-var index `< lvl`.

Proof: lockstep induction on `j` (substL position = closeAllAt
counter), generalized as `closeAllAt_substL_levelBvar`.

This is **Option D**: don't add a new substrate operator; just write
the right equation and prove it.  No engine change, no new API.

LOC added: ~150 to `lean/Och/Soundness/CloseAll.lean`.  Build green.

### v2 wall: closeAllAt_substL for arbitrary substituees

The companion `closeAllAt_substL_OPEN_QUESTION`,
   `closeAllAt c d (substL e j s) = substL (closeAllAt c d e) j (closeAllAt c d s)`,
is also false as stated.  On `e = .bvar (levelOffset + lvl)` with
`lvl < d - 1` and `j = 0`, LHS = `bvar (d-1-lvl+c)` (substL skips
level-vars), RHS = `bvar (d-2-lvl+c)` (substL decrements the closed
image because it's `> j`).

**But** `closeAllAt_substL_levelBvar` (the v1 helper) handles the case
where `s = levelBvar lvl` (the substituee is itself a level-var).
This is the **only** case needed for `closeAll_openFresh`; the
equation form is `closeAllAt j (lvl+1) (substL e j (levelBvar lvl)) =
closeAllAt (j+1) lvl e` (lockstep counter, off-by-one absorbed by
`d` decrement).

For the **iota_intro / unfoldFixR / iotaElim / unfoldFixL** arms of
`subCheckSubst`, the substituee is the term itself (`a` or `b`),
NOT a level-var.  So `closeAllAt_substL_levelBvar` doesn't apply
directly.

#### The genuine wall

We need a "closeAllAt commutes with substL on arbitrary closed
terms" lemma.  The natural shape:

   closeAllAt c d (substL e j s) =
     ??? (closeAllAt c d e) ??? (closeAllAt c d s)

The LHS at a level-var produces `bvar (d-1-lvl+c)`; the RHS's substL
will decrement that if the index `> j`.  The off-by-one is genuine
because `closeAllAt` produces images at de-Bruijn indices in the
range `[c, d-1+c]` and these get caught up in substL's decrement
discipline.

##### Possible resolutions

1. **Lockstep lemma**: state at `j = c` (substL position equals binder
   counter), with stronger hypotheses (`e.closedAtLvl (c+1)`).  In
   that regime, ordinary bvars in `e` are `≤ c = j`, so substL only
   substitutes (no decrement); the level-var image at index `d-1-
   lvl+c` is `≥ c+1 > j`, so it would be decremented to `d-2-lvl+c`.
   STILL OFF BY ONE.

   To fix: the closed substituee `closeAllAt c d s` would need to be
   "shifted" by 1 to compensate.  i.e.,

      closeAllAt c d (substL e c s) = (closeAllAt (c+1) d e).subst c
        ((closeAllAt c d s).shift 1 0)

   Wait — that uses `Expr.subst` (decrementing) on `closeAllAt (c+1)
   d e` — at counter c+1, level-var images live at `d-1-lvl+c+1`,
   which after decrement become `d-1-lvl+c`.  Match LHS!  Let's
   verify on a level-var `e = levelBvar lvl` with `lvl < d`:
   * LHS: `closeAllAt c d (substL (levelBvar lvl) c s) =
     closeAllAt c d (levelBvar lvl) = bvar (d-1-lvl+c)` (substL skips).
   * RHS: `(closeAllAt (c+1) d (levelBvar lvl)).subst c (...) =
     (bvar (d-1-lvl+c+1)).subst c (...) = bvar (d-1-lvl+c)` (since
     `d-1-lvl+c+1 > c`, decrements by 1).  ✓

   And on an ordinary bvar `e = bvar k` with `k ≤ c` (closedAtLvl c+1):
   * LHS: `substL (bvar k) c s`.  If k = c: returns s.  Else k < c:
     `bvar k`.
     - case k = c: closeAllAt c d s = closeAllAt c d s.
     - case k < c: closeAllAt c d (bvar k) = bvar k.
   * RHS: `(closeAllAt (c+1) d (bvar k)).subst c ((closeAllAt c d s).shift 1 0)`.
     - `closeAllAt (c+1) d (bvar k)` = `bvar k` (since k < levelOffset).
     - `(bvar k).subst c (...)` = if k = c then `(closeAllAt c d s).shift 1 0`
       else if k > c then `bvar (k-1)` else `bvar k`.
     - case k = c: result is `(closeAllAt c d s).shift 1 0`.
       But LHS is `closeAllAt c d s` (no shift).  **OFF BY ONE!**

   Hmm.  So this lockstep+shift form also fails on the substitution
   point.  The issue: at the substitution point `k = c`, the LHS
   delivers `closeAllAt c d s` directly, but the RHS needs to
   "compensate for the binder being eliminated" by shifting.

   This is where the substrate's two operations — `substL`
   (decrementing-style) and the closeAllAt's preservation discipline
   — fundamentally part ways.  No equation in the `(c, d, j, e, s)`
   parameter space appears to capture it cleanly.

2. **Engine-side fix (Option A from v1)**: refactor `openFresh` and
   the engine's substL-uses to a "shift-not-decrement" semantics,
   then closeAllAt commutes naturally.  Invasive (~ 1-2 days), but
   removes the off-by-one for good.

3. **Bridging via `Expr.subst`**: prove `closeAllAt_subst` (using
   `Expr.subst` directly, not `substL`) — but this has the same
   off-by-one (subst also decrements).

4. **Sidestep**: prove the iota/fix/etc. arms via a different
   strategy that doesn't need `closeAllAt_substL`.  E.g., reason
   about the substitution at the engine level via `evalSubst`'s
   semantic specification (β-reduction equivalence rather than
   syntactic substitution commutation).

#### Recommendation for next agent

* The **v1 win** (closeAll_openFresh) is enough to unblock the
  lam/iota/fix structural arms of subCheckSubst_sound_arm_neutral.
  These are the high-value cases.

* The **iota_intro / unfold* arms** still need substrate engineering.
  Recommend trying **Option 4 (sidestep)** first: see if the
  soundness proof can use the engine's β-reduction bisimulation
  rather than syntactic substitution commutation.  If that fails,
  fall back to **Option 2 (engine-side fix)**.

* The **engine-side fix** is what the v1 wall doc recommended — and
  is likely the right long-term answer.  Removes the closeAllAt_
  substL obstacle entirely.

## What's in the codebase

```
lean/Och/Soundness/CloseAll.lean
  Expr.lvarLT             -- predicate: every level-var < lvl
  lvarLT_mono             -- monotonicity
  closeAllAt_substL_levelBvar  -- the helper (substituee = level-var)
  closeAll_openFresh           -- v1 wall CLOSED
  closeAll_openFresh_OPEN_QUESTION  -- alias (corrected statement)
  closeAllAt_substL_OPEN_QUESTION   -- v2 wall, still sorry'd
```

## Numbers

* sorries before: 2 (CloseAll.lean) + 3 (SubCheckSubstNeutral.lean)
* sorries after: 1 (CloseAll.lean) + 3 (SubCheckSubstNeutral.lean)
* LOC added: ~150 (CloseAll.lean: 720 → 924)
* Build: green

The `subCheckSubst_sound_arm_neutral_closeAll` sorry remains, but
its body now needs only the (still-open) `closeAllAt_substL` for
the iota/fix arms; the lam arm should go through with
`closeAll_openFresh`.
