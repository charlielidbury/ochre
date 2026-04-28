# tyCtxPush_bridge_WALL — convention mismatch in dispatch arm packages

**Status:** structural wall, identified 2026-04-28 by lam-lam arm
attempt (commit `568f148`).

**Affects:** all three structural dispatch arms (lam-lam, iota-iota,
fix-fix).  Each arm's body sub-call recurses into a depth-grown
`tyCtx.push annB`; the IH yields a derivation against the raw
context but the arm-package expects a `closeAll`-translated head.

## The mismatch

After unfolding `subCheckSubstMatch.eq_def` for the `.lam, .lam`
arm, the engine's body sub-call is:

```
subCheckSubst fuel (tyCtx.push domB) seen (openFresh bodyA depth)
                                          (openFresh bodyB depth)
```

Applying the dispatch's `_ih` to this (with closedness preconditions)
gives:

```
Subtype' (liftSeenList (tyCtx.size + 1) seen)        -- seen depth: +1
         (tyCtxToCtx (tyCtx.push domB))              -- raw context
         (closeAll (tyCtx.size + 1) (openFreshTop bodyA tyCtx.size))
         (closeAll (tyCtx.size + 1) (openFreshTop bodyB tyCtx.size))
```

`tyCtxToCtx (tyCtx.push domB) = domB :: tyCtxToCtx tyCtx` — the head
is **raw** `domB`.

But `arm_lam_lam_compose` (in `SubCheckSubstStructural.lean`) requires:

```
ih_body : Subtype' (liftSeenList tyCtx.size seen)    -- seen depth: original
                   (closeAll tyCtx.size domB :: tyCtxToCtx tyCtx)
                   ...
```

The head is `closeAll tyCtx.size domB`, **not** raw `domB`.

`closeAll d e = e` only when `e` has no level-vars at depths `< d`.
In the dispatch context, `domB.lvarLT tyCtx.size = true` says the
level-vars in `domB` are `< tyCtx.size` — i.e., all in the range
that `closeAll tyCtx.size` *will* translate.  So
`closeAll tyCtx.size domB ≠ domB` in general.

## Why the arm-package has it that way

The arm-package was specified to produce the conclusion against a
context where ALL entries are in their canonical (closeAll'd) form.
This is consistent with:

* `Subtype'_lvar_via_tyCtx` (in `CloseAll.lean`) closes the C7 ascent
  by producing `Subtype' S (tyCtxToCtx tyCtx) (closeAll _ (bvar
  lvar)) (ty.shift _ _)` — note the *conclusion's RHS* is raw
  `tyCtx[lvl].shift _ _`, not `closeAll _ tyCtx[lvl].shift _ _`.

So the convention is mixed: bvars on the LHS get closeAll'd, but the
ascended type on the RHS does not.  This works for the leaf case but
breaks for binders — the inductive Ctx growth needs a consistent
treatment.

## Two consistent designs

### Design A: tyCtxToCtx applies depth-stratified closeAll

Redefine:

```lean
def tyCtxToCtx (tyCtx : Array Expr) : Ctx :=
  (tyCtx.toList.mapIdx (fun i e => closeAll i e)).reverse
```

So entry at original-index `i` (pushed at depth `i`) is closeAll'd
at depth `i`.  After this:

* Sub-derivation context after pushing `domB` at depth `tyCtx.size`
  is `tyCtxToCtx (tyCtx.push domB) = closeAll tyCtx.size domB ::
  tyCtxToCtx tyCtx` — matches the arm-package.
* `Subtype'_lvar_via_tyCtx`'s conclusion RHS becomes
  `(closeAll lvl tyCtx[lvl]).shift (tyCtx.size - lvl) 0` — needs a
  re-derivation but should still close.

Cost: every `tyCtxToCtx` use re-examined; ~4-6 hour rewrite.

### Design B: arm-packages take raw heads

Redefine `arm_lam_lam_compose` (and iota/fix counterparts) so
`ih_body`'s Ctx head is raw `domB`, not `closeAll _ domB`:

```
(ih_body : Subtype' ... (domB :: tyCtxToCtx tyCtx) ...)
```

But then the body's `Subtype'.lam_body` introduction needs the
binder type to be `domB` (raw), and the sub-derivation's level-var
references to depth `tyCtx.size` would translate to `bvar 0` —
which looks up the raw `domB`, not `closeAll _ domB`.

This is potentially fine for soundness but loses the
"closeAll'd-everywhere" canonical form.  Costs:
re-examining `subCheckSubst_arm_lam_lam_struct`'s body and any
other consumer.

### Recommendation

Design A is more uniform: the canonical form is "closeAll'd
everywhere".  But it's expensive (~4-6 hours).  Design B is cheaper
but the soundness tower's invariant becomes context-dependent
(some entries closeAll'd, others raw).

### Design A: implementation plan

The cascade of changes:

1. **`Och/Soundness/CloseAll.lean:63`** — redefine `tyCtxToCtx`:
   ```lean
   def tyCtxToCtx (tyCtx : Array Expr) : Ctx :=
     (tyCtx.toList.mapIdx (fun i e => closeAll i e)).reverse
   ```
   Or equivalently using `Array.foldl` with depth tracking.

2. **`Och/Soundness/CloseAll.lean:tyCtxToCtx_get?_at`** — return the
   depth-stratified-closeAll'd entry: `closeAll lvl tyCtx[lvl]`.

3. **`Och/Soundness/CloseAll.lean:Subtype'_lvar_via_tyCtx`** —
   conclusion changes from `ty.shift _ _` to
   `(closeAll lvl ty).shift _ _`.  Re-prove using the new
   `tyCtxToCtx_get?_at`.

4. **`Och/Soundness/SubCheckSubstNeutral.lean:liftSeenList`** —
   apply closeAll to entries:
   ```lean
   def liftSeenList (depth : Nat) (seen : List (Expr × Expr)) : Seen :=
     seen.map (fun (a, b) => (depth, closeAll depth a, closeAll depth b))
   ```

5. **`Och/Soundness/SubCheckSubstSoundness.lean`** — the inline
   `seen.any` short-circuit case (line ~474) now closes via
   `Subtype'.hyp` directly: `(d, closeAll d a, closeAll d b) ∈
   liftSeenList d seen` matches the goal.  Remove the
   `seen_coherence_WALL` sorry.

6. **Dispatch arms (lam-lam, iota-iota, fix-fix)** — IH now produces
   the right Ctx shape: `tyCtxToCtx (tyCtx.push domB) = closeAll
   tyCtx.size domB :: tyCtxToCtx tyCtx` matches the arm-package's
   expected `closeAll tyCtx.size domB :: tyCtxToCtx tyCtx`.  Apply
   `arm_lam_lam_compose` directly.

7. **Audit other `tyCtxToCtx` / `liftSeenList` users** in
   `SubCheckSubstSoundness.lean` (~60 references) — most should
   work without change because they only mention these names in
   types, not by structural pattern-matching.  The
   `Subtype'_lvar_via_tyCtx` conclusion change is the only
   substantive ripple.

**Estimated effort:** 4-6 hours of focused work; ~200 LOC of
modifications; one `Subtype'_lvar_via_tyCtx` re-proof; many
sorries that this closes (~3 structural + 1 seen + ~6 fallback
arms = ~10 internal dispatch sorries, plus the seen short-
circuit at line 474).

**Risk:** the `Subtype'_lvar_via_tyCtx` re-proof might hit a new
arithmetic obstacle (the `closeAll lvl ty` term mixes depths).
Worst case: design A is *also* unsound and we fall back to design
B with a `domB ≡ closeAll d domB` bridge lemma.

In the interim: arm packages remain unprovable in the dispatch.
The dispatch arm closures wall on this; iota-iota and fix-fix have
identical shape and identical wall.

## Connections

* `proposalA-wall.md` — the original C7 wall.  This new wall is
  *downstream* of Proposal A: it's a refinement of the same
  closeAll-vs-raw question, applied to inductive context growth.
* `proposalA-wall-v2.md` — substrate decrement off-by-one in
  `closeAllAt_substL`.  Different family.
* `lvar-refactor.md` — replacing the `levelOffset` trick with a
  proper `.lvar` constructor would NOT close this wall (the
  closeAll convention question is independent of the level-var
  encoding).

## Surfaced by

`Close lam-lam structural arm in dispatch (partial progress)` agent,
commit `568f148`.  The agent successfully discharged:

* Closedness/lvarLT precondition extraction from parent hypotheses.
* Domain (contravariant) sub-call: applied `_ih`, got the required
  derivation.
* `contra = false` short-circuit closed as vacuous from `_h`.

The body sub-call's IH-vs-arm-package mismatch is the residue.
