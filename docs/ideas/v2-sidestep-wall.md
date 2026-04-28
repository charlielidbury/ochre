# V2 sidestep attempt: wall stands

**Status:** sidestep DOES NOT eliminate the v2 wall.  The wall is
**substrate-arithmetic** (closeAll-substL commutation), not
eval-related, so β-reduction bisimulation does not address it.

## Recap

The wall-2 agent recommended:

> Try sidestep first: prove iota/unfoldFix arms via β-reduction
> bisimulation (use existing `evalSubst` semantic preservation)
> rather than syntactic `closeAllAt_substL` commutation.

The intended pattern was:

1. Engine: `bodyB' := substL bodyB 0 a`, `bodyB'' := evalSubst bodyB'`,
   then `subCheckSubst _ _ _ a bodyB''`.  IH: `Subtype' a bodyB''`.
2. Bridge `bodyB''` back to `bodyB.subst 0 a` (declarative form) via
   the existing `unfold_iota_R` / `unfold_fix_R` step lemmas + an
   `evalSubst_equiv` analog of `concEval_equiv` (bidirectional
   subtype equivalence between input and result of evalSubst).
3. Apply `iota_intro` declaratively.

## What I built

`lean/Och/Soundness/SubCheckSubstFallback.lean` (~340 LOC):

- Four **arm-lemmas** (`iota_intro_arm`, `unfold_fix_R_arm`,
  `unfold_fix_L_arm`, `unfold_iota_L_arm`) — each consumes IH
  derivations and a substitution bridge, produces the parent
  `Subtype'` via the corresponding declarative rule.
- Four **substitution-bridge** lemmas — each `sorry`'d, with
  precise wall annotations.
- Helper `closeAllAt_zero` (closeAllAt c 0 = id) for the d=0
  specialisation.

The arm-lemmas themselves are **structurally complete**: given a
working substitution bridge, they produce the parent `Subtype'`.
The wall is fully isolated to the bridges.

## Why the sidestep does NOT eliminate the wall

The β-reduction bisimulation handles only the **evalSubst step**.
After the bridge, the engine's `substL bodyB 0 a` still has to be
related to the declarative `bodyB.subst 0 a`.  In the closed form
we'd need:

```
closeAll d (substL bodyB 0 a)
  ≡_{Subtype'}  (closeAllAt 1 d bodyB).subst 0 (closeAll d a)
```

This is **exactly the v2 wall** (closeAllAt_substL for arbitrary
substituees, see `docs/ideas/proposalA-wall-v2.md`).  The eval
step bisimulation doesn't help: the substituee `a` is still
arbitrary, the off-by-one in closeAllAt_substL is still there.

## Where the sidestep WOULD work: depth 0

At d=0 (top-level, no level-vars):

- `closeAll 0` is the identity (proved as `closeAllAt_zero`).
- `substL bodyB 0 a = bodyB.subst 0 a` via
  `substL_eq_subst_no_levelvars` when both `bodyB` and `a` are
  no-level-vars.

So at d=0 the substitution bridge reduces to the **eval-step
bridge** alone:

```
Subtype' (evalSubst (bodyB.subst 0 a)) (bodyB.subst 0 a)
  ∧  Subtype' (bodyB.subst 0 a) (evalSubst (bodyB.subst 0 a))
```

This is provable by mirroring `concEval_equiv` (in
`Soundness/ConcEvalPreservation.lean`) for `evalSubst`.  The proof
would be ~150-200 LOC (each evalSubst arm has a corresponding
declarative rule via `Subtype'.trans` with the existing
`B1+B2 SubtypeSteps` lemmas).

## What this DOES unlock

Even walled, the new arm-lemma file is useful:

- The four parent `Subtype'` constructions are localised and
  reviewable.
- Future work has a clear contract: prove the four substitution
  bridges, fallback arms close.
- At d=0, only `evalSubst_equiv` is missing — much smaller piece
  than the v2 wall.

## Recommendation

Two paths forward:

1. **Engine-side fix** (Option 2 from v2 doc): refactor `openFresh`
   and the engine's substL-uses to a "shift-not-decrement"
   semantics.  Removes the closeAllAt_substL obstacle entirely.
   ~1-2 days of substrate engineering.

2. **Depth-0 specialisation**: write `evalSubst_equiv` (mirror of
   `concEval_equiv`), use the d=0 versions of the arm-lemmas to
   discharge `subCheck_sound`'s depth-0 fallback case.  Leaves
   the recursive (depth>0) case as the standing wall, but
   collapses the wall set: only structural arms entering binders
   need closeAllAt_substL.  ~1 day.

Option 2 reduces the wall to "structural arms create level-vars
that the fallback arms can't see through".  That's a smaller,
cleaner formulation than the current "v2 wall on arbitrary
substituees".

## File locations

- `lean/Och/Soundness/SubCheckSubstFallback.lean` (NEW, ~340 LOC) —
  arm-lemmas + walled bridges.
- `lean/Och.lean` — imports updated.
