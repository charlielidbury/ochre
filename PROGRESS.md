# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale.

### Completed

- [x] **Replace fix+iota with mu in Syntax.lean** — one constructor:
  `mu : Name → (ann : Expr) → (body : Expr) → Expr`.
  Updated `subst`, `freeVars`, `evalFreeVars`.
- [x] **Update Eval.lean** — all three evaluators (concEval, absEval, concEvalS)
  rewritten for mu. concEval unrolls (like fix). absEval normalizes body under
  binder AND normalizes annotation (returns mu term, not annotation).
  App case handles mu-elim for both concEval and absEval.
- [x] **Update Subtyping.lean** — Subtype' now has `mu_body` (replaces both
  `fix_cong` and `iota_body`). SubtypeTrans shape lemmas updated.
  `subCheckNF` handles mu-mu (body covariant), self-intro, self-elim.
  `inferType` handles mu via self-type elimination.
- [x] **Update Tests.lean** — all `.fix` uses → `.mu`, all `.iota` uses →
  `.mu x .type body`. ALL TESTS PASS. Key adaptations:
  - absEval of fix-like mu returns the mu term itself (not the annotation)
  - Tests that checked `absEval fixExpr = some annotation` now either check
    `absEval fixExpr = some fixExpr` (when mu is its own normal form) or
    use subtyping tests (which check via self-elim)
- [x] **Update Soundness.lean** — sorry'd the soundness_gen proof. The proof
  structure changes because absEval now returns mu terms (not annotations),
  and the app case needs mu-elim handling. WellTyped updated for mu.
  EnvNoFix removed (no longer needed).
- [x] **Update Monotonicity.lean** — sorry'd absEval_mono, absEval_mono_trans,
  absEval_succeeds_envsub, absEval_evalFreeVars_general. Key issue: mu_body
  requires same annotation, but annotations normalized in different envs
  may differ. EnvSub/EnvSubTrans helpers preserved.
- [x] **Gut Closure.lean** — closure-based evaluators deeply tied to old
  fix/iota constructors. Gutted with explanation. Rebuild deferred.
- [x] **Delete SoundnessS.lean** — stalled with 7 sorrys, superseded.
- [x] **Update CounterexampleTest.lean** — compiles, no fix/iota references.

### Build status

`lake build` passes with **5 sorry warnings**:
- Monotonicity.lean: 4 (absEval_mono, absEval_mono_trans,
  absEval_succeeds_envsub, absEval_evalFreeVars_general)
- Soundness.lean: 1 (soundness_gen)

All tests pass (native_decide). No other warnings.

### What needs to happen next

- [ ] **Prove absEval_evalFreeVars_general for mu** — the old proof was fully
  complete for fix/iota. The mu case needs handling for both body (like iota)
  and annotation (new). Should be straightforward: body case same as old iota,
  ann case like an additional sub-expression.
- [ ] **Prove absEval_mono for mu** — the mu case is non-trivial because
  mu_body requires same annotation but absEval normalizes annotations in
  different envs. Possible fix: add a more general Subtype' constructor
  for mu that allows different annotations (mu_cong?), or prove annotations
  normalize consistently under EnvSub.
- [ ] **Prove soundness_gen for mu** — the proof structure changes because
  absEval returns mu terms. The mu case in soundness should combine the old
  fix reasoning (concrete unrolls, abstract preserves) with the old iota
  reasoning (normalize body under binder). The app-mu case needs the
  function IH to give a mu, then mu-elim unfolds.
- [ ] **Rebuild Closure.lean** — closure-based evaluators with `cmu`/`amu`
  constructors replacing cfix/ciota/aiota.
- [ ] **Type-directed evaluation** — env must carry type info for stuck
  variables. This is the biggest design question for abstract appendVec.
- [ ] **Dependent Nat with mu** — self-typed Church Nat, typed add.

### Key design observations from this session

1. **absEval of mu returns the mu itself** (when already normalized). This is
   different from old fix (which returned the annotation). The subtyping tests
   still pass because self-elim unfolds `mu x ann body ⊑ T` to
   `body[x := mu x ann body] ⊑ T`.

2. **iota → mu translation uses `ann = .type`**. All iota self types get
   annotation Type. This works because the mu-mu subtyping rule compares
   bodies covariant, and the self-intro/self-elim rules don't depend on the
   annotation.

3. **The mu-mu subtyping rule in subCheckNF is body-covariant only** (not
   annotation-comparing). This matches the old iota-iota rule. Victor's
   annotation comparison trick (for preventing divergent recursive type
   unfolding) is not yet needed — the fuel limit handles termination. When
   recursive types are added (roadmap step 9), annotation comparison may
   become necessary.

4. **absEval's mu-elim in the app case uses substitution + re-evaluation**.
   When `absEval f = mu x ann body` and we need to apply it:
   ```
   let unfolded := body.subst x (.mu x ann body)
   absEval Γ unfolded
   ```
   This substitutes the self-reference and re-evaluates. Fuel prevents
   divergence. The approach works because body was normalized under
   `(x, var x)`, so `var x` in body gets replaced with the actual mu.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | ✅ Done | 0 |
| Eval.lean | ✅ Done | 0 |
| Subtyping.lean | ✅ Done | 0 |
| Tests.lean | ✅ All pass | 0 |
| Soundness.lean | ⚠️ Sorry'd | 1 |
| Monotonicity.lean | ⚠️ Sorry'd | 4 |
| Closure.lean | 🔨 Gutted | 0 |
| CounterexampleTest.lean | ✅ Done | 0 |
| SoundnessS.lean | 🗑️ Deleted | - |
