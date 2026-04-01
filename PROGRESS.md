# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We are replacing `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale.

### What exists (inherited from main branch)

- [x] Core Och mechanization in Lean 4 (Syntax, Eval, Subtyping)
- [x] Soundness and monotonicity fully proven (0 sorry) for the OLD syntax
- [x] All §6 tests passing for the OLD syntax
- [x] Church encodings for Bool, Nat, Pair, Array, Vec
- [x] Concrete recursive fix with thunked branches (concEvalS)
- [x] Closure-based evaluators (concEvalC, absEvalC) in Closure.lean
- [x] Self-type subtyping (iota intro/elim) in Subtyping.lean

### What needs to happen (the mu experiment)

- [ ] **Replace fix+iota with mu in Syntax.lean** — one constructor instead
  of two. `mu : Name → (ann : Expr) → (body : Expr) → Expr`.
- [ ] **Update Eval.lean** — concEval unrolls mu (like fix), absEval
  normalizes body under binder (like iota). The hard part: mu-elim in the
  app case for type-directed evaluation of stuck variables.
- [ ] **Update Subtyping.lean** — mu-mu annotation comparison, self-intro,
  self-elim. Replace fix_cong/iota_body with mu_body.
- [ ] **Update Tests.lean** — adapt .fix and .iota uses to .mu. All tests
  must still pass.
- [ ] **Update proof files** — Soundness.lean, Monotonicity.lean,
  Closure.lean. Sorry freely; the goal is compilation, not proofs yet.
- [ ] **Delete SoundnessS.lean** — stalled, superseded.
- [ ] **Type-directed evaluation** — env must carry type info for stuck
  variables. This is the biggest design question.
- [ ] **Dependent Nat with mu** — self-typed Church Nat, typed add.

### Key files

| File | Status | Notes |
|------|--------|-------|
| Syntax.lean | NEEDS REWRITE | Replace fix+iota with mu |
| Eval.lean | NEEDS REWRITE | New mu eval semantics |
| Subtyping.lean | NEEDS REWRITE | New mu subtyping rules |
| Tests.lean | NEEDS ADAPTATION | .fix/.iota → .mu |
| Soundness.lean | WILL BREAK | Sorry the mu cases |
| Monotonicity.lean | WILL BREAK | Sorry the mu cases |
| Closure.lean | JUDGMENT CALL | Adapt or remove, either ok |
| SoundnessS.lean | DELETE | Stalled, superseded |
| CounterexampleTest.lean | KEEP | May not be relevant post-mu |

### Design document

**READ `docs/ideas/merge-fix-iota.md` FIRST.** It contains:
- Why fix and iota are the same primitive
- Why the annotation is load-bearing
- The worked example showing exactly what typing rules are needed
- Open questions and sharp edges
