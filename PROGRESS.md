# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **6 sorrys** and all tests (including WellTyped witnesses).

- **Subtyping.lean: SORRY-FREE**
- **Monotonicity.lean: 3 sorrys** (env extend lemmas + absEval_mono, sorry'd for de Bruijn migration)
- **Soundness.lean: 3 sorrys** (env extend lemmas + soundness_gen, sorry'd for de Bruijn migration)

**Total: 6 sorrys.** All tests pass including WellTyped witnesses.

### Recent changes (2026-04-02, agent ochre-lean-20260402-123003)

**Phase 3: De Bruijn indices — COMPLETE.**

Migrated the entire codebase from named variables to de Bruijn indices.
This is the biggest mechanical change in the project's history.

**What changed:**

1. **Syntax.lean:** `Expr` now uses `bvar : Nat` (de Bruijn index) instead of
   `var : Name`. `lam` and `mu` no longer carry binder names. Added `shift`
   (increment free vars) and `subst` (substitute + shift down). Added `Named`
   type + `toExpr` converter so test terms can be written readably.

2. **Eval.lean:** `Env = List Expr` (positional, env[k] = value for bvar k).
   `Env.extend` shifts existing entries when entering a binder. Beta-reduction
   uses **substitution** (not env extension) — subst argument into body, then
   re-evaluate. This is a semantic change from the old env-based beta.

3. **Subtyping.lean:** `subCheckNF` uses `Env.extend` for ctx management (with
   shifting). Domains are normalized on BOTH sides before comparison (needed
   because subst-produced domains contain unreduced applications). `inferType`
   uses positional lookup (ctx.get? k). No variable renaming needed anywhere.

4. **Monotonicity.lean:** Sorry'd (was sorry-free). Needs reproving with new
   env extension patterns.

5. **Soundness.lean:** Sorry'd (was 3 sorrys). Needs reproving with new env
   and subst-based beta. WellTyped updated to use Env.extend and subst.

6. **Tests.lean:** All definitions use Named syntax + `n` converter. All tests
   pass. One behavioral change: `concEval toZero one'` now terminates (= zero')
   because subst-based beta reuses normalized mu bodies instead of re-evaluating.

7. **CounterexampleTest.lean:** Deleted (named-variable-specific concepts like
   freeVars/evalFreeVars; preserved in git history).

**Key design decisions:**

- **Hybrid evaluation:** Env-based for normalization under binders (lam, mu body),
  substitution-based for beta-reduction (app-lam, app-mu). This avoids the closure
  problem (env-based de Bruijn beta would need closures to track definition-site envs).

- **Env.extend shifts all entries:** When entering a binder, existing env/ctx entries
  are shifted up by 1 so their bvar indices stay correct at the new depth. New entries
  (neutrals for lam, mu values for mu) are NOT shifted because they're already at the
  correct depth. BUT domain types added to subCheckNF's ctx ARE shifted (they're from
  the outer scope).

- **Domain normalization on both sides:** With subst-based evaluation, domains can
  contain unreduced applications (e.g., `zero' Type Unit' (λacc. ...)` instead of
  `Unit'`). Both sides are normalized before comparison.

- **concEval behavioral change:** `concEval` for recursive mu + Church branching now
  terminates (was divergent). The subst-based beta reuses the already-normalized mu
  body, so the recursive call's result is embedded in the term rather than re-computed.
  The test was updated to reflect this.

**What's next (for the next agent):**

Phase 3 is done. The next phases from SUGGESTIONS.md:

1. **Reprove monotonicity (absEval_mono).** The proof structure is the same
   (induction on SubtypeCore), but the details of env extension (Env.extend
   with shifting) and beta (substitution) need updating. Start with the env
   extend lemmas (envSubCore_extend, envSubCore_extend_sub), then the main
   theorem. Key files: Monotonicity.lean.

2. **Reprove soundness_gen.** Same structure but harder. The pre-existing
   blockers remain (SubtypeCore too weak for asc case). Start with env
   extend lemmas, then the non-asc cases. Key files: Soundness.lean.

3. **Phase 4:** Address the SubtypeCore weakness (change output relation).

### Previous changes

See git log for full history. Key milestones:
- Phase 1 (milestone tests): All M1-M4 pass including abstract appendVec
- Phase 2 (non-vacuous WellTyped): Bool-valued with subCheckNF, 11 witnesses
- Phase 3 (de Bruijn): THIS SESSION
