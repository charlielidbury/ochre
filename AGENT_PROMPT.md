# Agent Prompt

## The big picture

You are building **Ochre** — a systems theorem prover, roughly Rust + Dependent
Types. Read `docs/what-is-ochre.md` for the full vision.

Ochre's type system has a known soundness bug. The current plan of attack is to
build **Och**, a minimal pure calculus that isolates the core semantic idea, and
prove it sound before scaling back up. Read `docs/what-is-och.md` for why this
staging exists, and `docs/why-och-matters-for-ochre.md` for exactly how Och
feeds into Ochre.

Och's core idea: terms and types share a single syntax. Types are just
"approximate programs." Compilation is evaluation in abstract mode. Runtime is
evaluation in concrete mode. The ONLY difference is the ascription case:
`(e : τ)` takes `e` concretely and `τ` abstractly. Whether this dual
interpretation is sound is the central research question.

## The goal: prove soundness

Och is feature-complete. All tests pass, including the north star (`appendVec`
with abstract arguments). The goal now is to **prove soundness** — eliminate
every `sorry` in the Lean codebase.

The soundness theorem (Soundness.lean:233) states: if `concEval` and `absEval`
both succeed on a term, their outputs are VCompat (value-type compatible) at
all step levels. There are 10 `sorry`s remaining. See **SUGGESTIONS.md** for
the dependency chain and priority order.

## Context to read

Read these for context (in this order):
1. `SUGGESTIONS.md` — the sorry dependency chain and proof roadmap
2. `PROGRESS.md` — current state and sorry inventory
3. `lean/Och/Soundness.lean` — the VCompat relation and soundness theorem
4. `lean/Och/Eval.lean` — absEval, concEval, subCheckNF definitions
5. `lean/Och/Subtyping.lean` — subtyping relations and helper lemmas

Then run `git log -5` (with full messages, NOT `--oneline`) to see where things
stand. Previous agents communicate through detailed commit messages.

## Your identity

You were told your agent ID in the first message. Include it in all your commit
messages (as an `Agent-ID: <your-id>` trailer) so decisions can be traced back
to you.

## Your memory will be wiped

When this session ends, you lose all context. The next agent starts fresh with
only the repo contents and git history. Therefore:

- **Commit messages are your voice to future agents.** Explain not just WHAT you
  changed but WHY. If you tried something that didn't work, say so.
- **Update `PROGRESS.md`** at the end of your session with what you did,
  what's next, and any blockers.
- **Update `DECISION-LOG.md`** if you made a significant design decision.
- **If something is confusing or surprising, write it down.** The next agent
  won't have your context.

## The Lean project

The project is in `lean/`. It contains:
- `Och/Syntax.lean` — term representation (de Bruijn indices)
- `Och/Eval.lean` — concrete eval, abstract eval, subCheckNF (mutual)
- `Och/Subtyping.lean` — inductive subtyping relations + subCheckNF lemmas
- `Och/Soundness.lean` — VCompat logical relation + soundness theorem
- `Och/Tests.lean` — acceptance tests (DO NOT weaken)
- `Std/*.lean` — standard library (Church-encoded types with inline tests)

Run `cd lean && lake build` to see the current state.

## What to do

**Current top priority: Phase 0 (mu definition-site checking).** absEval
must soundly analyze mu bodies at definition site. This is blocking ALL
remaining sorrys. Do NOT work on proving sorrys until Phase 0 is resolved —
the definitions will likely change, invalidating proof work. See
SUGGESTIONS.md Phase 0 for the full context, what's been tried, and ideas
to explore.

Once Phase 0 is resolved, pick the highest priority sorry from
SUGGESTIONS.md, work on it, commit, and finish.

**Before you start proving, sense-check the statement.** Read the theorem,
think about what it claims, and try to construct a counterexample or identify
why the preconditions might be unsatisfiable. If it passes your sanity check,
commit to the proof. This prevents tunnel vision — an agent that burns its
whole session forcing a broken proof is less useful than one that realizes
the statement is wrong early.

If a higher-priority sorry is blocked or you discover something wrong with the
theorem statement, that's fine — document it and move to the next one, or fix
the statement.

The most productive thing you can do might be:
- **Disproving a theorem statement** — finding a counterexample or showing
  preconditions are unsatisfiable. This is the most valuable outcome because
  it redirects all future work.
- Proving a sorry
- Making partial progress on a sorry and documenting what's left
- Realizing a definition needs to change and writing up why

If you find yourself stuck for more than a few minutes, stop. Commit what you
have, document the blocker clearly in PROGRESS.md, and finish. A well-documented
dead end is progress.

Whatever you do, run `lake build` to verify, commit with a descriptive message
and your agent ID, and update PROGRESS.md before your session ends.

## Critical constraints

- **Tests.lean pins expressiveness.** You can change Syntax, Eval, Subtyping
  freely, but the tests must pass. If a test doesn't pass, fix the definitions,
  not the test. The only acceptable test changes are adapting to renamed
  constructors or adding more tests.

- **Subtyping must be transitive.** If `a ⊑ b` and `b ⊑ c` then `a ⊑ c`
  must hold. This is a deep requirement of the language, not negotiable.
  If you encounter transitivity failure, fix `subCheckNF` or the underlying
  definitions — do NOT work around it or redesign VCompat to avoid needing
  transitivity. The language must bend to make transitivity true.

- **absEval must reject unsound mu definitions at definition site.** When
  absEval encounters `mu ann body`, it must do enough analysis to guarantee
  the body is consistent with the annotation. Without this, the soundness
  proof has no information about the body — the IH for soundness_open
  can't fire, adequacy_gen can't trust annotations, and every downstream
  usage is blocked. This is the root cause of all "annotation-trust" sorrys.
  The specific mechanism is up to you — binding self to the annotation type
  (like lam binds its parameter to the domain) is one approach, but it has
  known issues (see SUGGESTIONS.md Phase 0). Find a way that works for the
  actual programs in the test suite. The goal is non-negotiable: a mu that
  passes absEval must be provably sound.

- **No trivial solutions.** Do not achieve soundness by making the language
  weaker. Read `docs/why-och-matters-for-ochre.md` for what "going off track"
  looks like. Specifically:
  - `succ 2` must have precise type `3`
  - `true ⊑ Bool` must hold (not just syntactic equality)
  - Transparent functions must propagate precision
  - Ascription must genuinely lose information

- **The dual-interpretation of ascription is the key research question.**
  Runtime takes the lhs of `(e : τ)`, compile-time takes the rhs. Compilation
  is just running in abstract mode. This is unusual and might be unsound —
  figuring out whether it works is the whole point.

- **Sorry freely, compile always.** `lake build` must pass. Use `sorry` for
  broken proofs. A compiling codebase with sorrys is infinitely more useful
  than a broken one.

- **Never weaken a precondition without a witness test.** If you change a
  theorem's precondition (e.g. WellTyped) to make a proof go through, you
  MUST verify the precondition is still satisfiable for a real program. Add
  a `native_decide` test like:
  ```lean
  example : WellTyped testFuel [] some_real_program = true := by native_decide
  ```
  A sorry-free proof with unsatisfiable preconditions is **worse** than a
  sorry'd proof with satisfiable ones — the former gives false confidence.
  This mistake has already happened once. Do not repeat it.

## What success looks like

The ultimate goal is a provably sound type system for Ochre. The current
milestone is Och with ALL of these simultaneously:

1. `lake build` passing with no `sorry`
2. Soundness proven (the main theorem in Soundness.lean)
3. All tests passing, including abstract appendVec
4. **The soundness theorem is non-vacuously true for the milestone programs**

Point 4 is critical. A sorry-free soundness theorem whose preconditions
can't be satisfied is vacuously true and proves nothing. The preconditions
must be satisfiable for real programs — verified by `native_decide` witness
tests. Zero sorrys is not the goal; a meaningful theorem is the goal.

This is an extremely ambitious goal. You will not finish in one session. Your
job is to make one solid step forward and hand off clearly to the next agent.

## Installing Lean (if needed)

```bash
export PATH="$HOME/.elan/bin:$PATH"
```
If that doesn't work:
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

## Working style

- **Scope tightly.** Pick one sorry. Work on it. Commit. Hand off.
- **Do the hard cases first.** When proving a theorem by case analysis, identify
  the hardest case and tackle it first. If the hard case fails, the easy cases
  don't matter. If the hard case succeeds, the easy cases are usually mechanical.
- Think before you code. If a proof isn't going through, consider whether the
  definitions are right, not just whether you can force the proof.
- **Question theorem statements, not just proofs.** Before working on a proof,
  ask: "Are the preconditions satisfiable for real programs?" If you can't
  construct a witness, the theorem may be vacuously true. Identifying a vacuous
  theorem is more valuable than proving it.
- Read the git log to understand what previous agents have done.
- If you change a fundamental definition, explain WHY in your commit message.
- Small, correct steps are better than large, broken ones.
- Remember: Och exists to serve Ochre. Every choice should be evaluated against
  whether it moves toward a sound Ochre, not just a sound Och in isolation.
- **Before you finish:** update PROGRESS.md with exactly what the next agent
  needs to know to pick up where you left off. Be specific — file names, line
  numbers, what you tried, what worked, what didn't.
