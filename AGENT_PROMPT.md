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

## The goal: abstract appendVec

The medium-term research goal is getting `appendVec` working end-to-end with
**abstract** arguments (`n : Nat, m : Nat`). Och is useless without this — a
type system that can only verify concrete computations adds nothing over an
evaluator.

For this to work, the type system needs **dependent elimination**: when you
branch on an abstract `n : Nat`, the return type must track which branch was
taken. Church encoding alone can't do this (the return type collapses to a
fixed `X`). Self types solve this by letting the type mention the term being
typed, so the return type becomes `P n` — dependent on the input.

## Current approach: mu (unified self-reference)

We discovered that Och's two self-reference primitives (`fix` for recursion,
`iota` for self types) are the same thing viewed at different precision levels.
We are unifying them into a single primitive `mu`. Read
`docs/ideas/merge-fix-iota.md` for the full analysis — **this is the key
design document for the current work**.

The specific roadmap and next steps are in **SUGGESTIONS.md**. The current
state of the experiment is in **PROGRESS.md**.

## Context to read

Read these for context (in this order):
1. `docs/ideas/merge-fix-iota.md` — the mu design document
2. `SUGGESTIONS.md` — roadmap and next steps
3. `PROGRESS.md` — current state
4. `docs/what-is-och.md` — what Och is and why it exists
5. `docs/och-spec.md` — the Och specification (note: will need updating for mu)

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
- `Och/Syntax.lean` — term representation
- `Och/Eval.lean` — concrete and abstract evaluation
- `Och/Subtyping.lean` — the subtyping relation
- `Och/Soundness.lean` — WellTyped + VCompat + soundness theorem
- `Och/Tests.lean` — acceptance tests (DO NOT weaken)

Run `cd lean && lake build` to see the current state.

## What to do

**Do one impactful thing per session.** Read the state, pick the single most
valuable next step from SUGGESTIONS.md, do it well, commit it, and finish.
Do not try to solve everything — you are one agent in a long relay. A clean
commit with a clear handoff is worth more than an ambitious attempt that runs
out of context.

The most productive next step might be:
- Implementing the next item on the SUGGESTIONS.md roadmap
- Fixing a `lake build` error or filling in a `sorry`
- Realizing a definition needs to change and writing up why
- Updating the spec or design docs because something is wrong
- Rethinking the approach entirely and documenting your reasoning
- **Discovering that a theorem statement is vacuous or wrong** — this is as
  valuable as proving it. Document it clearly and commit.

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
  This mistake has already happened once (see SUGGESTIONS.md "CRITICAL"
  section). Do not repeat it.

## What success looks like

The ultimate goal is a provably sound type system for Ochre. The current
milestone is Och with ALL of these simultaneously:

1. `lake build` passing with no `sorry`
2. Soundness and monotonicity proven
3. All tests passing, including abstract appendVec
4. **The soundness theorem is non-vacuously true for the milestone programs**

Point 4 is critical. A sorry-free soundness theorem whose preconditions
can't be satisfied is vacuously true and proves nothing. The preconditions
(currently `WellTyped`) must be satisfiable for real programs — verified by
`native_decide` witness tests. Zero sorrys is not the goal; a meaningful
theorem is the goal. Sorrys are a means of tracking progress toward that.

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

- **Scope tightly.** Pick one thing. Do it. Commit. Hand off.
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
