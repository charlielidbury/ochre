# Och Agent Prompt

You are working on Och, a minimal research calculus. Your goal is to make `lake build`
pass in the `lean/` directory with no `sorry` remaining.

You were told your agent ID in the first message. Include it in all your commit
messages (as an `Agent-ID: <your-id>` trailer) so that decisions can be traced
back to you.

## Your memory will be wiped

When this session ends, you lose all context. The next agent starts fresh with only
the repo contents and git history. Therefore:

- **Commit messages are your voice to future agents.** Explain not just WHAT you
  changed but WHY. If you tried something that didn't work, say so in the message.
- **Update `lean/PROGRESS.md`** at the end of your session with what you did, what's
  next, and any blockers.
- **Update `lean/DECISION-LOG.md`** if you made a significant design decision
  (changed the Expr type, altered subtyping rules, chose a proof strategy, etc.).
- **If something is confusing or surprising, write it down.** Don't assume the next
  agent will figure it out. They won't have your context.
- Feel free to change the structure of PROGRESS.md or DECISION-LOG.md if you think
  a different format would be more useful for future agents.

## What you're building

Read these files for context (in this order):
1. `docs/what-is-ochre.md` — what the full language is
2. `docs/what-is-och.md` — what the minimal calculus is and why it exists
3. `docs/why-och-matters-for-ochre.md` — why your design choices matter
4. `docs/och-spec.md` — the specification and test suite

## The Lean project

The project is in `lean/`. It contains:
- `Och/Syntax.lean` — term representation (you can change this)
- `Och/Eval.lean` — concrete and abstract evaluation (you can change this)
- `Och/Subtyping.lean` — the subtyping relation (you can change this)
- `Och/Soundness.lean` — the soundness theorem (you must prove this)
- `Och/Monotonicity.lean` — the monotonicity theorem (you must prove this)
- `Och/Tests.lean` — acceptance tests (DO NOT weaken these)
- `PROGRESS.md` — current status and session log (update this)
- `DECISION-LOG.md` — significant design decisions (update this)

## What to do each iteration

1. Read `lean/PROGRESS.md` and the recent git log to understand where things stand.
2. Run `cd lean && lake build` to see the current state.
3. Read the error output carefully.
4. Identify the most productive next step. This might be:
   - Fixing a Lean compilation error
   - Filling in a `sorry` with an actual proof
   - Realizing a definition needs to change to make a proof go through
   - Uncommenting a test that the system is now ready for
5. Make the change.
6. Run `lake build` again to verify.
7. If it passes (or you've made clear progress), commit your work with a
   descriptive message explaining what you did and why. Include your agent ID.
8. Update PROGRESS.md and DECISION-LOG.md as appropriate.
9. Commit the documentation updates.
10. Repeat until you run out of turns.

## Critical constraints

- **Tests.lean pins expressiveness.** You can change Syntax, Eval, Subtyping
  freely, but the tests in Tests.lean must pass. If a test doesn't pass, fix
  the definitions, not the test. The only acceptable test changes are adapting
  to renamed constructors or adding more tests.

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

- **Monotonicity is historically the hard part.** The known counterexample
  (Ochre Proposition 5.2.9) showed that narrowing the environment can break
  subtyping. Your design must avoid this. If you find that monotonicity seems
  unprovable, that's important information — document why in a comment before
  changing the definitions.

## What success looks like

`lake build` passes with:
- No `sorry` in any file
- All uncommented tests passing
- Soundness and monotonicity proven

This is an extremely ambitious goal. You will likely not finish in one session.
That's fine. Make progress, commit it, and the next iteration will continue
where you left off.

## Installing Lean (if needed)

If `lake` is not found, run:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```
If that doesn't work, install elan:
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

## Working style

- Think before you code. If a proof isn't going through, step back and think
  about whether the definitions are right, not just whether you can force the
  proof.
- Read the git log to understand what previous iterations have done.
- If you change a fundamental definition (like the Expr type or the subtyping
  relation), explain WHY in your commit message.
- Small, correct steps are better than large, broken ones.
