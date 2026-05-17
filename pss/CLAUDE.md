# PSS — Lean 4 formalization of MPSS metatheory

You are working on a Lean 4 formalization of Pasquale & García-Pérez 2024
(arXiv 2407.13882, v2 Dec 2025) — the Machine-based PSS metatheory that
closes Hutchins' transitivity-elimination gap. See `README.md` for scope,
`PLAN.md` for module map and discharge campaign status, and `AXIOMS.md`
for the precise current axiom inventory with discharge plans.

## Operating principles

You have full ownership of this project. Quality > speed. There is no
time pressure. Throttling is in place — work as long as you need.

### Standing autonomy rules — read these every iteration

1. **Never stop on diminishing returns alone.** Low session-over-session
   yield is signal for *strategy change*, not stopping. If you've spent
   N sessions on the same residual without progress, dispatch a Plan
   agent to find a different angle, but do not pause.

2. **After every agent report, dispatch the next concrete agent within
   the same turn unless the user has interrupted.** Default to action.
   The `report → wait` pattern is the wrong default; the right default
   is `report → audit → dispatch next`.

3. **Legitimate stopping conditions are narrow:**
   - (a) A safety/correctness incident that genuinely needs human
         judgment (e.g. you discovered a false-axiom situation and need
         confirmation on the recovery strategy).
   - (b) The explicit user-stated goal has been achieved (in this
         project: zero outstanding axioms in headline theorem closures,
         excluding the permanent `Conjecture_8`).
   - (c) The user has interrupted you.

   None of these are "I think this is a natural pause point."

4. **Linguistic tells of bailing — banned phrases.** If you find yourself
   writing any of these, instead dispatch the next concrete agent for
   the work you were about to defer:
   - "future grinding"
   - "future work"
   - "natural pause point"
   - "consolidate now"
   - "good place to stop"
   - "out of scope this session"
   - "deferred to a follow-up"
   - "next session can…"

   The exception: a sub-agent's report can use these phrases. Your
   response to that report should NOT — it should dispatch the next
   agent that does the deferred work.

5. **If no clear next step is obvious, spend a turn on the `Plan`
   sub-agent type to find one.** Decision paralysis is itself a problem
   worth delegating.

5a. **Hardest case first.** When you have a choice of axioms / cases /
   targets to attack, pick the hardest one — not the one whose context
   is already loaded, not the one with the freshest blocker analysis,
   not the one a sub-agent's report happens to dangle in front of you.
   If the hard case falls, the easy ones are usually mechanical fallout.
   If it resists, you've learned something load-bearing for the next
   iteration. Easy-first feels productive but leaves the actual problem
   for later, indefinitely. Past anti-patterns to avoid:
   - Discharging `tAp × *` cells while leaving `Bet × Bet` axiomatic.
   - "Splitting" an axiom into two narrower axioms with no proof
     progress (Pareto-neutral or worse).
   - Picking the residual whose context is already loaded over the
     residual that matters most.

6. **You may NOT introduce axioms that are mathematically false.** Sub-
   agents have previously shipped axioms whose statements are
   counterexample-false (the proposed alpha-equivariance for arbitrary
   `hbody` is the canonical example). When dispatching agents that may
   add axioms, include this constraint:
   - "Before adding any new axiom, verify its statement is mathematically
     true — at minimum, check whether you can construct a counterexample.
     If the statement is only true under restricted shapes, the axiom
     must include those shape restrictions in its hypotheses."
   If you suspect a sub-agent shipped a false axiom, revert immediately
   and rewrite the constraint for the next attempt.

7. **Commit and push frequently.** Per the user's standing rule across
   all their projects, every commit ships with a push in the same turn.

## Workflow conventions

### Branch hygiene
- The active branch is `pss`. Long-running experiments go on dedicated
  branches (e.g. `type-lc-experiment`); the user expects you to merge
  back when done OR document why you didn't.
- A failed major refactor should be explicitly reverted via `git revert`
  (preferable to `git reset` for the audit trail).

### Sub-agent dispatch
- Read `PLAN.md` DISCHARGE CAMPAIGN STATUS section before dispatching.
  It lists the active blockers and recommended attack order.
- Each agent dispatch should specify:
  - The exact axiom or theorem being targeted.
  - The constraint set (no new axioms vs. permitted; no `sorry`; etc).
  - Files the agent may modify (default: scoped narrowly).
  - The blocker analysis from previous attempts so the agent doesn't
    re-discover the same wall.
- Parallel dispatch when files don't conflict (Diamond.lean and
  TypeSafety.lean can be touched concurrently; AvoidsPro.lean and
  Substitution.lean cannot).

### Build verification
After every commit (yours or a sub-agent's):
```sh
cd /home/charlielidbury/repos/ochre-pss/pss
nix develop --command lake build
nix develop --command lake build Pss.Sanity 2>&1 | grep -A 12 \
  "Theorem_3\|Theorem_4\|Theorem_5\|Lemma_1\|Lemma_2_DiamondMEqRed"
```
Compare the axiom dependency lists to the expected state in `AXIOMS.md`.
If a sub-agent's commit introduces NEW headline-axiom dependencies
without removing more than it added, audit the change carefully — that's
a regression.

### Documentation drift
- Every axiom should have a docstring covering: why it's an axiom, what's
  needed to discharge it, cross-reference to `AXIOMS.md`.
- After substantial changes, refresh `AXIOMS.md` to match `#print axioms`
  output. Stale documentation is a real cost — future agents follow the
  docs.

## The discharge campaign — current state

(See `PLAN.md` "DISCHARGE CAMPAIGN STATUS" for the authoritative version;
this is a snapshot.)

Lemma 1 and Lemma 2 are theorems with narrow per-cell residual axioms.
Active outstanding axioms blocking headline theorems (Theorems 3, 4, 5):

- **β-residual cells** (5 axioms): `Lemma_1_ctx_axiom`,
  `Lemma_1_inline_app_bet_residual`, `Lemma_2_DiamondMEqRed_ctx_axiom`,
  `Lemma_2_inline_app_bet_residual_axiom`,
  `Lemma_2_inline_bet_residual_axiom`. All converge on needing term-size
  induction with `avoidsPro` measure + alpha-equivariance.
- **Wf inversion family** (3 axioms): `Lemma_10_Inversion`,
  `Lemma_24_NarrowingMSubRed`, `Lemma_30_msPro_x_axiom`. Each has a
  specific structural blocker documented in its file's docstring.
- **LN encoding obstacle** (1 axiom): `Proposition_17_beta_axiom`.

Plus 1 permanent axiom (`Conjecture_8_WellSubtypingContextIndependent`,
paper-faithful, currently NOT in any headline closure).

Plus 1 inactive axiom (`Lemma_10_InversionRestricted`).

The next big architectural lever is the **renaming functor on MEqRed**
(~500-800 lines): a Type-valued recursive renaming that preserves
constructor structure, enabling honest discharge of alpha-equivariance.
This unblocks the β-residual layer.

## Loop runner

`loop.sh` is provided for autonomous iteration. The user invokes it
when they want sustained progress. It:
- Launches an interactive Claude Code session per iteration
- Names the session by timestamp
- Reads this CLAUDE.md and `PLAN.md` on each iteration

## Files you'll touch most

- `Pss/Mpss/Diamond.lean` — Lemma 2 case grid + residual axioms
- `Pss/Mpss/Commutation.lean` — Lemma 1 case grid + residual axioms
- `Pss/Mpss/AvoidsPro.lean` — `avoidsPro` Bool function and discharge
  helpers
- `Pss/Mpss/Substitution.lean` — substitution machinery, Lemma 30
- `Pss/Mpss/Renaming.lean` — body renaming infrastructure
- `Pss/Mpss/TypeSafety.lean` — Lemmas 6, 7, 11; Theorems 4, 5
- `Pss/Mpss/WellFormed.lean` — WfM, WSubM, WEquM judgments + Lemma 10

## Things that have been settled — do not re-litigate

- **Scope is KAM-only.** Hutchins' algorithmic system (`Pss/Algo/*`,
  `Pss/Decl/*`, `Pss/Bridge/*`) was deleted in commit history. Don't
  re-introduce.
- **`MEqRed.bet`'s body context is paper-faithful.** Past agents
  attempted to "fix" it as if it were wrong; see `MEQRED-BET-AUDIT.md`.
- **Term.LC is now Type-valued** (commit `ad3ff08`). The Prop-valued
  variant is permanently gone.
- **`MEqRedAvoidsPro` (Prop-indexed predicate) was unsound and was
  dropped.** The current `avoidsPro` is a Bool-valued recursive
  function. Do not re-introduce the predicate version.
- **Conjecture 8 stays.** The paper leaves it open; we mirror that.
