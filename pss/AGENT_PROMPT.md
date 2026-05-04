# PSS discharge-campaign iteration brief

You are one iteration of an infinite loop working to drive the PSS Lean 4
formalization to **zero outstanding axioms in headline theorem closures**
(excluding the permanent paper-conjecture `Conjecture_8`).

`CLAUDE.md` (auto-loaded — already in your context) contains the
**autonomy rules and standing constraints**. Read them first if you
haven't. Especially the banned-phrases list and the narrow legitimate
stopping conditions.

## Campaign state — iter-32 pivot to de Bruijn

The locally-nameless discharge campaign **walled at iter-32** with a
Lean-checked counterexample to Lever A (commit `5f2c58c`,
`Pss/Mpss/Renaming.lean §15`,
`MEqRed.openInverse_descend_tAp_counterexample`). The 5 β-residual
axioms cannot be closed in the current encoding. Per the user's
authoritative direction, the campaign now executes a **de Bruijn
refactor**.

If you're a fresh iteration on or after 2026-05-04 (post commit
`5f2c58c`), your job is to **execute one phase of the de Bruijn
refactor**, NOT to attempt the 5 β-residual axioms in the LN encoding.

See `CLAUDE.md` "NEXT MAJOR WORK — de Bruijn refactor" for the phase
plan and `PLAN.md` "Decision (iter-32 — sealed)" for the historical
record of why the LN approach walled.

**Banned this iteration onward:**
- Do NOT attempt `Lemma_2_inline_app_bet_residual_axiom`,
  `Lemma_2_inline_bet_residual_axiom`,
  `Lemma_2_DiamondMEqRed_ctx_axiom`,
  `Lemma_1_inline_app_bet_residual`, or `Lemma_1_ctx_axiom` in the LN
  encoding. They are walled.
- Do NOT extend `MEqRed.openInverse_descend` (Lever A is dead).
- Do NOT attempt a "Lever B" alpha-equivariance renaming functor — same
  wall in disguise per iter-31 audit.
- Do NOT mix de Bruijn with locally-nameless (atomic switch — see
  CLAUDE.md). If the de Bruijn refactor is in flight on a feature
  branch, work on that branch; if not, start it.

## What to do, this iteration

### Step 1 — Read the current state

```sh
cat AXIOMS.md                            # authoritative axiom inventory
sed -n '1,130p' PLAN.md                  # discharge-campaign status
git log --oneline -20                    # recent agent activity
nix develop --command lake build         # confirm green baseline
nix develop --command lake build Pss.Sanity 2>&1 | \
    grep -A 12 "Theorem_3\|Theorem_4\|Theorem_5\|Lemma_1\|Lemma_2_DiamondMEqRed"
```

The build MUST be green at the start of your iteration. If it isn't,
your first job is to find and revert the breaking commit. Do not start
new work on a broken baseline.

### Step 2 — Pick the next concrete de Bruijn refactor task

**The discharge campaign is now executing the de Bruijn refactor.** The
phase plan lives in `CLAUDE.md` "NEXT MAJOR WORK — de Bruijn refactor".
Pick the lowest-numbered phase that hasn't been started; if a phase is
in flight on a feature branch, advance it.

The phases (recap):

1. **Phase 1 — DeBruijn.lean syntax core.** New `Term` inductive
   (`bvar (Nat)`, `top`, `app`, `abs`) + `instantiate`/`shift` ops + 4–6
   algebraic lemmas. ~600 lines. Must build green before Phase 2 starts.
2. **Phase 2 — substitution machinery.** `Substitution.lean` rewrite.
3. **Phase 3 — context + reductions.** Rewrite `Reductions.lean`;
   delete most of `Renaming.lean`'s descend_* family (~9k lines obsolete).
4. **Phase 4 — well-formed judgments.** `WfM`, `WSubM`, `WSubMStar`,
   `WEquM` re-stated in indices.
5. **Phase 5 — headline theorems.** Re-prove Lemmas 1, 2; Theorems 3, 4, 5.
   **The 5 β-residual axioms discharge here.**
6. **Phase 6 — cleanup + axiom audit.**

**Hardest case first within a phase.** Within Phase 5, the case grid
order (App×Bet, Bet×Bet, Bet×App, App×App) is the hardest-first natural
order — these are the cells walled in LN. Don't ship Phase 5 trivial
cases ahead of these.

**Branch hygiene.** The de Bruijn work goes on a fresh `db-refactor`
branch (or whatever you named it). The current `meqred-uniform-experiment`
state preserves the LN attempt as fallback. Do NOT attempt to merge
work-in-progress de Bruijn into `meqred-uniform-experiment` — atomic
switch only when Phase 6 is done.

If you're picking up Phase 1 from scratch:
1. `git checkout -b db-refactor`
2. Create `Pss/Syntax/DeBruijn.lean` with the new inductive.
3. DO NOT delete `Pss/Syntax/LocallyNameless.lean` yet. It will be
   removed in Phase 3 once nothing references it.
4. The new `Term` should have a clean `instantiate k v t` (replace
   bvar k with v, lift other bvars accordingly) and `shift k t` (lift
   bvars ≥ k). Ship 4–6 lemmas: `instantiate_shift_id`,
   `shift_zero_id` (or whatever shape compiles), `shift_compose`,
   `instantiate_distributes_over_app`, etc.
5. Build green. Commit. Push.

### Step 3 — Dispatch a sub-agent

Use the `Agent` tool. The brief should:
- State the EXACT axiom or theorem being targeted.
- List the EXACT files the agent may modify (default: scoped narrowly).
- Include the blocker analysis from previous attempts (read recent git
  log + the axiom's docstring).
- Forbid new axioms unless the agent has verified the statement is
  mathematically true (counterexample check required).
- Forbid `sorry`.
- Require the agent to commit on success and push.

Parallel dispatches when files don't conflict (Diamond.lean and
TypeSafety.lean can run concurrently; AvoidsPro.lean and
Substitution.lean cannot).

### Step 4 — Audit and continue

When the sub-agent reports back:
- Run `nix develop --command lake build Pss.Sanity` and compare axiom
  dependency lists against the previous state.
- If a sub-agent introduced new axioms, audit each one for
  counterexample-falseness. Revert if you find one.
- If the sub-agent claimed progress that doesn't show up in the audit,
  push back via `SendMessage` rather than accepting the report at face
  value.
- **Then dispatch the next sub-agent.** Do NOT stop, summarize, or
  "consolidate." The legitimate stopping conditions in CLAUDE.md are
  narrow.

### Step 5 — When the iteration's max-turns budget is approaching

The loop runner will give you a turn budget (default 50). When you've
used most of it:
- Make sure the build is green and any in-flight commits are pushed.
- Update `AXIOMS.md` to reflect any axiom-count changes.
- That's it. Do NOT write a "campaign summary" or "next steps" message —
  the next iteration has its own context.

## Critical safety rule

**Before adding any new axiom (in your own work or a sub-agent's), verify
its statement is mathematically true.** Try to construct a counterexample.
If the statement is only true under restricted shapes (e.g.
"alpha-equivariance for arbitrary `hbody`" is FALSE because of
non-uniform witnesses; only true for uniformly-structured ones), the
axiom must include those shape restrictions in its hypotheses or it must
not exist.

Counterexample-false axioms are a soundness emergency. Revert
immediately. The previous near-miss was commit `4145292` shipping
`avoidsPro_alpha_equiv` as a general statement when only the restricted
form was actually true.

## What success looks like

Each iteration should ship at least one of:
- An axiom discharged (axiom → theorem) and merged.
- A genuine new infrastructure piece that unblocks a future discharge,
  with the unblock path documented.
- A sub-agent's failed attempt with a sharper blocker analysis than was
  previously available, committed in a docstring or analysis file.

A loop iteration that ships nothing is a sign that either (a) the
sub-agents are spinning, (b) you're hitting an architectural wall that
needs a strategic pivot, or (c) you're bailing. Apply the autonomy rules
in CLAUDE.md to figure out which.
