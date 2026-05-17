# PSS discharge-campaign iteration brief

You are one iteration of an infinite loop working to drive the PSS Lean 4
formalization to **zero outstanding axioms in headline theorem closures**
(excluding the permanent paper-conjecture `Conjecture_8`).

`CLAUDE.md` (auto-loaded — already in your context) contains the
**autonomy rules and standing constraints**. Read them first if you
haven't. Especially the banned-phrases list and the narrow legitimate
stopping conditions.

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

### Step 2 — Pick the next concrete target (HARDEST FIRST)

**Hardest case first** is non-negotiable. When you have a choice between
attacking a hard problem and an easy one, attack the hard one. If the
hard one falls, the easy ones are usually mechanical fallout. If the
hard one resists, the easy ones are still there for next iteration —
but you've learned something. Easy-first looks productive but leaves the
load-bearing problems for someone else, indefinitely.

Specific anti-patterns this campaign has fallen into:
- Discharging `tAp × *` and `Top` cells in Lemma 2's case grid while
  leaving `Bet × Bet` and `App × Bet` as axioms. Wrong shape.
- "Restructuring" or "splitting" an axiom into two narrower axioms with
  no actual proof progress. Pareto-neutral at best, axiom-count-negative
  at worst.
- Picking the residual whose blocker analysis is freshest because the
  context is loaded, instead of the residual that matters most.

The active outstanding axioms, **ranked hardest-first**:

1. **The renaming functor on `MEqRed`** (~500-800 lines, multi-iteration).
   This is the universal unblocker. Once it exists, alpha-equivariance
   for `avoidsPro` becomes provable, which unblocks the β-residual cells
   below, which unblocks Lemma 2's `_core` term-size induction, which
   unblocks Lemma 1's parallel residuals. Five axioms collapse off the
   headline closures. **If you don't have a clear single-iteration win,
   start this.** Multi-iteration work is fine — commit incremental
   pieces with green builds, the next iteration picks up.

2. **`Lemma_2_DiamondMEqRed_ctx_axiom`** (Diamond.lean) and
   **`Lemma_1_ctx_axiom`** (Commutation.lean). Confluence-shaped; need
   mutual recursion with the diamond/commutativity itself (now possible
   since both are theorems). Multi-session.

3. **`Lemma_2_inline_bet_residual_axiom`** and
   **`Lemma_2_inline_app_bet_residual_axiom`** (Diamond.lean), and
   **`Lemma_1_inline_app_bet_residual`** (Commutation.lean). β-residual
   cells. Need term-size induction in `_core` with `avoidsPro` measure;
   need alpha-equivariance to thread the moreover clause; need (1) above.

4. **`Proposition_17_beta_axiom`** (OperationalSem.lean). LN encoding
   obstacle on `MEqRed.refl` interaction with `MEqRed.bet`'s body
   context — see `MEQRED-BET-AUDIT.md` (the rule itself is paper-
   faithful; the issue is downstream).

5. **`Lemma_10_Inversion`** (WellFormed.lean). Needs WfM preservation
   under MEqRed; partial helper exists.

6. **`Lemma_24_NarrowingMSubRed`** (Narrowing.lean). Cycle: needs
   WSubMStar weakening from TypeSafety which is downstream of Narrowing.

7. **`Lemma_30_msPro_x_axiom`** (Substitution.lean). Easiest of the
   active list — leaf already discharged as `Lemma_30_msPro_x` theorem;
   "just" needs threading through `TypeSafety._S_lf2`. **Avoid this as
   your only target unless you've also tried something harder.**

Read each candidate's docstring (in its file) and `AXIOMS.md` entry for
the precise blocker. Pick the highest-ranked one whose blocker you can
actually attack this iteration, then dispatch a sub-agent on it.

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
