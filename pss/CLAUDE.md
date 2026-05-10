# PSS — Lean 4 formalization of MPSS metatheory

You are working on a Lean 4 formalization of Pasquale & García-Pérez 2024
(arXiv 2407.13882, v2 Dec 2025) — the Machine-based PSS metatheory that
closes Hutchins' transitivity-elimination gap. See `README.md` for scope,
`PLAN.md` for module map and discharge campaign status, and `AXIOMS.md`
for the precise current axiom inventory with discharge plans.

## Source of truth — the paper

**The paper IS the source of truth for every proof in this codebase.**

- **Local PDF:** `papers/pasquale-garcia-perez-2024-mpss.pdf` (46 pages,
  full proof appendix included).
- **Index:** `PAPER-PROOFS.md` maps every paper Theorem / Lemma /
  Proposition to its codebase counterpart with paper page citations.
  Read this first; consult the PDF for the full proof of any item the
  index links to.
- **Read the whole paper.** Every dispatch should read the entire PDF
  before working. ~60k tokens at ~1M context budget — the cost is
  negligible compared to the cost of inventing proofs that drift from
  the paper. Do not skim sections.

### Hard rules on proof construction

1. **NO AGENT MAY INVENT A PROOF that the paper provides.** If the paper
   has a proof for a lemma, theorem, or proposition, mechanize *that
   proof* — same case enumeration, same auxiliary lemmas, same
   structural argument. Do not search for a "Lean-friendlier" proof.
   Do not factor into payload/partial machinery the paper does not
   have.

2. **The only legitimate reasons to deviate from the paper's argument:**
   - (a) The paper genuinely omits the proof (handwaved, "similar to",
         "by routine induction"). The deviation must be flagged in the
         lemma's docstring with `-- Paper handwaves; mechanized as: ...`.
   - (b) A conscious mechanization choice we have made (currently:
         **de Bruijn indices** instead of named binders). Even then, the
         structural shape of the proof (case enumeration, induction
         principle, lemmas invoked) must match the paper. Only the
         binder representation differs.

3. **Codebase structure must mirror the paper's structure 1-to-1.**
   One file per paper section / paper lemma family. Lemma names match
   paper lemma numbers (e.g. `Lemma_19_Weakening`, `Theorem_1_StrongCommutes`).
   Docstrings cite paper page numbers. If you find an existing helper
   that doesn't correspond to anything in the paper, treat that as a
   defect — either remove it or document why it exists.

4. **Auxiliary lemmas must be named, not inlined per cell.** The paper's
   Theorem 1 closes its 8 cases by calling Lemmas 19, 32, 36, etc. by
   name. Our codebase must do the same. If your dispatch needs an
   auxiliary, find which paper lemma corresponds. If none does and the
   reason isn't (1a) or (1b), do not invent one — report back instead.

5. **Conjecture 8 stays explicit.** The paper acknowledges it as open;
   we mirror that. Theorem 5 / Lemma 7 are conditional on it. If a
   proof you write doesn't visibly rely on Conjecture 8 but the paper
   says it should, you've drifted — re-read the paper.

If a residual seems to need a novel proof technique, that's a flag.
Re-read the paper before grinding.

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

## NEXT MAJOR WORK — de Bruijn refactor (post-iter-32 decision)

**Lever A (open-target descent, the "renaming functor on MEqRed" approach)
walled at iter-32 with a Lean-checked counterexample at the `tAp` arm.**
See commit `5f2c58c` and `Pss/Mpss/Renaming.lean §15` for the
counterexample (`MEqRed.openInverse_descend_tAp_counterexample`). The
structural reason: every `MEqRed` constructor whose stack/operand carries
an `fv ⊆ Γ.dom` premise (`tAp`, `app`, `bet`, `fun_`, `fOp`) cannot
produce cofinite-z output when the body shape mentions `bvar 0` in such
positions, because `{z} ⊄ Γ.dom` for stray z. This forecloses the entire
LN-with-cofinite-quantifier discharge strategy at the encoding level.

The campaign's next major work is to **switch the formalization from
locally-nameless to de Bruijn indices**. Per the user's standing decision:

> "de Bruijn indices are a more organised approach which leads to cleaner
> codebases and will reduce our tech debt."

### Why de Bruijn dissolves the wall

The wall is the cofinite quantifier `∀ y ∉ L, MEqRed Γ s (body^[y])
(body'^[y])` on `MEqRed.bet`/`fun_`/`fOp`. The body sub-derivation is a
**function** over fresh names; two distinct witnesses can have proof
skeletons whose `avoidsPro` values disagree (no a priori uniformity). In
de Bruijn:

```
| bet : MEqRed (β :: Γ) s body body' →           -- ONE body derivation
        MEqRed Γ [] arg arg' →
        MEqRed Γ s (.app (.abs t body) arg) (instantiate 0 arg' body')
```

There are no fresh names to pick; the body sub-derivation is a single
proof tree; alpha-equivariance is vacuous; the 5 β-residuals close as
case-grid recursion over genuine structural sub-derivations.

### Scope estimate (calibrated)

Codebase: 27.5k Lean lines. Touched by the switch: ~25k (everything in
`Pss/Mpss/*` and `Pss/Syntax/*`; `Pss/Checker/*` ~700 lines is
orthogonal). Phasing:

| Phase | Scope | Dispatches |
|---|---|---|
| 1 | `Pss/Syntax/DeBruijn.lean` (new), rewrite `Reductions.lean`, shrink `AvoidsPro.lean` | 4–6 |
| 2 | `Substitution.lean` rewrite (lift/instantiate/strengthen lemmas) | 3–5 |
| 3 | `Prevalid`, `Weakening`, `ContextRed`, **delete most of `Renaming.lean`** (the 9.5k-line descend_* family becomes obsolete), replace with ~1k index-shift machinery | 4–7 |
| 4 | `WellFormed.lean`, `WfMPreservation.lean` | 3–4 |
| 5 | `Diamond`, `Commutation`, `Narrowing`, `TypeSafety`, `SubjectReduction`, `TransitivityElim` — **the 5 β-residuals discharge here** | 6–10 |
| 6 | Cleanup, axiom audit, doc refresh | 2–3 |
| **Realistic with risk multiplier** | | **35–60 dispatches** |

### Atomic switch — no incremental migration

Changing the `Term` inductive forces an atomic switch. Cannot half-port.
If a sub-agent walls partway, revert the whole work-branch and start
over rather than ship a Frankenstein. Recommend doing the work on a
fresh branch (e.g. `db-refactor`) so the `meqred-uniform-experiment`
LN state remains a fallback.

### Hard caveats

1. **Paper-faithfulness loss.** Theorem statements that mention binders
   no longer textually match Pasquale & García-Pérez 2024. For a
   paper-mechanization project, this is a real qualitative cost.
2. **Unknown new walls.** ~20% chance Prevalid-shaped invariants pose
   new problems in de Bruijn form. Phase 5e/5f's CAPSU population trap
   wasn't purely about alpha; some of it is Prevalid-shaped.
3. **WfM/WSubM still want names** in the paper's statements. Either
   keep names there and de-Bruijn only the reduction relations
   (hybrid encoding, its own complications) or push de Bruijn through
   the type system (loses readability).

### What an iteration on de Bruijn looks like

**Phase 1 first dispatch** should ship `Pss/Syntax/DeBruijn.lean` with
the new `Term` inductive plus the replacement `instantiate`/`shift`
operations and 4–6 algebraic lemmas. No `MEqRed` work yet — the syntax
core must compile and have its substitution machinery proved before
anything downstream switches over. See `AXIOMS.md` "Lever A
counterexample (iter-32)" section for what existing helpers are now
obsolete.

DO NOT attempt to keep both encodings live at once. The combinatorial
explosion of mixed-encoding work has been demonstrated in Phase 5g (~127
call-site migration) and is the pre-existing failure mode.

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
- **Lever A (open-target descent functor) is dead** as of iter-32.
  Lean-checked counterexample at the `tAp` arm in commit `5f2c58c`
  (`Pss/Mpss/Renaming.lean §15`,
  `MEqRed.openInverse_descend_tAp_counterexample`). The 3 honest arms
  closed (`top`, `var`, `pro`) and `Term.openInverse` infrastructure are
  retained in-tree as documented dead-end. Do not attempt the remaining
  5 arms. Do not attempt Lever B (alpha-equivariance renaming functor) —
  the iter-31 audit showed it has the same wall in disguise. The campaign
  has pivoted to the de Bruijn refactor; see "NEXT MAJOR WORK" above.
