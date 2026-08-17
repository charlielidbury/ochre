# Soundness: the statement of the task

This document states what it would mean for DLLBC to be *proven sound*, and what counts as
winning. It is deliberately not a proof plan — where it speculates about how the proof might
go, the speculation is marked as such. Its job is to fix the claims precisely enough that a
future theorem can be checked *against this document*, because the project's own history says
the failure mode is not "the proof is too hard" but "the statement quietly proves something
else." The standard is the one the mechanization set: a statement dispatched blind that the
work type-checks against exactly.

## 0. Why now, and why this shape

Two facts motivate the attempt and shape it.

First, the empirical soundness discipline has done its job and shown its limits in the same
month. The differential harness and the negative-control regime caught three genuine
unsoundnesses (the unguarded self-call, premise (3) refining a universal, and — with reversed
polarity — the concrete machine's own segment normalization) and localized each within a day.
That is evidence the *method* works. It is not evidence the *system* is sound: every one of
those bugs was found because a program happened to reach it, and the original Ochre
specification died of exactly the bug no program had happened to reach. The harness samples;
a theorem quantifies.

Second, the system is now worth proving things about. Two verified quicksorts — List and
Array, model-free, in place, `Sorted ∧ Perm` — check in milliseconds, execute correctly, and
agree with each other. The claims below are the claims those artifacts already make
informally. The task is to make them theorems.

## 1. The artifact the claims are about

The claims are about the **shipped Lean mechanization** — the functions the test suite
actually calls: `checkFn` and the interpreter it drives (`Machine.lean`, `Pure.lean`,
`Boundary.lean`), at a stated pin. Not an idealized twin calculus. This is a hard
requirement, stated as a winning condition below, because an idealized model would reintroduce
precisely the gap this project exists to close: the original Ochre spec was an idealization
whose unsoundness the implementation could not localize. If proof engineering demands an
intermediate model (it likely will — see §7), the model must be connected to the shipped code
by *machine-checked* equivalence, not prose.

One structural fact makes this tractable and should be named up front: **checking and
executing are one interpreter in two modes.** Most of the code is literally shared; the modes
diverge at an enumerable set of gates (symbolic generalization and refinement, group release
versus lazy ending, the carve's executing-gated normalization, `generalizeStuck`, opacity's
re-mint at calls). The proof obligation concentrates exactly at those gates. Everywhere the
code is shared, the simulation is definitional.

## 2. The claims, layered

Terminology: a **well-formed instantiation** of a declaration's telescope is an assignment of
closed concrete values to its parameters such that each value inhabits its (dependently
instantiated) parameter type. Note that telescopes carry *proof* parameters (`hfuel : Le n
fuel`, bounds, cited equations); an instantiation exists only when those hypotheses are true,
which is how preconditions scope every claim below. **Exhaustiveness of the explored paths is
a precondition throughout** — the checker's path-sensitive exploration must cover the branch
the concrete run takes; this has been the standing simulation precondition since the
differential was built, and the theorem inherits it as a proved lemma rather than an
assumption (the checker rejects non-exhaustive matches; that rejection is part of what S1
relies on).

**S1 — Progress (machine-faithfulness).** If `checkFn` accepts a declaration, then for every
well-formed instantiation and every sufficient fuel, the executing machine runs the body to
completion: it does not get stuck, and in particular never reads a hole, moves a moved value,
navigates a dead borrow, or fails a place operation. This is the property the differential
harness tests by sampling and the property whose violation has now been observed from *both*
sides (an accepted caller the machine rejected — C8; a machine that walled on a program the
checker rightly accepted — G5). S1 is the claim that both failure modes are gone for good.

**S2 — Correspondence (the simulation).** Under the same hypotheses, the final concrete state
is an *instance* of the symbolic exit state: there is an assignment of closed values to the
σs of the accepted path's final Ω such that the concrete final Ω is that instantiation, up to
the stated normalizations (the array fold; run/segment matching as `matchVal` implements it).
S2 is what makes the checker's exit snapshots *mean* something: `σ_exit` denotes the value
the machine actually ends with.

**S3 — Postcondition truth (the theorem-prover claim).** Under the same hypotheses, the
postcondition holds of the actual final state, in the following concrete sense: the return
type's computable content, evaluated at the concrete exit (and entry, for `old`), computes to
truth. For the flagship: run `quicksortA` on any concrete array with sufficient fuel — S3
says the resulting array *is* sorted (evaluating `SortedA` yields an inhabitant) and *is* a
permutation (every `countA` equation evaluates to a true numeral identity). S3 is deliberately
scoped to the **computable observation fragment** — the predicates postconditions are actually
written in (`Id` on numerals, `Le`, `count`/`Sorted`-style large eliminations), all of which
evaluate on closed values. This scoping matters: S3 so stated needs conversion-soundness on
closed values, *not* full canonicity or logical consistency.

**S4 — Deferred, and named so nobody mistakes the claim.** The following are explicitly *not*
part of winning, in order: logical consistency of the comptime fragment (no closed proof of
`⊥` — the project's standing position is consistency-deferred, "verified modulo Girard";
universes are future work); full adequacy for non-computable propositions and open terms;
termination or complexity of *checking* itself; and soundness of the legacy conformance
architecture (declared `back`s, the M22 baseline — it remains on main as a tested baseline,
but the theorem's scope is the direct architecture, which is the mission). A future S4 attempt
is welcome; conflating it with S1–S3 is not.

## 3. Winning conditions

The task is won when the following exist, and not before:

1. **Mechanized theorems for S1, S2, S3** in Lean 4, `sorry`-free, whose statements quantify
   over the shipped `checkFn` and executing interpreter (or over a model connected to them by
   a `sorry`-free equivalence theorem — prose equivalence does not count, and the delayed-lift
   `substPure` argument, currently stated only in a commit message, becomes an obligation of
   exactly this kind).
2. **The headline corollaries, instantiated.** From the general theorems, as corollaries with
   no additional axioms: the List quicksort and the Array quicksort each satisfy S1+S2+S3 —
   "for every concrete input and sufficient fuel, execution terminates in a sorted permutation
   of the input." These two corollaries are the falsifiable public face of the result; if the
   general theorems cannot produce them, the general theorems are about the wrong thing.
3. **The trust base, enumerated and minimal.** The theorems' trust base is the Lean kernel and
   the statement-level definitions only. In particular `native_decide` — which the test suite
   may keep using for speed — must not appear in the soundness theorems' dependency cone
   (`lean_verify`-style axiom audit is the check). The statement-level definitions (what
   "instance", "evaluates to truth", "well-formed instantiation" mean) are part of the trust
   base and must be small enough to review by eye; bloat there is where a wrong theorem hides.
4. **The assumed-obligation ledger discharged.** The mechanization has accumulated explicitly
   *assumed* obligations that the differential's own correctness now rests on. Winning requires
   each to become a lemma or be refuted: merge is value-preserving (¶8.2 obligation 4 — R9
   records that if this fails the harness goes silently green, so it is a premise of the
   evidence, not just of the system); the §6.1 lazy-versus-atomic reconciliation (the
   simulation relation must choose its hypothesis — fully-collapsed-at-observation or
   loan-as-instance — and prove it, knowing one member of that family already needed the
   *machine* fixed); exhaustiveness-as-precondition (becomes a lemma about rejection);
   copy-on-read's index-kind rule preserving values; and the §9-filed discarded-`let` laxity,
   which must either be closed in the checker or explicitly carved out of S1's statement (an
   accepted body may contain an unchecked dead binding; the claim must say which).
5. **Statement review against this document.** Each theorem's statement is checked, by a
   reviewer who did not write the proof, against §2's prose — the drift between "what we
   proved" and "what we claim" is the failure mode this document exists to prevent. The
   negative-control suite is *retained unchanged* alongside the theorems: a theorem with a
   subtly wrong statement plus deleted controls is strictly worse than controls alone.

**Staging — each stage a win on its own.** The claims decompose, and partial credit is real:

- **α**: S1+S2 for the call-free fragment (straight-line bodies, match with refinement and
  branch equations, borrows/loans/reborrows, take-and-refill) over the List basis.
- **β**: conversion soundness on closed values for the comptime fragment (whnf/convert agree
  with evaluation) — the engine of S3, and independently valuable.
- **γ**: calls — ensures-instantiation, exit-snapshot pinning, opacity's re-mint, and the
  recursion guard justified as well-founded induction (self-ensures admitted exactly where the
  snapshot-subterm order decreases). γ closes S1–S3 for the List flagship. This is the
  metatheoretically sharp stage; if the system has another C8-class surprise, it is here.
- **δ**: arrays — the carve, cited-equation refinement, segment normalization, and the
  simulation relation's array cases. δ closes the Array flagship and discharges the hardest
  ledger items. It is deliberately last: it exercises the relation where the polarity finding
  proved intuition unreliable in both directions.

## 4. Losing conditions, stated as wins of a different kind

The attempt can end three ways, and two of them are victories. A completed proof is the
obvious win. A **refuted claim** — a counterexample found because proving forced a case no
program had reached — is the other win, and the project's history says it is likely: this is
the outcome the attempt exists to force early rather than late, and the standing discipline
(fix toward whichever side is *right*, which the polarity finding proved is an open question
per-instance) already governs it. The only losing outcome is the quiet one: a proof about an
idealized system that drifts from the shipped one, maintained at growing cost, cited with
shrinking honesty. Winning condition 1 exists to make that outcome impossible to reach
without noticing.

## 5. Known hazards (so the estimate is honest)

Named here so nobody rediscovers them mid-proof: the simulation relation's array case is
*defined* through a normalization it must also prove value-preserving (circularity to be
broken by proving the normalization first); fuel appears in both machines and in the guard,
and the three roles must not be conflated (interpreter fuel is a totality device and the
statements are "for all sufficient fuel"; guard fuel is program data); `Err = String` means
"stuck" must be characterized as a *class* of results, not string-matched; the checker's
path-sensitivity means S2's "the accepted path" needs the path-selection function made
explicit; and the two modes share mutable interpreter plumbing whose refactors the proof will
freeze — landing the proof raises the cost of every future machine change, which is a real
price and should be paid knowingly, after the feature set it locks (post-array-era) is judged
stable enough.

## 6. Speculation (marked as such, welcome to be wrong)

The proof shape that fits the machine's actual structure: induction on interpreter fuel,
with a step lemma per mode-divergence gate and definitional simulation everywhere the code is
shared. The relation is `matchVal` generalized — it already *is* the informal relation, and
promoting it to the proof's relation keeps the differential and the theorem testing the same
thing. The nearest mechanized relative is in-repo: the `aeneas/` Rocq development proves an
LLBC-family symbolic-concrete soundness with tree-path machinery (`PathToSubtree`'s
disjointness trichotomy); its statement shapes transfer, its value model (no comptime
fragment, no dependent telescopes, no arrays) does not — the genuinely new metatheory here is
the *interaction* term: refinement (⇜) touching σ-bearing state that the concrete machine
represents as values, which is exactly where the swept-state principle (§9) already lives as
an invariant. β is a good first dispatch because it is self-contained, S3 rests on it, and
its statement is the easiest to get right. Estimating effort would repeat a mistake this
project has now made three times; the staging exists so that no estimate is ever load-bearing.
