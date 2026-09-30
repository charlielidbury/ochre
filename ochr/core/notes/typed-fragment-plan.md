# A proved theorem for a small typed fragment: viability assessment

Assessment only, 2026-09-30 (agent meta-order, for team-lead).

**Updates, same day, after two probes in the checker:**
- **R3 is confirmed and harmless.** `lean/Scratch/FootprintProbe.lean`: a footprint formed before a refinement has extra places, whose equations become `⊤` once the refinement is applied.
- **Part 1 of Theorem A is false for the current rules.** `lean/Scratch/DropProbe.lean`: `Bad2(n, b, x : &Nat) := let a = 0; x := Pick(n, &a, &b); let z = b; ()` is accepted, but `Bad2(0, 5, &y)` fails with a [Drop] error. The symbolic path ends `x`'s borrow early, and that lets `a` be dropped. The paper proof (`typed-fragment-proof.typ`) therefore restricts F: a borrow is never assigned into an existing variable. Whether to fix the rules instead is team-lead's call.

The original text follows. Written against `ochr-core` at cf55b4ef. The Lean facts below were checked against `ochr/core/meta-lean`, not taken from `notes/lean-meta.md`, which is stale in places (it still lists Lemma 0 as `sorry`, and it names a `Sched.lean` that exists only on the unmerged branch `ochr-core-meta-t1b`).

Asked by reviewers 6, 7 and 8. Reviewer 8's fragment is Nat, Unit, True/False/And, Eq, Id, first-order top-level functions with borrow parameters (one returning a borrow), [Close], and [Split] with refinement. It leaves out closures, stuck blocks, universes above Type₀ and large elimination, and says "a paper proof in the appendix is enough". Reviewer 7 asks for less: mechanise "an `Id` computed on abstract inputs holds on every concrete input" for the untyped first-order fragment. Reviewer 6 asks for consistency through the set model, for a fragment with closing off, `Id` and `Prop` erasure.

## 1. The smallest theorem that answers the reviewers

The three candidates are not independent. In reviewer 8's fragment they collapse into one theorem:

- **Consistency via a set model degenerates.** Without universes, type families, Prop-valued functions or function values, the only sets involved are ℕ and {()}. A proposition at a ground instance evaluates to a conjunction of `True`/`False`, because `Id` computes to `And` of `Eq`s, and `Eq` on ground values computes to `True` or `False`. So "the model" is just truth of closed Boolean formulas. All the content of consistency is in one question: is a lemma checked at its generic call true at every ground instance?
- **That question is soundness of `Id` at the generic call** (the second candidate), extended from `refl` to the proof forms of the fragment.
- **Naturality (the first candidate) is the lemma that soundness rests on, but not the theorem the reviewers asked for.** On its own it is a fact about the untyped machine. It would satisfy reviewer 7 but not reviewers 6 or 8, both of whom say "the typed system has no theorem at all".

So the smallest theorem that genuinely answers them is **Theorem A below, with consistency of the fragment as its corollary**. Naturality is Lemma N, inside its proof.

### The fragment F

- **Types:** `Nat`, `Unit`, `&Nat`; the propositions `True`, `False`, `And(P, Q)`, `Eq Nat a b`, `Eq Unit a b`, and `Id A t u` with `A ∈ {Nat, Unit}`.
- **Definitions:** top-level `def f (x̄ : Ā) : B by xⱼ := b`, each checked by [Def] at its generic call and by [Rec]. Parameters are `Nat`, `Unit`, `&Nat` or propositions (hypotheses). `B` is `Nat`, `Unit`, `&Nat` (with at least one `&Nat` parameter, D44) or a proposition. Data functions and lemmas may be recursive.
- **Terms:**
  - the first-order terms of `meta-lean`: read, borrow, assign, let, sequence, `Z`, `S`, `()`, a `Nat` match, calls;
  - the proof forms `refl`, `⟨h, k⟩`, a match on a proof of `And`, `match h {}` on a proof of `False`, lemma calls and proof parameters.
- **Checking:** [Split] on an abstract value, and on a sealed program by generalising it (D34/D37). A non-tail match on a neutral is rejected (there are no stuck blocks).
- **Left out:** closures, stuck blocks, universes, pairs, type families, Prop-valued functions, `J`/`rewrite`, and abstract function parameters. That last exclusion also rules out reviewer 6's A1, which needs both an abstract function and a type family.
- **Moves:** open decision. Either F uses copy reads of `Nat` (D53 off, what `meta-lean` does), or it includes D53's ghosts. Section 2 gives the cost of each.

### Statements

A *ground instance* of `def f (x̄ : Ā) : B` is a tuple of arguments: a numeral for `Nat`, `()` for `Unit`, a borrow of a fresh cell holding a numeral for `&Nat`, and `⋆` for a proof parameter. Its hypotheses *hold* if every proof parameter's type, computed by [Call-type] at those arguments, terminates and is true. A ground proposition value is *true* when it is `True`, or `And(P, Q)` with `P` and `Q` true. `Eq` and `Id` need no clause of their own, because at ground they have already computed to `True`, `False` or `And`.

- **Theorem A (accepted lemmas are true at every ground instance).** Let P be a program of F in which every definition is accepted by [Def] and [Rec]. Then:
  1. for every data function `f` of P and every ground instance, the call runs to completion without error;
  2. for every lemma `def L (x̄ : Ā) : B` of P and every ground instance whose hypotheses hold, the type `B` at that instance, computed by [Call-type], terminates and is true.
- **Corollary B (consistency of F).** No closed term of F has type `False`. Hence none has type `Eq Nat Z (S Z)`, or any `Id` whose ground runs disagree.
- **Corollary C (adequacy of `Id`, reviewer 7's form).** If `def L (x̄) : Id A t u := b` is accepted, then at every ground instance the runs of `t` and `u` from the ground call's environment, each followed by ending every borrow, give the same result and the same final contents of every place either of them writes.
- **Stability for F (Conjecture 3 restricted to F).** Most of its items are vacuous in F or are syntactic:
  - captures, stuck blocks and closure classes do not arise;
  - the erasure class and the [Close] row are read from the declared codomain;
  - "which matches are decided by the type of a proof" follows from Lemma N.

  One item is not vacuous and, as stated in the paper, looks false: the footprint. See risk R3 in §3.

Part 1 of Theorem A is there because the two parts need each other. A lemma's type mentions data calls, which get closed off symbolically and run concretely at ground. Those ground runs are safe only because the called functions were themselves accepted. So the proof is one simultaneous induction: on the order in which definitions call each other, then on the [Rec] measure of the ground arguments, then on the derivation.

### The lemmas inside the proof

- **Lemma N: naturality up to resolution; the core, and untyped.** Take a state Ω with abstract values, a term t and a ground refinement α. Assume every function of P is safe at ground inputs, which is the induction hypothesis from part 1. Suppose the symbolic run gives `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩`. Then the concrete run `⟨Ωα, tα⟩` gives some `⟨Ω'', v''⟩`, and after ending every borrow, the refined-and-normalised symbolic final state equals the concrete one up to renaming of loans; the results match the same way. The version without "after ending every borrow" is false: see `Tests/Basic.lean` namespace `T5`, and F3/F5 in `lean-meta.md`.
- **Lemma T: termination.** A concrete run of a program accepted by [Rec] terminates. This is `termination` in `GuardTerm.lean`, the `sorry` of property 3.
- **Lemma W: footprints.** Symbolic owners contain the ground owners, and the `Id` conjuncts for the extra owners are true at ground (see R3).
- **Lemma G: generalisation.** For F, where a sealed program's type is its declared codomain and never depends on a refinement, a global record `⌈n⌉ := σ` is sound: under any ground valuation, a sealed program's value is determined by its text.

## 2. What is proved, what is missing, and the cost

### Already in `meta-lean`, with no `sorry`

The development is 11.1k lines, plus 0.4k of property 7 added today.

| Piece | Where | Used for |
|---|---|---|
| frame: `frame_local`, `call_effect` | `Frame*.lean` (~1.5k) | N: a concrete call is its isolated run plugged back |
| `close_res/fin/cur/back` | `Close.lean` (~1.6k) | N: a sealed program normalises to what the call computes. Their hypotheses (loan-free arguments, name-free results) are stated in Lean but not yet discharged from `exec_wf` (~300 lines) |
| `exec_wf` (Lemma 0) | `WF*.lean` (~2k) | the invariants every step of N needs |
| `exec_rename`, `exec_mono`, `eval_det` | `Rename.lean`, `Mono.lean` | N: the renaming of loans; fuel |
| `end_order_indep`, `endAll_endSeq` | `EndOrder.lean` | N: resolution does not depend on which borrows were ended first. This is the pure-[End] half of T1(b) |
| `gexec` (the [Rec] checker, a symbolic run with [Split]) and `sim_gexec` | `Guard.lean`, `GuardSim*.lean` (~2.4k) | a working template: a simulation of a symbolic run with [Split] by the concrete run. But it is borrow-free only, and its value relation `VR` treats sealed programs as "anything" |
| `termination_bf`, `termination_nonrec` | `GuardLemma1.lean`, `GuardTerm.lean` | T for the borrow-free and non-recursive cases |
| `back_inj`, `ctx_inj` | `Inj.lean` | not needed for Theorem A in F. They matter for [Call-type] on borrow-returning *parameters*, which F leaves out |

### Missing

The estimates count Lean lines and agent-days. The anchor is the existing development: ~11k lines, written by parallel agents over about 1.5 days. The first two rows are the ones that stalled before, so they have the widest ranges.

| # | Missing piece | Lines | Agent-days | Note |
|---|---|---|---|---|
| M4 | **Lemma N.** A value relation in which a sealed program stands for its normal form under α (from `close_*`), a loan-name correspondence, and the two-sided F5 invariant "both states reach a common state by [End]s". One case per machine rule. The hard cases are [Access] on a loan inside a neutral head (after α the neutral may become a value, and the loan is then ended only by a deep access), and [Close] against the concrete call | 3–5k | 6–12 | **The crux.** The general termination proof stalled here: `GuardTerm.lean`'s docstring lists exactly these ingredients as what is missing |
| M5 | **Lemma T in general** (the `sorry`) | 0.5–1k | 2–3 after M4 | Reuses M4's relation, per the same docstring |
| M1 | **Machine up to the current rules for F.** [Close] without the `Unit` row (D59). [Seal] normalisation: `meta-lean` normalises when the final states are compared, while the rules re-normalise at every refinement and [End]; either prove the two agree or restate the rules | 0.5–1k | 1–2 | |
| M1′ | **D53 moves** (ghosts; an [End] must find its content whole) | +1.5–3k of changes to `WF`/`Frame`/`Close` | +3–5 | Optional: the fragment can say "copy reads" |
| M2 | **Observation in `meta-lean`:** owners, footprint, `observe`, `Id`/`Eq` computing | ~0.3k | 0.5 | Owners already exist in `Interp.lean` |
| M3 | **The typing judgement for F** as a checker function in the style of `gexec`: [Def], [Split] with generalisation records, [Call-type], the proof forms, the Eq/Id rules | 0.8–1.2k | 2–3 | |
| M6 | **Theorem A and Corollaries B and C:** the simultaneous induction, Lemma W, Lemma G | 1–1.5k | 3–5 | |

**Total to mechanise Theorem A:** about 7–11k lines, or 16–30 agent-days. With parallel agents that is 2–4 weeks of calendar time, high variance, and M4 is on the critical path. Without M4 nothing else can be proved. With M4, M5 and M6 are routine.

## 3. Is a paper proof a credible intermediate?

Yes, if it is structured so that the steps most likely to be wrong are the mechanised ones. The appendix proof would be about 4–6 pages:

- the definition of F;
- Theorem A, by the simultaneous induction of §1, one case per typing rule of F;
- Lemma N cited from Lean, if M4 is done; otherwise proved on paper;
- Lemma T cited;
- Lemmas W and G proved on paper, about half a page each;
- the corollaries.

The cases of Theorem A that read the rules backwards are routine: `refl`, `⟨h, k⟩`, a match on `And` or `False`, a lemma call, and `Eq` computing. So is stability for F, apart from footprints.

Most at risk of being wrong, in order:

- **R1. Lemma N at [Access].** The symbolic machine ends more borrows than the concrete one:
  - F3: a returned borrow's hole sits in the fill of every place it might point into;
  - loans inside a neutral head are ended as if they were at the head;
  - F5: ending early changes what a later assignment ends.

  "Equal after resolution" is not preserved one step at a time. The proof needs the two-sided invariant "each state reaches a common state by [End]s", and a paper argument is likely to miss a case, as every earlier enumeration did. This is the step to mechanise first.
- **R2. [Seal] normalisation against the concrete run.** A sealed program runs from the empty environment with *inert* loans, which behave like abstract values. In the concrete run the same loans are live, and [Access] would end them. The frame lemma plus `close_*` cover a single call. What is not covered is re-normalisation after an [End] substitutes into a fill, and a normalisation that errors (which the rules make a type error).
- **R3. Footprints: stability item (2) looks false as stated.**
  - Owners are computed before resolution. Symbolically, a returned borrow's owners are every place it might point into; `Pick`'s hole is in the fills of both `a` and `b`, so its owners are `{a, b}`. In the refined state, the fill of `b` normalises to a value without the hole, so the owners are `{a}`. The footprints of an `Id` in a lemma's type, formed at a call such as `L2(r)` with `r = Pick(n, &a, &b)`, are therefore not "the same" on the two paths.
  - It appears harmless. By the frame property, a place outside the ground footprint is written by neither `t` nor `u`, so the symbolic path's extra conjunct `Eq b_t b_u` is true at ground.
  - But the conjecture's wording must change to "the symbolic footprint contains the ground one, and the extra conjuncts hold", and the proof needs Lemma W.
  - The fuzzer's residual R1 shape ("an owner reached through a returned borrow", `notes/fuzzer.md`) sits in the same place.
  - Not checked in the checker yet. That takes a ten-minute probe: print the type of `L2(r)` at the generic call and at `n = 0`.
- **R4. Generalisation records are global (D37) and keyed by text.** This is where reviewer 6's A1 lived. In F it is sound only because a sealed program's type never depends on a refinement, and the paper proof must say so explicitly (Lemma G). Adding type families to F would reopen A1.
- **R5. Termination.** Theorem A says "terminates and is true". Without Lemma T, the honest statement is "if the ground type computation terminates, it is true". That still gives consistency, because a closed proof of `False` means the checker's own computation of the type terminated. But it weakens Corollary C.

Low risk: the corollaries, the `Eq` rules at ground, the syntactic stability items, and the cases of Theorem A that read the rules backwards.

## 4. Recommendation

**Write the paper proof, and mechanise its crux (Lemma N) alongside it. Do not try to mechanise Theorem A as a whole before submission. Sharpen the conjecture whatever else happens.**

- **Now (about 1 day):**
  - sharpen Conjecture 3 and property 9. Name the states compared: the refined and normalised symbolic state against the concrete one, equal after ending every borrow. Change footprints to "contains, and the extra conjuncts hold" (R3);
  - reframe it as the substitution lemma, as reviewer 8's (c) suggests;
  - run the R3 checker probe.
- **Paper proof of Theorem A and Corollaries B and C for F (4–6 appendix pages, about 1 week):** it cites the frame, `close_*`, `exec_wf` and property 7, and proves Lemmas W and G in full. With Lemma N not yet mechanised, it goes in as "Theorem 1, proof in Appendix X, whose Lemma N is mechanised for [list]". That is what reviewer 8 said would move their score.
- **In parallel, mechanise M4 (Lemma N) plus M1 (1.5–3 weeks):**
  - it is the step most likely to be wrong on paper (R1, R2);
  - it also closes the only `sorry` (M5, Lemma T), which reviewer 7 noticed;
  - it answers reviewer 7's request directly;
  - it is where every earlier false statement lived (F3, F5).
- **Leave D53 moves (M1′) and the typing judgement (M3) for later.** In the paper proof, F's reads are copies. Adding moves to the paper proof is cheap: one case per rule. Mechanising them is not.

**Why not "neither":** the reviewers say only a theorem moves their score. The exercise is also likely to find a real problem before a reviewer does; R3 is already a candidate. **Why not "mechanise it all first":** about 2–4 weeks with the crux untested, and M4 has walled once already. The paper proof lets the typed argument be reviewed now, while the part most likely to fail is checked by machine.
