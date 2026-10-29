# 15. A certifying checker: requirements

Started by team-lead on 2026-10-29 at the user's request. Status: **draft**. This is a requirements document for route R4 of docs/14: it says what must be true when the work is done, and how that will be judged. It says nothing about how to build it.

## Purpose

Every program the Ochr checker accepts comes with a **certificate**: a Lean development that Lean's kernel checks on its own. If the certificate checks, the program's theorems are theorems of Lean. Ochr's checker then no longer needs to be trusted for consistency: a wrong rule in it shows up as a certificate that fails to check, not as a proof of `False` that nobody notices.

## Terms

- **Certificate**: what is produced for one Ochr program, checked by Lean's kernel.
- **Corresponding Lean statement**: the Lean proposition a certificate gives for an Ochr statement (the type of a definition whose type is a proposition).
- **Trusted base**: everything that must be correct for a checked certificate to mean the Ochr program is right.

## Requirements

Each requirement has the test by which it is judged.

### Soundness

**R1. Checked means proved.** If a program's certificate checks, then for every Ochr definition in it whose type is a proposition, the corresponding Lean statement is proved in Lean.
*Judged by:* the certificate contains a Lean theorem for each such definition, and Lean's kernel accepts it.

**R2. No new trust.** A certificate introduces no axioms, no `sorry` (except as in R9) and no opaque constants standing in for Ochr definitions without their bodies.
*Judged by:* `#print axioms` on every theorem of every certificate in the suite lists only an agreed set of Lean's standard axioms (which ones is an open question below).

**R3. Certificates stand alone.** Checking a certificate does not run, import or depend on Ochr's checker. Otherwise the checker is trusted again.
*Judged by:* each certificate checks in a Lean environment that does not contain the checker's modules.

**R4. Every definitional equality is re-checked.** Wherever an Ochr proof relies on two things being equal by computation (`refl` after running code, closing off, `Eq` computing on constructors, `Id` computing to equations, η at `Unit`), the certificate justifies that equality in a form Lean checks: Lean's own computation or an explicit proof. Ochr's machine is never taken at its word.
*Judged by:* R2 and R3 together; no certificate can pass while relying on the checker's verdict.

### Faithfulness

**R5. Statements mean what they say.** The corresponding Lean statement of an Ochr statement expresses the same claim, readably:
- on data, the evident statement (`Eq(Nat, a, b)` becomes equality of natural numbers);
- for `Id(A, t, u)`, equality of what `t` and `u` return and of the final contents of every place either may write, with in-place functions read as functions from the borrowed places' contents to their result and final contents.
*Judged by:* a set of reference statements, at least `AddMZero`, `AddMEq`, `SubM`'s precondition, `SizeInsert`, the hash map's `InsertFindOther` and quicksort's `QSCorrect`, whose Lean statements a reader can check by eye against the paper's informal reading of them. The reference set and its expected Lean statements are written down before implementation starts.

**R6. Programs mean what they do.** For every data function, the Lean function in its certificate computes the same result and the same final contents of its borrowed places as Ochr's machine, on every input.
*Judged by:* this is the one trust assumption about the translation, and it is stated as such in the paper. It is checked on the example corpus by running both on concrete inputs and comparing; any disagreement is a bug in the translation.

### Coverage

**R7. Coverage grows in stated milestones.**
1. The paper's first-order fragment F (A.8): every accepted program in the suite that lies in F certifies.
2. The example suite: every accepted program in `Ochr/Examples` certifies, except those listed under R8.
3. The case studies: the hash map and quicksort certify in full.
4. Completion: every program the checker accepts certifies.
*Judged by:* a count in the build of accepted programs with and without a certificate, by milestone.

**R8. Every accepted program without a certificate is accounted for.** Until completion, each one is listed with a reason in one of two classes:
- a **translation gap**: a feature the certificates do not cover yet;
- a **rule finding**: the certificate cannot be produced or does not check because the Ochr rules accepted something they should not have.
A rule finding is treated like any closed proof of `False`: it becomes a `reject def` with the program that showed it, and the rule is fixed.
*Judged by:* the list is complete (it matches the count in R7), and no entry is unclassified.

**R9. Holes are visible.** A program with holes gets a certificate whose only `sorry`s are at the holes, labelled with their source positions.
*Judged by:* `#print axioms` shows `sorryAx` only for theorems that depend on a hole.

### Integration

**R10. Correct still means `lake build`.** Checking every certificate of the suite becomes part of `lake build`, so the project's definition of correct (`ochr/core/CLAUDE.md`) now includes "every accepted program certifies, or is listed under R8".
*Judged by:* removing a certificate, or breaking one, makes `lake build` fail.

**R11. A rejected certificate is a rejected program.** In certifying mode the checker never reports a program as accepted when its certificate fails to check. The failure is reported at the Ochr source location it concerns, with Lean's reason.
*Judged by:* a test program whose certificate is made to fail is reported as rejected.

**R12. The rules follow soundness, not the translation.** Ochr's rules change only when a certificate exposes a rule finding (R8), never to make the translation easier.
*Judged by:* every rule change made during this work cites a rule finding.

## What the paper may then claim

When R1–R11 hold at completion (R7.4): every program the checker accepts, both case studies included, is certified by Lean's kernel; its theorems are theorems of Lean, with the trusted base being Lean's kernel, the agreed axioms and the faithfulness of the translation (R5, R6). Before completion, the same claim restricted to the milestone reached.

## Non-goals

- A once-and-for-all proof that the translation is correct for every program. That would turn this into a consistency theorem for Ochr as a calculus (a syntactic model, docs/14), and is separate work.
- Consistency of Ochr as a calculus; this gives consistency per program.
- Verifying compiled code, or the native code behind `implemented by`. Natives are certified through their Ochr bodies; whether the native code matches its body stays outside the trusted base as it is today.
- Performance. Checking the suite's certificates only needs to stay practical for normal development (timings are engineering, not a result).

## Open questions

- **Which axioms are allowed** (R2): Lean's `propext` and `Quot.sound` seem unavoidable; `Classical.choice` is in the checker's own termination proofs today, but a certificate may not need it.
- **What a borrow-returning function means** in a statement (R5): a function to its result and a backward function, as in Aeneas, or something else; this decides how readable statements about `TailM`-like functions are.
- **Universes**: how Ochr's `Prop`, `Type₀` and `Type_i` map onto Lean's, given Ochr's non-cumulative universes.
- **Observational `Eq`**: Ochr's `Eq` computes on constructors to conjunctions; Lean's does not. R4 requires the certificate to prove each such step; whether the corresponding Lean statement uses Lean's `=` or a defined observational equality affects R5's readability.
- **Data derivations** (docs/13): derivations declared as `Type₀` data to get induction become proof-relevant in Lean; whether that matters for R5.
