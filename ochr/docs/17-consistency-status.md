# 17. Consistency: where things stand after the overnight run

Written by team-lead on 2026-10-30, for the user's return. The goal was "pursue full consistency of Ochr in whichever way you see fit". The theory lanes have since been merged; the branches still waiting for review are listed below.

## The short version

- **2026-11-02, OPEN: a fourth closed proof of `False` on main (`f5b030d4`), `EtaBoom`, not yet fixed.** Found by an attacker of docs/18, confirmed independently (`Bad1`, `Boom : False` accepted, control rejected). Leaving a split arm keeps η-refinements of one-constructor unknowns (`etaRefs`), on the claim that they "follow from the type alone"; but for a dependent constructor the field unknowns' types depend on the arm's refinement, so a sibling arm reuses fields typed in another world (`y : Void` where `Nat` is due), and a zero-arm match proves `False`. The bug predates the world choke point (`restoreKeep` kept `etaRefs` since D68). **The claim is false where it is written**: `notes/split-model.md` (η-refinement "world-independent"), the paper's A.1 state paragraph ("which follow from the type alone"), and docs/18's worlds rule (X); the split-model "no hole" result below is wrong for this case.
- **2026-11-02: the Lean `Conjecture2` (`Ochr/Stability.lean`) is false as stated, so `theorem stability` is a `sorry` proof of a false proposition.** Its `RunsCorrespond` demands equal contents after resolution, but at the reachable generic state of the accepted `G (n x : Nat) : Unit := ((match n { Z => (let y = x; ()), S _ => () }); ())` the generic run leaves `x` moved (`⊥`) while the instance at `n := 1` keeps `1`; the over-approximation is real (its variant ending in `x` is rejected). It must be restated with an ordering (`⊑`), as the plan's own agreement clauses already are. Separately, `ValueDeclCommutes` fails at states with unchecked globals, and those states are reached (a definition's own code is re-run before it is accepted). Nothing should rely on `stability` until it is restated.
- **2026-11-02: the docs/18 plan, attacked by three independent read-only referees.** None found a closed proof of `False` beyond `EtaBoom`, and none showed consistency impossible; all three found the plan *as written* cannot be completed. The shared main gap (found independently twice): truth is defined in the set model, but the soundness walk and every lemma under it ((P), (C), (Sp), frame, stability) speak only of machine values, and accepted programs prove things whose hypotheses only non-computable witnesses satisfy (a halting decider, `L3`, `UseK := K(M)`). Rescue: truth over machine values (realizability with Girard-style candidates, which also removes the inaccessibles) or a full denotational semantics with adequacy. Also: a cycle (stability must be fused into the soundness induction), no proved bridge between the heap design and the real checker, a stuck `J` at extensionally-equal endpoints breaking soundness clause (i), and ~80 unchecked `xs[i]!` accesses as a missing proof obligation.
- **Three real closed proofs of `False` were found on main and fixed** (on branches): `BoomI2` (D73, merged earlier), `BoomJ` (D75) and `BoomCap` (D78). All three came from the model lanes (deriving rules from a small model, docs/14 R1-style), none from the test suite.
- **The certifying checker (docs/15, route R4) works.** 1,161 of 1,226 accepted definitions certify, including both reference sets and the whole quicksort case study (`QSCorrect` in its planned Lean form). Lean's kernel refuses the certificates of `BoomJ` and `BoomCap` on a base where Ochr's checker still accepts them, each for the actual reason they are wrong: the certifying route keeps consistency even where Ochr's rules are wrong.
- **The theory side reduced the two-paths (stability) conjecture to a short list of lemmas**, each area of the calculus now stated as principles plus obligations, with choke points in the code so the obligations hold by construction.

## Branches to review

Merged since this was written, so no longer listed: `closeoff-model` (the theory chain), `frame-model`, `inductive-model`, `conv-model`, `decide-commute`, `decide-footprint`. The four below each branch directly off main (at an older commit), and none is stacked on another.

| Branch | What it holds |
|---|---|
| `cert` | **Both case studies fully certified (docs/15 R7.3)**: every accepted definition in the quicksort and hash-map studies, `QSCorrect` and `InsertFindOther` included; 1,249 of 1,289 suite definitions; nothing excluded (every certificate written passes Lean); the 40 without one are translation gaps outside the case studies (function values without a signature, stuck blocks returning a borrow, borrow-returning definitions as values, six one-offs). Paused there: the remaining gaps are completeness, not consistency, since certifying mode already rejects whatever does not certify. Carries `cert-faithful` (R6: each certified data function compared with Ochr's machine on concrete inputs, as a build target: 332 functions, 1,912 checks decided by Lean's kernel, no disagreement). Off main at `frame-model`; changes what the build requires. |
| `heap-close` | Off main at `frame-model`: closing off in the heap slice (thunks), the frame part of (C) proved sorry-free (`Ochr/Heap/Close.lean`); 1,166 runs agree with the real machine (0 differences), 579/579 forced thunks agree with direct calls. Remaining for (C): renaming invariance of fresh handles (2–3 weeks), nested thunks (~1 week). `notes/heap-close.md`. |
| `paper-metatheory` | **A proposal**, off main at `frame-model`: the abstract's last sentence, §1.4's contributions bullet, Figure 9's status column and §7 rewritten for per-program consistency via certificates, the models, and the reduced stability conjecture. Body still ends on p25 (no slack left). Coverage figures need refreshing when `cert` finishes; the Conclusion is untouched. |
| `port-step1` | **Not merged** (checker refactor), off main at `decide-footprint`. Heap-port step 1: 50 whole-value walks censused; the 17 scans of Ω replaced by a borrow-holder index (`MState.holders`), verified against the old scans on the whole suite, no verdict changed. The other 33 (walks of a single value: holes, loans) need per-node summaries, which belong to the port's value layer itself. `notes/port-step1.md`. |

Nine areas are now modelled (dependent fields, case splits, `Id`, recursion, erasure, closing off, frame, inductive types, conversion); the three proofs of `False` all came from the first four.

## What is now true, and why

| Property | Status |
|---|---|
| Consistency of each accepted program in certifying mode | **By construction, relative to Lean** (docs/15 R11): an accepted program's theorems are Lean theorems. Complete for 1,161 of 1,226; the rest are listed translation gaps. |
| Two paths make the same *decisions* (erasure, class, [Close] row, proof matches, sorts) | **By construction** for 8 sites (`Decide.lean` cannot run the machine); 11 more follow from stated principles; 6 rest on lemma N (`notes/stability.md`). |
| Dependent fields, case splitting, `Id`, recursion, erasure, closing off | **Modelled**: each has principles and obligations (`notes/*-model.md`), every checker rule maps to one, and a choke point enforces each where it fits. |
| Stability (Conjecture 2) | **Reduced** to N = (P) + (C) + (Sp), plus M. (C) reduces to the frame property plus (P). (P) is one internal lemma under the heap design (proved on a slice). |
| Frame property (paper property 2) | **Modelled**, no hole; **proved on the heap slice** (locality, `call_effect`), by construction for every run of the capability executor. |
| Consistency of the calculus as a whole (docs/14 R1–R3) | **Open**, with the remaining work costed (`notes/frame-model.md`): on the heap design (P) and frame are free, (C) needs a thunk node (1–2 weeks), (Sp) about 1 week, M 2–4 weeks or free if typing becomes the same program, after a 4–8 week port. |

## Decisions waiting for you

1. **Merges**: `cert`, which brings `cert-faithful`; `heap-close`, `paper-metatheory` and `port-step1` are independent of it and of each other.
2. **The heap restructure** (`notes/stability.md` §8): make (P) free by porting the value layer to a heap with `view`/`alloc`/`fill`. Estimated 4–8 weeks; steps 1–3 (replace whole-value walks with metadata, key tables by identity, a type per unknown) are verdict-neutral and worth doing regardless.
3. **The `CLAUDE.md` definition of correct** gaining "every accepted program certifies, or is listed with its reason" (wording in the `cert-integrate` report, `notes/cert-progress.md`).
4. **Rule-changing proposals** (none implemented): S1 and S3 (`notes/depfields-model.md` §9), P-c (`notes/erasure-model.md`), `RecCtx.cands` and the [Rec] value-equality fail-safe (`notes/rec-model.md`).
5. **The meaning of borrow-returning function values in certificates**: encoded as A.6 Definition 5's injective backward function (a proof carried in the type, no axiom), not get-after-put (false for `TailM`). A faithful encoding of the paper's own model, flagged because it is a semantic choice.
6. **Induction on proofs** (docs/13): still open; the derivation-as-data workaround works.

## Process notes

- The model lanes found every proof of `False`; certificates found none in the suite but refused both known ones. The two routes check each other.
- Two harness lessons are saved to memory: never wait with `pgrep -f` on a pattern in your own command (it deadlocked lanes for an hour), and never trust a silent `lake env lean` probe on a stale build (always print verdicts and include a control).
