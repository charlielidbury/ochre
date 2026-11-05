# 22. Every binding has its declared type: called bodies run typed by declaration

Written by the orchestrating session on 2026-11-05, at the user's request, to drive the `typed-bodies` lane. The implementer is the agent that ran the probe (branch `probe-typed-bodies`, `e79a9227`); this document, not the probe, is the specification. The orchestrator reviews; the merge is the user's.

## Why

The machine has two modes. Typing (the checked definition's own run) carries a type with every value and splits when stuck; the machine (called bodies, re-runs of sealed programs) carries none and closes off when stuck. Only the second difference is essential. Because the machine carries no types, it works a binding's type out from its value when a decision needs one (`valType?` via `placeType?`): from a constructor's head, from Δ for an unknown, by a typing run for a sealed program. Refining an unknown to a constructor switches which route is taken, so the same place can get its type differently on the generic call and at an instance. That is a hazard for (P) (a run that never looks at σ is unaffected by refining it), and the consistency proof would need a lemma per route. It also forces `observeTyping`'s machine-first re-observation (census site 21), whose docstring says typing from the start "would need the type of every value in an untyped frame, which `⋆` and `⊥` do not have": a decision that depends on whether a run got stuck.

## Evidence (the `typed-bodies` probe, `e79a9227`, built on the pre-D80 ablation branch)

- Every binding typed by declaration, the value fallback off, captures excepted: **0 verdict changes** of 1,844. With the fallback off and nothing in its place: 670.
- Declared type vs the value-read type over ~723,000 lookups: 0 disagreements; 332 equal only up to conversion (function-typed parameters whose closure writes its Π-type differently); 48 where only the declared type exists (values with moved-out holes, `⋆`).
- Captures typed too: 85 root failures, all "cannot infer the type of the place κ": a closure records its captured values, not their declared types (D51 records them for proofs only; D80 added each capture's *reading*, not its type).
- `observeTyping` typing from the start: 0 verdict changes.
- Check time: 49.5 s → 77.6 s, the declared types being evaluated at every call with no caching.

## The rule

Every binding, in every run, has a stored type, its declared type:
- a called body's parameters: the callee's declared parameter types, evaluated left to right at the arguments, as [Def] does at the generic call;
- a pattern variable: its constructor field's type at the scrutinee's type;
- a `let`: its annotation, else its right-hand side's declared type (the D80 reader);
- a closure's or Π-type's captures: the declared types of the captured places, recorded when the closure is formed ([Capture]; extend D51 from proofs to all captures, and D80's readings to types);
- the checker's internal frames that bind values to compute a type: field telescopes (`fieldTele`, `fieldTypeAt`), a sealed program's result frame, `runBodyCore`'s parameter frame. The probe found each needed only a one-line change.

Then:
- **Delete** the binding fallback: `placeType?` never reads a binding's value to get its type.
- **Delete** the re-observation: [Obs] runs a side of `Id` with the typing judgement from the start, in every run (census site 21 goes).
- The machine and typing differ only in what they do when stuck (close off vs split). Say so in RULES and the paper; renaming the `typed` flag to say what it now means is welcome if cheap.

**Out of scope.** `valType?` on *embedded* values (sealed programs, loans, field contents, the packing and lending checks: about ten sites) stays; list each in the census as class (c) with its argument, as a later question. No caching or other speed work: report the check time and leave optimisation to a branch until a workload needs it.

## Expectations and acceptance

- No verdict changes are expected. List any change with its reason; if one is not explained by the rule, stop and report before going on.
- The paper's A.1 state paragraph ("the stored type A is omitted for the parameters bound by the untyped machine") and every other text about untyped frames, RULES, the census (the value fallback and site 21), and a DECISIONS entry D82 change in the same landing as the checker, with rule tags as usual.
- Tests: a closure capturing data then run at an instance; a pattern variable whose value has a moved-out hole (typed only by declaration); a stuck `Id` side in a called body now typed from the start; each with a twin where it helps.
- Report the check time before and after.

## Process

- A fresh raw worktree from current main (`efb7a8f7` or later, which has D80 and D81): `git -C /home/charlielidbury/repos/ochre worktree add /home/charlielidbury/repos/ochre-typed -b typed-bodies origin/main`; seed `.lake` by `cp --reflink=always -r` from the primary checkout; pin builds to cores 0-14. The probe branch is reference only: its switches and detect mode do not land.
- Commit at checkpoints, push the branch, report. After the user's go-ahead: rebase onto the latest main (never a merge commit), build green, `git -C /home/charlielidbury/repos/ochre merge --ff-only typed-bodies`, push main.
- Another fork (`no-eta`) is experimenting on η at `Unit` on a local branch; it does not land, so it does not block this lane.
