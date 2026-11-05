# 21. Copy-or-move and η at `Unit` decided from declared types

Written by the orchestrating session on 2026-11-05, at the user's request ("yes start that lane"), to drive the `declared-copy` lane. The implementer is a different agent (spec/implementation separation); the orchestrator reviews; the merge to main is the user's.

## Why

Ochr checks a definition by running it twice over: once at its *generic call*, on unknowns, and directly at each instance. The consistency plan (`docs/18`) needs the decisions the machine makes along a run to come out the same on both paths. The two-paths census (`ochr/core/notes/two-paths-census.md`) lists every decision and what it reads. Three of them read a *computed* type, the type a value has after evaluation, and are kept only on a one-directional argument:

| Census site | Decision | Today it reads | Argument today |
|---|---|---|---|
| 16 | copy or move on a read (D53) | the place's stored (evaluated) type, else the value's own constructor in an untyped run | the generic call is stricter: an unknown type is never a copy type, so it moves at least what an instance moves |
| 13 | stuck-block captures: copied or moved | copy-ness of each place's stored type | as 16 |
| 9 | η at `Unit` for a call's result (D59) | the declared codomain, else the call's computed result type | a path where the type is still unknown keeps the value un-normalised and is "only more stuck" |

There is a fourth site of the same kind that the census does not list: when a call is closed off ([Close]), a borrowed argument whose content is literally `()` gets `()` back instead of a sealed program (`closeCall`, the line `if u == .unit then pure .unit`). That reads a value. Example where the two paths differ:

```
def TouchA (A : Type₀) (a : &A) (n : Nat) : Unit := match n { Z => (), S(m) => () }
def ExA (A : Type₀) (x : A) (n : Nat) : A := ( let c = x; TouchA(A, &c, n); c )
```

At `ExA`'s generic call `c` holds an unknown, so its fill is a sealed program; at the instance `ExA(Unit, (), n)` it holds `()`, so its fill is `()`.

Each one-directional argument is a lemma the consistency proof would have to prove (a monotonicity lemma: refining an unknown can only turn "move" into "copy", "stuck" into "`()`"). The user's preference is correctness by construction: make all four decisions read only syntax and declared types, as Rust does (a generic `T` is never `Copy` without a bound, whatever it is instantiated at), so both paths decide them identically and the lemma disappears. This moves sites 9, 13 and 16 from class (c) to class (a) of the census.

## Evidence so far (the `copy-probe` fork, 2026-11-04, on `7ebfdb75`)

A throwaway probe (worktree `../ochre-copyprobe`, branch `copy-probe`, never to be merged) tried two narrow versions:

- **E1, copy-or-move from a generic reading of the declared type** (type parameters made unknown, the declared type evaluated): no verdict changed in the whole suite. 4,850 individual decisions changed (copied today, moved under E1), in 50 declarations, all instance runs where a type parameter is `Word` or similar. No verdict changes because a definition's own check already moves values of type-parameter type, so a body that reads one twice is rejected there before any instance runs. The probe fell back to today's rule when its generic reading failed to type-check (dependent parameter types), so 4,850 may be an undercount.
- **E2, η at `Unit` only from a call's declared codomain:** 4 verdicts changed, accepted to rejected, all in `ClosingOff.lean`'s block on computed `Unit`: `RowI`, `ConvUnitRes`, `ConvUnitWritten`, `ComputedUnit`. Nothing else in the suite.

Read the probe's diff (`git -C ../ochre-copyprobe diff`) for orientation only. Do not build on it: its fallbacks to today's rule are exactly the seams this lane removes, and it predates D79.

## The rule

**One reader.** There is one reader of declared types, the one D77 introduced for a binding's class (`Decide.typeDecl`, `typeFnDecl`, `agreeTypeDecl`): it reads a declared type term without evaluating it, unfolding a call of a type function as the body is written, through `let`s and the arms of a match, the arms required to agree, a call of the function itself saying nothing new, a type parameter of a type function standing for the call's argument read as a type. Today it reads only whether a type is a Π-type, and of which class. This lane extends it so that it also answers two questions about a declared type: *is it `Unit`?* and *is it a copy type?* Both answers are computed from syntax, declarations and the stored readings of bindings only, in `Decide.lean`, which cannot run the machine (the import graph enforces this).

- **Copy type, as read.** As P3 lists today (`Unit`, a sort, a proposition, `Eq`, an inductive declared `copy`, a non-recursive non-dependent inductive in `Type₀` whose field types read as copy types at the arguments as written), plus: **a variable whose declared type is a sort (a type parameter) is never a copy type.** Ochr has no bounds; a `copy` bound on type parameters is out of scope (record it as a follow-up if some program needs it). A type function call reads as a copy type exactly when every arm of its body does. Anything the reader cannot see through (an unknown, a Π-type, a borrow) is not a copy type.
- **`Unit`, as read.** A declared type reads as `Unit` when it is written `Unit`, or is a call of a type function every arm of whose body reads as `Unit` (so `UU(n)` reads as `Unit` for every `n`, since both of `UU`'s arms are `Unit`), and so on through the reader. Never by evaluating.

**R1, copy or move.** A read of a place copies exactly when the place's declared type reads as a copy type (or inside `clone`). The declared type of a place is: a parameter's written type; a `let`'s annotation, or, unannotated, the declared type of its right-hand side as the reader reads it (a call's declared codomain with the arguments substituted as written, a place's declared type, ...); a projection's field type at its parent's declared type; a pattern variable's constructor field type at the scrutinee's declared type. The value's own constructor is never consulted (delete the `valType?` fallback in `copyRead`). The same reading decides stuck-block captures (census site 13), closure captures ([Closure]: "moves the captured places whose types are not copy types") and the Fn rule.

**R2, η at `Unit`.** A value is replaced by `()` exactly where its *declared* type reads as `Unit`, never from a computed type. Positions: a parameter (or a fresh unknown made for one) whose declared type reads as `Unit`; the result of a call whose callee's declared codomain reads as `Unit`, whether or not the call closes off; and any other place a declared type sits over a value (the type slot of `Id`/`Eq`, a `let` annotation, the declared codomain of a closure). Decide during the lane which of these positions the machine needs, and state the list in RULES; the principle is that a declared `Unit` normalises and a computed one does not. Delete "or evaluated declared type" and "or computed result type" from RULES §4 and the paper.

**R3, the [Close] fill.** A borrowed argument's fill is `()` exactly when the callee's parameter's declared type reads as `&Unit`; otherwise the sealed program. Not when the content happens to be `()`.

## What to expect

- R1: no verdict change, per E1. If a verdict changes, find out why before going on.
- R2/R3: E2's 4 breakages were measured under a narrower rule (codomains only, no reading through type functions). Under R2 with the D77 reader, `UU(Z)` and `UU(n)` both read as `Unit`, so all four may stay accepted, and `NeutralKept` (rejected today, a true statement since `UU(n)` is `Unit` for every `n`) may become accepted. Measure; don't predict.
- Every verdict change is listed in the decision entry and the commit message, one line each with its reason. A rejection that becomes an acceptance must be a true statement (say why). An acceptance that becomes a rejection is either rewritten (the test is about computed `Unit`: write `Unit` where η is wanted) or kept as `reject def` with a comment saying what the rule now says. If anything outside `ClosingOff.lean`'s computed-`Unit` block changes verdict, stop and report to the orchestrator before rewriting tests.

## Deliverables

1. The checker: R1–R3 in `Decide.lean` (the readers) and `Machine.lean` (the call sites), no fallback to a computed type or a value's constructor anywhere in these four decisions. The docstrings on `copyRead`, `resultIsUnit`, `blockCaptures` and `closeCall` stop saying "two paths, value-dependent by design" and say what they read. Rule tags in the paper's names (the checker implements exactly the paper's rules, tagged; the build checks the tags).
2. Tests: the four `ClosingOff` tests and `NeutralKept` as measured; new tests for each rule, each with a twin: an instance run where a type-parameter place is now moved (`f (A : Type₀) (x : A)` read twice in a statement at `A := Word` is rejected; `clone` makes it accepted); `ExA`/`TouchA` above, with a statement showing the instance and generic fills agree; a type function whose arms disagree (`Unit` vs `Nat`) is neither `Unit` nor copy, and one whose arms agree is.
3. RULES.md: P3, [Read], [Closure], §4's η paragraph, [Close]'s fill. DECISIONS.md: D80, with the evidence (decision and verdict counts before and after, total test count). The paper: `eval.typ`'s [Copy], appendix [Copy]/[Read], the appendix's η paragraph, and any text in §6.3 that argues copy-ness or η "generic stricter" or "only more stuck"; both sides change in the same landing.
4. `notes/two-paths-census.md`: sites 9, 13 and 16 become class (a); add the [Close] fill as a site.
5. Don't edit `ochr/docs/17`–`20`; the orchestrator updates the consistency plan after landing.

## Process

- Worktree with raw git, from current main (`9b0f36ff` or later): `git -C /home/charlielidbury/repos/ochre worktree add /home/charlielidbury/repos/ochre-declared-copy -b declared-copy origin/main`. Seed the Lean cache: `cp --reflink=always -r /home/charlielidbury/repos/ochre/ochr/core/lean/.lake /home/charlielidbury/repos/ochre-declared-copy/ochr/core/lean/.lake`, then `lake build` there. Pin background builds with `taskset -c 0-14`.
- Commit in the worktree at meaningful checkpoints (R1 green; R2/R3 green; docs), push the branch. Detailed commit messages: what changed and why.
- Report to the orchestrator with the verdict table and the decision counts. After review and the user's go-ahead, rebase onto the latest main (never a merge commit), rebuild green, and `git -C /home/charlielidbury/repos/ochre merge --ff-only declared-copy` then push main; on failure, rebase again and retry.
