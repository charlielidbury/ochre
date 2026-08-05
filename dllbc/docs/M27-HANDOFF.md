# M27 handoff — phases α through δ

Written by `dllbc-p1` at the α boundary, for the build lead taking the ratified
function model into the kernel. Phases P1–P3 and the three soundness containments
are done and on `main`; `PROGRESS.md`'s M27 entry is the narrative, this is the
map.

Read the ratification brief for the model itself. This document is the parts that
are expensive to rediscover: measured scopes, one design danger, and a ledger of
traps this campaign actually fell into.

---

## Where the tree stands

Green at `12867305`. Thirteen commits of campaign work:

| | |
|---|---|
| `30298000` | P1 — the disposition ledger (`Tests/S27Dispose.lean`) |
| `2f94aa6d` `2b12d7fe` `9feed8fa` `297460a3` | P2 — instrument retirement, paper SHA pin, Bench deleted, surface-test cluster retired |
| `a41980f2` | P3 — copy-on-read ruled KEEP |
| `1dfdd1b7` | `collapseLoanIn` (cherry-pick; **no regression test on main**, receipt owed at the conversion) |
| `eb510a0f` `be679f35` `67cf6053` | the three soundness containments |
| `668f3987` `c9c2bb4d` | `back` retires from corpus, then from kernel |
| `c0d61f0c` `ad083f83` `12867305` | PROGRESS entry, dllbc-arrows folds, §12 refresh |

Corpus is **110 accept / 58 reject / 19 decline**; the 19 are the true `[v]`
payload-decrease residue, each with a written disposition in `S27Dispose` §B.

---

## α — the kernel

### α.1a: annotate `.lamR` (mechanical, but 95 of them)

`Term.lamR : List Var → Term → Term` (`Syntax.lean:202`) becomes
`List (Var × Term) → Term → Term`.

**Kernel sites**, enumerated so none is found by a red build instead of by
reading:

* `Syntax.lean` — 202 (the definition), 279 (`beq`: needs `Term.beq` on the
  types, **not** `==`), 419 (`freeRVars`: should traverse the types too).
* `Machine.lean` — 929, 1062, 2035, 2726, 3082, 3137, 3155, 3658, 3666, 3680.
  The last three are `sealRec`'s arm destructurings for `natRec`/`listRec`/`boolRec`.
* `AlphaEq.lean` — 70–73. Must alpha-normalize the binder types as well as the body.
* `FnMacro.lean` — 125, 251, 314, 398–405, 455.

**`Val.rfn` must NOT be annotated.** Ratified. `Syntax.lean`'s own comment is the
argument: *"the ascription IS the contract. Executing needs no types at all."* The
executing machine binds and runs; it never converts. `readR` drops the types when
it forms an `.rfn`. The symmetric change would look tidier and be wrong — this is
the model's erasure principle applied to the value side.

**`FnMacro:314` is free**: `.lamR (tel.map (·.1)) d.body` becomes
`.lamR tel d.body`, because the telescope already carries the types.

> **THE ONE DESIGN DANGER IN α, and the reason this handoff exists at this
> boundary.** `FnMacro:398–405` builds the recursor arms, and `restIds`, `dec`,
> `ih` and `stepBs` all need types. `rest` is already a telescope, so those come
> for free — but **`ih`'s type is the motive applied to the predecessor**, a term
> the macro must *synthesize*, and `dec`'s is the scrutinee's domain, which
> differs between `natRec` and `listRec`. That is design judgement, not
> transcription. It is the one place in α where a wrong answer compiles, passes,
> and is subtly the wrong type. Give it a control that would fail if `ih` were
> typed at the wrong level — M26-C already established that `ih`-at-the-wrong-level
> is a *type error rather than a check*, so the control exists to be written.

**Surface**: `Uni.lean:136`'s rule `λ "(" ident,* ")" "{" ublk "}"` gains `: uterm`
per binder. **95 runtime λs migrate**: `S26Rec` 69, `S26Prog` 19, `S27Mixed` 5,
plus 4 in `Machine.lean`'s doc comments. The types are all in the ascriptions
today, so each is a lookup rather than a decision.

### α.1b: the semantic half — keep it a separate commit

`sealFn`'s check becomes **one conversion** (synthesized Π against the
ascription); arm-checking becomes **motive-agreement**.

Split from α.1a deliberately: *a red build should never be ambiguous between a
mistyped binder and a wrong conversion rule.* 95 mechanical edits and two rule
changes in one commit makes every failure a two-suspect investigation.

### α.2: the enforcement rider

No function-typed runtime slots **at all** — complete `67cf6053`'s borrow-moded
case into the model rule: any Π-typed runtime binding refused, checking-side.
Functions live as names and capital bindings. `.callV`'s slot-reading case dies
with it; its scope/capital resolution survives. Fix D2's backwards doc comment
while there (c1's finding).

Your negative battery already exists: `S26Rec` §M and `S27Mixed` §F. §F2 in
particular — the borrow-free sealed function that must stay **accepted** — is the
control that caught an over-broad version of exactly this rule once already (see
the trap ledger).

---

## β — the surface

Juxtaposition application, `f a b`. The comma form parses until δ. `ctorApp`
disambiguates by reserved head, so `S n` and a call are distinguishable. Watch
statement sequencing (`f a; g b`) stays clean.

Note from the dllbc-arrows fold: the document's grammar has said `t t′` and
`λ (x : τ). t` all along. β and α.1a are the implementation returning to the
written grammar, not a change to it.

---

## γ — the fleet (P4)

**The conversion is a rewrite, not a re-derivation.** Measured: of 57 declarations
both paths reject, 54 produce the same message modulo σ/loan **numbering** (the
program path audits callees first, so its counter has run further), and the only
three real divergences are the guard twins `recBad`/`recMutA`/`recMutB` — whose
needle correctly becomes §8's "unknown function", the guard's deletion and scope's
replacement stated as an error message.

**The four-helper translation table.** ~285 call sites across 23 files, all
reached through four helpers in `Boundary.lean`:

```
checkFnOk d tbl        →  progOk (progOf (cohort) .unit)
checkFnErr d needle t  →  progRejects (progOf (cohort) .unit) needle
checkFn tbl d          →  checkProgram
runFn tbl d            →  programEnvs        (executing side: runProgram)
```

**Load order** for the worker split: `S23Direct` 56, `S24Arrays` 34,
`S19Partition` ~20, `S25ArrSort` 30, then a tail under 12. The S26 files' apparent
declaration counts are mostly `decl{ fn caller () -> Unit { … } }` *harnesses*
wrapping program terms — size them as trivial, not by line count.

**Standing lines every worker brief carries:**

1. **A twin that DECLINES teaches nothing.** It must MIGRATE and then be REFUSED,
   on both paths. A decline-tolerant helper quietly passes half a differential.
2. **Needles stay id-free.** The program path's fresh-supply counter runs further
   because it audits callees first; a needle containing `σ3` or `ℓ7` will pass
   today and rot tomorrow.
3. **One writer per file, across all lanes including merge time.** Per-file
   commits; worktree workers self-merge by rebasing.
4. **Per-demand-site controls, not per-rule-branch.** Phase A's finding, which
   fired three times since: a control that binds something and never demands it
   passes vacuously.
5. **`Le` computes.** A concrete `Le` twin passes for the wrong reason; only stuck
   spines are honest negatives (pk1's find).
6. **Assert your instrument before your conclusion.**

`S17`'s callee relocation per `S27Dispose` §C2; retire-class files per the
dispositions there.

---

## δ — P5

Delete `Decl`, `checkFn`, the tables, the `[k]` guard, the comma-call form. `fsig`
stores the Π `Term`, with `piPeel` on demand — **no surviving record type**; a
signature *is* a Π and the AST already has one.

> **SEQUENCING CONSTRAINT, verified by probe: the `[k]` guard must die in the same
> commit as `checkFn`.** Remove it earlier and the declaration path proves
> `Z = S Z` — `recBad` is `fn recBad () -> Id Nat Z (S Z) { recBad() }`, and
> signature-only checking admits a self-call at the function's own declared return
> type, so the decrease check is that rule's side condition. Five `S23Direct`
> assertions go red the moment it is removed alone.

Riding along: `alphaEq`'s `dec`-widening becomes **correct** exactly when the guard
dies (until then `[k]` is a guard input; after, it is purely a scrutinee hint, and
two declarations differing only in it elaborate to different recursors).
`Group.constrained` (the test-only identity wire the differential flips) and
`Decl.dec` each need a disposition.

**The ledger form to aim for**: `S27Dispose` §A's assertions are *gone* rather
than updated, because `(·.back.isSome)` no longer typechecks. The strongest ledger
is the one that fails to compile.

---

## ε — what remains

The already-final half is done: the PROGRESS entry (`c0d61f0c`), the dllbc-arrows
folds (`ad083f83`), the §12 refresh (`12867305`). What is left for whoever closes
δ is small: the final-deletions log, and the paper §7 one-sentence SHA treatment —
same shape as the §6 pin in `2b12d7fe`, which is the template.

---

## The trap ledger

Every one of these cost this campaign real time. They are ordered by how easily
they recur.

**Agreement is not coverage.** `Migrate.report` never compares a *declining*
declaration's declaration-path verdict — `progVerdict` returns `none` and the
comparison skips — so `disagree.isEmpty` was true throughout while **27 of the 42
declarations that stopped declining under a strip became REJECTS**. That is what
hid fourteen S19 regressions until a deletion exposed them. The harness dies at δ
anyway; the lesson does not.

**Measure outside the pools.** Every number this campaign produced came from
`S26Migrate.pools`, which is the *test corpus*. `Bench.lean`/`BenchQS.lean` were
`checkFn`'s other consumer, declared fifteen backs, and were invisible to all of
it — because being excluded from the corpus is precisely what they were *for*. Grep
the whole of `Dllbc/*.lean` **and** the lakefile when scoping a deletion.

**A deletion that removes MORE than intended looks exactly like a correct deletion
plus a compile error.** A regex written to swallow "docstring plus field" ate half
the `St` structure; the build reported `nextGroup`, `obligations`, `exitSyms` and
`entrySyms` as missing fields, which reads as fallout rather than as damage.
Exact-string anchors, one construct at a time, build between each.

**Validate one perturbation per file.** Importers cascade. Perturbing three files
at once reported only the first, and would have passed for validation of ten while
validating four.

**`with`-closures reach where syntax sweeps do not.** `nth2Lie` carried its `back`
as a record update, so stripping the `back = …` surface left it behind. Adopting a
fix at the source reaches the whole closure; sweeping the syntax reaches the
syntax.

**Both dispatch surfaces — including when the *ruling* names one.** The
mixed-return containment was ruled "at the same dispatch site", singular. There
were two, and the unnamed one (`checkRFnBody`, the seal) is the path the endgame
*keeps*. Patching only `checkFn` would have fixed the half being deleted.

**The isolating control is what knows your predicate is wrong.** The third
containment's first predicate was "resident in `fsig`", and the borrow-free
control went red: `sealMint` records *every* sealed function in `fsig` and
*additionally* reflects a borrow-free Π into `sctx`. The condition is **absence
from `sctx`**, not presence in `fsig`. Right prose, wrong predicate — and only the
control could tell.

**Probe through a module, never a scratch file.** `#eval` in a scratch file dies
with "incomplete case" on ordinary programs; the twelve-function well-founded
mutual block cannot be walked by the interpreter.

---

## Contact

`dllbc-p1` stands by as incumbent expert for questions on any of the above.
