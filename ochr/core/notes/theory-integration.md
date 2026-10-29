# Theory-lane integration (2026-10-29)

Branch `theory-integration`, off main `4cc0beda`: the four theory branches brought in as one reviewable branch, in the order `depfields-model`, `split-model`, `rec-model`, `stability`, by cherry-picking each branch's commits in order with their original messages. Each commit whose pick needed a conflict resolved says so in a `[theory-integration]` paragraph at the end of its message.

## What each branch contributes

| Branch | Contribution |
|---|---|
| `depfields-model` | D75: a closed-off `J` ends its borrows where its transported term ends (closes `BoomJ`, a closed proof of `False` on main). D76: invariant (W) and the producer obligation (P); [Return]; `closeBlock` is the only place a block is formed, and it runs its arms itself; D72 and D75 become corollaries. The `Producers` and `JBlocks` attack tests. `notes/depfields-model.md` (S1, S3 as proposals). |
| `split-model` | Every split arm runs in a world (`enterWorld`/`inWorld`/`exitWorld`, replacing `restoreArm`); `Id`'s and [Conv-fun]'s observation is one operation (`obsResult`). `notes/split-model.md`, `notes/id-model.md`. No finding. |
| `rec-model` | D78: a recursive call is recognised by name (`recUid`, `capMarks`, `recFrameOf`), not by value (closes `BoomCapSplit`/`BoomCapLam`, a closed proof of `False` on main). `notes/rec-model.md`. |
| `stability` | D77: a binding's class is read from its type's syntax, including through type functions and `let`-named types; a statement argument's place too. `Ochr/Stability.lean` (Conjecture 2 stated, `sorry`). `notes/stability.md` (per-site classification, the (P) probe, the heap viability lane). `Ochr/Heap/Slice.lean`, `HeapSlice.lean` and the `heapslice` exe (not a default target); the scratch probes (not built). |

## D-numbers

No collisions: each lane took a different number. Map: D75, D76 (`depfields-model`), D77 (`stability`), D78 (`rec-model`). `DECISIONS.md` lists them in numeric order (D77 placed before D78, though `rec-model` was integrated first).

## Conflicts and how they were resolved

- **`Machine.lean`, `splitArmsThenClose` / `closeBlock`** (split-model's world commit over D76): `splitArmsThenClose` keeps D76's `BlockArm` form, and split-model's world discipline moves into `closeBlock`'s arm loop. `closeBlock` now calls `enterWorld` once and runs each arm inside `inWorld`, capturing the arm's end state inside the world, instead of `restoreArm`, which split-model deleted. The closed-off `J`, which D76 routes through `closeBlock`, therefore also runs in a world, which is D76's stated behaviour (its arm drops its generalisation records as a match's arms do).
- **`Ochr/Stability.lean`, the `captures` field** (stability over D76): D76 deleted `closeOffMatch`; the field is restated over `closeBlock`, with the same arms run at both states (arms are computations that read the state they run in).
- **`RULES.md`**: split-model changed only the [Split] line and rec-model only the [Rec] line; each side's change kept.
- **`DECISIONS.md`**: entries kept and ordered D75, D76, D77, D78; D77's "Known incompleteness" bullet replaced by its own follow-up's "Type parameters" bullet.
- **`notes/stability.md`**: its one reference to `closeOffMatch` now names `closeBlock`.
- **`Registry.expectedTotal`**: 1663 (main) + 22 (depfields-model) + 6 (rec-model) + 33 (stability: 11, 9, 13) = **1724**.
- **`paper/main.pdf`**: rebuilt from the merged sources after each docs pick; 67 pages, §11 Conclusion on page 25.

## Checks

- Full `lake build` green after each branch (97 jobs, then 100 with `Stability.lean`); every verdict asserted on every branch holds, including every attack test's rejection with its asserted reason (`ochr` blocks assert verdicts at elaboration, `rejectedWith` guards assert reasons).
- `lake build tests fuzz heapslice` green.
- `lake exe heapslice` on the integrated checker reproduces the stability lane's comparison: 46 (P) checks, 46 agree; the same six closing-off differences.
- No behaviour change from combining the fixes was found.

Final verdict total: **1724**.
