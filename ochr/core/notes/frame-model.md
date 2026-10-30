# The frame property: a model, a check, and a proof on the heap design

The `frame-model` lane, 2026-10-30, branched from `closeoff-model` (`0f104430`). Status: no hole found; one invariant turned out narrower than stated (F4, below); a verdict-neutral assertion landed in the checker; locality and `call_effect` proved sorry-free on the heap design.

The frame property is the paper's property 2 and Assumption 11 (T2): a run changes the state below its own frame only through the loans held by its frame's borrows, and a call's effect is its isolated run, plugged back into the caller. The stability lane reduced the two-paths conjecture to N = (P) + (C) + (Sp), plus M; `closeoff-model` reduced (C) to the frame property plus (P). So this is the central unproved lemma. The deleted meta-lean proved it (`frame_local`, `call_effect`) for an earlier rule set.

## 1. The model, as principles

- **F1. Names are local.** A running body names only places of its own frame: a variable resolves in the top frame (`varPos`). A closure's captures are copied into its own frame when it is called, and a closure captures no borrow (A.5, condition 4). Globals are immutable.
- **F2. Writes stay in the frame.** A borrow carries its content (`borrow_ℓ v`), and the lender holds `loan_ℓ`. So `*r := t` changes the content inside the borrow held in the running frame; the lender's place does not change until the borrow ends.
- **F3. Calls exchange only what is passed.** Arguments move into the callee's frame: owned values are moved out of the caller, and a borrow argument carries the caller's loan (A.5, condition 5: each argument is loan-free, or a borrow of loan-free content). The callee returns its result; popping its frame drops its bindings, which ends its borrow parameters. [Close] puts its fills into the loans of the call's borrow arguments. Nothing else crosses.
- **F4. Borrowers sit at or above their loans** (for the frames a program pushes). A loan in frame `f` is borrowed from frame `f` or a frame above it. Its sources: no borrows in data and no borrows of borrows (types), a closure captures no borrow, and a borrow of a local never outlives the local ([Drop]'s "dies while a value in flight borrows it", D65). Consequence: [Access] and [Drop], which start from a place of the top frame, only ever end borrowers in the top frame.
- **F5. Ending is the one channel down.** [End] substitutes the content for `loan_ℓ` wherever the loan occurs, which is how a lender below gets its content back. By F4, the borrows a run can end are its own frame's, so the places it can change below are exactly the places those borrows were lent from: the frame's ports.
- **F6. Private runs leave no trace.** A statement position (`inStatement`) and the checker's scaffolding (`privately`) run on a copy, which `restoreKeep` throws away.
- **F7. Sealed programs are closed.** A sealed program's re-run (`nfSealed`) runs from the empty environment and reads no frame. It changes only by substitution: [End] (F5), or refinement (F8).
- **F8. Refinement is not a run.** [Split] and [Split-gen] substitute across every frame (`substEnv`, `mapState`), but that is the typing judgement acting on the whole state, not a run's effect. A callee's body runs in the machine (⇓app), which never refines.

## 2. Against the checker

| Rule, function | Principle |
|---|---|
| variables (`varPos`), [Read], [Borrow], [Assign] (`readPlace`, `borrowPlace`, `assignPlace` via `setPlace`) | F1, F2 |
| [End] (`endBorrow`) | F5 |
| [Access] (`accessPath`, `accessInside`, `accessNeutralHead`) | F4: now through `endTopLoan` |
| [Drop] (`dropTopBind`, `endLoansOfTopBind`, `dropValue`, `endLoansOfTopTemp`) | F4/D65: the last two now through `endTopLoan` |
| [App]'s pop (`popFrame`), [Close] (`closeCall`) | F3 |
| stuck blocks (`closeBlock`): a call of an anonymous function of its captures | F3 |
| closure capture (`capture`) | F1 |
| `inStatement`, `privately` (`onCopy`) | F6 |
| `nfSealed` | F7 |
| `substEnv`, `renormAll` (`mapState`) | F5 ([End]), F8 (refinement) |

No rule lets a run whose effects persist reach a place it neither owns nor was lent.

**F4 is narrower than first stated.** The assertion below first fired on accepted programs: `DepFields.CellGet` and `GetLentOk`. The checker computes a field's type by binding copies of the value's fields in a scratch frame of its own (`fieldTele`, under `privately`). At `CellGet`'s generic call that frame holds `o = Some(loan_1)` while the borrower `r = borrow_1 σ3` lives in the function's frame below, and reading `o` there ends `r`'s borrow. This happens on the private copy, so nothing leaks (F6), but F4 is an invariant of runs whose effects persist, not of every frame the checker builds.

**Choke point (landed, verdict-neutral).** `Machine.endTopLoan` is now the one place [Access] and [Drop] end a borrower found from a place of the top frame. It asserts F4 whenever the run is not inside a private copy, tracked by a new `MState.privateDepth` that `onCopy` raises. A violation is an internal error, never a silent write below the frame. The full `lake build` is green: it never fires on the suite.

**Probes.** These are registered as the block `FrameModel` in `Examples/Borrows.lean`, 7 declarations, with verdicts printed beside a rejected control:
- `RetHole` is rejected, by [Drop]: a borrow of a local escapes through a stuck call's hole (`let a = n; TailM(&a)`). Its twin `RetHoleOk` is accepted.
- `ClosOwn` is accepted: a closure that assigns its capture writes its own copy. `ClosOwnLie`, which claims otherwise, is rejected.
- `ReassignStmt` is accepted: re-pointing a borrow parameter at a local cuts it off from the caller's place. `ReassignLie` is rejected.

## 3. On the heap design, locality, proved

**The slice, extended** (`Ochr/Heap/Slice.lean`):
- Bindings are cells, a node holding a value's handle.
- A borrow is a handle to a place, `ref c path`. `*` follows a borrow to the cell it points into.
- Assignment rebuilds the value along the path and writes the cell.
- `let` and a call's parameters get fresh cells, so a call with borrow arguments runs on cells holding the argument handles.
- `Prog` gains `write`; a write counts as an ask in `queries`, and `exec_agree` gains its case. `P_evalH` is unchanged and still sorry-free.

**The theorems** (`Ochr/Heap/Frame.lean`, sorry-free). Each is one induction on `Prog`, and none looks at a case of the evaluator.
- `execR` runs a computation with capabilities. It may view or write only a handle it holds, and store only nodes whose children it holds. Viewing grants the node's children, allocating grants the fresh handle, and anything else is an error.
- `cap_queries` (locality): a successful capability run asks only about handles reachable from what it started with (`Reach`), or fresh ones.
- `untouched`: a handle a run never asks about keeps its node.
- **`frame`**: if a capability run succeeds, its result is the result of its isolated run (on `Heap.isolate`, where the frame is empty). The reachable part and the fresh handles end as the isolated run leaves them, and the frame is left exactly as it was.
- **`call_effect`** is `frame` applied to a callee: it holds exactly its arguments' handles, and through a borrow argument it reaches the caller's cell and nothing else of the caller.
- Axioms: `propext` and `Quot.sound`, plus `Classical.choice` for `frame` and `call_effect`, which decide membership of `Reach`.

**What this means.** On the heap design the frame property holds by construction for every run the capability executor accepts. A run that reaches what it was not given is an error, not an effect. Whether a given evaluator respects capabilities is then either a measurement or one per-construct lemma ("it obtains handles only from its environment, views and allocations"). The slice evaluator is written that way, and on the suite the capability executor never refused a run.

**The comparison** (`lake exe heapslice`, against the real machine):
- 98 functions in the slice, 37 with a borrow parameter, and 1,166 runs.
- 943 runs give the same value, and 162 are stuck on both sides.
- 61 are stuck in the heap where the real machine closes the call off and goes on. That is the known class: closing off is outside the slice. There is no other kind of difference.
- 469 final contents of borrowed cells were compared.
- (P) on the real machine: 193 of 193 agree.
- Capability runs: 1,166, of which 0 were refused.

**What locality does not cover, or where a port must take care:**
- **Granularity.** Locality is at the granularity of a cell: a borrow of `x.f` reaches all of `x`'s cell. That over-approximates, so it is sound.
- **Unknowns** are global handles granted to every run. They have no node, so no frame state lives there. A refinement filling one must stay the typing judgement's act (F8), never a run's.
- **A returned borrow's hole** becomes a handle. The fills that hold it, and the run that holds the returned borrow, both hold it.
- **A closed-off call** becomes a thunk, which must capture only its arguments' handles.
- **[End]'s global substitution** has no counterpart: a reference to a place needs no ending. So F5 becomes trivial.
- **The whole-value walks** of stability §8 affect (P), not locality.
- **The semantic gap.** The heap design replaces Ochr's moving borrows and loans with references to places. Their agreement on accepted programs is measured above, not proved. A port would adopt references to places, so the frame property would then hold for the checker itself.

## 4. What remains for N on the heap design

| Part | Status | Remaining work (agent effort, honest) |
|---|---|---|
| (P), substitution commutes with a run that never asks | proved on the slice (`P_evalH`, from `exec_agree`) | free once the machine is a `Prog`; the cost is the port |
| Frame, locality and `call_effect` | proved on the slice (`frame`, `call_effect`); 0 capability refusals on the suite | free under `execR` once ported; optionally the lemma "the evaluator never fabricates a handle", about 1 week |
| (C), closing off | reduced to frame + (P) on holes (`closeoff-model`) | a thunk node in the slice, then "forcing a thunk agrees with the direct run" from `frame` and `exec_agree`: 1–2 weeks |
| (Sp), splits commute | bookkeeping given (X)/(S) (`split-model`) | a split as fill and unfill of the scrutinee's node inside `enterWorld`/`exitWorld`, from `exec_agree`: about 1 week |
| M, typed and untyped runs agree (census site 21 only) | open | a simulation proof, 2–4 weeks; or free by construction if the port makes typing the same `Prog` with types as a second output |
| The port itself (stability §8) | prerequisites known: walks to metadata, identity keys, typed unknowns | 4–8 weeks to parity on every verdict |

Without the port, relating today's loan-and-borrow machine to the heap design is a simulation proof of its own, larger than any row above. I recommend the port.
