# Closing off: a model, and what lemma (C) needs

Branch `closeoff-model`, off `erasure-model` (`f71ede9c`, which contains `theory-integration`: D75–D78 and the world, block and statement choke points). The sixth model lane. **No new hole found.** Closing off holds up on every probe, and lemma (C) of `notes/stability.md` reduces to two facts the project already names (the frame property, and (P) applied to holes) plus bookkeeping that the checker now keeps by construction. One coverage gap was found and closed without changing any verdict: re-normalisation after a generalised neutral is refined skipped the types of abstract values, which substitution reached. The probes are kept as a registered regression block (`ClosingOff.lean`, block `CloseOffModel`, 24 declarations; total 1,732 → 1,756).

## 1. What a closed-off call means

At a call point Ω a call `f(w̄)` gets stuck: its body needs a value it does not have. Its borrow arguments are `wᵢ = borrow_ℓᵢ uᵢ`, every `uᵢ` loan-free and whole; the others are values. What the call *does* is a function of its inputs: from cells holding `ū` and the other arguments, it returns a result and leaves final contents `ū′` in the cells. Closing off does not compute that function; it **delays** it. Each output becomes a *sealed program*: the call rebuilt as text, `⌈L; C; K⌉`, where `L` puts each `uᵢ` in a fresh cell `cᵢ`, `C` is the call with `&cᵢ` for each borrow argument, and `K` reads one output (nothing, for the result; `peek(cᵢ)` for a place's final content). A returned borrow's final content is not known at the call point at all: it is what the caller will write through the borrow before it ends. So it is a **parameter** of every output that can depend on it, written as an inert loan `loan_k` (the *hole*), and the caller's eventual [End] of `borrow_k` supplies it by substitution.

The principles a sealed program must keep for (C) to hold:

- **(C1) Reconstruction.** The text rebuilds the call exactly: the same function value (code and captures), the other arguments as the values they were at the call point, each borrowed content in a fresh cell, in the same order. Nothing else of the call point reaches the callee: functions capture values, not places; there are no borrows in data; globals do not change. So the sealed program is a closed text whose run depends only on what it embeds (and on the facts of the world it is run in: refinements, generalisation records).
- **(C2) Projections.** Each output is its own sealed program: the result, and for each borrowed place its final content. The last read copies (`peek`), because the run's cells are discarded with the run: it is an observation of the run's state, not a move out of the caller's.
- **(C3) Holes are parameters.** A returned borrow's final content is a parameter of every fill, since at the generic call it is not decided which borrowed place the returned borrow points into (`Pick`). The run of a fill never inspects the hole: an inert loan is stuck at a match and passes through reads and writes unchanged. Filling it is substitution, which then re-runs the fills.
- **(C4) Re-run exactly when an input changes, wherever it occurs.** A sealed program is re-run when something it depends on changes: a value it embeds is substituted (a refinement, or the fill of a loan: `substV`), or a neutral its run derives is refined (a generalisation: `renormAll`). Both must reach every position a sealed program can occupy: Ω, stored types, the types of abstract values, the goal (**S-all**).
- **(C5) No re-closing.** On a re-run the head call is not closed off again ([Seal]'s head guard, neutral-headed calls included, D39), so a sealed program either makes progress or stays exactly as it is. Without it a re-run would produce a new text, and new holes, for the same delayed call.
- **(C6) One text, one value.** In a world, a sealed program's text determines its value (C1, determinism), so two derivations of one text may be identified: a generalisation record maps the text to its `σ` (`canonNeutral`), for the world that made it (`split-model`'s (G)).
- **(C7) Errors surface.** A re-run that errors is a type error at the point that triggered it ([Seal-err]); running out of fuel is undecided.
- **(C8) Clean inputs.** The inputs are loan-free and whole when the text is made. A live loan copied into a text would outlive a borrow ending differently later; a `⊥` would be read by the callee. [Access] and `wholeBorrowArgs` guarantee both; `closeCall` asserts the first.
- **(C9) η at `Unit`.** A `Unit`-typed output is `()`, its only value: a borrowed place holding `()`, a result whose type is `Unit`.
- **(C10) Blocks are calls.** A stuck match or `J` is closed off as a call of an anonymous function of its captures (`closeBlock`, D76), so C1–C9 apply with the captures as arguments; `erasure-model`'s K1 makes each capture's mode at least what any arm does.

## 2. What lemma (C) says, and what it reduces to

**(C).** Let a call close off at Ω, leaving Ω′ (its fills in the lent places) and its result `r`. For a refinement α under which the direct call `f(w̄α)` at `Ωα` runs to completion, leaving `Ω″` and `v`: once the hole is supplied by the caller's [End] and every borrow is ended, `Ω′α` (re-normalised) agrees with `Ω″`, and `rα` with `v`, up to renaming of loans.

It reduces to:

1. **(C1), by construction.** `closeCall` builds the text of the call itself, so re-running it under α *is* running the call at the arguments refined by α, in isolation.
2. **The frame property** (the paper's property 2 and Assumption 11 (T2)): a call affects only what it is passed, and its effect in context is its isolated run plugged back into the caller's places. This turns "the isolated run of the text" into "the call in context at Ωα". It is an invariant of the machine, stated in the paper and not yet proved for the current rules (the earlier rule set's `frame_local`/`call_effect` were deleted with `meta-lean`).
3. **(P) applied to the hole** (C3): the fills' runs never inspect `loan_k`, so supplying it afterwards equals running with it. This is the same parametricity as (P), with the hole as the unknown; on the heap design (`notes/stability.md` §8) it is `exec_agree` with the hole's handle in `D`.
4. **Bookkeeping, by construction in the checker:** C4 (every occurrence is re-run, now through one `mapState`), C5 (the head guard), C6 (`canonNeutral` on every sealed output), C8 (asserted).

So (C) adds no new kind of argument beyond (P) and the frame property: what it needs beyond them is that the checker's bookkeeping is complete, which is now structural. On the heap design closing off would allocate thunk nodes over the call's input handles; re-normalisation would be forcing a thunk after its unknowns' nodes are filled, so (C)'s first and last parts become definitional and what remains is the frame property, itself an instance of `exec_agree` over the handles a call cannot reach. A Lean proof for the heap slice was not attempted here: the slice (`Ochr/Heap/Slice.lean`) stops at a stuck call rather than closing it off, so it first needs a thunk node and a call rule that allocates one; the argument above is the plan.

## 3. Derived rules against the current ones

| Principle | Current rule (code) | Verdict |
|---|---|---|
| C1 reconstruction | `closeCall`: `L := let cᵢ = uᵢ`, `C := f(ā)ʰ` with `aᵢ = &cᵢ` or the value | holds; `closeCall` is the only place a sealed program is made (a block or `J` goes through it via `closeBlock`) |
| C2 projections, last read copies | `peek` (`withCopying`, D53) in each fill and the borrow row's result | holds |
| C3 holes are parameters | the borrow row puts `loan_k` in every fill; inert loans are stuck at matches (`Match-stuck`), copied by reads | holds; reading a place whose fill holds a live hole ends the borrow first (D29, `accessNeutralHead`), so a split never sees a live hole |
| C4 re-run at every position | `substV` → `nfSealed` on substitution; `renormAll` after a generalised neutral is refined | **gap, now closed:** `renormAll` reached Ω, the goal and stored types but not the types of abstract values, which `substEnv` reached. Both now go through `Env.mapState`, which visits one fixed list of positions. No verdict changed |
| C4, fills and [End] skip types | `substEnv … false` for a loan's fill and for [End] | holds: a type is formed on a private copy, where reading a place ends every loan inside it, so types hold no live loan |
| C5 no re-closing | [App-head], [App-neutral-head]; `callFn`'s `head` flag | holds |
| C6 one text, one value | `canonNeutral` on every sealed output (`closeCall`'s four, `nfSealed`'s stuck case, `renormV`) | holds |
| C7 errors surface | `nfSealed` rethrows errors and exhaustion | holds |
| C8 clean inputs | `wholeBorrowArgs`; the INTERNAL assertion on live loans | holds |
| C9 η at `Unit` | `closeCall`'s `u == .unit` fill and `resultIsUnit` (two-paths site 9) | holds |
| C10 blocks are calls | `closeBlock` → `closeCall` over `blockCaptures` | holds |

No checker rule turned out to be unneeded by the model.

## 4. Probes

Each probe below was run with its verdicts printed explicitly, beside a control that must be rejected, and is now a registered regression block (`CloseOffModel` in `ClosingOff.lean`): every true statement is accepted and every false twin rejected.

| Shape | True statement (accepted) | False twin (rejected) |
|---|---|---|
| hole in two fills (`Pick`), split | `CoPick` | `CoPickOnlyA`, `CoPickBoth`, `CoPickRefl` |
| two writes through a returned borrow | `CoTwice` | `CoTwiceFirst` |
| a reborrow through the returned borrow passed to a stuck call (a borrow argument holding a sealed program) | `CoReborrow` | `CoReborrowOff` |
| the returned borrow moved into a second call | `CoMoved` | `CoMovedOff` |
| a re-run meets the hole as an inert loan, a later [End] fills it | `CoInert` | `CoInertOff` |
| the write before the split, refined twice | `CoWrittenFirst` | `CoWrittenFirstOff` |
| the returned borrow written differently per arm | `CoPerArm` | `CoPerArmOff` |
| a closed-off call generalised by a split and derived again | `CoGen` | `CoGenOff` |
| the same, refined twice | `CoGenTwice` | `CoGenTwiceOff` |
| a stuck block whose arms close off calls on a borrowed place | `CoBlockCalls` | `CoBlockCallsOff` |
| a stuck block that returns a borrow (`Pick` in each arm) | `CoBlockBorrow` | `CoBlockBorrowOff` |

## 5. What landed

- **`Env.mapState`**: one function visits every value position of the state in one order (each value of Ω and its binding's type, then the types of abstract values, then the goal). `substEnv` (refinement with types; a loan's fill and [End] without) and `renormAll` both go through it, so a sealed program cannot be left stale in one because a position was missed in the other. This closed the gap above; the full `lake build` was green before and after with every verdict unchanged.
- **Docstrings** of `closeCall` (the only maker of sealed programs: C1, C2, C3, C5, C6, C8) and `nfSealed` (the only re-runner: C4).
- **The paper's `#lean` pointers** for the declared-type readers that moved to `Decide.lean` (D74, D77) now name it: `ctorIsProof`, `fnClass`, `paramFlags`, `preFlags`, `declOf`, `declKind`, `kindOf`, `byTypeMatch`, `sortOf`, `sealedSort?`, `isPropV`, `typePos`, `typeDecl`, `typeClass`, `jErased`, `largeElim`, `fieldTermIsProp`; `isDataType`, deleted with the switches, is replaced by `evalCore (.ref)` where it stood alone. The rule guard's two stale expected issues (`propDecl`, `jValue`) are removed; it now lists no pointer issue. The issues it still lists predate this branch and are not pointers: `[T-J-stuck]` has no `Rule` constructor, and its reference scan reads the paper's theorem headings (`[Theorem]`, `[Lemma]`, …) and `[Open]`/`[Repack]` as rule names.

## 6. Proposals (not implemented)

- **A thunk in the heap slice.** Give `Ochr/Heap/Slice.lean` a thunk node and a call rule that allocates one when the call is stuck; then prove, for the slice, that forcing a thunk after its unknowns are filled equals running the call (definitional) and that supplying a hole afterwards equals running with it (`exec_agree`). That would make (C) for the slice a corollary, leaving only the frame property.
- **State the frame property against the current checker**, in `Ochr/Stability.lean` beside `Conjecture2`: (C) now rests on it, as Theorem 19 already does (Assumption 11, T2).
- **A `Rule` constructor for [T-J-stuck]**, and teach the rule guard's reference scan to skip the paper's theorem headings, so its remaining warnings are real.

## 7. Open

As in every model lane, the argument rests on (P), here for holes as well as for abstract values, and now explicitly on the frame property. Both are named, neither is proved for the current rules.
