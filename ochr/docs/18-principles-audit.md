# Audit of `ochr/docs/18-principles.typ` (theory8's consolidation), by referee7

Working material for the next author, not for the owner. Audited: `main` at eacdc6597 (theory8's 03524347b and 00e3324c7, and the orchestrator's eacdc6597), against the version it replaced (863b5bc27), the reports in the scratchpad (`theory8.md`, the tops of `checker13.md`, `checker14.md`, `exists12.md`, `lead37.md`, `referee6.md`), the plan's status table, docs/31 on `origin/spine`, and the Lean on `origin/spine` at 73f1a1075 (built; every theorem named below had `#print axioms` run on it). Programs were run on main's checker (sources identical to 217e22529's) with `lake env lean --load-dynlib=.lake/build/lib/libochr_Ochr.so`; files in the scratchpad's `r7/ev/`.

## Verdict

The owner can rely on the rewrite for the design decisions and the evidence, and on most of its account of the proof, with four corrections. Nothing the referees found is silently gone: every objection of the six reports is folded in, marked standing, or superseded by a later ruling, and the few programs and sentences dropped are minor. Every one of the 475 verdicts in the document's program blocks, and 52 more programs it cites from the old reports, is as written on today's checker, with the quoted messages. The numbers in the decisions match their sources but one (a cost range). What is wrong is the account of the Lean, in both directions, because the document was written from docs/31 up to D234 but missed D221 to D231, which landed on `spine` on 27 November, hours before the rewrite:

1. **Too strong (corrected in the document):** "conversion sound for values without code" is listed as proved in Lean's kernel. It is on the unmerged branch `rules-trial` only, against the model before its type formers were strict, and `conv_sound_T`/`mkEqM_sound_T` assume, besides the typing hypothesis and the two data-layer facts the document names, the function rules' premises (`PremSoundT`, needed even for first-order values), `GenericKept`/`EqKept`, `CodeOk`, `FieldTysSound` and `FieldTyIdx`.
2. **Too weak (corrected):** the frame property is proved in Lean (`runFrameI_frameFree`, standard axioms, docs/31 D225) for every term with no function, function type or `Id` formed in it, which is everything but its three standing clauses; and its first use, the call in place C1, is proved for such a global's body from three stated facts (`callInPlace_of`, D230). The document still says the clauses with labels are argued on paper and FR is open in Lean as a whole.
3. **Stale (table only; needs rewriting):** the proof-field repair. D229 (built on `spine`) makes the model skip a match on a proof of a non-subsingleton, as the checker's untyped run does; D231 checked V2 against it and found the model needs nothing more, and rejected the repair this document proposes (running the rewritten arm in the model's `.matchInd`: `runT` is structural and the rewritten arm is not a subterm). So the standing objection at `<sec-proof-fields>` ("until the model mirrors the locals, the simulation has no reference run for `PB`, `PExT`, `PExF`") is false today; what is owed is the [T-Match-prop] step of (II) and the alignment of `Decisions.subsingleton`. The theorem's list of model changes, case 2, case 7 and §1's "four model changes ... not built" all carry the stale form.
4. **Presented as settled, and misattributed (table only):** `<sec-n1>` says which model N1 states was "settled in this pass, as the sixth referee and `exists12` recommend". The sixth referee recommended neither: it gave two options and wrote that the choice "is the user's". It belongs in `<sec-decide>`.

Counts of findings, each counted once though several appear in two checks: ok, 94 rows; status too strong 1 (N3 for values); status too weak 3 (FR in Lean, C1 in Lean, N9's `run_hintIndep`); number wrong 1 (decision (a)'s cost), and 1 number with no source found (decision (b)'s "about twenty files"); missing 5 (`fig-n1-checks`'s sort row; docs/31's items 30, 34, 35; `hwt_of_fit`'s exclusion); weakened 2 (the [Call-type] route of the observation's fault; the private runs' `privateDepth` detail); misstated 7 (the proof-field repair; FR "hypothesis for hypothesis" since D222; N1's statement "settled" and misattributed; `Leak`'s first sentence; §1's "four model changes"; §1's `G1` wording; (H12)'s stated reason). All five checks were done; check 4 was done in full (every block), not on a sample.

## Corrections made in the document (each its own commit, with the evidence)

| Commit | What changed |
|---|---|
| 38613a508 decision (a)'s cost range | "−0.01% to 0.0%" → "−0.07% to 0.0%" (checker13: Quicksort −0.01%, HashMapTests −0.07%, Arrays 0.0%) |
| 3ed24bf90 N3 for values: on a branch, under named premises | §1 moves it out of "Proved in Lean's kernel" into a conditional; `fig-named`'s N3 row and `<sec-n3>`'s first paragraph list the premises `conv_sound_T`/`mkEqM_sound_T` take and say the branch is unmerged and against the pre-strict model |
| 80a1e7f96 the frame property in Lean | §1, `fig-named`'s N4 row, the FR statement's status, and "not proved, in words" now say FR is proved for frame-free terms (`runFrameI_frameFree`, D225) and C1 for frame-free global bodies from three facts (`callInPlace_of`, D230); FR's "hypothesis for hypothesis" qualified (FrameInv gained four clauses, D222) |
| 688aee9ca N9 and `hwt_of_fit` | N9's "Lean's `HintIndep` stated" → `run_hintIndep` proved for terms whose tails read no hint; `hwt_of_fit`'s exclusion (constructor values of `Prop`-sorted declarations) added where it is cited |

Not changed, because each needs judgement or rewriting: the proof-field section and everything that cites the proof-field locals (finding 3 above); the clause-by-clause statuses inside FR's proof paragraph and its hypothesis table (several clauses marked argued on paper are proved in Lean; see check 2); the N1 statement choice (finding 4).

## Check 1: nothing lost

Old locations are labels of 863b5bc27; new ones of the current file.

| Item | Old | New | Finding |
|---|---|---|---|
| O1 principles are the proof's open theorems | `<sec-referee>` O1 | principles intro, `fig-named`, `<sec-statement>` | ok |
| O2 the claim does not survive an end | O2 | `<sec-halves>` "why the relation survives" | ok |
| O3 membership on the checker's side | O3 | `<sec-halves>` "what is not in (II)" | ok |
| O4 D135's gap used | O4 | `<sec-dec-landed>`, case 1, `<sec-ev-rec>` | ok (`Sel`, `Q3`, `Loop`, `LC2` re-run rejected; `Q2` re-run rejected) |
| O5 (a) a second maker of sealed values | O5 | principle 7 `#stand` | ok, standing |
| O5 (b) typing hypothesis | O5 | `<sec-n3>` | ok |
| O6 frame property never stated | O6 | `<sec-frame>` | ok |
| O7 two producers of returned borrows | O7 | case 2; `QB` in evidence | ok (`QB2` re-run: rejected) |
| O8 local recursion | O8 | D136, `<sec-induction>` | ok, superseded |
| O9 captures read values | O9 | N6 `#stand` | ok, standing |
| O10 open members undefined | O10 | `<sec-halves>` "Good" | ok |
| Items 1 to 14 | `<sec-referee>` table | as theory8's checklist says | ok |
| Referee 1's probes through `TailM` (`PF(TailM(x), refl)` and three variants) | "For a second referee" | not shown; `AFill` covers the shape | ok |
| R1 `G1`, the model reads a borrow parameter with no cell | R1 | (M1), `G1`, `CallG1` | ok; `G2` (the [Obs-ref] variant) dropped, minor |
| R2 a closure formed in the body | R2 | (M2), `#stand` at `<sec-frame-stmt>` | ok, standing; note D226: under the structural frame the `.fix`/`.pi` clauses need only (O2), site faithfulness is C3's |
| R3 four unstated shapes; RL unnamed | R3 | N8, N9, RL, C1 to C6 | ok |
| R4 (P) false | R4 | invariant (I); `P2` | ok |
| R5 (T) and [End] misstated | R5 | (O1), (O3) | ok |
| R6 `Id` exclusion needs a hypothesis | R6 | `<sec-idclause>` | ok |
| R7 fixpoint equation at one state / locals | R7 | `<sec-frame-fix>`; D136 | ok |
| R8 (II) lacks hypotheses | R8 | (E5) to (E9), (C5) to (C7) | ok |
| R9 smaller | R9 | FR's statement | ok |
| T1 (M3) false; observation's type-safety fault | T1 | (M3) restricted; decision (a); `CallI` | ok for the model; **weakened** for the checker: T1 measured two routes, a body run in place and [Call-type] reading a callee's parameter type at the call site (`CallH`; the fourth referee's `CallF`); the document shows and counts only the first (§1 item 1, principle 6). Both routes are repaired by (C)/(C+) (checker13 lists `CallF`, `CallFZ` among the twins). Add the [Call-type] route to §1's item 1 and principle 6's audit. Re-run: `CallH`, `CallF`, `UseK` rejected, `UseKS` accepted. |
| T2 (M2)'s `.pi` | T2 | (M2); `PiMove`, `PiLentEq`, `FixMove` | ok |
| T3 C3 a lemma | T3 | `#stand` | ok, standing |
| T4 C2 at a call point only | T4 | `#stand` | ok, standing |
| T5 C6 is FR's | T5 | (C6) | ok |
| T6 D208 misattributed | T6 | (H8) row | ok, recorded as refuted |
| T7 smaller | T7 | `P5`, N8 hypothesis, case 2, (O6) | ok |
| F1 the patch needs a restriction (`Bad`) | F1 | decision (a) (B); CV3 | ok (`Bad` re-run: rejected today; `BadW` accepted) |
| F1's last bullet: under (B) `idType`'s [Repack] skips the cells (redundant) | F1 | — | dropped, minor, ok |
| F2 proof owner finer than the model | F2 | `<sec-proof-fields>` `#stand` | **misstated (stale)**: D229 (built on `spine`, 12e6f47cf) and D231 resolve the model's side differently; see the verdict's finding 3 |
| F3 FR is not `RunFrameI` | F3 | `<sec-frame-stmt>` | ok as of D220; **misstated (stale)** since D222: `FrameInv` gained `psites`, `heldAll`, `orderAll`, `monoAll`, and D222's model change (a match's join lends its result label only when live) changes the stated reason for (H12) |
| F4 RD stated too widely | F4 | RD (a), (b); N5's disjoint-path sentence; item 11 | ok |
| F5 a side opens a caller owner | F5 | N7 sites; `S5` | ok (`AH8` re-run rejected, `AW8` accepted) |
| F6 (X1) at deferred types | F6 | (X1)'s exception | ok |
| F7 smaller | F7 | P4 shift, CloFix order, N6 `#stand`, `FsHs` | ok |
| V1 (C+) finer; missed verdict changes | V1 | decision (a), measured | ok; `ConsP` dropped (minor); `ConsM`, `IdxDiff` cited and re-run (accepted, rejected) |
| V2 checker binds locals | V2 | D138, `<sec-proof-fields>` | ok for the checker; the model's repair **misstated** (as F2) |
| V3 DL over two label lists | V3 | `#stand` | ok, standing |
| V4 assertion at the detach | V4 | `#stand` | ok, standing |
| V5 smaller | V5 | DL text, principle 7, `InFrameMoved`, `SwapCall2` | ok |
| V5's implementer's notes (detach before the footprint, footprint in the detached state, identity fills only, a cell's type for a temporary, [Conv-fun] untouched, dump the suite) | `<sec-referee5>` verdict | "checker13's decisions 2, 5, 6" | ok (built and measured since) |
| Y1 the paper's model is not the Lean's | Y1 | `<sec-n1>` "Which statement" | **misstated**: "settled ... as the sixth referee and `exists12` recommend"; the referee recommended neither and left the choice to the user. Move to `<sec-decide>` as a decision, with `exists12`'s recommendation (codes) attributed to it alone |
| Y2 checks filed under the wrong step | Y2 | `fig-n1-checks`, decision (d) | ok; **missing** one row: the declaration's own sort `Prop` or `Type₀` (`d.sort > 1`), "not needed for existence; serves borrows and the rules that assume data is in `Type₀`" (Y2's table, row 2) |
| Y3 hard-case Lean plan | Y3 | `<sec-n1>` | ok, resolved |
| Y4 standing assumption | Y4 | `<sec-n1>` | ok |
| Y5 smaller (S0, S6, two meanings, §6.2.1, `VL`, `DPB`, [Rec] `Type₀`, [Conv-cong]) | Y5 | N1 corrections, beyond-Lean list, `fig-n1-checks`, N3t | ok |
| Y5 `Leak` | Y5 | `<sec-proof-fields>` | **misstated in one sentence**: "everything the checker accepts about σ holds for every value of it" is false of `q`'s own type, `Eq(Bool, σ, true)`; the settlement rests on the next sentence (the assignment extended at the witness's field for the rest of the run). Drop the first sentence or restrict it to facts that do not mention the arm's proof fields |
| theory1: ledger, residue | `<sec-ledger>`, `<sec-residue>` | appendix | ok (re-counted: 139 rows, 10 design/feature, 67 fit an earlier principle, 62 none) |
| theory1: predictions (`Loop`, `Sel`, `LC2`, `DeadIll`, `DeadMoves`, `W2`, `T5`) | audits | principles 4, 3, 5; evidence | ok |
| theory2: census site 7 (`PT`, `L`, `L2`, D77) | `<sec-arg-found>` | principle 3 | ok |
| theory2: six further private-run sites | `<sec-a6>` | principle 6 | ok; **weakened**: dropped that these sites do not raise `privateDepth` (so `endTopLoan`'s (L4) assertion stays armed in them) and that three restore on success or stuck only, not on error. Harmless by its own argument, but it is the detail V4 turns on |
| theory2: `hintLater` | `<sec-a6>` | principle 7 `#stand` | ok |
| theory2: principle 2's open audit (each identification preserved by refinement) | `<sec-a2>` | principle 2 | ok (the old text itself reframed it as not needed) |
| theory3: (II), cases, D135 re-runs | `<sec-twohalves>` | §4, evidence | ok |
| theory4: `P4`, `run_frame_obs` false | `<sec-frame>` | (H8) row, `<sec-idclause>` | ok |
| theory5: RD and its attack | `<sec-rd>` | `<sec-rd>`, `<sec-ev-obs>` | ok (attack summarised with every program name) |
| theory5: the `Unit` fill mismatch | `<sec-rd>` | D137 | ok |
| theory5: `T0` | `<sec-next>` | principle 4, `Fst0Gen` | ok |
| theory6: five sites, (C)/(C+), DL, findings 1 to 4 | `<sec-obs>` | decision (a), `<sec-idclause>`, evidence | ok; `LiftC` dropped (`LiftR` carries it) |
| theory7: N1, 193 attacks, `VF`, `B10`, (B2) | `<sec-n1>`, `<sec-n1-attack>`, `<sec-a1>` | `<sec-n1>`, evidence, principle 1 | ok |
| lead37 items 36 to 41 | (not in the old document) | decision (b), `<sec-induction>`, `#stand` 39, `<sec-frame-fix>` | ok |
| docs/31 "for the theory" items 30, 34, 35 (D227, D230) | (not in the old document; on `spine` before the rewrite) | — | **missing** (item 31, the paper's [T-Match-prop] form, is already corrected in the paper's appendix): 30 (no use of `RunFrameI` needs the `Id` clause with parameter labels), 34 (C4 is "by definition" only if the run in place reads the callee's types at the closure's forming state; the model read them on the caller's state, a model fault found and repaired in D230: add to §1's faults in the model), 35 (the pop's conclusion is a transfer of the relation, not the same state; `<sec-frame-fix>` says "after the ends (F4) reads the caller at the cells' finals, which is `callOf`'s fixes") |
| The old "what is next" lists | `<sec-next>` | none | ok by design; their content is folded into decisions and statuses |

## Check 2: the one page and every status

"Lean" means `origin/spine` at 73f1a1075, built, `#print axioms` run: "standard" is `propext`, `Classical.choice`, `Quot.sound` with no `sorryAx`.

| Claim | Where | Lean name and statement read | Finding |
|---|---|---|---|
| (I) N2 proved | §1, N2 | `Strict.fund_all`: standard; hypotheses `FundCtx` (the data layer's read lemma, globals' membership, no data declaration at `Type₁`) and `valsOk`; `Witness.fundCtx_Kw` an instance | ok |
| N1 on codes, from five facts | §1, N1 | `Assembly.exists_dataModel` (namespace `Ochr.Meaning.Assembly`, `Consistency.lean`): standard; assumes `ResolvesTo` and `DataFacts` = `NamesFact`, `VaryValFact`, `FieldHeads`, `DecCaps`, `DecStable` (docstring); `itemFacts`, `globalCallLevels` standard | ok |
| N3 for values proved in the kernel | §1, `fig-named`, `<sec-n3>` | not on `spine`; `rules-trial` (ea3fbb37) `Rules.ComposeT.conv_sound_T` assumes `GenericKept`, `PremSoundT` (the function rules' premises), `UnitOk`, `CodeOk`, `HWT`; `mkEqM_sound_T` assumes `EqKept` and `AHyps` (`PremSoundT`, `UnitOk`, `CodeOk`, `LibOkT`, `FieldTysSound`, `FieldTyIdx`); the plan: "stated against the model as it was before its type formers were strict" | **status too strong**; corrected |
| The frame property: operation lemmas, a match and a call's fixes in Lean; FR open | §1, `fig-named` N4, `<sec-frame-stmt>`, FR proof paragraph, "not proved, in words" | `termFrame_all`, `runFrameI_frameFree`: standard, FR (`FrameAgreeI`) for every `t.frameFree` (no `.fix`, `.pi`, `.id`) from `FundCtx`, `FrameStart`, `valsOk` (D225, 27 Nov 20:03); clause lemmas `runFrameI_place`, `_borrow`, `_assign`, `_letIn`, `_seq`, `_J`, `_ctor`, `_call` (head, arguments, data or borrow result, D221), `_matchNat`, `_matchInd`: all standard; (O6) proved (D223) | **status too weak**; §1, `fig-named`, FR's status and "not proved" corrected; the clause list inside FR's proof paragraph and the operation lemmas' marks ((O6), (O9), "with labels ... #a-full", "its borrow result, head and arguments #a-full") left for the next author |
| C1 #a-red[FR, FixEq]; case 1 "Lean: the call point stated" | `<sec-frame-fix>`, case 1, `fig-cases` | `CallInPlace.callInPlace_of` (C1 for a global with a frame-free body), `body_agree`, `frameStart_inStart`: standard; `callInPlace_of` assumes `CallStartG` (its `FrameStart` half proved), `CallPopG`, `FixEqG` (D230) | **status too weak**; §1 corrected; case 1 and `fig-cases` left |
| FR "hypothesis for hypothesis" `RunFrameI` | `<sec-frame-stmt>` | `FrameInv` gained `psites`, `heldAll`, `orderAll`, `monoAll` (D222) | **misstated (stale)**; qualified in the statement; the hypothesis table not updated |
| (II) for a fragment | §1 | `Steps.Machine.frag_run_free`: standard, no fact assumed | ok |
| (II) for four single definitions under a few facts | §1 | `column_I_def` (3 facts), `column_J_def` (5), `column_P_def` (2), `column_R_def` (2) | ok |
| (II) assembled from 32 step statements | §1, `<sec-halves>` | `Form.Master.master`: standard, assumes `AllSteps` | ok |
| `Rel.start`, `sim_seq`, `Rel.private_copy` | `<sec-halves>` | standard | ok |
| `hwt_of_fit` | `<sec-concl>` | standard; hypothesis `NoProp K v` (no constructor value of a `Prop`-sorted declaration) | **missing assumes**; corrected |
| `endLabel_comm_state`, `perm_fold` | (I4) | standard | ok |
| `fixEqG_of` from `RecDescG`, `FnGoodG` | `<sec-frame-fix>` | standard, assumes both | ok |
| `frameJ2_holds` | the start | standard | ok |
| `run_counter_indep` open | RL | `sorryAx` | ok |
| N6 agreement across fuels | N6 | `Steps.Machine.decide_fuel_agree'`: standard | ok |
| N9 "Lean's `HintIndep` stated" | `fig-named` N9 | `run_hintIndep`, `runT_hintIndep`: standard, for terms with `tailHintFree` | **status too weak**; corrected |
| `MB0r` kernel-checked | decision (b) | `StageBlockCE` (lead37: standard; not re-printed here) | ok by lead37's report |
| §1 "Open: ... four model changes specified and not built" | §1 | (M2) widened, (M3) restricted, [Obs-ref] (D113) unbuilt; the proof-field change built in another form (D229); D222's join change built | **misstated (stale)**: three, and say D229 and D222 are built |
| §1 "Kernel-checked: the Lean items above, nothing else" | §1 | the N3 item is a branch result under premises | misstated; fixed by the N3 correction |
| "Argued on paper and refereed": the rest of N3 | §1 | CV: the fourth referee (holds; CV3, CV5, CV6 reduced); TC: the sixth (proved or reduced) | ok |
| N4 but three clauses | §1 | the second to fifth referees, clause by clause | ok |
| N5 | §1 | the fourth referee: (WF11), (WF12), RD2 hold, (X1) false as stated and folded; no referee read every clause's argument | ok, partial: say which clauses a referee read |
| N6, N7, N8, N9 | §1 | the fourth referee: holds by reading / holds; N9 the third "could not decide", the fourth "holds by reading" | ok |
| The nine cases of (II) | §1 | the first and second referees refereed the earlier argument's cases; the nine cases in this form were assembled by theory3/5 and read by the second and third | ok, loosely |
| "One author only: ... the case for blocks as text (measured, not refereed)" | §1 | checker14 measured it; no referee | ok |
| N2 "applied to seven concrete runs" | N2 | the plan's status table | ok |

## Check 3: the decisions

| Item | Source | Finding |
|---|---|---|
| (a) branch `exp-obs-detach` at 016d19439; `today` reproduces 5,475 rows | checker13 | ok |
| (a) (C): 13 rows, 4 accepted → rejected (`Inj`, `QOk`, `QFOk`, `BoomOk`), 9 messages, 0 rejected → accepted | checker13 | ok |
| (a) (C+): 15 rows, + `BadD18`, `DetourHide` messages | checker13 | ok |
| (a) five sites and twins accepted; every attack rejected | checker13 | ok |
| (a) newly rejected / newly accepted lists | checker13 "three kinds, all measured" | ok |
| (a) cost "−0.01% to 0.0% instructions" | checker13: −0.01% / −0.07% / 0.0% | **number wrong**; corrected to −0.07% to 0.0% |
| (a) size +138 / −12 in 4 files | checker13 | ok |
| (a) `Inj` quoted; the bridging needs `g` injective | checker13 item 1 | ok (re-run: `Inj`, `L` accepted) |
| (a) recommendation (C+) "theory6's" | old `<sec-obs>` "I recommend it, with one refinement ... (C+)" | ok |
| (a) "agreed by the fifth referee as sound for consistency with no restriction" | V's verdict | ok; that agreement was by reading, before (C+) was built |
| (a) the orchestrator's second view, (C) | eacdc6597 | ok |
| (a) "What each option removes" | old `<sec-obs-compare>`, V's table | ok |
| (b) branch `exp-block-text` at 600bcc5b5; 5,478 rows; 1 verdict (`ConvBlocks`); 8 messages; 659 proof-lane rows; four probes `EqJ`, `IdJ`, `DJ`, `SJ`; +206/−88; two proofs repaired | checker14 | ok |
| (b) "cost within 0.3%" | checker14: +0.27%, +0.23%, −0.44% | ok (the one beyond 0.3% is a saving) |
| (b) "sized at about twenty files" for the model's `.block` clause | none found: lead37 sized the closure-style clause at "~10 induction files + column Q"; checker14's trial stopped at `Run.lean` | **unsourced number**: give the source or say "not sized" |
| (b) recommendation (iii) "the orchestrator's, with lead37's analysis behind it" | lead37 recommended (alpha) with a closure-style clause, then found the fourth fault and named (gamma), blocks not closures (D234) | ok |
| (c) D135: `Sel`, `Q2`, `Loop`; fifteen programs written by the hunt | docs/32 | ok |
| (c) D136: five rows of `Examples/Recursion.lean`; three commits | docs/32 | ok |
| (c) D137, D138 as corrections of the documents | DECISIONS.md D137; RULES.md v2.1 history (D138) | ok |
| (d) nine declarations with least models | Y2 | ok (`D2`, `LD`, `NBD`, `B11`, `B12`, `B6`, `TBD`, `Q11`, `NT`) |
| (d) `exists12`'s two checks "not made, not measured" | exists12 | ok |
| (e) "None has been built or measured" | — | ok |
| N1's statement on codes "settled in this pass" | Y1 ("is the user's"), exists12 docs/34 §18.18 | **presented as decided that is only proposed**; belongs in `<sec-decide>` |
| `Leak`'s optional rule | theory8 | ok ("not built or measured") |

## Check 4: the evidence re-run

Done in full, not sampled: all 20 program blocks of the document were extracted verbatim and run as `ochr` blocks with `uses Nats` (`r7/extract.py`; `r7/ev/B00` to `B19`): **475 verdicts, 174 of them rejections, every one as written** (`Ctl` rejected in each block). The rejections' messages were collected by running the same blocks with `reject` removed (`r7/messages.txt`); every message the document quotes matches (among them `S1Z`, `S2Z`, `CallI`, `InFrameMoved`, `SwapCall2`, `PickEnds`, `ConvBlocks`, `Loop`, `AddZ`, `CapSplit`, `Shadow`, `qe`, `B1` to `B14`, `DH`, `DL`, `DA2`, `VF`, `U1` to `U10`, the D45 family, `NoRefute`, `R1` to `R4`, `T1` to `T5`, `tl`, `D2`, `LD`, `NBD`, `TBD`, `Q11`, `NT`, `EE`, `PT`, `EP`, `MoveTy`, `IdTy`, `NoTEq`, `RZ`, `Q7`, `Q9`, `T10`, the `Borrow…` family, `LShow`, `LRw`, `LPass`, `LTwo`, `TwiceH`, `GetN`). `q` and `acc` report "unknown constant", which is the document's "a definition does not name itself (D118)".

Programs the document cites but shows only in the old reports, run with the verdicts those reports give (D135 applied): `CallF`, `Bad`, `CallH`, `UseK`, `ARBn`, `AG6`, `AH8`, `ConsP`, `IdxDiff`, `QB2`, `Q2`, `LB` rejected; `BadW`, `FI`, `FJ`, `CallK`, `UseKS`, `RB`, `G6`, `AW8`, `ConsM`, `TwoW`, `LocalForm`, `EWhole`, `PExT`, `G7T`, `OwnForm`, `SwapForm2`, `PF`, `P2`, `P3`, `UseP2`, `G2`, `IdT`, `IdG` accepted (`r7/ev/OLD.lean`). No difference.

| Program | Verdict or message differs? |
|---|---|
| all of the above | none |

## Check 5: contradictions with itself, the paper or the Lean

| Item | Where | Finding |
|---|---|---|
| The proof-field repair against D229/D231 | `<sec-proof-fields>`, `#stand` F2/V2, `<sec-statement>`'s model changes, case 2, case 7, `fig-cases`, §1 "four model changes" | contradicts the Lean (verdict finding 3); **misstated** |
| "no pass found an accepted definition of an empty type" beside "an accepted definition with an empty type, `G1`" | §1 | reads as a contradiction; the second is the model's reading. Say "an accepted definition whose type the model read as empty" |
| (H12)'s "forced by" cites [Entry] lending a dead result label | FR's hypothesis table | D222 changed the model so the join lends the result label only when live; the reason is stale (the hypothesis stays in `FrameInv`) |
| "the pop: ... which is `callOf`'s fixes" | `<sec-frame-fix>` | Lean's pop (D230) concludes a transfer of the relation, not equal states (item 35) |
| C4 "by definition under (M1) and (M2)" | `<sec-frame-fix>` | true only once the run in place reads the callee's types at the closure's forming state, as the model does since D230 (item 34) |
| `Leak`: "everything the checker accepts about σ holds for every value of it" | `<sec-proof-fields>` | false of `q`'s type; see check 1 |
| §1 "Proved in Lean's kernel: ... conversion" against `<sec-n3>`'s "branch `rules-trial`" | §1, `<sec-n3>` | contradicted itself (one page said kernel, the section a branch); corrected |
| The paper | `core/paper` | nothing found that the document contradicts; the paper's [T-Match-prop] is already the rewritten-arm form (D138) |

## Not reached

Nothing of the five checks is left undone. Not attempted: re-deriving the arguments of N5 to N9 (the brief asks for statuses, not a new referee pass on them), and reading `rules-trial`'s proofs beyond their statements.
