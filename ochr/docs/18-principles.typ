// Why the Ochr checker is correct: the current theory, stated once.
// Where the theory stands; the design decisions awaiting the owner; the principles; the theorem
// and the named theorems it rests on, each with one current argument and its status; the
// evidence as tables of programs; the ledger of decisions by principle.
// Standalone: compile with
//   typst compile ochr/docs/18-principles.typ
// Notation macros are copied from the top of 18-consistency-proof-plan.typ (which copies the paper's).
// The passes that produced this document (seven authors, six referees, then an audit and a revision) are in git history.

#set document(title: [Why the Ochr checker is correct])

#let dark-mode = false
#let ink = if dark-mode { white } else { black }
#let muted-ink = if dark-mode { luma(170) } else { luma(80) }
#let code-bg = if dark-mode { rgb("#2a2a2e") } else { luma(246) }
#let expl-fill = if dark-mode { rgb("#1d2733") } else { rgb("#eef3f8") }
#let expl-rule = if dark-mode { rgb("#7fa3cc") } else { rgb("#5b7fa6") }
#let warn-fill = if dark-mode { rgb("#33201d") } else { rgb("#fbefe9") }
#let warn-rule = rgb("#c0604a")
#let dec-fill = if dark-mode { rgb("#2a2a1d") } else { rgb("#f7f4e4") }
#let dec-rule = rgb("#a8953c")
#let status-ink = black
#set text(font: "New Computer Modern", size: 10pt, fill: ink)
#set page(paper: "us-letter", margin: (x: 2.0cm, y: 2.2cm), fill: if dark-mode { rgb("#1e1e21") } else { white }, numbering: "1")
#set par(justify: true, leading: 0.62em, spacing: 0.9em)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => { v(0.8em); it; v(0.3em) }
#show raw: set text(font: "DejaVu Sans Mono", size: 8.4pt)
#show raw.where(block: true): it => block(width: 100%, inset: (x: 8pt, y: 6pt), fill: code-bg, radius: 2pt, it)
#show figure.where(kind: table): set block(breakable: true)
#set table(stroke: 0.4pt + luma(170), inset: 4pt)
#show table: set text(size: 8.6pt)
#show table: set par(justify: false)

// Notation (copied from 18-consistency-proof-plan.typ, which copies the paper's).
#let kw(s) = math.bold(math.upright(s))
#let ty(s) = math.sans(s)
#let seal(t) = $lr(⌈ #t ⌉)$
// A mark: the place lent to the returned borrow `l`, with content `v` (the paper's).
#let lent(l, v) = $"lent"_#l #v$
// The meaning of x in the set model; under an assignment `at` of the unknowns when given.
#let deno(x, at: none) = if at == none { $lr(⟦ #x ⟧)$ } else { $lr(⟦ #x ⟧)_(#at)$ }
// The reference run of t: the meaning of running t.
#let refrun(t) = $upright("Run") lr(( #t ))$
// Dereference of a place, as the paper writes it.
#let dr = $ast$
// The set a sort means in the set model (Carneiro's U).
#let univ(s) = $cal(U)_(#s)$
// The stage of the cumulative hierarchy at the i-th inaccessible.
#let vk(i) = $V_(kappa_(#i))$
// The data model's family for a declaration d.
#let fam(d) = $cal(M)_(#d)$
// The meaning of a field type b with the declared type's own occurrences read through the family x.
#let ftm(b, x) = $lr(⟦ #b ⟧)^(#x)$
// The stage operator of a data-sorted declaration d.
#let stageop(d) = $Phi_(#d)$
// The detached state of an observation at frame o.
#let detached(o) = $Omega^(#o)$

// A principle, numbered on its own counter.
#let pcount = counter("principle")
#let principle(name, body) = block(width: 100%, above: 1em, below: 0.6em, breakable: true, [
  #pcount.step()
  *Principle #context pcount.display() (#name).* _#body _
])
// Status tags.
#let tagc(c, s) = box(inset: (x: 3pt, y: 1.5pt), radius: 2pt, fill: c, text(size: 7.5pt, weight: "bold", fill: status-ink, s))
#let s-cons = tagc(rgb("#cfe8cf"), [by construction])
#let s-check = tagc(rgb("#e6dcf2"), [by a named check])
#let s-not = tagc(rgb("#f6cfcf"), [NOT ENFORCED])
#let a-full = tagc(rgb("#cfe8cf"), [argued in full here])
#let a-lean = tagc(rgb("#d4e4f4"), [proved in Lean])
#let a-red(x) = tagc(rgb("#fbe5c0"), [reduced to #x])
#let a-claim = tagc(rgb("#f2f2c4"), [claimed])
#let a-np = tagc(rgb("#f6cfcf"), [NOT proved])
#let standing = tagc(rgb("#f6cfcf"), [standing objection])
// A program that was run, with its measured verdict.
#let measured(body) = block(width: 100%, inset: 7pt, stroke: (left: 2pt + expl-rule), fill: expl-fill, above: 0.7em, below: 0.7em, breakable: true, [#set text(size: 9pt); #body])
// A decision awaiting the owner.
#let decision(body) = block(width: 100%, inset: 8pt, stroke: (left: 2pt + dec-rule), fill: dec-fill, above: 0.8em, below: 0.8em, breakable: true, [#set text(size: 9.4pt); #body])
// A standing objection, at the place it applies.
#let stand(who, body) = block(width: 100%, inset: 7pt, stroke: (left: 2pt + warn-rule), fill: warn-fill, above: 0.7em, below: 0.7em, breakable: true, [#set text(size: 9pt); #standing *(#who)* #body])

#align(center, text(size: 16pt, weight: "bold")[Why the Ochr checker is correct])
#align(center, text(size: 11pt)[The current theory: where it stands, the decisions it waits on, its principles, its named theorems and their arguments, and the programs that test them])
#v(0.3em)
#align(center, text(size: 9pt, fill: muted-ink)[Consolidated by `theory8` on 28 November 2026 from the passes of seven authors (`theory1` to `theory7`) and six adversarial referees (`referee1` to `referee6`), and the lanes' measurements (`checker13`, `checker14`, `exists12`, `lead37`); audited by `referee7` and revised by `theory9` the same day, its account of the Lean brought to the proof line `spine` at 73f1a1075. Every program shown was run on the checker of `main` (217e22529, whose checker sources are those of b3f6a3854 and of today's `main`) unless its block says otherwise.])
#v(0.6em)
#outline(depth: 2, indent: auto)
#pagebreak()

= Where the theory stands <sec-stand>

*What is claimed.* The checker is _consistent_ (no accepted definition without parameters has a type that evaluates to `False`) _if_ eight named theorems hold (@sec-theorem). Types mean sets; a _strict reference run_ gives each term a meaning and fails wherever a value would be put at a type it is not a member of; (I) a strict run that succeeds returns members; (II) every successful run of the checker makes the strict run succeed with the same meanings. So an accepted definition means a member of its type, and `False` has none.

*What is in Lean* (the proof line `spine` at 73f1a1075; standard axioms, no `sorry`). A theorem that assumes facts not yet established is listed with them, never as proved.
- _Proved, assuming nothing beyond its statement:_ (I), the fundamental lemma (N2, `fund_all`, its context instantiated); (II) for a fragment (numbers, variables, `let`, sequencing, borrows; `frag_run_free`); the frame property for every body forming no function, function type or `Id`, all of N4 but three clauses (`runFrameI_frameFree`, docs/31 D225); the reference run's half of N9 (`run_hintIndep`).
- _Proved from facts it assumes_ (each read true against today's code unless said; none derived): N1 for the Lean model on codes, programs writing no sort above `Type₁` (`exists_dataModel`), from five facts about the checker and its decisions (@sec-n1; three more it assumed are now proved); a call in place agreeing with the callee's meaning (C1), at a global whose body forms none of those three, from three facts: the start's relation, the pop, and the global's fixpoint equation (`callInPlace_of`, D230); that equation, for every accepted global, from two clauses, the descent clause and the knot's goodness (the definition's meaning built from stages is good; open), both waiting on decision (b) where a block calls the global (`fixEqG_of`, D234); (II) for four single definitions, from two to five facts each (two read true, the rest unread); (II) in general (`master`), from its 32 step statements, seven proved in general under named facts and 25 open (docs/31 D153).
- _On an unmerged branch, under named premises:_ conversion sound for values without code (N3; `rules-trial`, against the model before its type formers were strict, assuming the function rules' premises and facts of the data layer).

*Argued on paper and refereed:* the rest of N3, N4's three remaining clauses (a function or function type formed in the body, `Id`), N5 to N9 (N5 in part: no referee read every clause), and the nine cases of (II). *Open:* (II) in general; every assumed fact above; N5 to N9 in Lean; three model changes specified and not built ((M2) widened, (M3) restricted, the model's [Obs-ref]); and the model's reading of a stuck block (decision (b)).

*What the adversaries found.* Six referees and seven authors in alternation, then an audit; *no pass found an accepted definition of an empty type* (a closed proof of `False` among them), a declaration without a model, or a large elimination from a non-subsingleton. The faults were _in proofs_ (the first argument was a reduction; the frame property was stated and refuted six times; an invariant, resolved determination, a descent clause and a well-formedness clause were false as stated), _in the model_ (it read the type of an accepted definition, `G1`, as empty; two of three model changes were wrong; a proof's fields read at the error type, a dead label lent at a join, and the callee's types read on the caller's state, all repaired (D229, D222, D230; a proof's fields: @sec-proof-fields); a stuck block read as a function of every value, `NTr`, `MB0r`, open) and _in the documents_ (the paper's [Close] at a `Unit` place and its match on a proof, D137, D138; this document's account of the Lean, stale in both directions until this revision).

*Faults of the checker found, all of type safety or precision:*
+ An observation tests its caller's state, by two routes: a callee's body run in place (five accepted functions whose calls at a known argument are rejected, `S1Z` to `S5Z`; `CallI`, a callee with no borrow parameter), and a callee's parameter type read at the call site by [Call-type] (`CallH`; `CallF`, through a returned borrow). Standing: decision (a)'s detached observation repairs both.
+ A function under check ran its own body (`Loop` undecided; `Sel`'s verdict followed that run). Fixed: D135.
+ Two stuck blocks compared as functions reject a true statement (`ConvBlocks`). Standing: decision (b).
+ A dead arm is never checked, though its moves feed the join (`DeadIll`, `DeadMoves`); a term of type `⊤` reading as data runs its effects (`W2`), not a route to `False`. Both standing.
+ A deferred parameter type with an `Id` over an ended borrow is weaker than the checked one (by reading; no program known; closed under decision (a)'s (C), (C+)).
+ Incomplete, true programs rejected: a field access in an untyped run (`Fst0Gen`), an `Id` beside its frame's partly moved borrow (`InFrameMoved`), two declaration shapes (`VF`, `B10`), two stuck functions compared (`FsHs`), conjuncts in the caller's order (`SwapCall2`).

*How much to believe.* Kernel-checked: the Lean items above, under their listed facts. Refereed: every paper argument of @sec-theorem not marked otherwise; every verdict of @sec-evidence was re-run by the audit (but the twin `CallHW`, added since). One author only: the settlement of `Leak`, (II) as the mechanisation states it, and the case for blocks as text (measured on the checker's side, not refereed; the proof's side under way). No attack produced an accepted definition of an empty type; the proof has been wrong, and repaired, at least once in every part.

#pagebreak()

= The design decisions awaiting the owner <sec-decide>

Each is stated as a decision: the question, the options, what was measured, the recommendation and whose it is, and what would change in the paper. The programs named are in @sec-evidence with their verdicts; the shortest is quoted here.

== (a) What an `Id` observation ends and compares <sec-dec-obs>

#decision[
*The question.* `Id(A, t, u)` runs each side on a private copy, ends borrows, and compares what is left. Today (A) it ends _every_ borrow of the whole state, tests each end (D98: the content whole; [Repack] in a typed run), and compares the _owners_ of the places the sides write, wherever they are, the caller's frames included. So a callee's observation reads and tests its caller's state.

*The options.*
- (A) Today's checker.
- (B) The patch: still end every borrow, but test only those held in the observing frame or with a sealed fill among their sites (the fourth referee's restriction, without which an unchecked end puts a non-member into a fill inside a formed type: `Bad`), and [Repack] only owners in the observing frame. About twenty lines.
- (C) The _detached_ observation (the owner's proposal, specified by `theory6`): build, on the private copy, a state of two frames, a cell for each borrow the observing frame holds that is lent from below (or has no site at all), then the observing frame; nothing below exists. Compare the result, the frame's own places, and each such borrow by its _final_, what was last written through it, exactly as a function's own check compares its cells.
- (C+) As (C), but every borrow the frame holds gets a cell, an internal one through an identity fill `⌈loan⌉`; no loan is ever followed outward.

*What was measured* (`checker13`, branch `exp-obs-detach` at 016d19439, never merged; one switch, its `today` value reproducing `main`'s 5,475 rows exactly).
#table(columns: (24%, 38%, 38%), table.header([], [*(C)*], [*(C+)*]),
  [Suite and case studies], [13 rows change: 4 accepted → rejected (`ReturnedBorrows.Inj`, `QOk`, `QFOk`, and `BoomOk` which calls `QOk`), 9 messages only, 0 rejected → accepted], [15 rows: the same, and 2 more messages (`BadD18`, `DetourHide`)],
  [The five sites and their twins (among them the [Call-type] route, `CallF`, `CallFZ`)], [all accepted], [all accepted],
  [Every attack on `G5`, `Q`, `QU`, `PEx`, `ATag*`], [still rejected], [still rejected],
  [Newly rejected that a user would write], [`Inj`-style lemmas, not repairable; `Lift` (repairable by one `rewrite`: `LiftR`); `SwapCall2Ok`], [the same, and `ConsW`, `ConsM` (an `Id` over a local borrow whose lender a side later writes)],
  [Newly accepted], [the five sites, `Bad` (a function from `False`; `Bad(Z, refl)` rejected), `SwapCall2`, `OwnRF`], [the same, and `IdxSame`, `IdxDiff`, `OwnRxF`, `BothF`],
  [Cost], [−0.07% to 0.0% instructions], [the same],
  [Size], table.cell(colspan: 2)[+138 / −12 lines in 4 files, both variants behind one switch],
)
The shortest lost lemma, with `L (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e`:
```
def Inj (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, (let r = g(x); *r := 0), (let r = g(x); *r := 1))) : False := (let r = g(x); L(r, e))
```
Accepted today; rejected under (C) and (C+): the hypothesis compares `x`'s cell through `g`'s fill, the lemma's parameter type compares `r`'s own final, and bridging them needs `g`'s backward function injective, which nothing in Ochr proves.

*What each option removes from the proof, or adds.*
- (A) owes resolved determination at every call point (@sec-rd), with three exclusions (no proof owner, ancestors holding whole members, and the function under check covered by its sealed calls' decreasing arguments, the first referee's item 11), resolution injective (N5's (X5)) over the caller's state, N1's injectivity relation $R$ for every backward function, the frame property's separate `Id` clause (OBS) with order-independence over the caller's labels, (M3) restricted, and a gap for a deferred parameter type read late. Five type-safety faults stand.
- (B) owes all of (A)'s, plus resolved determination through ancestors holding moved or open contents, and N3 for open and moved caller owners; leaves `S4Z`.
- (C) removes resolved determination at call points, OBS, the order lemma over caller labels, (M3)'s restriction, the deferred-type gap; keeps resolved determination within one frame (for the block lemma's `Id` row, through a stuck call's fill: `BlkFill1`), with $R$ and (X5) there. Adds the detach lemma DL, which needs the frame property restated over two lists of labels (V3).
- (C+) removes all of that, and $R$ and (X5) altogether: no injectivity of a backward function is used anywhere; the rule that a function type returning a borrow takes one (D44) and the hole kept at a `Unit` place (D137) become choices about `'static` borrows, not conditions of soundness. Adds DL (with V3's restatement) and exceptions for identity fills in principle 7 and in N3 for code.

*The recommendation.* (C+), `theory6`'s, agreed by the fifth referee as sound for consistency with no restriction (by reading, before it was built), and by `theory8`, who consolidated this document: it makes the observation a function of its own frame, so principle 6 holds for observations by construction, a statement read at a call site is the function's own statement by construction, and the most delicate lemma of the argument goes. It is not free. The owner should accept, knowing them, three costs: `Inj`-style lemmas (a fact about an abstract borrow-returning function that is true only because the model makes its backward function injective) become unprovable; an induction hypothesis lifted through a stuck call's returned borrow needs a `rewrite`; and inside a body `Id` compares what was last written through each borrow of the frame, whether or not a continuation can still see it (`ConsW`), which changes what `Id` means. _A second view, the orchestrator's:_ (C), the variant that gives cells only to the borrows that come from below the frame. It repairs the same five faults, loses the same four suite rows and the same two repairable forms, and leaves `Id` inside a body meaning what it means today (two sides are equal when no continuation can tell them apart); what it costs the proof against (C+) is one lemma that stays, a one-frame remnant of resolved determination at a block. The difference between the two views is only the third cost above: whether the simpler proof is worth changing what `Id` means inside a body.

*What would change in the paper.* §5's definition of `Id` and the appendix's [Obs] (the places compared: the result, the frame's owned places, each borrow of the frame by its final); RULES §4; the frame property loses its `Id` exclusion; D44 and D137 are re-justified by what `Id` says, not by soundness. Before landing: a wider hunt aimed at the choices the implementation made where the specification was silent (`checker13`'s: under (C) a label lent from below with a site in the frame gets an identity fill; a cell's type for a temporary with no stored type; the detach's assertion and its message), and the deep sweeps, not run.
]

== (b) What a stuck block is <sec-dec-block>

#decision[
*The question.* A stuck match that is not the last thing in a body is closed off as a _block_. Today a block is an anonymous function of the places its arms use, applied to them: a closure value with a parameter list, a function type and a binding of itself.

*The options.* (i) Today's. (ii) The small repairs ruled as D139 (not landed: held until (iii)'s experiment reports, docs/32): the block names a function under check by its global, not as a parameter, and a block's re-run binds a placeholder for its own name. (iii) _Blocks as text_: a sealed block binds each captured value in a cell at the declared type and reading of the place it took, and then _is_ the match itself; a new term former made only by closing off, run only by a re-run; nothing in it is a function. For `NTr`: `⌈(fix _ (n : Nat) (m : Nat) : Nat := match m { Z => clone(n), S _ => clone(n.0) })(S(σ2), σ1)⌉` becomes `⌈let n = S(σ2); let m = σ1; match m { Z => clone(n), S _ => clone(n.0) }⌉`.

*What was measured* (`checker14`, branch `exp-block-text` at 600bcc5b5, never merged). Of 5,478 rows one verdict changes, rejected → accepted (`ConvBlocks`, a true statement the suite's own comment calls wrongly rejected), and eight messages change in how a block is printed; nothing goes from accepted to rejected, in the suite, the probes or the proof lane's 659 rows. Four more probes become accepted, all of one kind: two sealed blocks whose texts differ only in convertible embedded values are now convertible, compared by text as sealed calls already are (`EqJ`, `IdJ`, `DJ`, `SJ`); their false twins stay rejected. Code: +206, −88 lines; two proofs about the checker repaired with nothing left unproved; cost within 0.3%.

*The model today.* The model reads a sealed block as a closure value, an element of its function type. So (II) is false at two accepted definitions: at `NTr`, which has no recursion, and, under the stage contexts of a recursive definition's check, at `MB0r` (both below); nothing on `spine` repairs it. The repair ruled for today's representation, a model clause that reads a block by running its body at its arguments only, with a placeholder for its own name (D233's (alpha), with option (ii) in the checker), was built in part on a branch that does not build (`spine-lead37-blockwip`) and stopped at fault (4) below (D234).

*What it removes from the proof.* Four faults of the block as a function (`lead37`, docs/31 D232 to D234), three gone by construction and one by naming the global, by the checker lane's reading of the built branch (whether the proof agrees is the experiment below): (1) a block takes the function under check as a parameter at its declared type, where the meaning the proof gives the function while it is checked (its stage, a function good only below a bound) is not a member (`MB0r`, kernel-checked: the reference reads its leaf as an error where the direct run gives `0`); (2) the model reads a block as a closure over every value, which fails where the checker checked it only at its captured value (`NTr`: its arm reads `n.0`, which exists only at a successor); so "a closure value's meaning is a member of its type" (CloFix (b), @sec-frame-fix) is false for blocks; (3) a block's re-run binds the block as `self`, whose meaning is an error; (4) a block's closure and a program's closure being one kind of value makes a block-aware reading not invariant under substitution. Also gone: conversion observing two blocks as functions, and the typed run of a sealed block. The block lemma N8 becomes definitional for the model's reading. _Adds:_ a `.block` clause in the model's run and its case in every induction over the run; not sized. For comparison, the closure-style clause begun instead (D234) had five of those inductions repaired when it stopped, with about twenty files left to repair.

*The proof's side of (iii)*, under way: an experimental branch of the proof line built against `exp-block-text` (`lead38`, never to be merged without the owner), whose tasks are the model's `.block` clause with its case in every induction and the fundamental lemma, then each of the four faults checked as gone, gone under a named condition, or not gone. No result was reported when this was written.

*The recommendation.* (iii), the orchestrator's, with `lead37`'s analysis behind it; `theory8` agreed: the small repairs (ii) remove two of four faults and keep the representation that produced all four.

*What would change in the paper.* The appendix's [Block] and [App-close] (the block's head is a term, not a call; [Close]'s table unchanged, with the block's text for the call); [Conv-cong] for blocks; RULES §3 "Stuck blocks"; `notes/closeoff-model.md` C10.
]

== (c) Landed and awaiting acknowledgement: D135, D136, D137, D138 <sec-dec-landed>

#decision[
- *While a function is checked, a call of it closes off* (D135, on `main`). Before it, a typed recursive call ran the body under check in place, where calls no [Rec] test saw were run (`Loop` ended undecided instead of rejected) and a statement's verdict followed what that run computed (`Sel` accepted, `Q2` rejected, differing only in what the `Z` arm returns). _Cost to a user:_ a definition whose own body needs its own recursive call to compute, `Sel`, is rejected; the same equation stated after the definition holds (`SelAfter`). Nothing in the suite did this; the landing's hunt wrote fifteen such programs. _Removes:_ every claim about runs of unchecked code; the outer induction never needs the function's meaning above its stage.
- *A local function is not recursive* (D136, on `main`; three commits to be reverted together or not at all). _Cost:_ a recursive helper can no longer close over its surroundings; it is written at the top level with what it used as parameters (`AddZ` is rejected; `AddZH` and `AddZ2` are its lifted form), and one that calls the enclosing definition back takes that call as a function argument. Five rows of `Examples/Recursion.lean` changed; no case study. Lean's kernel has no local recursion either (`let rec` and `where` are lifted by the elaborator), and Ochr can get the feature back the same way, as surface sugar. _Removes:_ the closed proof of `False` of October (`CapSplit`), the recognition of a function by its code, the nested induction for local recursion, and the descent argument for a recursive closure (CloDesc): a closure's fixpoint equation becomes immediate (@sec-frame-fix).
- *A `Unit` place's fill keeps its hole in [Close]'s borrow row* (D137): the checker always did; the paper and RULES said otherwise, and under their rule `QU` would refute a type safe Rust inhabits. A correction of the documents.
- *A match on a proof binds its data fields as locals of the arm* (D138): the checker always did; the paper said they were written at the scrutinee, under which `Nest` would be rejected. A correction of the documents. The model's side is settled differently from what this document first proposed: the model does not run such a match at all, and the simulation's step there runs the reference on the checker's rewritten arm, the fields given a witness's values as locals (docs/31 D229, D231; @sec-proof-fields).
]

== (d) Checks on declarations stricter than a model needs <sec-dec-decl>

#decision[
*The question.* The sixth referee's Y2: nine declarations rejected today each have a least model by the paper's construction. Should the checks that reject them stay, and on what grounds?

#table(columns: (16%, 30%, 27%, 27%), table.header([*Program*], [*Rejected by*], [*The model it has*], [*What the check serves*]),
  [`D2`, `LD`, `NBD`], [D120: a variable mentions what its declared type mentions], [finite chains; finite trees], [Lean's kernel rule; the Lean model's records (`KnotCE`)],
  [`B11`, `B12`], [D121: a nested occurrence passes only through its own sort], [$emptyset$], [Lean's rule; the Lean records (`PropNestCE`, `CrossSortCE`)],
  [`B6`], [the declared type not in an equation (D36)], [$emptyset$], [the syntactic form of positivity],
  [`TBD`], [a parameter passed to an equation is not nestable], [finite chains], [the same],
  [`Q11`], [the type's constructors unreadable while it is declared (D107)], [finite chains], [the simulation: before it a zero-arm match on the type being declared was vacuous],
  [`NT` (against `DPF`, accepted)], [a field type that is a Π at the generic telescope (D36)], [as `DPF`'s], [nothing the model distinguishes],
)
Two checks serve neither the construction nor Lean's rules but other parts of the proof: no borrow in a parameter or field type serves N5's "a borrow is the whole value of a binding or temporary", and D105 (where a constructor's parameter is inferred) serves the simulation's agreement with the checker. The checks the construction does need, and where one notch weaker breaks it, are listed in @fig-n1-checks.

*The two syntactic checks the Lean lane proposes* (`exists12`, not made, not measured): in `checkInd`, a parameter heading a field's type must be written `Prop` or `Type`, and a global heading a field's type must have a written codomain `Prop` or `Type`. Today both facts are decided by the run-based `sortOf` check, so deriving `FieldHeads` in Lean needs type preservation; with the checks it becomes a postcondition of `checkInd`, and the case of `VaryValFact` left open in Lean (a parameter whose reading is "any", excluded today only by the run of the parameter loop) closes too. By reading they reject only heads whose sort is hidden behind a computation, which the run-based check already rejects; whether any accepted row changes is not measured.

*The recommendation* (`theory8`'s, after the sixth referee and `exists12`). Keep D120 and D121: they are Lean's, and the Lean model, which the consistency proof uses, needs them; relaxing either needs the Lean records rebuilt first. Record each check with what it serves (@fig-n1-checks does), so that a later relaxation does not remove a load-bearing check or keep a dead one. Adopt the two syntactic checks after measuring them.

*What would change in the paper.* The appendix's [Ind-decl] gains the two checks; its note on positivity can say which conditions are the model's and which are Lean's.
]

== (e) Redesigns "by construction" proposed and not measured <sec-dec-redesign>

#decision[
Each would make a principle hold by structure instead of by checks at listed sites. None has been built or measured.
- *A certificate for an untyped run* (principle 4). `callFn` runs a body only given a `Checked` record that only `checkFix` can make; a closure carries its λ's. Since D135 and D136 the same effect is one test in `callFn` by name; the certificate would make it a type error to forget. Deletes: the need to find D135's routes one by one.
- *One evaluator* (principle 4). `typed` becomes a parameter that may only guard checks and type computations; `checkTailAt` becomes `evalCore` with the goal checked at the end; every branch that changes control, state or hints goes behind one function both modes call. Cost: a refactor of `Machine.lean`'s largest functions. Deletes, as separate rules, the patches that brought the two modes into line (a tail split ending with the join, D119; the hint an untyped run hands down, D124; a call of a function ending in `split`, D125), and the class "an accepted function whose call is rejected", which recurred five times.
- *Check every arm* (principle 4). Check an arm of a match on a known constructor at its declared types, as Lean and Rust do. Reverses the ruling recorded in D118. Deletes: the join's rejection of a place an unchecked arm names (D94), the check on a `*` in a moved place (D101), the walk that checks the names of arms no run takes (D118), and the model's obligation to give ill-typed arms a meaning (`DeadIll`, `DeadMoves`).
- *Flags as parameters; values in flight on the evaluator's stack* (principle 5). The one-shot flags and the results passed back through the state become arguments and return values of `eval`, and `eval` leaves its result on the temporaries. Deletes as rules (each becomes impossible to write) the one-shot defer flag consumed at every evaluation (D130) and a `let` deferring only a non-erased call's type (D132), and, as a method, the hunt for values held outside the state while a call runs (D115).
- *One grammar of declarations shared with the model* (principle 1). The Lean lane wrote the conditions once as decidable predicates (`Knot/Grammar.lean`: `GrammarOk`, with `grammar_of_checks`); `checkInd` would call only that module. Deletes: the drift between the model's grammar and the checker's tests (how the site principle 1's audit found, D120's (B2), stayed open), and makes the Lean fact that `checkInd`'s acceptance gives the grammar's conditions (`CheckIndGivesChecks`, now proved) hold by construction.
- *Smaller ones:* hints of a type of their own, not `Value` (principle 7's one maker, N9); a block's capture modes from declared readings only (N6); a reading that is a function of the type (principle 3: either complete the reader through a type function's body and assert reading against type in `evalAt`, or reject a hidden sort where a type's sort is read).
]

== (f) Which model the paper states the existence of data types for <sec-dec-n1>

#decision[
*The question.* N1 (@sec-n1) says that the data types of every accepted program have a model. Two models are in play, and nothing defined relates them (the sixth referee's Y1). The _Lean model on codes_: families indexed by codes, trees that record their declaration's parameters, parameters ranging over codes, for programs that write no sort above `Type₁`; `exists_dataModel` builds it from five facts (@sec-n1), and the consistency proof uses it and only it (`consistency_rel` takes it; no step reads a set model; docs/34 §18.18). The _set-level construction_ (S0 to S9 of @sec-n1): families over all small sets, trees with no record, every universe level; the paper's sketch is of this kind, and on sets it is argued only given three properties of a run on sets, since the reference run is defined on codes.

*The options* (the sixth referee's two, who left the choice to the owner).
- (i) State N1 for the Lean model on codes, bounded at `Type₁`, and give S0 to S9 as its explanation, each step with its Lean counterpart named. _What it costs the paper:_ its N1 says less than its sketch does today: it is bounded at `Type₁`, and the set model's extra identifications (`Ph(Nat)` with `Ph(Bool)` for a phantom parameter, any two empty data types, any two true propositions) are no longer claimed; consistency never reads them, so the theorem loses nothing. The construction's prose stays, read as the explanation of the Lean one.
- (ii) Keep the set model as the statement and add a bridge: a decoding of codes into sets that commutes with the run at every node of the field-type grammar (the three properties: congruence, locality, calls typed at their codomain). _What it costs the paper:_ a new theorem about the run, about the size of the congruence and locality lemmas together, not started. It buys unbounded universe levels and the coarser identifications.

*What was measured.* Nothing; both are choices of statement. The third property, on codes, is `GlobalCallLevels`, now proved (docs/31 D260).

*The recommendation.* (i), `exists12`'s (docs/34 §18.18). The earlier consolidation presented (i) as settled and as the sixth referee's recommendation; it was neither.

*What would change in the paper.* Under (i): §7's sketch of the model and the appendix's section on the model state N1 on codes, bounded at `Type₁`, the construction as its explanation with each step's Lean name. Under (ii): the same sections keep the set model and gain the bridge theorem, stated and proved.
]

#pagebreak()

= The principles <sec-principles>

A _principle_ is one sentence about the design, not about a line of code, such that the consistency argument uses it at a point that can be named, a wrong program would be accepted (or a step of the argument would break) if it failed, and the checker makes it true either _by construction_ (a structural reason it cannot be violated) or _by checks_ at sites that can be listed. A site where a principle could fail and nothing makes it hold is _not enforced_. The principles are the design's half; what must be _proved_ about the checker or the model is a named theorem (@sec-theorem), which rests on them. Twelve principles explain the 139 recorded decisions and eight accepted proofs of `False` (the ledger, @sec-ledger); five of them were written for the first time by this theory, found in the residue of decisions no earlier principle explained. Each is stated with what in the argument uses it ("cases" are those of (II), @sec-cases), how it is enforced, and what its audit found.

#principle[Declarations are in the model's grammar][Every accepted declaration satisfies, by its syntax, the conditions under which the model builds a meaning for it: fields positive and first-order, nested only at nestable parameters, read through only what the model can follow; a type parameter written as a sort and the declaration's own name only in its fields; borrows only of `Type₀`; a match on a proof produces data only from a subsingleton; a function type that returns a borrow takes one.]
A declaration with no model (a type that is its own negation) lets the checker accept a closed proof of `False` by typing alone, before anything runs. _Used by:_ N1, and through it every case. _Enforced:_ by checks, all in `Check.checkInd`, each on syntax and the earlier declarations before the declaration is stored (@fig-n1-checks), and elsewhere: subsingleton elimination at every match on a proof (D45), `&A` only for `A : Type₀` (D66), a borrow result with a borrow parameter (D44), `&` only at the top of a written type (D48; the surface rejects `&Nat` as an argument), constructor parameters inferred only where the model reads them back (D105). _Audit_ (`theory7`, attacked by the sixth referee): every site a named check, but one #s-not, unreachable: a value argument at a parameter whose own type reads a nestable parameter (D120's (B2); `NF`, `DF` accepted, as by Lean). The construction reads an applied declaration loosely and never tests that argument, and a value that varies would have to name the declared type, read a field of it, or take its parameter from a hint, each rejected. Several checks are stricter than the construction needs and serve Lean's records or the simulation instead (decision (d)).

#principle[Identifications are made only by structure][Conversion is the least relation closed under its rules, so a comparison that needs itself answers "not convertible"; functions and Π-types are compared by running their generic calls, with their class and borrow flag; `Eq` decides only by convertibility, injectivity and disjointness of constructors, and on `⊥` as a value of its own; `J` computes only at convertible endpoints; an impossible arm is stuck, never a value; and a record is looked up by its exact key.]
Conversion is how a checked term moves from one type to another, so an identification that fails at some instance transports a member of one set into another. _Used by:_ N3 and every "≡" premise (cases 2, 3, 4, 6 and the step to the theorem). _Enforced:_ by construction, by the definition of conversion (D30, D48, D54, D56, D58, D84, D103, D108). _Audit:_ the checker's `eq` returns `False` at two places only, two constructor values of different constructors and `⊥` against a value, so it never refutes an equation between two type values, whatever their formers (the sixth referee, by reading `mkEqM`). The comparison of code rests on every sealed program having [Close]'s shape (principle 7).

#principle[Readings are true where they replace a value][Whatever the checker reads about a term from syntax and declared types, and acts on by replacing a value with a canonical one (`⋆` for a proof, `()` for `Unit`, its constructor for a one-constructor type, nothing for an erased type), is true of the term's type; and a type is read off a value only where the value says its type.]
Decisions are made from _readings_, facts read off syntax and declared types; principle 4 makes them the same on every run, this one makes them right where a value is replaced. _Used by:_ cases 3, 5, 7, 8 (only this direction). _Enforced:_ by one reader of declared types (`Decide.typeDecl`, `declOf`) made syntactic (D55, D77, D80, D86, D96, D100, D116, D128), and by checks where a reading meets a type: D131's at every binding a typed run makes, D55's in [T-Pi], D128's at a declaration's parameters, and for a type read off a value D110's strong update, D112's leaf fields. _Audit:_ one #s-not site: a term that is not bound (a statement, an argument, an arm's result) is never compared with its type, so a term of type `⊤` whose sort hides behind a call reads as data and runs with its effects (`W2`, beside `WP2`, which is erased). Not a route to `False`: the reading is the same on every path, and conversion cannot identify the two motives, whose classes differ (D54). It means "a term is a proof exactly when its type is a proposition" is false; "a binding is" is true. One site predicted by the two-paths census (its site 7: a binding whose declared type is a type function whose arms are Π-types of different classes) is closed by D77, which rejects such a binding (`theory2`'s `PT`, `L`, `L2`, measured at 105021637). Redesign in decision (e).

#principle[One code, two runs][Every decision that changes what a run computes (whether a term is erased; a function type's class and [Close] row; copy or move; η; the places a match moves and their grain; which borrows end where and what a result is lent; the parameters a constructor records; the hint handed down) is a function of the code and the declared types, computed alike by the code's typed check, by every untyped run of it and by its meaning.]
A definition is checked once, by a typed run at unknowns, and afterwards run untyped, in place or sealed; the argument gives the code one meaning and shows each run computes it, which holds only if every run decides as the meaning does. The oldest instance is the generic call against an instance (D28 to D40, D54, D84, D90); the newest the typed check against an untyped run (D124, D125, D134, D135). _Used by:_ cases 1, 3, 4, 6, 7, 8 and N6. _Enforced:_ by construction for decisions made in `Decide.lean`, which does not import the machine (D74), writes no cache (D95), and reads unknowns by frozen readings (D96); by construction with listed obligations for borrow ends (D90's fills and marks, D99's fresh result label, D93); by checks for hints (D124's sites, each consulting `readsHint`) and for a deferred call's head test (D134); by one test where every run of a body starts, for "only checked code runs" (D135: a call of the function under check closes off, recognised by name since D136). _Audit:_ every place an untyped run starts runs checked code (since D135); two #s-not classes. (1) A static decision read from an arm no run takes reads unchecked code: places and names are checked (D94, D101, D118), anything else is not (`DeadIll` accepted, `DeadMoves` rejected by its dead arm's capture). Not a route to `False`: a dead arm's moves only add to the join. (2) Tests made only by untyped runs: one is shared (`callPi`, D134); nothing structural stops another. And one difference of decision, an incompleteness: whether an unknown of a one-constructor type is refined in place or the run is stuck is decided differently by the typed check and an untyped run's field access (`Fst0Gen`); the join's drop does refine. _For type safety, not consistency:_ "an untyped run runs only checked code, can run every form the check accepts, and makes the check's tests". At an observation the principle fails today (principle 6 below).

#principle[The state is the whole truth][Every value the checker holds while anything runs is at a position of its state with a stored type; nothing outside that state decides a step (no flag, cache or record outlives the evaluation it was made for); and every step that succeeds is an instance of a rule: no failure is turned into a value, and running out of fuel is undecided.]
The argument reads every success of the checker as a derivation of the rules at the state the rules describe, and its invariant is a predicate on that state. _Used by:_ the first move of every case; the meaning of a state; a call's arguments held where an end reaches them (case 1). _Enforced:_ by checks at each site found: every value in flight is a typed temporary (D104, D115's sites), D106 rejects ending a borrow a temporary holds, D111 asserts no borrow below a root, D92 and D117 keep scaffolding frames from holding a loan twice; by construction for one-shot flags (consumed at `evalAt`'s entry, D130) and private runs (`restoreKeep`, `restoreNames`). Fuel exhaustion is its own exception, outside what `catchStuck` catches. _Audit:_ two #s-not sites, both harmless: `J`'s endpoint values held in Lean variables while its motive runs (everything then runs on private copies), and the `inPlace` flag between its set and its read (a nested re-run there restores the whole state; predicted fault `T5` refuted). Redesign in decision (e).

#principle[Effects stay local][A running body names only its own frame and reaches anything below only through the loans its borrows hold, so every borrow it can end is its own frame's; a call exchanges only its arguments and its result; a closure captures no borrow; and a private run (a statement, a type, a proof, a comparison, scaffolding) restores the state but fresh names and facts that mean the same in every state.]
_Used by:_ the frame property N4 (the equation between a body run in place and its run in its own frame), cases 1, 4, 7. _Enforced:_ by construction for what survives a private run: two functions decide it (`restoreKeep`; `restoreNames` for comparisons, D103); statements go through `Env.inStatement`, scaffolding through `Env.privately`; six further sites save and restore directly (`nfSealed`, `stuckScrutinee`, `checkFix` with `restoreKeep`; `conv`, `convPi`, `convFn` with `restoreNames`). Unlike the two functions, those six do not raise the private-run depth (`privateDepth`), so the two checks `endTopLoan` skips inside a private copy stay armed inside them: the assertion that a loan in the top frame is borrowed from the top frame, and D106's rejection of an end that a value in flight holds; and the first three restore on success or stuck only, not on an error. Both are harmless (an armed check can only reject more, and an error rejects the definition anyway, principle 5), but the first is the detail the detached observation's assertion turns on (the fifth referee's V4, @sec-idclause). _Audit:_ #s-not at an observation, five sites: the observation's `endAll` ends every borrow of the whole state, and D98 and [Repack] then test the caller's borrows' contents, and `idType` tests every owner it compares, the caller's included. Each gives an accepted function whose call at a known argument is rejected (`S1Z` to `S5Z`); and with no borrow parameter at all, any callee that forms an `Id` cannot be called while its caller holds a borrow partly moved (`CallI`). A second route reaches the same tests: [Call-type] reads a callee's parameter types at the call site on a private copy, so a function whose parameter type forms an `Id` cannot be called while its caller holds a borrow partly moved (`CallH`; through a returned borrow, the fourth referee's `CallF`), and the caller is rejected. Type safety only. Decision (a) repairs both routes (`CallF` measured under (C) and (C+)).

#principle[Closing off rebuilds the call][A call stuck on an unknown, and a stuck match or `J`, is replaced by sealed programs that rebuild it exactly from what it was passed, capturing every place any arm uses at least as strongly as the arm does; nothing else makes or changes a sealed program held in the state but substitution and re-running, which happens exactly when an input it embeds changes, everywhere it occurs, never re-closes its head, and never runs a program that holds a borrow's hole.]
_Used by:_ cases 3 and 4; N3 for code (every sealed program held in the state has [Close]'s shape). _Enforced:_ by construction: `closeCall` makes the sealed programs of the state; blocks go through `closeBlock`, which computes captures (`blockCaptures`) and calls `closeCall`; `nfSealed` re-runs, refusing a text with a hole (D97); substitution and re-normalisation share `Env.mapState`. _Audit:_ one other sealed value exists, the deferred hint `⌈⋄hint P w̄⌉` (`hintLater`, D124), an evaluation's argument read only by `forceHint`; it is never stored (by reading, at every site; two passes agree) but nothing structural prevents it. Under the observation design (C+) the identity fills are a second exception, made and filled on the observation's copy. Under blocks as text the block's head is a third term form, made only by `closeBlock`.
#stand[the first referee's O5 (a)]["Nothing else makes a sealed program" holds of the deferred hint by reading, not by construction, and the hint's meaning enters (II)'s (E4) (the second referee's R8), which N9 argues. Redesign: give hints a type distinct from `Value`.]

#principle[Worlds are exclusive][A fact established while checking one arm of a split, and depending on the arm's constructor, is visible in that arm and its sub-worlds only, and entering an arm substitutes its refinement into every position of the state.]
_Used by:_ cases 3, 4 and the step to the theorem (every assignment takes one arm; a record is a path condition). _Enforced:_ by construction: every arm runs in `Env.inWorld`, whose exit restores every component of the state but those listed, so a new component is dropped by default (eleven sites). _Audit:_ held; its historical faults are `EtaBoom` (D79) and records rewound with a copy (D37). One known exception, harmless: an erased match's arm unknowns can appear in the type of what leaves the arm (`Leak`, @sec-proof-fields).

#principle[Whole where relied on][A value may be open (break its type's telescope, or hold a moved part) only while the code that opened it runs; wherever it passes to code that relies on its type it is whole, at every future of the parts still lent; and whatever produces an unknown of a dependent type has checked whole the value it stands for.]
_Used by:_ case 5, N7, and every strict end of a borrow. _Enforced:_ by construction for returns: `closeBlock` runs its arms itself and calls `bodyReturns`, the function `checkFix` calls, at each arm's end (D76); by checks elsewhere: [Repack] at whole reads, borrows, captures and observations, a lent part checked as an unknown of its borrow's type (D73), the `⊥` tests at read, borrow, capture and end (D53, D98, D127). _Audit:_ held. Its historical faults: `GetN` (D73), `JLie` (D75), `LieLent` (D64 amended).

#principle[Recursion descends][Every call the check of a definition makes is of an earlier accepted definition, of a value, or of the definition itself, recognised by the name it binds for itself and checked to be on a strict part of the entry value as refined so far.]
_Used by:_ the outer induction and case 9. _Enforced:_ by construction for recognition (`recFrameOf`, by a mark on the binding; only top-level definitions recurse, D136); by checks for descent (`recCheck` at every typed call, in nested functions and block arms too); a call of the definition under check closes off (D135); a global enters Σ before its check and is kept only if accepted. _Audit:_ held. "Only on a `Type₀` inductive" is redundant with the strict-subterm test (`qe`). Historical faults: `CapSplit` (D78), recursion on overwritten parts (`L`).

#principle[Observation names every root][The places `Id` observes are read from the syntax of its two sides, which run on independent copies; today each place is traced to every one of its owners; under the observation design (C) or (C+), each root of the observing frame is compared at itself or at its cell, and no loan is followed below the frame.]
_Used by:_ case 2 (computing `Id`; a statement used at another state). _Enforced:_ by construction: `Obs.footprint` takes roots from the sides' terms, `Obs.owners` follows every occurrence of a loan or a mark outward, and one function, `obsResult`, observes for `Id` and [Conv-fun]. _For the adequacy of `Id`, not consistency:_ the sides leave the same type-state ([Id-typestate], D84, D114), re-pointed borrows are observed ([Obs-ref], D38, D113), conjuncts come in a canonical order. _Audit:_ held; a known gap of adequacy: where a re-pointed borrow of `Unit` points.

#principle[Access is exclusive][Every access first ends the borrows that lend what it touches, so nothing reads, copies, matches, overwrites or drops a live loan; no access or drop ends a borrow a value in flight holds; a borrow ends only over a whole content; and a borrow is only ever the whole value of a binding or a temporary.]
This is Aeneas's discipline and the machine's [Access]: the borrow checker is a consequence of running the program. _Used by:_ N5, which every case uses; the end of a borrow as an equality of reference states; injectivity of contexts (only under today's observation). _Enforced:_ by checks: [Access] (`accessPath`, `accessInside`, `accessNeutralHead`); every end of a borrower goes through `endTopLoan`, which rejects ending a borrow a value in flight holds (D106); [End] requires a whole content (D98); D111's assertions at overwrite, drop and read; `closeCall` asserts loan-free inputs. _Audit:_ held; the invariant it keeps (N5) is argued per operation and swept on 2,137,352 states, not proved.

#pagebreak()

= The theorem and the named theorems <sec-theorem>

== The statement <sec-statement>

*Theorem (consistency, conditional).* Assume ZFC with one inaccessible cardinal per universe level used. Let the model be changed as @sec-frame-model, @sec-proof-fields and decision (b) say: (M1), built; a match on a proof of a declaration that is not a subsingleton not run, built (D229); a borrow-typed match's join lending its result only while live, built (D222); (M2) widened; (M3) restricted or, under the observation design (C) or (C+), the detached observation; the model's [Obs-ref]; and a reading of a stuck block that is not a function of every value (decision (b)); the last four not built. If N1, N3, N4, N5, N6, N7, N8 and N9 hold, then for every accepted, hole-free program no definition without parameters has a type that evaluates to `False`. In Lean this is `Ochr.Consistency.consistency`, about the checker at every fuel; the mechanisation aims first at `consistencyBounded`, for programs writing no sort above `Type₁`.

_Proof._ By (II) (@sec-halves), every successful typed run of the checker is matched by a successful strict reference run from a related reference state. By (I) (N2) that run's result is a member of the type it returns. At a leaf of a definition's case tree [Def] compared that type with the goal, so by N3 the result is a member of the goal under every assignment (@sec-concl). A parameterless definition is checked from the empty state, which has one assignment; a member of `False` would be a member of $emptyset$. $square$

#figure(table(columns: (12%, 38%, 30%, 20%), align: left, table.header([*Name*], [*Statement*], [*Status*], [*Rests on*]),
  [N1 _A model of the data types exists_], [For every accepted, hole-free program there is a data model of its declarations: per declaration a family, least, closed under its constructors with the field types the reference run computes, monotone in its nestable parameters, stable as the program grows (@sec-n1).], [In Lean for the model on codes, programs up to `Type₁`, assuming five facts, each read true and none derived (`exists_dataModel`); the set-level construction argued in full given three properties of a run on sets; which the paper states is decision (f); attacked with 193 + 90 programs, nothing found.], [Principle 1.],
  [N2 _The fundamental lemma_, (I)], [From a good reference state a strict run that succeeds returns a good result and leaves a good state; a proof that runs proves a true proposition.], [#a-lean (`fund_all`, every clause of the strict run; its context has a kernel-checked instance).], [N1.],
  [N3 _Conversion is sound_], [If $v equiv w$ at a reached state, both well typed inside at one type, they mean the same under every assignment; `Eq` computed on `⊥` or whole members means equality of meanings (@sec-n3).], [For values without code proved in Lean on the unmerged branch `rules-trial`, under named premises (@sec-n3); argued for code and at a type; attacked, nothing found.], [Principles 2, 3, 4, 7; N1.],
  [N4 _The frame property_], [A body run in place and the same body run in its own frame with a cell per borrow parameter, from related good states, both fail or both succeed with the same result and related states (@sec-frame).], [#a-lean for terms with no `.fix`, `.pi` or `.id` (`runFrameI_frameFree`); the clauses for those three forms argued as @sec-frame-stmt marks them, open in Lean; its first use, C1, in Lean for a frame-free global body assuming three facts (`callInPlace_of`).], [Principles 4, 5, 6, 10, 12; N1, N5.],
  [N5 _Exclusive access is preserved_], [Every step keeps the state well formed: one holder per live borrow, every loan bound, lending acyclic, arguments exclusive, no live loan on a written path, the typing of places, types hold no loan, fills only of [Close]'s shapes (@sec-excl).], [Argued per operation; refereed for some clauses only; swept on 2,137,352 states; not mechanised.], [Principle 12.],
  [N6 _The decisions are aligned_], [Each decision the checker makes is the one the reference run reads from syntax and declared types (@sec-n6).], [By construction in `Decide.lean` (agreement across fuels #a-lean); a block's captures by reading at three sites.], [Principle 4.],
  [N7 _[Repack] is sound at a read_], [A whole open member that passes [Repack] is a member (@sec-n7).], [Argued; attacked; not mechanised.], [Principles 3, 9; N3.],
  [N8 _The block lemma_], [A match run directly agrees with `callOf` of the block it would close off as (@sec-n8).], [Reduced to C1 and the place renaming PR, argued; today's model reads a block as a function of every value, which is false at `NTr` (decision (b)); under blocks as text, definitional for the model's reading (by reading).], [Principles 4, 7, 12.],
  [N9 _Hints are inert_], [A body run at the checker's hint runs as at its codomain, and the deferred hint means the codomain (@sec-n9).], [Argued by reading; the reference run's half of (a) proved in Lean, for terms whose tails read no hint (`run_hintIndep`).], [Principle 4.],
), caption: [The named theorems.]) <fig-named>

Two further lemmas have the status of named theorems though the argument derives them: _resolved determination_ (RD, @sec-rd), needed only under today's observation, and the _renaming lemma_ RL (a run is unchanged by shifting the label counter, @sec-frame-stmt). Under the observation design (C) or (C+) the frame property's `Id` clause needs the _detach lemma_ DL (@sec-idclause) instead of RD.

== The two halves <sec-halves>

*An assignment* γ of a checker state Ω gives each unknown Ω still refers to (in a value, a stored or deferred type, the goal, a record in force) a member of its type's meaning, in the order the unknowns were made, meeting the _path conditions_ of the current world: a refinement $sigma := r$ in force fixes γ(σ) to $r$'s meaning, a generalisation $n := sigma$ to the meaning of the sealed program $n$. An unknown function ranges over every set function.

*A reference state* $S$ is a structure, not a set of values: the checker's frames, bindings and temporaries, each position with a _meaning_ (a function of the _future_, which gives labels values), a stored type as a _code_, and its declared reading; which position holds each label (one at most); for each live label where it is _lent_ (each site a loan or a fill) and its _record_, a whole member of its content's type; a label counter. A future is _typed_ when it agrees with the run's off the live labels and gives each live label a whole member of its record's type.

*The strict reference run* $refrun(t)$ runs the machine's rules on a reference state, except that a call applies its callee's meaning and never runs a body (a callee returning a borrow lends the new label wherever its borrow arguments are lent); an access ends the live borrows lent at, over or under the place; a match reads its scrutinee's tag, so nothing splits; `Id`, `Eq` and `J` mean as in the model. It fails wherever a value is put at a type it is not a member of (an annotation, a constructor's field, a closure's formation, a borrow, an assignment, a read, a call's borrow argument), at a write at a field unless the path exists at every typed future, and at the end of a borrow unless its holder's content is a whole member at every typed future. A read is taken at the typed future that gives each live label its record. *Good:* at every typed future each binding holds an _open member_ of its stored type (defined field by field, with completions of moved earlier fields: the plan's), each holder an open member of its label's record type, each record a member, each label one holder.

*The relation.* $S$ simulates Ω under γ and a renaming π of labels at φ when (R1) they have the same frames and bindings in order, types of the same code and the same readings; (R2) π is one to one on the live labels into labels $S$ issued; (R3) at every typed future each binding means under γ what the reference's means, and holders match through π; (R4) each live borrow is lent at the same places, fill or loan alike; (R5) each live label of $S$ has a record. It holds at the start, steps compose, and it survives a private copy (`Rel.start`, `sim_seq`, `Rel.private_copy`: #a-lean).

*(I), the fundamental lemma,* is N2.

*(II), the simulation, as the mechanisation states it* (`EvalAt` for a run of `eval`, `TailAt` for `checkTail`; one strong induction on fuel, `master`, which assembles it from 32 step statements and assumes them: seven proved in general, 25 open). Let the checker run $t$ from Ω, typed (to $v$, $A$, Ω') or untyped (a body in place, a sealed program's re-run; to $v$, Ω'). Hypotheses: (E1) Pre(Ω, γ): γ an assignment; the context is Ω's (its declarations, a data model of them, each global's meaning a member of its type, but the definition under check, whose meaning is its stage, a member of the weakened type; the decision table the checker's); the typing of places; Ω well formed (N5). (E2) $S$ good and simulating Ω. (E3) $t$'s embedded values good, its unknowns Ω's, no hole. (E4) _Untyped runs only:_ the strict run of $t$ from $S$ succeeds, at the checker's hint (which N9 relates to the codomain). (E5) The plain mode: not copying, not in place, no head evaluation (in copying mode the checker's read leaves a place the strict run moves: `let x = S(Z); let y = clone(x); x`, at the read inside `clone`; such sub-runs have their own steps). (E6) The reading handed down is none or the decision table's. (E7) The hint names only Ω's unknowns. (E8) A frame exists; a typed run starts outside tail position. (E9) The decision table is aligned at the run's end, not its start. Conclusions, for some γ' and π' extending γ and π at what the run made: (C1) the strict run of $t$ succeeds, in tail position exactly when the checker's is, with result $r$, type $T$, state $S'$; (C2) $r$ means $v$ at the future the run is read at; (C3) typed runs: $T$ means $A$; (C4) Pre(Ω', γ') holds and the states with the results held as temporaries are related; (C5) the run keeps its mode, its number of frames and its top frame's readings; (C6) a deferred call type reads as the reference's result type; (C7) a promised type that is missing reads as an error.

_What is not in (II):_ no clause says a value the checker holds is a member of its type. Membership is (I)'s, about the strict run; (C2) and (C3) carry it to the checker. This is what answered the first referee (the form that carried membership on the checker's side failed when mechanised: a value in flight had no type, a return check did nothing at `Unit`, an untyped run bound positions at types it never checked). _Why the relation survives the end of a borrow:_ an end is an operation on reference states, not a choice of future: the holder becomes _moved_ and every position that read the label reads the holder's content, on both sides alike, with equality at every typed future. Its strict test passes because the checker ends a borrow only over a whole content (D98) and a whole open member that passed [Repack] is a member (N7). #a-lean for the fragment's leaves.

*Open in (II)'s statement:* that a successful run ends with the deferral flag clear (`DeferClearG`, read true, unproved); (C2) is proved at one future, (R3) asks every typed future.

== The induction <sec-induction>

*Outer:* on the position $k$ of $d_k$ in the program and, for a recursive $d_k$, on a bound $b$ on the rank of its decreasing argument. An earlier global's meaning is its own, a member (the outer hypothesis); $d_k$'s is its _stage_ $b$, a member at every argument of rank below $b$. Under D135 nothing during $d_k$'s check runs $d_k$'s body: every call of it closes off, so the outer hypothesis is used only through the meaning of such a sealed call, the stage applied. The step $k$ establishes, in this order (`lead37`, correcting D213): (II) for $d_k$'s check; membership of $d_k$'s meaning (the _knot's_ goodness: the meaning built from the stages is good at every member argument, `FnGoodG`); the descent clause (`RecDescG`, restated); the fixpoint equation (`FixEqG`), which uses membership. In Lean the last is proved from the two before it, which it assumes (`fixEqG_of`); the first three are open, and for a global whose blocks call it they wait on decision (b) (`MB0r`). _Inner:_ (II) by strong induction on fuel; a callee's body and a sealed program's re-run run at less fuel than what caused them. _Nested:_ a function formed in a body (non-recursive since D136) is checked at its own node, by the same two halves; its membership, and the injectivity of a returned borrow's backward function where the model needs it, is proved there. A stuck block is checked at its own node too, but only at its captured values, so its function need not be a member of its function type (`NTr`); what that node gives is the block's meaning at those values, and the model must read the block so (decision (b)).

== From (II) to the theorem <sec-concl>

At the root of $d_k$'s check the generic state, read as a reference state, is good and simulates itself. Each assignment reaches exactly one leaf $(Omega', v, A)$: at each split its value of the scrutinee has one tag and selects one arm (principle 8). By (II) along the path the strict run of the body succeeds with $v$'s meaning and $A$'s; by (I) the result is a member of $A$; [Def] checked $A equiv G'$, the goal refined on the path, so by N3 (whose typing hypothesis (I) supplies: a value whose meaning fits a type is well typed inside at it, except through constructor values of `Prop`-sorted declarations, `hwt_of_fit` #a-lean) $A$ and $G'$ mean the same, and $G'$ is $G$ under the path's refinements, which the assignment meets. The cells are compared by (R3) and are whole at the leaf ([Return], principle 9). This is an instance of the frame property (C6, @sec-frame-stmt): the generic state as the in-place side, its frame of cells as the caller's frames.

_Injectivity of a returned borrow's backward function._ As long as the model's function types hold only functions whose backward functions are injective (the relation $R$; under every option but (C+)), membership has one more clause: a $d_k$ that returns a borrow has an injective backward function. Its cells' contents are contexts around the result's loan, built only by steps that place a loan (a borrow, a reborrow, a stuck call's fill, a call's mark, the end of a borrow whose content holds the loan) and touched by nothing else while the loan is live (principle 12); each such step is injective jointly over the places it fills, and composition keeps that: _holes are placed injectively_, N5's (X5). A borrow of $d_k$'s own local cannot be returned (it is a value in flight when the local dies: D106). Under (C+) the model drops $R$ and this clause with it. #a-red[N5]

== N1: a model of the data types exists <sec-n1>

*Which statement.* Two models are in play: the Lean model on codes, which the consistency proof uses and only it, and the set-level construction below, which the paper sketches; nothing defined relates them. Which one the paper states N1 for is decision (f) (@sec-dec-n1), open. This section gives both: the Lean theorem, and the construction as the argument it mirrors.

*The Lean theorem.* `Assembly.exists_dataModel` (on `spine` at 73f1a1075): for every resolved list of items and every fuel, a data model covering every declaration, faithful at every stage, assuming five facts, each read true against today's checker and none derived: that the names an accepted item mentions are the stage's (`NamesFact`); that no field type of an accepted declaration reads a value parameter that varies (`VaryValFact`); that a parameter or a global heading a field's type is at level 0 (`FieldHeads`); these three about the checker, derivable, but the first needs a whole-machine invariant on names for a constant's stored value, and the other two need type preservation through the run-based `sortOf` check, or the two syntactic checks of decision (d); that a block's captures are rooted at the term's free places (`DecCaps`, a fact about the decisions; blocked by Lean's `Array.qsort`, whose recursion is private to Lean's core and has no lemmas); and that a field type runs the same at every later state the checker reaches (`DecStable`, about the decisions; false at an arbitrary state, `FactsCE`; not attempted). So it proves N1 on codes only once those five are established. Proved since the last pass: `GlobalCallLevels` (the hard case, a global with a domain in `Type₁` heading a field type, by a stage invariant on a global's type, the telescope of a written Π with a sort codomain, and a new lemma tracking `telL`'s terminal code, the sixth referee's Y3), `ItemFacts` (with `CheckIndGivesChecks` assembled), `NoValFact` (from the program's resolution), and three of the four parts of the decisions' locality (`DecLocal`; its fourth is `DecCaps`).

*The construction, as explanation* (`theory7`; refereed by the sixth referee, who found its logic right). Universes mean Carneiro's: `Prop` the two truth values, `Type_i` the stage $vk(i)$. A data value means a tree: its declaration, its constructor, its fields' meanings. Per declaration, by recursion on the program (S1), the field types form a grammar (S2): `Nat`, `Unit`, a parameter, an applied earlier declaration, the declaration itself, a call of an earlier type function, an equation over first-order data; its _spine_ is the field type and, inside an applied declaration, its arguments at type parameters. Off the spine nothing varies with the family being defined (S3a); on it everything is monotone and preserves unions of increasing chains, own nesting included ($X(X(A)) subset.eq Y(Y(A))$ by $Y$'s monotonicity, S3b); every field type is small (S4); a data declaration means the union of its ω stages, a least fixed point among monotone families (S5); a proposition its least truth by Knaster and Tarski on monotone predicates (S6); the result is faithful to the strict run wherever that is defined (S7) and stable (S8); so constructors are injective and disjoint, trees have finite depth and ranks decrease through any field, and a subsingleton's arm is determined by its proposition (S9 (1) to (3)). The other type formers (S9 (4): Π-types as dependent products, cut to $R$ for a borrow result; `Eq`, `Id` as truth values; $\&T$ as $T$) are the plan's, #a-claim. On sets, S1, S3a, S4 and S7 hold _given three properties of a run on sets_ (the sixth referee's Y1): (P1) congruence (a node means the same under two models that agree at the names it mentions); (P2) locality (it reads its frame only at the variables it mentions; on codes this needed `DecLocal`, and a run on sets needs the same of its decisions); (P3) calls typed at their codomain. On codes these are the Lean lemmas `runT_congrN`, `runT_qset` and `GlobalCallLevels`. _Corrections folded in:_ S0's closure under tuples holds of $vk(i)$, not of `Prop`; S6 needs monotonicity only in the nestable `Prop` parameters; a function's meaning is the typed function cut at its codomain (S4's), not "its body's reference run" (S1 said both); the ω-union and its leastness are Kleene's, not taken from Carneiro's §6.2.1 (which has no stages); taken from the thesis are the universes and `Prop` of §6.2, the truth-value reading of ∀, and Remark 1, and nothing of §5's reduction or its unfinished §5.4.

*Where Ochr goes beyond Lean's metatheory*, each covered by the construction: nesting at an earlier declaration's and at the declaration's own parameter with a varying argument (`DD(A) := DLeaf | DNode(x : DD(DD(A)))`, which Lean's kernel rejects); recursion at other values of value parameters, families Forded through equation fields (`Vec`, `EvV`), including a value-indexed declaration nested at a field variable (`VL`, which Lean rejects); field types computed by running code (`AV` writes a local through a borrow); propositions nested at their own `Prop` parameter (`N2`, `PN`); data holding functions at instances of its field types, borrow-returning ones included (`DPF`, `DPB`), whose relation $R$ is part of S9 (4).

#figure(table(columns: (30%, 14%, 56%), align: left, table.header([*Check (decision, function)*], [*Serves*], [*Without it, or one notch weaker*]),
  [Fresh names; constructors distinct within a declaration ([Ind-decl], `declared`)], [construction], [two arms named alike make one tree, while `distinctCtors` tells them apart by index],
  [The declaration's own sort `Prop` or `Type₀` (`d.sort > 1` rejected, and by the surface before it)], [borrows; the rules that assume data is in `Type₀`], [not needed for existence: a data declaration in `Type₁` would have its family in #vk(1); `inductive Big1 : Type₁ := MkBig1(x : Type)` rejected, "(surface) Big1: an inductive type is in Prop or Type"],
  [Fields a telescope (D64, `fieldRefs`)], [construction], [no dependent sum (`LateEq`)],
  [First-order fields: no Π over the declared type; no Π at all (D36, `firstOrderTerm`)], [construction], [`Bad := MkBad(f : Π(x : Bad). False)`: Curry; a positive Π into the type (`WT := … WNode(f : Π(n : Nat). WT)`) makes ω stages too few],
  [… and no call computing to a Π at the generic telescope], [nothing], [`NT` rejected, `DPF` accepted: alike to the model],
  [The declared type on the spine at calls (D36, `firstOrderArgs`, `firstOrderCallArgs`)], [construction], [`B1`, `B2`: negativity behind a type function],
  [… and not in an equation or a value argument], [positivity's syntax], [`B6` means $emptyset$],
  [Nesting only at nestable parameters, the greatest set, own occurrences included (D107, `nestableSet`)], [construction], [`PositivitySelf.Q`: Curry's paradox, a closed proof of `False` before D107],
  [… a parameter passed to an equation or a value is not nestable], [positivity's syntax], [`TBD` has a least model],
  [A variable mentions what its declared type mentions (D120, `readViolation`, `deepVars`)], [Lean records (`KnotCE`); Lean's rule], [`D2`, `LD`, `NBD` have least models],
  [One sort per knot (D121, `sortNestViolation`)], [Lean records (`PropNestCE`, `CrossSortCE`); Lean's rule], [`B11`, `B12` mean $emptyset$],
  [The type's constructors unreadable while it is declared (D107, the declaring entry)], [(II)], [`Q11` has a least model; before it a zero-arm match on the type being declared was vacuous, so the checker's field type differed from the strict run's],
  [Field levels; sorts syntactic (D55); a type parameter written as a sort (D128)], [construction], [`U1` to `U10`, `T1` to `T5`; `TL`'s `B` ranges over $vk(1)$, so a field type would not mean a small set (S4)],
  [Names declared and earlier; own name in fields only (D118, D133, `undeclaredCheck`)], [construction], [S1's recursion; `Q3` ran the checker out of memory],
  [No borrow in a parameter or field type (D71, `typeHasRef`)], [N5], [N5's (X1): a borrow is the whole value of a binding or temporary],
  [A constructor's parameter inferred only where the model reads it back (D105)], [(II)], [a tree does not depend on what is inferred; the run's agreement does],
  [_Elsewhere:_ subsingleton elimination in every position (D45)], [construction], [`IsL`, `D1` to `D15`],
  [_Elsewhere:_ recursion only on a `Type₀` inductive ([Rec])], [nothing (redundant)], [`recCheck` already fails a parameter with no entry value (`qe`)],
  [_Elsewhere:_ borrows only of `Type₀` (D66); a borrow result needs a borrow parameter (D44)], [S9 (4)], [`Impred` (Hurkens); `QF`, `QU`],
), caption: [The checks of a declaration and what each serves: the paper's construction, Lean's records or rules, the simulation (II), or N5 (after the sixth referee's Y2).]) <fig-n1-checks>

*The standing assumption.* A model that identifies two type values the checker tells apart is wrong. Neither model is: the checker's `eq` refutes only two constructor values of different constructors and `⊥` against a value, never a type value (the sixth referee, by reading `mkEqM`); every other place it compares two types (conversion in [Eq-refl], [J], a goal, [Rec]; a record's exact lookup) gives `True` or stuck, accepts or rejects, never wrong. So no equation between any two type values, whatever their formers, is refuted (`EE`, `PT`, `EP`, `NoTEq` rejected, each stuck). The earlier justification "a type is a copy, so a place that holds one is never moved" is false: a type at a place declared at a type parameter is moved (`MoveTy`).

*Status.* Lean: on codes up to `Type₁`, assuming five facts, each read true and none derived. Which model the paper states: decision (f). Paper: S0 to S9 argued, S1 to S7 given (P1) to (P3), S9 (4) claimed. Attacks: 193 programs by `theory7` and 90 more by the sixth referee, re-run: no accepted declaration without a model, no large elimination from a non-subsingleton, no accepted empty type. Incompletenesses: a parameter typed by a function type over an earlier type parameter cannot be declared (`VF`); a constant that is a type is not admitted as a field's type, while a call is (`B10`).

== N2: the fundamental lemma <sec-n2>

From a good reference state, a strict run that succeeds returns a good result and leaves a good state, and a proof that runs proves a true proposition. #a-lean: `fund_all`, on `spine`, every clause of the strict run, nothing unproved beneath it; its context has a kernel-checked instance; applied to seven concrete runs. It was found vacuous, then false at a write to a field, then too wide for the simulation, and changed each time; its typed futures give each live borrow a whole member, and the end of a borrow is a strict point. Not covered: the frame operations of a call run in place (push, pop), which are N4's.

== N3: conversion is sound <sec-n3>

*For values that hold no code:* proved in Lean on the branch `rules-trial` (ea3fbb37, not merged into `spine`, and stated against the model as it was before its type formers were strict; `conv_sound_T`, `mkEqM_sound_T`, in two halves), assuming named premises: the function rules' premises sound (`PremSoundT`: a successful generic call or comparison of generic arguments' types makes the two values alike; [Conv-fun] at two globals can fire even between first-order values), the comparisons' generic sub-computations keeping the state (`GenericKept`, `EqKept`), the code cases (`CodeOk`, outright for first-order values), `Eq`'s field types (`FieldTysSound`, `FieldTyIdx`), and two facts of the data layer (the library's `And`, `True`, `False` mean conjunction, truth and falsity, `LibOkT`; the unit laws keep typing, `UnitOk`), which TC4 and TC5 below derive from N1; and under the typing hypothesis (both sides well typed inside at one type; without it `Eq(Nat, And(True, Nat), Nat)` against `Eq(Nat, Nat, Nat)` refutes it, and no accepted program forms the first). (I) supplies the hypothesis at every use.

*For code* (`theory5`; refereed by the fourth). By induction on the derivation of $v equiv w$, which is finite since the relation is the least one. CV1 [Conv-refl]: invariance under renaming of bound variables, #a-full. CV2 data: N3 for values above (in Lean on a branch, under its premises). CV3 sealed programs equal but for convertible embedded values mean the same: a sealed program means the strict run of its text, which depends on embedded values through their meanings (`RunCongr`) and through their _readings_, which convertible values need not share (`F (n : Nat) : Unit := ()` and `H (n : Nat) : TF(Z) := ()` are convertible, and a call's result is copied for one, moved for the other: `TwiceH`); but every sealed program held in the state has [Close]'s shape (principle 7), where a reading is read at three points only, the head's class and row (equal by [Conv-pi]), η at `Unit` (sends a member to itself), and the head's codomain as `r`'s stored type in the borrow row (which nothing reads to decide). It needs every embedded value to be a member (true today; false under the unrestricted patch (B), the fourth referee's F1). #a-red[principle 7, `RunCongr`] CV4 closures by the fast path: CV1. CV5 [Conv-fun]: two functions with convertible Π-types and captures and convertible observations at the generic call mean the same, since a function's only effects are its result and its borrowed places and its meaning is that observation at every argument list; the generic runs are cases of (II) whose (E4) is the functions' membership. #a-red[(II), FR (C1, C6)] CV6 [Conv-pi]: under (M1) the model's domains and codomain are runs in exactly the generic state. #a-red[(II), (M1)] CV7: every "not convertible" fails safe; read coinductively, [Conv-fun] would identify any two closures stuck at their generic calls and `J` would prove `Eq(Nat, S(Z), Z)` (`G12` rejected). #a-full

*At a type* (`theory7`; refereed by the sixth). TC1 sorts and [Conv-refl]; TC2 $ty("D")(overline(v)) equiv ty("D")(overline(w))$: a family is a function of its parameters' meanings; TC3 $\&T$ and `Eq`; TC4 the unit laws, from N1 at the library's `True`, `False`, `And`, which also keep typing (a match on either side decides by its own stored type's head); TC5 [Eq-inj], [Eq-disj], [Eq-refl] from N1's consequence 1; TC6 [Conv-pi] as CV6; TC7 neutral types as CV3. [Conv-cong] on two Π-closures with the same code and convertible captures (the checker's fast path), missing from that list, is CV3's congruence. The two hypotheses the Lean proof for values took about the data layer (the library's connectives mean conjunction, truth and falsity; the unit laws keep typing) follow from N1 (TC4, TC5); on the Lean model through its least truths (`truth_exists`). #a-full given N3 for values.

*Attacks:* 13 programs on code, 23 at types, re-run by two referees: no pair of convertible values with different meanings. One incompleteness: two convertible functions with stuck bodies, `Fs (n : Nat) : Unit` and `Hs (n : Nat) : TF(Z)`, give a stuck `Eq(Unit, (), ⌈Hs(σ0)⌉)`, since η reads the head's declared codomain.

== N4: the frame property <sec-frame>

A function's body runs in two ways. The checker runs it _in place_: a frame pushed on the caller's state, each borrow parameter holding the caller's borrow. The model reads the function's _meaning_ off a run of the same body in its _own_ state: its captured values and, per borrow parameter, a fresh borrow whose loan sits in a _cell_ below the body's frame, which ends holding the parameter's final content. The frame property says the two runs agree. Every call run in place rests on it, and so do a statement read at a call site, a sealed program's re-run and the step from (II) to the theorem. It was stated six times and refuted six times, each by a state the statement admitted and no call makes; every refutation is now a hypothesis, with the program or lemma that forced it.

=== The model it is about <sec-frame-model>

- *(M1) A function type's later parameter types and codomain are read with a cell per borrow parameter* (forced by the second referee's `G1`: with no cell, the model read `G1 (x : &Nat) (e : Id(Unit, (*x := 0; let z = x; ()), (*x := 1; let z = x; ()))) : False`'s second domain as `True`, so it read an accepted definition's type as empty). This is what [Def], [Conv-pi] and [Conv-fun] do. _Built in Lean_ (docs/31 D210).
- *(M2) A closure formed in a body runs from its captures, in a frame laid out like the forming top frame* (structural form; it replaces a circular definition, the third referee's T3). The `.fix` clause accesses each capture, reads each captured position as a constant, and runs the original body from that frame at counter 0. A Π-type's captures are read on a copy, with no access and no move, as the checker forms them (T2: built like `.fix`, `PiMove` and `PiLentEq` would lose their meaning). _Widened_ (D220): the type runs of a Π-type, and of a closure's own parameter types and codomain, read the whole forming state, so (M2) must host them too. Not built.
- *(M3) An end inside an observation is a strict point exactly when its label is held in the observing frame* (the third referee's repair: unrestricted, it made the frame property false at a call with no borrow parameter, `CallI`). Not built: a change of the model's observation, to be carried through the fundamental lemma's `Id` clause and the simulation's `Id` step (D227). Under the observation design (C) or (C+) every end in the detached state is the side's own, and the unrestricted form is right.

=== The statement <sec-frame-stmt>

*Theorem FR* (Lean `RunFrameI`: its hypotheses are the start conditions `FrameStart` and the internal relation `FrameInv`, whose clauses the table below names one by one, as Lean has them on `spine` today. Proved in Lean, standard axioms, for every term with no `.fix`, `.pi` or `.id`: `runFrameI_frameFree`, docs/31 D225, from the run's context, `FrameStart`, the embedded values' goodness and the relation at the start; open for those three forms). Over the model with (M1). Let the context meet the fundamental lemma's conditions; let $s_0$, the state just _after_ the callee's frame is pushed, and its parameter labels `ks` meet the start conditions (S1) the caller reads no label at or above the counter, (S2) the parameter labels are below it and distinct, (S3) the caller holds none of them (true only after the push: at the call point the caller's temporaries still hold the arguments, D115), (S4) the caller's borrows are lent only in the caller's frames; let $t$'s embedded values be good and $t$ form no `Id` when there are parameter labels; let a renaming σ (closure labels to in-place ones) relate $s$ and $s'$ (`FrameRel`: (F1) σ injective and fresh to fresh; (F2) frames; (F3) the caller's frames keep their types, readings and holders; (F4) each caller position reads what it read at the call with each $k_i$ given cell $i$'s current meaning; (F5) the top frames hold the same bindings with meanings related through σ; (F6) holders correspond; (F7) content types and records agree but at parameter labels; (F8) the top frames' sites correspond; (F9) closure labels go to parameter labels or above the counter). With:

#table(columns: (30%, 20%, 50%), table.header([*Hypothesis*], [*Lean (`FrameInv`)*], [*Forced by*]),
  [The renaming relates the frames: (F1) to (F9) above], [`FrameRel` (inside `AccInv`)], [the statement itself],
  [(H1), (H2) both states good], [`good`, `good'`], [a caller binding holding `err` makes the whole-state test fail in place only (D113); a junk binding in frame 0 makes it fail in the closure only (D201)],
  [(H3) locality: positions read only live labels, a holder only labels above its own; no top-frame position reads a parameter label], [`rinv'`, `noParam`], [a run reads a meaning at one future; a variable reading label 0 in the closure and 5 in place reads differently off the live labels (D129)],
  [(H4) frame 0 holds the cells first, one per parameter label], [`cells`], [with no cell, a parameter label's end changes a caller position and nothing in the closure (D203)],
  [(H5) every recorded holder is a position; one holder per label on each side], [`shape`, `uniq`, `uniq'`], [[End] finds a holder by search (D209)],
  [(H6) lending well founded], [`lend`], [two labels each lent at the other's holder, ended in two orders, leave different sites (D215)],
  [(H7) in place, a parameter label is lent in the callee's frame only as a fill], [`pfill`], [`relend` of a loan site is not associative at an empty path (D211, D215)],
  [(H8) parameter labels' preimages lie below every other closure label, and σ is monotone on the others], [`order`, `mono`, for live labels], [ends go in label order; σ may reverse two parameter labels (`P4`); D208's monotonicity is true and insufficient, its premise that a parameter label has no site in the callee's frame is false (`P2`, `P4`)],
  [(H9) the in-place counter is at or above $s_0$'s], [`counter`], [fresh labels correspond],
  [(H12) σ sends every closure label, dead ones too, to a parameter label or past $s_0$'s counter], [`srange`], [a label the closure's run returns must never be a caller's, so that [Entry]'s lending at a match's result label and a call's fixes at a consumed label never reach a caller's borrow (D219, D220). Since D222 the join lends a result label only while it is live; the clause is still asked of every label, because a label ended inside a run comes back to life when a `let` or an assignment binds the value that carries it],
  [(H13) every site in the callee's frame is at a binding], [`bsites`], [lending a parked result further would close a cycle (D219)],
  [(H14) every site of a live label in the callee's frame is at an existing position], [`psites`], [a `let` binding a result pushes a binding at a new position; a stale site there would lend the label at its own holder, and lending would not be well founded (D222; it was the `let` invariant of D220, then in neither statement)],
  [(H15) the records, (H8)'s order and σ's monotonicity correspond for every label the closure has made, live or dead], [`heldAll`, `orderAll`, `monoAll`], [a dead label comes back to life when a `let` or an assignment binds the value carrying it, and must come back with corresponding records and order (D222)],
  [In place, every live label's record is a member of its content type], [`held`], [what [Access]'s strict ends test (D215)],
)
Then the strict runs of $t$ from $s$ and $s'$ both fail, or both succeed with the same result (its label renamed) and related final states again meeting the hypotheses; and the result's label, if live, is held by a temporary of the callee's frame (`ResAtTemp`, D219), and, if dead, is lent nowhere, on both sides (`ResAtTemp`'s second clause and `ResDead`, D222). These are the clauses of Lean's conclusion, `FrameAgreeI`. Two further hypotheses are `RunFrameI`'s own: the run's context meets the fundamental lemma's conditions (`FundCtx`), and the term forms no `Id` unless there are no parameter labels (`idFree ∨ ks = []`). _Beside FR, needed by the argument and not in Lean:_ (H10) site faithfulness (a position reads a live label only where it is lent; argued by reading every operation, D226 re-reading it against the clauses proved since). FR's clause for a closure formed in the body does not need it: under (M2) each capture is read at the state's typed future, and the two sides' frames are then equal by (O2) alone (D226). C3 (a closure value means what the strict run formed) and resolved determination need it. The `let` invariant that the earlier statement lacked is now (H14), in Lean.

*The invariant* the proof carries, replacing (P) ("a parameter label is lent only at its cell", false: `P2`'s [Entry] lends a parameter label at a callee place, which an access then ends). (I1) No callee position reads a parameter label, and in place none reads a label the caller holds (#a-lean per operation). (I2) A live label with a site in the callee's frame is held there and is in σ's image. (I3) A parameter label is lent at the caller's frames (in place) or a cell (in the closure, not necessarily its own: `P5`), and at callee places only as fills. (I4) Two ends commute as states when neither holder reads the other's label, lending is well founded and a site of either at the other's holder is a fill; two strict ends commute in their tests (`endLabel_comm_state`, `perm_fold`: #a-lean).

*The proof,* by induction on $t$ as the strict run is defined, clause by clause; Lean's names are on `spine` (docs/31 D212 to D227).
- _Operation lemmas, all #a-lean:_ typed futures correspond on live labels (O1, restated after the second referee's R5; at an end, and at the callee's frame, `typed_push`, `typed_pull`); a read (O2: `contentOf_corr`); [End] (O3, including a label the body made, through (F4): `frameRel_endLabel`); [Access] by commutation of ends (O4: `frameRel_access`); a write (O5), a fresh label (O7), bindings and temporaries (O8) (D216); the whole-state test after a write or a borrow below a root (O6: `lentOk_corr`, `stateOk_corr`, with the rest of each state good position by position inside the clause, D223); D112's invalidation of dependent fields (O9: inside the borrow and assignment clauses, D223, D224).
- _Clauses #a-lean, each a lemma `runFrameI_…`:_ a read, by copy or by move (`_place`); a borrow (`_borrow`); an assignment, at a root, through a borrow or at a field path (`_assign`); `let` and `;`, with labels or without (`_letIn`, `_seq`); a match on a number or on a declared type (`_matchNat`, `_matchInd`); a call, its head, its arguments, the strict test of its borrow arguments and a data or borrow result (`_call`); `J` with its [Entry] and join (`_J`); constants, literals and embedded values (`_val`), `S(u)`, equations and their proofs, annotations, inductive types and constructors, `clone` and `peek`, `split`, and the other primitives (`Steps/FrameSimple`, D225); a body reading its own binding, through the read clause, the two selves being the same meaning at the start (D202, D230). Assembled by induction over the term for every term with no `.fix`, `.pi` or `.id`: `runFrameI_frameFree`.
- _Argued on paper only:_ a closure formed in the body (`.fix`): under (M2) the captures are accessed and moved on both sides as today, and every run from the structural frame is the same run on both sides by (O2) (D226), #a-full by reading; (M2) is not built, a change of the model that touches 48 files. A Π-type formed in the body, and a closure's own parameter types and codomain (`.pi`): under (M2) widened, equal results from the unchanged state, #a-full by reading (D226); not built.
- _`Id`:_ `RunFrameI` uses it only where there are no parameter labels, and there it holds by reading under today's model (D227); with parameter labels it is outside FR (@sec-idclause), and no use of `RunFrameI` needs that case (D227).
#stand[the second referee's R2, narrowed by D220 and D226][The model runs a Π-type's parameter types and codomain, and a closure's own, from the whole forming state under a fresh bottom frame, so in place they see the caller's frames and in the closure frame 0, and the relation cannot relate the two runs. The clause holds once (M2) hosts those runs in its structural frame, captures read on a copy, and then needs only (O2) (D226, by reading); (M2) is not built.]

=== The call in place, the fixpoint equation, closures <sec-frame-fix>

*The start:* at a good call point, $s_0$ (the in-place state after the push) and the closure state `fixBodyAt` builds (captures under (M2), own name $G$ at its true type, a cell per borrow parameter) are related and meet every hypothesis, each from the call point's goodness, the arguments' decoding at the domains (case 2, through C2), N5's acyclic lending, and the arguments being loan-free temporaries. #a-full. In Lean, for a global (D230): the start conditions at the state after the push are proved from the call point's locality (`frameStart_inStart`); the relation half is the named fact `CallStartInvG`, read true clause by clause, one sub-fact of it (a parameter's content type is its binder's, a round trip through the telescope's codes) not yet a lemma; `frameJ2_holds` is one program's instance. *The pop:* both sides end the same labels, in orders differing only among parameter labels, which commute; after the ends the cells read the finals, and (F4) reads the caller at the cells' finals, which is `callOf`'s fixes. What the pop concludes is a _transfer_ of the relation, not equal states: the run in place made and ended the body's labels, so the counters and the records and sites of dead labels differ, while the relation reads only live labels and a bound on the labels that occur. #a-full, given the fixpoint equation; in Lean the named fact `CallPopG`, read, not proved (D230).

*The descent clause and the fixpoint equation* (`lead37`, docs/31 D234). `RecDescG` as Lean first stated it is false (it asked no membership of the two selves, and the whole-state test reads `self`); restated: for two meanings of the own name that are closures over the domains, good functions, agreeing at member arguments below the call's rank, the body's runs give the same output. `FixEqG` is stated at the global's forming state only, and needs the global's function good everywhere (`FnGoodG`, the knot's output), so membership comes before the equation. `FixEqDesc.fixEqG_of` proves the fixpoint equation in Lean from `RecDescG` and `FnGoodG`, which it assumes: the first read true as restated, the second the knot's output; neither is established. For a global, `RecDescG` comes from (II) for its own check and the fact that every sealed call of it in that check carries a decreasing argument of rank below the entry's (D135 makes every such call close off at a site the [Rec] test saw); no circle, since under D135 the check never runs the body. Establishing `RecDescG` and `FnGoodG` in Lean is blocked, for globals whose blocks call them, by decision (b).

#stand[`lead37`, item 39][The paper's [App] binds a function's own name in its frame only when it declares `by`; the checker's `runBody` binds and marks it for every function (unread without `by`; the proof's relation reads the mark, D136's amendment). The paper should say what the checker does; for a block the binding is fault (3) of decision (b).]
*A closure's fixpoint equation* (CloFix). Under D136 a closure declares no `by`, binds no own name in its body, and has rank 0, so its body does not read its own binding: (b) its meaning is a member of its type (by the nested induction where the typed check formed it, by (E4) of the case that made an untyped run otherwise); (a) its fixpoint equation follows by OwnIrr, a run does not read a binding its term does not name (read (b) first: (a)'s whole-state test uses it). #a-full. *False for a block's closure* (`NTr`: the model reads the block as a function of every value, the checker checked it at its captured value): decision (b).

*The uses, as corollaries.* (C1) A call in place: from FR, the start, the pop and the fixpoint equation, the run in place succeeds exactly when `callOf` does, with the same result and a state to which the relation transfers. #a-red[FR, FixEq] In Lean for a global whose body forms no function, function type or `Id`: `callInPlace_of` (D230), assuming three facts, the start's relation (`CallStartInvG`, read true), the pop (`CallPopG`, read) and the fixpoint equation (`FixEqG`, above). (C2) A statement read at a call site, under (M1): FR for a type term run on a copy. #a-red[FR] _At a call point only_ (the third referee's T4): the checker evaluates borrow parameters' types at the call point and defers the others; a deferred type keeps the arguments as passed and finds the same owners while their labels live; one with an `Id` over a borrow parameter whose label has ended before it is read finds no owner and is weaker than the model's. #a-np for that case (no program known; an untyped run does not read a proof parameter's stored type); repair under today's observation: evaluate such types at the call point; under (C) or (C+) closed by construction.
#stand[the third referee's T4][Case 1's push rests on C2, which says nothing of a deferred parameter type read after its borrow argument's label has ended.] (C3) A closure value means what the strict run formed: a renaming of variables and positions undoing `capture`'s inlining. #a-np
#stand[the third referee's T3][C3 is a lemma, not a definition, and is not proved; case 3's [T-Fix] and resolved determination's producer of a closure's fill rest on it.] (C4) The start's parameter types: by definition under (M1) and (M2), provided the run in place reads the callee's parameter types and codomain where the closure reads them, on the closure value's forming state. The model read them on the caller's state, where a type with an `Id` observes the caller's frames: a fault of the model found and repaired in D230. C2, the checker's types read at the call site, stays a separate step. (C5) A sealed program's re-run: by RL. (C6) The step from (II) to the theorem: an instance of FR (frame 0 of cells as the caller's frames; (F4) the identity). *RL* (a run is unchanged by shifting the counter, for bindings that read no future and carry no label; Lean `run_counter_indep`, false as first stated, open): FR's argument with the caller's clauses deleted, a separate proof.

*Not proved, in words:* the `Id` clause with parameter labels (by RD under today's observation, by DL under the detached one; no use of FR needs it, D227); C3; the block lemma's place renaming PR; a deferred parameter type read after its borrow has ended; the clauses that need (M2) widened (argued, D226; the model change not built); FR in Lean for terms that form a function, a function type or an `Id` (for every other term it is `runFrameI_frameFree`); and the facts C1 and the fixpoint equation assume (the start's relation, the pop, the descent clause, the knot's goodness).

== N5: exclusive access is preserved <sec-excl>

Every step keeps the state well formed. The clauses, in the forms the argument uses:
- (X1) each label has at most one borrow, the whole value of a binding or temporary, never inside data, a sealed program, a closure, a type or a record; one exception: a deferred parameter type's record keeps the call's arguments as passed, a borrow argument with its content at the call (`lazyTy`), read only by `paramTypes` on a private copy after taking the live borrow from its holder (`takeArgBorrow`), and lent nowhere once the label has ended (the fourth referee's F6; the sweep scans values, not these records);
- (X2) every loan or mark has its borrow (but an inert loan inside a sealed program's run); outside sealed programs a label occurs as a loan at most once;
- (X3) lending is acyclic;
- (X4) at every call point each argument is loan-free or a borrow of loan-free content;
- (X5) _resolution is injective:_ the map from the live labels' final contents (independent whole members) to the meanings of the positions holding no borrow is injective under every assignment (needed only under (A), (B), (C));
- (X6) after a write's access no live loan or mark lies on the written path;
- (X7) the typing of places: a place declared a borrow type holds a borrow, `⊥`, a loan or a mark, and a place holding a borrow is declared a borrow type;
- (WF11) no stored or deferred type, type of an unknown, goal or record holds a live loan; (WF12) under a live fill only borrows filled there; (WF4), (WF15), (WF16) captures hold no borrow and no `⊥`, sealed programs are closed and end in a read whose meaning does not depend on its type.

*One argument per operation* (`theory3`, completed by `theory5`; refereed by the fourth). [Borrow]: after the access the place holds no live loan; one temporary holds the fresh borrow; its loan is one occurrence; the identity context keeps resolution injective. [End]: the holder becomes `⊥`; the content replaces the loan or fills the holes, in values only (no type holds the label); loans inside it move with it, their contexts composed (jointly injective maps compose); where the site was a fill its loans become holes of that fill (WF12). [Access], [Drop], the join's drop, a `let`'s end: sequences of ends; a drop that would end a borrow a value in flight holds is an error (D106). Reads: data read after its access is loan-free; a moved borrow passes to a temporary; a partly moved place or a borrow over one is not read (D127). [Assign]: the access ends the loans in the part the place owns (D67); (X7) in a typed run by conversion, in an untyped run because a term's declared type reads as a borrow exactly when its value is one. [Close]: inputs loan-free (asserted), holders consumed, each loan becomes a fill of the call's text, the hole in every fill, the fills jointly the callee's backward function (injective by its membership), a `Unit` place's fill keeping its hole in the borrow row (D137). [Lend] and [Entry]'s lending: marks, jointly but not singly injective, which is why every owner is observed. [Split], refinement, generalisation: no label touched; a sealed program generalised only after its holes' borrows ended (D29, D90). A sealed program's re-run: only with no hole (D97). Capture, private copies, observations: captures read after access; a private run keeps names and records only, which hold no loan. Forming a type: on a private copy from loan-free reads; a dependent field's type in a frame binding what each earlier field stands for (D117), a tree field whose content does not have that type taking its content's (D112): so (WF11). A call's push and pop: arguments move to bindings; the deferred record is (X1)'s exception. D112's invalidation: writes `⊥` after ending a lent leaf's borrows. And one correction (the fourth referee's F4): a step can change the value around a live site, a write to a sibling field or the invalidation of a leaf beside a lent field, but only at a disjoint path, which keeps a constructor context around the site, so (X5) is kept. #a-full by reading; the sweep holds every clause on every recorded state (`RdWhileFilled`, `TwoParts` probe (WF11), (WF12)). Refereed in part: the fourth referee read (WF11), (WF12) and the preservation of (X5) (RD2) and found them to hold, and found (X1) false as stated (its exception, a deferred parameter type's record, is now folded in); no referee has read every clause's argument. Not mechanised.

== N6: the decisions are aligned <sec-n6>

At every reached state each decision the checker makes (erasure, a function type's class and row, copy or move, η, the join's places and grain, a block's captures and modes, a match's entry, a constructor's recorded parameters, the hint) is the one the reference run reads from syntax and declared types. _By construction_ for decisions made in `Decide.lean`; their agreement across fuels is #a-lean (but the captures). _For a block's captures, by reading at three sites:_ `blockCaptures` counts a variable a borrow variable when its stored type is a borrow type _or its value is a borrow_, and splits a capture by its content's constructor; the two readings agree on every state because a binding's type is deferred only for a `let` of a call whose declared result is not a borrow (`callFn`'s deferral) and for a parameter whose declared type is not a borrow (`runBodyCore` evaluates borrow parameters' types eagerly), and a split by constructor is only through a value of a one-constructor type. The first referee's shape (a borrow ended before a borrow-typed match, assigned whole in an arm the run does not take) agreed. #a-full by reading; the redesign "modes from declared readings only" would make it structural.
#stand[the first referee's O9; the fourth referee's F7][N6 for captures holds by checks at three sites, not by construction. And whether the core (not the surface, which cannot write it) admits a borrow type at a type parameter, which would give a binding with a deferred type a borrow, is not tested.]

== N7: [Repack] is sound at a read <sec-n7>

A whole value that is an open member of $T$ at every typed future and passes [Repack] (each lent part replaced by an unknown of its borrow's type) is a member of $T$ at every typed future. By induction on the value: with no dependent constructor inside, no strong update was made, so every field fits; otherwise each field fits its declared shape or is a tree open at its own record whose type [Repack] compares (N3), and a proof or leaf field, which [Repack] cannot test, fits because a write through an index invalidates it and re-assigning it is checked at the current contents with lent parts unknown (D64 amended, D112); a lent part takes any member of its borrow's type at a future, and the unknown stood for exactly that. #a-red[N3] _Sites:_ principle 9's whole-again points; at `Id`'s owners only in the observing frame (a caller's owner holds the caller's state with the side's writes put in, open by either's doing: the fourth referee's F5). _Attacked:_ a proof field made true while an index it reads is lent (`ReSnd` accepted: the proof reads a part the result does not point at; `ReFst` rejected; `ReFill` rejected through a stuck call's fill; `GetN` rejected). Not mechanised.

== N8: the block lemma <sec-n8>

A match not in tail position, after its [Entry], whose tag selects arm $i$: the direct run (the arm, the join's drop, a borrow-typed match's lending) and `callOf` of the block's function at the arguments [Args] takes both fail or both succeed with the same result and state, up to the result's label. Hypothesis: each captured value decodes at the block's domain for it (the third referee's T7; supplied in case 4, where the checker closed the block off). _Reduction:_ `callOf` is the block's function run in place (C1, no captures, no recursion); that run is the direct run by the place-renaming lemma PR. *PR:* a relation between the direct state $D$ and the block's state $B$: (P1) below the frame and outside the captures, the same; each capture holds a loan (`ref`), _moved_ (`mv`) or its entry value (`cp`) in $B$'s frame; (P2) $B$'s parameters hold $D$'s current contents at the captures; (P3) the arm's own positions correspond; (P4) the arm's labels correspond by the shift of the `ref` captures' labels, and for a borrow-typed match one more, the result's label its call reserves (D99; the fourth referee's F7); (P5) a place $q_j pi$ corresponds to $(dr z_j) pi$ or $z_j pi$ with the same reading; (P6) sites correspond. One lemma per operation: an access under a capture ends the same labels (after the [Entry] none is lent on the path but the arm's own); reads, writes, borrows, ends, drops, nested matches and calls act alike; an `Id` in the arm compares a different position for a `ref` capture with the same truth (in the model, the same proposition up to a reflexive conjunct; through a stuck call's fill internal to the frame, the same truth by that fill's injectivity, today; by constructors only under (C+)); at the arm's end the join and the pop give the same state. _Hints:_ the direct arm gets none out of tail position; the block's body gets its codomain, the arm's own checked type, so recorded parameters agree. #a-full; not mechanised. This form reads `callOf` of the block's function only at the block's captured values. Today's model reads a sealed block as a closure, a function of every value, and that reading fails where the block was checked only at its captured value (`NTr`), so N8's model half needs decision (b): under the closure-style clause ruled for today's representation the model's reading is the body's run at the captured values, and N8 is the link from the checker's re-run to it (D233); under blocks as text the model reads a block by running its text at its captured values, which is the direct run's shape, and N8 becomes definitional for the model's reading.

== N9: hints are inert <sec-n9>

A body run in place gets the deferred hint of its codomain (`hintLater`), the codomain computed at the call point when an argument is a borrow, or no hint where `readsHint` says its tails read none. (a) Where `readsHint` is false the run at no hint and at the codomain are the same run: `readsHint` follows `evalCore`'s reads of its hint (a constructor with unwritten parameters, an embedded value, `rewrite`, `clone`, `peek`, tails in tail position). (b) The deferred hint, forced at any later point, means what the codomain means: it keeps the arguments as passed, its evaluation reads nothing of the state but them, and the forcing's own records mean what they stand for. (c) So the runs mean the same. #a-full by reading (`UseMv`, `UseWr`, `UseTT` measured). It is a check, not a construction: a new form of `evalCore` that reads its hint must be added to `readsHint`. In Lean: the reference run's half of (a), a run whose tails read no hint giving the same value and state at every hint (`run_hintIndep`, for terms with `tailHintFree`); the checker's half of (a), and (b), are not mechanised.

== Resolved determination (needed under today's observation) <sec-rd>

A statement `Id` over a borrow parameter is checked at the generic call, where the parameter's loan sits in a cell, and used at every call site, where its loan sits in the caller's places. The two readings agree only if the caller's places, once the borrows between them end, determine what was written through the parameter; otherwise `G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e`, accepted, could be called with `refl`.

*RD* (stated by `theory5`, restricted after the fourth referee's F2 and F4). Let $K$ be live labels held in the top frame of a reached state Ω, $E(K)$ $K$ with its lending ancestors, and $W(K)$ the owners of $K$'s labels. If (a) every ancestor in $E(K)$ outside $K$ is held by a holder whose content is a whole member at every typed future, and (b) no position of $W(K)$ is a binding declared a proof, then for every assignment: if every position of $W(K)$ means the same after giving $K$ the finals $v$ and ending $E(K)$ as after giving it $v'$, then $v = v'$. _Hypothesis (a)_ holds wherever today's observation has passed, since it ends and tests each ancestor first. _Hypothesis (b)_ is vacuous in the checker: since D138 a proof's data fields are locals of the arm, so no proof binding is ever the owner of a written place (the fifth referee's V2). _Assumptions:_ (X5); every backward function a fill computes is injective on members, by producer: an earlier global by the outer hypothesis, an unknown function by the assignment, the definition under check by its stage and item 11 (its sealed calls carry decreasing arguments below the rank), a block's function by N8, a closure by CloFix and C3; site faithfulness; `eq` injective on whole members. *RD1* (readback): from (X5), upward closure of $E(K)$, site faithfulness and (a). #a-full *RD2* ((X5) kept by every step): @sec-excl. #a-full by reading. _The checker's sites it rests on_, each a predicted way for it to fail: [Access] (`accessPath`, `accessInside`, `accessNeutralHead`, `Value.ownedLoans`); [Drop] and D106 (`dropTopBind`, `dropValue`, `popFrame`, `endTopLoan`); `closeCall` (loan-free inputs asserted, one hole in every fill, no η in the borrow row); [Lend] and [Entry]'s lending (`lendEnv`, `blockEntry`); generalisation only after the access (D29, D90) and [Seal-hole] (D97); `owners` and `footprint`, counting marks; D44; D48, D66, `capture`, D110, D111 (a borrow only the whole value of a position); D98 in `endBorrow`. *Attacked* with a program for each way an owner could ignore a write (a pick, a dependent field's leaf and index, a borrow into a moved or overwritten value, through a partly moved borrow, two levels, a stuck call's fill, a proof's field, functions that overwrite after an inner call, `Unit` places, two parameters into one owner's fields, a fill inside a fill): no call of `G5` with `refl` is accepted (@sec-ev-obs).

*Which borrows an observation must end.* With $O$ the observing frame: every label held in $O$ ($E_1$), their lending ancestors ($E_2$: the owners are positions holding no borrow, and between a parameter's label and its owners there may be caller borrows), and every label lent at a compared owner with its ancestors ($E_3$: the formed `Id` is a stored type and must hold no loan). Ending only $E_1$ is unsound: in `AAncWhole` the owner would hold `r`'s loan on both sides, compared as reflexive, and `G5(&(*r).0, refl)` would be accepted (predicted by reading). It must _test_ only what the side produced: $E_1$'s ends and $O$'s owners; testing the caller's is the type-safety fault of decision (a).

== The `Id` clause of the frame property <sec-idclause>

_What FR's uses need_ (docs/31 D227). Lean's `RunFrameI` asks that the term form no `Id` or that there be no parameter labels, so its `Id` clause is needed only at a call point with no parameter labels; the general case, with parameter labels (Lean's `run_frame_obs`), is reached by no use of `RunFrameI`. With no parameter labels the clause holds by reading under today's model, whose observation ends every live label and tests nothing: the caller's frames read what they read at the call in both in-place runs, and the closure's runs correspond through the renaming. What follows, the clause with parameter labels, is needed only if FR is ever used at an `Id` inside a call with borrow parameters; (M3)'s restriction is a change of the model's observation, not built.

_Under today's observation (A) or the patch (B):_ *Lemma OBS* (Lean's `run_frame_obs` is false as stated: its `CellsDetermined` asks unresolved caller frames to tell the members apart, which a caller borrow reading the parameter label does while its resolution through a constant fill does not; by reading, not kernel-checked). Restated with RD at the call point and (M3) restricted, the in-place proposition holds exactly when the closure's does: after a side's run and every end no position reads a label; the callee frames compare alike (FR); the caller's labels end unchecked in place, in any order (*OI*: in an acyclic state ending live labels in any two orders gives the same meanings, #a-full; the strict half `perm_fold` #a-lean); and by RD the resolved caller frames are equal exactly when the finals are. #a-red[OI, RD]

_Under the detached observation (C) or (C+):_ *Lemma DL* (detach is related). If $s$ and $s'$ meet FR's hypotheses, their detached states meet them again at C6's shape (frame 0 of cells, (F4) the identity), so the `Id` clause is FR's at that shape and OBS, OI over caller labels, RD at call points, (M3)'s restriction, `CellsDetermined`, `run_frame_obs` and `RunFrameI`'s `Id` exclusion are not needed. _What DL needs_ (the fifth referee's V3): FR restated over two lists of labels, the cells' and those the renaming may reorder or whose records may differ (`noParam`, `pfill`, `srange` and (H8) fail for the detached pair if stated over one), and, under (C) only, an invariant (I6) (a closure label has a site at a cell exactly when its image has one in a caller's frame). _What the checker must assert at the detach_ (V4): no position of the observing frame is a site of a label held below it (`endTopLoan` asserts it only outside private copies, and scaffolding frames break it inside some); otherwise a formed `Id` could keep an inert loan. `checker13` built the assertion; it never fired. #a-full by reading; not in Lean.
#stand[the fifth referee's V3, V4, V5][For (C) or (C+) to discharge the `Id` clause: FR and `FrameStart` restated over two label lists; the detach's assertion landed with it; under (C+), a lemma that each position outside the footprint ends as the same function of the compared finals on both sides (today's footprint lemma changes form); and the identity fills excepted from principle 7 and from N3 for code.]

== A proof's data fields, and what "a proof is irrelevant" means <sec-proof-fields>

A match on a proof of a constructor with data fields (`Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))`) is decided by type (D45) and, `Ex` not being a subsingleton, is a declared proof run on a private copy. *The checker* (D138, `bindDataFields`) rewrites the arm: each data field becomes a local `let g = σ` with σ fresh, a proof field of a dependent constructor `let h = (⋆ : T)`, every place at or under the field's place in the arm (inside nested matches too) the local; the scrutinee stays `⋆`. So a nested match on the same proof sees the outer arm's writes (`Nest` accepted), a proof field's type is fixed when the arm starts (`Boom` rejected), and an `Id` over a field compares the local (`PExF`, `PIdSelf` accepted with type `False` inside the arm). The checker's untyped run does not run such a match at all: its value is `⋆`, and no constructor value is ever written into the proof's place.

*The model follows the checker* (docs/31 D229, built on `spine`). A proof means `•` everywhere and never keeps data fields. The model does not run a match on a proof of a declaration that is not a subsingleton: after the scrutinee's tag is accessed its value is `•`, exactly where the checker's untyped run does not run it; the decision is read from the declaration (`Decisions.subsingleton`, the model's copy of the checker's `largeElim`). A match on a proof of a subsingleton runs its one arm, its fields `•`, as before. The fault this repairs was the fourth referee's F2, confirmed in Lean: the model ran such an arm with the scrutinee `•`, read a data field of `•` at the error type, and failed its strict test at a borrow of it, where the checker accepts (`PB`, `PExT`, `PExF`). F2's premise that such a borrow's owner is the proof is false of the checker: the owner is the arm's local, so resolved determination's hypothesis (b) is not touched. The fundamental lemma, the relation and the data model keep their statements.

*The simulation's step there* (D231; owed, not built). Where the checker's typed run checks such a match, (II) applies its induction hypothesis to the checker's typed run of the _rewritten_ arm (`let w = σ; let h = (⋆ : T); …`, the term the checker runs, at less fuel), from the reference state related to the checker's after the tag's access, under the assignment extended at the fresh unknowns by the fields of a _witness_: a member of the proposition, which exists because the scrutinee is a member (`DataLib.mem_iff`); its proof fields' types then hold, so each `(⋆ : T)` is good. The reference's run of that term binds the locals to the witness's fields, position for position the checker's state, the scrutinee `•`; a nested match on the same proof is skipped again by the reference and is again a step of this kind for the checker, whose rewrite there finds the outer locals (`Nest` was checked so: its inner `Eq(Nat, w, 5)` reads the outer local `5` on both sides). (I) on that run makes the arm's type true, which is the type of the match; the model's `•` then means the checker's `⋆` at it. Owed with the step: the alignment of `Decisions.subsingleton` with the checker's `largeElim` in the decision table, the step being its only consumer.

*Not done, and why.* The repair this document proposed before, the model's match clause running the rewritten arm itself, was rejected (D231): the reference run is defined by structural recursion on the term, and the rewritten arm is not a subterm of it; and nothing needs it, since the fundamental lemma's clause is about `•`, the frame property's two sides both skip the match, and an untyped run skips it in the checker too. A witness written at the scrutinee (the paper's earlier rule) relates no state the checker reaches and fails at `Nest`. The alternative in the checker, rejecting every borrow, read and write of a proof's data field, would reject `PB`, `PExT`, `PIdSelf`; not measured. _One named residual_ (D229): a match on a proof of a subsingleton whose constructor is dependent (all fields proofs, a later field's type mentioning an earlier one) is run by the model with its fields `•` at the error type, while the typed check binds them at their telescope types; no such declaration is known (an index field must be data for a later field's type to read it).

*What "a proof is irrelevant" means*, three things the argument uses. (1) A proof is `⋆` in the checker and means `•` in the model, inside an erased match on it too: its data fields exist only as the typed check's unknowns, which the simulation instantiates at a witness; any two proofs of one proposition are convertible (N3, [Def]'s `⋆` parameters, CV3, [T-Call-proof], case 7). (2) Inside such a match its data fields are unknowns, so what the arm proves it proves at every witness. (3) No _value_ computed from a witness leaves the arm: the arm is a declared proof unless the type is a subsingleton (all of whose fields are proofs), and its copy is discarded; records it makes are keyed by its fresh unknowns, never reissued.

*The arm's unknowns can leave through a type* (the sixth referee's `Leak`; settled by the consolidation's author alone, not refereed). `Leak (p : Pin) : True := (let q = match p { MkPin(b, e) => e }; refl)`, with `Pin : Prop := MkPin(b : Bool, e : Eq(Bool, b, true))`, is accepted, and `q`'s stored type is `Eq(Bool, σ, true)` with σ the arm's unknown for `b`. Measured (@sec-ev-proof): `q` cannot be used as the proof it names (`LShow`, `LPass` rejected), matched on (`LTwo`), or used to prove a goal it is rewritten into (`LRw`: `rewrite q in h` turns the goal `Eq(Bool, g(true), c)` into `Eq(Bool, g(σ3), c)`, and `h` no longer fits). _Why it is harmless:_ σ is constrained by nothing. An unknown is constrained only by a split, which needs a place holding it, or by a record, which constrains the record's own new unknown; σ is held by no place. Not everything the checker accepts about σ holds at every value of it: `q`'s own type, `Eq(Bool, σ, true)`, is false where σ is `false`. What the argument needs is that it holds at the witness's value, and it does: (II)'s conclusion extends the assignment existentially at the unknowns a run made; choosing the witness's field there, _kept for the rest of the run_, makes every type that mentions σ mean what it meant in the arm, where the witness makes the proof fields' types true (point (3) above is about values, not types). _What could be done:_ nothing is needed for consistency. Lean's elaborator rejects the same program (a match's motive may not mention a pattern variable); the corresponding checker rule, "a match's type mentions no unknown its arm made", would make point (3) hold of types too, and loses nothing usable, by the measurements above; it is not built or measured against the suite.

== The cases of (II) <sec-cases>

Each case is a rule of the checker, argued against the strict run; each step is marked.

*Case 1: a call that runs in place.* The checker evaluates head and arguments into temporaries, computes the call's type (case 2), makes the [Rec] test; the callee is an earlier global or a closure whose check has finished (a call of the function under check closes off, D135); it pushes the callee's frame, runs the body untyped, and pops. The strict run applies the callee's meaning. Steps: the arguments and the call point (Lean: `CallHeadArgsG`, stated, not proved) #a-full; the push relates the checker's frame to the reference's, which under (M1) reads parameter types in the generic state with cells, so it rests on C2 (a deferred type read late #a-np) #a-red[C2]; (E4) for the body: the callee's meaning is a member and the arguments members of its domains, so its run in its own frame succeeds (with its fixpoint equation), and by FR so does the run in place, at the codomain, which N9 relates to the checker's hint #a-red[N4, N9]; the body by the induction hypothesis #a-full; the pop alike on both sides #a-full; the link to `callOf` by C1 #a-red[N4] (in Lean for a global with a frame-free body, `callInPlace_of`, assuming three facts: @sec-frame-fix). Measured on D135: `Sel`, `Q2`, `Q3` (an equation about the function's own call inside its body) rejected alike; `Loop`, `LC2` rejected.

*Case 2: the call's type, `Id`, and a statement used at another state.* [Call-type] evaluates the parameter types and codomain in a frame binding the parameters to the arguments, on a copy. The strict call decodes each argument at the parameter type read in the generic state, and returns the codomain read there. Both directions follow from statement transfer, C2 under (M1). For a type with an `Id` over a borrow parameter, the conclusion direction is immediate (owners are functions of the finals); the hypothesis direction is RD today, by construction under (C) or (C+). _Computing `Id`:_ the sides are typed sub-runs on copies; the footprint's roots are read from syntax and their owners from where loans are lent, the same on both sides by (R4); the checker ends no borrow over a content with a hole (D98) and checks [Repack] (N7), so the strict ends pass. One model repair is owed: the model's observation does not yet read what a re-pointed borrow points to ([Obs-ref], D113; queued, not built). No proof binding is ever an owner: a proof's data fields are the arm's locals (D138), and the model's side of that is built (@sec-proof-fields). _Other producers of returned borrows:_ a closure returning a borrow is a function checked inside the derivation, whose membership (with injectivity where $R$ requires it) is proved at its own node; a stuck match of borrow type is a block, checked at its captured values only, and its backward function's injectivity is proved at those values, which is how the model must read it (decision (b)) (`QB`, `QB2` rejected). #a-red[N3, N4, N5; RD under (A)]

*Case 3: closing off, re-running, generalising, functions formed in a body.* [Close] discards the partial run, consumes the borrow arguments, fills each loan with ⌈$L; C; c_i$⌉ and returns ⌈$L; C$⌉; a sealed program means the strict run of its text, which binds each cell to the borrowed content (a whole member: a borrow passed to a call is whole, D127, and N7) and applies the callee's meaning, so each fill means what `callOf` leaves there (principle 7). The callee's meaning is a member: an earlier global's, an unknown function's by γ, a closure's by the nested induction, the definition under check's stage below its rank ([Rec]); a block's only at its captured values, at which the model must read it (decision (b)). A re-run after a split: the substituted text's strict run succeeds under every assignment meeting the refinement; a text with a hole never runs (D97), so no run meets a live hole and the paper's assumption of _hole parametricity_ (a fill's run never inspects its hole) is not needed; a head is never re-closed. Generalising: a record $n := sigma$ is a path condition found by exact equality (D108), alive only in its world (principle 8); a record whose text a later refinement changes no longer matches, and the call is a fresh neutral (sound, incomplete). A closure formed in a body: its [Def] is a sub-derivation. #a-red[N7]

*Case 4: a split, a stuck block, the entry and the join.* Every assignment takes one arm and meets its refinement (principle 8); a tail match branches the case tree, each arm ending with the join (D119); an arm skipped on a known constructor is skipped at every assignment of that state, the scrutinee being that constructor there #a-full. A non-tail match closes off as a block after its entry; the strict run reads the tag, makes the same entry, runs the arm directly and drops the join's places. The entry ends the same borrows given the same captures (N6) #a-red[N6]; the block is checked at its captured values only (its arms are its case tree, each end checked as a return), so its function need not be a member of its function type (`NTr`, D233), and the model must read a block at its captured values only, which today's model does not (decision (b)); the block's run is the arm's run (N8) #a-red[N8, decision (b)]; the places moved are read from syntax (`Decide.jdMoves`), a borrow-typed match lends alike (D90) #a-red[N6].

*Case 5: dependent fields.* Positions hold open members. A write or borrow through an index field invalidates the proof and leaf fields whose type mentions it, in both runs (D112); a write at a field finds its path at every typed future because no live loan lies on it after the access (N5's (X6), measured on 48,804 writes); typing by position, strong updates only by values whose content says their type (D110, D112) and checked writes of proof and leaf fields keep open membership; a whole read is a member by N7; a split of a neutral of a dependent type reads it as a whole member (an unknown by γ, a sealed program by case 3, a block by its arms' returns). One known difference: a tree field whose declared type computes to a leaf at the current index while holding a tree from before (no accepted program known). #a-red[N5, N7]

*Case 6: conversion, `Eq`, `J`, `rewrite`, `split`.* Every "≡" premise is used as an equality of meanings (N3, typing hypothesis from (I)); the function rules' generic runs are cases of (II); `Eq` computes by injectivity, disjointness, convertibility, and on `⊥` as _moved_ alike on both runs (principle 4); `J` computes only at convertible endpoints, else it closes off as a block of its transported term; `rewrite` and `split f in t` never run (a `split`'s run runs its term, D125). #a-red[N3]

*Case 7: erased terms, proofs, types formed once.* An erased term runs on a private copy in both runs, and the relation survives the copy (#a-lean); erasure is read from syntax (by construction); a proof the checker types has its strict run succeed, so it proves a true proposition; `⋆` replaces a term only when its declared type is a proposition (principle 3, one direction); a proof's data fields are the arm's locals, which the model does not run and (II) instantiates at a witness, a step argued and not built (@sec-proof-fields); a type is formed once, closed over values. #a-full.

*Case 8: places: reads, writes, borrows, ends, drops.* [Access] ends the same borrows (R4); each end is an equality of reference states, its strict test passed (D98, N7); a read takes the stored type; a write is checked against the place's type (N3) and finds its path (case 5); a drop that would end a borrow in flight is an error on both sides; copy or move is a decision of the code; η at `Unit` and at a one-constructor type keeps meaning (principle 3). #a-lean for the fragment; beyond it #a-red[N3, N7].

*Case 9: recursion.* Every call recognised as recursive (by name, D78) passes a strict part of the entry value as refined; under γ, of smaller rank; under D135 it closes off, its meaning the stage applied; never on a proof. #a-full; the checker held against `L` (recursion on a part of an overwritten value: rejected; by syntax it would prove `Eq(Nat, Z, S(Z))`).

#figure(table(columns: (32%, 24%, 44%), align: left, table.header([*Case*], [*Status*], [*Rests on*]),
  [1 A call run in place], [#a-red[N4, N9]], [FR with start, pop, fixpoint equation; the push on C2 (a deferred type read late open); Lean: the call point stated, and C1 for a frame-free global body assuming three facts (`callInPlace_of`)],
  [2 Call types; `Id`], [#a-red[N3, N4, N5]], [C2 under (M1); RD today, none under (C)/(C+); the model's [Obs-ref] owed],
  [3 Closing off; re-runs; local functions], [#a-red[N7]], [a block's meaning at its captured values (decision (b))],
  [4 Split, block, entry, join], [#a-red[N8, N6]], [PR; captures by reading; the model's reading of a block (decision (b))],
  [5 Dependent fields], [#a-red[N5, N7]], [no live loan on a written path; [Repack] at a read],
  [6 Conversion], [#a-red[N3]], [conversion for code],
  [7 Erased terms], [#a-full], [the step at a match on a proof, owed (@sec-proof-fields)],
  [8 Leaf rules], [#a-lean (fragment)], [beyond it N3, N7],
  [9 Recursion], [#a-full], [—],
  [From (II) to the theorem], [#a-full], [(I), N3; the injectivity clause N5 (not under (C+))],
), caption: [The cases of (II) and what each rests on.]) <fig-cases>

No step needed a different verdict from the checker. Two steps need a change in how the checker represents a stuck block, the knot's simulation at `MB0r` and a block's re-run: either D139's two small repairs (held, expected to change no verdict) or blocks as text (decision (b), measured: one verdict changes, a true statement now accepted).

#pagebreak()

= The evidence: programs <sec-evidence>

One section per area. Each opens with one block of programs, self-contained with the `Nat` prelude (`uses Nats`, `Ochr/Examples/Nat.lean`, which defines `Add`, `AddM`, `AddMZero`, `TailM`), each definition written `reject` where it is rejected; each block also holds the control `Ctl`, rejected every time. The blocks marked _re-run_ were run for this document on `main` at 217e22529 with `lake env lean --load-dynlib=.lake/build/lib/libochr_Ochr.so` (files in the scratchpad's `t8/`); every verdict was as written. The audit re-ran every block (`r7/`), and this revision the observation block with its four new programs (`t9/`): all as written. The table after each block says what each program shows and its verdict, today and under an experiment where one was measured ((C), (C+): the detached observation, `checker13`; text: blocks as text, `checker14`). Helpers are not listed in the tables.

== Observations <sec-ev-obs>

_Re-run_ (55 verdicts as written; `CallH`, `CallHW`, `PP`, `CallF` added in this revision):
#measured[
```
reject def Ctl : Eq(Nat, Z, S(Z)) := refl
def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
def FJ2 (n : Nat) (x : &Nat) : Unit := match n { Z => (let h : Id(Unit, *x := 0, *x := 0) = refl; ()), S(m) => (), }
def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S(m) => y, }
def S1 (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; FJ2(n, &(*r).0); (*r).1 := z; ())
reject def S1Z : Unit := S1(Z)
def S1S : Unit := S1(S(Z))
inductive Bit := B0 | B1
def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
inductive TW := MkTW(b : Bit, x : Payload(b), w : Nat)
def S2 (n : Nat) : Unit := (let t = MkTW(B0, 3, 5); match t { MkTW(b, x, w) => (b := B1; FJ2(n, &w); x := ()), })
reject def S2Z : Unit := S2(Z)
inductive Void : Type
inductive One := O
def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
inductive VW2 := MkVW2(n : Nat, x : Fin1(n), w : Nat)
def S3 (n : Nat) : Unit := (let t = MkVW2(S(Z), O, 5); let r = &t; match *r { MkVW2(k, x, w) => (k := Z; FJ2(n, &w); k := S(Z)), })
reject def S3Z : Unit := S3(Z)
def PickP (n : Nat) (x : &Pair(Nat, Nat)) (y : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => y, }
def S4 (n : Nat) (m : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let q : Pair(Nat, Nat) = Mk(3, 4); let r = PickP(m, &p, &q); *r := Mk(7, 8); let z = (*r).1; FJ2(n, &(*r).0); (*r).1 := z; ())
reject def S4Z (m : Nat) : Unit := S4(Z, m)
inductive VV := MkVV(n : Nat, x : Fin1(n))
def S5 (n : Nat) : Unit := (let t = MkVV(S(Z), O); match t { MkVV(k, x) => (FJ2(n, &k); k := S(Z)), })
reject def S5Z : Unit := S5(Z)
def FI (n : Nat) : Unit := (let h : Id(Unit, (), ()) = refl; ())
reject def CallI : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).0; FI(Z); (*r).0 := z; ())
reject def CallH : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).0; let c = 3; H(&c, refl); (*r).0 := z; ())
def CallHW : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let c = 3; H(&c, refl); ())
def PP (n : Nat) (x : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => x, }
reject def CallF (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); let z = (*r).1; H(&(*r).0, refl); (*r).1 := z; ())
reject def InFrameMoved : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; let h : Id(Unit, (), ()) = refl; (*r).1 := z; ())
reject def APick (n : Nat) : False := (let a = 0; let b = 0; let r = Pick(n, &a, &b); G5(r, refl))
reject def AAncWhole : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; G5(&(*r).0, refl))
reject def AFill (n : Nat) : False := (let a = n; let r = TailM(&a); G5(r, refl))
reject def QU (g : Π(u : &Unit). &Nat) : False := (let u = (); G5(g(&u), refl))
reject def Hide : Unit := (let x = 0; let w = 0; let y = &w; let h : Id(Unit, y := &x, (y := &x; *y := 5)) = refl; ())
def Honest : Unit := (let x = 0; let w = 0; let y = &w; let h : Id(Unit, y := &x, y := &x) = refl; ())
def Eat (r : &Nat) : Unit := ()
def A1 (n : Nat) (x : &Nat) : Id(Unit, match n { Z => Eat(x), S(m) => (), }, match n { Z => Eat(x), S(m) => (), }) := refl
def A1s : True := (let c = 0; A1(1, &c))
def Lift (x : &Nat) : Id(Unit, (let r = TailM(&*x); AddM(&*r, 0)), (let r = TailM(&*x); ())) := (let r = TailM(&*x); AddMZero(r))
def LiftR (x : &Nat) : Id(Unit, (let r = TailM(&*x); AddM(&*r, 0)), (let r = TailM(&*x); ())) := (let r = TailM(&*x); let c = clone(*r); let h = AddMZero(&c); rewrite ← h in refl)
def L (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
def Inj (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id(Unit, (let r = g(x); *r := 0), (let r = g(x); *r := 1))) : False := (let r = g(x); L(r, e))
def ConsW : Unit := (let a = 0; let r = &a; let h : Id(Unit, (let r2 = r; a := 5), (let r2 = r; *r2 := 7; a := 5)) = refl; ())
reject def IdxSame : Unit := (let t = MkVV(S(Z), O); match t { MkVV(k, x) => (let r = &k; let h : Id(Unit, *r := Z, *r := Z) = refl; ()), })
def G7 (a : Nat) (b : Nat) (x : &Nat) (y : &Nat) (e : Id(Unit, (*x := clone(a); *y := clone(b)), (*x := clone(b); *y := clone(a)))) : Unit := ()
reject def SwapCall2 (a : Nat) (b : Nat) (e : Eq(Nat, a, b) ∧ Eq(Nat, b, a)) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 5); G7(clone(a), clone(b), &p.1, &p.0, e))
def SwapCall2Ok (a : Nat) (b : Nat) (e : Eq(Nat, b, a) ∧ Eq(Nat, a, b)) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 5); G7(clone(a), clone(b), &p.1, &p.0, e))
reject def OwnR (x : &Nat) : Unit := (let r = TailM(x); let h : Id(Unit, *r := 0, *r := 1) = refl; ())
def G1 (x : &Nat) (e : Id(Unit, (*x := 0; let z = x; ()), (*x := 1; let z = x; ()))) : False := e
reject def CallG1 : False := (let a = 7; G1(&a, refl))
def F (x : &Nat) : Unit := (let h : Id(Unit, *x := 0, *x := 0) = refl; ())
def GT2 : Eq(Nat, (let c = 5; let r = TailM(&c); F(r); c), 5) := refl
```
]

#table(columns: (16%, 46%, 19%, 19%), table.header([*Program*], [*What it shows*], [*Today*], [*(C) / (C+)*]),
  [`S1`, `S1S`; `S1Z`], [Site 1: the test that a borrow ends only over a whole content (D98), at the end of a caller's borrow between the parameter and its owner. An accepted function whose call at a known argument is rejected.], [accepted; `S1Z` rejected, "a borrow ends while its content is partly moved out"], [`S1Z` accepted],
  [`S2`; `S2Z`], [Site 2: [Repack] at a caller's owner the caller holds open.], [`S2Z` rejected, "Id observes it, but it is open"], [accepted],
  [`S3`; `S3Z`], [Site 3: [Repack] at the end of a caller's borrow whose content the caller holds open.], [`S3Z` rejected], [accepted],
  [`S4`; `S4Z`], [Site 4: the same test (D98) at a caller's borrow with a sealed fill among its sites; the patch (B) keeps this one.], [`S4Z` rejected], [accepted],
  [`S5`; `S5Z`], [Site 5: [Repack] at a caller's owner the side itself opens through a borrow of an index field.], [`S5Z` rejected], [accepted],
  [`FI`, `CallI`], [With no borrow parameter at all, a callee forming an `Id` cannot be called while the caller holds a borrow partly moved: the observation ends every borrow of the whole state (the third referee's T1).], [`CallI` rejected], [accepted],
  [`CallH`, `CallHW`; `PP`, `CallF`], [The [Call-type] route: a callee's parameter type that forms an `Id` (`H`'s) is read at the call site on a private copy, and its observation ends the caller's partly moved borrow `r`; `CallF` is the same through a returned borrow (the fourth referee's F1). `CallHW` is `CallH` without the move out of `(*r).0`.], [`CallH`, `CallF` rejected, "[D53] a borrow ends while its content is partly moved out"; `CallHW` accepted], [`CallF` accepted (measured); `CallH` accepted by reading],
  [`InFrameMoved`], [The in-frame twin: an `Id` formed while the frame itself holds a borrow partly moved, which its sides never touch.], [rejected], [rejected under both],
  [`G5`; `APick`, `AAncWhole`, `AFill`, `QU`], [Attacks on resolved determination: a borrow whose owners might ignore a write. Each hypothesis is a conjunction over every fill of the hole, or `False`. `QU` is D137's: a `Unit` place's fill keeps its hole.], [all rejected], [rejected, each with hypothesis type `False`],
  [`Hide`, `Honest`], [D113: a write through a re-pointed borrow is observed.], [`Hide` rejected, `Honest` accepted], [the same],
  [`A1`, `A1s`], [D114: a side may end a borrow it consumes, on every path; before it, `A1s` was rejected while `A1` was accepted.], [accepted], [the same],
  [`Lift`, `LiftR`], [An induction hypothesis lifted through a stuck call's returned borrow.], [both accepted], [`Lift` rejected; `LiftR`'s `rewrite` repairs it],
  [`Inj`], [A lemma about an abstract borrow-returning function, true only by the injectivity of its backward function.], [accepted], [rejected, not repairable],
  [`ConsW`], [An `Id` over a local borrow whose lender a side writes after consuming the borrow: today the two sides are equal.], [accepted], [(C) accepted; (C+) rejected, type `False`],
  [`IdxSame`], [An `Id` over a local borrow of an index field: today [Repack] rejects the owner it opens.], [rejected], [(C) rejected; (C+) accepted],
  [`G7`; `SwapCall2`, `SwapCall2Ok`], [Today a statement read at a call site keeps its truth, not its form: its conjuncts follow the caller's owners.], [`SwapCall2` rejected, `SwapCall2Ok` accepted], [flipped],
  [`OwnR`], [An `Id` over a borrow a call returned from a consumed parameter: today a stuck equation over the fill.], [rejected (stuck)], [rejected, type `False`],
  [`G1`; `CallG1`], [The second referee's R1: accepted, its type `False` at the generic check; with no cell the model read its second domain as `True`, so it read `G1`'s type as empty. Fixed in the model by (M1).], [`G1` accepted, `CallG1` rejected], [the same],
  [`F`, `GT2`], [A body with an `Id` over its borrow parameter run in place, through `TailM`'s fill: the shape of the frame property's `Id` clause.], [accepted], [the same],
)

The programs of resolved determination's attack (`theory5`, the fourth referee), measured on `main` at 662110042 and 0228b0283 and re-measured under (C) and (C+) by `checker13`, each beside a twin with the true statement, accepted: a pick (`APick`, `APickZ`), a dependent field's leaf and index (`ATagLeaf`, `ATagIdx`, rejected by [Repack] today and `False` under (C)), a borrow into a moved, overwritten or partly moved value (`AMoved`, `AOver`, `AOverPart`, `APart`), through a partly moved borrow (`AAnc`, rejected by D98 today; `False` under (C)), two levels (`ATwo`), a stuck call's fill and a fill inside a fill (`AFill`, `AFill2`, `APT`), functions that overwrite or re-point after an inner call (`KF`, `KR`, `KH`, `RB`), two parameters into one owner's fields (`AG6`), `Unit` places (`APU`, `QU` to `QUN`, `GUn`): no call of `G5` with `refl` is accepted, today or under either variant. The fourth referee's `Bad` (a hypothesis built through an unchecked end of a caller's borrow returned by a closed-off call) is rejected today and accepted under (C) and (C+) with hypothesis type `False`, so `Bad(Z, refl)` is rejected: not an empty type.

== Blocks and closing off <sec-ev-block>

_Re-run_ (18 verdicts as written):
#measured[
```
reject def Ctl : Eq(Nat, Z, S(Z)) := refl
def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S(m) => y, }
reject def Clear (x : &Nat) : Id(Unit, match *x { Z => (), S(p) => p := Z, }, ()) := refl
reject def QB (n : Nat) (a : Nat) (b : Nat) : False := (let r : &Nat = match n { Z => &a, S(k) => &b, }; G5(r, refl))
reject def PickEnds (n : Nat) : Unit := (let a = 0; let b = 0; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S(m) => (), })
def MB0r (m : Nat) (n : Nat) : Nat by n := (let r = match m { Z => Z, S(p) => match n { Z => Z, S(k) => MB0r(p, k), }, }; r)
def NTr (n : Nat) (m : Nat) : Nat := match n { Z => Z, S(p) => (let r = match m { Z => clone(n), S(q) => clone(p), }; r), }
reject def ConvBlocks (q0 : Nat × Nat) : Prop := (match q0 { Mk(a, b) => Id(Nat × Nat, (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => (q0 := Mk(clone(p1), p1); q0) } }), (match q0 { Mk(p15, p16) => match p16 { Z => (p16 := 0; (1, 0)), S _ => q0 } })), })
def Blk4 (n : Nat) (x : &Nat) : Unit := (match n { Z => (let r = TailM(&*x); *r := 7), S(m) => (), }; ())
def Blk4Gen (n : Nat) (x : &Nat) : Id(Unit, Blk4(clone(n), &*x), match n { Z => (let r = TailM(&*x); *r := 7), S(m) => (), }) := match n { Z => refl, S(m) => refl, }
def Fst0 (x : &Pair(Nat, Nat)) : Unit := (*x).0 := 2
reject def Fst0Gen (x : &Pair(Nat, Nat)) : Id(Unit, Fst0(&*x), (*x).0 := 2) := refl
def DeadIll (x : &Nat) : Nat := (let k = Z; match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); S(())), })
reject def LiveIll (x : &Nat) : Nat := (let k = S(Z); match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); S(())), })
reject def DeadMoves (x : &Nat) : Nat := (let k = Z; let r = match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); 0), }; *x := 5; r)
def P2 (n : Nat) (x : &Nat) : Nat := (let q = 5; let r : &Nat = match n { Z => x, S(j) => &q, }; *r := 1; clone(q))
def UseP2c : Eq(Nat, (let c = 3; P2(Z, &c); c), 1) := refl
```
]

#table(columns: (16%, 46%, 19%, 19%), table.header([*Program*], [*What it shows*], [*Today*], [*Text*]),
  [`Clear`], [The paper's overview: a write through a pattern variable is a write to the scrutinee, so the block takes `*x` by borrow (D32), and the false statement is rejected.], [rejected], [rejected],
  [`QB`], [The first referee's O7: a borrow returned by a stuck match passed to `G5`: the hypothesis is over the block's fills.], [rejected], [—],
  [`PickEnds`], [Borrow ends are static (D90): `r` borrows `a` and `b` whether `Pick` is stuck or runs, so reading `b` ends `r` on every path.], [rejected], [—],
  [`MB0r`], [A block whose arm calls the function under check takes it as a parameter at its declared type, where the function's meaning during its own check (its stage, good only below a bound) is not a member (`lead37`, kernel-checked in the model).], [accepted], [accepted; the text names the global],
  [`NTr`], [A block that reads `n.0`, checked only at its captured `S(σ2)`; read as a function of every value it has no meaning at `n = 0`.], [accepted], [accepted; text `⌈let n = S(σ2); let m = σ1; match m {…}⌉`],
  [`ConvBlocks`], [Two blocks compared as functions at generic arguments, where a field of an abstract pair does not exist: a true statement rejected.], [rejected], [accepted],
  [`Blk4`, `Blk4Gen`], [A block's re-run agrees with the direct run, by `refl` at each instance.], [accepted], [—],
  [`Fst0`, `Fst0Gen`], [Incomplete: an untyped run's field access does not refine an unknown pair in place, so the call closes off where the typed side refines.], [`Fst0Gen` rejected], [—],
  [`DeadIll`, `LiveIll`, `DeadMoves`], [A dead arm is never checked: its capture of a borrow is accepted, the live twin rejected, and its moves feed the join.], [`DeadIll` accepted, the others rejected], [—],
  [`P2`, `UseP2c`], [[Entry]'s lending lends a parameter label at a callee place, which a later access ends: the second referee's refutation of the invariant (P).], [accepted], [—],
)
`BlkFill1` (a match's arm forming an `Id` over a borrow `Pick` returned inside the frame) is rejected today with a conjunction over the two fills and under (C+) with `False`: the block lemma's `Id` row, which under (C) still needs the fill's injectivity. `checker14`'s further probes under blocks as text: `EqJ`, `IdJ`, `DJ`, `SJ` (two `J` blocks with convertible motives of different code) rejected today, accepted under text; their false twins rejected under both.

== Recursion <sec-ev-rec>

_Re-run_ (20 verdicts as written):
#measured[
```
reject def Ctl : Eq(Nat, Z, S(Z)) := refl
inductive BB := TT | FF
reject def Loop (p : BB) (n : Nat) : Nat by n := match p { TT => match n { Z => Z, S(m) => Loop(FF, m), }, FF => Loop(FF, n), }
reject def Sel (n : Nat) : Nat by n := match n { Z => Z, S(m) => match m { Z => (let e : Eq(Nat, Sel(m), Z) = refl; Z), S(k) => Z, }, }
def Sel2 (n : Nat) : Nat by n := match n { Z => Z, S(m) => match m { Z => Z, S(k) => Z, }, }
def SelAfter : Eq(Nat, Sel2(Z), Z) := refl
reject def Q3 (n : Nat) : Nat by n := match n { Z => S(Z), S(m) => match m { Z => (let e : Eq(Nat, Q3(m), S(Z)) = refl; Z), S(k) => Z, }, }
reject def LC2 (p : BB) (n : Nat) : Nat by n := match p { TT => match n { Z => Z, S(m) => (let e : Eq(Π(u : Unit). Nat, λ(u : Unit) : Nat => LC2(FF, clone(m)), λ(u : Unit) : Nat => 0) = refl; Z), }, FF => LC2(FF, n), }
reject def AddZ (n : Nat) : Eq(Nat, Add(clone(n), Z), n) := (fix go (y : Nat) : Eq(Nat, Add(clone(y), Z), y) by y := match y { Z => refl, S(p) => go(p), })(n)
def AddZH (y : Nat) : Eq(Nat, Add(clone(y), Z), y) by y := match y { Z => refl, S(p) => AddZH(p), }
def AddZ2 (n : Nat) : Eq(Nat, Add(clone(n), Z), n) := AddZH(n)
reject def CapSplit (n : Nat) (x : Nat) : False := (fix go (y : Nat) : False by y := match n { Z => go(y), S(q) => go(y), })(x)
reject def Shadow (n : Nat) : Nat by n := (fix Shadow (y : Nat) : Nat := Shadow(y))(n)
def H1 (n : Nat) : Nat by n := match n { Z => Z, S(m) => (let f = (λ(u : Unit) : Nat => S(H1(clone(m)))); f(())), }
def UseH1 : Eq(Nat, H1(3), 3) := refl
reject def H1Bad (n : Nat) : Nat by n := match n { Z => Z, S(m) => (let k = clone(n); let f = (λ(u : Unit) : Nat => H1Bad(clone(k))); f(())), }
reject def H3 (n : Nat) : Nat by n := match n { Z => Z, S(m) => (let g = H3; g(clone(m))), }
reject def L (n : Nat) (h : Eq(Nat, n, S(Z))) : Eq(Nat, Z, S(Z)) by n := match n { Z => h, S(p) => (n := S(S(Z)); L(p, refl)), }
inductive Q : Prop := MkQ(h : And(Q, True))
reject def qe (x : Q) : False by x := (match x { MkQ(h) => match h { Intro(a, b) => qe(a) } })
```
]

#table(columns: (18%, 60%, 22%), table.header([*Program*], [*What it shows*], [*Today*]),
  [`Loop`], [D135: before it, the recursive call `Loop(FF, m)` ran the body under check, whose untested call ran for ever ("undecided").], [rejected by [Rec]],
  [`Sel`; `Sel2`, `SelAfter`], [D135's cost: an equation about the function's own call inside its body is rejected (before D135 accepted, the verdict following what the run of the body computed); stated after the definition it holds.], [`Sel` rejected; the others accepted],
  [`Q3`], [The first referee's O3: `Q2` and `Q3` differ only in their `Z` arm; before D135 `Q2` was rejected and `Q3` accepted.], [rejected],
  [`LC2`], [A second route to the body under check, through comparing two closures; D135 sits where every run of a body starts.], [rejected],
  [`AddZ`; `AddZH`, `AddZ2`], [D136's cost: a local recursive proof is rejected; its lifted form is accepted.], [`AddZ` rejected],
  [`CapSplit`], [The October proof of `False` (D78): a local recursive function capturing a value it splits on; now rejected by D136 where its check starts.], [rejected],
  [`Shadow`], [Without `by`, a function's name is not in scope in its body (D31).], [rejected],
  [`H1`, `UseH1`; `H1Bad`], [A closure that calls the enclosing global: its calls are tested by [Rec] where the closure is formed.], [`H1Bad` rejected],
  [`H3`], [The function under check occurs only as the head of a call.], [rejected],
  [`L`], [Recursion on a part of an overwritten value: [Rec] compares with the entry value as refined; by syntax it would prove `Eq(Nat, Z, S(Z))`.], [rejected],
  [`Q`, `qe`], [No recursion on a proof (redundant with the strict-subterm test).], [`qe` rejected],
)

== Inductive declarations and universes <sec-ev-decl>

These blocks were run by `theory7` (on `main` at 8153a6665) and the sixth referee (at 44a82dc84), whose checker sources are today's; the sixth referee re-ran all 193 of `theory7`'s verdicts at 44a82dc84, as written. They show what @fig-n1-checks claims, and the decisions of D107 (whose proof of `False` is `PositivitySelf.Q`: `inductive Q (A : Type) (n : Nat) := MkQ(z : Q(Q(A, n), 1), e : Eq(Nat, n, 0)) | Stop(f : Neg(A, n))` with `Neg(A, n)` `False` at zero and `Π(x : A). False` above, which made `Q(Unit, 0)` the type `Q(Unit, 0) → False`; rejected since D107).

#figure(table(columns: (25%, 15%, 22%, 38%), align: left,
  table.header([*Aim*], [*Programs*], [*Verdict*], [*If accepted: the model*]),
  [A negative occurrence behind a type function], [`B1`, `B2`], [Rejected (D36: the declared type in a call's argument).], [—],
  [… behind a parameter, a nested declaration], [`B3`, `B4`, `B14`; `NB`, `DP`, `HB`, `HA`], [`B3`, `B4`, `B14` rejected (not nestable, D107); the inner declarations accepted.], [`NB(A) = A ⊎ NB(A → Void)`, a family over #vk(0) in which `A` is not nestable; `HA`’s `A` is nestable (a whole field type), so `B13 = {MkB13(h)} ⊎ {E13}` with `h` in `HA(NegV, B13)`, a least fixed point.],
  [… behind a function type's domain, at a parameter's own type (D120’s (B2))], [`NF`, `DF`, `DG`, `DH`; `NL`, `DL`, `DL2`; `NA`, `DA`, `DA2`; `VF`], [`NF`, `DF`, `NL`, `NA` accepted; the rest rejected.], [`DF = {LeafF} ⊎ {NodeF(p)}` with `p` in `NF(DF, 0, ()) = DF`’s trees: `NF` never reads its value parameter, and the value `()` is in `NegF(X, 0)` for every `X`. A value at a parameter whose type reads the nestable parameter would have to name the declared type (`DG`, `DL2`, `DA`), read a field of it (`DA2`), or take its parameter from a hint (`DL`): each rejected. A parameter typed by a Π over an earlier type parameter cannot be declared at all (`VF`), an incompleteness.],
  [… behind an `Eq` or `Id` type], [`TE`, `B5`, `B6`, `B7`], [`TE` accepted; `B5` to `B7` rejected.], [`TE(T, a)` is `{MkTE}` (the equation is true); `T` is not nestable (passed to an equation).],
  [… behind a dependent field's type, a match in a field type], [`B2`, `B4`, `B8`, `B9`; `SelfIx`], [Rejected.], [—],
  [… a declaration at another sort], [`B11`, `B12`; `PP`, `Wrap`], [`B11`, `B12` rejected (D121).], [`PP(A)` is the truth of `A ≠ ∅`; `Wrap(P)` is `{MkWrap(•)}` or ∅.],
  [A field one universe too high, hidden the same ways], [`U1` to `U10`, `T1` to `T5`, `FA`, `FAf`], [All rejected but `FA`.], [`FA (n : Nat) : TypeA(n) := Nat` is a data-class function returning the type `Nat`; `TypeA(n)` is a type of sort `Type₁` written as a codomain, legal (D55). It cannot head a field (`FAf`, D55) and its result cannot be bound (`FAuse`, D131). Its meaning is $n |-> NN$, a member of $NN -> vk(0)$.],
  [An equation at a universe], [`TEq`, `te`, `TyEq`, `tyeq`], [Accepted.], [A proof field means $[a = b] subset.eq {bullet}$ at any type; a parameter in `Type₁` is recorded by no tree.],
  [A two-constructor proposition into data: direct, through a nested proposition, through `J`, through a match in a type], [`IsL`, `IsLT`, `IsLP`, `InAnn`, `InArg`, `InEq`, `InId`, `TagO`, `TagF`, `TagFE`, `ViaSS`, `ViaWr`, `ViaJ`, `Proj`, `ProjM`, `ProjC`], [All rejected (D45), in types and value arguments alike.], [—],
  [A `Prop`-sorted declaration whose data field a later field reads], [`ExB`, `ExP`, `Pin`, `IsTr`, `Imp`, `NestW`, `UseP`], [Accepted; `GetB`, `GetPin`, `Forge`, `exBbad` rejected.], [`ExB` is the truth of $exists b. thin deno(ty("BF"))(b) != emptyset$: true. No data leaves a proof (D45); a proof may split on the data field.],
  [Fording with a computed index], [`EvV`, `HV`, `MV`, `AV`, `VD`, `Inj`, `EvNo`], [Accepted; `ev1`, `NoRefute` rejected.], [One family over the value parameter, the index fixed by an equation field: `EvV(n)` holds the trees whose last equation is true. An index computed by a call, a match or a local write is a steady value (S3a). Injectivity at an unconvertible index field stays stuck (`NoRefute`), never `False`.],
  [The hard case `F (A : Type₁) : Type` heading a field: a constant, a match, the identity, through a declaration, into `Prop`, a domain in `Type₂`], [`WT`, `WM`, `WI`, `WB`, `WP`, `WF`, `W2`], [Accepted; `wtBad`, `wmBad`, `FId` rejected.], [`WT(A) = {MkWT(n) | n ∈ ℕ}` for every $A in vk(1)$: the family is a function from #vk(1) to #vk(0). `F`’s meaning sends every argument to a member of #vk(0), whatever its domain (`GlobalCallLevels`). `W2` writes `Type₂`, beyond the Lean model's bound but not the paper's.],
  [The standing assumption: an equation between two applications of one type former refuted], [`R1` to `R4`, `Cast`], [`R1` to `R4` rejected (the equation is stuck, never `False`); `Cast` accepted, a stuck cast.], [The model identifies `Ph(Nat)` and `Ph(Bool)`; the checker neither proves nor refutes it.],
  [A parameter read off the spine while it varies (D128’s readers)], [`T1` to `T8`], [`T1`, `T4` rejected by D128; `T2`, `T3`, `T5` by D55; `T6` to `T8` accepted.], [`T6`, `T7`: the parameter that varies is read by no field. `T8`: a written sort.],
  [Parameters inferred at a higher universe (D105)], [`ti`, `tl`, `tw`], [`ti`, `tw` accepted, `tl` rejected.], [The parameter comes from the annotation, never from the fields.],
  [Propositions whose least model is empty; recursion through them], [`Q`, `Acc1`, `N2`, `E1`, `E0`; `q`, `qn`, `qe`, `acc`], [Declarations accepted; every attempt to build or refute rejected.], [`Q`, `Acc1`, `E1` mean $emptyset$ (no base case); `N2` is the least truth of its rules. `Q` cannot be refuted either: no recursion on a proof (`qe`).],
), caption: [The attacks on N1, by aim.]) <fig-n1-attack>

*A negative occurrence, hidden.*
#measured[
```
inductive Bool := false | true
inductive Void : Type
def NegV (X : Type) : Type := (Π(x : X). Void)
def NegB (X : Type) (b : Bool) : Type := (match b { false => Unit, true => (Π(x : X). Void) })
reject inductive B1 := MkB1(f : NegV(B1))
reject inductive B2 := MkB2(b : Bool, f : NegB(B2, b))
inductive NB (A : Type) := NBase(a : A) | NStep(r : NB(NegV(A)))
reject inductive B3 := MkB3(x : NB(B3))
inductive B3Ok := MkB3Ok(x : NB(Unit))
inductive DP (A : Type) := MkDP(b : Bool, f : NegB(A, b))
reject inductive B4 := MkB4(d : DP(B4))
def NegF (X : Type) (n : Nat) : Type := (match n { Z => Unit, S _ => (Π(x : X). Void) })
inductive NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)
inductive DF := LeafF | NodeF(p : NF(DF, 0, ()))
reject inductive DG := LeafG | NodeG(p : NF(DG, 1, λ(x : DG) : Void => match x { LeafG => LeafG, NodeG(q) => LeafG }))
reject inductive DH := LeafH | NodeH(m : Nat, p : NF(DH, m, ()))
inductive TE (T : Type) (a : T) := MkTE(e : Eq(T, a, a))
reject inductive B5 := MkB5(t : TE(NegV(B5), λ(x : B5) : Void => match x { MkB5(t) => match t { MkTE(e) => λ(y : B5) : Void => y } }))
reject inductive B6 := MkB6(b : B6, e : Eq(B6, b, b))
reject inductive B7 := MkB7(e : Id(Unit, (), ()))
reject inductive B8 := MkB8(b : Bool, f : (match b { false => Unit, true => (Π(x : B8). Void) }))
reject inductive B9 := MkB9(f : (let T = Nat; T))
def NatA : Type := Nat
reject inductive B10 := MkB10(x : NatA)
inductive PP (A : Type) : Prop := MkPP(x : A)
reject inductive B11 := MkB11(q : PP(B11))
inductive Wrap (P : Prop) := MkWrap(h : P)
reject inductive B12 : Prop := MkB12(w : Wrap(B12))
def App (G : Π(X : Type). Type) (A : Type) : Type := G(A)
inductive HA (G : Π(X : Type). Type) (A : Type) := MkHA(x : A, y : App(G, Nat))
inductive B13 := MkB13(h : HA(NegV, B13)) | E13
inductive HB (G : Π(X : Type). Type) (A : Type) := MkHB(y : App(G, A))
reject inductive B14 := MkB14(h : HB(NegV, B14)) | E14
```
The reasons: `B1`, `B2`, `B6` to `B10` "fields are first-order data" (D36); `B3`, `B4`, `B14` "occurs at the parameter A of …, which is not nestable" (D107); `DG`, `B5` "reads the constructors of …, which are not known while … is declared" (D107); `DH` "the parameter f of NF has type Unit, expected ⌈NegF(DH, σ0)⌉"; `B11`, `B12` "a nested occurrence passes only through declarations of its own sort" (D121). `B10` is an incompleteness: a constant that is a type is not admitted as a field type, while a call is.]
*The site D120 left open, and parameters typed by a Π.*
#measured[
```
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
inductive NL (A : Type) (l : List(A)) := MkNL(y : A)
reject inductive DL := LeafL | NodeL(p : NL(DL, Nil))
reject inductive DL2 := LeafL2 | NodeL2(p : NL(DL2, Nil[DL2]))
reject inductive VF (A : Type) (g : Π(x : A). Nat) := MkVF(y : A)
inductive VF0 (g : Π(x : Nat). Nat) := MkVF0(y : Nat)
inductive NA (A : Type) (a : A) := MkNA(y : A)
reject inductive DA := LeafA | NodeA(p : NA(DA, LeafA))
reject inductive DA2 := LeafA2 | NodeA2(t : DA2, p : NA(DA2, t))
```
`DL`: "cannot infer the parameter A of Nil" (a bare constructor at a value argument has no hint); `DL2`: "fields are first-order data" (the argument names `DL2`); `DA`: the constructor `LeafA` "reads the constructors of DA" (D107); `DA2`: "the argument at the value parameter a of NA reads t, whose declared type DA2 mentions DA2" (D120). `VF` is rejected with "κ is not a type: its declared type is not a sort", for any Π-typed parameter whose type mentions an earlier type parameter (`VF (A : Type) (g : Π(x : A). Nat)`, likewise `Π(x : Nat). A`, `Π(x : A). B`, `Π(x : A). Type`); `VF0`, with no earlier parameter in it, is accepted. An incompleteness, and the message names a variable internal to the checker.]
*A field one universe too high, hidden.*
#measured[
```
inductive Bool := false | true
reject inductive U1 := MkU1(x : Type)
reject inductive U2 := MkU2(x : Prop)
reject inductive U3 (A : Type₁) := MkU3(x : A)
def TyF (n : Nat) : Type₁ := Type
reject inductive U4 := MkU4(x : TyF(0))
def TyM (b : Bool) : Type₁ := (match b { false => Type, true => Prop })
reject inductive U5 := MkU5(b : Bool, x : TyM(b))
def TyS (n : Nat) : Type₁ := (match n { Z => Type, S _ => Prop })
reject inductive U6 := MkU6(n : Nat, x : TyS(n))
def PiU (b : Bool) : Type₁ := (match b { false => Type, true => (Π(A : Type). A) })
reject inductive U7 := MkU7(b : Bool, x : PiU(b))
reject inductive U8 : Prop := MkU8(A : Type)
def UU (n : Nat) : Type₁ := (match n { Z => Prop, S _ => Prop })
def VV (n : Nat) : UU(n) := (match n { Z => True, S _ => True })
reject inductive U9 := MkU9(h : VV(0))
inductive Bx (A : Type) := MkBx(x : A)
reject inductive U10 := MkU10(x : Bx(Type))
inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
def te : TEq(Type, Nat, Nat) := MkTEq[Type, Nat, Nat](refl)
reject def teBad : TEq(Type, Nat, Unit) := MkTEq[Type, Nat, Unit](refl)
inductive H2 (U : Type₂) := MkH2
def h2 : H2(Type₁) := MkH2[Type₁]
```
`U1` to `U8`: "its type must be in Prop or Type" (`U6` at a stuck call, by its head's codomain; `U8` a proposition with a field in `Type₁`, which Lean allows); `U9`: D55; `U10`: "the parameter A of Bx has type Type₁, expected Type".]
*A proposition with two constructors eliminated into data.*
#measured[
```
inductive Bool := false | true
inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
inductive Tag (n : Nat) := MkTag
reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }
reject def IsLT (h : Or(True, True)) : Type := match h { Inl(p) => Nat, Inr(q) => Unit }
reject def IsLP (h : Or(True, True)) : Prop := match h { Inl(p) => True, Inr(q) => False }
reject def InAnn (h : Or(True, True)) : Unit := (let x : (match h { Inl(p) => Unit, Inr(q) => Unit }) = (); ())
reject def InArg (h : Or(True, True)) : Type := Tag(match h { Inl(p) => 0, Inr(q) => 1 })
reject def InEq (h : Or(True, True)) : Prop := Eq(Nat, match h { Inl(p) => 0, Inr(q) => 1 }, 0)
reject def InId (h : Or(True, True)) : Prop := Id(Nat, match h { Inl(p) => 0, Inr(q) => 1 }, 0)
reject inductive TagO (h : Or(True, True)) := MkTO(t : Tag(match h { Inl(p) => 0, Inr(q) => 1 }))
reject inductive TagF := MkTF(h : Or(True, True), t : Tag(match h { Inl(p) => 0, Inr(q) => 1 }))
reject inductive TagFE := MkTFE(h : Or(True, True), e : Eq(Nat, match h { Inl(p) => 0, Inr(q) => 1 }, 0))
inductive SS : Prop := MkSS(o : Or(True, True))
reject def ViaSS (s : SS) : Bool := match s { MkSS(o) => match o { Inl(p) => true, Inr(q) => false } }
def ViaSSOk (s : SS) : Bool := match s { MkSS(o) => true }
inductive Wr (P : Prop) : Prop := MkWr(x : P)
reject def ViaWr (s : Wr(Or(True, True))) : Bool := match s { MkWr(o) => match o { Inl(p) => true, Inr(q) => false } }
def InProof (h : Or(True, True)) : Eq(Nat, 0, 0) := match h { Inl(p) => (let k = 1; refl), Inr(q) => (let k = 2; refl) }
inductive Ex : Prop := Wit(n : Nat, e : Eq(Nat, n, n))
reject def Proj (x : Ex) : Nat := x.0
reject def ProjM (x : Ex) : Nat := match x { Wit(n, e) => n }
reject def ProjC (x : Ex) : Nat := match x { Wit(n, e) => clone(n) }
reject def ViaJ (h : Or(True, True)) (b : Bool) : Type := J(Bool, match h { Inl(p) => true, Inr(q) => false }, b, λ(c : Bool) : Type => Nat, refl, Nat)
```
Every rejection is D45’s "a match on a proof of … returns a non-proof, but … is not a subsingleton", in a type, an annotation, an equation's side and an inductive declaration's field type as in code. `ViaSSOk` takes apart a subsingleton (one constructor, all fields proofs) and produces data that does not depend on its field.]
*A proposition whose data field a later field reads.*
#measured[
```
inductive Bool := false | true
inductive Void : Type
def BF (b : Bool) : Type := (match b { false => Nat, true => Void })
def IsT (b : Bool) : Prop := (match b { false => False, true => True })
inductive ExB : Prop := WitB(b : Bool, x : BF(b))
inductive ExP : Prop := WitP(b : Bool, h : IsT(b))
def exB : ExB := WitB(false, 3)
def exP : ExP := WitP(true, refl)
reject def exBbad : ExB := WitB(true, 3)
def UseP (e : ExP) : Eq(Nat, 0, 0) := match e { WitP(b, h) => match b { false => match h {}, true => refl } }
reject def GetB (e : ExP) : Bool := match e { WitP(b, h) => b }
inductive Pin : Prop := MkPin(b : Bool, e : Eq(Bool, b, true))
reject def GetPin (e : Pin) : Bool := match e { MkPin(b, h) => b }
inductive IsTr (b : Bool) : Prop := MkIsTr(e : Eq(Bool, b, true))
def FromIsTr (b : Bool) (h : IsTr(b)) : Nat := match h { MkIsTr(e) => 0 }
def NestW (e : ExP) : Eq(Nat, 0, 0) := match e { WitP(b, h) => (b := true; match e { WitP(b2, h2) => (let q : Eq(Bool, b2, true) = refl; refl) }) }
reject def Forge (e : ExP) : IsT(true) := match e { WitP(b, h) => h }
inductive Imp : Prop := MkImp(n : Nat, e : Eq(Nat, S(n), 0))
def ImpE (i : Imp) : False := match i { MkImp(n, e) => match e {} }
```
`GetPin` is rejected though `Pin`’s equation determines its data field: Ochr's subsingleton rule asks every field to be a proof, stricter than Lean's (no indices). `Forge` is rejected because the arm's `h` has type ⌈`IsT(σ0)`⌉, not `⊤`.]
*Fording, with a computed index.*
#measured[
```
def Double (n : Nat) : Nat by n := (match n { Z => Z, S k => S(S(Double(k))) })
def Half (n : Nat) : Nat by n := (match n { Z => Z, S k => match k { Z => Z, S j => S(Half(j)) } })
inductive EvV (n : Nat) := EZ(h : Eq(Nat, n, Double(0))) | ES(m : Nat, r : EvV(m), h : Eq(Nat, n, Double(S(m))))
def ev2 : EvV(2) := ES(0, EZ(refl), refl)
reject def ev1 : EvV(1) := ES(0, EZ(refl), refl)
inductive HV (n : Nat) := HZ(h : Eq(Nat, n, 0)) | HS(m : Nat, r : HV(Half(m)), h : Eq(Nat, n, S(m)))
inductive MV (n : Nat) := MZ(h : Eq(Nat, n, 0)) | MS(m : Nat, r : MV(match m { Z => Z, S k => k }), h : Eq(Nat, n, S(m)))
inductive AV (n : Nat) := AZ(h : Eq(Nat, n, 0)) | AS(m : Nat, r : AV((let c = clone(m); AddM(&c, 1); c)), h : Eq(Nat, n, S(m)))
def EvNo (r : EvV(1)) : False := match r { EZ(h) => match h {}, ES(m, q, h) => match m { Z => match h {}, S k => match h {} } }
inductive VD (n : Nat) := VDN(h : Eq(Nat, n, 0)) | VDC(m : Nat, h : Eq(Nat, n, S(m)))
reject def NoRefute (a : Nat) (b : Nat) (h1 : Eq(Nat, 3, S(a))) (h2 : Eq(Nat, 3, S(b))) (e : Eq(VD(3), VDC[3](a, h1), VDC[3](b, h2))) : False := match e {}
inductive Tg (n : Nat) := MkTg
reject inductive SelfIx := SL | SN(t : SelfIx, r : Tg(match t { SL => 0, SN(u, v) => 1 }))
```
`NoRefute`: "[Match] on e, whose type Eq(VD(3), VDC(σ0, ⋆), VDC(σ1, ⋆)) is not an inductive type": `m` is an index field, so injectivity waits for it (D64), and the equation is never `False`. With the cases on `a` and `b` written out, `a = b` is proved (`Inj`, accepted). `SelfIx`: D107.]
*The hard case: a global with a domain in `Type₁` heading a field's type.*
#measured[
```
inductive Bool := false | true
def FT (A : Type₁) : Type := Nat
inductive WT (A : Type₁) := MkWT(x : FT(A))
def wt : WT(Type) := MkWT[Type](3)
def wt2 : WT(Π(X : Type). X) := MkWT[Π(X : Type). X](4)
reject def wtBad : WT(Type) := MkWT[Type](())
def FM (A : Type₁) (b : Bool) : Type := (match b { false => Nat, true => Unit })
inductive WM (A : Type₁) := MkWM(b : Bool, x : FM(A, b))
def wm : WM(Prop) := MkWM[Prop](true, ())
reject def wmBad : WM(Prop) := MkWM[Prop](true, 3)
def FI (A : Type₁) (B : Type) : Type := B
inductive WI (A : Type₁) (B : Type) := MkWI(x : FI(A, B))
def wi : WI(Type, Nat) := MkWI[Type, Nat](5)
reject def FId (A : Type₁) : Type := A
inductive Big (U : Type₁) := MkBig(n : Nat)
def FB (A : Type₁) : Type := Big(A)
inductive WB (A : Type₁) := MkWB(x : FB(A))
def wb : WB(Type) := MkWB[Type](MkBig[Type](1))
def FP (A : Type₁) : Prop := Eq(Type₁, A, A)
inductive WP (A : Type₁) := MkWP(h : FP(A))
def wp : WP(Prop) := MkWP[Prop](refl)
def FF (G : Π(X : Type₁). Type) : Type := G(Prop)
inductive WF (G : Π(X : Type₁). Type) := MkWF(x : FF(G))
def wf : WF(λ(X : Type₁) : Type => Nat) := MkWF[λ(X : Type₁) : Type => Nat](7)
def F2 (A : Type₂) : Type := Nat
inductive W2 (A : Type₂) := MkW2(x : F2(A))
def w2 : W2(Type₁) := MkW2[Type₁](8)
```
Each declaration's family is a function from its parameters' universe to #vk(0): for every $A in vk(1)$, `WT(A)` holds the trees `MkWT(n)` for $n in NN$, `WB(A)` the trees `MkWB(MkBig(n))`, `WM(A)` the dependent sum of `FM(A, b)` over `b`, and `WF(G)` the trees whose field lies in `G`’s value at `Prop`. In each, the field's type is a call whose result the model places in #vk(0) because the global's codomain is `Type` (or `Prop`), whatever its domain.]
*The identification of types, and the readers behind D128.*
#measured[
```
inductive Bool := false | true
inductive Big (U : Type₁) := MkBig
inductive Ph (A : Type) := MkPh
reject def R1 (h : Eq(Type, Big(Type), Big(Prop))) : False := match h {}
reject def R2 (h : Eq(Type, Ph(Nat), Ph(Bool))) : False := match h {}
reject def R3 (h : Id(Type, Ph(Nat), Ph(Bool))) : False := match h {}
reject def R4 (h : Eq(Ph(Nat), MkPh[Nat], MkPh[Nat])) : False := match h {}
def R4ok : Eq(Ph(Nat), MkPh[Nat], MkPh[Nat]) := refl
def Cast (h : Eq(Type, Ph(Nat), Ph(Bool))) (x : Ph(Nat)) : Ph(Bool) := J(Type, Ph(Nat), Ph(Bool), λ(X : Type) : Type => X, h, x)
def TyAlias : Type₁ := Type
def SortF (X : Type) : Type₁ := Type
reject inductive T1 (A : Type) (B : (let z = A; Type)) := MkT1(x : B)
reject inductive T2 (A : Type) (B : TyAlias) := MkT2(x : B)
reject inductive T3 (A : Type) (B : SortF(A)) := MkT3(x : B)
reject inductive T4 (A : Type) (B : (match 0 { Z => Type, S _ => Type })) := MkT4(x : B)
reject inductive T5 (A : Type) (B : (Type : Type₁)) := MkT5(x : B)
inductive T6 (A : Type) (B : TyAlias) := MkT6(n : Nat)
inductive T7 (A : Type) (B : SortF(A)) := MkT7(n : Nat)
inductive T8 (A : Type) (B : (Type)) := MkT8(x : B)
inductive TE (U : Type₁) (a : U) := MkTE(h : Eq(U, a, a))
def ti : TE(Type, Nat) := MkTE(refl)
reject def tl : Unit := (let x = MkTE(refl); ())
def tw : TE(Type, Nat) := MkTE[Type, Nat](refl)
```
`R1` to `R3`: "[Match] on h, whose type Eq(Type, …, …) is not an inductive type": the equation is stuck; `R4`: its type is `True`, which has a constructor. `T1`, `T4`: D128; `T2`, `T3`, `T5`: "[D55] B is written where a type is expected, but its declared type is not a sort", the reader not seeing through a constant, a call or an ascription, where D128’s reader agrees, so `B` is a value parameter for both. `tl`: "cannot infer the parameter U of MkTE" (D105).]
*Propositions whose least model is empty.*
#measured[
```
inductive Bool := false | true
inductive Q : Prop := MkQ(h : And(Q, True))
reject def q : Q := MkQ(⟨q, refl⟩)
reject def qn (n : Nat) : Q by n := (match n { Z => MkQ(⟨qn(n), refl⟩), S m => MkQ(⟨qn(m), refl⟩) })
reject def qe (x : Q) : False by x := (match x { MkQ(h) => match h { Intro(a, b) => qe(a) } })
inductive Acc1 : Prop := MkAcc1(h : Acc1)
def fromAcc (a : Acc1) : Nat := (match a { MkAcc1(h) => 0 })
reject def acc : Acc1 := MkAcc1(acc)
inductive N2 (P : Prop) (n : Nat) : Prop := MkN2(z : N2(N2(P, n), 1), e : Eq(Nat, n, 0)) | StopN2(a : P)
def n2 : N2(True, 0) := MkN2[True, 0](StopN2[N2(True, 0), 1](StopN2[True, 0](refl)), refl)
reject def n2f : N2(False, 1) := StopN2[False, 1](refl)
def TypeA (n : Nat) : Type₁ := Type
def FA (n : Nat) : TypeA(n) := Nat
reject def FAuse (n : Nat) : Nat := (let T = FA(n); 0)
reject inductive FAf := MkFAf(x : FA(0))
inductive E0 : Type
inductive E1 := MkE1(e : E1)
def e1f (x : E1) : False by x := (match x { MkE1(y) => e1f(y) })
inductive TyEq (U : Type₁) (A : U) := MkTyEq(e : Eq(U, A, A))
def tyeq : TyEq(Type, Nat) := MkTyEq[Type, Nat](refl)
```
`q`, `acc`: a definition does not name itself (D118); `qn`: [Rec], the recursive call is on `n`; `qe`: "the decreasing parameter must have an inductive type", a proof having no rank. `Q` and `Acc1` mean $emptyset$ in the least model, and the checker can neither build nor refute them; `E1` means $emptyset$ and `e1f`, accepted, is true there. `FAuse`: D131; `FAf`: D55.]
*Checks stricter than the construction needs (the sixth referee's Y2; decision (d)).*
#measured[With the `Nat` prelude, on `main` at 44a82dc84:
```
inductive Bool := false | true
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
inductive Pt (A : Type) (a : A) := MkPt
reject inductive D2 := D2Leaf | D2Node(x : D2, p : Pt(D2, x))
reject inductive LD := LLeaf | LDNode(xs : List(LD), e : Eq(Nat, (match xs { Nil => 0, Cons(h, t) => 1 }), 1))
inductive NA (A : Type) (a : A) := MkNA(y : A)
inductive NB (A : Type) := MkNB(x : A, r : NA(A, x))
reject inductive NBD := LNB | NNB(m : NB(NBD))
inductive PP (A : Type) : Prop := MkPP(x : A)
reject inductive B11 := MkB11(q : PP(B11))
inductive Wrap (P : Prop) := MkWrap(h : P)
reject inductive B12 : Prop := MkB12(w : Wrap(B12))
reject inductive B6 := MkB6(b : B6, e : Eq(B6, b, b))
inductive TE (T : Type) (a : T) := MkTE(e : Eq(T, a, a))
inductive TB (T : Type) := MkTB(x : T, t : TE(T, x))
reject inductive TBD := LTB | NTB(m : TB(TBD))
reject inductive Q11 := L11 | N11(p : NA(Q11, L11))
def PF (b : Bool) : Type := (match b { false => Nat, true => (Π(x : Nat). Nat) })
inductive DPF := MkDPF(b : Bool, f : PF(b))
def dpf : DPF := MkDPF(true, λ(x : Nat) : Nat => S(x))
def NegT (X : Type) : Type := (Π(x : X). Bool)
reject inductive NT := MkNT(x : NegT(Nat))
```
All 22 verdicts as written. `D2`, `LD`: D120 ("… reads x, whose declared type D2 mentions D2 …"); `NBD`: "NBD occurs at the parameter A of NB, which is not nestable in NB: a field of NB reads … a variable whose declared type mentions it" (D120); `B11`, `B12`: D121; `B6`: D36; `TBD`: "TB passes it to … an equation"; `Q11`: "the constructor L11 reads the constructors of Q11, which are not known while Q11 is declared (D107)"; `NT`: "NegT(Nat) computes to Π(x : κ1). Bool …, which is not first-order data, D36".]
*The standing assumption (the sixth referee's Y4).*
#measured[With the `Nat` prelude, on `main` at 44a82dc84:
```
inductive Bool := false | true
inductive E1 : Type
inductive E2 : Type
inductive T2 : Prop := MkT2
inductive Ph (A : Type) := MkPh
reject def EE (h : Eq(Type, E1, E2)) : False := match h {}
reject def PT (h : Eq(Prop, True, T2)) : False := match h {}
reject def EP (h : Eq(Type, Ph(Nat), Ph(Bool))) : False := match h {}
reject def MoveTy (U : Type₁) (a : U) : U := (let b = a; let c = a; b)
def MoveTyOk (U : Type₁) (a : U) : U := (let b = a; b)
reject def IdTy (U : Type₁) (a : U) (n : U) : Prop := Id(Unit, (let z = a; ()), (let z = a; a := n))
inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
reject def CT1 (y : TEq(Type, Ph(Nat), Ph(Nat))) : TEq(Type, Ph(Nat), Ph(Bool)) := y
reject def NoTEq (t : TEq(Type, Ph(Nat), Ph(Bool))) : False := match t { MkTEq(h) => match h {} }
```
All 14 verdicts as written. `EE`, `PT`, `EP`, `NoTEq`: "[Match] on h (t.h), whose type Eq(…) is not an inductive type"; `MoveTy`: "[Read] a was moved out or its borrow ended (reading ⊥)"; `IdTy`: "[Id-typestate] the left side of Id moves a, the right side does not"; `CT1`: not convertible. In the model `TEq(Type, Ph(Nat), Ph(Bool))` is ${ty("MkTEq")(bullet)}$, inhabited, and the checker neither builds nor refutes it.]
*Value-indexed nesting at a field variable; data holding borrow-returning functions (Y5).*
#measured[With the `Nat` prelude, on `main` at 44a82dc84:
```
inductive Bool := false | true
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
inductive VL (n : Nat) := VLeaf(e : Eq(Nat, n, 0)) | VNode(m : Nat, r : List(VL(m)), e : Eq(Nat, n, S(m)))
def vl : VL(1) := VNode(0, Cons[VL(0)](VLeaf(refl), Nil[VL(0)]), refl)
def PB (b : Bool) : Type := (match b { false => Nat, true => (Π(x : &Nat). &Nat) })
inductive DPB := MkDPB(b : Bool, f : PB(b))
def dpb : DPB := MkDPB(true, λ(x : &Nat) : &Nat => x)
def UseDPB (d : DPB) (y : &Nat) : Unit := match d { MkDPB(b, f) => match b { false => (), true => (let r = f(y); *r := 0) } }
```
All 8 verdicts as written: every declaration and definition accepted.]
*Places beyond Lean, attacked.*
#measured[With the `Nat` prelude, on `main` at 44a82dc84:
```
inductive Bool := false | true
inductive Void : Type
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
def FD (b : Bool) : Type := (match b { false => Unit, true => Nat })
inductive SelfD := L0 | N0(b : Bool, x : FD(b))
def FE (n : Nat) (e : Eq(Nat, n, 0)) : Type := (match n { Z => Nat, S _ => (let k : Void = match e {}; Unit) })
inductive DE := MkDE(n : Nat, e : Eq(Nat, n, 0), x : FE(n, e))
def de : DE := MkDE(0, refl, 5)
def Len (A : Type) (xs : List(A)) : Nat by xs := (match xs { Nil => Z, Cons(h, t) => S(Len(A, t)) })
def TyOfLen (n : Nat) : Type := (match n { Z => Unit, S _ => Void })
reject inductive NI2 := LN2 | NN2(xs : List(NI2), y : TyOfLen(Len(NI2, xs)))
def Pick (b : Bool) (A : Type) (B : Type) : Type := (match b { false => A, true => B })
inductive MP (A : Type) := MkMP(b : Bool, x : Pick(b, A, Nat))
reject inductive MQ := LQ | NQ(m : MP(MQ))
inductive PN (P : Prop) (n : Nat) : Prop := PA(z : PN(PN(P, n), 1), k : Nat) | PB(a : P, j : Nat)
def pn : PN(True, 0) := PB[True, 0](refl, 3)
reject def D1 (h : PN(True, 0)) : Bool := match h { PA(z, k) => true, PB(a, j) => false }
reject def D2 (h : PN(True, 0)) : Bool := match h { PA(z, k) => match z { PA(z2, k2) => true, PB(a2, j2) => false }, PB(a, j) => false }
def D3 (h : PN(True, 0)) : True := match h { PA(z, k) => (let q : Eq(Nat, k, k) = refl; refl), PB(a, j) => refl }
reject def D4 (h : PN(True, 0)) : Nat := match h { PA(z, k) => k, PB(a, j) => j }
reject def D5 (h : PN(True, 0)) : Type := J(Bool, match h { PA(z, k) => true, PB(a, j) => false }, true, λ(c : Bool) : Type => Nat, refl, Nat)
inductive WP (P : Prop) : Prop := MkWP(w : P)
def D6 (h : WP(PN(True, 0))) : Bool := match h { MkWP(w) => true }
reject def D7 (h : WP(PN(True, 0))) : Bool := match h { MkWP(w) => match w { PA(z, k) => true, PB(a, j) => false } }
reject def D9 (h : PN(True, 0)) : Bool := (let f = (λ(u : Unit) : Bool => (match h { PA(z, k) => true, PB(a, j) => false })); f(()))
def PT (b : Bool) : Prop := (match b { false => True, true => PN(True, 0) })
reject def D13 (b : Bool) (h : PT(b)) : Bool := match b { false => true, true => match h { PA(z, k) => true, PB(a, j) => false } }
def D14 (h : And(True, PN(True, 0))) : Bool := match h { Intro(l, r) => true }
reject def D15 (h : And(True, PN(True, 0))) : Bool := match h { Intro(l, r) => match r { PA(z, k) => true, PB(a, j) => false } }
```
All 29 verdicts as written. `NI2`: D36 (the call's argument is not first-order); `MQ`: "MQ occurs at the parameter A of MP, which is not nestable in MP"; `D1`, `D2`, `D4`, `D5`, `D7`, `D9`, `D13`, `D15`: "[D45] a match on a proof of PN returns a non-proof, but PN is not a subsingleton (it has 2 constructors)". `D3`, `D6`, `D14` accepted: a proof built from a data field bound as a local, and constant data from a subsingleton.]
*Names, levels and borrows.*
#measured[With the `Nat` prelude, on `main` at 44a82dc84:
```
inductive Bool := false | true
reject inductive RZ := Z | S(x : RZ)
reject inductive Q7 (n : Nat) (x : (match Z { Z => Nat, S(k) => (let w = MkQ7; Nat) })) := MkQ7
reject inductive Q9 (b : Bool) (x : (match b { false => Nat, true => Q9(b, 0) })) := MkQ9
inductive Box (A : Type) := MkBox(x : A)
def SortF (X : Type) : Type₁ := Type
reject inductive T10 (A : Type) (B : SortF(A)) := MkT10(x : Box(B))
def PiAll : Type₁ := (Π(X : Type). X)
reject def BorrowPi (x : &PiAll) : Unit := ()
def TF1 (n : Nat) : Type₁ := (Π(X : Type). X)
reject def BorrowCall (n : Nat) (x : &TF1(n)) : Unit := ()
reject def BorrowProp (P : Prop) (x : &P) : Unit := ()
reject def BorrowPiProp (x : &(Π(n : Nat). Eq(Nat, n, n))) : Unit := ()
def IdT (A : Type₁) : Type₁ := A
reject def BorrowIdT (x : &IdT(Type)) : Unit := ()
inductive Big (U : Type₁) := MkBig
def BorrowBig (x : &Big(Type)) : Unit := ()
```
All 17 verdicts as written. `RZ`: "(surface) Z is built in"; `Q7`, `Q9`: D133, the own name or its constructor in a dead arm of a parameter's type; `T10`: "[D55] B is written where a type is expected, but its declared type is not a sort" (a value parameter at a type argument; D55 and D128 are what keep one out, since `Term.nestOk` accepts a bare variable at a nestable position whatever its declared type reads, and only a type parameter written as a sort reads nothing); each `Borrow…` rejected: "[D66] … is not in Type₀", the Π over `Type` hidden behind a constant, a call and an identity at `Type₁`.]

== Proofs, erasure and conversion <sec-ev-proof>

_Re-run_ (44 verdicts as written):
#measured[
```
reject def Ctl : Eq(Nat, Z, S(Z)) := refl
def PropF (n : Nat) : Type₁ := Prop
reject def V1 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : PropF(x) => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())
def W2 (x : &Nat) : Unit := ((*x := 7; J(Nat, Z, Z, λ(z : Nat) : PropF(z) => ⊤, refl, refl)); ())
def W2Runs : Eq(Nat, (let c = 0; W2(&c); c), 7) := refl
def WP2 (x : &Nat) : Unit := ((*x := 7; J(Nat, Z, Z, λ(z : Nat) : Prop => ⊤, refl, refl)); ())
def WP2Runs : Eq(Nat, (let c = 0; WP2(&c); c), 0) := refl
def G5T (x : &Nat) : Prop := Id(Unit, *x := 0, *x := 1)
def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
reject def PEx (e : Ex) : False := match e { Wit(w, h) => G5(&w, refl), }
def PB (e : Ex) : True := match e { Wit(w, h) => (let r = &w; refl), }
def PExF (e : Ex) : True := match e { Wit(w, h) => (let t : Prop = G5T(&w); let f = (λ(k : t) : Eq(Nat, Z, S(Z)) => match k {}); refl), }
reject def PW (e : Ex) : True := match e { Wit(w, h) => (let q : Eq(Nat, w, 0) = refl; refl), }
def Nest (e : Ex) : True := match e { Wit(w, h) => (w := 5; match e { Wit(w2, h2) => (let q : Eq(Nat, w2, 5) = refl; refl), }), }
inductive Succ : Prop := MkSucc(n : Nat, m : Nat, h : Eq(Nat, n, S(m)))
reject def Boom (e : Succ) : Eq(Nat, Z, S(Z)) := match e { MkSucc(n, m, h) => (n := Z; match e { MkSucc(n2, m2, h2) => match h2 {}, }), }
inductive Bool := false | true
inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }
reject def ProjM (x : Ex) : Nat := match x { Wit(n, e) => n }
inductive Pin : Prop := MkPin(b : Bool, e : Eq(Bool, b, true))
def Leak (p : Pin) : True := (let q = match p { MkPin(b, e) => e }; refl)
reject def LShow (p : Pin) : True := (let q = match p { MkPin(b, e) => e }; let t : True = q; refl)
reject def LRw (g : Π(b : Bool). Bool) (c : Bool) (h : Eq(Bool, g(true), c)) (p : Pin) : Eq(Bool, g(true), c) := (let q = match p { MkPin(b, e) => e }; rewrite q in h)
def UseEq (x : Bool) (h : Eq(Bool, x, true)) : True := refl
reject def LPass (p : Pin) : True := (let q = match p { MkPin(b, e) => e }; UseEq(true, q))
reject def LTwo (p : Pin) : True := (let q = match p { MkPin(b, e) => e }; let k : False = match q {}; refl)
def TF (n : Nat) : Type := match n { Z => Unit, S(m) => Nat, }
def F (n : Nat) : Unit := ()
def H (n : Nat) : TF(Z) := ()
def FH : Eq(Π(n : Nat). Unit, F, H) := refl
def TwiceF (n : Nat) : Unit := (let r = F(n); let a = r; let b = r; ())
reject def TwiceH (n : Nat) : Unit := (let r = H(n); let a = r; let b = r; ())
def G1 (x : Nat) : Nat := match x { Z => Z, S(p) => S(Z), }
def G2 (x : Nat) : Nat := match x { Z => Z, S(p) => Z, }
reject def G12 : Eq(Π(x : Nat). Nat, G1, G2) := refl
inductive Void : Type
inductive One := O
def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
inductive V := MkV(n : Nat, x : Fin1(n))
reject def BoomF : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := refl; n := Z; let z : Void = match x {}; z), })
def Keep (r : &One) : &One := r
reject def A2 : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let k : Void = x; k), })
```
]

#table(columns: (18%, 60%, 22%), table.header([*Program*], [*What it shows*], [*Today*]),
  [`PropF`, `V1`], [D131: a proof read as data behind a hidden sort; before it `V1` was accepted and `V1(Z)` rejected.], [`V1` rejected],
  [`W2`, `W2Runs`; `WP2`, `WP2Runs`], [Principle 3's converse is false: a term of type `⊤` whose sort hides behind a call reads as data and writes `7`; with `Prop` written it is erased and writes nothing. Not a route to `False`.], [all accepted],
  [`PEx`; `PB`, `PExF`; `PW`], [A proof's data fields are compared by the checker (as locals since D138): `PEx` would be a closed proof of `False` were they compared as `•`; `PExF` relies on the finer reading.], [`PEx`, `PW` rejected; `PB`, `PExF` accepted],
  [`Nest`; `Boom`], [D138: a nested match on the same proof sees the outer arm's write; a proof field's type is fixed when the arm starts.], [`Nest` accepted, `Boom` rejected],
  [`IsL`, `ProjM`], [Subsingleton elimination (D45).], [rejected],
  [`Leak`; `LShow`, `LRw`, `LPass`, `LTwo`], [An erased match's arm unknown escapes through its type and was used for nothing in these attempts; argued harmless by one author (@sec-proof-fields).], [`Leak` accepted; the rest rejected],
  [`F`, `H`, `FH`, `TwiceF`, `TwiceH`], [Two convertible functions differ in a reading (copy against move of a call's result), which changes what a context written with the name may do, not what a value means.], [`TwiceH` rejected; the rest accepted],
  [`G12`], [The least relation: two functions whose generic calls are both stuck are not identified.], [rejected],
  [`BoomF`], [The proof of `False` of D110: `⋆` stored in a data field by a strong update, read at its declared type.], [rejected],
  [`A2`], [The proof of `False` of D112's amendment: a field lent to a call's returned borrow read at its declared type.], [rejected],
)

*Conversion at a type* (N3t), run by `theory7` on `main` at 8153a6665, re-run by the sixth referee; 23 verdicts as written:
#measured[With the `Nat` prelude, on `main` at 8153a6665:
```
inductive Bool := false | true
inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
inductive Box2 (P : Prop) := MkB2(h : P)
def U1 (Q : Prop) (x : Box2(And(True, Q))) : Box2(Q) := x
def U2 (Q : Prop) (x : Box2(Q)) : Box2(And(Q, True)) := x
reject def U3 (Q : Prop) (x : Box2(And(Q, Q))) : Box2(Q) := x
def S1 (h : And(True, Or(True, True))) : Bool := match h { Intro(l, r) => true }
def S2 (h : Or(True, True)) : Bool := S1(h)
reject def S3 (h : And(True, Or(True, True))) : Bool := match h { Intro(l, r) => match r { Inl(p) => true, Inr(q) => false } }
def I1 (a : Nat) (b : Nat) (h : Eq(Pair(Nat, Nat), Mk(a, b), Mk(b, a))) : Eq(Nat, a, b) := match h { Intro(l, r) => l }
def I2 (h : Eq(Bool, true, false)) : False := match h {}
inductive UP (u : Unit) := MkUP
def E1 (x : Unit) (y : UP(x)) : UP(()) := y
def UU (n : Nat) : Type := (match n { Z => Unit, S _ => Nat })
inductive UQ (n : Nat) (u : UU(n)) := MkUQ
reject def E2 (u : UU(0)) (v : UU(0)) (y : UQ(0, u)) : UQ(0, v) := y
inductive HT (f : Π(x : Nat). Type) := MkHT
def F1 (y : HT(λ(x : Nat) : Type => Nat)) : HT(λ(z : Nat) : Type => Nat) := y
reject def F2 (y : HT(λ(x : Nat) : Type => Nat)) : HT(λ(z : Nat) : Type => Unit) := y
inductive Big (U : Type₁) := MkBig
reject def B1 (y : Big(Type)) : Big(Prop) := y
def PA : Type₁ := Prop
reject def P1 (f : Π(x : Nat). Prop) : (Π(x : Nat). PA) := f
```
All 23 verdicts as written. The unit laws act inside a type argument (`U1`, `U2`) and nothing more (`U3`). `S2` passes a two-constructor proof where a subsingleton is declared, and `S1`’s result does not depend on it; taking `r` apart into data is rejected (`S3`, D45). η at `Unit` reaches a parameter declared `Unit` (`E1`) and not one that is `Unit` only by computation (`E2`). Function-valued arguments are compared by their generic calls (`F1`, `F2`). `B1` and `P1`: types the model identifies or that differ in class are not converted.]

== The frame property's shapes <sec-ev-frame>

_Re-run_ (38 verdicts as written):
#measured[
```
reject def Ctl : Eq(Nat, Z, S(Z)) := refl
def P4 (n : Nat) (x : &Nat) (y : &Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 6); let r1 : &Nat = match n { Z => x, S(j) => &p.0, }; let r2 : &Nat = match n { Z => y, S(j) => &p.1, }; *r1 := 1; *r2 := 2; let z = p; ())
def UseP4a : Eq(Nat, (let a = 3; let b = 4; let ry = &a; P4(Z, &b, ry); a), 2) := refl
def P5 (n : Nat) (x : &Nat) (y : &Nat) : Unit := (let r : &Nat = match n { Z => (let w = x; y), S(j) => x, }; *r := 1; ())
def UseP5a : Eq(Nat, (let a = 3; let b = 4; P5(Z, &a, &b); b), 1) := refl
def P8 (n : Nat) (x : &Nat) : Nat := (let q = 5; let r : &Nat = match n { Z => x, S(j) => &q, }; *r := 1; let f = (λ(u : Unit) : Nat => clone(q)); f(()))
def UseP8 : Eq(Nat, (let c = 3; P8(Z, &c); c), 1) := refl
def W2 (x : &Nat) : (*x := 7; Eq(Nat, *x, 7)) := refl
reject def W3 (x : &Nat) (y : (*x := 7; Nat)) : Eq(Nat, *x, 7) := refl
def W4 (x : &Nat) (y : (*x := 7; Nat)) : Unit := ()
def UseW4 : Eq(Nat, (let c = 3; W4(&c, 0); c), 3) := refl
def PiMove : Nat := (let a = 5; let T = (Π(u : Unit). Eq(Nat, a, 5)); a)
def PiLentEq : Eq(Nat, (let a = 5; let r = &a; let T = (Π(u : Unit). Eq(Nat, a, 5)); *r := 6; a), 6) := refl
reject def FixMove : Nat := (let a = 5; let f = (λ(u : Unit) : Nat => clone(a)); a)
def PickF (n : Nat) (a : &(Π(x : Nat). Nat)) (b : &(Π(x : Nat). Nat)) : &(Π(x : Nat). Nat) := match n { Z => a, S(k) => b, }
def Inc (x : Nat) : Nat := S(x)
def T5 (n : Nat) : Nat := (let g = Inc; let h = Inc; let r = PickF(clone(n), &g, &h); match n { Z => (let a = g(0); g(1)), S(m) => 0, })
def T5Z : Nat := T5(0)
inductive Void : Type
inductive One := O
def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
inductive V := MkV(n : Nat, x : Fin1(n))
reject def RdWhileFilled (v0 : V) : Unit := (let v = v0; match v { MkV(n, x) => (let r = TailM(&n); let y = x; let z : One = y; *r := Z; ()), })
def PickP (n : Nat) (x : &Pair(Nat, Nat)) (y : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => y, }
def TwoParts (n : Nat) : Nat := (let a : Pair(Nat, Nat) = Mk(1, 2); let b : Pair(Nat, Nat) = Mk(3, 4); let c : Pair(Nat, Nat) = Mk(5, 6); let r = PickP(n, &a, &b); let q1 = &(*r).0; let q2 = &(*r).1; r := &c; *q1 := 7; *q2 := 8; let z = a; let w = b; 0)
reject def TwoPartsBad (n : Nat) : Nat := (let a : Pair(Nat, Nat) = Mk(1, 2); let b : Pair(Nat, Nat) = Mk(3, 4); let c : Pair(Nat, Nat) = Mk(5, 6); let r = PickP(n, &a, &b); let q1 = &(*r).0; let q2 = &(*r).1; r := &c; let z = clone(a.1); *q2 := 8; 0)
def IsSuccN (n : Nat) : Prop := match n { Z => False, S(m) => ⊤, }
def IsSuccFst (p : Pair(Nat, Nat)) : Prop := match p { Mk(a, b) => IsSuccN(a), }
def IsSuccSnd (p : Pair(Nat, Nat)) : Prop := match p { Mk(a, b) => IsSuccN(b), }
inductive PS := MkPS(p : Pair(Nat, Nat), h : IsSuccSnd(p))
inductive PF2 := MkPF2(p : Pair(Nat, Nat), h : IsSuccFst(p))
def Fst (x : &Pair(Nat, Nat)) : &Nat := &(*x).0
def ReSnd : Unit := (let c = MkPS(Mk(0, 1), refl); match c { MkPS(p, h) => (let r = Fst(&p); h := refl; *r := 5; let z = c; ()), })
reject def ReFst : Unit := (let c = MkPF2(Mk(1, 1), refl); match c { MkPF2(p, h) => (let r = Fst(&p); h := refl; *r := 0; let z = c; ()), })
reject def GetN (v : &V) : &Nat := match *v { MkV(n, x) => &n, }
inductive Tag (A : Type) (n : Nat) := MkTag
def Wr (A : Type) (x : &Nat) : Tag(A, *x) := (*x := 0; MkTag)
def UseWr : Eq(Tag(Nat, 5), (let c = 5; Wr(Nat, &c)), (MkTag : Tag(Nat, 5))) := refl
```
]

#table(columns: (18%, 60%, 22%), table.header([*Program*], [*What it shows*], [*Today*]),
  [`P4`, `UseP4a`], [One access ends two parameter labels in an order the renaming reverses; the states agree by commutation of ends (I4).], [accepted],
  [`P5`, `UseP5a`], [A parameter label lent at another parameter's lender (the third referee's T7: (I3) in a detail).], [accepted],
  [`P8`, `UseP8`], [A closure formed in the body over a place lent to a parameter: its capture's access ends the parameter's label.], [accepted],
  [`W2`; `W3`; `W4`, `UseW4`], [(M1): a parameter type's run leaves nothing behind, as the generic state's does.], [`W3` rejected],
  [`PiMove`, `PiLentEq`; `FixMove`], [A Π-type's captures are read on a copy (no access, no move); a closure's are real: why (M2)'s `.pi` is not `.fix`'s.], [`FixMove` rejected],
  [`T5`, `T5Z`], [The `inPlace` flag survives a sealed re-run between its set and its read (`nfSealed` restores the state); prediction refuted.], [accepted],
  [`RdWhileFilled`], [(WF11): a tree field read while its index is lent to a stuck call takes its content's type, which has no hole.], [rejected],
  [`TwoParts`; `TwoPartsBad`], [(WF12): two parts of a returned borrow lent onward, then the borrow ended: reading one field of its lender ends both, on every path.], [`TwoPartsBad` rejected],
  [`ReSnd`; `ReFst`; `GetN`], [N7 and principle 9: a proof field re-proved while an index is lent holds only if it reads no part the borrow may still write; a lent index read at a whole-again point (`GetN`, the proof of `False` of D73) is rejected.], [`ReSnd` accepted; the others rejected],
  [`Wr`, `UseWr`], [N9: a body whose codomain mentions a borrow argument gets its hint at the call point, before the body writes.], [accepted],
)

#pagebreak()

= Appendix <sec-appendix>

== The ledger of decisions, by principle <sec-ledger>

Every entry of `ochr/core/DECISIONS.md` (D1 to D134, with amendments), the rulings D135 to D138 recorded in docs/32, and the eight accepted proofs of `False` since October, each in one row: the decision in words with its number after, what went wrong (or, for a design choice that fixed no fault, what it decides), the principle of @sec-principles it restores or establishes, and the principle written before 27 November it fits, if any (docs/18's seven of 2 November: locality, closing off, worlds, wholeness, erasure and captures, recursion, observation; or `CLAUDE.md`'s three standards: no catch-and-default, total code, decisions never read a run). "Design" marks a founding choice and "feature" an addition that repairs nothing. Where a row has two principles, the first is the one the fix restores. Later rulings: D136 (local functions are not recursive) restores principle 10's order and removes the case D78 repaired; D137 and D138 correct the documents to the checker (principles 6 and 3); D139 (blocks name a function under check by its global, held for decision (b)) restores principle 4.

#let L(..xs) = table(columns: (17%, 52%, 13%, 18%), align: left, table.header([*Decision*], [*What went wrong, or what it decides*], [*Principle*], [*Written before as*]), ..xs)

=== The early rounds: D1 to D44

#L(
  [Normalisation by a symbolic machine (D1)], [Design: equality is "same normal form".], [design], [—],
  [A formed type is a closed statement (D2)], [Re-reading a type's free variables at each use changes its meaning after `x := S Z`.], [6], [locality],
  [Copy on read (D3)], [Design, overturned by D53.], [design], [—],
  [Close off at the innermost stuck call (D4)], [Design: sealed programs as backward functions.], [7], [closing off],
  [`Id` computes to `Eq` of observations (D5)], [Design: the footprint.], [11], [observation],
  [`Eq` computes on constructors (D6)], [Design; sound because the model identifies propositions by truth.], [2], [none],
  [Imprecise join (D7)], [Design, later replaced (D15, then D84).], [design], [—],
  [Scope: no borrows in data, no shared borrows, no loops (D8)], [Design.], [design], [—],
  [A sealed program never closes off its own head (D9)], [Re-running a sealed call re-closed it into itself: a loop.], [7], [closing off],
  [Saturated calls; λ is a `fix` (D10)], [Currying let a closure capture a borrow.], [6], [locality],
  [Loans are variables bound by their borrow (D11)], [Anonymous pending bindings and a side condition at ends.], [7], [closing off],
  [A definition is checked at its generic call (D12)], [Design: checking `f` is running `f(&c₁, …)` at unknowns. The root of "one code, two runs".], [4 (design)], [none],
  [Π-types capture values at formation (D13)], [`Oops2`: a Π-type re-read `x` at the call site; a closed proof of `⊥`.], [6], [locality],
  [Proofs are not run (D14)], [Lemma calls overwrote borrowed places; irrelevance identified a writing and a non-writing function; a closed proof of `⊥`.], [6], [erasure],
  [Stuck matches close off like calls (D15)], [The join was a weaker copy of closing off, not natural under refinement.], [7], [closing off],
  [`Eq` computation trimmed (D16)], [Design: fewer conversion rules.], [2], [none],
  [Recursion on entry values (D17)], [A syntactic check accepted `*x := S *x; f(&p)`: a proof of `Π(n). ⊥`.], [10], [recursion],
  [Owners are sets (D18)], [Observing one owner of a hole proved `Id Nat (S Z) Z`.], [11], [observation],
  [Access ends loans on the path and in the content; `Id`'s sides on independent copies (D19)], [A dangling borrow; the exclusivity the frame property needs was implicit.], [12, 11], [locality, observation],
  [Proofs have no effect outside themselves (D20)], [A `Prop`-typed block wrote when sealed and not when run directly: `Id Nat (S Z) Z`.], [6], [erasure],
  [[Call-type] after the arguments; arguments in temporaries (D21)], [Effect goals were all `⊤`; arguments in flight were invisible to [Access].], [5], [none],
  [Blocks capture like closures; generalise then split (D22)], [Blocks hid their arms' moves and writes.], [7], [closing off],
  [`J` has explicit endpoints; recursion names its parameter (D23)], [`Eq A a a ≡ ⊤` erased endpoints; several shrinking arguments.], [2, 10], [recursion],
  [Every type is formed on a private copy (D24)], [A type formed elsewhere ran effectfully in the real environment.], [6], [erasure],
  [The pure theorem by the in-place lemma (D25)], [Usage, not a fault.], [feature], [—],
  [Erased terms run on a private copy; a neutral head closes off at once; Π-types capture no borrow (D26)], [D20's static check replaced by one principle.], [6, 7], [erasure, closing off],
  [Proof parameters are `⋆` (D27)], [Sealed programs embedding different proofs failed to compare (incompleteness).], [2], [erasure],
  [Erasure decided per declaration, never from a normal form; universes not cumulative (D28)], [`U(n)` computing to `Prop` at `Z` only: erased at one path, run at the other; `Lie(Z) : Eq Nat Z (S Z)`.], [4], [decisions never read a run],
  [Matching ends loans inside a neutral head; normalisation errors are type errors (D29)], [A hole inside a sealed head was generalised away; an accepted program wrote through an ended borrow.], [7, 5], [closing off, no catch],
  [A function's normal form is its generic call's observation (D30)], [Closures compared by result only: `Eq Nat (S Z) Z`.], [2], [none],
  [`f` not in scope without `by` (D31)], [Unannounced recursion.], [10], [recursion],
  [Pattern variables resolved before captures and footprints (D32)], [`p := Z` in a block unseen as a write: `Clear(&c)` proved a false equation.], [7, 11], [closing off, observation],
  [Type-level matches are type-checked (D33)], [Unchecked arms of a match in a type could fail after refinement.], [4], [none],
  [Generalising a sealed program is a persistent refinement (D34)], [Re-derived sealed programs never met the induction hypothesis (incompleteness).], [7, 8], [worlds],
  [Erasure purely syntactic (D35)], [`BoomL`, `BoomB`: a local function's and a block's class computed from values, decided differently on the two paths.], [4], [decisions never read a run],
  [Strict positivity (D36)], [`Bad := Mk(f : Π(x : Bad). Empty)` accepted; a proof of `0 = 1` by typing alone.], [1], [none],
  [Records global, names never reused (D37)], [A private copy's restore rewound the name counter and dropped a record: a later split reused a name; a closed false proof.], [6, 8], [erasure, worlds],
  [Observing a borrow result writes through it (D38)], [`PickX` and `PickY` observed alike: `0 = 1`.], [11, 2], [observation],
  [The head guard covers neutral heads (D39)], [D9's loop again, through a neutral head.], [7], [closing off],
  [A block is erased when each arm is (D40)], [A match's computed type decided erasure: `BoomG`.], [4], [decisions never read a run],
  [Erased terms may not affect outer places (D41)], [Defence in depth for misclassified erasure; deleted by D69.], [6], [erasure],
  ["A proof" is read from declarations (D42)], [`BoomH`: a value-based proof test erased a write at one path only.], [4, 3], [decisions never read a run],
  [A function type returning a borrow must take one (D44)], [No owner for a returned borrow made `e`'s type `⊤`; with a leaking function, a closed `Empty`.], [6, 1], [locality],
)

=== Uniform inductives to the switches' removal: D45 to D70

#L(
  [`Prop` inductives, subsingleton elimination, matching proofs by type (D45)], [General `Prop` inductives need Lean's rule for consistency with proof irrelevance.], [1, 4], [none],
  [Uniform parameters (D46)], [Polymorphic data.], [feature], [—],
  [Distinct constructors disjoint in `Eq` (D47)], [Completes `Eq`'s computation; valid in the model.], [2], [none],
  [Borrows only of data, `&` only at the top of a declared type; Π-types compared under binders (D48)], [`&Type` made `Type₀` impredicative (Hurkens); a codomain computing to `&Nat` read `⊥`; capture-sensitive comparison of Π-types.], [1, 3, 2], [none],
  [Clarifications of D45 (D49)], [A proof scrutinee's type must normalise to a head (fail-safe); a proof's value is always `⋆`.], [3], [decisions never read a run],
  [The unit laws are conversion (D50)], [Normalising stored types lost their head.], [2], [none],
  [Captured values keep their declared types (D51)], [A captured proof or sealed program could not be typed.], [5, 3], [none],
  [Pairs are an ordinary inductive; `Eq` injective (D52)], [Design: one rule instead of a primitive.], [2], [none],
  [Runtime reads move; copy decided by declared type; `clone` (D53, amendments)], [Design; its viability found the erasure flags decided after running, made a syntactic pre-pass; the `⊥` checks at reads, captures and ends.], [4, 9], [decisions never read a run, wholeness],
  [The class and [Close] row are part of the Π-type (D54, refined)], [`RunGGen(H)`: conversion let a writing function stand at a proof-class type: a closed `False`.], [3], [none],
  [Sorts are syntactic: one notion of proposition (D55)], [Declared and computed sorts disagreed (`T(Z) : P(Z)`): closed proofs of `False`, and a proposition with two distinguishable inhabitants.], [3], [none],
  [`J` computes only at convertible endpoints (D56)], [Equality reflection under a false hypothesis: untyped λ-calculus, `5` at `Bool`.], [2], [none],
  [Arrays as a library (D57)], [Design.], [feature], [—],
  [An impossible branch is stuck, never an ill-typed value (D58)], [A zero-arm match returned `⋆` at a data type in an open run.], [2], [none],
  [η for `Unit` (D59)], [Design: removes a [Close] row.], [2], [none],
  [`Nat` stays non-copy; `Word` (D53 second amendment)], [Design.], [feature], [—],
  [`rewrite`, destructuring `let` (D60); `split` (D61)], [Proof ergonomics.], [feature], [—],
  [`Id`'s owners in a canonical order (R6)], [Closing off reorders Ω; the two paths must build one conjunction.], [11], [observation],
  [η for one-constructor types on demand (D62)], [A block's move refined a pair that a direct path did not: the paths disagreed on which places exist.], [4], [none],
  [The rule audit's divergences (D63)], [A match did not check its stored type; `J` ran when stuck; `Eq`'s sides were not private; a closure captured through a block's borrow; `Id` was stuck in untyped runs only; a reader answered "any".], [3, 2, 6, 4], [locality, erasure],
  [[Drop] ends the borrows of a dying place (D65)], [The generic run ended a borrow earlier than an instance, so a drop failed at the instance only.], [4], [none],
  [D65 amended: a value in flight's borrow is not ended (D65)], [`Blk` returned a borrow of its own local through a block; its closed run read `⊥`.], [12, 4], [none],
  [`Prop : Type₁`; `&A` iff `A : Type₀` (D66)], [Predicativity of `Type₀` for borrows of functions and type parameters.], [1], [none],
  [`Eq`'s sides on a private copy, effects discarded (D63 item 6 reversed)], [Confinement rejected the in-place sort inside a statement.], [6], [erasure],
  [Dependent fields with open and repack; the nesting condition (D64)], [The unconditional rule had a closed `False` (`NBox`).], [9, 1], [wholeness],
  [Overwriting a borrow does not end the reborrows behind it (D67)], [Precision ("move the cursor down"); the generic run still ends at least what an instance ends.], [6], [locality],
  [Using a variable consumes it, in statements too (D68)], [Five more disagreements between abstract and ground runs once statements moved: copy-ness from values, nested erased terms not private, a closure in an arm capturing only when run, η named afresh in each copy.], [6, 4, 7], [erasure, closing off],
  [Confinement deleted (D69)], [Simplification: private copies made it redundant.], [6], [erasure],
  [A proof field assigned while its index is lent (D64 amended)], [`LieLent`: the proof was checked at the borrow's current content, the borrow then wrote another: a closed `False`.], [9], [wholeness],
  [Switches and the counterfactual ledger removed (D70)], [Process: the theorem is about the checker at its defaults.], [5], [total code],
)

=== Fording to the frozen readings: D71 to D96

#L(
  [Fording: value parameters, equation fields, non-uniform recursion (D71)], [Feature; its attack pass found a parameter of borrow type recorded in a type.], [1, 12], [none],
  [A stuck block's arms repack (D72)], [A dependency lie in an arm followed by more code escaped every whole-again point.], [9], [wholeness],
  [A lent part is unknown at a whole-again point (D73)], [`GetN` returned a borrow of an index field; `BoomI2`, a closed `False`.], [9], [wholeness],
  [Decisions are made where the machine cannot run (D74)], [Implementation: `Decide.lean` does not import the machine.], [4], [decisions never read a run],
  [A closed-off `J` ends its borrows where its term ends (D75)], [`JLie`, `BoomJ`: a closed `False`.], [9], [wholeness],
  [The producer obligation, one choke point (D76)], [Restructure: `closeBlock` takes its arms as computations and checks each return.], [9], [wholeness],
  [A binding's class from its type's syntax (D77)], [A binding's class read from a value: the paths decided differently (fail-safe, true programs rejected).], [4, 3], [decisions never read a run],
  [A recursive call recognised by name (D78)], [`CapSplit`: a split rewrote a captured function value, the recursion check compared values and missed its calls: a closed `False`.], [10], [recursion],
  [An η-refinement belongs to its world (D79)], [`EtaBoom`: a sibling arm reused fields typed in another world: a closed `False`.], [8], [worlds],
  [Copy or move and η at `Unit` from declared types (D80)], [Three decisions read computed types under one-directional arguments.], [4], [decisions never read a run],
  [`t.i` for any one-constructor type (D81)], [Feature: `Pair` no longer special.], [feature], [—],
  [Every binding has its declared type; the machine carries types (D82)], [A place's type was read off its value by a route that depends on whether it is refined.], [5, 4], [none],
  [A value holding `⊥` is convertible with nothing (D83, retired)], [`Same`: two observations that had each lost a moved part were identified: a closed `False`; also through `trans` and [Rewrite].], [2], [none],
  [Moves are definite: the join; `Id` between equal type-states; `⊥` a value of its own (D84)], [`Same`'s root: "maybe moved" on one path, "not moved" on another; grain faults `Moves84.G`, `WholeUse`, `LentField`, each a closed `False`.], [4, 2, 11], [decisions never read a run (moves), observation],
  [A constructor's parameters move nothing (D84 amendment)], [The static fold counted a position the run evaluates on a copy.], [4], [none],
  [`J` at runtime is its term (D85)], [Type safety: a true cast between unconvertible endpoints stopped a closed run.], [6], [erasure],
  [A Π-type term has its declared sort in every reading (D86)], [Every Π-type read as `Type₀`: borrows of proofs and `Type₁` functions accepted.], [3], [none],
  [A block's arm may not return a borrow of a place it takes by move (D87)], [`JoinMv` accepted, its closed call rejected: the block's return check lacked the function's.], [4, 7], [none],
  [An untyped constructor records its inferred parameters (D88)], [Untyped runs built `Some(n)` with no type where the check had one.], [4], [none],
  [An untyped run gives a constructor its context's type (D89)], [The residue of D88 (overshot: corrected by D124).], [4], [none],
  [When a borrow ends is a decision every run shares (D90)], [`EI`, `EJ`, `EIB`, `GJI`, `G1`: accepted, closed calls rejected; the generic run over-approximated borrow ends and two consumers were not monotone.], [4], [none],
  [A block's arms are checked after its entry (D91)], [Inside arms the generic run held borrows no instance holds.], [4], [none],
  [A private copy takes a borrow argument from its holder (D92)], [One borrow held twice inside a copy.], [12], [none],
  [A one-constructor match never closes off (D93)], [`clone(x.0)` moved `x`; a field read ended a borrow of a sibling; an internal error; the model and the checker disagreed.], [4], [none],
  [The join drops a place that exists, or rejects (D94)], [The join read an ill-typed place from an arm no run takes.], [4], [none],
  [The deciders write no cache (D95)], [A decision procedure writing the state.], [5, 4], [decisions never read a run],
  [A decision reads an unknown by its frozen reading (D96)], [Decisions read Δ, which refinement rewrites.], [4], [decisions never read a run],
)

=== The proof's findings: D97 to D135

#L(
  [A sealed program holding a hole is never run (D97)], [A nested run wrote a hole whose borrow only the outer state holds.], [7, 5], [closing off],
  [A borrow never ends over a moved content, in an observation too (D98)], [An exception for observations only: the model cannot read a moved-out borrowed content.], [9, 4], [wholeness],
  [A call's returned borrow is always fresh (D99)], [The label of a result differed between a run, a closed-off call and the model.], [4], [none],
  [Every proposition is a copy; a proof function's own binding is a proof (D100)], [Copy-ness and erasure disagreed on a Π-type into proofs; a binding classified one way before running and another after.], [3], [none],
  [The join rejects a move through `*` of a place not declared a borrow (D101)], [`DP1`, `DP4`: an arm no run takes moved through a proof; the checker and the model disagreed on liveness.], [4], [none],
  [Every value in flight has a stored type (D104)], [The invariant "values have their types" said nothing of temporaries; three statements of the proof false.], [5], [none],
  [The join's "do nothing" by the copy decision only (D102)], [A drop decided on the value a run produced.], [4], [decisions never read a run],
  [A constructor's parameter inferred only where the model follows (D105)], [`SH`: a parameter at a higher universe solved from a field; also an index bug left an untyped value bare.], [1, 4], [none],
  [No access ends a borrow a value in flight holds (D106)], [`TK`: the join's access ended the result's borrow; rejected only by an unrelated later rule.], [12], [none],
  [A strong update stores only first-order data (D110)], [`BoomF`: `⋆` stored in a data field, read at its declared type: a closed `False`; `Leak`: a borrow stored inside a value.], [3, 12], [wholeness (W3)],
  [A comparison keeps nothing but names (D103)], [A comparison's copy left a record naming an unknown of an empty type.], [6], [erasure],
  [Nesting covers the type being declared; a greatest set (D107)], [`Q(Q(A, n), 1)`: Curry's paradox, a closed `False`; a second hole (`PositivitySwap`); readers of a constructor-less entry.], [1], [none],
  [A leaf dependent field is a proof field (D112)], [The model cannot read a number's or a function's type off its content; [Entry] invalidated on one path only.], [3, 4], [wholeness (W3)],
  [D112 amended: typing reads through a mark], [`A2`: a lent field's mark had no readable type and fell back to the declared type: a closed `False`.], [3], [wholeness (W3)],
  [A generalisation record is looked up exactly (D108)], [Lookup by conversion's equality ignores recorded parameters.], [2], [closing off],
  [A loop bounded by fuel (D109)], [A `while`, opaque to the kernel.], [5], [total code],
  [A borrow is never left without its end (D111)], [An overwrite ended no borrow below a root; a lender kept a loan for ever.], [12], [none],
  [`Id` observes what a re-pointed borrow points to (D113)], [`Hide`: a write through a re-pointed borrow went unobserved.], [11], [observation],
  [A side of `Id` may end a borrow it consumes, on every path (D114)], [A theorem accepted and a closed instance rejected: the check asked who held the borrow, which differs by path.], [4], [none],
  [A call's arguments stay in Ω until its frame binds them (D115)], [In a window no position held a borrow argument: 662,366 states with a loan of an ended borrow.], [5], [none],
  [`clone` of a proof is that proof (D116)], [The after-run classification table had no row for `clone`.], [3], [none],
  [A tail split ends with the join (D119)], [Three paths of a tail match left different places moved.], [4], [none],
  [A declaration names only declared things, checked before running (D118)], [An undeclared name in an arm no run takes was accepted, the live twin rejected.], [4], [none],
  [A variable mentions what its type mentions (D120)], [`D2Node(x : D2, p : Pt(D2, x))`: the model cannot build it; Lean rejects it.], [1], [none],
  [A nested occurrence passes only through its own sort (D121)], [`D := MkD(q : Q(PP(D)))`: no model for `Prop`-sorted knots.], [1], [none],
  [The field-type frame binds what a loan stands for (D117)], [A loan held twice; reading a field's type ended a borrow.], [12], [none],
  [`clone` and `peek` take a place in the core (D122)], [The core copied any term; the checker itself built `clone((⋆ : T))`.], [4], [none],
  [The untyped run hands a hint exactly where the typed check does (D124, three entries)], [A run of checked code read a hint its check never had, or missed one it had (12 sites; `J`; an embedded value's type).], [4], [none],
  [A function ending in `split` can be called (D125)], [Every call of an accepted function ending in `split` was rejected.], [4], [none],
  [The braces `split` names its call (D126)], [Nothing that had only the term could run it.], [4], [none],
  [A borrow whose content is moved out is not read (D127)], [`TakeRefill`: a callee checked on the actual state, which its type does not describe.], [9], [wholeness],
  [The join carries the places moved at its entry as they are (D129)], [`f` accepted, `f(A0(…), Z)` rejected.], [4], [none],
  [A type parameter is written as a sort (D128)], [Two tests of "is a type" disagreed on `TL`.], [3, 1], [none],
  [The defer flag is consumed when an evaluation starts (D130)], [A one-shot flag persisted in the state until some later call read it.], [5], [none],
  [A `let` defers only a non-erased call's type (D132)], [A record returned through the state was discarded with a private copy: `useT` accepted, `useT(1)` rejected.], [5, 4], [none],
  [An inductive's own name in its fields only (D133)], [`Q6`'s own name in a dead arm of a parameter type; `Q3` ran the checker out of memory.], [1], [none],
  [A binding's reading agrees with its type and value (D131)], [`V1`: a proof read as data behind `PropF(x)`; accepted, its instance rejected.], [3], [none],
  [A deferred call's head type tested when recorded (D134)], [The deferred and the eager path of one call tested differently.], [4], [none],
  [While a function is checked, a call of it closes off (D135, on `main` since f63e5a84)], [`Loop`: a typed recursive call ran the body under check, untested, for ever.], [4], [recursion (R3, unexplained)],
)

=== The eight accepted proofs of `False` since October

#table(columns: (30%, 50%, 20%), align: left, table.header([*Proof of `False`*], [*Where it broke*], [*Principle*]),
  [An index field lent through a returned borrow (`GetN`, D73)], [A part still lent at a whole-again point was read at its current content.], [9 wholeness],
  [A stuck `J` not checked at its term's end (`JLie`, D75)], [A producer of a dependent unknown did not check whole.], [9 wholeness],
  [A recursive local function splitting its capture (`CapSplit`, D78)], [Recursive calls identified by value, which refinement changed.], [10 recursion],
  [`EtaBoom` (D79)], [A world's fact (an η-refinement) kept after its world.], [8 worlds],
  [`Same` (D83, D84)], [An identification true at the generic run, false at an instance, because the paths disagreed on what was moved.], [2 and 4],
  [A declaration nested at its own parameter used negatively (D107)], [A declaration with no model.], [1 meanings exist],
  [An unchecked write into a dependent field (D110)], [A field typed by a content (`⋆`) that does not say its type; a borrow stored in data.], [3 and 12],
  [A dependent field lent to a call's returned borrow (D112 amended)], [A mark with no readable type, given the declared type.], [3 readings],
)

*The residue, and the principles it gave.* Of the 139 rows, 10 are design choices or features. Of the other 129, 67 fit a principle written before 27 November and 62 fit none. The 62 fall into five groups, each one idea nobody had written down: declarations that have no model (principle 1); identifications that fail at some instance (principle 2); readings that are the same on every path but wrong (principle 3); a run of checked code that is not the checked computation (principle 4: D12 is its root, D33 its first instance, the two-paths faults of the generic call against an instance its old half, D124, D125, D134, D135 its new one); values outside the state and state that is not the program's (principle 5, from which exclusive access was later split as principle 12). The seven of 2 November explain most faults found before they were written; of those since, they explain only `EtaBoom`, a sealed program run over a hole (D97), a comparison's leftover record (D103), two of observation (D113, D114) and two of wholeness (D98, D127).

== How this document was made <sec-made>

Seven authors and six adversarial referees worked in alternation on 27 and 28 November 2026, followed by an audit and a revision; each referee read the current document, the paper and the code, ran programs on the checker of the day, and wrote a report the next author answered. The reports and answers are in git history (this file before 28 November); every objection is now folded into the text, marked as standing where it applies, or recorded as refuted.
- `theory1` wrote the ledger, found the residue's five principles, and audited principles 4, 3 and 5 against the code. `theory2` revised the principles against a first argument for consistency from the principles alone.
- _The first referee_ showed that argument to be a reduction: four principles were the proof's open theorems, its induction did not survive the end of a borrow, membership was carried on the checker's side and asserted for untyped runs, and D135 was described as landed when it was not. `theory3` restated consistency as conditional on named theorems, in the two-half form of the mechanisation, and landed D135's consequences.
- _The second referee_ showed the frame property's proof did not exist (a false invariant, a closure formed in the body not covered, four shapes used and not stated, (II) missing what its Lean statement needs) and found the model's fault `G1`. `theory4` rewrote the frame property; `theory5` brought it to the mechanisation and argued resolved determination, exclusive access, conversion on code, [Repack], the block lemma and hints.
- _The third referee_ showed all three model changes wrong as written ((M3) made the frame property false at `CallI`, (M2) was circular and its `.pi` clause wrong), and found the observation's first type-safety fault. `theory6` measured the five sites, specified the detached observation and its refinement, and stated the frame property as Lean's.
- _The fourth referee_ showed the observation patch unsound without a restriction (`Bad`), resolved determination false at a proof owner and at non-whole ancestors, the frame property not Lean's, a fifth site, and (X1) false at deferred types.
- _The fifth referee_ found the detached observation sound, but its cost understated (`ConsW`, `IdxSame`, `SwapCall2`), the detach lemma needing the frame property over two label lists, and the checker binding a proof's data fields as locals where the paper and this document said otherwise (D138). `theory7` proved a model of the data types exists on paper and attacked the declaration checks with 193 programs.
- _The sixth referee_ showed the paper's model is not the Lean's and is defined through a run that exists only on codes, that several declaration checks serve Lean's records or the simulation rather than the construction, that the Lean plan for the hard case understated a step, and that the standing assumption was too narrow; and found `Leak`.
- `theory8` consolidated the document into its present form, settled `Leak`, presented the choice of N1's model as settled (it is decision (f)), and re-ran the evidence.
- `referee7` audited the consolidation against the version it replaced, the Lean, the experiments and the checker, re-ran every program block (475 verdicts, all as written) and 52 programs cited from the old reports, and found its account of the Lean stale in both directions: it had missed docs/31 D221 to D231. It corrected four statuses and a number itself and left a table of the rest.
- `theory9` applied that table: the section on a proof's data fields rewritten to the model as built; the frame property's hypotheses and proof clause by clause as Lean has them; N1's statement moved to decision (f); every status brought to the proof line at 73f1a1075, a theorem that assumes facts reported with them; and the [Call-type] route of the observation's fault added to the evidence (`CallH`, `CallF`).
