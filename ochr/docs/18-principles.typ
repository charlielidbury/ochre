// The principles the Ochr checker's correctness rests on: a ledger of every recorded decision and
// fault by the principle it restores, each principle's audit against the code, and the redesign
// that would make it hold by construction. Written to replace docs/18's section on principles.
// Standalone: compile with
//   typst compile ochr/docs/18-principles.typ
// Notation macros are copied from the top of 18-consistency-proof-plan.typ (which copies the paper's).

#set document(title: [Why the Ochr checker is correct: its principles])

#let dark-mode = false
#let ink = if dark-mode { white } else { black }
#let muted-ink = if dark-mode { luma(170) } else { luma(80) }
#let code-bg = if dark-mode { rgb("#2a2a2e") } else { luma(246) }
#let expl-fill = if dark-mode { rgb("#1d2733") } else { rgb("#eef3f8") }
#let expl-rule = if dark-mode { rgb("#7fa3cc") } else { rgb("#5b7fa6") }
#let warn-fill = if dark-mode { rgb("#33201d") } else { rgb("#fbefe9") }
#let warn-rule = rgb("#c0604a")
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
// The meaning of x in the set model; under an assignment `at` of the unknowns when given.
#let deno(x, at: none) = if at == none { $lr(⟦ #x ⟧)$ } else { $lr(⟦ #x ⟧)_(#at)$ }
// The reference run of t: the meaning of running t.
#let refrun(t) = $upright("Run") lr(( #t ))$

// A principle, numbered on its own counter: P1, P2, ...
#let pcount = counter("principle")
#let principle(name, body) = block(width: 100%, above: 1em, below: 0.9em, breakable: true, [
  #pcount.step()
  *Principle #context pcount.display() (#name).* _#body _
])
// Status tags for audit rows.
#let tagc(c, s) = box(inset: (x: 3pt, y: 1.5pt), radius: 2pt, fill: c, text(size: 7.5pt, weight: "bold", fill: status-ink, s))
#let s-cons = tagc(rgb("#cfe8cf"), [by construction])
#let s-check = tagc(rgb("#e6dcf2"), [by a named check])
#let s-not = tagc(rgb("#f6cfcf"), [NOT ENFORCED])
#let s-open = tagc(rgb("#f2f2c4"), [not audited])
// A program that was run, with its measured verdict.
#let measured(body) = block(width: 100%, inset: 7pt, stroke: (left: 2pt + expl-rule), fill: expl-fill, above: 0.7em, below: 0.7em, breakable: true, [#set text(size: 9pt); #body])
// A predicted fault: the prediction, the program, and what happened.
#let fault(body) = block(width: 100%, inset: 7pt, stroke: (left: 2pt + warn-rule), fill: warn-fill, above: 0.7em, below: 0.7em, breakable: true, [#set text(size: 9pt); #body])
#let why(body) = block(above: 0.6em, below: 0.8em, inset: (left: 0.8em), text(size: 9pt, fill: muted-ink, style: "italic")[Why: #body])

#align(center, text(size: 16pt, weight: "bold")[Why the Ochr checker is correct])
#align(center, text(size: 11pt)[A small set of principles of the design, the decisions and faults each explains, where the code enforces each, and where it does not])
#v(0.3em)
#align(center, text(size: 9pt, fill: muted-ink)[Draft by the agents `theory1` (ledger, audits) and `theory2` (argument, revision), 27 November 2026 · to replace the section "The principles the checker enforces" of docs/18])
#v(0.6em)

#align(center, box(width: 92%, align(left)[
  *Summary.* The checker has accepted closed proofs of `False` eight times since October, and about 135 decisions record a rule added or tightened after a counterexample. Each fix was local. This document states the reasons the design is correct as twelve principles, each one sentence about the design, and tests them two ways. Against the history: every decision and every known proof of `False` is classified by the principle it restores (@sec-ledger), which found five principles nobody had written down (@sec-residue). Against the consistency argument: @sec-argument proves, case by case and riskiest first, that every accepted definition means a member of its type, citing the principles and nothing else. The argument closes in every case; no case shows the design wrong. It found five clauses missing from the first statements of the principles (that nothing touches a live loan, that backward functions are injective, that a value relied on is whole at every future of its lent parts, the order of calls, and why a constructor's recorded parameters are a decision), and clauses it never uses: the adequacy clauses of observation, the type-safety clauses of "one code, two runs", and the converse of "readings are true". The list is revised accordingly (@sec-revision): exclusive access is now principle 12, and "undecided decides nothing" a clause of principle 5. For each principle, @sec-audits gives the cases that consume it, its enforcement (principles 6 to 12 re-read against the code), the audits of principles 4, 3 and 5 from the code, and the redesign that would make it hold by construction.
]))
#v(0.4em)
#outline(depth: 2, indent: auto)
#pagebreak()

= What a principle is <sec-what>

A _principle_ here is one sentence about the design, not about a line of code, with three properties. The consistency argument uses it at a point that can be named: types mean sets, `False` means the empty set, and every accepted definition must mean a member of its type; a principle is what one step of that argument needs. If it failed, some wrong program would be accepted, or some step of the argument would break, and we can say which. And the checker makes it true either _by construction_, for a structural reason it cannot be violated (the module that makes decisions does not import the machine, so no decision can read a run), or _by checks_ at a list of sites that can be enumerated. A site where a principle could fail and nothing makes it hold is _not enforced_; the audits (@sec-audits) look for these by reading the code, predict the fault each would allow, and run the smallest program that should show it.

Every program in this document is self-contained and was run with `lake env lean` on the checker of `main` at 105021637 (the same checker as the proof line's base, `ochre-checker10-base`); its verdict is the one measured. "With the `Nat` prelude" means the block `uses Nats` (`Ochr/Examples/Nat.lean`).

= The principles <sec-principles>

Twelve principles, revised by `theory2` against the argument of @sec-argument: each is stated in the form the argument uses, and a clause the argument does not use is marked as type safety's or as the adequacy of `Id`'s (a target dropped on 13 November). The numbers of the first draft are kept, so the ledger's numbers still apply, with one exchange: the borrow half of the first draft's principle 5 is now principle 12, _access is exclusive_, and the first draft's principle 12 (_undecided decides nothing_) is now a clause of principle 5. @sec-revision lists every change and the case of the argument that forced it. Each principle is stated once here; @sec-audits gives each its consumers in the argument, its enforcement, its audit and its redesign.

#principle[Meanings exist][Every declaration the checker accepts denotes in the set model: an inductive type is the least set closed under its constructors (positive, nestable, one sort per knot, its field types read only through what the model can follow), every universe is predicative but `Prop`, a proposition is a truth value, and a function type means the functions from the contents of its borrowed places and its other arguments to its result and their final contents, where a returned borrow derives from a borrow argument and has an injective backward function.]
The set model is the ground of the argument: types mean sets, `False` the empty set, and every accepted definition must mean a member of its type. A declaration with no model (a type that is its own negation, as in Curry's paradox) lets the checker accept a closed proof of `False` by typing alone. The model is built declaration by declaration, so what it needs of the checker is a syntactic condition on each: strict positivity (D36), nesting at the greatest set of nestable parameters (D64, D107), no value of the type read off a field's spine (D120), one sort per knot (D121), a type parameter written as a sort (D128), the declaration's own name only in its fields (D133), predicativity of `Type₀` (D48, D66), subsingleton elimination (D45), and constructor parameters inferred only where the model can follow (D105). The last clause is the model's relation R (paper A.6): Ochr proves of every abstract `g : Π(x : &Nat). &Nat` that writing `0` and writing `1` through `g(x)` leave different states, which is true only of functions whose backward functions are injective, so the model must contain only those; a returned borrow always derives from a borrow argument (D44), and @sec-arg-id proves every accepted function is one.

#principle[Identifications hold][Wherever the checker identifies two things (two types or values by conversion, an `Eq` computed to `True` or `False`, a `J` that computes, a record looked up by its key), the two mean the same element under every assignment of the unknowns, not only under the ones the generic run happens to see.]
Conversion is how a checked term moves from one type to another, so an identification that fails at some instance transports a member of one set into another. The history's faults are of two kinds: an identification that holds at the generic run and fails at an instance (closures compared by their results only, D30; a borrow result observed without writing through it, D38; two values that had each lost a moved part, `Same`, D83 and D84), and one that breaks typing in open contexts (equality reflection by `J` under a false hypothesis, D56; an unreachable arm giving a value at the wrong type, D58). Keys need exact equality, not conversion's (D108); and since a decision can read an embedded value's reading, conversion of code relies on the shape principle 7 gives sealed programs (@sec-arg-conv).

#principle[Readings are true where they replace a value][Whatever the checker reads about a term from syntax and declared types and acts on by replacing a value with a canonical one (`⋆` for a term read as a proof, `()` for a value read as `Unit`, its constructor for a value of a type with one constructor, nothing for an erased type) is true of the term's type; and a type is read off a value only where the value says its type.]
Most decisions are made from _readings_, facts read off syntax and declared types (D28, D35, D55, D77, D80); principle 4 makes them the same on every run, and this principle makes them right where rightness matters to the meaning: a replaced value keeps its meaning only if its type has that one element. The history: two notions of proposition (D54, D55), a Π-type's sort read as `Type₀` (D86), copy-ness against erasure (D100), `clone` missing from a table (D116), two tests for "is a type" (D128), a sort hidden behind a call (D131); and, for types read off values, a field typed by a content that does not say its type (D110, D112 and its amendment). Only this direction is used: a term whose type is a proposition but reads as data is run with its effects on every path (the first draft's `W2`, @sec-a3), which is harmless to consistency, though a type-directed compiler would assume the converse.

#principle[One code, two runs][Every decision that changes what a run computes (whether a term is erased; a function type's class and [Close] row; copy or move; η; the places a match moves and their grain; which borrows end where, and what a result is lent; the parameters a constructor records) is a function of the code and the declared types, computed alike by the code's typed check, by every untyped run of it (in place, sealed, at unknowns or at values) and by its meaning.]
A definition is checked once, by a typed run at unknowns, and afterwards run untyped, in place or sealed; the argument gives the code one meaning and shows each run computes it, which holds only if every run decides as the meaning does. The history's _two paths_ (the generic call against an instance, paper §6.3) are the oldest instance (D28 to D40, D54, D84, D90); last week's faults are the typed-against-untyped instance (D124, D125, D134, D135). _For type safety, not consistency_ (@sec-arg-unused): an untyped run runs only code whose check has finished, can run every form the check accepts, and makes the tests the check made; their faults made accepted functions uncallable.

#principle[The state is the whole truth][Every value the checker holds while anything runs is at a position of its state with a stored type, nothing outside that state decides a step (no flag, cache or record outlives the evaluation it was made for), and every step that succeeds is an instance of a rule: no failure is turned into a value, and running out of fuel is undecided.]
The argument's first move at every step reads the checker's success as a derivation of the paper's rules at the state the rules describe, and its invariant is a predicate on that state. A value held in a variable of the checker's Lean code while other code runs is invisible to the invariant (a borrow with no holder, D115); a fact kept in the state that is not about the program (a cache, D95; a one-shot flag left set, D130; a record a private copy throws away, D132) makes the next step depend on something the rules do not describe; and a caught failure with a default turns "something is wrong" into a value. The last clause is the first draft's principle 12, the standards "no catch-and-default" and "all checker code is total" of `ochr/core/CLAUDE.md`. Its borrow half is now principle 12.

#principle[Effects stay local][A running body names and changes only its own frame and what its borrows lend; a call exchanges only what it is passed; and a run the checker makes privately (a statement, a type, a proof, a comparison, its own scaffolding) leaves nothing behind but fresh names and facts that mean the same in every state.]
This is docs/18's locality (L1 to L7) and the erasure half of its "erasure and captures" (E1, E3 to E5), and it is the frame property: a callee's meaning, read off a run of its body in a fresh frame, is the body's run in place. Faults: a Π-type reading its free variables at the call site (D13), proofs writing outer places (D14, D20), a record kept from a private copy naming the wrong program (D37) or an unknown of an empty type (D103).

#principle[Closing off rebuilds the call][A call stuck on an unknown, and a stuck match or `J` as a call of its captures, is replaced by sealed programs that rebuild the call exactly from what it was passed and capture every place any arm uses at least as strongly as the arm does; nothing else makes or changes a sealed program but substitution and re-running, which happens exactly when an input it embeds changes, everywhere it occurs, never re-closes its head, and never runs a program that holds a borrow's hole.]
This is docs/18's closing off (C1 to C9) with the capture rules (K1, K3): a block takes, as a function takes its arguments, everything any arm uses, at least as strongly as any arm uses it. Faults: re-closing the head (D9, D39), a write to a scrutinee unseen by the captures (D32), a hole lost by a generalisation (D29), a hole read by a nested run (D97). The clause "nothing else makes or changes a sealed program" is new: the comparison of code needs every sealed program to have [Close]'s shape (@sec-arg-conv).

#principle[Worlds are exclusive][A fact established while checking one arm of a split, and depending on the arm's constructor, is visible in that arm and its sub-worlds only, and entering an arm substitutes its refinement into every position of the state.]
docs/18's worlds (X1 to X4). Faults: an η-refinement kept after its arm (`EtaBoom`, D79); generalisation records rewound with a copy (D37).

#principle[Whole where relied on][A value may be open (break its type's telescope, or hold a moved part) only while the code that opened it runs; wherever it passes to code that relies on its type it is whole, at every future of the parts still lent; and whatever produces an unknown of a dependent type has checked whole the value it stands for.]
docs/18's wholeness (W1, W2); W3, a type read off a value, is in principle 3. Faults: an index field lent past a whole-again point (`GetN`, D73, the fault the clause "at every future" names), a stuck block's or `J`'s arm not checked at its end (D72, D75), a proof field assigned while its index is lent (D64 amended), a borrow with a moved-out content handed on (D127).

#principle[Recursion descends][Every call the check of a definition makes is of an earlier accepted definition, of a value, or of the definition itself, recognised by the name it binds for itself and checked to be on a strict part of the entry value as refined so far.]
docs/18's recursion, without R3 ("check before running"), which @sec-arg-call shows is a matter of termination. The first clause (docs/18's R4, "one order") is the order the outer induction of the argument runs in. Faults: a non-structural argument (D17), recursive calls missed after a split rewrote a captured function value (`CapSplit`, D78).

#principle[Observation names every owner][The places `Id` observes are read from the syntax of its two sides, which run on independent copies, and each place is traced to every one of its owners.]
What the argument uses of docs/18's observation (O1, O3's roots, O4): a statement proved at a definition's generic call is true at a call site, and the converse for a hypothesis, only if the two observations name corresponding places and every owner of a loan is observed (@sec-arg-id). Faults: one owner observed of several (D18); a write through a pattern variable unseen (D32). _For the adequacy of `Id`, not consistency_ (@sec-arg-unused): the observed places include every place a continuation could read (O3's sufficiency), the sides leave the same moves and borrows ([Id-typestate], D84, D114), where re-pointed borrows point is observed ([Obs-ref], D38, D113), and the conjunction comes in one order (O5, completeness).

#principle[Access is exclusive][A live borrow has one holder and lends exactly the places that hold its loan, fill or mark, never its own holder's content; nothing reads, copies, matches, overwrites or drops a live loan, because every access first ends the borrows that lend what it touches; and a borrow ends only over a whole content.]
This is Aeneas's discipline and the machine's [Access] (paper §4.1: "this is the whole of the borrow checker"), the borrow half of the first draft's principle 5. The argument uses it more than any other: it makes the meaning of a state a function of a future, it keeps every context around a live loan injective, which is what lets a hypothesis proved at a call site be used by the callee and what makes every accepted backward function injective (@sec-arg-id), it makes a write at a field find its path at every future (@sec-arg-dep), and it gives [Close] closed texts (@sec-arg-close). Faults: a dangling borrow and the frame property's implicit exclusivity (D19), a borrow of a local returned through a block (D65 amended), a borrow recorded in a type (D71) or stored in data (D110's `Leak`), one borrow held twice in a copy (D92), an access ending a borrow a value in flight holds (D106), a borrow below a root (D111), a loan held twice in the field-type frame (D117).

== What changed, and why <sec-revision>

#table(columns: (16%, 54%, 30%), align: left, table.header([*Principle*], [*Change from the first draft*], [*Forced by*]),
  [1 Meanings exist], [Added: a function type's returned borrow derives from a borrow argument and has an injective backward function (the model's R).], [Case 1: the hypothesis direction at a call site, and membership of a borrow-returning definition.],
  [2 Identifications hold], [Unchanged; its consumers named.], [Cases 1, 3, 5, 7 and the conclusion of the induction.],
  [3 Readings are true], [Narrowed to the direction used (a reading that replaces a value is true of its type), with the type read off a value; "every reader gives the same answer" is principle 4's.], [Cases 2, 7, 8, 9; `W2` shows the converse is not used.],
  [4 One code, two runs], [Restated as "every decision is a function of the code, computed alike by every run and by the meaning"; the hint kept, with its reason; "only checked code runs", "every accepted form runs" and "the same tests" marked as type safety's.], [Cases 1, 3, 4, 5, 7, 8, 9; D135 is termination (case 4).],
  [5 The state is the whole truth], [Merged with the first draft's 12 (every success is an instance of a rule); its borrow half moved to 12.], [The first move of every case.],
  [6 Effects stay local], [Unchanged.], [Cases 1, 3, 4, 5, 7, 8.],
  [7 Closing off rebuilds the call], [Added: nothing else makes or changes a sealed program; the capture clause stated.], [Case 7 (comparison of code); cases 3 and 5.],
  [8 Worlds are exclusive], [Unchanged.], [Cases 3, 5, 6 and the conclusion of the induction.],
  [9 Whole where relied on], [Added: "at every future of the parts still lent".], [Case 2.],
  [10 Recursion descends], [Added: every call the check makes is of something earlier, a value, or itself at a strict part (the order).], [Cases 4 and 6; the outer induction.],
  [11 Observation names every owner], [Narrowed to the places read from syntax and every owner; sufficiency, type-state, [Obs-ref] and order marked as adequacy's or completeness's.], [Case 1.],
  [12 Access is exclusive], [New: the borrow half of the first draft's 5, with "nothing touches a live loan" stated.], [Cases 1, 2, 3, 9.],
)


= The ledger <sec-ledger>

Every entry of `ochr/core/DECISIONS.md` (D1 to D134, with its amendments), the ruling D135 recorded in docs/32, and the eight accepted proofs of `False`, each in one row: the decision in words with its number after, what went wrong (or, for a design choice that fixed no fault, what it decides), the principle of @sec-principles it restores or establishes, and the principle written before 27 November that it fits, if any: docs/18's seven (locality, closing off, worlds, wholeness, erasure and captures, recursion, observation) or `CLAUDE.md`'s three standards (no catch-and-default, total code, decisions never read a run). "Design" marks a founding choice of the calculus and "feature" a decision that adds to the language without repairing anything; neither restores a principle, and neither is counted in the residue. Where a row has two principles, the first is the one the fix restores. The numbers are the revised list's (@sec-revision): rows about exclusive access, filed under 5 by the first draft, are under 12, and rows filed under the first draft's 12 (undecided decides nothing) are under 5.

#let L(..xs) = table(columns: (17%, 52%, 13%, 18%), align: left, table.header([*Decision*], [*What went wrong, or what it decides*], [*Principle*], [*Written before as*]), ..xs)

== The early rounds: D1 to D44

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

== Uniform inductives to the switches' removal: D45 to D70

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

== Fording to the frozen readings: D71 to D96

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

== The proof's findings: D97 to D135

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
  [While a function is checked, a call of it closes off (D135, ruled, not landed)], [`Loop`: a typed recursive call ran the body under check, untested, for ever.], [4], [recursion (R3, unexplained)],
)

== The eight accepted proofs of `False` since October

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

== The residue, and the principles missing from it <sec-residue>

Of the 139 rows, 10 are design choices or features. Of the other 129, 67 fit a principle written before (docs/18's seven or the three standards) and 62 fit none. The 62 are not scattered: each falls into one of five groups (10 rows in the first, 10 in the second, 7 in the third, 23 in the fourth, 12 in the fifth, counting each row by its first principle; several rows have a second), and each group has one idea nobody wrote down. The idea is the missing principle.

+ *Declarations that have no model* (D36, D44's leak, D45, D48 (1), D64's nesting, D66, D71's borrow parameter, D105, D107, D120, D121, D128, D133). docs/18's seven are about runs; none says anything about a declaration, and the model needs each declaration to denote before any run means anything. Three of these were accepted proofs of `False` or Hurkens-style paradoxes (D36, D48, D107). This is principle 1.
+ *Identifications that fail at some instance* (D6, D16, D30, D47, D48 (3), D50, D52, D56, D58, D59, D83, and D84's `⊥`). The written principles constrain runs; this group constrains what the checker _equates_: conversion, `Eq`'s computation, `J`'s computation. Principle 2.
+ *Readings that are the same everywhere but wrong* (D48 (2), D54, D55, D86, D100, D116, D128, D131, and D51's captured readings; D110 and D112, filed by docs/18 under wholeness's W3, are the same idea applied to a type read off a value). The standard "decisions never read a run" makes a decision the same on every run; nothing written required it to be _true_. Principle 3.
+ *A run of checked code that is not the checked computation* (D12's design, D33, D62, D65, D84's amendment, D87, D88, D89, D90, D91, D93, D94, D99, D101, D114, D118, D119, D122, D124 (three entries), D125, D126, D129, D134, and D135, which docs/18 names as R3, "check before running", with no explanation). Principle 4.
+ *Values outside the state, and state that is not the program's* (D21, D51, D65 amended, D82, D92, D104, D106, D111, D115, D117, D130, D132, and D71's borrow in a type). Principle 5. (The revision split this group: D65 amended, D71's borrow, D92, D106, D111 and D117 are about exclusive access, now principle 12.)

*The hypothesis, tested.* The orchestrator's hypothesis was that last week's faults (D124, D125, D130 to D135) fit none of the seven and share two unstated ideas: (i) one code, two runs, and (ii) readings are sound. The ledger confirms it with two amendments.
- D124, D125, D134 and D135 are (i): a run handed a hint its check did not, a form the check accepts that no run can run, a test made on one path of one operation and not the other, and a body run before its check finished. D131 is (ii).
- D133 is neither: it is a declaration with no model, the first group. Its sibling D118, the check that names are declared, is (i): acceptance depended on which arms a run reaches.
- D130 and D132 are not (i) or (ii) as stated, but a fifth idea, the state is the whole truth. D130 is a fact about one evaluation kept in the persistent state (a flag set for "the next call", read by whichever call came next); D132 is a result passed back through the state, which a private copy then threw away. Both were found by the proof because its invariant is a predicate on the state, and both are the mirror image of D104 and D115 (values the checker held outside the state). D132 is also (i), since its symptom was an accepted function its call could not run.
- (i) is older than last week. D12 ("checking `f` is running `f`'s generic call") is its root, D33 (2026-09) its first instance, and every two-paths fault of the generic call against an instance (D28 to D40, D54, D84, D90) is the same idea with "the typed check at unknowns" for one run and "an instance" for the other. What changed last week is that the proof began to state the untyped run's step, which exposed the typed-against-untyped half that the generic-against-instance half had hidden.

*Where the seven were right.* The seven explain most faults found before they were written (2 November). Of the faults since, the seven explain only these: `EtaBoom` (D79, worlds, which a referee found in the worlds principle itself), a sealed program run over a hole (D97, closing off), a comparison's leftover record (D103, locality), two of observation (D113, D114's first half) and two of wholeness (D98, D127). Every other fault since 2 November, the November proofs of `False` included, is in one of the five groups above: what one expects of a list that was complete for what it named and silent about the rest.

= The principles audited <sec-audits>

_How this section was written._ The audits of principles 4, 3 and 5, their predicted faults and their redesigns are the first draft's (`theory1`), from the code alone. Every "what consumes it" now opens with the cases of the argument (@sec-argument) that use the principle, written by `theory2` after reading the paper and the model notes; the first draft's reading of the history follows it, kept for its counterexamples. The section on principles 6 to 12 (@sec-a6) is `theory2`'s, its enforcement read against the code.

Each principle in turn: what in the consistency argument consumes it, how the checker enforces it today, an audit of the sites where it could fail, and the redesign that would make it hold by construction. The audits of principles 4, 3 and 5 were done from the code (`ochr/core/lean/Ochr/Machine.lean`, `Env.lean`, `Decide.lean`, `Runtime.lean` at 105021637) and their predictions run; the others are shorter and say what was not audited. The status tags are #s-cons, #s-check, #s-not, and #s-open for a site this pass did not read.

== Principle 4: one code, two runs <sec-a4>

*What consumes it.* In the argument: every case that compares a run of checked code with the code's meaning, which holds only if the run decides as the meaning does: a statement's evaluation at a generic call and at a call site (@sec-arg-id), a sealed program's re-run (@sec-arg-close), a callee's body run in place, including the parameters a constructor records (@sec-arg-call), a block against the arm it stands for (@sec-arg-split), conversion's generic runs (@sec-arg-conv), erasure (@sec-arg-erase) and copy or move (@sec-arg-places). Its clauses about untyped runs as such (only checked code, every accepted form, the same tests) are not consumed by consistency (@sec-arg-unused). _The first draft's reading of the history:_ the meaning-preservation theorem relates the checker's _typed_ run of a definition (at its generic call, the unknowns standing for anything) to the model, and supplies every other run of the same code from that one: an untyped run of a body at a call, a sealed program's re-run, a direct arm on a known constructor, the runtime. The supply is the callee's membership (its meaning is a member of its function type) carried through the frame property, so it exists only for code whose typed check has finished, and it says something about the untyped run only if that run is the same computation as the checked one. "The same" means: the same decisions at corresponding points (D90's alignment property is the borrow part of it), and differences only in the values the unknowns stand for. The historical counterexamples are of two shapes. A wrong acceptance where the two paths decided differently, such as `Same` (D83, D84): at an unknown `n` a block took `x` by move because one arm moved it, at `n = 1` the arm that ran left it, so two observations were equal at the generic run and different at the instance. And an accepted function that cannot be called (D119, D125, D129, D131, D132), with the smallest of them:
#measured[
```
inductive B := T | F
def IsZ (n : Nat) : B := match n { Z => T, S(m) => F, }
def V (b : B) : Type := match b { T => Nat, F => Unit, }
def G (n : Nat) : V(IsZ(n)) := split IsZ(n) { T => Z, F => (), }
def H : Nat := G(Z)
```
With the `Nat` prelude, both accepted today (D125, D126); before D125, `G` was accepted and `H` rejected ("split: only in tail position").]

*How it is enforced today.* By construction for the decisions read from syntax: `Decide.lean` does not import the machine (D74), writes no cache (D95), and reads unknowns by frozen readings (D96), so erasure, a function type's class and row, copy or move, η at `Unit`, whether a statement argument runs in place, and the join's moved set (`Decide.jdMatch`, D84) are functions of syntax and declarations. By construction, with listed obligations, for borrow ends: D90's fills and marks make every run end the same borrows at the same points, under eight obligations D90 lists, and D99 gives a call's result one label on every path. By checks at enumerated sites for hints (D124's table of fourteen sites, each consulting `readsHint`) and for the test a deferred call makes (D134's shared `callPi`). Not at all, today, for "an untyped run runs only checked code": that is D135, ruled and not landed.

*The audit, part (a): every place an untyped run starts, and why its code was checked first.*
#table(columns: (25%, 45%, 30%), align: left, table.header([*Site*], [*What guarantees the code was checked*], [*Status*]),
  [A call of a known function (`callFn`, its `.gfn` and `.clo` cases, through `runBody`)], [A global enters Σ _before_ its own check (`Check.lean`: the definition is appended to `globals`, then `checkFix` runs), so during that check it is the one global in Σ not yet accepted; if the check fails, later declarations do not see it (D118). A closure was formed by a typed run, which checks a λ where it is formed (`checkFix` in `evalCore`'s `.fix` case), or by an untyped run of code so checked. Exception: the function whose check is running, reached through its binding of itself or its provisional entry in Σ.], [#s-not for the function under check (D135); #s-cons otherwise],
  [A sealed program's re-run (`nfSealed`)], [Its text is made by [Close] from a call in checked code (head as above) or by `closeBlock`, which checks every arm itself before it forms the block (D76). Inherits the exception: a sealed call of the function under check, re-run after a split in its own check.], [#s-cons, with the same exception],
  [Conversion's generic call of a function value (`convFnRun` → `callFn`)], [As a call. The function's own name used as a value is refused by [Rec] ("occurs in its own body other than as the head of a call"); a closure that calls it is not.], [#s-not for a closure calling the function under check],
  [A stuck block's call (`closeBlock` → `evalCall`)], [The block's arms were checked by `closeBlock` before the call.], [#s-cons],
  [`J`'s transported term, and a match on a proof's arm, in an untyped run], [Parts of code being run, checked with it.], [#s-cons],
  [The goal's stuck scrutinee for `split` (`stuckScrutinee`)], [A sealed program's text, as above.], [#s-cons],
  [The runtime (`Runtime.closedCall`)], [Its caller passes the accepted globals; nothing in `runCall`'s type requires acceptance. Outside `checkProgram`, so outside the consistency theorem; it matters for type safety.], [#s-check by convention only],
  [A static analysis that reads an arm no run takes (the join's moved set, `Decide.jdMoves`; a block's captures)], [Checked there: a moved field exists (D94, at the join's run), a dereference is of a declared borrow (D101), names are declared (D118). Everything else in an arm of a match on a known constructor is never checked, by the ruling recorded in D118.], [#s-not beyond places and names],
)

#fault[*Predicted:* the function under check runs its own body at a typed recursive call, so a call inside that run is never tested and the check does not end. *Run:*
```
inductive BB := TT | FF
def Loop (p : BB) (n : Nat) : Nat by n := match p { TT => match n { Z => Z, S(m) => Loop(FF, m), }, FF => Loop(FF, n), }
def Sel (n : Nat) : Nat by n := match n { Z => Z, S(m) => match m { Z => (let e : Eq(Nat, Sel(m), Z) = refl; Z), S(k) => Z, }, }
```
With the `Nat` prelude: `Loop` is "undecided (call depth exceeded)", where its `FF` arm's call is not decreasing and should be rejected; `Sel` is accepted, its statement proved by running `Sel`'s own body before its check finished. Both as D135 says.]

#fault[*Predicted:* a second route to the same site, which D135's text does not name: conversion compares a closure that calls the function under check by running its generic call, which runs the body under check. *Run:*
```
inductive BB := TT | FF
def LC2 (p : BB) (n : Nat) : Nat by n := match p {
  TT => match n { Z => Z, S(m) => (let e : Eq(Π(u : Unit). Nat, λ(u : Unit) : Nat => LC2(FF, clone(m)), λ(u : Unit) : Nat => 0) = refl; Z), },
  FF => LC2(FF, n), }
```
"undecided (call depth exceeded)". The closure's call `LC2(FF, m)` passes [Rec] where the closure is formed (`m` is a strict part of `n`); comparing the closures runs it, and the run reaches `LC2(FF, n)`, untested, for ever. (With the `FF` arm returning `Z`, the same definition is rejected because the closures differ, which is right.) *Consequence for D135's landing:* the rule must sit where every run of a body starts (`callFn`, or a certificate it requires, below), not at the typed call site, or the comparison route (and the re-normalisation of the function's own sealed call after a split) stays open.]

#fault[*Predicted:* a static decision read from an arm no run takes changes what the live code may do, while the arm itself is never checked. *Run:*
```
def DeadIll (x : &Nat) : Nat := (let k = Z; match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); S(())), })
def LiveIll (x : &Nat) : Nat := (let k = S(Z); match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); S(())), })
def DeadMoves (x : &Nat) : Nat := (let k = Z; let r = match k { Z => 0, S(j) => (let c = (λ(u : Unit) : Nat => clone(*x)); 0), }; *x := 5; r)
```
With the `Nat` prelude: `DeadIll` accepted, with a closure that captures a borrow and `S(())` in its dead arm; `LiveIll` rejected ("closures capture no borrows"); `DeadMoves` rejected ("no such place `*x`"): the dead arm's illegal capture consumes `x` at the join, for the live code after it. Not a route to `False`: a static decision is the same on every path, and a dead arm's moves only add to the join's set, which only removes options. It is the class of D94, D101 and D118, which each closed one kind of unchecked thing (a field, a dereference, a name) the join reads. The model has to give the join of ill-typed code a meaning, which is the obligation D94 and D101 were landed to avoid.]

*The audit, part (b): every kind of decision, and what makes the untyped run make the checker's.*
#table(columns: (30%, 45%, 25%), align: left, table.header([*Decision*], [*Mechanism*], [*Status*]),
  [Erasure, proof flags, a function type's class and [Close] row, copy or move, η at `Unit`, statement argument in place], [`Decide.lean`, which cannot run anything (D74, D95, D96); `evalAt` asserts the pre-pass against the run's own classification (`INTERNAL [pre-pass]`).], [#s-cons],
  [What a match moves (the join), at which grain], [`Decide.jdMatch` from syntax and declared types (D84, D129); `movedPlace` resolves each place in the state, under D90's obligation 1.], [#s-cons, with an obligation],
  [When a borrow ends and what it lends; a result's label], [Fills and marks (D90 rules 1 and 2), the block's entry before its arms (D91), D99's reserved label, no block for one-constructor matches (D93).], [#s-cons under D90's eight obligations],
  [Tail position (D90's obligation 2)], [Read for every form `checkTailAt` recurses into: `let`, `;`, `split`, `rewrite`, both matches and a match on a proof pass `tailNext` in the untyped run; an ascription and `J` are not tail on either path.], [#s-check (by reading: consistent)],
  [The hint a term is given], [D124's fourteen sites, each consulting `readsHint` (and `forceHint`).], [#s-check],
  [The tests a step makes], [Typed-only checks only ever reject a definition. An untyped-only rejection makes an accepted function uncallable; the one shared test (`callPi`, D134) covers a call's head; nothing structural stops another.], [#s-not in general],
  [The reading of a binding], [D131's net, at the bindings a typed run makes; the bindings only untyped runs make ([Close]'s cells, a block's parameters) are typed by construction from declared types.], [#s-check],
)

*The redesign.* Three structural changes would make principle 4 hold by construction, and delete most of the checks above.
+ *Untyped evaluation takes a certificate only the typed check can produce.* A `Checked g` record (a Lean structure whose constructor is private to the module of `checkFix`) is put into Σ when a definition is accepted, and `callFn` runs a body only given the callee's certificate; a closure carries the certificate of the λ it was formed from. The function under check has none, so every route to running it (a typed call, a re-normalisation, conversion's generic call, a closure) closes off, as D135 rules, by one test in one place. Cost: a field in `GDef` and in closures; D135's loss (`Sel`). Deletes: the need to find D135's routes one by one.
+ *One evaluator, with the typed mode as checks only.* Today `checkTailAt` and `evalCore` are two evaluators for the forms a body ends in, and `evalCore` branches on `typed` in about forty places, some of which change what runs (a hint handed, a split rejected or run, a flag set) rather than only add a check. The redesign makes `typed` a parameter that may only guard checks and type computations: every branch that changes control flow, state or hints is moved behind one function both modes call (the hint table of D124 becomes the definition, not a list of sites kept in agreement). `checkTailAt` becomes `evalCore` with the goal as a check at the end. Cost: a refactor of `Machine.lean`'s largest functions. Deletes: D119's, D124's and D125's patches as separate rules, and the class of "an accepted function whose call is rejected", which recurred five times.
+ *Every arm is checked.* Check every arm of a match on a known constructor at its declared types, as Lean and Rust do, so that every static analysis reads checked code. Cost: reverses the ruling recorded in D118 (dead arms must be well typed; no program of the suite is known to rely on an ill-typed dead arm). Deletes: D94's run-time rejection, D101's check, D118's special walk (subsumed), and the model's obligation to interpret ill-typed arms.

== Principle 3: readings are true <sec-a3>

*What consumes it.* In the argument: every step that replaces a value by a canonical one, which keeps its meaning only if the reading is true of the type: `⋆` for a proof (@sec-arg-erase), `()` and η (@sec-arg-places), η at `Unit` inside a compared sealed program (@sec-arg-conv); and a dependent field typed by its content (@sec-arg-dep). Only that direction is used. _The first draft's reading:_ the strict reference run decides erasure, copy and move, and a function's class from the same readings the checker uses (it must, by principle 4), but the model gives each value a meaning by its _type_: a member of a proposition is a proof, irrelevant and without effect; a member of a sort is a type. The two agree only if every reading agrees with the type it reads. Where they disagree the run the model follows is not one the model can give a meaning to: an effect it does not erase, a proof it moves, a value it reads at the wrong type. Counterexamples: D54's `RunGGen(H)` (a closed `False`: a function read as a proof-class function writes), D55's two notions of proposition (closed proofs of `False`), D110's `BoomF` (`⋆` read as data of a field's declared type: a closed `False`), and D131's `V1`, re-run today:
#measured[
```
def PropF (n : Nat) : Type₁ := Prop
def V1 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : PropF(x) => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())
```
With the `Nat` prelude: rejected, "[D131] y is a proof (its type ⊤ is a proposition), but its declared type reads as data". Before D131 it was accepted and `V1(Z)` rejected.]

*How it is enforced today.* By one reader of declared types (`Decide.typeDecl`, `declOf`) that every decision consults, made syntactic (D55, D77, D80, D86, D96, D100, D116, D128), and by checks where a reading meets a type: D131's net at every binding a typed run makes (`readingAgrees`: the `let` of an evaluation, `checkTailAt`'s `let`, `checkFix`'s parameters); the pre-pass assertion in `evalAt` (`INTERNAL [pre-pass]`), which compares the reading with the run's own classification of the same term but not with its type; D55's assertion in [T-Pi]; D128's check at a declaration's parameters; and, for a type read off a value, D110's `strongStorable`, D112's leaf fields and the census behind `depFieldType`'s internal error.

*The audit.* Every place a reading is made or consumed, and whether it is tied to the type:
#table(columns: (30%, 45%, 25%), align: left, table.header([*Reading*], [*What ties it to the type*], [*Status*]),
  [A binding made by a typed run (`let`, a parameter, a λ's parameter)], [D131's `readingAgrees`: class of the reading, of the stored type and of the value.], [#s-check],
  [A binding made only by untyped runs ([Close]'s cells, a block's parameters, a called body's parameters)], [Typed from declared types written by the checker; a cell's type is a borrow's content type, in `Type₀`.], [#s-cons],
  [A pattern variable, a field], [Fields are first-order data (D36); a dependent field's type at its index is a data type or a leaf (D112).], [#s-cons],
  [A capture], [Copies the captured binding's recorded reading (D80, D82), tested where the binding was made.], [#s-cons],
  [A term that is not bound: a statement `t; u`, an argument, an arm's result, a value dropped], [The pre-pass asserts the reading equals the run's classification, both read from syntax; nothing compares either with the term's type.], [#s-not],
  [A function type's class and row (from its codomain term)], [D54: part of the Π-type, compared by conversion; D55: a codomain's declared type is a sort. A codomain that _computes_ to a sort behind a call (`PropF(Z)`) reads as data, so its function's calls run.], [#s-not (same root as the row above)],
  [The sort of a Π-type term], [Read from declared sorts (D86); [T-Pi] asserts it against evaluation.], [#s-check],
  ["Is a type" for an inductive's parameter], [D128: written as a sort exactly when it reads as one.], [#s-check],
  [Copy or move against erasure], [`declCopy` counts every proposition a copy (D100).], [#s-cons],
  [A type read off a value in a dependent field], [D110, D112 and its amendment; the census of contents.], [#s-check],
)

#fault[*Predicted:* a term whose type is a proposition, not bound to a name, reads as data when its proposition hides behind a call, so it is not erased and its effects stay; the same term with the sort written is erased. *Run:*
```
def PropF (n : Nat) : Type₁ := Prop
def W2 (x : &Nat) : Unit := ((*x := 7; J(Nat, Z, Z, λ(z : Nat) : PropF(z) => ⊤, refl, refl)); ())
def W2Runs : Eq(Nat, (let c = 0; W2(&c); c), 7) := refl
def WP2 (x : &Nat) : Unit := ((*x := 7; J(Nat, Z, Z, λ(z : Nat) : Prop => ⊤, refl, refl)); ())
def WP2Runs : Eq(Nat, (let c = 0; WP2(&c); c), 0) := refl
```
With the `Nat` prelude: all accepted. The inner term `(*x := 7; J(…))` has type `⊤` in both; in `W2` it reads as data and writes `7`, in `WP2` it reads as a proof, runs on a private copy, and writes nothing. *Not a route to `False` found:* the reading is the same on every path (principle 4 holds), and conversion cannot identify the two motives, whose Π-types differ in class (D54). *What it breaks:* the paper's appendix sentence after D131 is careful to say "a binding is a proof exactly when its type is a proposition"; the stronger "a term is a proof exactly when its type is a proposition", which erasure arguments and a type-directed compiler would assume, is false, and the reference run must erase by reading, never by type.]

*The redesign.* Make the reading a function of the type, so that it cannot disagree: either (a) complete the reader so that a call of a type function whose body is a sort reads as that sort (D131's "not done" third case of `typeFnDecl`), and then assert in `evalAt`, for every term a typed run evaluates, that the pre-pass class equals the class of its type, as it already asserts the pre-pass against the run's own classification; or (b) the converse restriction, cheaper and in D55's spirit: a type function whose body reads as a sort (`PropF`) may not be called where a type's sort is read (a codomain, a motive's codomain, an annotation), so the hidden-sort spellings are rejected where they are written. (a) deletes D131's net as a separate rule (it becomes an instance of the assertion); (b) deletes the case.

== Principle 5: the state is the whole truth <sec-a5>

*What consumes it.* In the argument: the first move of every case, which reads the checker's success as an instance of a rule at the state the rules describe (@sec-arg-induction), the meaning of a state, which exists only for values at its positions (@sec-arg-statement), and a call's arguments held where an end reaches them (@sec-arg-call). Its borrow half, exclusive access, is now principle 12. _The first draft's reading:_ the invariant every step of the simulation carries is a predicate on the checker's state: every position holds a member of its type (D104 made the temporaries positions), every live borrow is held once and lends exactly its places (the spine's (WF1), (WF2)), and nothing else in the state changes what the next step does. A value held only in a variable of the checker's Lean code is outside the predicate: a refinement or an [End] that maps over Ω does not reach it (it goes stale), and a borrow it holds has no holder (D115's 662,366 states with a loan of an ended borrow). A fact kept in the state that is not about the program is outside the predicate too: a cache (D95) or a one-shot flag left set (D130) makes the next step depend on something the invariant does not say. Counterexample with a closed `False`: D110's `ViaLoan`, a borrow stored inside a value, where no holder is looked for, and read back as data.

*How it is enforced today.* By checks at each site found: D104 and D115 push every value in flight as a typed temporary (a call's head and arguments, a constructor's fields, an assignment's right-hand side, a borrow during [Open]'s invalidation, a result across the join, [Lend]'s renaming and a frame's pop, the generic arguments of [Conv-fun] and [Conv-pi]); D106 rejects ending a borrow a temporary holds, at the one place every access ends one (`endTopLoan`); D111 asserts no borrow below a root and no loan without its borrow; D92 and D117 keep scaffolding frames from holding a loan twice. By construction: one-shot flags are consumed in one update at `evalAt`'s entry (D130); mode flags (`copying`, `erasedDepth`, `modelDepth`, `typing`) are bracketed by `onFail`; every private computation restores the whole state but the names (`restoreKeep`, `restoreNames`).

*The audit.*
#table(columns: (30%, 45%, 25%), align: left, table.header([*Site*], [*What keeps it in the state, or out*], [*Status*]),
  [A value in flight while other code runs], [Pushed as a typed temporary at each of D115's sites, found by a hunt; no structural rule forces the next site.], [#s-check],
  [`J`'s endpoint values `av`, `bv` (typed `J`) held in Lean variables while the motive, the proof and `mkEqM` run], [Not in Ω. Harmless: everything that runs meanwhile runs on private copies (principle 6), so nothing maps over the real Ω.], [#s-not (harmless by locality)],
  [One-shot flags (`tailNext`, `tailDecl`, `wantTy`, `deferCallTy`, `headEval`)], [Read and cleared in one update at `evalAt`'s entry (D130).], [#s-cons],
  [`inPlace`, set before a call's head is read, consumed by the next `readPlace`], [Between the set and the read the head's access can end borrows and so re-run sealed programs, which read places. See the prediction below: [End]'s re-runs are private (`nfSealed` restores the whole state), so the flag survives them.], [#s-cons (by `nfSealed`'s restore)],
  [Results passed back through the state: the erasure flags (`lastErased`, `lastProof`) and the deferred call's record (`callTyLater`)], [Each reader reads them right after the evaluation that set them, or saves and restores them around a drop; carried out of a private copy explicitly (flags) or not deferred across one (D132).], [#s-check],
  [Caches written by decisions], [Removed (D95); the nestable sets are declaration data (D107).], [#s-cons],
  [A borrow stored where no holder is looked for (inside a value, a type, a record)], [D48 and D110 keep a borrow out of data; types and records hold no loan ((WF11), swept, not proved); D111 asserts at overwrite, drop and read.], [#s-check],
)

#fault[*Predicted:* the `inPlace` flag, set before a call's head is read, is consumed by a read inside a sealed program that the head's own [Access] re-runs, so the head is read by move and a second call of the same function finds it moved, at the generic call and not at an instance. *Run:*
```
def PickF (n : Nat) (a : &(Π(x : Nat). Nat)) (b : &(Π(x : Nat). Nat)) : &(Π(x : Nat). Nat) := match n { Z => a, S(k) => b, }
def Inc (x : Nat) : Nat := S(x)
def T5 (n : Nat) : Nat := (let g = Inc; let h = Inc; let r = PickF(clone(n), &g, &h); match n { Z => (let a = g(0); g(1)), S(m) => 0, })
def T5Z : Nat := T5(0)
```
With the `Nat` prelude: both accepted, so the prediction is refuted. Why: `nfSealed`, the only code that re-runs a sealed program at an [End], saves the state and puts it all back but the names (`restoreKeep saved`), so whatever the re-run consumed, the flag included, is restored. That is a by-construction protection, but an incidental one: a nested run that is not wrapped this way, started between a one-shot flag's set and its read, would consume it. The redesign below removes the class.]

*The redesign.* Two changes would make principle 5 structural. (1) _Values in flight are the evaluator's stack, and the stack is in the state._ Every function of the machine that holds a value across a call to another function that can run code takes and returns it through `pushTemp`/`popTemp`, which a Lean type can force: give `eval` the type `M Unit` with its result left on the temporaries, so a value can only be held where the invariant sees it. Cost: a rewrite of every caller of `eval` (about sixty in `Machine.lean`); deletes the D115 hunt as a method. (2) _Control information is a parameter, never state._ The one-shot flags (`tailNext`, `wantTy`, `deferCallTy`, `inPlace`, `headEval`) and the results passed back through the state (`lastErased`, `lastProof`, `callTyLater`) become arguments and return values of `eval`, so nothing a nested run does can consume or clobber them and a private copy cannot discard them. Cost: wider signatures; deletes D130 and D132 as rules (each becomes impossible to write).

== Principle 1: meanings exist <sec-a1>

*What consumes it.* In the argument: the model itself (@sec-arg-statement), the meaning of a recursive function by stages (@sec-arg-rec), `Eq`'s injectivity and disjointness (@sec-arg-conv), the Σ-sets of dependent constructors (@sec-arg-dep), and, through its clause on backward functions, the hypothesis direction at a call site (@sec-arg-id). _The first draft's reading:_ the model's existence: every type of every accepted program means a set, built declaration by declaration, with `False` the empty set (docs/18's lemma that the model exists, and the eight named facts of the data model). It is consumed before any run: a step lemma about a definition is stated in the model of the declarations before it. Counterexample, re-run today:
#measured[
```
def Neg (X : Type) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
inductive Q (A : Type) (n : Nat) := MkQ(z : Q(Q(A, n), 1), e : Eq(Nat, n, 0)) | Stop(f : Neg(A, n))
```
Rejected: "field z of MkQ : Q(Q(A, n), 1): Q occurs at the parameter A of Q, which is not nestable in Q". Before D107 it was accepted, and `Q(Unit, 0)` was `Q(Unit, 0) → False`, a closed proof of `False` by typing alone.]

*How it is enforced today.* By checks in one function, `Check.checkInd`, each before the declaration enters Σ and each read from syntax and earlier declarations: first-order fields (D36), the nesting condition with the greatest set of nestable parameters stored with the declaration (D64, D107), no read of a value of the type off a field's spine (D120), one sort per knot (D121), a type parameter written as a sort (D128), the own name only in fields (D133), the declaration's own constructors unreadable while it is declared (D107); and elsewhere: `&A` only for `A : Type₀` (D66), subsingleton elimination (D45), inference of a constructor's parameters only where the model follows (D105).

*The audit, by `theory2`, of the condition the first draft named first.* D120 records a third condition of the model's grammar, (B2): a value argument does not stand at a parameter whose declared type mentions an earlier parameter whose argument varies. The checker does not enforce it: `NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)` with `DF := LeafF | NodeF(p : NF(DF, 0, ()))` is accepted (asserted in `NestReads`), as by Lean. So (B2) is #s-not, and principle 1 holds there only if the model's construction is extended to it, which is open. No route to `False` is known, and none is expected from the argument: the value argument stands where no field reads it (`f` is not in `MkNF`'s fields), and a value argument that used the declared type negatively would have to be a closed function out of the type being declared, which cannot be written while its constructors are unreadable (D107). The rest of the first draft's note:  The history suggests where to look: six of the conditions above (D105, D107, D120, D121, D128, D133) were found by the lanes building the model, each the model failing at a declaration the checker accepted. The model's grammar has one condition the checker does not state, (B2) of D120 ("a value argument does not stand at a parameter whose declared type mentions an earlier parameter whose argument varies"), recorded as open; that is the first site to test. #s-open

*The redesign.* The conditions are a grammar: declarations the model's construction accepts. Write the grammar once, as a syntactic predicate on a declaration in its own module (as `Decide.lean` is for decisions), with the model's construction proved against the same predicate, and make `checkInd` call only it. Cost: restating six checks as one; deletes the drift between the model's grammar and the checker's tests, which is how D120's (B2) is open today.

== Principle 2: identifications hold <sec-a2>

*What consumes it.* In the argument: every ≡ premise, as an equality of meanings under every assignment: the leaf's type against the goal (@sec-arg-induction), conversion, `Eq` and `J` (@sec-arg-conv), the arms' types of a block (@sec-arg-split), a record's exact key (@sec-arg-close). _The first draft's reading:_ the soundness of conversion and of `Eq`'s computation (docs/18's conversion soundness, proved on a branch for values with no code): an identification moves a member of one type into another. Counterexample: D84's `Same`, where two observations each holding `⊥` were identified at the generic call and differed at an instance; and D30's closures compared by their results only.

*How it is enforced today.* By the definition of conversion: functions and Π-types are compared by their generic calls (D30, D48), with their class and row (D54); `J` computes only at convertible endpoints (D56); an impossible arm is stuck (D58); `⊥` is a value of its own because moves are definite on every path (D84); keys are compared exactly (D108); a comparison keeps nothing but names (D103).

*The audit, reframed by the argument.* The first draft asked of each identification site whether it is preserved by every refinement. The argument does not need that: an identification is a check made at one state, and what it needs is that the two sides mean the same under _every_ assignment of that state, which @sec-arg-conv argues rule by rule. One rule rests on another principle: the comparison of code (two sealed programs compared by their texts) is sound because every sealed program has [Close]'s shape, so the only decision in it that reads an embedded value's reading is η at `Unit` (principle 7 with principle 3). The one sealed value in the checker that is not [Close]'s, `hintLater` (@sec-a6), is a hint that is not stored; that it never reaches a comparison is open. The first draft's list of sites: the identification sites are `conv` and its consumers (`expectTy`, [Eq-refl] in `mkEqM`, `J`, `trans`, [Rewrite]'s occurrences, a goal), the record lookups (`neutralLookup`, `substV`), [Rec]'s strict subterms, and `convStack` (D83's and D108's audits list them). Each was audited in D83 and D108 for one fault class each (values with `⊥`; equality up to recorded parameters). What no audit has done is the general question this principle asks of each: is the identification preserved by every refinement of the unknowns? For conversion on code that rests on "every sealed program has the shape [Close] gives it", swept, not proved (docs/18's risks). #s-open

*The redesign.* Identification by evaluation is what makes Ochr's equality useful, so it cannot be replaced; what can be made structural is its monotonicity under refinement. Conversion answers from normal forms in a world; it is sound for every instance if every step of normalisation commutes with refinement (principle 4 for conversion's own runs, at unknowns). The redesign is the same as principle 4's: conversion's generic calls are untyped runs, and a certificate and one evaluator make them the checked computation.

== Principles 6 to 12 <sec-a6>

For each: what in the argument consumes it, and how it is enforced, read by `theory2` against the code at 105021637 (`Machine.lean`, `Env.lean`, `Obs.lean`, `Decide.lean`); the first draft's claims came from docs/18 and had not been re-read. The historical counterexample of each, re-run by the first draft, is in its row.

#table(columns: (14%, 26%, 42%, 18%), align: left, table.header([*Principle*], [*What consumes it*], [*Enforcement, as read in the code*], [*Open*]),
  [6 Effects stay local], [The frame property: a call in place is its isolated run plugged in (@sec-arg-call); the same at a statement's call site (@sec-arg-id) and for a block's arm (@sec-arg-split); a function's meaning fixed by its generic observation (@sec-arg-conv); private copies and types formed once (@sec-arg-erase). Counterexample: D103's leftover record (`Units.CompareEmpty`).], [#s-cons for what survives a private run: two functions decide it, `restoreKeep` (names, the types of new unknowns, records) and `restoreNames` (names only, for comparisons, D103). Statements run through `Env.inStatement` (25 references) and scaffolding through `Env.privately` (22), both wrapping `onCopy`, private to `Env.lean`, which raises `privateDepth`. *Correction:* the claim that every discarded run is one of the two is false as stated. Six more save and restore the state directly: `nfSealed` and `stuckScrutinee` (a sealed program's re-run), `checkFix` (a λ checked where it is formed), with `restoreKeep`; `conv`, `convPi` and `convFn`, with `restoreNames`. These do not raise `privateDepth`, so `endTopLoan`'s assertion of (L4) stays armed inside them, and the first three restore on success or stuck only, not on an error, which ends the definition anyway (principle 5).], [The frame property itself is unproved for today's checker (docs/18: its first statement was false).],
  [7 Closing off rebuilds the call], [[Close] is exact; re-runs compute the text's meaning; one text, one value; blocks are calls of their captures (@sec-arg-close, @sec-arg-split); sealed programs have [Close]'s shape, which the comparison of code needs (@sec-arg-conv).], [#s-cons: `closeCall` makes the sealed programs of the state (four constructions, each through `canonNeutral`); blocks go through `closeBlock` (25 references), which computes captures in `blockCaptures` (K1) and calls `closeCall`; `nfSealed` re-runs, refusing a text that holds a loan (D97); substitution (`substEnv`) and re-normalisation (`renormAll`) share `Env.mapState`. *One exception found:* `hintLater` (D124) builds a sealed value `⌈⋄hint …⌉` that is not [Close]'s: a deferred hint, handed down and read only by `forceHint` where `readsHint` says a hint is read.], [That `hintLater`'s value is never stored (not audited exhaustively). Redesign: give hints a type distinct from `Value`.],
  [8 Worlds are exclusive], [Every assignment has one arm, and a fact of one arm never constrains another's assignment (@sec-arg-split); records as path conditions (@sec-arg-close); the goal refined on a path (@sec-arg-induction). Counterexample: `EtaBoom` (D79), asserted in `CaseSplits.ArmEta`.], [#s-cons: every arm of a split runs in `Env.inWorld` (eleven sites in `Machine.lean`: `splitArmsThenClose`, `evalMatchInd`, `checkTail`'s arms, `closeBlock`'s arms), whose exit (`exitWorld`) restores every component of the state but those listed, so a new component is dropped by default.], [—],
  [9 Whole where relied on], [Membership at whole reads, ends, captures, observations and returns, at every future of the parts still lent (@sec-arg-dep); a block's neutrals checked at its arms' returns (@sec-arg-split); [Def]'s cells (@sec-arg-induction). Counterexamples: `GetN` (D73), `JLie` (D75), asserted rows.], [#s-cons for returns: `closeBlock` runs its arms itself and calls `bodyReturns` at each arm's end (`Machine.lean`, the arm loop), the same function `checkFix` calls at a body's return; no block can be formed without it (D76). #s-check for the rest: [Repack] at whole reads, borrows and captures; a lent part checked as a fresh unknown (D73); the `⊥` tests at read, borrow, capture and end (D53, D98, D127).], [The soundness of [Repack] at a read for dependent constructors has no owner (docs/18).],
  [10 Recursion descends], [The outer induction (@sec-arg-induction); every run of a body during a check is of something earlier or smaller (@sec-arg-call, @sec-arg-rec). Counterexample: `CapSplit` (D78), rejected.], [#s-cons for recognition: one function, `recFrameOf`, decides whether a call belongs to a recursion entry, by a mark on the binding. #s-check for descent: `recCheck` at every typed call, including calls in nested functions and block arms. The order: a global enters Σ before its own check and is kept only if accepted (`Check.lean`), and every name is checked declared before anything runs (D118).], [D135 is termination, not consistency (@sec-arg-call).],
  [11 Observation names every owner], [The [Call-type] step, both directions (@sec-arg-id). Its adequacy clauses are not consumed (@sec-arg-unused).], [#s-cons: `Obs.footprint` takes its roots from the sides' terms (`placeOccs`), and `Obs.owners` follows every occurrence of a loan or a mark outward; one function, `obsResult`, observes a result for `Id` and for [Conv-fun]. `Decide.typeState` reads the type-state from syntax (adequacy).], [Known gap of adequacy, not consistency: where a re-pointed borrow of `Unit` points (D84's `RU`).],
  [12 Access is exclusive], [The meaning of a state; joint injectivity of the contexts around a loan, and so the hypothesis direction of [Call-type] and a returned borrow's backward function (@sec-arg-id); writes at a field at every future (@sec-arg-dep); clean inputs to [Close] (@sec-arg-close); the leaf rules (@sec-arg-places).], [#s-check: [Access] in `accessPath`, `accessInside`, `accessNeutralHead`; every end of a borrower found from a place of the top frame goes through `endTopLoan`, which rejects ending a borrow a value in flight holds (D106) and asserts (L4) outside private copies; [End] requires a whole content (D98); D111's assertions at overwrite, drop and read; `closeCall` asserts loan-free inputs (C8).], [That every step keeps (WF1) to (WF3): swept on 2,137,352 states, not proved.],
)

= The argument from the principles alone <sec-argument>

_Written by `theory2` after reading the paper whole, `RULES.md`, the nine model notes and docs/18's shape of the argument; it replaces the first draft's three cases._ This section proves consistency from the principles, as a paper proof a reader can check case by case. It takes from docs/18 only the _shape_ (a set model, a meaning for every state the checker reaches, and the checker's run read as computing those meanings) and argues every step from the principles of @sec-principles, citing each by number and name and nothing else: no fact about the code and no lemma of the mechanisation. The two inductions it sets up are its own. Where a step needed more than the first draft's principles said, the step names what was missing, and each such finding is now a clause of a principle (@sec-revision). @sec-arg-unused lists what no step uses. The cases come in order of risk, the riskiest first.

== The statement, and what it is about <sec-arg-statement>

*Theorem (consistency).* For every program the checker accepts, every accepted definition $d_k$ means a member of the meaning of its declared type. In particular an accepted constant $c : T$ means a member of $deno(T)$, so $T$ does not compute to `False`, whose meaning is empty.

*The model* is principle 1 (meanings exist). Each type value means a set; `False` means $emptyset$; a proposition means $emptyset$ or ${bullet}$, and every proof means $bullet$; `Eq(A, a, b)` means ${bullet}$ exactly when $a$ and $b$ mean the same element; a function type with borrow parameters means the functions from the contents of the borrowed places and the other arguments to the result together with the final contents of the borrowed places, and, for a returned borrow, to a _backward function_ from the value finally left in it to those final contents, which must be injective; a Π-type into propositions means the truth value "true at every argument"; a recursive function means its limit by stages on the size of its decreasing argument.

*The meaning of a state.* A state Ω the checker reaches means something under two choices. An _assignment_ γ gives every unknown σ that Ω names a member of the meaning of its type, and meets every record in force in the current world: a refinement $sigma := r$ when γ(σ) is the meaning of $r$, a generalisation $n := sigma$ when γ(σ) is the meaning of $n$ (principle 8, worlds are exclusive: the records in force are exactly the current world's). A _future_ φ gives every live borrow a whole member of its content's type, the content it will hold when it ends (principle 12, access is exclusive: a borrow ends only over a whole content). Under γ and φ each position of Ω means: an unknown its value under γ; a loan, or a place marked lent, the future's value of its borrow, or the content it marks; a place holding a borrow that borrow's current content; a sealed program the meaning of running its text (principle 7); `⊥` the value _moved_; a constructor value its tree; a closure a function. This is defined only because every value the checker holds is at a position of Ω with a stored type (principle 5, the state is the whole truth), and the live borrows form a forest in which each has one holder and lends exactly the places that hold its loans (principle 12).

*The meaning of a term*, run from a state's meaning, is its _reference run_ (docs/18, the strict reference run): the rules of the machine, except that a call applies the meaning of its callee instead of running its body, and a match reads its scrutinee's constructor under γ instead of splitting. Every decision the rules make (whether a term is erased, copy or move, the places a match moves, which borrows end where, η, the parameters a constructor records) the reference run makes as principle 4 says they are made: as a function of the code and the declared types.

*Good states.* A state is good when, under every assignment and every future, every position with a stored type holds a member of that type, or an _open_ member (a value of a dependent type in the middle of a mutation, or partly moved: principle 9).

== The induction <sec-arg-induction>

*Outer induction:* on the position of $d_k$ in the program, and, for an assignment γ of $d_k$'s generic call, on the size of $d_k$'s decreasing argument under γ (principle 10). Its hypothesis: every earlier definition, and $d_k$ itself at every smaller size, means a member of its type.

*Inner induction:* on the checker's derivation of $d_k$ (its typed run at the generic call, case tree included). The claim, for each step from a good state Ω running a term $t$ to a value $v$ of type $A$ and a state Ω': for every assignment γ of Ω, extended at each split by the fields of γ's value of the scrutinee and following that arm, and every future φ,
- (i) the reference run of $t$ from Ω's meaning is defined, returns $v$'s meaning, and leaves Ω''s meaning;
- (ii) $v$'s meaning is a member of $A$'s;
- (iii) Ω' is good.
An _untyped_ run (a callee's body run in place, a sealed program's re-run, a generic call a comparison makes) satisfies (i) and (iii) for code whose meaning is a member of its type, which the outer hypothesis supplies (@sec-arg-call).

*From the claim to the theorem.* $d_k$'s derivation ends, on each path of its case tree, at a leaf $(Omega', v, A)$ where [Def] checked that the frame pops and that $A equiv G'$, the goal as refined on the path. Each γ reaches exactly one leaf: at each split, γ's value of the scrutinee is a constructor of its type and selects one arm (principle 8). At that leaf, (ii) puts $v$'s meaning in $deno(A)$; principle 2 (identifications hold) gives $deno(A) = deno(G')$; and $deno(G') = deno(G)$ under γ, because $G'$ is $G$ with the path's refinements substituted, which γ meets (principle 8). The pop ends the borrow parameters, so their cells receive their final contents, which [Return] checked whole (principle 9, whole where relied on). So under every γ, $d_k$'s result and the final contents of its borrowed places are members of what its type says: membership in its Π-type, but for one clause, that a $d_k$ returning a borrow has an injective backward function. That clause is proved in @sec-arg-id, and needs principle 12.

*The first move of every case* reads the checker's successful step as an instance of a rule of the paper, taken at the state the rules describe. That needs principle 5 (every value the checker holds is in its state, nothing outside the state decides a step, and no failure becomes a value); it is not repeated below.

== Case 1, the riskiest: `Id`, and a statement used at another state <sec-arg-id>

*Computing `Id`* ([Id]). At Ω, `Id(A, t, u)` runs each side on its own copy of Ω (principle 6, effects stay local) with the typing judgement, ends every borrow, and conjoins the equation between the two results with those between the two final contents of each place of the footprint: the places the sides write or borrow, each traced to its owners (principle 11). The model's `Id` is the paper's (the paper's figure for `Id`, §5.2): the equality of the two observations at those places. Each side's run computes the side's meaning, by the inner hypothesis (i) applied to the side's run on its copy. Ending every borrow fixes each future at its holder's content, which in meaning is a substitution, and substitutions along a forest commute, so the order does not matter (principle 12). Each equation means what it says (principle 2). So the conjunction means the model's `Id`, and computing `Id` is exact.

This used neither that the footprint names _every_ place a side can change (footprint sufficiency) nor that the two sides leave the same moves and borrows ([Id-typestate]). With `Id` meaning the equality at the footprint, both are about whether `Id` says what its user means (adequacy, which is no longer a target), not about whether the checker computes it truly.

*Using a statement at another state* ([Call-type]). This is the step the paper names the hardest. A definition $d$ with parameters $overline(x) : overline(A)$ and codomain $B$ was checked at its generic call, where each borrow parameter $x_i : \&T_i$ lends a fresh cell $c_i$ holding an unknown $sigma_i$. A caller calls it at a call point Ω with arguments $overline(w)$; the call's type is $B$ evaluated with the parameters bound to $overline(w)$, at Ω: the callee's statement observed through the caller's places. Let $overline(d)$ be the arguments' meanings (for a borrow argument, its content's). The callee's meaning $F$ is a member of its type (outer hypothesis), and that membership speaks of the _generic_ statement at $overline(d)$; the caller holds the _call-site_ one. Both directions are needed: a hypothesis true at the call site must be true generically at $overline(d)$, so that $F$ applies; and a conclusion true generically must be true at the call site, so that the call's value is a member of the type the checker gave it.

Everything in $B$ other than an `Id` is computed from the parameters' meanings alone, the same at both states: a type is formed once, closed over values (principle 6), and every decision in it is a function of its code (principle 4). So the two evaluations of $B$ differ only inside its `Id`s, and only in their footprints. A footprint's roots are read from the sides' syntax, the same at both (principle 11), so the footprints differ only in the owners of the borrow parameters' loans: the one cell $c_i$ generically, and at the call site the set $O_i$ of the caller's places that own the argument's loan $ell_i$ (several when the argument reborrows through a borrow that a stuck call returned, whose hole sits in the fill of every place that call borrowed).

Each side's run at the call site is its run at the generic state plugged into the caller: it reaches the caller only through the loans its borrow parameters hold (principle 6). So once a side has run and every borrow has ended, each owner $o in O_i$ holds $C_o [f]$, where $f$ is the final content of $ell_i$ (the generic cell's final content) and $C_o$ is the context around $ell_i$'s loan at $o$, the same for both sides. The conclusion direction follows: if the generic equations hold, $f_t = f_u$, so $C_o [f_t] = C_o [f_u]$ at every owner. The hypothesis direction needs the converse, that $C_o [f_t] = C_o [f_u]$ at every $o in O_i$ gives $f_t = f_u$: the contexts must be _jointly injective_. They are, for three reasons.
- The footprint at the call site holds _every_ owner (principle 11). With one owner of two, the context can be constant: `Pick(n, &a, &b)` at an unknown `n` puts its hole in the fills of both `a` and `b`, and in the world where `n` is a successor `a`'s fill no longer depends on it (the counterexample `BadD18`, the paper's table of side conditions).
- A context is built only by the steps that place a loan: a borrow (the identity); a reborrow (a loan inside another borrow's content, composed with that borrow's context); a stuck call returning a borrow (its hole in the fills of the places it borrowed: the callee's backward function, injective by principle 1 for an unknown callee and by the outer hypothesis for a checked one); a call that ran and returned a borrow (its mark on each lent place: a constructor context around the hole, or none); and the end of a borrow whose content holds the loan (composition). Each of these is injective, jointly over the owners.
- Nothing else changes a context while its loan is live. No read, copy, match, overwrite or drop touches a live loan, because every access first ends the borrows that lend what it touches (principle 12); and a sealed fill that holds a live hole is never run (principle 7). So a context, once built, changes only by composition.

_What was missing._ The last bullet is the one step of this case that no principle of the first draft stated. Its principle 5 said that a borrow's loans "sit exactly where it lends", which does not say that nothing touches them, and its principle 1 did not say that backward functions are injective. Both are clauses now: principle 12 (access is exclusive, split from 5) and the last clause of principle 1.

*The injectivity clause of membership.* The same argument proves the clause that [Def] left open (@sec-arg-induction): a $d_k$ returning a borrow has an injective backward function. At a leaf, the result is a borrow whose loan the pop has carried into the cells (a borrow of one of $d_k$'s own locals cannot be returned: it is a value in flight when the local dies, an error by principle 12), and the cells' contents are contexts around that loan, built and kept as above, so jointly injective in its final value.

_Verdict:_ closes, from principles 1, 2, 4, 6, 7, 11 and 12, with the two clauses above, which are new.

== Case 2: dependent fields <sec-arg-dep>

The steps: an assignment to a field of a dependent constructor (a strong update of a tree field; a checked write of a proof or leaf field; a write or borrow through an index field, which invalidates the fields whose types mention it), a read or borrow of a field typed by position, a split of a neutral of a dependent type by its telescope, and the end of a borrow into such a value.

The model (principle 1) gives a dependent constructor a Σ-set: tuples whose later fields lie in sets computed from the earlier ones. Principle 9 (whole where relied on) gives the invariant: a value may be _open_ (a later field outside the set its earlier fields compute, a field moved or invalidated) while the code that opened it runs, so a good state's positions hold open members, and at every point where code relies on a value's type the value is whole. Each step keeps the state good:
- A write through an index field invalidates every proof field and leaf field whose type mentions it, so no field is left claiming a type its new index refutes, and open membership is kept (principle 9).
- A tree field takes the type of what it holds, and a leaf or proof field keeps its declared type at the current index: a type is read off a value only where the value says its type (principle 3, readings are true, its last clause). A strong update stores only a value whose content says its type, so the field's type as the checker reads it is its type in the model.
- A whole read, a borrow's end, a capture, an observation and a return are points where a value is relied on (principle 9), so the value is a member there. A part still lent at such a point may receive any member of its borrow's type before its borrow ends, so the value must be whole at every future of the parts still lent; the checker checks a lent part as a fresh unknown of its type (D73). _What was missing:_ the first draft's principle 9 did not say "at every future", which is the clause `GetN` broke before D73. It is a clause now.
- A write at a field must find the field's path under every future, since a state means a function of the future. After the write's [Access] no live loan or mark lies on the path (principle 12), so the path exists in every future.
- A split of a neutral of a dependent type by its telescope assumes that the neutral means a whole member. An unknown does, by the definition of an assignment; a stuck call's result or fill means the callee's result or final contents, members by the outer hypothesis; a block's means what its arms return, each checked whole at the arm's end (principle 9, its producer clause, with principle 7: a block is a call of its captures).

_Verdict:_ closes, from principles 1, 3, 7, 9 and 12. The meaning of an open value is the model's design (principle 1); what the principles give is that the checker reads it truly (3) and never lets it escape (9).

== Case 3: closing off a stuck call, and re-running it after a later split <sec-arg-close>

*Closing off* ([Close], [Lend]). At a call point the call $f(overline(w))$ gets stuck; the checker discards the partial run, consumes the borrow arguments, gives each borrowed place a fill #seal[$L; C; c_i$] and returns #seal[$L; C$] (for a returned borrow, a borrow of a fresh label, whose hole is in every fill). The reference run applies $f$'s meaning to the arguments' meanings: its result is the forward value, and each lent place means its component of the final contents, or of the backward function at the returned borrow's future value. The two agree because a sealed program means the meaning of running its text (principle 7), and the text rebuilds the call exactly: the same function value, the other arguments as their values, each borrowed content in a fresh cell (principle 7), with nothing else of the call point reaching the callee (principle 6). Each output is its own program, whose last read copies, so reading one output moves nothing another needs (principle 7). The inputs are loan-free and whole, because [Access] ended the loans inside them and a borrow passed on is whole (principles 12 and 9), so the text is closed. Whether a call lends its result the places it borrowed does not depend on whether it ran or closed off (principle 4), so the borrows live afterwards, and what they lend, are the reference run's.

*Re-running after a split.* A later split substitutes a constructor pattern for an unknown at every position of the state, and re-runs every sealed program it changes (principle 8, the substitution is total; principle 7, re-run exactly where an input changes). Under an assignment that meets the refinement, substitution changes no meaning. The re-run is an untyped run of the text from an empty frame, which computes the text's meaning because the text is a member's code (its head is an earlier definition, the definition under check at a smaller size, an unknown function, or a block whose arms were checked: the outer and inner hypotheses), and it takes the decisions that meaning takes (principle 4). Its head call does not close off again (principle 7), so the re-run computes or leaves the text as it was. A text still holding a hole is never run (principle 7, D97): its meaning is a function of the future, and it stays so until the hole is filled. _What this removes:_ the paper's route assumes _hole parametricity_ (a fill's run never inspects its hole), an assumption about runs. In this argument no run ever meets a live hole, so it is not needed.

*Generalising* ([Split-gen], `split f in t`). A sealed scrutinee $n$ is replaced everywhere by a fresh unknown σ and recorded as $n := sigma$. The record is a path condition, γ(σ) the meaning of $n$, which every later derivation of the same text meets, because one text has one meaning (principle 7: the text is closed and the machine deterministic), looked up by exact equality (principle 2: a record's key is compared exactly, D108). The record is in force only in the world that made it, since in a sibling world the same text can have another type (principle 8; the closed proof of `False` through `g(())` and `T(n)`, the paper's §6.4).

_Verdict:_ closes, from principles 2, 4, 6, 7, 8, 9 and 12.

== Case 4: a call that runs in place, and what it leaves in the caller <sec-arg-call>

[T-Call] with a callee that runs: the checker checks the arguments and the call's type, then runs the callee's body untyped in a frame pushed on the caller's, and pops it. The reference run applies the callee's meaning. Three things make the checker's run compute it.
- _The callee's meaning is a member._ The callee is an earlier definition, the one under check at a smaller size, a closure formed and checked by a typed run, or an unknown (closed off at once: case 3). Every run of a body that the check makes is of one of these, because every call the check makes passes [Rec] where it is written, and a call that passes [Rec] at the generic call is on a smaller entry value at every instance (principle 10). _What was missing:_ the first draft's principle 10 said how a recursive call is checked, but not that every call is of something earlier or smaller; that order is what the outer induction needs, and it is a clause now. The rest of the first draft's principle 4, "only checked code runs", is not used: D135's `Loop` and the first draft's `LC2` run the body under check at a call that has not yet been checked, but a definition is accepted only if every such call passes [Rec], so in an accepted definition every run of its own body is at a smaller size; before acceptance such a run can only fail to end, which is undecided (principle 5), never an acceptance. D135 is a fault of termination, not of consistency.
- _The run in place is the run in isolation._ A body names only its own frame, reaches the caller's places only through the loans its borrow parameters hold, and gives them back by ending those borrows (principle 6). So its run in place is its run from a fresh frame with cells, plugged back into the caller: the callee's meaning applied. The arguments stay at positions of the state until the frame binds them, so an end during the call reaches them (principle 5).
- _It decides as its meaning does._ The untyped run takes every decision as a function of the code (principle 4): erasure, copy and move, the join's moves, borrow ends, η, and a constructor's recorded parameters (the hint, restored by D124). The hint is a decision because a constructor value's meaning includes the parameters it records.

What the call leaves in the caller: its result; the final contents of its borrowed places, at their loans; and, for a returned borrow, that borrow lent every place its borrow arguments lend (principle 4: the same whether it ran or closed off). The pop drops the frame's bindings, and a binding that dies while a value in flight borrows it is an error (principle 12). The call's type is its codomain at the call site, which case 1 relates to the callee's meaning.

_Verdict:_ closes, from principles 4, 5, 6, 10 and 12, with case 1.

== Case 5: a split on an unknown, and the join <sec-arg-split>

[Split] checks each arm in its own world, under the refinement of the scrutinee σ to that arm's constructor with fresh fields. A match not at the end of the body is then closed off as a _block_, an anonymous function of the places its arms use, and the rest of the body is checked once, from the state the block leaves.
- _Every assignment has one arm._ γ(σ) is a member of an inductive type, a tagged union, so exactly one constructor matches it, and extending γ by its fields meets that arm's refinement. What an arm establishes about its refinement is visible in it alone (principle 8), so γ is never asked to meet another arm's.
- _The block means the match._ The block's sealed programs mean the run of its text, which is the arm γ selects run in the block's frame on the places it captured (principle 7: blocks are calls). The block takes every place any arm uses at least as strongly as any arm uses it, by move if an arm moves it and by borrow if an arm writes or borrows it (principle 7, its capture clause), so its fills compute every place the selected arm changes. The arm run in the block's frame is the arm run in place, plugged in (principle 6).
- _The state after the block is the state after the arm._ The reference run runs the selected arm directly, after the same accesses at the match's entry, and then drops at the join the places the arms move. The block's entry, the places it moves and their grain are read from the code (principle 4), so after the block the checker's state has the same borrows ended, the same places moved (`⊥`, _moved_ on both sides), and fills meaning the arm's final contents.
- _The block's result is a member._ Each arm's result is checked against the block's type, and each arm's return is checked whole, its borrowed captures included (principle 9: a block's arms are the returns of a producer). The arms' types are convertible (principle 2), and a type convertible across sibling worlds names no arm's own unknowns, since names are never reused.
- A match at the end of the body is not closed off: its arms are branches of the case tree, each a world (principle 8), and each ends with the join an instance's arm makes (principle 4). A match on a value of a type with one constructor refines it in place, recorded in its world (principle 8).

_Verdict:_ closes, from principles 2, 4, 6, 7, 8 and 9.

== Case 6: recursion <sec-arg-rec>

`fix f (…) : B by x_j := b` means its limit by stages (principle 1). [Rec] checks every call recognised as recursive, by the name `f` binds for itself and never by comparing function values (which refinement changes), to pass at position $j$ a strict part of $x_j$'s entry value as refined so far (principle 10). Refinement only adds constructors, so under every γ that meets the path the argument's meaning is a strict part of γ's entry value, of smaller size: the stage below is the function itself there, which is membership, and the outer hypothesis covers the call. Recursion is never on a proof, whose meaning is $bullet$ and has no size: the decreasing parameter's type is data (principle 10, with principle 1). Every call is of an earlier definition, of a value, or of `f` at a smaller size (principle 10's order, case 4).

_Verdict:_ closes, from principles 1, 8 and 10.

== Case 7: conversion, and `Eq` and `J` computing <sec-arg-conv>

Every "≡" premise of the rules is used as an equality of meanings under every assignment: principle 2 (identifications hold). Rule by rule:
- Values are compared by their structure, constructors by tag and fields (the parameters they record are fixed by their type), sealed programs by their text. Equal parts give equal meanings, provided a text's meaning depends on its embedded values only through their meanings. The decisions in a text can read an embedded value's _reading_ (its declared type), which convertible values need not share: `F (n : Nat) : Unit := ()` and `H (n : Nat) : TF(Z) := ()` are convertible, and a call of one is copied where a call of the other is moved (docs/18, conversion). But a sealed program has [Close]'s shape (principle 7: nothing else makes one), and in that shape the only decision that reads an embedded value's reading is η at `Unit` on the head call's result, which sends a member of `Unit` to itself (principle 3). So texts with convertible parts mean the same.
- Two Π-types are compared at generic arguments, with their class and borrow flag, which are part of their meaning (a Π-type into proofs is a truth value); compared by their parts (the fast path), their recorded readings are compared too. Generic arguments range over every member, and the evaluation of the components is the same function of the code at every argument (principle 4), so equal meanings there are equal meanings everywhere.
- Two function values are compared by the observations of their generic calls: their results and the final contents of their cells, a returned borrow observed through a fresh value written through it. A function's meaning is fixed by that observation, because its only effects are its result and its borrowed places (principle 6), and the observation's runs are untyped runs of members (case 4).
- The relation is the least one: a comparison that needs itself answers "not convertible" (principle 2), and every "not convertible" fails safe, as an error, a stuck term or a later check.
- `Eq` computes by injectivity and disjointness of constructors (principle 1: an inductive type is a tagged union of tuples; for a dependent constructor only while its index fields are convertible), by reflexivity (conversion, above), and on `⊥` as a value of its own, which means _moved_ alike on every run because moves are decided by the code (principle 4).
- `J` computes to its transported term only at convertible endpoints (principle 2), where the motive's two instances mean one set; otherwise it is closed off as a block of its transported term (case 5), which computes once a refinement makes the endpoints convertible. Under a hypothesis equating unequal values no assignment exists, so nothing is claimed there. `rewrite` and `split f in t` never run: `rewrite` checks its term against the goal with one side of a true equation put for the other, the same proposition by principle 2, and `split` is a generalisation and a split (cases 3 and 5).

_Verdict:_ closes, from principles 1, 2, 3, 4, 6 and 7.

== Case 8: erased terms, proofs, and types formed once <sec-arg-erase>

An erased term (a proof, a type, anything in a type or erased position) runs on a private copy of the state, which is thrown away but for fresh names and records that mean the same in every state of the world (principle 6). The reference run erases the same terms (principle 4), so afterwards both are at the state before. A proof's value is `⋆`, which means $bullet$ and is a member of its type only if that proposition is true; the erased run's derivation shows it is (inner hypothesis (ii), on the copy), and a term is replaced by `⋆` only when its type is a proposition (principle 3). A lemma's call is not run: its type is its codomain at the call site, which case 1 relates to the lemma's meaning, under the outer hypothesis. A type is formed once, closed over the values of its free variables, so later mutation does not change its meaning, and [Call-type] rebinds only the parameters (principle 6).

Principle 3 is used in one direction only: a term replaced by `⋆` has a type that is a proposition. The converse fails (the first draft's `W2`, @sec-a3: a term of type `⊤` that reads as data and writes), and the argument does not need it: that term runs, with its effects, in the checker and in the reference run alike.

_Verdict:_ closes, from principles 3, 4 and 6.

== Case 9: places, reads, writes, borrows and ends <sec-arg-places>

The machine's leaf rules. Before a place is read, borrowed, assigned or matched, [Access] ends the borrows that lend what is touched (principle 12), so its content then holds no live loan and its meaning does not depend on the future. An end fixes the future at its holder's content, which is whole (principle 12); it only loses information. A read takes the place's stored type, its declared type (principle 5), and a whole read is a point where the value is relied on (principle 9). A written value was checked convertible with the place's type (principle 2). η at `Unit`, η at a type with one constructor and `⋆` at a proposition replace a value by its canonical one, which keeps its meaning only because the reading is true (principle 3). Whether a read copies or moves is a decision of the code (principle 4), so the checker and the reference run leave the same places moved. A dropped value's borrows end, and dropping a live loan while a value in flight borrows it is an error (principle 12).

_Verdict:_ closes, from principles 2, 3, 4, 5, 9 and 12.

== What the argument does not use <sec-arg-unused>

- _Principle 11 beyond its first clause._ That the footprint names every place a continuation could read, that the sides leave the same moves and borrows ([Id-typestate]), and where re-pointed borrows point ([Obs-ref]) make `Id` mean what its user means (adequacy, dropped as a target on 13 November); that the conjunction comes in one order makes the two paths' conjunctions convertible (completeness). Consistency uses only that the observed places are read from syntax and every owner is observed (case 1). The other clauses stay, marked as adequacy's.
- _Principle 4's clauses about untyped runs as such:_ that they run only checked code (beyond principle 10's order), can run every form the check accepts (D125), and make the tests the check made (D134). Their faults made accepted functions uncallable (a failure of type safety), never an acceptance. Kept, marked as type safety's.
- _Principle 3's agreement among readers_ ("every reader of one fact gives the same answer") is principle 4 applied to readings; and the converse of a reading (a propositional type always reads as a proof) is not used (case 8).
- _The first draft's principle 12_ (undecided decides nothing) is used only in the first move of every case, reading a success as a derivation of the rules; it is now a clause of principle 5.
- Every principle of the revised list is used by at least two cases.

== What the argument found <sec-arg-found>

No case needed something the design does not provide, so nothing here says the design is wrong. Five clauses were missing from the first draft's statements, each now in its principle (@sec-revision): that nothing touches a live loan (principle 12, case 1); that backward functions are injective (principle 1, case 1); "at every future of the parts still lent" (principle 9, case 2); the order of calls (principle 10, cases 4 and 6); and that the parameters a constructor records are a decision (principle 4, case 4, already among the first draft's decisions, now with its reason). One assumption of the paper's route is not needed: hole parametricity (case 3). D135 is a fault of termination, not of consistency (case 4). And one risk predicted from case 8 is closed already:

#measured[*Predicted from case 8:* a binding whose declared type is a call of a type function whose arms are Π-types of different classes takes its class from a normal form (the two-paths census's site 7, "the weakest argument in this census"), where principle 3 would have to hold of a stuck type. *Run:*
```
def PT (n : Nat) : Type₁ := match n { Z => Π(x : &Nat). Type, S(k) => Π(A : Type). A, }
def L (n : Nat) (p : PT(n)) : Nat := (let c = 0; let T = p(&c); c)
def L2 (n : Nat) (p : PT(n)) : Nat := match n { Z => (let c = 0; let T = p(&c); c), S(k) => 0, }
```
With the `Nat` prelude: both rejected at the binding of `p`, "[D77] this binding's type is computed by a type function whose arms are Π-types whose calls are erased differently". D77 removed the site; the census's argument for it is obsolete.]

*Where the argument is weakest.* It is a paper proof, and three of its steps rest on facts the principles state but nobody has proved of the checker: the frame property (principle 6, cases 1, 3, 4, 5), that every step keeps the borrows a forest with exact lending (principle 12, swept on 2,137,352 states and not proved), and that every decision in an untyped run is computed by the deciders the reference run uses (principle 4, by construction for the decisions in `Decide.lean`, by D90's unproved first obligation for a block's captures). These are where a fault would show next.

= What is done, and what is next <sec-next>

_Done (theory1)._ The ledger of all 139 decisions and the eight proofs of `False` (@sec-ledger), the residue and the principles found in it (@sec-residue), audits from the code of principles 4, 3 and 5 with predictions run (@sec-a4, @sec-a3, @sec-a5).

_Done (theory2)._ The paper read whole, `RULES.md`, the nine model notes and docs/18's shape of the argument. The argument from the principles alone (@sec-argument): the statement, the two inductions, and nine cases, riskiest first, each closed from principles cited by name. It found five missing clauses and no case where the design is wrong. The principles revised against it (@sec-principles, @sec-revision): exclusivity split out as principle 12, the first draft's principle 12 merged into 5, principles 3, 4 and 11 narrowed to what consistency uses with the rest marked as type safety's or adequacy's, and clauses added to 1, 7, 9 and 10. Every "what consumes it" now points at cases of the argument; the enforcement of principles 6 to 12 was read against the code at 105021637 (@sec-a6), which found the claim "every private run is one of two combinators" false as stated (six more sites, all restoring through the same two functions) and one sealed value that is not [Close]'s (`hintLater`). One prediction run: census site 7 (closed by D77).

_Next._
- *The frame property*, the step most cases use (cases 1, 3, 4, 5, 7): state it against today's checker over good states (docs/18 says its first statement was false) and prove it; on the heap design it is proved (`notes/frame-model.md`), so the port is the alternative.
- *Principle 12's preservation:* that every step keeps the borrows a forest, lends exactly where its loans sit, and touches no live loan. Swept, not proved; case 1's injectivity and every field write rest on it.
- *Principle 4 for a block's captures:* D90's first obligation (the checker computes them partly from values; the reference reads them from declared types).
- *`hintLater`* (@sec-a6): show it is never stored, or give hints a type distinct from `Value`, so principle 7's "one maker" is structural.
- The audits the first draft left: principle 1's open (B2) condition of D120; principle 2's question for each identification site, whether it is preserved by every refinement; principle 4's tests made only by untyped runs. The first draft's suggestion of a generated differential for principle 4 is withdrawn (the user ruled out generated testing): the answer is its redesign, one evaluator (@sec-a4).
- docs/18's own section on principles (`<sec-principles>` of the plan) still lists the seven of 2 November; once this file is accepted it replaces that section, and the plan's "lemmas each step uses" should cite these twelve.

= The referee's report <sec-referee>

_Written by `referee1`, 27 November 2026, as the adversarial referee of @sec-argument, after reading the paper whole (with its appendix and the fragment proof), `RULES.md` whole, the principles and the argument above closely, and the plan's section on the shape of the argument (the set model, conversion, meaning preservation and the strict reference run). Programs were run with `lake env lean` on the checker of `main` at c830346b6, whose checker sources are those of 105021637; each is self-contained, "with the `Nat` prelude" meaning `uses Nats`. Nothing in the author's sections was changed._

== Verdict

The argument does not show what its summary says it shows. Its cases are, read one at a time, mostly sound reasoning about the design, and the decomposition into nine cases by risk is a useful map; but "the argument closes in every case, citing the principles and nothing else" is true only because four of the twelve principles are not properties of the design that a check enforces: they are the open theorems of the consistency proof itself (the existence of the set model, the soundness of conversion for code, the frame property, and the preservation of the borrow invariants), so what the section proves is a reduction to them, of the same kind as the paper's conditional theorem for the fragment F. Two further faults lie in the induction rather than in any case: the claim it carries is stated pointwise in a future that the end of a borrow changes, and it carries membership as a conclusion of every step of the checker, including the untyped runs, which is the form the mechanisation tried and abandoned on 20 November, here asserted for untyped runs without an argument. Three steps rest on a principle in a form that the author's own audit, or the code, shows false: that nothing but [Close] makes a sealed program; that a run of the body under check before its acceptance can only fail to end, D135 not being on `main`; and that a stuck block's captures are read from the code alone. No program was found that the checker accepts and that proves `False`, and no accepted empty type; every attack on the design itself (a stuck block's returned borrow passed to a lemma that needs writes through it visible, a borrow of a borrow, the universe rules, fuel) was rejected or held. So the result is: the design survives this referee, and the proof does not yet exist; the objections below say where it is missing.

== Objections, most serious first

=== O1. The principles that carry the argument are the proof's open theorems

*Where.* The summary ("proves, case by case ... citing the principles and nothing else. The argument closes in every case"), @sec-arg-statement, and the verdict line of every case.

*Objection.* A principle, by @sec-what, is a sentence about the design that the checker makes true by construction or by checks at enumerable sites. Four of the twelve are not that:
- Principle 1 (_meanings exist_) is the existence of the data model. The plan's own statement of it (`exists_dataModel`) assumes eight named facts, of which one is an unproved fact about the model (a global heading a field's type has a small result at every argument, with a hard case at a domain in a higher universe) and six are read true but not derived from the code. The syntactic conditions principle 1 lists (positivity, nesting, D120, D121, D128, D133, …) are necessary conditions found one at a time by the lanes building the model; that they suffice is the theorem.
- Principle 2 (_identifications hold_) is the soundness of conversion. The plan proves it in Lean only for values that hold no code; for the two function rules it is part of the simulation (the plan's (V4) and (V5)). Case 7 argues it rule by rule, so it is not merely assumed; but its function rules rest on case 4's untyped runs (O3), and principle 2 as written lacks the plan's typing hypothesis (O5).
- Principle 6 (_effects stay local_) is the frame property. The mechanisation found it false as stated four times (item 2 below) and has no current statement; cases 1, 3, 4, 5 and 7 use it.
- Principle 12's clause that every step keeps the borrows a forest with exact lending is the preservation of well-formedness, which the author's audit records as swept on 2,137,352 states and not proved; case 1's injectivity and every field write rest on it.

The author's "Where the argument is weakest" names three of these steps; it does not name principle 1 or principle 2, and the summary and @sec-arg-found still say the argument closes.

*Evidence.* The plan's paragraph on the general proof of the model (eight facts) and its status of conversion (for code, and for the premises of the two function rules: open); item 2 below; the author's own audit row for principle 12. With the `Nat` prelude, the hard case of the model's fact (6) is accepted by the checker:
#measured[
```
def FT (A : Type₁) : Type := Nat
inductive WT (A : Type₁) := MkWT(x : FT(A))
```
Accepted. A data type in `Type₀` whose field's type is a call of a global whose domain is `Type₁`: the case the plan's fact (6) calls hard. The argument's principle 1 says only "its field types read only through what the model can follow".]

*Kind.* The argument is incomplete, and its summary overclaims.

*What would settle it.* Restate the theorem as conditional on principles 1, 2 (for code), 6 and 12's preservation, as the paper's fragment theorem is conditional on naturality and the machine's invariants; mark in @sec-principles which principles are theorems of the proof rather than properties enforced at sites; and correct the summary and @sec-arg-found. Or prove the four.

=== O2. The induction's claim does not survive the end of a borrow

*Where.* @sec-arg-induction: "for every assignment γ of Ω ... and every future φ, (i) the reference run of t from Ω's meaning is defined, returns v's meaning, and leaves Ω'’s meaning”. And case 9: "An end fixes the future at its holder's content ...; it only loses information."

*Objection.* The meaning of a state is defined pointwise, under one assignment γ and one future φ: a loan of ℓ means φ(ℓ). When a step ends ℓ (at every access, drop, join and observation), the loan's place afterwards holds the holder's content, whatever φ(ℓ) was. So for every φ with φ(ℓ) different from that content, Ω''s meaning at φ is not obtained by any run from Ω's meaning at φ, which has forgotten who holds ℓ and what it holds now: claim (i), read with the argument's own definitions, is false at every step that ends a borrow, and the conclusion does not survive the next step. It is repairable only by changing what (i) is about: a reference state that keeps which position holds which label and its current content, as the plan's strict reference run does (meanings as functions of the future, reads taken at the future that gives each live borrow its record, each end tested at every typed future). Case 9's justification of an end, "it only loses information", is true of the plan's meanings as functions of the future (the plan records it proved in Lean), but it is not what (i) asks: the plan used that order first as the relation between the checker's state and the reference's and abandoned it because comparing by the order admitted wrong states, and (i) demands equality; at one fixed φ an end does not lose a meaning, it replaces one. "Good states", quantified over every future of whole members, is consistent with the plan's typed futures, but nothing in the argument says at which future a read is taken; the plan's example `let r = &p; let z = (*r).0; let w = q; (*r).0 := z; w` shows that the obvious choice (each borrow's current content) is not a future of whole members in mid-run.

*Evidence.* The reasoning above; the plan's definition of the strict reference run (where a read is taken) and its note on the abandoned order.

*Kind.* The argument is wrong as stated (a conclusion that does not survive the next step), and repairable.

*What would settle it.* State the inner claim over reference states with labels and records, as in the plan, with reads at the record future; and re-derive case 9's end as an equality of reference states.

=== O3. Membership is carried on the checker's run, and asserted for untyped runs

*Where.* @sec-arg-induction: "(ii) v's meaning is a member of A's"; "An untyped run (a callee's body run in place, a sealed program's re-run, a generic call a comparison makes) satisfies (i) and (iii) for code whose meaning is a member of its type, which the outer hypothesis supplies (@sec-arg-call)”. Case 4, all three bullets.

*Objection.* This is the second form of the plan's route: "a simulation by a reference run that was not strict, carried membership as a second conclusion of every step of the checker". Stating it in Lean showed that no step concluded membership of the value an evaluation returns: a value in flight had no type, the check at a function's return does nothing on a value with no dependent constructor (so `0` passed at `Unit`), and a known callee's body binds positions at types it never checks. The argument returns to that form without addressing any of the three. For untyped runs it asserts (i) and (iii) and gives no induction for them: case 4's bullets say that the callee's meaning is a member, that the run in place is the run in isolation (principle 6), and that it decides as its meaning does (principle 4). None of these gives (iii), that every position an untyped run binds holds a member of its stored type: an untyped run binds a callee's parameters and its `let`s at types it never compares with the values; its temporaries may have no stored type (D104, "none where an untyped run computed none"), and its `let` of a call has a type computed later (D82, D132, D134), about which "good" says nothing. And "decides as its meaning does" is about decisions, not about the values the run computes, which is what (i) needs.

This matters most during the check of a recursive definition, where an untyped run of the body under check computes values that a type then uses. The outer hypothesis gives only that the definition at a smaller size is _a member of its type_; for the checker's type to mean the reference run's, the in-place run must compute the definition's meaning at that size, which is exactly the untyped-run claim. The ruling meant to remove this (D135: while a function is being checked, a call of it closes off at once) is not on `main`.
#measured[
```
def Sel (n : Nat) : Nat by n := match n { Z => Z, S(m) => match m { Z => (let e : Eq(Nat, Sel(m), Z) = refl; Z), S(k) => Z, }, }
```
With the `Nat` prelude: accepted on `main`. While `Sel` is being checked, the type `Eq(Nat, Sel(m), Z)` at `m = Z` is computed by running `Sel`'s own body in place, untyped, to `Z`, and `refl` is accepted against it. The reference run reads the same type as `Eq(Nat, ⟦Sel⟧(0), 0)`, which is `True` only if the untyped run computed the stage. The verdict follows the value that run computes:
```
def Q2 (n : Nat) : Nat by n := match n { Z => Z, S(m) => match m { Z => (let e : Eq(Nat, Q2(m), S(Z)) = refl; Z), S(k) => Z, }, }
def Q3 (n : Nat) : Nat by n := match n { Z => S(Z), S(m) => match m { Z => (let e : Eq(Nat, Q3(m), S(Z)) = refl; Z), S(k) => Z, }, }
```
`Q2` is rejected ("the ascribed term has type ⊤, expected False") and `Q3` accepted; they differ only in what the `Z` arm returns, which only the run of the body under check reads.]

*Kind.* Incomplete (a step asserted, in the form that failed when it was mechanised); covers items 1, 3, 4 and 5 below.

*What would settle it.* Either adopt the plan's split: a strict reference run whose membership is the model's own fundamental lemma, so that the checker owes only that the strict run succeeds; or give the untyped runs their own simulation lemma, proved by induction on the untyped run inside the outer induction, saying what a position bound or held in flight by an untyped run means; and land D135 or prove that the in-place run of the body under check computes the stage below.

=== O4. "What the argument does not use" uses D135's gap

*Where.* Case 4: "before acceptance such a run can only fail to end, which is undecided (principle 5), never an acceptance. D135 is a fault of termination, not of consistency"; repeated in @sec-arg-unused and @sec-arg-found.

*Objection.* As a description of the checker this is false: before acceptance, a run of the body under check can end and decide a type (`Sel` above). The conclusion, that no wrong program is accepted through it, may still hold, but the argument offered for it is that in an accepted definition every run of its own body is at a smaller size, and that reaches consistency only through O3's untyped-run claim for the definition under check, which is what D135 was ruled to make unnecessary. The ruling is described as if in force; it is recorded as "not landed yet" in docs/32, and the checker of `main` still runs the body.

*Kind.* The argument is wrong in a stated fact, and incomplete in the step that matters.

*What would settle it.* Land D135 (and then case 4 needs no claim about the body under check), or prove O3's claim for it.

=== O5. Two clauses the argument relies on are false as written

*Where.* Case 7: "a sealed program has [Close]’s shape (principle 7: nothing else makes one)”. Principle 2: "Wherever the checker identifies two things ..., the two mean the same element under every assignment".

*Objection.* (a) Principle 7's "nothing else makes a sealed program" is false at the code: `hintLater` (`Machine.lean`, line 828) builds a sealed value whose head is no call, `⌈⋄hint P w̄⌉`, the deferred hint of a called body. The author's own audit found it (@sec-a6) and @sec-next lists it as to do, yet case 7's verdict "closes" depends on the clause without mentioning it. Reading the sites where a run hands on or reads a hint (the `.val`, `rewrite`, `hole`, constructor and `split` cases of `evalCore`), each either forces the hint (`forceHint`) before storing it or returning it as a type, or passes it on unread (`split`; `hole` is stuck in an untyped run before it reads one), so I found no route by which it reaches a stored position or a comparison; but nothing structural prevents one. (b) Principle 2 as stated has no hypothesis, and the plan's lemma needs one: both sides well typed inside at one type. The plan's counterexample is a pair of convertible propositions with different meanings, `Eq(Nat, And(True, Nat), Nat)` and `Eq(Nat, Nat, Nat)`; no accepted program forms the first, which is what the hypothesis says. The argument never carries "well typed inside", so it cannot discharge the hypothesis at the sites where it uses principle 2 (cases 1, 3, 5, 7 and the conclusion).

*Kind.* (a) a principle is not enforced (no structural guarantee); (b) a principle is misstated.

*What would settle it.* (a) as @sec-next says: give hints a type distinct from `Value`. (b) add the typing hypothesis to principle 2, and derive it at each use from membership (the plan's lemma that a value whose meaning fits a type is well typed inside at it).

=== O6. The frame property is used five times and never stated

*Where.* Case 1: "Each side's run at the call site is its run at the generic state plugged into the caller: it reaches the caller only through the loans its borrow parameters hold (principle 6)"; case 4's second bullet; cases 3, 5 and 7.

*Objection.* Principle 6 is a sentence ("a running body names and changes only its own frame and what its borrows lend; a call exchanges only what it is passed"), and the steps use it as an equation between two runs, "plugged in". That equation is the frame property, which was false as first written four times when stated in Lean: a dead label read through the renaming of labels; a callee state that is not itself well formed; no cell for a borrow parameter; and the caller's frames compared only by value. The argument does not say which equation it means, so none of the four can be checked against it, and case 1's hypothesis direction (a hypothesis true at the call site is true generically) depends on its exact form: it must relate every owner's context, not values only, which is precisely the fourth failure.

*Kind.* A principle is missing in the form the argument uses (an equation, over good states, with labels).

*What would settle it.* The author's first "next" item: a precise statement over good states, with how labels are renamed and what the isolated run's cells are, checked against the four failures before it is used.

=== O7. Two producers of returned borrows are missing from case 1

*Where.* Case 1: "A context is built only by the steps that place a loan: ... a stuck call returning a borrow (... the callee's backward function, injective by principle 1 for an unknown callee and by the outer hypothesis for a checked one) ...".

*Objection.* Two other things return a borrow whose hole lands in the caller's places: a stuck match whose declared type is a borrow, closed off as a block (its result is lent what the block takes by `&` and what its by-move borrow variables lend), and a local closure returning a borrow. A block is not a definition, so the outer hypothesis does not cover it, and it is not an unknown callee; a closure is checked by its own [Def] inside the current derivation, not by the outer hypothesis. Injectivity of their backward functions is therefore not established by the case as written. The design does observe them: the attack below is rejected because the checker observes both fills.
#measured[
```
def PF (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
def QB (n : Nat) (a : Nat) (b : Nat) : False := (let r : &Nat = match n { Z => &a, S(k) => &b, }; PF(r, refl))
def QB2 (n : Nat) (a : Nat) : False := (let r : &Nat = match n { Z => &a, S(k) => &a, }; PF(r, refl))
```
With the `Nat` prelude: `PF` accepted; `QB` and `QB2` rejected ("argument 2 (e) has type ⊤, expected" a conjunction over the fills of `a` and `b`, resp. of `a`). Had either been accepted, `QB(0, 0, 0)` would be a closed proof of `False`.]

*Kind.* Incomplete.

*What would settle it.* Add the two producers: a block's backward function is injective because each arm's returned borrow derives from its by-`&` captures or its by-move borrow variables, checked at the arm's return; a closure's by the inner claim at its own [Def].

=== O8. Local recursive functions have no induction

*Where.* @sec-arg-induction (the outer induction is on $d_k$'s position and its decreasing argument), case 6: "the stage below is the function itself there, which is membership, and the outer hypothesis covers the call".

*Objection.* A `fix go (…) by y` inside a body is checked by its own [Def] as a node of $d_k$'s derivation, and its recursive calls are on `go`'s own argument, not on $d_k$'s. The outer hypothesis says nothing about `go` at smaller sizes, and the inner induction is on the derivation, in which `go`'s check is one node; membership of `go` needs an induction on `go`'s decreasing argument at that node, which the argument does not set up. Such functions are accepted, proofs among them:
#measured[
```
def AddZ (n : Nat) : Eq(Nat, Add(clone(n), Z), n) := (fix go (y : Nat) : Eq(Nat, Add(clone(y), Z), y) by y := match y { Z => refl, S(p) => go(p), })(n)
```
With the `Nat` prelude: accepted.]

*Kind.* Incomplete (routine to repair).

*What would settle it.* A third induction, on the local function's decreasing argument under the assignments of its generic call, nested at its [Def] node.

=== O9. Principle 4 for a block's captures reads values

*Where.* Case 5: "The block's entry, the places it moves and their grain are read from the code (principle 4)"; the author lists D90's first obligation as open.

*Objection.* At the code, the capture modes are partly a function of values: `blockCaptures` (`Machine.lean`, around line 4188) treats a variable as a borrow variable if its stored type is a borrow type _or its current value is a borrow_ (`b.val.isBorrow`), and the granularity step (around line 4239) splits a capture by the constructor its content holds. Both are consumed by the entry of a match run directly (which accesses the captures, invalidates the dependent fields of those taken by `&`, and lends a borrow-typed result the places taken by `&`), in typed and untyped runs alike. In an untyped run a `let` of a call has its type deferred, so the reading of a borrow variable there is its value. I tried the one shape where that could differ (a let-bound borrow ended before a borrow-typed match, assigned whole in an arm the run does not take), and it did not:
#measured[
```
def Mkb (x : &Nat) : &Nat := x
def F (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Nat := (let y = Mkb(&a); let a2 = a; let k = Z; let r : &Nat = match k { Z => &c, S(j) => (y := &b; &c), }; y := &d; *r := 5; c)
def T : Eq(Nat, F(0, 0, 0, 0), 5) := refl
```
With the `Nat` prelude: both accepted (the typed check and the closed call agree).]

*Kind.* A principle is not enforced by construction; no fault found.

*What would settle it.* Compute modes from declared readings only (the typed run's stored type is the declared reading; an untyped run should consult the same reading, not the value), or prove D90's first obligation.

=== O10. Open and partly moved members are used and not defined

*Where.* @sec-arg-statement: "Good states. ... holds a member of that type, or an open member (a value of a dependent type in the middle of a mutation, or partly moved: principle 9)"; case 2.

*Objection.* The argument defines neither. Principle 9 says a value "may be open ... only while the code that opened it runs", but a partly moved local stays partly moved until its scope ends (a match binds places, so `match xs { Cons(h, t) => t }` leaves `xs` partly moved), and a partly moved value is compared in `Id` and `Eq` (`⊥ = ⊥` is `True`), so its meaning matters beyond the code that moved it. The plan needed three definitions (two refuted in Lean, by a rewritten index and by tuples compared only with tuples) before it reached a structural one, field by field, with completions of the moved earlier fields. Case 2's steps are only as good as the definition they keep.

*Kind.* Unclear (a definition missing).

*What would settle it.* Take the plan's definition of whole, partly moved and open members and check case 2 against it.

== On what the argument says it does not use

Read skeptically, as the brief asked. _Principle 11's adequacy clauses_ (footprint sufficiency, [Id-typestate], [Obs-ref], the order of conjuncts): agreed, not used. The model's `Id` is the equality of the observations at the footprint, so nothing about what a continuation could read enters; and at a call site the sides run in the pushed parameter frame and can name no place of the caller, so [Id-typestate]’s clause against ending an outside borrow protects nothing that consistency needs. _Principle 4's clauses about untyped runs as such_ (only checked code runs, every accepted form runs, the same tests): the second and third are type safety's, agreed; the first is used, through the body under check (O4). _Principle 3's converse_ (W2): agreed, not used; the replacing direction is enforced at every site I read (a declared type of declared sort `Prop` is always a proposition: `Eq`, `Id`, a `Prop` inductive, a `Π` into one, a variable declared `: Prop`, a call whose codomain is written `Prop`). _Hole parametricity_ (case 3): agreed, not needed, since no run meets a live hole (D97); this is one real simplification over the paper's route.

== The fourteen items

#table(columns: (24%, 46%, 30%), align: left, table.header([*Item*], [*Where the argument handles it, and by which principle*], [*Referee's reading*]),
  [1. A value in flight had no type; a function's return check did nothing on some values (`0` at `Unit`).], [Claim (ii) of the inner induction, for typed steps; nothing for untyped steps.], [*Not handled.* The argument carries membership in the form that failed (O3).],
  [2. The frame property, false as stated four times.], [Principle 6, cited in cases 1, 3, 4, 5, 7.], [*Not handled.* No statement given; none of the four failures discussed (O6).],
  [3. A recursive function's body run in place while it is being checked.], [Case 4: "D135 is a fault of termination, not of consistency"; principle 10's order.], [*Not handled.* D135 is not on `main`; `Sel` shows the run's value used in a type; the needed step is O3's (O4).],
  [4. A borrow returned at a result type not written as a borrow type; a binding whose type is computed later.], [Principle 4 ("a function type's class and [Close] row") for the first; nothing for deferred types.], [*First handled:* the surface rejects `&T` anywhere but a written type (`IdT(&Nat)` as an argument: "Nat is not a place"). *Second not handled:* "good" is about positions with a stored type, and says nothing of a deferred one (O3).],
  [5. An untyped run's binding is not tested; an erased call's private copy discards its records.], [Principle 6 for the private copy ("leaves nothing behind but fresh names and facts"); nothing for untyped bindings.], [*Not handled* for bindings (O3). The private copy is handled for consistency; D132 was a type-safety fault.],
  [6. The existence of the data model.], [Principle 1, its list of syntactic conditions (D107, D120, D121, D128, D133).], [*Assumed*, not argued (O1). The higher-universe head is accepted (`WT`); the parameter that varies under nesting, the own name in parameters and nesting across sorts are rejected by D128, D133, D121.],
  [7. A live borrow's future; the end of a borrow as a failure point; members of what, when partly moved or open.], [The meaning of a state under a future; principle 12 (ends over whole contents); principle 9.], [*Partly handled.* Futures are introduced but the claim is pointwise in them (O2); the end as a failure point of the strict run is not discussed; open membership undefined (O10).],
  [8. One holder per label; a place lent twice; a borrow whose content is a borrow.], [Principle 12 ("one holder", "lends exactly the places that hold its loan, fill or mark").], [*Handled in the statement*; its preservation is unproved (O1). `let y = &x` with `x : &Nat` is rejected ("a borrow of a borrow-typed place").],
  [9. A split on a stuck call generalised to an unknown, its record, the same call met again after a refinement.], [Case 3, "Generalising": principles 2 (exact keys, D108), 7, 8.], [*Handled.* Not discussed: a record whose text a later refinement changes no longer matches, so the call is a fresh neutral; sound, incomplete.],
  [10. The join: a place moved in one arm only; re-rooting; an arm never run and never checked.], [Case 5, principle 4 (the join from syntax and declared types).], [*Handled for paths that split.* An arm skipped on a known constructor is not mentioned; it is harmless only because the scrutinee is that constructor at every instance, which the argument should say.],
  [11. Conversion of functions by running at fresh unknowns; `Eq` on values holding code.], [Case 7: observation of the generic call, least relation, injectivity and disjointness.], [*Handled*, modulo O3 (the observation's runs are untyped) and O5.],
  [12. Impredicative `Prop`, large elimination, subsingleton elimination, universe levels.], [Principle 1's list (predicativity of `Type₀`, subsingleton elimination), case 6 (no recursion on a proof).], [*Partly handled.* Where the model needs impredicativity and how a Π-type's sort is computed is not discussed. Probes hold: `Π(A : Type) (a : A). A` declared in `Type` is rejected ("has type Type₁"); a borrow of a proof is rejected (D66).],
  [13. The hint a tail is handed; what an untyped run decides differently.], [Case 4: principle 4, "the hint is a decision" (D124); untyped-only tests marked type safety's.], [*Handled* in principle; the one hint that is a value (`hintLater`) is O5 (a).],
  [14. A decision taken with less fuel than another run had.], [Principle 5: "running out of fuel is undecided".], [*Handled.* The checker's monad puts fuel exhaustion in its own exception, outside the one `catchStuck` catches (`Env.lean`, line 280; `Catch.lean`), and every fuel-bounded reader throws on exhaustion; so a run with less fuel is undecided, never decided differently.],
)

== The cases, restated

#table(columns: (14%, 43%, 43%), align: left, table.header([*Case*], [*What it claims, from what*], [*Referee's reading*]),
  [Statement], [Every accepted definition means a member of its type; a constant of type `False` is impossible.], [Fine as a target; "means" needs the structured reference state (O2).],
  [Induction], [Outer on program order and decreasing size; inner on the typed derivation, with (i) exact meanings, (ii) membership, (iii) goodness; untyped runs get (i), (iii).], [O2 (pointwise in the future), O3 (membership on the checker's run; untyped runs asserted), O8 (local recursion).],
  [1 `Id`, [Call-type]], [Computing `Id` is exact; a statement transfers between the generic call and a call site in both directions by joint injectivity of contexts.], [The strongest case; rests on O6 and principle 12's preservation; missing producers (O7). The attack `QB` is rejected.],
  [2 Dependent fields], [Invalidation, typing by position, strong updates and [Repack] keep open membership; writes find their paths at every future.], [Rests on an undefined open membership (O10) and an unproved measurement (no live loan on a written path).],
  [3 Closing off], [A sealed program rebuilds the call; re-runs compute the text's meaning; generalisation is a path condition.], [Sound reasoning; "the re-run computes the text's meaning" is O3's claim for untyped runs.],
  [4 Calls in place], [The callee's meaning is a member; the run in place is the isolated run; it decides as its meaning.], [O3 and O4; principle 6's equation (O6).],
  [5 Split and join], [Each assignment takes one arm; the block means the arm; the state after the block is the arm's.], [Sound given principle 4 for captures (O9) and principle 6.],
  [6 Recursion], [[Rec] at the generic call gives descent at every instance; the stage below is the function.], [Sound for top-level definitions; local recursive functions need their own induction (O8).],
  [7 Conversion], [Each conversion rule is an equality of meanings.], [Needs the typing hypothesis (O5 (b)) and one maker of sealed programs (O5 (a)); the function rules rest on O3.],
  [8 Erasure], [Erased terms leave nothing; `⋆` only at propositions.], [Sound; the converse (W2) is indeed not used.],
  [9 Leaf rules], [Accesses end what is touched; reads, writes and drops keep meanings.], [The end step is argued by the abandoned order (O2).],
)

== For a second referee

The objections above are on the argument's structure and on three principles' enforcement; the design itself held against every program tried. What was not done: the frame property's four failures were not each turned into a program against this argument's use of principle 6 (O6); principle 12's preservation was not attacked beyond the borrow-of-a-borrow probe; the dependent-field case (2) was read but not attacked with programs; and O9's value-dependent captures were tried in one shape only (the granularity split by a content's constructor was not tried). Also tried and held, with the `Nat` prelude and `PF` of O7: the hypothesis direction of case 1 through a returned borrow of a stuck call, a reborrow of it, and a reborrow that outlives its holder's re-pointing, `PF(TailM(x), refl)`, `(let r = TailM(&n); PF(r, refl))`, `(let r = TailM(&n); let s = &*r; PF(s, refl))` and `(let r = TailM(&n); let s = &*r; r := &a; PF(s, refl))`, are all rejected (the fill over the hole is observed); and a recursive call at the same argument inside a type in the body, `def Q (n : Nat) : Nat by n := (let e : Eq(Nat, Q(clone(n)), Q(clone(n))) = refl; Z)`, is rejected by [Rec]. The probes are in this report; the runner is `lake env lean --load-dynlib=.lake/build/lib/libochr_Ochr.so` from `ochr/core/lean`.
