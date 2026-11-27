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
#align(center, text(size: 9pt, fill: muted-ink)[Draft by the agent `theory1`, 27 November 2026 · to replace the section "The principles the checker enforces" of docs/18])
#v(0.6em)

#align(center, box(width: 92%, align(left)[
  *Summary.* The checker has accepted closed proofs of `False` eight times since October, and about 135 decisions record a rule added or tightened after a counterexample. Each fix was local. This document states the reasons the design is correct as twelve principles, each one sentence about the design, and checks them against the history: every decision and every known proof of `False` is classified by the principle it restores (@sec-ledger). Seven principles were written on 2 November in docs/18 and three are standards of `ochr/core/CLAUDE.md`; they explain about half the history. The rest falls into five ideas nobody had written down, which became principles 1 to 5 here: _meanings exist_ (every accepted declaration denotes a set), _identifications hold_ (every equation the checker makes holds at every instance), _readings are true_ (what the checker reads from syntax about a term agrees with its type and its value), _one code, two runs_ (a definition is checked once and then run untyped, and the untyped run must run only checked code and make every decision its check made), and _the state is the whole truth_ (every value the checker holds is in its state at a type, every borrow there has one holder, and nothing else is). The orchestrator's hypothesis about last week's faults is confirmed for D124, D125, D131, D134 and D135, and needs two amendments: D133 belongs to _meanings exist_, and D130 and D132 to _the state is the whole truth_. For each principle, @sec-audits says what in the consistency argument consumes it, how the checker enforces it, an audit of the sites where it could fail, and the redesign that would make it hold by construction.
]))
#v(0.4em)
#outline(depth: 2, indent: auto)
#pagebreak()

= What a principle is <sec-what>

A _principle_ here is one sentence about the design, not about a line of code, with three properties. The consistency argument uses it at a point that can be named: types mean sets, `False` means the empty set, and every accepted definition must mean a member of its type; a principle is what one step of that argument needs. If it failed, some wrong program would be accepted, or some step of the argument would break, and we can say which. And the checker makes it true either _by construction_, for a structural reason it cannot be violated (the module that makes decisions does not import the machine, so no decision can read a run), or _by checks_ at a list of sites that can be enumerated. A site where a principle could fail and nothing makes it hold is _not enforced_; the audits (@sec-audits) look for these by reading the code, predict the fault each would allow, and run the smallest program that should show it.

Every program in this document is self-contained and was run with `lake env lean` on the checker of `main` at 105021637 (the same checker as the proof line's base, `ochre-checker10-base`); its verdict is the one measured. "With the `Nat` prelude" means the block `uses Nats` (`Ochr/Examples/Nat.lean`).

= The principles <sec-principles>

Twelve principles. The first five are new: each names a class of decisions that fit nothing written before (@sec-residue). The next six are docs/18's seven of 2 November, regrouped: _locality_ absorbs the erasure half of "erasure and captures", and the capture half goes to _closing off_, since a block is a call of its captures. The last joins the two standards of `ochr/core/CLAUDE.md` about failure and totality. The third standard, "decisions never read a run", is the by-construction half of principle 4. Each principle is stated once here; @sec-audits gives each its consumer, its enforcement, its audit and its redesign.

#principle[Meanings exist][Every declaration the checker accepts denotes: an inductive type is a set built from earlier declarations and itself at positive, nestable positions of its own sort, every universe is predicative but `Prop`, and every function's type is a set of functions.]
The set model is the ground the whole argument stands on: before anything can be said about a definition, its type must mean a set and `False` the empty set. A declaration with no model (a type that is its own negation, as in Curry's paradox) makes every later statement meaningless, and the checker then accepts a closed proof of `False` by ordinary typing alone, with nothing wrong in any run. The model is built declaration by declaration, so what it needs from the checker is a syntactic condition on each declaration: strict positivity (D36), the nesting condition with its greatest set of nestable parameters (D64, D107), no value of the type read off a field's spine (D120), one sort per knot (D121), a type parameter written as a sort (D128), the declaration's own name only in its fields (D133), predicativity of `Type₀` (D48, D66), subsingleton elimination out of `Prop` (D45), and constructor parameters inferred only where the model can follow (D105).

#principle[Identifications hold][Wherever the checker identifies two things (two types or values by conversion, an `Eq` computed to `True` or `False`, a `J` that computes, a record looked up by its key), the two denote the same element under every assignment of the unknowns, not only under the ones the generic run happens to see.]
Conversion is how a checked term moves from one type to another, so an identification that fails at some instance transports a member of one set into another. The history's faults here are of two kinds: an identification that holds at the generic run and fails at an instance (closures compared by result only, D30; a borrow result observed without writing through it, D38; two values that had each lost a moved part, `Same`, D83 and D84), and an identification that breaks typing in open contexts (equality reflection by `J` under a false hypothesis, D56; an unreachable arm yielding a value at the wrong type, D58). Keys need exact equality, not conversion's (D108).

#principle[Readings are true][Whatever the checker reads about a term or a binding without running it (a proof, a type or data; erased or not; a copy or not; a borrow or not; its sort; a function type's class and [Close] row; the type of a value it finds in a field) agrees with what the term's type and value are, and every reader of one fact gives the same answer.]
Most decisions are made from _readings_: facts read off syntax and declared types (D28, D35, D55, D77, D80). Principle 4 makes the readings the same on every run; this principle makes them right. A reading that is the same on every run but wrong (a proof read as data, a function in `Type₁` read as in `Type₀`) still breaks the argument, because the operations that look at values (a read never moves `⋆`) and the decisions that look at readings (the join moves what reads as data) then disagree, and the run the model follows is neither. The history: two notions of proposition (D54, D55), a Π-type's sort read as `Type₀` (D86), copy-ness against erasure (D100), `clone` missing from a classification table (D116), two tests for "is a type" (D128), a sort hidden behind a call (D131); and, for readings off values, a field typed by a content that does not say its type (D110, D112 and its amendment).

#principle[One code, two runs][A definition is checked once, by a typed run at unknowns, and afterwards its code is run untyped, in place or sealed; an untyped run runs only code whose typed check has finished and accepted it, can run every form that check accepts, and makes at every point the decision the check made there: the same erasure, class and copy, the same moves and borrow ends, the same hint, the same test.]
The model gives a definition one meaning, a function, and the argument proves the typed check's run computes it. Every other run of the same code (a call's run of the body, a sealed program's re-run, a direct arm on a known constructor, the runtime) is then justified only by being the same computation: the argument supplies the untyped run's correctness from the callee's membership, which the typed check established, through the frame property. If a decision differs (a borrow ends in one run and not the other, a place is moved in one, a hint is read in one), the untyped run is a different computation and nothing supplies it; if the code was never checked (a body still under check, an arm no run took), there is no membership to supply. The history's _two paths_ (the generic call against an instance, paper §6.3) are the oldest instance (D28 to D40, D54, D84, D90); last week's faults are the typed-against-untyped instance (D124, D125, D134, D135).

#principle[The state is the whole truth][Every value the checker holds while anything runs is in its state, at a stored type (bindings, temporaries, arguments in flight, results on their way out), every borrow there has exactly one holder and its loans sit exactly where it lends, and nothing else is in the state: no cache, flag or record outlives the evaluation it was made for.]
The argument's invariant is a predicate on the checker's state: every position holds a member of its type, every borrow is held once and lends exactly its places. A value held in a variable of the checker's Lean code while other code runs is invisible to that invariant (a borrow with no holder, D115), and a fact kept in the state that is not about the program (a cache, D95; a one-shot flag left set, D130; a record a private copy throws away, D132) makes the next step's behaviour depend on something the invariant does not describe. Exclusivity of borrows (D19, D92, D106, D111, D117) is the borrow half of the same principle.

#principle[Effects stay local][A running body names and changes only its own frame and what its borrows lend; a call exchanges only what it is passed; and a run the checker makes privately (a statement, a type, a proof, a comparison, its own scaffolding) leaves nothing behind but fresh names and facts that mean the same in every state.]
This is docs/18's locality (L1 to L7) and the erasure half of its "erasure and captures" (E1, E3 to E5). The frame property (a callee's meaning, read off a run of its body in a fresh frame, is the body's run in place) rests on it, and so does the erasure lemma (running a proof and skipping it agree). Faults: a Π-type reading its free variables at the call site (D13), proofs writing outer places (D14, D20), a record kept from a private copy naming the wrong program (D37) or an unknown of an empty type (D103).

#principle[Closing off rebuilds the call][A call stuck on an unknown, and a stuck match or `J` as a call of its captures, is replaced by sealed programs that rebuild the call exactly from what it was passed; each is re-run exactly when an input it embeds changes, everywhere it occurs, never re-closes its own head, and is never run while it holds a borrow's hole.]
This is docs/18's closing off (C1 to C9) with the capture rules (K1, K3): a block takes, as a function takes its arguments, everything any arm uses, at least as strongly as any arm uses it. Faults: re-closing the head (D9, D39), a write to a scrutinee unseen by the captures (D32), a hole lost by a generalisation (D29), a hole read by a nested run (D97).

#principle[Worlds are exclusive][A fact established while checking one arm of a split, and depending on the arm's constructor, is visible in that arm and its sub-worlds only, and entering an arm substitutes its refinement into every position of the state.]
docs/18's worlds (X1 to X4). Faults: an η-refinement kept after its arm (EtaBoom, D79); generalisation records rewound with a copy (D37).

#principle[Whole where relied on][A value may be open (break its type's telescope, or hold a moved part) only while the code that opened it runs; wherever it passes to code that relies on its type it is whole, and whatever produces an unknown of a dependent type has checked whole the value it stands for.]
docs/18's wholeness (W1, W2); W3 moves to principle 3, since it is about reading a type off a value. Faults: an index field lent past a whole-again point (D73), a stuck block's or `J`'s arm not checked at its end (D72, D75), a proof field assigned while its index is lent (D64 amended), a borrow with a moved-out content handed on (D127).

#principle[Recursion descends][A recursive call is recognised by the name the function binds for itself and is checked to be on a strict part of the entry value as refined so far.]
docs/18's recursion, without R3 ("check before running"), which is principle 4. Faults: a non-structural argument (D17), recursive calls missed after a split rewrote a captured function value (CapSplit, D78).

#principle[Observation sees every effect][`Id` compares two computations by every result and every final content a continuation could read, on independent copies, at every owner of every place either side writes, and only between sides that leave the same moves and borrows.]
docs/18's observation (O1 to O5). Faults: one owner observed of several (D18), a write through a pattern variable unseen (D32), where a returned or re-pointed borrow points (D38, D113).

#principle[Undecided decides nothing][Every function the checker runs is total, running out of fuel or depth is the answer "undecided", and no failure is ever turned into a value.]
The standards "no catch-and-default" and "all checker code is total" of `ochr/core/CLAUDE.md`. The consistency theorem is a statement about the checker's code, so the code must be total for the statement to be provable, and a verdict must not depend on the fuel: a caught failure with a default can turn "something is wrong" into acceptance.

= The ledger <sec-ledger>

Every entry of `ochr/core/DECISIONS.md` (D1 to D134, with its amendments), the ruling D135 recorded in docs/32, and the eight accepted proofs of `False`, each in one row: the decision in words with its number after, what went wrong (or, for a design choice that fixed no fault, what it decides), the principle of @sec-principles it restores or establishes, and the principle written before 27 November that it fits, if any: docs/18's seven (locality, closing off, worlds, wholeness, erasure and captures, recursion, observation) or `CLAUDE.md`'s three standards (no catch-and-default, total code, decisions never read a run). "Design" marks a founding choice of the calculus and "feature" a decision that adds to the language without repairing anything; neither restores a principle, and neither is counted in the residue. Where a row has two principles, the first is the one the fix restores.

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
  [Access ends loans on the path and in the content; `Id`'s sides on independent copies (D19)], [A dangling borrow; the exclusivity the frame property needs was implicit.], [5, 11], [locality, observation],
  [Proofs have no effect outside themselves (D20)], [A `Prop`-typed block wrote when sealed and not when run directly: `Id Nat (S Z) Z`.], [6], [erasure],
  [[Call-type] after the arguments; arguments in temporaries (D21)], [Effect goals were all `⊤`; arguments in flight were invisible to [Access].], [5], [none],
  [Blocks capture like closures; generalise then split (D22)], [Blocks hid their arms' moves and writes.], [7], [closing off],
  [`J` has explicit endpoints; recursion names its parameter (D23)], [`Eq A a a ≡ ⊤` erased endpoints; several shrinking arguments.], [2, 10], [recursion],
  [Every type is formed on a private copy (D24)], [A type formed elsewhere ran effectfully in the real environment.], [6], [erasure],
  [The pure theorem by the in-place lemma (D25)], [Usage, not a fault.], [feature], [—],
  [Erased terms run on a private copy; a neutral head closes off at once; Π-types capture no borrow (D26)], [D20's static check replaced by one principle.], [6, 7], [erasure, closing off],
  [Proof parameters are `⋆` (D27)], [Sealed programs embedding different proofs failed to compare (incompleteness).], [2], [erasure],
  [Erasure decided per declaration, never from a normal form; universes not cumulative (D28)], [`U(n)` computing to `Prop` at `Z` only: erased at one path, run at the other; `Lie(Z) : Eq Nat Z (S Z)`.], [4], [decisions never read a run],
  [Matching ends loans inside a neutral head; normalisation errors are type errors (D29)], [A hole inside a sealed head was generalised away; an accepted program wrote through an ended borrow.], [7, 12], [closing off, no catch],
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
  [D65 amended: a value in flight's borrow is not ended (D65)], [`Blk` returned a borrow of its own local through a block; its closed run read `⊥`.], [5, 4], [none],
  [`Prop : Type₁`; `&A` iff `A : Type₀` (D66)], [Predicativity of `Type₀` for borrows of functions and type parameters.], [1], [none],
  [`Eq`'s sides on a private copy, effects discarded (D63 item 6 reversed)], [Confinement rejected the in-place sort inside a statement.], [6], [erasure],
  [Dependent fields with open and repack; the nesting condition (D64)], [The unconditional rule had a closed `False` (`NBox`).], [9, 1], [wholeness],
  [Overwriting a borrow does not end the reborrows behind it (D67)], [Precision ("move the cursor down"); the generic run still ends at least what an instance ends.], [6], [locality],
  [Using a variable consumes it, in statements too (D68)], [Five more disagreements between abstract and ground runs once statements moved: copy-ness from values, nested erased terms not private, a closure in an arm capturing only when run, η named afresh in each copy.], [6, 4, 7], [erasure, closing off],
  [Confinement deleted (D69)], [Simplification: private copies made it redundant.], [6], [erasure],
  [A proof field assigned while its index is lent (D64 amended)], [`LieLent`: the proof was checked at the borrow's current content, the borrow then wrote another: a closed `False`.], [9], [wholeness],
  [Switches and the counterfactual ledger removed (D70)], [Process: the theorem is about the checker at its defaults.], [12], [total code],
)

== Fording to the frozen readings: D71 to D96

#L(
  [Fording: value parameters, equation fields, non-uniform recursion (D71)], [Feature; its attack pass found a parameter of borrow type recorded in a type.], [1, 5], [none],
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
  [A private copy takes a borrow argument from its holder (D92)], [One borrow held twice inside a copy.], [5], [none],
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
  [No access ends a borrow a value in flight holds (D106)], [`TK`: the join's access ended the result's borrow; rejected only by an unrelated later rule.], [5], [none],
  [A strong update stores only first-order data (D110)], [`BoomF`: `⋆` stored in a data field, read at its declared type: a closed `False`; `Leak`: a borrow stored inside a value.], [3, 5], [wholeness (W3)],
  [A comparison keeps nothing but names (D103)], [A comparison's copy left a record naming an unknown of an empty type.], [6], [erasure],
  [Nesting covers the type being declared; a greatest set (D107)], [`Q(Q(A, n), 1)`: Curry's paradox, a closed `False`; a second hole (`PositivitySwap`); readers of a constructor-less entry.], [1], [none],
  [A leaf dependent field is a proof field (D112)], [The model cannot read a number's or a function's type off its content; [Entry] invalidated on one path only.], [3, 4], [wholeness (W3)],
  [D112 amended: typing reads through a mark], [`A2`: a lent field's mark had no readable type and fell back to the declared type: a closed `False`.], [3], [wholeness (W3)],
  [A generalisation record is looked up exactly (D108)], [Lookup by conversion's equality ignores recorded parameters.], [2], [closing off],
  [A loop bounded by fuel (D109)], [A `while`, opaque to the kernel.], [12], [total code],
  [A borrow is never left without its end (D111)], [An overwrite ended no borrow below a root; a lender kept a loan for ever.], [5], [none],
  [`Id` observes what a re-pointed borrow points to (D113)], [`Hide`: a write through a re-pointed borrow went unobserved.], [11], [observation],
  [A side of `Id` may end a borrow it consumes, on every path (D114)], [A theorem accepted and a closed instance rejected: the check asked who held the borrow, which differs by path.], [4], [none],
  [A call's arguments stay in Ω until its frame binds them (D115)], [In a window no position held a borrow argument: 662,366 states with a loan of an ended borrow.], [5], [none],
  [`clone` of a proof is that proof (D116)], [The after-run classification table had no row for `clone`.], [3], [none],
  [A tail split ends with the join (D119)], [Three paths of a tail match left different places moved.], [4], [none],
  [A declaration names only declared things, checked before running (D118)], [An undeclared name in an arm no run takes was accepted, the live twin rejected.], [4], [none],
  [A variable mentions what its type mentions (D120)], [`D2Node(x : D2, p : Pt(D2, x))`: the model cannot build it; Lean rejects it.], [1], [none],
  [A nested occurrence passes only through its own sort (D121)], [`D := MkD(q : Q(PP(D)))`: no model for `Prop`-sorted knots.], [1], [none],
  [The field-type frame binds what a loan stands for (D117)], [A loan held twice; reading a field's type ended a borrow.], [5], [none],
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
  [An unchecked write into a dependent field (D110)], [A field typed by a content (`⋆`) that does not say its type; a borrow stored in data.], [3 and 5],
  [A dependent field lent to a call's returned borrow (D112 amended)], [A mark with no readable type, given the declared type.], [3 readings],
)

== The residue, and the principles missing from it <sec-residue>

Of the 139 rows, 10 are design choices or features. Of the other 129, 67 fit a principle written before (docs/18's seven or the three standards) and 62 fit none. The 62 are not scattered: each falls into one of five groups (10 rows in the first, 10 in the second, 7 in the third, 23 in the fourth, 12 in the fifth, counting each row by its first principle; several rows have a second), and each group has one idea nobody wrote down. The idea is the missing principle.

+ *Declarations that have no model* (D36, D44's leak, D45, D48 (1), D64's nesting, D66, D71's borrow parameter, D105, D107, D120, D121, D128, D133). docs/18's seven are about runs; none says anything about a declaration, and the model needs each declaration to denote before any run means anything. Three of these were accepted proofs of `False` or Hurkens-style paradoxes (D36, D48, D107). This is principle 1.
+ *Identifications that fail at some instance* (D6, D16, D30, D47, D48 (3), D50, D52, D56, D58, D59, D83, and D84's `⊥`). The written principles constrain runs; this group constrains what the checker _equates_: conversion, `Eq`'s computation, `J`'s computation. Principle 2.
+ *Readings that are the same everywhere but wrong* (D48 (2), D54, D55, D86, D100, D116, D128, D131, and D51's captured readings; D110 and D112, filed by docs/18 under wholeness's W3, are the same idea applied to a type read off a value). The standard "decisions never read a run" makes a decision the same on every run; nothing written required it to be _true_. Principle 3.
+ *A run of checked code that is not the checked computation* (D12's design, D33, D62, D65, D84's amendment, D87, D88, D89, D90, D91, D93, D94, D99, D101, D114, D118, D119, D122, D124 (three entries), D125, D126, D129, D134, and D135, which docs/18 names as R3, "check before running", with no explanation). Principle 4.
+ *Values outside the state, and state that is not the program's* (D21, D51, D65 amended, D82, D92, D104, D106, D111, D115, D117, D130, D132, and D71's borrow in a type). Principle 5.

*The hypothesis, tested.* The orchestrator's hypothesis was that last week's faults (D124, D125, D130 to D135) fit none of the seven and share two unstated ideas: (i) one code, two runs, and (ii) readings are sound. The ledger confirms it with two amendments.
- D124, D125, D134 and D135 are (i): a run handed a hint its check did not, a form the check accepts that no run can run, a test made on one path of one operation and not the other, and a body run before its check finished. D131 is (ii).
- D133 is neither: it is a declaration with no model, the first group. Its sibling D118, the check that names are declared, is (i): acceptance depended on which arms a run reaches.
- D130 and D132 are not (i) or (ii) as stated, but a fifth idea, the state is the whole truth. D130 is a fact about one evaluation kept in the persistent state (a flag set for "the next call", read by whichever call came next); D132 is a result passed back through the state, which a private copy then threw away. Both were found by the proof because its invariant is a predicate on the state, and both are the mirror image of D104 and D115 (values the checker held outside the state). D132 is also (i), since its symptom was an accepted function its call could not run.
- (i) is older than last week. D12 ("checking `f` is running `f`'s generic call") is its root, D33 (2026-09) its first instance, and every two-paths fault of the generic call against an instance (D28 to D40, D54, D84, D90) is the same idea with "the typed check at unknowns" for one run and "an instance" for the other. What changed last week is that the proof began to state the untyped run's step, which exposed the typed-against-untyped half that the generic-against-instance half had hidden.

*Where the seven were right.* The seven explain most faults found before they were written (2 November). Of the faults since, the seven explain six: `EtaBoom` (D79, worlds, which a referee found in the worlds principle itself), a sealed program run over a hole (D97, closing off), a comparison's leftover record (D103, locality), two of observation (D113, D114's first half) and two of wholeness (D98, D127). Every other fault since 2 November, the November proofs of `False` included, is in one of the five groups above: what one expects of a list that was complete for what it named and silent about the rest.

= The principles audited <sec-audits>

_Stage 2, in progress._ Each principle in turn: what in the consistency argument consumes it, how the checker enforces it today, an audit of every site in the code where it could fail, and the redesign that would make it hold by construction. Principles whose audit is not written yet say so.

= What is done, and what is next <sec-next>

_Done:_ the ledger (@sec-ledger) and the list of principles (@sec-principles).
_Next:_ the audits (@sec-audits), starting with principles 4 and 3, then 5, 1 and 2; then the argument from the principles alone.
