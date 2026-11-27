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

Each principle in turn: what in the consistency argument consumes it, how the checker enforces it today, an audit of the sites where it could fail, and the redesign that would make it hold by construction. The audits of principles 4, 3 and 5 were done from the code (`ochr/core/lean/Ochr/Machine.lean`, `Env.lean`, `Decide.lean`, `Runtime.lean` at 105021637) and their predictions run; the others are shorter and say what was not audited. The status tags are #s-cons, #s-check, #s-not, and #s-open for a site this pass did not read.

== Principle 4: one code, two runs <sec-a4>

*What consumes it.* The meaning-preservation theorem relates the checker's _typed_ run of a definition (at its generic call, the unknowns standing for anything) to the model, and supplies every other run of the same code from that one: an untyped run of a body at a call, a sealed program's re-run, a direct arm on a known constructor, the runtime. The supply is the callee's membership (its meaning is a member of its function type) carried through the frame property, so it exists only for code whose typed check has finished, and it says something about the untyped run only if that run is the same computation as the checked one. "The same" means: the same decisions at corresponding points (D90's alignment property is the borrow part of it), and differences only in the values the unknowns stand for. The historical counterexamples are of two shapes. A wrong acceptance where the two paths decided differently, such as `Same` (D83, D84): at an unknown `n` a block took `x` by move because one arm moved it, at `n = 1` the arm that ran left it, so two observations were equal at the generic run and different at the instance. And an accepted function that cannot be called (D119, D125, D129, D131, D132), with the smallest of them:
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

*What consumes it.* The strict reference run decides erasure, copy and move, and a function's class from the same readings the checker uses (it must, by principle 4), but the model gives each value a meaning by its _type_: a member of a proposition is a proof, irrelevant and without effect; a member of a sort is a type. The two agree only if every reading agrees with the type it reads. Where they disagree the run the model follows is not one the model can give a meaning to: an effect it does not erase, a proof it moves, a value it reads at the wrong type. Counterexamples: D54's `RunGGen(H)` (a closed `False`: a function read as a proof-class function writes), D55's two notions of proposition (closed proofs of `False`), D110's `BoomF` (`⋆` read as data of a field's declared type: a closed `False`), and D131's `V1`, re-run today:
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

*What consumes it.* The invariant every step of the simulation carries is a predicate on the checker's state: every position holds a member of its type (D104 made the temporaries positions), every live borrow is held once and lends exactly its places (the spine's (WF1), (WF2)), and nothing else in the state changes what the next step does. A value held only in a variable of the checker's Lean code is outside the predicate: a refinement or an [End] that maps over Ω does not reach it (it goes stale), and a borrow it holds has no holder (D115's 662,366 states with a loan of an ended borrow). A fact kept in the state that is not about the program is outside the predicate too: a cache (D95) or a one-shot flag left set (D130) makes the next step depend on something the invariant does not say. Counterexample with a closed `False`: D110's `ViaLoan`, a borrow stored inside a value, where no holder is looked for, and read back as data.

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
