// A plan for proving Ochr consistent and type safe. Standalone: compile with
//   typst compile ochr/docs/18-consistency-proof-plan.typ
// The notation macros below are copied from the paper's style file
// (ochr/core/paper/style.typ) and its appendix, because Typst does not let a
// document import files outside its own directory. Only the few used here are copied.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#set document(title: [A plan for proving Ochr consistent and type safe])


#let dark-mode = false
// Colours, named by role, for light and dark pages. Status fills are pastel in both modes,
// so the text on them is always dark.
#let ink = if dark-mode { white } else { black }
#let muted-ink = if dark-mode { luma(170) } else { luma(80) }
#let code-bg = if dark-mode { rgb("#2a2a2e") } else { luma(246) }
#let oq-fill = if dark-mode { rgb("#2e2c1b") } else { rgb("#fbfbe9") }
#let oq-rule = rgb("#b8a200")
#let expl-fill = if dark-mode { rgb("#1d2733") } else { rgb("#eef3f8") }
#let expl-rule = if dark-mode { rgb("#7fa3cc") } else { rgb("#5b7fa6") }
#let status-ink = black
#let rem-fill = if dark-mode { rgb("#262a24") } else { rgb("#f2f5ef") }
#let rem-rule = if dark-mode { rgb("#8fb07a") } else { rgb("#6f8f5a") }
#set text(font: "New Computer Modern", size: 10pt, fill: ink)
#set page(
  paper: "us-letter",
  margin: (x: 2.2cm, y: 2.4cm),
  fill: if dark-mode { rgb("#1e1e21") } else { white },
  numbering: "1",
)
#set par(justify: true, leading: 0.62em, spacing: 0.9em)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => {
  v(0.8em)
  it
  v(0.3em)
}
#show raw: set text(font: "DejaVu Sans Mono", size: 8.6pt)
#show raw.where(block: true): it => block(width: 100%, inset: (x: 8pt, y: 6pt), fill: code-bg, radius: 2pt, it)


// Notation (copied from the paper).
#let kw(s) = math.bold(math.upright(s))
#let ty(s) = math.sans(s)
#let seal(t) = $lr(⌈ #t ⌉)$
// The observation of t, optionally at footprint w from state s: its result and the final
// contents of the places in w. Written Obs, since ⟦·⟧ is the denotation (deno below).
#let obs(t, w: none, s: none) = $attach(upright("Obs"), tr: #w, br: #s) lr(( #t ))$
#let cfg(o, t) = $chevron.l #o, #t chevron.r$
#let ev = math.scripts(sym.arrow.b.double)
#let res = $rho$
#let ok(x) = $tack.double #x$
// The meaning of x in the set model; under an assignment `at` of the unknowns when given.
#let deno(x, at: none) = if at == none { $lr(⟦ #x ⟧)$ } else { $lr(⟦ #x ⟧)_(#at)$ }
// "Less informative than": the information order on meanings of states.
#let lessinfo = $subset.sq.eq$
// The reference run of t: the meaning of running t, a state transformer on meanings.
#let refrun(t) = $upright("Run") lr(( #t ))$

// Numbered statements, one counter, as in the paper.
#let thm(kind, name, body) = figure(kind: "plan-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "plan-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
// The headline targets, lettered on a counter of their own: Target A, B, C.
#let target(name, body) = figure(kind: "plan-target", supplement: [Target], numbering: "A", caption: name, body)
#show figure.where(kind: "plan-target"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let proof(body) = block(width: 100%, above: 0.6em, below: 0.9em, [_Proof sketch._ #body #h(1fr) $square$])

// Status tags.
#let tagc(c, s) = box(inset: (x: 3pt, y: 1.5pt), radius: 2pt, fill: c, text(
  size: 7.5pt,
  weight: "bold",
  fill: status-ink,
  s,
))
#let s-heap = tagc(rgb("#cfe0f5"), [proved on the heap slice])
#let s-red(x) = tagc(rgb("#fbe5c0"), [reduced to #x])
#let s-paper = tagc(rgb("#e6dcf2"), [paper argument])
#let s-open = tagc(rgb("#f6cfcf"), [open])
#let s-design = tagc(rgb("#f2f2c4"), [open design question])

// Status colours, for figures and legends.
#let st-heap = rgb("#cfe0f5")
#let st-red = rgb("#fbe5c0")
#let st-paper = rgb("#e6dcf2")
#let st-open = rgb("#f6cfcf")
#let st-design = rgb("#f2f2c4")
// A legend swatch for a status colour.
#let swatch(fill, label) = box(fill: fill, inset: 2pt, text(fill: status-ink, label))
#let dn(pos, label, fill, name) = node(
  pos,
  text(size: 7.5pt, fill: status-ink, label),
  fill: fill,
  stroke: 0.5pt,
  corner-radius: 2pt,
  inset: 4pt,
  name: name,
)

// Open design questions, numbered.
#let oq(n, title, body) = block(
  width: 100%,
  inset: 7pt,
  stroke: (left: 2pt + oq-rule),
  fill: oq-fill,
  above: 0.8em,
  below: 0.8em,
)[*Open design question Q#n (#title).* #body]

// Quick explainers: standard background a reader may not have, set apart from the argument.
// Nothing in the argument depends on a box; a reader who knows the concept can skip it.
#let explainer(title, body) = block(
  width: 100%,
  inset: 7pt,
  stroke: (left: 2pt + expl-rule),
  fill: expl-fill,
  above: 0.8em,
  below: 0.8em,
  breakable: true,
)[#set text(size: 9pt); *Quick explainer: #title.* #body]

// Reminders: notation introduced earlier in this document, restated briefly where it is
// next used heavily, with a reference to where it was defined.
// Why: an intuition note inside an argument, like a comment in code. The formal text does
// the work; a why-note says what a step means and why it is there.
#let why(body) = block(above: 0.8em, below: 1em, inset: (left: 0.8em), text(
  size: 9pt,
  fill: muted-ink,
  style: "italic",
)[Why: #body])

#let reminder(body) = block(
  width: 100%,
  inset: 7pt,
  stroke: (left: 2pt + rem-rule),
  fill: rem-fill,
  above: 0.8em,
  below: 0.8em,
  breakable: true,
)[#set text(size: 9pt); *Reminder.* #body]

#align(center, text(size: 16pt, weight: "bold")[A plan for proving Ochr consistent and type safe])
#align(center, text(size: 11pt)[The route to be followed, the lemmas it needs, and where it could fail])
#v(0.3em)
#align(center, text(
  size: 9pt,
  fill: muted-ink,
)[Draft for discussion · revised 6 November 2026, route changed (first draft 2 November) · a plan for a proof, not a proof])
#v(0.6em)

#align(center, box(width: 90%, align(left)[
  *Summary.* The claim this plan serves is that a language like Ochr makes a good general-purpose language. That needs two guarantees, _consistency_, so that its proofs can be trusted, and _type safety_, so that accepted programs never crash or go wrong when run, and Ochr promises a third, _`Id` adequacy_: programs it proves equal can be swapped in any context. The plan proves the first two by _meaning preservation_, and the third from the same meanings with a context lemma. Types are given meanings in a set model, in which `False` denotes the empty set. Every state the checker reaches while checking a definition is given a meaning too, as a function of what its unknowns stand for: an _assignment_ gives each unknown any element of its type's meaning, non-computable functions included. The central theorem has three parts, proved together by one ordinary induction: each step of the checker keeps the meaning of its state under every assignment, or loses only information; every value the checker stores lies in the meaning of its type, whatever the borrows still live may later write; and the state stays well formed. An accepted definition therefore means an element of its type, and a closed proof of `False` would be an element of the empty set. This route replaces the one the first draft followed, which compared the checker's run on unknowns with a second run at each concrete instance; three referees showed that route could not be completed as written (@sec-referees), and it is preserved on a branch (@sec-old). All four planned paper tests have passed (@sec-tests): the set model exists on a slice chosen to contain everything that made its definition doubtful; states with live borrows have a meaning, as functions of their borrows' final contents, and the step lemmas hold on a higher-order slice, much of both checked in Lean; each of the four closed proofs of `False` the checker once accepted and has since fixed is a step at which one of the theorem's three parts fails; and an audit of every decision the checker makes left one item to settle. The one failure found is a fifth closed proof of `False`, conversion identifying two values that hold a moved-out place, which fails the monotonicity the theorem requires of computing steps; it is fixed on main by D83. Type safety reuses the same meanings: a closed run of an accepted function means what the reference run of its call says, and that reference run never goes wrong; what remains is to show that the machine goes wrong only where the reference run does, a runtime rule for `J`, erasure and termination (@sec-safety). The rest is a short list of residual lemmas (@sec-order).
]))
#v(0.4em)

#outline(depth: 2, indent: auto)
#pagebreak()

= What this document is <sec-intro>

This is the plan we intend to follow to prove that Ochr is consistent and type safe, and that programs it proves equal can be swapped: the shape of the argument, the definitions it needs, the lemmas it reduces to, which of those are already proved and where, and where the plan could fail. It is written as a section of theory work would be, so the statements are precise where they can be, and where they cannot be yet, that is said.

*The object of study.* The calculus is the one implemented by the Lean checker in `ochr/core/lean/Ochr/` (chiefly `Syntax.lean`, `Basic.lean`, `Env.lean`, `Machine.lean`, `Decide.lean`, `Obs.lean`, `Check.lean` and `Run.lean`) and laid out rule by rule in the appendix of the Ochr paper. @sec-prelim restates every part of it that the plan relies on, so that the plan can be followed without either.

*Status labels.* Each lemma carries one of four labels.
- #s-heap: proved, without `sorry`, in Lean for the _heap slice_, a second evaluator for part of the calculus built in the style of a heap-based design that the first draft proposed porting the checker to. The port is abandoned (@sec-order); the slice's proved results are kept as history where they are cited. Not a statement about the checker.
- #s-red[X]: shown to follow from the named lemmas X by an argument given here.
- #s-paper: an argument exists at the level of detail of this document, not checked in Lean.
- #s-open: no argument yet.
Design questions that must be decided before an argument can be written are marked #s-design.

*Route.* The plan follows _meaning preservation_. Every type, value and checker state is given a mathematical meaning (a _denotational model_), and each step the checker takes is shown to keep the meaning of its state. Truth is defined in the model, so a step that keeps meaning cannot lead the checker from true premises to a false conclusion. This is the usual soundness argument for _symbolic execution_ (@sec-route), with set-theoretic meanings in place of concrete machine states. The first draft of this plan followed an _operational simulation_ route instead: show that every step of the checker's run on unknowns is matched by the concrete machine at every instance. Three referees found that it could not be completed as written, and the present route was agreed as its replacement on 6 November 2026, by the plan's author and a second session that proposed it. The superseded route is preserved on a branch, and @sec-old says why it was superseded. A third route, translating each accepted program into Lean and having Lean's kernel check it, gives consistency one program at a time; it is not part of this plan, though its results are used in @sec-risks as evidence.

= The calculus, as far as the plan needs it <sec-prelim>

== Terms, values and neutrals

Terms and types share one grammar: variables, the universes `Prop` and $ty("Type")_i$, n-ary Π-types, recursive functions $kw("fix") f (overline(x) : overline(A)) : B kw("by") x_j := t$ (a `fix` without `by` is a λ), saturated calls, inductive types $ty("D")(overline(a))$ and constructors $ty("C")(overline(t))$, the primitive equality $ty("Eq") A space t space u$, transport $ty("J")(A, a, b, P, h, t)$ and $kw("rewrite") h kw("in") t$, borrow types $\&A$, places $p ::= x | *p | p.g$, borrowing $\&p$, assignment $p := t$, `let`, sequencing $t; u$, $kw("match") p space {ty("C")_1 (overline(y)_1) => t_1, dots}$ with any number of arms, $kw("split") f kw("in") t$, and $ty("Id") A space t space u$, the equality of two computations.

Every type of data and every connective is an inductive declaration $kw("inductive") ty("D") (overline(x) : overline(X)) : s := ty("C")_1 (overline(g)_1 : overline(B)_1) | dots$ with $s in {ty("Prop"), ty("Type")_0}$. The library declares `Nat`, `Unit`, `Pair`, `False` (no constructors), `True` (one constructor `I`, written `refl`) and `And`. A field's type may mention the type being declared, other declared types, parameters, earlier fields of the same constructor (the fields form a _telescope_), calls of earlier _type functions_ (definitions whose codomain is a sort), and equations between _first-order data_ (types built from inductive types and parameters, with no Π, no `&` and no sort); never `Π` or `&`. Parameters whose declared type is syntactically a sort are _type parameters_; the others are _value parameters_, and a recursive occurrence of $ty("D")$ in a field may take any arguments at them (_non-uniform_ occurrences). A family indexed by values is written by fixing the index with an equation field (_Fording_): `Vec(A, n) := VNil(h : Eq(Nat, n, Z)) | VCons(m : Nat, x : A, xs : Vec(A, m), h : Eq(Nat, n, S(m)))`.

$\&A$ requires $A : ty("Type")_0$, and `&` occurs only as the whole declared type of a parameter, result or annotated term: never inside another type and never as the result of computing a type. So there are no borrows inside data and no borrows of borrows. Universes are not cumulative, and `Prop : Type₁` beside `Type₀ : Type₁`.

*Values* are constructor values $ty("C")(overline(a); overline(v))$ (recording the inductive's parameters $overline(a)$), the proof value `⋆`, top-level function names, closures $chevron.l overline(kappa) tack.r kw("fix") dots chevron.r$ (code with captured values $overline(kappa)$), Π-closures $chevron.l overline(kappa) tack.r Pi(overline(x) : overline(A)). B chevron.r$ (types are values), type values, borrows $"borrow"_ell v$, loans $"loan"_ell$, the moved-out marker `⊥`, and _neutrals_. A neutral is an _abstract value_ σ (an unknown of a known type Δ(σ), introduced only by the checker) or a _sealed program_ #seal[$t$] (a program with no free variables whose run is stuck). A value is _borrow-free_ if it contains no borrow and no live loan. A value is _closed_ if it contains no free variables, no abstract values, no loans and no `⊥`: nothing whose meaning depends on an environment, on what the unknowns stand for, or on contents held elsewhere in the state. A closed value therefore means the same thing wherever it appears, which is what lets the model give it a meaning $deno(v)$ on its own (@sec-model). A sealed program has no free variables but is stuck on some abstract value, so it is not closed; nor is anything containing one.

== States, borrows and resolution <sec-states>

An environment Ω is a stack of frames, each binding variables (with declared types) to values, plus temporaries. A _state_ adds Δ (the types of abstract values), ρ (the refinements and generalisation records made so far), the goal while a definition is checked, and the recursion stack. $"content"_Omega (p)$ follows a place through variables, borrows ($*p$ looks inside $"borrow"_ell v$ at $v$) and fields.

*Borrows.* $\&p$ moves the content $v$ of $p$ into $"borrow"_ell v$ and leaves $"loan"_ell$ at $p$. _Ending_ the borrow ([End]) replaces it by `⊥` and substitutes its content for every occurrence of $"loan"_ell$: a loan is a variable bound by its borrow. Every access to a place is preceded by [Access], which ends every borrow whose loan lies on the path to the place or inside its content (for a match, which inspects only the head: on the path, at the head, or anywhere inside a neutral head). Reading non-copy data moves it out, leaving `⊥`; data of a _copy type_ (`Unit`, sorts, propositions, inductives declared `copy`, and non-recursive inductives whose fields are copy types) is copied, copy-ness being read from the place's declared type, in which a type parameter is never a copy type; and $kw("clone")(p)$ copies explicitly. The machine's rules for these steps are [Borrow], [Read] (moving data out), [Move] (moving a borrow), [Copy], [Clone] and [Assign]; [Ctor] builds a constructor value. A borrow must be whole (no `⊥` inside) when it ends, is returned, or is passed to a call that closes off.

*Dropping.* When an owned value dies holding a live loan, [Drop] ends the borrower if the borrower is held in a binding, and fails if the borrower is a value in flight (a temporary such as a result being returned). So a local may die while a variable that borrowed it is never used again, but nothing may return a borrow of its own local.

*Owners and resolution.* $"owners"_Omega (ell)$ follows each occurrence of $"loan"_ell$ outward: through the content of an enclosing $"borrow"_m$ to $"owners"_Omega (m)$, otherwise to the owned position holding it. The _resolution_ $res(Omega)$ ends every borrow; $res_Omega (w)$ is $w$ with each live loan replaced by the resolved content of its borrow.

*Well-formedness.* A state is well formed when (WF1) each label has at most one borrow, which is the whole value of a binding or temporary, never inside data, a sealed program, a closure or a type; (WF2) every loan's borrow is in Ω, except a loan inside a sealed program whose borrow is outside the run (an _inert_ loan); outside sealed programs a label occurs as a loan at most once, inside them any number of times; (WF3) the relation "a loan of ℓ occurs in the content of borrow m" is acyclic; (WF4) closures and Π-closures capture no borrow and no `⊥`, and sealed programs are closed; (WF5) at every call point each argument is loan-free or is $"borrow"_ell u$ with $u$ loan-free; (WF6) each binding's value is `⊥`, or a loan whose borrow's content has the binding's type, or a value of the binding's type, and every σ has a type in Δ.

== The machine, closing off and sealed programs <sec-machine>

The machine is big-step and deterministic: $cfg(Omega, t) ev cfg(Omega', v)$, or the run is _stuck_ (it must inspect a neutral), or it fails. Calls evaluate their arguments left to right into temporaries, push a frame binding the parameters, run the body, and pop the frame, dropping its bindings. Types and proofs are _erased_: an erased term runs on a private copy of the state, which is discarded (@sec-erasure).

*Closing off* ([Close]). When a call $f(overline(w))$ is stuck, the call itself returns. Let the borrow arguments be $w_i = "borrow"_(ell_i) u_i$ ($i in I$) with each $u_i$ loan-free, let $L$ be $"let" c_i = u_i$ for $i in I$, and $C$ the call $f(overline(a))$ with $a_i = \&c_i$ for $i in I$ and $a_i = w_i$ otherwise. If $f$'s declared codomain is borrow-free, the call returns #seal[$L; C$] and each $"loan"_(ell_i)$ is filled with #seal[$L; C; c_i$]. If it is $\&T$, the call returns $"borrow"_k seal(L"; let" r = C"; " *r)$ for a fresh $k$, and each $"loan"_(ell_i)$ is filled with #seal[$L; "let" r = C; *r := "loan"_k; c_i$]: the fills have a _hole_ $"loan"_k$ for the final content the caller will write through the returned borrow, which the caller's eventual [End] of $"borrow"_k$ supplies by substitution. A result whose declared type at the call reads as `Unit` is `()`, and so is the fill of a lent place whose declared type is `Unit`. A call whose head is a neutral is stuck at once and closed off the same way.

*Sealed programs.* Values are kept in normal form. A sealed program's normal form is its run from the empty environment, except that its head call $C$ may not itself close off ([Seal]'s head guard); so a sealed program either runs to a value or stays exactly as it is. A loan whose borrow lives outside the run is inert: the run treats it like an abstract value.

*Stuck blocks.* A stuck `match` that is not the body of a call is closed off as a call of an anonymous function of the places it uses. Pattern variables are first resolved to the places they denote; the block takes each maximal place by move if some arm moves it, by borrow if some arm writes or borrows it, and by copy otherwise. A stuck `J` is closed off the same way, with its transported term as the block's one arm.

== Observation, footprints, `Id` and `Eq` <sec-obs>

The _footprint_ $W_Omega (t, u)$ is the set of owners of the roots of the places that $t$ or $u$ borrows or assigns, and of the borrow variables they read whole, in a canonical order read off the syntax. A place that is only read contributes nothing. The owner of a variable holding a borrow is the owners of its loan; of an owned variable, the variable itself.

The _observation_ $obs(t, w: W, s: Omega)$ runs $t$ on a private copy of Ω, ends every remaining borrow, and returns the tuple of the result and the contents of the positions of $W$. A borrow-typed result is observed after writing a given fresh $sigma_w$ through it, so that its owners show where it points ([Obs-borrow]); only conversion observes such results.

$ty("Id")(A, t, u)$ computes, at Ω, to $"and"("eq"(A, r, r'), "eq"(T_1, w_1, w'_1), dots)$, where $obs(t, w: W, s: Omega) = (r, overline(w))$, $obs(u, w: W, s: Omega) = (r', overline(w'))$ and $W = W_Omega (t, u)$; $A$ must be borrow-free. `Eq` computes through the smart constructor `eq`: on two values of one constructor it is the conjunction of the fields' equations (injectivity; for a _dependent_ constructor, one some of whose fields' types mention earlier _index_ fields, only when the index fields are convertible), on values of different constructors of one inductive it is `False` (disjointness), on convertible values (equal by definitional equality, @sec-conv) it is `True`, and otherwise, or whenever `⊥` occurs in a side, it is the stuck type $ty("Eq") T space v space w$. `and` drops `True` conjuncts. $ty("J")(A, a, b, P, h, t)$ computes to $t$ only when $a equiv b$; otherwise it is stuck and closed off.

== Erasure and private copies <sec-erasure>

A term's _declared type_ is read from the declared types of its heads without normalising (a variable's declared type, a call's callee codomain term, a constructor's inductive, an annotation, a tail's or arms'). A term's _declared sort_ is the sort of its declared type, read the same way. A term is _erased_ when it is a proof (its declared type has declared sort `Prop`) or forms a type (a type former, a call of a function returning a sort, or anything in a _type position_: an annotation, a Π domain or codomain, a type slot of `Eq`, `Id` or `J`, or a parameter or field type). An erased term is a _statement_. A run is in _erased mode_ while it runs a statement, and in _runtime mode_ while it runs code. A Π-type's _class_ (returns types, returns proofs, other) and whether it returns a borrow are read from its codomain term when it is formed, and Π-types that differ in either are not convertible. _Sorts are syntactic_: whatever is written in a type position must have a declared type that is syntactically a sort, so a type's declared sort is its computed sort. Every erased term runs on its own private copy of the state, which is discarded. In the checker these decisions are functions of syntax, declarations and declared types only, collected in one module (`Decide.lean`) that cannot run the machine.

== Typing <sec-typing>

The typing judgement $Omega tack.r t ev v : A tack.l Omega'$ is the machine run with types: each rule performs the machine's step and computes a type. Where the machine would be stuck on the program being checked, typing splits instead. The rules the plan relies on:

- *[Call-type].* The type of a call is its callee's codomain evaluated, on a private copy, with the parameters bound to the arguments' values; each argument's type must convert to the corresponding parameter type, evaluated the same way.
- *[T-Call].* The call's type is its [Call-type]; then the callee runs in the machine, where a stuck body closes off. For a proof-typed call ([T-Call-proof]) the body is never run.
- *[Rec].* In the body of $kw("fix") f dots kw("by") x_j$, $f$ occurs only as the head of a call (also inside nested functions and block arms), and every call of $f$, recognised by the name $f$ binds for itself or a nested function's capture of that name, passes in position $j$ a strict subterm (through any field, and through the borrow for $\&ty("D")$) of the _entry value_ of $x_j$ (its value when the call started), as refined so far.
- *[Split].* A match on a place whose content is an abstract value σ checks each arm $i$ under the refinement $sigma := ty("C")_i (overline(sigma)_i)$ with fresh field values typed by the constructor's telescope; the refinement is applied to the environment, every stored type, Δ and the goal, with sealed programs re-normalised. Then the match is closed off as a stuck block, and checking continues once from the unrefined state.
- *[Split-gen].* A match on a sealed program $n$ first _generalises_ it: replace $n$ everywhere by a fresh σ of the place's type, record $n := sigma$ (so a later derivation of $n$ normalises to σ), then split σ. $kw("split") f kw("in") t$ does the same for the first stuck call of $f$ in the goal.
- *Worlds.* Each arm of a split is checked in its own _world_. Leaving an arm discards everything it established except fresh-name counters and the types of abstract values it created. A generalisation record, and an _η-refinement_ (refining σ to $ty("C")(overline(sigma))$ because σ's type has only the one constructor $ty("C")$), lives until the arm that made it ends: the constructor follows from the type alone, but the fields' types are the arm's.
- *[Def].* A definition is checked at its _generic call_: each borrow parameter is bound to $"borrow"_(ell_i) sigma_i$ with a fresh owned cell $c_i |-> "loan"_(ell_i)$ in a bottom frame, each proof parameter to `⋆`, each other parameter to a fresh $sigma_i$. The goal $G$ is the [Call-type] of that call. The body is checked in _tail position_ (where only trailing drops follow: the body itself, and the tails of `let`s, sequences and arms in tail position), producing a finite _case tree_ whose leaves $(Omega', v, A)$ are the states, values and types at the end of each path; on every leaf the frame's pop must succeed and $A equiv G'$, the goal refined along that path. The tail rules are [Tail-let] and [Tail-seq] (run a `let` or sequence, then continue), [Tail-match] (a match on a known constructor), [Tail-split] (a split on an abstract value, one subtree per arm), [Tail-gen] (generalise a sealed program, then split), [Tail-prop] (a match on a proof, one subtree per arm) and [Tail-end] (a leaf). Constants are checked from the empty state ([Const]); inductive declarations by [Ind-decl], which checks the conditions of @sec-model-conditions.
- *Matches on proofs.* A match whose arms name constructors of an inductive in `Prop` is decided by the scrutinee's type, never its content (`⋆`). It may produce data or a type only if the inductive is a _subsingleton_ (no constructors, or one whose fields are all proofs). `match h {}` on $h : ty("False")$ is ex falso; in tail position it contributes no leaves.

#explainer[large elimination and subsingletons][_Eliminating_ a value means taking it apart with a match. Matching on data is unrestricted. Matching on a proof to produce data or a type is called _large elimination_, and it needs care, because proofs are erased and every two proofs of one proposition count as equal (_proof irrelevance_). If the result could depend on which constructor the proof used, two "equal" proofs would give different results. For example, if $ty("Or")(P, Q)$ could be matched to produce a `Bool`, the proofs $ty("Inl")(t)$ and $ty("Inr")(t)$ of `Or(True, True)` are equal yet would give `true` and `false`, so `true = false`. Large elimination is therefore allowed only from a _subsingleton_, a proposition with at most one possible proof: no constructors (`False`, where there is nothing to match) or one constructor whose fields are all proofs (`True`, `And`, an equation). Lean has the same rule.]

*Dependent fields.* A field whose type mentions earlier fields makes its constructor _dependent_; the earlier fields it mentions are _index fields_. Writing, borrowing or moving a field of a dependent value _opens_ it ([Open]): while open, a data field is typed by its content, assigning it is a strong update, and a write or borrow through an index field sets the proof fields whose type mentions it to `⊥` (an error to read until reassigned). A value must be _whole_ again (every dependent constructor inside it at its telescope type, no `⊥` inside) wherever it passes to code that relies on its type ([Repack]); a part still lent at that point is checked as an unknown of its borrow's type, since the borrow may still write anything of that type there. Where a checked body returns, its result and every place it holds by borrow must be whole ([Return]); [Def] and closures check this at their body's return, and a stuck block at the end of each arm (it is an anonymous function, so its arms are its bodies).

== Conversion <sec-conv>

Conversion $v equiv w$ is the _least_ relation closed under: [Conv-refl] identity up to bound-variable names; [Conv-cong] same outermost former with pairwise convertible components (a constructor value's recorded parameters ignored; sealed programs compared by their program text); [Conv-unit] $ty("And")(ty("True"), P) equiv P equiv ty("And")(P, ty("True"))$; [Conv-pi] two Π-closures with the same class and borrow flag whose parameter types and codomains, evaluated at the generic arguments of the first, are pairwise convertible; [Conv-fun] two function values whose Π-types are convertible, whose captured values are pairwise convertible, and whose generic calls have convertible observations (with one shared $sigma_w$ for a borrow result). There is no η-rule; values are `()` wherever their declared type reads as `Unit`, and every proof is `⋆`.

== Refinements and the two paths <sec-two-paths>

#thm([Definition], [refinement], [
  A _refinement_ α assigns values to abstract values, $sigma |-> v$. It _respects_ a state Ω when each σ it refines is an abstract value of Ω and $alpha(sigma)$ is borrow-free and has a type convertible with Δ(σ). It is applied to a state, value or term by substituting and then restoring normal form: every sealed program that changed is re-run ([Seal]) and every `Eq` type rebuilt by `eq`. We write $Omega alpha$, $v alpha$, $t alpha$; α _covers_ Ω when it assigns a value to every abstract value of Ω. More generally, $Omega[w slash a]^+$ replaces every occurrence of an abstract value, loan or sealed program $a$ by $w$ in the values of Ω, its stored types, Δ and the goal, and then restores normal form; $"nf"(v)$ is the normal form of $v$.
]) <def-refinement>

Refinements cover the three ways the checker instantiates an unknown: a case split ($sigma := ty("C")(overline(sigma)')$), a call site (a parameter's generic σ instantiated with the argument), and an abstract function instantiated with a closure. Borrow-freeness costs nothing: a borrow parameter's generic value is $"borrow"_ell sigma$ with σ borrow-free, and since `&` is never produced by computation and never an argument, no unknown type is ever refined to a borrow type.

*The two paths.* Every statement is evaluated along two paths: at a definition's generic call, where calls and matches on abstract values close off, and directly at each instance, where they run. [Call-type] and [Split] identify the results, so a proof checked on the first path is used on the second. If the paths take any decision differently, and the decision changes a result, a statement proved on one path can be false on the other: a closed proof of `False`. The design principle is that _no decision that changes a result is read from a normal form_. The present route needs less: a decision may read anything, provided its outcomes mean the same, are chosen by syntax the model reads the same way, or are ordered by information (@sec-wf).

The superseded route compared the first path with runs at _ground instances_, refinements whose values contain no unknowns. The present route reads states under _assignments_ instead (@def-assign), which give each unknown a mathematical element of its type's meaning rather than a machine value.

= The target <sec-target>

#thm([Definition], [accepted program], [
  A _program_ is a finite list of inductive declarations and definitions, read in order. It is _accepted_ when each item is accepted by [Ind-decl], [Def] or [Const] against the signature of the items before it, the library's declarations (`Pair`, `False`, `True`, `And`, with `Nat` and `Unit` built in) coming first. It is _hole-free_ when no term in it is a hole (`?`, also written `sorry`). Every definition has a body, so holes are the only axioms.
]) <def-accepted>

#target([consistency of the calculus], [
  Assume ZFC with one inaccessible cardinal per universe level used (both defined in @sec-sets). For every accepted, hole-free program, no definition without parameters has a type that evaluates to `False`. Equivalently, no closed term has type `False`, nor any type, such as `Eq(Nat, Z, S(Z))`, that computes to it.
]) <target>

#target([type safety], [
  For every accepted, hole-free program, and every _closed run_ of an accepted data function (a definition whose codomain is data or a borrow type, called with every parameter a concrete value and every proof parameter's type true), the run of the _erased_ program, with proofs and types removed, terminates without error; any borrow it returns is live; and its result, with the final contents of its borrowed places, means what the reference run of the call says (@def-refrun).
]) <target-safe>

#target([`Id` adequacy], [
  If an accepted, hole-free lemma proves $ty("Id")(A, t, u)$, then at every instance where its hypotheses hold, $t$ and $u$ are _contextually equivalent_: at every accepted program position holding $t$, replacing $t$ by $u$ gives a run with the same result, the same final state and the same errors.
]) <target-adeq>

*Why three.* The plan serves the claim that a language like Ochr makes a good general-purpose language. Its proofs must be trustworthy, which is @target, and its programs must not crash or go wrong when run, which is @target-safe: what any verified language owes its users. @target-adeq is Ochr's distinctive promise: programs proved equal can be swapped, the substitution principle behind D84 (drop at the join). Neither of the first two implies it (@sec-adeq). The statement of @target-adeq is a draft, to be sharpened, and no Lean statement of @target-safe or @target-adeq is fixed yet.

*Termination.* Ochr stays total for now: every recursion passes [Rec], so type safety includes termination. General recursion is desirable, but is deferred until a pure, consistent and sound core exists.

The Lean statement of @target against the checker is `Ochr.Consistency.consistency`:
```
theorem consistency (q : Program) (fuel : Nat)
    (holes : NoHoles q) (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst
```
`Prelude.decls` is the library's declarations. `Accepted p fuel` says that the checker's entry point `checkProgram` gives every declaration of `p` the verdict _accepted_ at that fuel (not _rejected_, and not _undecided_, which is what running out of fuel or a depth limit gives). `IsFalseConst` says a declaration is a definition with no parameters whose declared type is the identifier `False`.

*How the two statements relate.*
- *Rules and checker.* @target is about the rules; the Lean statement is about the checker that implements them. Every step of this plan is phrased so that it can be stated against the checker's functions, so a completed plan would prove both, the Lean form being the stronger since it also excludes implementation errors.
- *A literal `False` loses nothing.* If an accepted program had a parameterless $c$ whose type merely computes to an empty type, one more fresh declaration turns it into a literal one: `def B : False := c` when the type computes to `False`; a one-arm match for `False ∧ ⊤`; an annotated zero-arm match for a user's empty inductive. The Lean statement quantifies over all programs, so it covers these.
- *Fuel.* Exhaustion is an outcome of its own that no rule below the verdict catches, and a caught failure cannot refund fuel, so a decided verdict is the same at every larger fuel. The Lean statement quantifies over every fuel and does not need this fact, but a proof may use it to fix a fuel large enough for a given run.
- *Totality.* Every function the checker runs is total, with explicit fuel where recursion is not structural, so the kernel can unfold every step. The one exception, an opaque address used to key the editor's location table, is never consulted when locations are off, which `Accepted` ensures.
- *Universes.* Lean's strength is ZFC with $n$ inaccessibles for every $n < omega$. If the set model for Ochr needs one inaccessible per level at once, the uniform Lean statement is unprovable in Lean (Gödel's second incompleteness theorem: a theory cannot prove the consistency of one at least as strong, @sec-sets), and must be weakened to bounded universe levels, made relative to an assumed model, or stated per program (@sec-oq, Q8).

#explainer[Lean's kernel and its axioms][Lean's _kernel_ is the small trusted core that checks every proof; tactics and the elaborator only produce proof terms for it to check, so a Lean theorem is believed exactly as far as the kernel is. Beyond its core type theory, Lean has three standard axioms: `propext` (two propositions that imply each other are equal), `Quot.sound` (elements related by a relation are equal in its quotient) and `Classical.choice` (from a proof that something exists, pick one). All three hold in Lean's set model. `#print axioms t` lists the axioms a theorem $t$ depends on; an unfinished proof shows up there as `sorryAx`. A `partial def` is opaque to the kernel: it can run, but a proof cannot unfold it, which is why a provable statement about the checker needs every function the checker runs to be total.]

= The shape of the argument <sec-shape>

The argument has three parts: a set model that says what "true" means (@sec-model); a meaning for every state the checker reaches, with a theorem that the checker's steps keep it (@sec-route); and consistency as a corollary (@cor-cons-route). Type safety follows from the same theorem and four further lemmas (@sec-safety), and `Id` adequacy from it and a context lemma (@sec-adeq). The model and the soundness of conversion (@sec-conv-sound) are shared with the superseded route; the second part replaces its soundness theorem and its walk.

== The set model <sec-model>

=== Background: sets, universes and models <sec-sets>

This subsection defines everything the model uses. It follows the standard set model of Lean (Carneiro, _The Type Theory of Lean_, a copy of which is at `docs/papers/theory-of-lean.pdf`), but nothing below depends on having read it. For readers who want the full construction for Lean, of which @sec-model is an adaptation, the relevant parts are, optionally: §1.2 (why sets model a type theory, the two-element `Prop`, and why inaccessible cardinals are needed); §6.2 (the interpretation map, with universes $U_(n+1) = V_(kappa_n)$ and the clauses for Π, ∀ and `=`); §6.2.1 (the least-fixed-point construction of inductive types in ZFC); and §6.3, Theorem 6.7 (the soundness of the model: types denote sets, proofs denote •, convertible terms denote the same thing).

*ZFC, and consistency relative to it.* ZFC is Zermelo–Fraenkel set theory with the axiom of choice, the usual foundation of mathematics. A theory T is _consistent_ if it does not prove a contradiction. By Gödel's second incompleteness theorem, a consistent theory cannot prove its own consistency, nor that of a theory at least as strong; so a consistency proof for a strong type theory is always _relative_: "if ZFC plus some axioms is consistent, so is the type theory".

#explainer[countable and uncountable sizes][Two sets have the _same size_ if there is a bijection between them (a pairing that matches every element of one with exactly one element of the other); $|A|$ is the size of $A$, and $|A| <= |B|$ means $A$ can be matched one-to-one into part of $B$. A set is _countable_ if it is finite or has the same size as the natural numbers $NN$, that is, its elements can be listed $a_0, a_1, a_2, dots$; the integers, the rationals and the set of all finite strings are countable. A set is _uncountable_ if it is not. Cantor's theorem says that no set $A$ has the same size as $cal(P)(A)$, the set of all its subsets: $cal(P)(A)$ is always strictly bigger. So $cal(P)(NN)$, equivalently the real numbers or the set of all functions $NN -> NN$, is uncountable, and the sizes go on growing forever: $NN$, $cal(P)(NN)$, $cal(P)(cal(P)(NN))$, …]

#explainer[cardinals][A _cardinal_ is a size. The size of $NN$ is written $aleph_0$ ("aleph-nought"), the smallest infinite cardinal; the cardinals bigger than it are the _uncountable_ cardinals. If $lambda = |A|$, then $2^lambda$ is the size of $cal(P)(A)$ (a subset of $A$ is a choice of in or out for each element, hence the notation); by Cantor, $2^lambda > lambda$ always. Cardinals are ordered by $<=$ above, and "fewer than $kappa$ sets" means a collection of them whose size is less than $kappa$.]

#explainer[ordinals][Ordinals extend counting past the natural numbers. They measure _position_ in a sequence, not size: $0, 1, 2, dots, omega, omega + 1, omega + 2, dots, omega dot 2, dots$, where ω is the first position after every natural number. Every ordinal other than 0 is either a _successor_, which has an immediate predecessor ($3 = 2 + 1$; $omega + 1$ comes straight after ω), or a _limit_, which has none and is reached only as the limit of all smaller ordinals (ω, $omega dot 2$, …). Different ordinals can have the same size: ω, $omega + 1$ and $omega dot 2$ are different positions but all countable. Each cardinal is identified with the first ordinal of that size, so $aleph_0$ is ω, and every infinite cardinal is a limit ordinal, though most limit ordinals are not cardinals. This identification is what lets a cardinal $kappa$ index a stage $V_kappa$ below.]

#thm([Definition], [cumulative hierarchy], [
  $V_0 = emptyset$; $V_(alpha + 1) = cal(P)(V_alpha)$, the set of all subsets of $V_alpha$; and $V_lambda = union.big_(alpha < lambda) V_alpha$ for a limit ordinal λ. Every set belongs to some $V_alpha$.
]) <def-V>

#thm([Definition], [inaccessible cardinal], [
  An uncountable cardinal $kappa$ is _inaccessible_ if it is _regular_ (a union of fewer than $kappa$ sets, each of size less than $kappa$, has size less than $kappa$) and a _strong limit_ ($2^lambda < kappa$ whenever $lambda < kappa$).
]) <def-inacc>

The two conditions say that $kappa$ cannot be reached from below by the two ways of making sets bigger: taking a union of fewer than $kappa$ smaller sets, and taking all subsets of a smaller set. $aleph_0$ satisfies both (a finite union of finite sets is finite, and a finite set has finitely many subsets), which is why the definition asks for an uncountable $kappa$: an inaccessible is to the uncountable cardinals below it what $aleph_0$ is to the finite numbers.

If $kappa$ is inaccessible, $V_kappa$ is closed under every construction a type theory needs: for $A in V_kappa$ and a family $B(x) in V_kappa$ indexed by $x in A$, the set of subsets of $A$, the _dependent sum_ $Sigma(x in A) B(x)$ (the set of pairs $(x, y)$ with $x in A$ and $y in B(x)$; when $A$ is a set of tags this is a _disjoint union_, written $union.big.plus_(x in A) B(x)$) and the _dependent product_ $product_(x in A) B(x)$ (defined below) are again in $V_kappa$. So $V_kappa$ can serve as "the type of all small types". ZFC cannot prove that an inaccessible exists (with one, $V_kappa$ would be a model of ZFC, proving ZFC consistent), so the existence of inaccessibles is the extra axiom the target assumes.

*Notation.* Throughout, $deno(T)$ is the set a type $T$ is interpreted as, and $deno(v)$ the element a value $v$ is interpreted as.

*Universes.* Fix inaccessibles $kappa_0 < kappa_1 < dots$, one for each universe level used. $ty("Type")_i$ is interpreted as $V_(kappa_i)$: a type in $ty("Type")_i$ is a set in $V_(kappa_i)$. Since $V_(kappa_i) in V_(kappa_(i+1))$, the rule $ty("Type")_i : ty("Type")_(i+1)$ holds in the model.

*Propositions, proofs and proof irrelevance.* Fix an object •, "the proof". A proposition is interpreted as $emptyset$ (false) or ${bullet}$ (true), so `Prop` is interpreted as the two-element set ${emptyset, {bullet}}$, and every proof is interpreted as •. Any two proofs of one proposition therefore have the same meaning; this _proof irrelevance_ is what makes it sound for the calculus to represent every proof by the single value `⋆`. A _subsingleton_ is a set with at most one element; every proposition denotes one.

*Dependent products.* A function type $Pi(x : A). B$ whose codomain is data or a type is interpreted as the dependent product $product_(x in deno(A)) deno(B)(x)$: the set of functions $f$ with domain $deno(A)$ such that $f(x) in deno(B)(x)$ for every $x$.

*Products of propositions, and impredicativity.* When $B$ is a proposition the product cannot be used as it stands, because it is not a truth value, but it is always one step away from one. Each $deno(B)(x)$ is $emptyset$ or ${bullet}$, so there are two cases. If $deno(B)(x_0) = emptyset$ for some $x_0$, no function can choose a value at $x_0$, and the product is $emptyset$. If $deno(B)(x) = {bullet}$ for every $x$, each $f(x)$ is forced to be $bullet$, so exactly one function qualifies, the constant function $x |-> bullet$ (when $deno(A)$ is empty, it is the empty function), and the product is ${x |-> bullet}$. So the product always has at most one element: it is empty exactly when "$deno(B)(x)$ is true for every $x$" fails. But its one element, when there is one, is a function, not $bullet$, so the product is a singleton without being the set ${bullet}$. The model therefore interprets a Π into a proposition not as the product but as the truth value the product carries:
$ deno(Pi(x : A). B) = { bullet | deno(B)(x) = {bullet} "for every" x in deno(A) }, $
which is ${bullet}$ when the product is a singleton and $emptyset$ when it is empty. This collapse loses nothing, and it is forced by proof irrelevance: every proof denotes $bullet$, so a proof of $Pi(x : A). B$, for instance a `λ`, must denote $bullet$ too rather than the function $x |-> bullet$, and applying such a proof to an argument denotes $bullet$, which is what $deno(B)(x)$'s one element is. Since no rule can look inside a proof, nothing can tell the collapsed meaning from the product it replaces. The result is always $emptyset$ or ${bullet}$, a member of `Prop`'s interpretation ${emptyset, {bullet}}$, _however large_ $deno(A)$ is, even when $A$ is `Prop` itself or a universe. This is _impredicativity_: a proposition may quantify over all propositions, or over all types of a universe, without moving to a larger universe. The set model gets it for free because the size of the domain never reaches the result. The same move is unavailable for data: `Π(A : Type₀). A → A` is a set of functions on all of $V_(kappa_0)$, which is too large to be a member of $V_(kappa_0)$ again, so a Π over a universe into data must live in a larger universe.

*Least fixed points.* An operator Φ on families of sets is _monotone_ if $X subset.eq Y$ (pointwise) implies $Phi(X) subset.eq Phi(Y)$. Its _least fixed point_ is the smallest family $X$ with $Phi(X) subset.eq X$, the intersection of all such families, which exists for a monotone operator acting inside a fixed set such as $V_kappa$. An inductive type is interpreted as the least fixed point of the operator "one more layer of constructors". In Ochr no recursive occurrence of a type lies under a Π (fields are first-order), so every element is built by finitely many constructor applications, and the least fixed point is the union $union.big_(n < omega) Phi^n (emptyset)$, which stays inside $V_kappa$.

*Why a model gives consistency.* A model assigns to each type $T$ a set $deno(T)$ and to each well-typed term $t : T$ an element $deno(t) in deno(T)$; that it does so for every derivable typing is the model's _soundness_. Since $deno(ty("False")) = emptyset$, no closed term of type `False` can exist, and since the model is built in ZFC with the inaccessibles, the conclusion is relative to that theory. For Ochr, "well-typed term" is replaced by "definition accepted by the checker", and the model's soundness is @cor-mean, which follows from the theorem of @sec-route that the checker's steps keep meaning.

=== The interpretation

Types are interpreted as sets in the way just described, adapting Werner's model of the calculus of inductive constructions (Coq's type theory) and Carneiro's of Lean. As above, $deno(T)$ is the meaning of a closed type value $T$, and $deno(v)$ of a closed value.

#thm([Definition], [meaning of types], [
  - $deno(ty("Type")_i) = V_(kappa_i)$ and $deno(ty("Prop")) = {emptyset, {bullet}}$.
  - An inductive declaration in `Type₀` denotes, simultaneously for every value of its parameters, the least family of sets closed under its constructors: the least fixed point of the operator sending a family $X$ to $ā |-> union.big.plus_i {ty("C")_i} times Sigma(g_1 : B_1) dots Sigma(g_k : B_k)$, where each field type is read at the parameters $ā$ and the earlier fields, with every occurrence $ty("D")(overline(b))$ read as $X(overline(b))$. Non-uniform occurrences make the fixed point simultaneous over the whole family; it is still the least fixed point of a monotone operator on families.

    _For example_, `inductive List (A : Type) := Nil | Cons(h : A, t : List(A))` has, at a parameter value $T$, the operator
    $ Phi(X) = {ty("Nil")} union.plus ({ty("Cons")} times deno(T) times X), $
    writing $ty("Cons")(a, l)$ for the triple $(ty("Cons"), a, l)$. Its iterates from $emptyset$ are $Phi^0(emptyset) = emptyset$; $Phi^1(emptyset) = {ty("Nil")}$, since `Nil` has no fields and a `Cons` needs an element of $X = emptyset$; $Phi^2(emptyset)$ adds the one-element lists $ty("Cons")(a, ty("Nil"))$ for $a in deno(T)$; and in general $Phi^(n+1)(emptyset)$ is exactly the lists of length at most $n$, each stage containing the one before (by induction, since Φ is monotone). Their union $L = union.big_(n < omega) Phi^n (emptyset)$ is therefore exactly the finite lists of elements of $deno(T)$: a list of length $n$ appears at stage $n + 1$, and every stage holds only finite lists. $L$ is a fixed point. An element of $Phi(L)$ is `Nil`, which is in $L$, or $ty("Cons")(a, l)$ with $l in L$, so $l$ is in some stage $Phi^n (emptyset)$ and $ty("Cons")(a, l)$ in the next. Conversely an element of $L$ lies in some $Phi^(n+1)(emptyset) = Phi(Phi^n (emptyset)) subset.eq Phi(L)$, by monotonicity. And $L$ is the least such set: if $Phi(Y) subset.eq Y$, as for any fixed point $Y$, then every stage is inside $Y$, by induction on the stage, since $emptyset subset.eq Y$, and $Phi^n (emptyset) subset.eq Y$ gives $Phi^(n+1)(emptyset) subset.eq Phi(Y) subset.eq Y$. So $L subset.eq Y$, and $deno(ty("List")(T)) = L$.
  - An inductive declaration in `Prop` denotes the same fixed point, truncated: ${bullet}$ if inhabited, $emptyset$ otherwise. So $deno(ty("False")) = emptyset$, $deno(ty("True")) = {bullet}$ and $deno(ty("And")(P, Q)) = deno(P) inter deno(Q)$.
  - $deno(ty("Eq")(A, a, b)) = {bullet}$ if $deno(a) = deno(b)$, and $emptyset$ otherwise. An equation field denotes the same.
  - A function type with borrow parameters $x_i : \&T_i$ for $i in I$ denotes a subset $R$ (defined next, @def-inj) of $Pi(overline(d) : overline(D)). "Out"_B (overline(d))$, where $D_i = deno(T_i)$ for $i in I$ and $D_j = deno(A_j)$ otherwise, $"Fin" = product_(i in I) deno(T_i)$ is the tuple of final contents of the borrowed places, and $"Out"_B (overline(d))$ is $deno(B)(overline(d))$ if $B$ is a proposition, $deno(B)(overline(d)) times "Fin"$ if $B$ is borrow-free data, and $deno(T) times (deno(T) -> "Fin")$ if $B = \&T$. For $F$ in this set, $"fwd"_F$ and $"back"_F$ are the two components of $F(overline(d))$; $"back"_F (overline(d))$ is the _backward function_, mapping the value the caller leaves in the returned borrow to the final contents. A Π-type whose class is "returns proofs" is the exception: as argued in @sec-sets, it denotes not this set but the truth value it carries, ${bullet}$ if $deno(B)(overline(d)) = {bullet}$ for every $overline(d)$ and $emptyset$ otherwise (impredicativity). Its borrowed places need no final contents, since a proof's run is discarded.

    _Example, a function that takes a borrow._ In-place addition, `def AddM (x : &Nat) (y : Nat) : Unit`, which walks down `*x` to its final `Z` and replaces it with `y`. Its one borrow parameter is `x`, so $I = {x}$, both domains are $deno(ty("Nat")) = NN$, and $"Fin" = NN$ is the final content of `*x`. The codomain `Unit` is borrow-free data, so a meaning is a function $NN times NN -> deno(ty("Unit")) times NN$, and `AddM` denotes $(n, m) |-> ((), n + m)$: started with `*x` holding $n$, it returns `()` and leaves $n + m$ in `*x`. The borrow is thus modelled as passing the place's starting content in and getting its final content back out.

    _Example, a function that returns a borrow._ `def TailM (x : &Nat) : &Nat`, which returns a borrow of the final `Z` inside `*x`. Again $I = {x}$ and $"Fin" = NN$, but now $B = \&ty("Nat")$, so a meaning sends the starting content $n$ of `*x` to a pair in $NN times (NN -> NN)$, and `TailM` denotes $n |-> (0, v |-> n + v)$. The first component, $"fwd"(n) = 0$, is what the returned borrow holds when the call returns: the final `Z`. The second, $"back"(n) = (v |-> n + v)$, is the backward function: if the caller leaves $v$ in the returned borrow before it ends, `*x` finally holds $n$ with its final `Z` replaced by $v$, that is $n + v$. This backward function is injective (different $v$ give different final contents), which is what the injectivity relation defined next demands of every function returning a borrow.
  - $deno(ty("Id")(A, t, u)) = {bullet}$ iff the meanings of the two observations of @sec-obs are equal.
]) <def-meaning>

*What $R$ is for.* For a function that returns a borrow, the backward function says how the final contents of the borrowed places depend on the value the caller leaves in the returned borrow. The plain product of functions contains every pair $("fwd", "back")$, including ones whose backward function ignores its argument entirely. The model must leave those out, because no Ochr function behaves that way and the checker accepts proofs that rely on it. $R$ is the condition that leaves them out: the backward function of every function returning a borrow, at every type, must be _injective_, so that different values left in the returned borrow give different final contents.

*Why every Ochr function has an injective backward function.* A function type returning a borrow must have a borrow parameter, so Ochr has no `'static` borrows: a returned borrow is always derived from one of the function's borrow arguments, and points at some position inside the places they lend. When it ends, the value the caller left in it is put back at that position. So the final contents still hold that value at that position, and two different values give two different final contents. For `TailM` above, $"back"(n) = (v |-> n + v)$: the value left in the borrow becomes the final `Z`'s replacement, and can be read back off the result. A function returning a leaked borrow would be different: Rust allows a `fn(&mut u64) -> &mut u64` to return `Box::leak(Box::new(0))`, a borrow of a fresh place that nobody owns, whose backward function is constant because what is written through it never reaches the caller's places.

*Why the model must build it in.* The checker relies on it, so a model without it would make an accepted program false. Take
```
def PF (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
```
At its generic call the statement observes the owner of `x`, where the two sides leave `0` and `1`, so it computes to $ty("Eq")(ty("Nat"), 0, 1)$, which is `False`, and `PF` is accepted: writing `0` and writing `1` through a borrow can never be indistinguishable. Now call `PF` with a borrow returned by an unknown function $g : Pi(x : \&ty("Nat")). \&ty("Nat")$. Its hypothesis says that writing `0` and writing `1` through $g(x)$ leave the same contents, which in the model says $"back"_g (n)(0) = "back"_g (n)(1)$. If the meaning of that function type contained a $g$ with a constant backward function, this hypothesis would be true for that $g$, and `PF` would turn it into a proof of `False` that is true in the model, which no sound model allows. So the meaning of a function type returning a borrow must contain only functions with injective backward functions, which is $R$.

#thm([Definition], [injectivity relation], [
  For each type $A$, $R_A subset.eq deno(A)$ is the set of values of $A$ all of whose borrow-returning functions, however deeply nested, have injective backward functions. It is defined by induction on $A$. For propositions and universes $R_A = deno(A)$. At an inductive type, $R$ holds of a constructor value when it holds of each field. $R_(\&T) = R_T$. For a function type, $F in R_(Pi(overline(x) : overline(A)). B)$ iff for all arguments in $R$, $"fwd"_F (overline(d)) in R_B$ and, if $B = \&T$, $"back"_F (overline(d))$ is injective.
]) <def-inj>

#oq(9, [a well-founded definition of the model])[
  As written, the interpretation (@def-meaning) and $R$ (@def-inj) are not yet a valid definition, for two reasons.
  - _They are circular at function types._ @def-meaning makes the meaning of a function type returning a borrow equal to the subset $R$ of a product, while @def-inj defines $R_A$ as a subset of the meaning of $A$. The intended order is: the plain product first, then $R$ as a condition on it, then the meaning as the part of the product satisfying $R$.
  - _"By induction on $A$" has nothing smaller to recurse on._ A function type's codomain is computed by running code at each argument (a type function such as `Cells(E, n)` is defined by recursion on data), not a subterm of $A$; and a type variable, such as a parameter $A : ty("Type")_0$, has no structure at all, so $R$ is undefined there.
  _Resolved on a slice by test 0_ (@sec-test-model), neither by the repair first proposed here (pairing each type with a set of good elements, which would make conversion of functions unsound) nor by a universe of codes. A function type means only its good functions, so $R$ at every type is the meaning itself, and a type variable means a set, all of whose elements are good. Meanings are defined on terms, by recursion on the item's position in the program, the term's structure, and, inside a recursive function, the rank of its decreasing argument; $ty("Type")_i$ means $V_(kappa_i)$ outright.
]

#thm([Definition], [truth], [
  A closed proposition value $P$ is _true_, $ok(P)$, when $deno(P) = {bullet}$.
]) <def-truth>

In the paper's fragment, truth was defined syntactically on ground proposition values (`True`, `False`, `And` and stuck equations, the last counting as true). Beyond the fragment, propositions include Π-types (implication and universal quantification over data, functions and propositions), user inductives in `Prop`, and `Eq` at any type, so truth must be semantic. Whether a stuck equation still counts as true is Q3 (@sec-oq).

=== Conditions under which the model is defined <sec-model-conditions>

#thm([Lemma], [the model is well defined], [
  If every inductive declaration satisfies (I1)–(I6) below, every match on a proof satisfies (I7), recursion satisfies (I8), `Eq` satisfies (I9), and borrows are only of `Type₀`, then @def-meaning assigns a set to every type value formed by an accepted program, in the universe of its sort.
  - (I1) _Strict positivity._ The declared type $ty("D")$ occurs in a field type only as the whole field type, or inside another inductive at a _nestable_ parameter (one occurring in that inductive's fields only as a whole field type or at a nestable parameter); never left of a Π, under `&`, or as the argument of a type function.
  - (I2) The arguments of an occurrence of $ty("D")$ never mention $ty("D")$.
  - (I3) A parameter is never called in a field type; only earlier global type functions are.
  - (I4) Parameter types do not mention $ty("D")$.
  - (I5) Fields form a telescope: a field's type mentions only parameters and earlier fields.
  - (I6) Every field of an inductive in `Type₀` or `Prop` lives in `Prop` or `Type₀`.
  - (I7) A match on a proof produces data or a type only from a subsingleton (no constructors, or one whose fields are all proofs).
  - (I8) Recursion is never on a proof.
  - (I9) `Eq` decides only by conversion (`True`) or by distinct constructors of one inductive (`False`); otherwise it is stuck. So an equation at any type, functions and sorts included, adds no rule that could prove `False`.
]) <lem-model>
#proof[(I1)–(I5) make the constructor operator monotone on families, so the least fixed point exists; (I6) keeps it in the sort's universe; (I7) is what makes a match on a proof well defined, since all proofs are $bullet$ and only a subsingleton's eliminator cannot tell them apart; (I8) because a proof has no structure to measure; (I9) because constructors are injective with disjoint images. Borrows only of `Type₀`: borrowing a universe would put `Π(x : &Type₀)(a : *x). *x` in `Type₀`, which would be impredicative and have no set model.]

#explainer[strict positivity and W-types][An inductive declaration is read as "the least set closed under its constructors", and such a set exists only if the type being declared is used _positively_ in its fields. A field that is a function _out of_ the type breaks this, and no set fits the declaration. In Ochr, with `inductive Bad := MkBad(f : Π(x : Bad). Empty)`:
  ```
  def L (b : Bad) : Empty := match b { MkBad(f) => f(b) }
  def bad : Bad := MkBad(λ(x : Bad) : Empty => L(x))
  def Boom : False := absurd(L(bad))
  ```
  `L` applies `b`'s own field to `b` itself; `L(bad)` would loop forever, but `Boom` is typed by its callee's statement alone and proofs are not run, so it would be a closed proof of `False`. (Before the positivity rule existed, the checker accepted exactly this.) Linearity does not stop it: `f` is used once, and `b` is consumed only once, by the call, because the match does not consume it (it names `f` as a sub-place of `b`). A language where a match consumes its scrutinee, such as Bend, must rebuild the value and write `f(MkBad(f))`, using `f` twice, which affinity rejects; Ochr's matches do not consume, so it needs positivity instead. _Strict positivity_ is the syntactic rule that rules this out: the type being declared appears only as a whole field type, or nested inside another inductive that itself uses it positively, never left of an arrow. A _W-type_ is an inductive with a field that is a function _into_ the type, such as `Tree := Node(children : Π(n : Nat). Tree)`, an infinitely branching tree. That is strictly positive and Lean allows it, but its least fixed point is reached only after transfinitely many stages of the construction, which the model must have room for. Ochr forbids any function-typed field, so it has no W-types, and its fixed points are reached after ω stages (@sec-sets). This is one reason Ochr may be weaker than Lean (Q8).]

*Status.* #s-paper. Every condition is enforced by [Ind-decl], the match rules and [Rec]; a probe of each condition against the checker found none missing. One condition is enforced more strictly than (I9) needs: equation fields are required to be over first-order data, which a type parameter instantiated at a function type bypasses harmlessly.

== Conversion is sound <sec-conv-sound>

#thm([Lemma], [conversion respects meaning], [
  If $v equiv w$ (definitionally equal) at a state Ω reached by the checker, then $deno(v, at: gamma) = deno(w, at: gamma)$ for every assignment $gamma$ of Ω (@def-assign). In particular, convertible closed values (no free variables and no unknowns, @sec-prelim) have equal meanings, and convertible propositions are equally true.
]) <lem-conv>

The argument is one principle per conversion rule. Every principle reads the values under an arbitrary assignment, so it speaks of every element of every type, not only of values the machine can build.
- (V1) Normal forms are compared structurally; the meaning of a normal form is a function of its parts.
- (V2) A constructor value means its tag and fields; the parameters it records are fixed by its type and never read, so ignoring them is sound.
- (V3) A sealed program means the meaning of its program (@def-state-meaning), so two with the same text have the same meaning under every assignment, and refinement substitutes into both alike.
- (V4) A Π-type means its family of parameter types and codomain over every argument. [Conv-pi] compares the two at the generic arguments of the first, which are fresh unknowns. An assignment extended to those unknowns can give them any element of the parameter types' meanings, so, by @thm-mp applied to the evaluation of the parameter types and the codomain, equal meanings at the generic arguments under every extension are equal meanings at every argument. The class and the borrow flag are part of the meaning: they decide which functions inhabit the type and how their calls close off.
- (V5) A function value means a function on its annotated domain, with the backward functions of @def-meaning. [Conv-fun] compares the observations of the two generic calls, which run each function's body on fresh unknowns. By @thm-mp applied to those runs, the meaning of an observation under every extension of $gamma$ is the function's result and final contents at every argument, since the fresh unknowns range over every element of the domain, non-computable functions included. So convertible observations mean equal functions.
  #why[the first draft argued (V4), (V5) and (V9) from (P), the lemma that a run which never inspects an unknown behaves uniformly at every instance, because it compared the generic call with runs at instances. Here nothing is compared with an instance: the generic call's own meaning, under every assignment, already covers every argument.]
- (V6) Conversion is least: a comparison that needs itself answers "not convertible". Read coinductively, any two functions stuck at their generic calls would be identified, and `J` along that proves `Eq(Nat, S(Z), Z)`.
- (V7) The unit laws and $eta$ at `Unit` are equalities of sets: $deno(ty("True") and P) = deno(P)$, and `Unit` has one element.
- (V8) `Eq` computes by meanings: reflexivity by (V1)–(V7), injectivity and disjointness by (V2), and an equation over `⊥` stays stuck. `J` returns its argument only at convertible endpoints, where it is the identity on meanings.
- (V10) A value that contains `⊥` is convertible with nothing, itself included ([Conv-bot]). `⊥` means no information, so two values that hold it may stand for different values, and identifying them is not monotone. Until D83 the checker's conversion lacked this rule: its first test identified equal representations, `⊥` included, which gave the fifth closed proof of `False` (@sec-risks), through conversion itself and through `trans`. D83 adds the rule, and its counterpart for [Rewrite]'s search for occurrences, a separate code path: [Rewrite] finds no occurrence of a value holding `⊥`. Its cost is one known incompleteness: a type holding `⊥` is not convertible with itself (`SelfBot`, a `P → P` for such a `P`).
The first draft's (V9), that conversion is stable under refinement, is not needed: conversion is a check made at one state, and @thm-mp carries its conclusion through every later step.

*An induction shared with @thm-mp.* (V4) and (V5) use @thm-mp on runs that conversion makes, and @thm-mp uses this lemma at every leaf. Both are proved by one induction on the checker's derivation, which is finite because the checker accepted: the runs a conversion check makes are parts of that check's derivation.

*Status.* #s-paper, to be re-argued in this form; the first draft's argument rested on (P). Every rule is enforced by the checker's conversion; 35 probes, among them transport along true equations between in-place programs, behave as predicted.

== Meaning preservation <sec-route>

#reminder[
  - The checker checks a definition $d_k$ once, at its _generic call_, where each parameter is bound to a fresh abstract value ([Def], @sec-typing). A match on an unknown _splits_, checking each arm in its own _world_ ([Split], Worlds); a call that gets stuck on an unknown is _closed off_ into a sealed program #seal[$t$] ([Close], @sec-machine).
  - $deno(T)$ is the set a closed type $T$ means in the model (@def-meaning), and $R$ the injectivity relation (@def-inj).
  - The check of $d_k$ builds a finite _case tree_: a node for each split, with one child per arm, and a leaf where the body ends.
]

=== The idea

The checker never runs a definition on real inputs. It runs it once, on unknowns, and accepts it if every leaf of the case tree has the goal's type. The first draft of this plan then took each concrete instance, ran the definition on it for real, and walked the case tree in step with that run (@sec-old). The present route compares the checker's run with no second run. It gives each state of that run a meaning, as a function of what the unknowns stand for, and compares the run with the _reference run_ of the same term: the meaning of running it, which applies the meanings of functions at calls instead of running their bodies (@def-refrun). Every step of the checker keeps that meaning, or loses only information. At a leaf the checker has established that the result has the goal's type, so under every choice of what the unknowns stand for, the result's meaning lies in the goal's. Since the unknowns range over every element of their types, that is exactly the statement that the definition means an element of its type.

#why[a second run needs a relation saying how its states correspond to the checker's, and most of the first draft's open questions lived in that relation (Q2, Q4–Q6). With one run and one meaning there is nothing to correspond: the "other side" is mathematics, which has no states.]

#explainer[symbolic execution and its soundness][_Symbolic execution_ runs a program on unknowns instead of values. Where the program branches on an unknown, the executor follows every branch, recording on each what it learned (a _path condition_, such as "$sigma = 0$"). Each symbolic state stands for many concrete situations: one for each choice of values for its unknowns that satisfies its path condition. The executor is _sound_ if each symbolic step maps every situation its state stands for to one the next state stands for. The statement is one-sided: a symbolic state may stand for _more_ situations than can really arise (an _over-approximation_), which only makes the executor more cautious. No second run is involved; the comparison is between one step and what the step means. Aeneas, the Rust verification tool whose borrow model Ochr's machine follows, proves its symbolic semantics sound against its concrete one in this style. Here the situations are not machine states but set-theoretic meanings, which is what lets them include non-computable functions.]

=== Assignments and the meaning of a state

#thm([Definition], [assignment], [
  Let Ω be a state the checker reaches while checking a definition. An _assignment_ $gamma$ of Ω gives each abstract value $sigma$ of Ω an element $gamma(sigma) in deno(Delta(sigma), at: gamma)$, in the order the unknowns were created (a type in Δ may mention earlier unknowns, so its meaning depends on $gamma$ at them). No separate condition of injectivity is needed: a type means only its good elements, so $R$ is the meaning itself (@sec-test-model). It must satisfy the _path condition_ of Ω: for each generalisation record $n := sigma$ in force in the current world, $gamma(sigma) = deno(n, at: gamma)$. Refinements made by a split or an η-expansion substitute a constructor value for $sigma$ throughout the state, so they need no condition. An assignment of $d_k$'s generic state is a choice of arguments for $d_k$: one element of each parameter's type, including the initial content of each borrowed cell.
]) <def-assign>

Nothing requires $gamma(sigma)$ to be computable. For $sigma : Pi(n : ty("Nat")). ty("Nat")$ it ranges over all functions $NN -> NN$, the characteristic function of the halting problem included; for $sigma : ty("Type")_0$, over every set in $V_(kappa_0)$; for $sigma : ty("Prop")$, over $emptyset$ and ${bullet}$.
#why[the generic call binds each parameter to a fresh unknown, and an assignment says what those unknowns stand for. Ranging over every element of the model's sets, not only over values the machine can build, is what makes the conclusion a statement about the model's Π, which quantifies over every set function. This closes the gap all three referees found in the first draft (@sec-referees).]

#explainer[information orders][An _information order_ compares two descriptions of the same thing by how much they say. A description that leaves something open is _below_ one that fills it in, and nothing it does say may contradict the other. The least element says nothing at all, and is often written ⊥, which is why the moved-out marker can be read as it. A step is _monotone_ if more information in gives more information out, or the same: a monotone step never turns "unknown" into a definite answer that more information would contradict.]

#thm([Definition], [meaning of a state], [
  Under an assignment $gamma$:
  - $sigma$ means $gamma(sigma)$; `⋆` means •; a constructor value means its tag and its fields' meanings; a type value means its set (@def-meaning), read at the meanings of what it embeds.
  - A sealed program #seal[$t$] means $deno(t, at: gamma)$, the meaning of running its program (Q11).
  - A closure means a function on its annotated domain: at each element of its parameter types' meanings, the meaning of its body with the parameters bound to that element. The function may be partial, taking an error value where the body goes wrong; no accepted derivation reaches such a point. A recursive closure, or a recursive global, has a meaning by _guarded_ recursion on the rank of its decreasing argument: a recursive call whose decreasing argument does not drop in rank means the error value. So every `fix` has a meaning, checked or not; passing [Rec] is what makes the guard never fire, which is part of membership.
  - A state with live borrows is read under a _future_ $phi$, which gives each live borrow's label ℓ its _final content_ $phi(ell)$, an element of the meaning of the borrow's content type. A loan of ℓ, at a place that lent its content, means $phi(ell)$: what the place will finally hold. A place holding $"borrow"_ell w$ means $w$'s meaning, its _current_ content, which is what a read through it sees. A sealed fill means its program, run with each hole read from $phi$. So a state means a function of a future, as a function returning a borrow means a backward function (@def-meaning). We write $deno(Omega, at: gamma)(phi)$ for the meaning of Ω under $gamma$ and $phi$.
  - An open dependent value means the raw tuple of its fields' meanings, which need not lie in the set its telescope describes; [Repack] is where membership is restored.
  - `⊥` means _no information_: the least element of the order of @def-lessinfo. The model ignores linearity otherwise: a move makes a place inaccessible to the program, but changes no mathematical value.
  A _configuration_, a state together with a term still to run, means the reference run of the term from that state (@def-refrun).
]) <def-state-meaning>

*Why two readings.* A place that lent its content will be given back the borrow's final content, so it means that; a place holding the borrow can still read and write it, so it means what is there now. [End] connects the two: it fixes the borrow's final content at its holder's current content, and forgets the holder. The Lean encoding of the state (@sec-test-ho) found this shape necessary: one function from the final contents to the resolved contents cannot express a read through a borrow.

#why[every position of a state the checker builds now has a meaning that depends only on $gamma$ and on the final contents of the borrows still live. The fills with holes, which made the first draft's agreement hold only "up to resolution" (with `Pick(n, x, y) := match n { Z ⇒ x, S _ ⇒ y }` at an unknown `n`, the hole of its returned borrow sits in the fills of both lent places), are ordinary functions of the hole here; reading a place whose meaning depends on a live hole ends that borrow, which fixes the hole at the borrow's current content.]

*Why `⊥` means no information.* `⊥` could instead mean the value that was moved out, which would make moves invisible and need no order. Two tests ruled that reading out (@sec-tests). A stuck block takes a place by move when some arm moves it, even if another arm _writes_ it, so the block's `⊥` would have to mean a value the writing arm contradicts. And the checker's `⊥` does not record what was moved, so the meaning of a state would need ghost data that the state does not hold. Read as no information, both problems disappear, at the price of the order below.

#thm([Definition], [less informative], [
  A state meaning $m'$ is _less informative_ than $m$, $m' lessinfo m$, when every reading of $m'$ is a reading of $m$: for every future $phi'$ there is a future $phi$ such that $m'(phi')$ and $m(phi)$ agree at every position where $m'(phi')$ says something (is not no information). A step is _exact_ when it keeps the meaning; an _end_ when it ends a borrow, which narrows the futures to those in which the borrow ends with its current content and forgets the holder; and an _over-approximation_ when it forgets a place, as a stuck block's capture by move does where the arm the assignment selects would keep it. Ends and over-approximations are less informative.
]) <def-lessinfo>

=== The theorem

#thm([Definition], [reference run], [
  The _reference run_ $refrun(t)$ of a term $t$ sends the meaning of a state, under an assignment and a future, to the meaning of a result and of a new state, or to the error value. It is defined by structural recursion on $t$, inside the model's recursion on program position and decreasing argument, with the machine's rules except four:
  - every call applies the callee's meaning (an earlier global's, a parameter's under the assignment, or a closure's) and never runs its body; for a callee returning a borrow, each lent place means its component of the backward function at the returned borrow's final content;
  - before a place is read, borrowed or matched, it ends exactly the borrows whose final content the place's meaning depends on, and nothing else;
  - a match on data reads the tag of the scrutinee's meaning, which under an assignment is always a constructor, so nothing is stuck and nothing is split;
  - `Id`, `Eq` and `J` mean as in the model, and statements run on a copy that is thrown away.
  A function's meaning is read off the reference run of its body in a fresh frame, with a cell holding each borrowed argument.
]) <def-refrun>

#why[the reference run is the denotation of the term as a state transformer, not a second machine run: it never runs a callee's body, it applies the callee's meaning, which at a function parameter ranges over every set function. It is the standard each step of the checker is measured against.]

#thm([Theorem], [meaning preservation, membership and well-formedness], [
  Let $cal(P) = d_1 dots d_m$ be accepted and hole-free, and let the checker, while checking $d_k$, run a term $t$ from a state Ω satisfying (b) and (c). For every assignment $gamma$ of Ω, following at each split the arm whose constructor $gamma$ selects, the run reaches a value $v$ and a state Ω', and:
  - (a) _Below the reference run._ There is an assignment $gamma'$ of Ω', extending $gamma$ to the unknowns the run created and satisfying its path condition, such that the meaning of $v$ and Ω' under $gamma'$ is less informative than $refrun(t)$ applied to the meaning of Ω under $gamma$, and that reference run is not the error value. It is proved one rule at a time: each step is exact, an end the reference does not make, or an over-approximation.
  - (b) _Membership._ Every value stored in Ω', at a binding, a temporary or in Δ, has its meaning in the meaning of its stored type under every typed future: $deno(v, at: gamma')(phi) in deno(T, at: gamma')$ for every future $phi$ giving each live borrow a final content of its type. (Since a type means only its good elements, this includes the injectivity of every backward function, the old relation $R$.)
  - (c) _Well-formedness._ Ω' is well formed (@sec-wf).
  (a), (b) and (c) are proved together, by induction on the checker's derivation for $d_k$, inside an outer induction on $d_k$'s position in $cal(P)$ and the size of its decreasing argument under the assignment.
]) <thm-mp>

#why[(a) says the checker never computes anything the meaning of the term does not, only possibly less; (b) says it never stores a value in a slot its type does not describe, whatever the live borrows write there later; (c) says the borrow discipline that gives the state a meaning still holds. None of the three suffices alone, and the first test showed it: of five past proofs of `False`, part (a) alone catches one (@sec-tests).]

*For a split, every assignment has an arm.* An assignment gives the scrutinee $sigma$ an element of $deno(ty("D")(overline(a)), at: gamma)$, which is a disjoint union of its constructors' field tuples (@def-meaning). So exactly one arm's constructor matches, and $gamma$ extends to that arm's fresh field unknowns by the element's fields; the arm's refinement $sigma := ty("C")_i (overline(sigma))$ is then a substitution that changes no meaning. A split on a sealed program $n$ first generalises it to a fresh $sigma$ with the path condition $gamma(sigma) = deno(n, at: gamma)$, which $gamma$ satisfies by taking that value. So the case tree covers every assignment, and no step needs a "real" value with a head constructor, which is where the first draft's walk broke on non-computable witnesses.

*Where (a) needs (b).* Most steps keep meaning by computation alone. Two kinds replace a value by a canonical one: a value whose declared type is a proposition becomes `⋆`, and a value whose declared type reads as `Unit`, or as a one-constructor type (η), becomes `()` or that constructor. Those keep meaning only if the value lies in its type's meaning: $deno(v, at: gamma) in deno(P, at: gamma) subset.eq {bullet}$, or in the one-element set $deno(ty("Unit"))$. For a stuck call that becomes `()` at a declared `Unit`, that is $deno(f, at: gamma)(overline(a)) in deno(ty("Unit"))$, membership of $f$'s meaning in its Π-type. That comes from the outer induction for an earlier global; from the outer induction at a smaller argument for a recursive call, since [Rec] made its decreasing argument a strict part of the entry value, and the strict-part relation on a least fixed point is well founded (@sec-sets); from (b) at an earlier step for a closure built earlier in the run; and from $gamma$ itself for a function parameter.

*Where (b) and (c) are earned.* (b) and (c) are not consequences of (a); they are established at particular steps, and the checker's _checks_ are where. Membership of a value that leaves an open dependent value is established by [Repack] at every whole-again point, under every future of the holes still lent from it; membership of a block's or a `J`'s sealed result by the return check at the end of each arm; membership of a recursive function, that its guard never fires, by [Rec]; membership of a function returning a borrow, that its backward function is injective, by an invariant that every hole is placed injectively in the state, kept by [Access], D67, D65 and (C8) (test 2); and membership of a returned borrow's forward value by the requirement that a returned borrow be whole. A check that fails produces no derivation, so only its accepting direction carries an obligation, and that obligation is exactly the part of (b) or (c) the check is there to establish.

*Why this is ordinary induction.* Every appeal is to an earlier step of the same derivation or to the outer hypothesis. The first draft had a cycle: soundness needed stability, stability needed a typing invariant, and the invariant needed soundness (the foundations and structure referees, @sec-referees). Here the typing invariant is (b) itself, proved step by step alongside (a). The first draft's counterexample to "declared readings survive refinement", a sealed call of an unchecked global that re-runs to a type (an unchecked `F (n : Nat) : Nat := Nat` at a refined argument), cannot arise: while $d_k$ is checked, every global is $d_1, dots, d_(k-1)$, checked and covered by the outer induction, or $d_k$ itself at a smaller argument.

#thm([Corollary], [an accepted definition means an element of its type], [
  Under @thm-mp and @lem-conv, for every assignment $gamma$ of $d_k$'s generic state, the meaning of $d_k$'s body (its result and the final contents of its borrowed cells) lies in $deno(G, at: gamma)$, its goal. So $deno(d_k)$, the function sending each choice of arguments to that meaning, lies in the meaning of $d_k$'s declared Π-type.
]) <cor-mean>
#proof[Follow the case tree from the root under $gamma$, using (a) at each step: every assignment reaches one leaf $(Omega', v, A)$, with an extended assignment $gamma'$. By (b), $deno(v, at: gamma') in deno(A, at: gamma')$. [Def] checked $A equiv G'$, the goal refined along the path, so by @lem-conv $deno(A, at: gamma') = deno(G', at: gamma')$, which is $deno(G, at: gamma)$ because the path's refinements are substitutions and its records are $gamma'$'s path condition. By (a), the leaf's meaning is less informative than the reference run of the body, which is $d_k$'s meaning at the arguments $gamma$ chooses; but the result and the borrowed cells' final contents are whole at a leaf ([Return]), so on them "less informative" is equality.]

#thm([Corollary], [consistency], [
  Under @thm-mp, @lem-conv and @lem-model, @target holds.
]) <cor-cons-route>
#proof[A parameterless definition $c$ is checked from the empty state ([Const]), which has exactly one assignment, the empty one. By @cor-mean, $deno(c) in deno(T)$ for the value $T$ of its type. If $T$ computed to `False`, then by @lem-conv $deno(T) = deno(ty("False")) = emptyset$, which has no element.]

=== What the checker must satisfy <sec-wf>

The theorem asks four things of the checker. None asks that a run make progress or terminate; consistency needs neither.

*Well-formedness, part (c).* Backward functions mean the right thing only under the borrow discipline, so @def-state-meaning is defined only for states satisfying (WF1)–(WF6) of @sec-states (each label has at most one borrow; loans only where closing off allows; no cycles among borrows; closures capture no borrow; arguments exclusive at call points; bindings hold values of their types) and
- (WF7) `&` is applied only to types in `Type₀`, so that a borrow means forward and backward functions on data.
An earlier version also put "every closure and global has passed [Rec]" here, on the ground that a `fix` means a function only through well-founded recursion. Test 0 showed that guarded recursion gives every `fix` a meaning, so [Rec] belongs to membership instead.
The first draft assumed the preservation of (WF1)–(WF6) without proof, and it is not yet proved for the current rules; test 2 assumed it, and found that the preservation of (WF2) needs (WF3). (WF5), loan-free arguments at a call, is not only a runtime matter: with a live loan in an argument, a read now would depend on a write made later, so the meaning of a state needs it.

*Monotone computing steps.* Steps that over-approximate (a stuck block's captures by move, a capture split less finely, an early end) are harmless only if no later step turns the missing information into a definite answer that the full information would contradict. So every step that _computes_ on a state must be monotone in the order of @def-lessinfo: `Eq` and `J` computing to `True`, `False` or a value, a match choosing an arm, [Close] choosing its row, conversion, which decides that two values are equal, and [Rewrite]'s search for the occurrences of a side, which decides that a subterm equals it. Test 2 checked `Eq`, `J`, matches and [Close]'s rows. The checker has the instances for them: an equation with `⊥` on either side stays stuck rather than computing (a test, `MovedBothSides`, guards it), reading `⊥` is an error, and an observed owner holding `⊥` gives a stuck equation. Conversion and [Rewrite] did not, until D83: each identified two values that hold `⊥`, which may stand for different values, the fifth closed proof of `False` (@sec-risks). D83 adds [Conv-bot], a value containing `⊥` is convertible with nothing, itself included, which also covers `trans`; and [Rewrite] finds no occurrence of a value holding `⊥`. So every computing step is now monotone over `⊥`. The generalisation records, which also compare sealed programs by text, are safe: `⊥` reaches a data-valued sealed program only inside an erased statement. This is a smaller form of the first draft's monotonicity requirement: it concerns computing steps only, not every decision.

*Decisions, by kind.* The first draft required every decision to come out the same on the generic call and at every instance. Here each decision falls into one of four kinds, and the census of @sec-tests sorted every one:
- _same_: every outcome keeps the meaning, possibly given (b). η at `Unit` and at one-constructor types (the type has one element); a proof's value being `⋆`; `Eq` and `J` computing; [Split], records and re-normalisation.
- _aligned_: the outcomes differ in meaning, so the model must make the same choice, and it can because the decision reads only syntax and declared types, which the model's meaning of code reads the same way. Whether a term is erased (run in place, or on a private copy that is thrown away, discarding writes through borrows); a function type's class; whether a statement argument runs in place; [Close]'s row. A binding's class is the decision of this kind the first draft identified, read from syntax since D77.
- _less informative_: copy or move, and a stuck block's captures by move and splits. Harmless given monotone computing steps.
- _check_: only accepts or rejects, so only the accepting direction needs an argument (above). Some checks establish (b), some (c), and some protect only runtime safety, which consistency does not need but type safety (@target-safe) does: the requirement that a borrow be whole when it is passed to a call that closes off. (That a returned borrow be whole is membership: a returned borrow holding `⊥` has a forward value with no meaning.)

*Five lemmas behind "same".* The decisions of kind _same_ rest not on one argument per site but on five lemmas: membership, part (b); the soundness of the function that reads a value's own type (`valType?`: the meaning of a value lies in the meaning of the type it reads, under every assignment), used where a type is read off an embedded value; _footprint coverage_, that the places `Id` observes include every place either side may write, under every assignment, with the extra owners at a call site handled by the injectivity of contexts (a context holding a loan is injective in the loan's final value, which test 2's invariant that holes are placed injectively provides); conversion soundness (@lem-conv); and well-formedness, part (c).

=== The lemmas each step uses

The step lemmas, one per checker rule, are where the principles of @sec-principles are used, read as statements about meaning:
- worlds (X1)–(X4): leaving an arm drops every fact that depends on the arm's path condition, so the assignment that held in the arm's world is never asked to hold elsewhere; keeping such a fact is how `EtaBoom` proved `False` (@sec-risks);
- closing off (C1)–(C9): [Close] is exact by definition, because a sealed program means its program, and (C1) is what makes the text rebuild the call;
- locality (L1)–(L7), read as the compositionality of the meaning of code: a call's meaning changes only its result and its borrowed places (the frame property, proved on the heap slice as `Ochr.Heap.frame` and `call_effect`);
- observation (O1)–(O5): `Id`'s computation to a conjunction over the footprint is exact by footprint coverage;
- erasure and captures (E1)–(E5), (K1)–(K3): erased runs keep meaning because their copies are discarded, and captures are over-approximations in the sense of @def-lessinfo;
- wholeness (W1)–(W2): every point where a value passes to code relying on its type is a point where (b) is established for it;
- recursion (R1)–(R6): membership of recursive functions (the guard never fires) and the outer induction.

=== From meanings to type safety <sec-safety>

Type safety (@target-safe) reuses the route. The step lemmas of @thm-mp are untyped: they speak of every state the checker reaches, and a closed run is such a state with no unknowns, so they cover concrete runs as well. And the reference run of an accepted definition never goes wrong (@thm-mp, part (a)). What remains is to connect the machine's run of the erased program with the reference run:
- (a) _Error reflection._ If the machine goes wrong at a concrete input, the reference run goes wrong there too. Since the reference run of an accepted definition never does, the machine never does. #s-open.
- (b) _Runtime `J`._ The checker computes `J` only at convertible endpoints. In a closed run a hypothesis $ty("Eq")(A, a, b)$ can be true while $a$ and $b$ are not convertible (two closures with equal meanings and different code), and the run would stop at `J`. The likely fix is that at runtime `J` returns its transported term, erasing the cast, while the checker keeps its rule. An open design question (Q3).
- (c) _Erasure._ Running with proofs and types erased gives the same result as running them: a statement runs on a private copy that is thrown away, so skipping it changes nothing. The first draft proved this only for its first-order fragment. #s-open.
- (d) _Termination._ Every recursion passed [Rec], so the guard of guarded recursion never fires (part (b) of @thm-mp): each recursive call is at a smaller rank, and the run terminates. #s-red[@thm-mp (b)].
- (e) _Well-formedness_ at runtime, shared with consistency (@sec-wf).

*The frame property is a lemma, not a target.* Both targets use it: for consistency it is the compositionality of the meaning of code (a call's meaning changes only its result and its borrowed places), and for type safety the fact that a call's effect at runtime is its isolated run, plugged back into the caller.

*Adequacy* in the narrow sense is the last clause of @target-safe: a closed run's result means what the reference run says. With it, an accepted `Id` lemma makes its two observations equal at runtime. That the two terms can then be swapped in every context is more, and is @target-adeq.

=== `Id` adequacy <sec-adeq>

@target-adeq says that terms proved equal by `Id` are interchangeable. Neither of the other targets implies it. @target needs only that the checker computes `Id`'s meaning soundly, and that meaning can be weaker than substitution: `Id` compares the results and the observed owners, not everything a later context could notice. @target-safe does not look at `Id`'s meaning at all.

*The new piece is a context lemma*: what a context can observe of a term is exactly what `Id` compares. Given it, a proved `Id` makes the two terms indistinguishable to every continuation, and @target-adeq follows from @thm-mp and @target-safe. The audit of @sec-test-adeq lists every channel through which a context can observe a term and compares the list with `Id`'s footprint.

*Two known gaps.* Neither is a proof of `False`: in both, `Id`'s meaning in the model is computed soundly, and what fails is substitution.
- _Moves._ `Id` does not compare a place that either side leaves moved, so two terms that move different places, such as `F(x)` and `F(y)`, can be proved equal while a continuation that reads `x` tells them apart. D84 (drop at the join), not yet merged, closes this.
- _Where a borrow points_ (`RePoint`, accepted on main at `a2861cbf`). `def RePoint (x z : Nat) (y : &Nat) : Id(Unit, (y := &x; ()), (y := &z; ())) := refl`. The resolved owners are unchanged on both sides, so `Id` holds; but a continuation `*y := 7` writes `x` after one side and `z` after the other. So the observation principle that where a borrow points does not matter, only resolved contents (O2), is false under substitution. The likely fix is to observe each borrow variable a side assigns by writing a fresh $sigma_w$ through it, as [Obs-borrow] already does for a borrow-typed result.

=== How the route answers the referees <sec-referees>

Three independent referees attacked the first draft on 2 November 2026, each asked for an obstruction that would stop it from ever reaching a proof. None showed consistency impossible; all three found that the draft as written could not be completed.
- _Foundations._ The draft's truth (in the set model) and its proof (over machine values) do not meet. Ochr can state "$f$ decides halting": with `Prog` a type of two-counter machines, `ExW(Prog → Nat, Decides)` is true in the set model, witnessed by the characteristic function of the halting set, but by no machine value, and an accepted lemma `L3` derives excluded middle for halting from it. On it the walk breaks: matching on the hypothesis binds the decider to an unknown $sigma_w$, and splitting the stuck $n = seal(sigma_w (P_0))$ needs a head constructor no machine value supplies. Here $sigma_w$ ranges over every function, the halting decider included, and $n$ is generalised to a fresh $sigma_n$ with the path condition $gamma(sigma_n) = gamma(sigma_w)(P_0)$; the split on it covers every assignment, since the value is `Z` or `S` of something. Likewise a lemma `M` stating that every decider answers 0 on a program that halts at once holds at every set-theoretic decider by the outer induction at `M`, not vacuously.
- _The simulation and stability._ The referee found `EtaBoom`, then a closed proof of `False` on main (@sec-risks), and showed that (P) was false as first stated, that the draft's decomposition into (P), closing off and splits was incomplete, and that its Lean stability conjecture was false without an information order. `EtaBoom` is a step at which part (a) fails: leaving the arm kept field unknowns whose types were read under that arm's path condition, so in the sibling arm no assignment exists at all, since one field would need an element of $deno(ty("Void")) = emptyset$. The referee's other three findings concern lemmas this route does not use.
- _Structure._ The referee found the same gap between truth and proof, a cycle between soundness, stability and the typing invariant, and a missing obligation on about 80 unchecked array accesses in the checker. Here truth and the proof meet by construction, the cycle is gone as described above, and conversion soundness is argued under assignments rather than from (P). The array accesses, and Q8, remain.

= The principles the checker enforces <sec-principles>

The step lemmas of @thm-mp use a small number of principles, each derived from a model of one part of the calculus (dependent fields, case splitting, observation, recursion, erasure, closing off, locality), and each enforced in the checker at a single place, so that a rule cannot be forgotten by one of several code paths; @sec-route says which step uses which. Every current checker rule corresponds to one of them, and in each area probes looked for a rule the principles demand and the checker lacks. Three such gaps were found on the checker of October 2026, each a closed proof of `False`, and a referee found a fourth, `EtaBoom`, in the worlds principle as first written; all are fixed (@sec-risks). The principles were first stated for the superseded route's simulation; none is proved.

== Locality <sec-locality>

- (L1) _Names are local._ A running body names only places of its own frame. A closure's captures are copied into its own frame when it is called, and a closure captures no borrow. Global definitions are immutable.
- (L2) _Writes stay in the frame._ A borrow carries its content, so a write through a borrow changes the content inside the borrow held in the running frame; the lender's place does not change until the borrow ends.
- (L3) _Calls exchange only what is passed._ Arguments move into the callee's frame (an owned value is moved out of the caller; a borrow argument carries the caller's loan); the callee returns its result; popping its frame drops its bindings, ending its borrow parameters; [Close] fills only the loans of the call's borrow arguments.
- (L4) _Borrowers sit at or above their loans_, in every run whose effects persist: a loan in frame $f$ is borrowed from $f$ or a frame above it. It follows from no borrows in data, no borrows of borrows, closures capturing no borrow, and [Drop] refusing to let a borrow of a local outlive it. So [Access] and [Drop], which start from a place of the top frame, end only borrowers of the top frame. (L4 fails inside the checker's own private copies, which compute a field's type by binding copies of fields in a scratch frame; those copies are discarded, so nothing leaks.)
- (L5) _Ending is the one channel down._ [End] is how a lender below gets its content back; by (L4) the places a run can change below its frame are exactly the places its frame's borrows were lent from.
- (L6) _Private runs leave no trace._ Statements, and the checker's own scaffolding, run on copies that are thrown away.
- (L7) _Sealed programs are closed, and refinement is not a run._ A sealed program's re-run starts from the empty environment and reads no frame. Refinement substitutes across all frames, but that is the typing judgement acting on the whole state, never the effect of a run.

_Enforced:_ the checker ends a borrower found from a place of the top frame in one function (`endTopLoan`), which asserts (L4) outside private copies; it never fires on the test suite.

== Closing off <sec-closing>

- (C1) _Reconstruction._ The sealed text rebuilds the call exactly: the same function value (code and captures), the other arguments as their values at the call point, each borrowed content in a fresh cell. Nothing else of the call point reaches the callee, by (L1) and (L3). So a sealed program is a closed text whose run depends only on what it embeds and on the refinements of the world it runs in.
- (C2) _Projections._ Each output (the result, and each borrowed place's final content) is its own sealed program, and its final read copies. A `Unit`-typed output is `()`.
- (C3) _Holes are parameters._ A returned borrow's final content is a parameter of every fill, because at the generic call it is not decided which borrowed place the returned borrow points into. A fill's run never inspects its hole: an inert loan is stuck at a match and passes through reads and writes unchanged. Filling it is substitution, which then re-runs the fills.
- (C4) _Re-run exactly when an input changes, everywhere._ A sealed program is re-run when a value it embeds is substituted (a refinement, or the fill of a loan) or a neutral its run derives is refined, at every position a sealed program can occupy: the environment, stored types, the types of abstract values, the goal.
- (C5) _No re-closing._ On a re-run the head call is not closed off again, so a sealed program makes progress or stays exactly as it is.
- (C6) _One text, one value._ Within a world, a sealed program's text determines its value (by (C1) and determinism), so two derivations of one text may be identified.
- (C7) _Errors surface._ A re-run that fails is a type error where it was triggered; exhaustion is undecided.
- (C8) _Clean inputs._ Every input is loan-free and whole when the text is made.
- (C9) _Blocks are calls._ A stuck match or `J` is closed off as a call of an anonymous function of its captures, so (C1)–(C8) apply with the captures as arguments.

_Enforced:_ one function makes sealed programs and one re-runs them; substitution and re-normalisation share one traversal of every value position of the state (`mapState`), which closed a gap in (C4) where re-normalisation had skipped the types of abstract values.

== Worlds <sec-worlds>

Checking a match on an unknown σ of an inductive $ty("D")(overline(a))$ is elimination of a disjoint union: σ denotes an element of $deno(ty("D")(overline(a)))$, which is the union of its constructors' field tuples, and each arm is one summand.

- (X1) _Worlds are exclusive._ No fact established while checking arm $i$ that depends on σ being $ty("C")_i$ is visible while checking arm $j$: a refinement, a type refined by it, a generalisation record, a captured value.
- (X2) _Refinement is total substitution._ Entering a world substitutes σ everywhere it can occur (environment, stored types, types of abstract values, goal, values embedded in sealed programs and closures) and re-normalises. A component skipped keeps a stale, pre-refinement value in a refined world.
- (X3) _Records are scoped._ A generalisation record $n := sigma$ is in force in the world that made it and its sub-worlds (private copies, nested splits), nowhere else: the same text $n$ can denote values of different types in different arms, since it may mention the scrutinee.
- (X4) _The block is checked unrefined._ What follows the match is checked once with σ unknown; its sealed programs resolve when a later split learns σ.

What a world may keep is exactly what holds in every world: fresh-name counters (a counter states no fact) and the types of abstract values created inside the arm (nothing kept names them, since the arm's records are dropped with it). An η-refinement of an abstract value of a one-constructor type is _not_ among them. Its constructor follows from the type alone, but its fields are fresh abstract values whose types are read off σ's type in the arm's world, and can mention what the arm refined: a value parameter, or an earlier field of a dependent constructor. Kept, a sibling arm reused fields typed in another world, a closed proof of `False` (EtaBoom, @sec-risks). So an η-refinement, like a generalisation record, lives until the arm that made it ends, and survives the private copies made within it. _Enforced:_ every arm of every split runs inside one combinator (`inWorld`), whose exit restores every component of the state except those listed, so a new component is restored by default.

== Wholeness <sec-whole>

A dependent constructor $ty("C")(g_1 : A_1, dots, g_k : A_k)$, with $A_j$ mentioning earlier fields, denotes a _Σ-type_: the set of tuples whose later components lie in sets determined by the earlier ones. A borrow of a field, as in Aeneas (the Rust verification tool whose borrow model Ochr's machine follows), receives back when it ends any value of its type.

- (W1) _Open only while the opener runs._ A value may break its telescope only while the code that opened it runs. Wherever it passes to code that relies on its type, it must be whole: read, moved, copied or borrowed whole; captured by a closure, Π-type or block; observed by `Id`; at the end of a borrow of it (a borrow parameter's at its function's return); as a result.
- (W2) _Producer obligation._ The generic path treats every neutral of a dependent type as whole: [Repack] does not look inside it, and [Split] splits it by its telescope. So whatever produces such a neutral must have checked whole the value it stands for. A parameter's σ: the caller passed it whole. A field of a refined neutral: whole because the neutral is. A generalised sealed program: inherited. A stuck call's result or fill: the callee's body checked at its return. A fill with a hole: the same, with the lent part unknown. A stuck block or closed-off `J`: each arm, or the transported term, checked at its end. A hole `?`: an axiom, excluded.
- [Return] is the common form: where a checked body returns, its result and every place it holds by borrow must be whole; a part still lent there is any value of its borrow's type.

_Enforced:_ one function forms every block, taking its arms as computations and running them itself, and calls the same return check that function bodies use; so no block can be formed without the check.

== Erasure and captures <sec-erasure-principles>

- (E1) _Discard._ Every erased term runs on a private copy of the state it would start in, and the copy is thrown away.
- (E2) _Decided by declaration._ Whether a term is erased is read from syntax and declared types. Since sorts are syntactic, "is a proof" is a property of the term itself, so a re-run of a sealed program erases exactly what the direct arm erases.
- (E3) _Only copy-independent facts survive a copy:_ name counters, the types of names created in it, generalisation records (keyed by closed program texts, which mean the same in any state), η-refinements (the fields' types are the copy's world's, which the copy shares), checked recursion obligations, caches.
- (E4) _In place means within the statement's copy._ A borrow-typed argument of a statement runs in place, not on its own copy, but the statement call is itself erased.
- (E5) _Reads move inside statements as at runtime,_ on the copy only: a side that reads $x$ and then observes $x$ sees `⊥`, and its equation is stuck.
- (K1) _Captures over-approximate._ For each outer place and each arm, a block's capture mode is at least the arm's effect on it, in the order none ⊑ copy ⊑ write or borrow ⊑ move, measured at the granularity of the place moved and net of the arm's own refills; a closure or Π-type in an arm moves what it mentions.
- (K2) _Over-approximation is safe._ A stricter generic call only removes options for the code after the block: a read of a place the block moved is an error, and an equation over it is stuck.
- (K3) _Effects are measured where they happen:_ a move inside a nested block is that block's, and a move inside a statement is discarded with its copy. By (E2) a block's re-run decides as the direct arm does.

_Enforced:_ statement positions run through one combinator (`inStatement`) and the checker's scaffolding through another (`privately`); captures are computed by one function (`blockCaptures`).

== Recursion <sec-rec>

A definition $kw("fix") f (overline(x) : overline(A)) : B kw("by") x_j := b$ denotes the function defined by well-founded recursion on the size of the entry value of $x_j$.
- (R1) _The measure is the entry value, as refined._ Each recursive call's argument (its content, through a borrow) is compared with the caller's entry value as refined so far, whatever the body did to the place since. Strict subterm implies smaller size. Refinement only adds constructors, so a strict subterm at the generic call is one at every instance.
- (R2) _Recursive calls are named._ $f$ is reached only through the name it binds for itself, or a nested function's capture of that name; which calls recurse is a fact about syntax, never decided by comparing function values, which refinement changes.
- (R3) _Check before running._
- (R4) _One order._ A definition sees only earlier definitions and itself, so every chain of calls is ordered lexicographically by (definition, entry size). A call through a function value is not a recursive call unless its head is the name; a closure formed in $f$'s body that calls $f$ is checked against $f$'s entry value where it is formed.
- (R5) _Types recurse like terms_, and a statement never mentions the definition being checked.
- (R6) _Runs only unfold._ Untyped runs unfold definitions without the check; they decide nothing about well-foundedness, and a run that does not terminate is exhaustion, never a decision.

_Enforced:_ one function decides whether a call belongs to a recursion entry, by a mark on the binding (`recFrameOf`).

== Observation <sec-obs-principles>

- (O1) _Independence._ The two sides of `Id` run from the same state on independent copies, in the same world.
- (O2) _Resolved, not represented._ Observations compare resolved values, so where a borrow sits does not matter; owners are observed, not borrows. This is sound for `Id`'s meaning (@target), but false under substitution (@target-adeq): a borrow variable that a side reassigns points elsewhere afterwards, and a continuation can write through it (`RePoint`, @sec-adeq).
- (O3) _Footprint sufficiency._ A position whose resolved content cannot differ between the sides need not be observed. It can differ only if a side writes it, directly or through a borrow, so the owners of every place written or borrowed, and of every borrow variable handed on whole, are observed; a place only read is not (a read that moves leaves `⊥`, which must be refilled before the borrow over it ends, and refilling is a write). Sufficient for `Id`'s meaning; for @target-adeq the footprint must also cover what a continuation can observe: where an assigned borrow variable points, and, until D84, places moved by one side only (@sec-adeq).
- (O4) _All owners._ A loan can sit in several owned positions (a hole in several fills); each is observed.
- (O5) _One order._ The conjunction is ordered by syntax, the same on both paths, since `∧` is not commutative by conversion.

*Footprints at two paths.* A footprint's roots are read off syntax, so they are the same on both paths; only the owners can differ. At the generic call a borrow parameter's loan sits in one fresh cell; at an instance it may sit in several owners (O4). Every extra owner's resolved content is a function of what was written through the borrow plus parts no side writes, so if the generic statement proves the written values equal, each extra owner's equation is true too. In the present route that is footprint coverage, with the injectivity of contexts.

= Tests before mechanisation <sec-tests>

The route is checked on paper before anything is mechanised, hardest first, following the standing preference to attack first the part most likely to fail. Four tests were planned: tests 0 and 1 independent of each other, the census audit cheap, and test 2 after test 0. Each result is summarised here; the full write-ups are the documents named. All four have passed. The one failure they found is a fifth closed proof of `False`, conversion over `⊥` (@sec-risks), since fixed on main by D83. A fifth test, test 3, checks type safety (@target-safe).

== Test 0: the model exists, on a slice <sec-test-model>

*What it checks.* That the set model, stratified by universe, can be defined without circularity (Q9) on a slice containing each feature that makes the definition hard: `Nat`; a type function defined by recursion on data (`Cells(E, n)`); a type variable $A : ty("Type")_0$ with $R$ at it; a function type returning a borrow, with injective backward functions; and a Π into `Prop` over `Type₀`.

*What would fail it.* A clause with nothing smaller to recurse on, or a meaning that is not a set. Then both routes fail, since both rest on the model.

*Result: the model exists on the slice* (`ochr/docs/24`, 6 November 2026, by the session that proposed the route; a paper result, most of it also encoded in Lean in `ochr/core/lean/Ochr/Model/Slice.lean`, which builds with no `sorry` and uses only the axioms `propext` and `Quot.sound`). Neither of Q9's circularities is an obstacle; both came from how the model was first phrased.
- _A type means only its good elements._ If a function type returning a borrow means only the functions whose backward functions are injective, then $R$ at every type is the meaning itself, and the meaning and $R$ are one definition. A type variable means whatever set the assignment gives it, and $R$ at it is that whole set: an Ochr program can use a value of a type variable as a function only after transporting along a proof that the variable _is_ some Π-type, whose meaning is already a good set. Pairing each type with a separate set of good elements, as Q9 proposed, is not just unneeded but harmful: the Lean encoding found two functions that agree on every good argument yet differ at a junk one, so with pairs two convertible functions would have different meanings and [Conv-fun] would be unsound. With carriers holding only good elements, [Conv-fun] is function extensionality, proved in Lean.
- _Meanings are defined on terms, not on type values._ The recursion is on the position of the item in the program, then the structure of the term, then, inside a recursive function, the rank of its decreasing argument; all three are well founded. A Π-type's codomain _term_ is a subterm of the Π-term even though the Π-type value computes the codomain by running code; a computed type $F(a)$ means the meaning of an earlier item at the meaning of $a$; a type variable is looked up, not recursed into. $ty("Type")_i$ means $V_(kappa_i)$ outright, so there is no universe of codes and no induction–recursion; universe levels matter only for sizes (that a type at level $i$ means a member of $V_(kappa_i)$), which is part of membership, not of the definition. The Lean encoding needs its levels bounded (Q8).
- _A recursive function means a function whether or not it passed [Rec]._ Its meaning is defined by _guarded_ recursion: a recursive call whose decreasing argument does not drop in rank means the error value. So [Rec] is not needed for the definition; it is what makes the guard never fire, which is part of membership, (b). The defining equation under that hypothesis is proved in Lean for type functions recursive on `Nat`. This moves [Rec] from well-formedness to membership throughout this document (@thm-mp, @sec-wf, test 1).

*What it leaves.* The meaning of the state (live borrows as functions of their final contents, holes, inert loans, `⊥`) and therefore of `Id` inside types, which Q11 now names as the next hardest piece. Two obligations come with it: a type's meaning never depends on a hole, and every accepted closure returning a borrow has an injective backward function (now part of membership). In a typed mechanisation, meaning and membership must be built together, as the Lean encoding already does for borrow-returning functions.

== Test 1: the known proofs of `False` are failed steps <sec-test-bugs>

*What it checks.* For each closed proof of `False` the checker once accepted (@sec-risks), and for the moved-out equation the test `MovedBothSides` guards, whether a part of @thm-mp fails at the buggy step and holds once the fix is in. A bug that no part catches would mean the theorem is too weak.

*Result: all five are explained, and none escapes* (`ochr/docs/25`, 6 November 2026; a paper analysis, the buggy behaviour taken from each fix's commit).
- _A returned borrow of an index field_ (`BoomI2`). [Repack] at the function's return checked the owner whole with the lent field read at its current content. Its accepting direction owes (b) for the owner under _every_ future of the returned borrow's hole, and the caller writes another value there, at which the record's dependent field no longer fits. (b) fails; the fix, checking the lent part as an unknown of its type, restores it.
- _A stuck `J` closed off unchecked_ (`BoomJ`). The fill left in the borrowed place means exactly what running the `J` means, so (a) holds even before the fix. (b) fails for the fill: where the endpoints are equal, it means a record whose dependent field was typed at the old index. The fix, checking each arm of a block at its end, is (b) at a producer of a sealed value.
- _A recursive closure capturing a value it splits on_ (`BoomCapSplit`). The split keeps meaning: the refined closure means the same function, so (a) holds. [Rec] identified recursive calls by comparing function values, which the split changed without changing their meaning, so a recursive call went unchecked, and (b) fails: under guarded recursion (test 0) that call's decreasing argument does not drop, so the guard fires and the closure's meaning there is the error value, which lies in no type. The fix, recognising recursive calls by name, is syntax, which refinement does not change.
- _`EtaBoom`._ Leaving the arm $n := ty("Z")$ kept an η-refinement whose fields were typed in that arm. In the sibling arm the field of type `Void` forced every assignment to choose an element of $emptyset$, so the arm admitted no assignment at all and could prove anything. (a) fails in its coverage part, the case the route predicted. The fix drops the refinement with its arm.
- _`MovedBothSides`._ At the generic call a stuck block on each side of an `Id` took the same place by move, so the equation between the two `⊥` computed to `True`, though at an instance only one side moves it and the equation is false. Reading `⊥` as no information, that step is not monotone: filling in the two `⊥` differently makes the equation false. The fix keeps an equation with `⊥` on either side stuck.
Five further soundness guards found by ablating the checker fit the same way: a match on `Z`/`S` needs a `Nat` scrutinee (coverage, in (a)); a whole read repacks, a proof field assigned while part of its value is lent is checked under every future, and each arm of a block is checked at its end (all (b)); a borrow is formed only at `Type₀` ((b) for types, and (c)).

*What it shows.* Part (a) alone catches one of the five. Three are caught by (b): two quantified over the futures of the live holes, one by the guard of a recursive function (as first written, test 1 put that one under (c); test 0 moved [Rec] to membership). In all three the step's (a) holds even before the fix. So the route stands or falls with (b) as much as with (a), and must be presented, as @thm-mp is, as one induction over all three, never as "each step keeps meaning" alone. In the first draft each bug was a disagreement between two runs; here each is local to one step and one part of the theorem. The test also favours reading `⊥` as no information: the alternative, `⊥` as the moved-out value, needs the old value, which the checker's `⊥` does not record. A fifth closed proof of `False`, found after this test, fits as well, but as a failure of the monotonicity required of computing steps (@sec-wf), not of (a), (b) or (c) (@sec-risks).

== The census, under the new criterion <sec-test-census>

*What it checks.* Every decision the checker makes, as listed by the two-paths census (`ochr/core/notes/two-paths-census.md`), with every edge case found by ablating the checker and every remaining site that reads a value's own type (`valType?`), sorted into the kinds of @sec-wf: same, aligned, less informative, or check.

*Result: everything sorts, apart from one item* (`ochr/docs/26`, 6 November 2026; read-only, on main with D80 and D81). The audit raised two; a probe has since settled the first.
- _`⊥` must mean no information._ A stuck block takes a place by move when some arm moves it, even if another arm writes it, so `⊥` read as the moved-out value would contradict that arm. Read as no information, block captures, moves and splits are less informative, and the computing steps the audit examined are monotone over `⊥` (an equation over `⊥` stays stuck; reading `⊥` is an error; an observed owner holding `⊥` gives a stuck equation). This settles Q10. The audit counted conversion as a check that only rejects, but its accepting direction must be monotone too: after the audit, identifying two values that hold `⊥` turned out to be a fifth closed proof of `False` (@sec-risks).
- _Same:_ the η family, a proof's `⋆`, `Eq` and `J` computing, splits and records, the fill of a lent `Unit`. _Aligned:_ erasure, a function type's class, a statement argument's place, [Close]'s row, all read from syntax since D77 and D80. _Less informative:_ copy or move, and a block's captures. _Checks:_ the rest, each establishing (b), establishing (c), or protecting only runtime safety (the requirement that borrows passed to a call that closes off be whole). The audit also put "a returned borrow must be whole" here; test 2 corrected that: it is membership.
- _The "same" kind rests on five lemmas, not one per site:_ membership; the soundness of `valType?`; footprint coverage; conversion soundness, which must be monotone over `⊥` ([Conv-bot], (V10)); and well-formedness (@sec-wf).
- _Item 1, settled by a probe: a simplification of the proof, not a gap._ When a value is checked whole while part of it is lent, the rule checks the lent part as an unknown of the borrow's _declared_ type, since the borrow may still write anything of that type there. The checker instead uses the type read off the lent part's current content (`lentUnknown`). The audit worried about the case where that type cannot be read. A probe found that this case rejects rather than accepts: the loan stays in the value, and [Repack]'s check reads the same unreadable type and reports that the part is not of its type. The case is also effectively unreachable, since a lent index field is first-order data, whose content's type can always be read (a constructor value records its parameters, an unknown has a stored type, a sealed program has its head's codomain); four attacks and an attempted closed proof of `False` were all rejected by [Repack]. Reading the borrow's declared type, as the rule says, would change no verdict. It would only remove this check's dependence on the soundness of `valType?`, one of the five lemmas behind "same".
- _Item 2, open: the class of an embedded call head._ When a call's head is a value with no written type, such as a sealed function value, its class is read off the value's Π-type. That agrees with the declared position only because Π-types of different class are not convertible (D54), and no test exercises that check. The fix: a witness test, or carrying the class with the value, as D80 does for captures.
- _Untested invariant checks:_ that a closure in a block arm captures nothing the block borrows, in the copy-type case, and that a recursive function occurs in its body only as a call's head. Each needs a test that it rejects something.

== Test 2: a higher-order slice <sec-test-ho>

*What it checks.* The route on a slice with the features that the first-order fragment F leaves out (F is the part of the calculus for which the Ochr paper proves soundness: no closures, no function parameters, no type families): function parameters ranging over every set function, a closure built in a run and called later, [Conv-fun] (functions compared by their generic observations), and a function taking a function that returns a borrow. It asks whether the first draft's hard points (`Pick`'s early end, early ends with pairs after a [Drop], and resolution commuting with refinement through inert loans) disappear, or move into the meaning of a state, and it checks the census's reading of `⊥` on higher-order code.

*Why not F.* F is first-order: no closures, no function parameters, no type families. Redoing its proof this way is at most a warm-up, and its outcome says little about the whole calculus.

*Result: states have a meaning, and the step lemmas hold on the slice* (`ochr/docs/27`, 6 November 2026, by the session that proposed the route; a paper result, with the meaning of states checked in Lean on a toy symbolic machine in `ochr/core/lean/Ochr/Model/State.lean` and `State2.lean`, which build with no `sorry` and use only the axioms `propext` and `Quot.sound`). With it, all four planned tests have passed; the one failure this test found is a fifth closed proof of `False`, conversion over `⊥`, since fixed on main by D83.
- _A state means a function of a future._ A future gives each live borrow its final content. A place that lent its content means its final content; a place holding the borrow means its current content, which is what a read through it sees; a sealed fill means its program, with its hole read from the future; `⊥` means no information. Ending a borrow fixes the future at the holder's current content and forgets the holder, so it loses only information, and that is what the checker's [End] does by substitution. The Lean check found this shape necessary: a single function from final contents to resolved contents cannot express a read through a borrow.
- _`Id`'s meaning._ Each observation ends every live borrow of its copy, so it depends on the assignment alone, and `Id` compares the results and every position neither side moves. The checker's conjunction over the footprint's owners is then exact, given footprint coverage.
- _Both obligations test 0 left hold, with no new rule._ No stored type holds a live loan: types are formed on private copies after [Access] has ended the loans in what they read, and the one type computed over a lent field, an open dependent value's, quantifies over the hole, as D64 amended and D73 require. Every accepted function returning a borrow has an injective backward function, by an invariant that every hole is placed injectively in the state. [Access], D67 (an assignment ends the loans it overwrites), D65 (a borrow of a dying local cannot escape) and (C8) (arguments hole-free at [Close]) keep it, and every called function is good because types mean only good elements.
- _The first draft's three hard points disappear._ `Pick`'s early end becomes a definition (a fill is a function of its hole) and an end that loses only information. Early ends with pairs after a [Drop] (Q4) become an end, which is below whatever the shape of the ended borrow's content, since reborrows travel with it and are read from the same future. And resolution commuting with refinement through inert loans becomes meaning preservation for a fill's re-run, with the hole as one more unknown.
- _Monotonicity._ `Eq`, `J`, matches and [Close]'s rows are monotone over `⊥`. Conversion was not: its identity test identified two values that hold `⊥`, which is the fifth closed proof of `False` (@sec-risks). The fix, [Conv-bot] with its counterpart for [Rewrite], is on main since D83, and changed no existing verdict.
- _The form of the main theorem._ The checker's run is below a _reference run_ of the term on meanings (@def-refrun): the denotation as a state transformer, which applies the meanings of functions at calls instead of running their bodies, so it is not a second machine run. Each step is exact, an end the reference does not make, or an over-approximation. @thm-mp states it this way.
- _The higher-order slice._ A function parameter means any good function, non-computable ones included, and a call through it closes off exactly. A closure built in a run is fixed when it is formed, since its captures hold no loan, and a later call applies its meaning. [Conv-fun] is sound by function extensionality on good functions. A function taking a function that returns a borrow, `UseG (g : Π(x : &Nat). &Nat) (a : Nat) : Nat := (let r = g(&a); *r := 5; clone(a))`, means $(G, n) |-> "back"_G (n)(5)$, so two different writes give two different results, by injectivity.
- _In Lean._ [Access] is derived the checker's way; ending one borrow reaches every reborrow, and shallow ends are sound, so Q4 dissolves; nested holes hold; and [Drop] loses only information. (WF5), loan-free arguments at a call, turns out to be about causality: with a live loan in an argument, a read now would depend on a write made later, so the meaning of a state needs it, not only runtime safety. Lean's own gaps: the step lemmas at field paths are checked only on the runs it encodes, and the preservation of (WF2) is assumed.
- _A correction to the census._ "A returned borrow must be whole" is membership, not only runtime safety: a returned borrow holding `⊥` has a forward value with no meaning. The requirement that borrows passed to a call that closes off be whole stays on the runtime side.

*What it leaves.* The lemmas this test assumed or argued without checking: footprint coverage; the soundness of `valType?`; the preservation of well-formedness, where (WF2) needs (WF3); [Open] and [Repack] beyond the lent-index case; and erased runs inside the reference run. These are the residuals of @sec-order.

== Test 3: type safety on the higher-order slice <sec-test-safety>

*What it checks.* @target-safe on test 2's higher-order slice: error reflection, runtime `J`, erasure and termination, for closed runs of accepted data functions.

*What would fail it.* A closed run of an accepted function that goes wrong where the reference run does not, or whose result differs from the reference run's.

*Result.* Pending (the session that proposed the route; `ochr/docs/29-type-safety-slice.typ` and `Ochr/Model/Safety.lean`). It is stated against D84's drop-at-the-join semantics, which is not yet merged.

== Audit: what a context can observe <sec-test-adeq>

*What it checks.* For @target-adeq: every channel through which a context can observe a term (its result, the places it writes or moves, where a borrow it assigns points, and any other), compared with `Id`'s footprint, on main and under D84.

*What would fail it.* A channel `Id` does not observe, as `RePoint` is for where a borrow points.

*Result.* Pending (the session that proposed the route; lane `id-audit`, `ochr/docs/30-id-adequacy-audit.md`).

= The lemmas and their status <sec-route-dag>

@fig-route-dag draws what the present route's lemmas depend on, and @fig-route-status lists their statuses. The superseded route's own lemma graph is preserved with it (@sec-old).

#figure(
  kind: image,
  supplement: [Figure],
  placement: none,
  diagram(
    spacing: (6pt, 20pt),
    edge-stroke: 0.6pt + ink,
    dn((2.6, 0), [Consistency (@cor-cons-route)], st-red, <r-cons>),
    dn((0.5, 0), [Id adequacy (@target-adeq)], st-open, <r-adeq>),
    dn((0.5, 1), [Context lemma (@sec-adeq)], st-open, <r-ctx>),
    dn((4.5, 0), [Type safety (@target-safe)], st-red, <r-safe>),
    dn((4.7, 1), [Safety lemmas (@sec-safety)], st-open, <r-pieces>),
    dn((2.6, 1), [Definitions mean elements (@cor-mean)], st-red, <r-mean>),
    dn((0.6, 2), [Model (@lem-model)], st-paper, <r-model>),
    dn((2.6, 2), [Meaning preservation, membership, well-formedness (@thm-mp)], st-open, <r-mp>),
    dn((4.7, 2), [Conversion (@lem-conv)], st-paper, <r-conv>),
    dn((0.2, 3), [Q9: settled on a slice], st-paper, <r-q9>),
    dn((1.5, 3), [Meaning of states, reference run], st-paper, <r-code>),
    dn((2.8, 3), [Monotone computing steps], st-paper, <r-mono>),
    dn((4.1, 3), [Census: one item], st-open, <r-census>),
    dn((5.3, 3), [valType? sound], st-open, <r-vt>),
    dn((0.9, 4), [Principles (@sec-principles)], st-paper, <r-princ>),
    dn((2.3, 4), [Frame property], st-heap, <r-frame>),
    dn((3.7, 4), [Footprint coverage (assumed)], st-open, <r-call>),
    dn((2.6, 5), [[Open], [Repack] beyond the lent index; erased runs], st-open, <r-res>),
    dn((5.1, 4), [(WF1)–(WF7) preserved], st-open, <r-wf>),
    edge(<r-mean>, <r-cons>, "-|>"),
    edge(<r-ctx>, <r-adeq>, "-|>"),
    edge(<r-mp>, <r-adeq>, "-|>"),
    edge(<r-mp>, <r-safe>, "-|>"),
    edge(<r-pieces>, <r-safe>, "-|>"),
    edge(<r-model>, <r-cons>, "-|>"),
    edge(<r-mp>, <r-mean>, "-|>"),
    edge(<r-conv>, <r-mean>, "-|>"),
    edge(<r-conv>, <r-mp>, "<|-|>"),
    edge(<r-model>, <r-mp>, "-|>"),
    edge(<r-q9>, <r-model>, "-|>"),
    edge(<r-code>, <r-model>, "-|>"),
    edge(<r-code>, <r-mp>, "-|>"),
    edge(<r-mono>, <r-mp>, "-|>"),
    edge(<r-census>, <r-mp>, "-|>"),
    edge(<r-vt>, <r-mp>, "-|>"),
    edge(<r-princ>, <r-mp>, "-|>"),
    edge(<r-frame>, <r-mp>, "-|>"),
    edge(<r-call>, <r-mp>, "-|>"),
    edge(<r-wf>, <r-mp>, "-|>"),
    edge(<r-res>, <r-mp>, "-|>"),
  ),
  caption: [The present route's lemmas and their dependencies; an arrow points from a lemma to one that uses it, and the double arrow marks the induction conversion soundness shares with the main theorem. Colours: #swatch(st-heap, [proved on the heap slice]), #swatch(st-red, [reduced]), #swatch(st-paper, [paper argument]), #swatch(st-open, [open]), #swatch(st-design, [open design question]).],
) <fig-route-dag>

#figure(
  kind: image,
  supplement: [Figure],
  placement: none,
  block(breakable: true, {
    set text(size: 8.3pt)
    set par(justify: false)
    table(
      columns: (30%, 22%, 48%),
      stroke: none,
      inset: (x: 4pt, y: 2.5pt),
      align: (left, left, left),
      table.hline(stroke: 0.5pt + ink),
      [*Lemma*], [*Status*], [*Depends on; notes*],
      table.hline(stroke: 0.4pt + ink),
      [Consistency (@cor-cons-route)], [#s-red[@cor-mean, the model]], [Lean statement `Ochr.Consistency.consistency` (`sorry`)],
      [Definitions mean elements (@cor-mean)], [#s-red[@thm-mp, @lem-conv]], [],
      [Meaning preservation, membership, well-formedness (@thm-mp)],
      [#s-open],
      [reference-run form; the step lemmas hold on a higher-order slice (test 2), much of it in Lean; test 1 found every fixed proof of `False` to be a step where one part fails; residuals in @sec-order],
      [Model (@lem-model)], [#s-paper; most of a slice in Lean], [conditions (I1)–(I9), all enforced by the checker; Q9 settled on a slice by test 0; `Ochr/Model/Slice.lean`, no `sorry`],
      [Meaning of a state, reference run (@def-state-meaning, @def-refrun)], [#s-paper; a toy machine in Lean], [futures (test 2); `Ochr/Model/State.lean`, `State2.lean`, no `sorry`; `⊥` as no information (Q10)],
      [Types hole-free; backward functions injective], [#s-paper], [test 2; from [Access], D64, D65, D67, D73 and (C8)],
      [[Open], [Repack] beyond the lent index], [#s-open], [covered by test 2 only for a lent index field],
      [Erased runs in the reference run], [#s-paper], [argued in test 2, not checked],
      [Conversion sound (@lem-conv)], [#s-paper], [(V1)–(V8) and (V10), re-argued under assignments; shares @thm-mp's induction; (V10) is [Conv-bot], on main since D83; known incompleteness `SelfBot`],
      [Monotone computing steps], [#s-paper], [`Eq`, `J`, matches and [Close]'s rows are monotone over `⊥` (test 2); conversion and [Rewrite]'s occurrence search since D83 ([Conv-bot]), which closed the fifth proof of `False`],
      [Decisions sorted (census)], [#s-open], [one item, an embedded call head's class; reading the lent-part check's type from the borrow's declaration would only simplify the proof],
      [`valType?` sound], [#s-open], [one lemma about one function; D82 (on main) removed its uses at bindings],
      [Footprint coverage], [#s-open], [assumed by test 2; the extra owners at a call site by the injectivity of contexts and (O4)],
      [Frame property], [#s-heap; #s-red[(L1)–(L7)] on checker], [a lemma both targets use, not a target: a call's meaning changes only its result and borrowed places; `Ochr.Heap.frame`, `call_effect` (heap slice, history)],
      [Type safety (@target-safe)], [#s-red[the reference run; (a)–(e) of @sec-safety]], [test 3 pending],
      [`Id` adequacy (@target-adeq)], [#s-red[@thm-mp, @target-safe, the context lemma]], [a draft statement; neither other target implies it],
      [Context lemma], [#s-open], [what a context can observe of a term is what `Id` compares; the audit of @sec-test-adeq pending; known gaps: moves (D84, not merged) and `RePoint` (observe assigned borrow variables)],
      [Error reflection], [#s-open], [the machine errs only where the reference run errs],
      [Runtime `J`], [#s-design], [Q3: at runtime `J` returns its transported term],
      [Erasure], [#s-open], [the first draft proved it for its first-order fragment only],
      [Termination], [#s-red[@thm-mp (b)]], [the guard never fires; Ochr stays total],
      [Well-formedness, (WF1)–(WF7)], [#s-open], [(WF2) needs (WF3), assumed by test 2 and in Lean; (WF5) is about causality; two of its checks have no test],
      table.hline(stroke: 0.5pt + ink),
    )
  }),
  caption: [Status of every lemma the present route uses.],
) <fig-route-status>

= The order of work <sec-order>

+ *The residual lemmas*, which test 2 assumed or argued without checking: footprint coverage; the soundness of `valType?` (D82, on main, removed its uses at bindings); the preservation of well-formedness, where (WF2) needs (WF3); [Open] and [Repack] beyond the lent-index case; and erased runs inside the reference run.
+ *The census's open item*: a witness test for the class check on Π-types, and a rule change if it fails; tests for the two invariant checks that have none. Optionally, the lent-part check can read the borrow's declared type, which changes no verdict and removes one use of `valType?`.
+ *Type safety*: test 3 (@sec-test-safety); error reflection; the runtime rule for `J` (Q3); erasure beyond the first-order fragment; termination from guarded recursion; and well-formedness at runtime, shared with consistency (@sec-safety).
+ *`Id` adequacy*: the audit of what a context can observe (@sec-test-adeq); the context lemma; observing each assigned borrow variable by writing a fresh $sigma_w$ through it, which closes `RePoint`; and D84 for moves (@sec-adeq).
+ *The model and the meaning of states, on paper, for the whole calculus*: what the slices covered only on paper or not at all (user inductives and dependent constructors in Lean, inductives declared `abstract` or `implemented by`, `split f in t`, `rewrite`, records), with conversion soundness (@lem-model, @def-state-meaning, @def-refrun, @lem-conv).
+ *The step lemmas, on paper*, one per checker rule, against the reference run, each stating which of (a), (b) and (c) the step must keep and which it establishes, with the five lemmas behind "same" (@sec-wf). Large but routine; the standing preference is that size costs nothing and risk is what counts.
+ *The Lean statements* of the three targets (Q8 for consistency), and mechanisation, with meaning and membership built together, as both Lean encodings already do.

*Abandoned: the heap port.* The first draft proposed porting the checker's value layer to a heap design, to make (P) cheaper to prove. (P) is off the present route's path, so the port is abandoned, and its branches (`heap-close`, `port-step1`) are not to be merged; the heap slice's proved results remain as history where they are cited, for the frame property.

*Not needed for consistency.* Two checker changes made for the first draft's sake: reading copy-or-move and η at `Unit` from declared types (D80) and giving every binding its declared type (D82), both on main. They still simplify the checker, and D82 removed the uses of `valType?` at bindings.

= Where the plan could fail <sec-risks>

The risks below are places where a lemma might be _false_, not merely unproved.

*`Id` adequacy needs rule changes* (@sec-adeq). `RePoint` shows that `Id`'s footprint misses where an assigned borrow variable points, moves by one side need D84, and the audit of @sec-test-adeq may find further channels. These are gaps in substitution, not proofs of `False`.

*Type safety's missing pieces may fail* (@sec-safety). Error reflection may have exceptions where the machine's representation goes wrong but the meaning does not; runtime `J` needs a rule change (Q3); and erasure is proved only for a first-order fragment. Test 3 is stated against D84's drop-at-the-join semantics, which is not merged.

*The residual lemmas may be false.* Test 2 assumed footprint coverage, the soundness of `valType?` and the preservation of well-formedness, and covered [Open] and [Repack] only for a lent index field and erased runs only by argument (@sec-test-ho). Each is a place a lemma could fail; [Repack] is where one of the October proofs of `False` was. On the slices, the model (test 0) and the meaning of states (test 2) held.

*A decision's class may come from a value* (the census's second item). The class of an embedded call head is read off its Π-type, and agrees with the declared position only through a check on Π-types that no test exercises.

*The well-formedness invariant may not be preserved.* The first draft's question about early ends with pairs (Q4) reappears here: an early end of a borrow must not leave a reborrow alive and readable. Two of the invariant's checks have no test.

*Statements that turned out false as first written.* Mechanising the decision half of the first draft's stability lemma corrected four statements, none of them a checker bug:
- the class and [Close] row of a function type commute with refinement only for Π-type values and only from the generic to the instance (an unknown $A : ty("Type")$ refined to a Π-type reads no class generically);
- the [Close] row of a stuck block does not commute (an unknown match type refined to `Unit` flips it from data to `Unit`, harmlessly);
- footprint containment fails for a refinement that makes an unknown type a borrow type (excluded by requiring borrow-free refinements, which is what refinements are);
- declared readings survive refinement only at states of checked programs (a sealed call of an unchecked global can re-run to a type).
Each says that stability holds for states that checked programs reach, not for arbitrary states. The present route does not use stability; membership, proved inside the induction, plays the part of the typing invariant those corrections called for (Q7).

*Closed proofs of `False` found while the principles were being derived.* On the checker of October 2026, three accepted programs proved `False`; a referee of the first draft found a fourth on 2 November; and a fifth was found on 6 November, while test 2 was being written. All five are fixed and are now rejected tests:
- writing through a returned borrow of an index field, so that a value's length and its dependent field disagreed while the generic path trusted the value as whole (fixed: a part still lent at a whole-again point is an unknown of its type);
- a stuck `J` closed off without checking its borrowed places at the end of its transported term (fixed: a `J` block is checked at its return, like any block);
- a recursive local function capturing a value it splits on: the split rewrote the capture, the recursion check identified calls by comparing function values, and missed them (fixed: recursive calls are recognised by name);
- `EtaBoom` (@sec-referees): leaving a split arm kept the η-refinement of a one-constructor unknown, whose fields' types had been read in the arm's world, so a sibling arm reused a field typed `Void` where a `Nat` was due (fixed: an η-refinement, like a generalisation record, lives until the arm that made it ends);
- `Same` (6 November): at an unknown `n`, each side of an `Id` is a stuck block `match n { Z => (let y = x; ()), S _ => (x := c; ()) }`, which takes `x` by move because its `Z` arm moves it; every observation then leaves `x` as `⊥`, so a hypothesis (with `c = 5` on both sides) and a goal (with `5` and `6`) both compute to the stuck `Eq(Nat, ⊥, ⊥)`, and conversion's identity test identified them; at $n = 1$ they are $5 = 5$ and $5 = 6$. The fix's own audit found two more routes to `False` through the same identification, so this is one bug with three routes, all identifying values that have lost information: conversion's identity test (`Same`); `trans`, which composed $5 = $ `⊥` and `⊥` $= 6$ into $5 = 6$ because conversion at the middle point treated the two `⊥` as equal (`TrBotBoom`); and `rewrite`, whose occurrence search uses equality of representations, so `rewrite ← h` with `h : Eq(Nat, ⊥, 5)` put `5` in place of another observation's `⊥` (`RwBotBoom`), a separate code path from conversion. Fixed on main by D83 (`98e711ed`): [Conv-bot], a value containing `⊥` is convertible with nothing, itself included, and [Rewrite] finds no occurrence of a value holding `⊥`.
Test 1 (@sec-test-bugs) found each to be a step at which one part of @thm-mp fails: (b) for the first three (the third through the guard of a recursive function), (a) for the fourth. The fifth, found after test 1, fits none of the three parts: it is a failure of the monotonicity @thm-mp requires of every step that computes on a state (@sec-wf), by three routes that each identify two values holding `⊥`, which may stand for different values. Since [Rewrite]'s occurrence search is a separate code path from conversion, monotonicity has to cover both. The principles of @sec-principles name the obligations and single points in the checker enforce them, and probes of five further areas found nothing; but a list of principles can be incomplete, which is what the plan exists to rule out. Independent evidence: a route that translates each accepted program into Lean and has Lean's kernel check it refused, for the second and third programs, the certificates that a checker still accepting them produced, each for the actual reason the program was wrong.

*Incompletenesses are not risks, but they shape the theorem.* Several true programs are rejected because the generic call is stricter than an instance: two copies of a function that inspects its argument are not convertible; a match on a generalised call is not convertible with the call; a block's capture over-approximation rejects a closure inside a statement inside an arm, and a block that takes a place by `&` because an erased term assigns it; changing an index while a dependent field is lent is rejected even when the field's type is the same at every index; large elimination from a Forded proposition is refused at an index where only one constructor is possible; an impossible arm is refused at an unknown index; and, since D83, a type holding `⊥` is not convertible with itself (`SelfBot`). Each confirms that some steps over-approximate, so @thm-mp must allow a less informative result (@def-lessinfo), not only an equal one.

*Universes in Lean* (Q8). The uniform Lean statement may be unprovable in Lean.

*Rules and checker.* The Lean statement is about the checker; its correspondence with the rules is tested, not proved. A proof against the checker makes this moot; a paper proof about the rules does not.

The risks specific to the superseded route (equality only up to resolution, runs stuck at `J` at concrete instances, impredicative quantification over function values) are recorded with it, and in the re-triaged questions (@sec-oq).

= Open design questions, re-triaged <sec-oq>

The first draft raised Q1–Q9. On 6 November 2026 they were re-triaged for the present route: each says whether it goes away, moves into the meaning of a state (@def-state-meaning), changes form, or is unchanged. Q10 and Q11 are new, and Q10 is already settled.

#oq(
  1,
  [good ground values],
)[_Goes away._ Unknowns range over every element of their types (@def-assign), function parameters over good functions, and nothing needs to terminate.]
#oq(
  2,
  [agreement after a block],
)[_Goes away_ (test 2). A stuck block's capture by move forgets a place, a step below the reference run (@def-lessinfo); there is no second state to disagree with. What it needs is the monotonicity of computing steps (@sec-wf): `Eq`, `J`, matches and [Close]'s rows are monotone over `⊥`, and so, since D83, are conversion and [Rewrite]'s occurrence search, (V10).]
#oq(
  3,
  [stuck equations and `J`],
)[_Gone for consistency; open for type safety._ Truth is semantic, so nothing counts a stuck equation as true by fiat, and a stuck `J` means transport, the identity at endpoints with equal meanings, which membership of the equation's proof guarantees. For type safety (@target-safe) a closed run must not stop at `J`, yet a hypothesis can be true while its endpoints are not convertible (two closures with equal meanings and different code). The likely fix: at runtime `J` returns its transported term, erasing the cast, while the checker keeps its rule.]
#oq(
  4,
  [early ends with pairs],
)[_Goes away_ (test 2). An early end, at [Access] or [Drop], is an end on meanings, below whatever the shape of the ended borrow's content: a reborrow in the content, or in either component of a pair, travels with it into the lender and is read from the same future. The Lean encoding checks that ending one borrow reaches every reborrow and that shallow ends are sound. The only requirement left is the checker's own: it does not use a borrow it has ended.]
#oq(
  5,
  [dependent values in the relation],
)[_Partly settled._ An open value means the raw tuple of its fields (@def-state-meaning), and [Repack] restores membership under every future of the holes still lent from it; the question of how two paths type an open field disappears with the second path. Test 2 settled the lent-index point: the one type computed over a lent field quantifies over the hole (D64 amended, D73), so no stored type depends on a hole. The census's doubt about the lent-part check was settled by a probe as a simplification. [Open] and [Repack] beyond the lent-index case remain a residual (@sec-order).]
#oq(
  6,
  [resolution with moved-out contents],
)[_Goes away._ A state's meaning is a function of its live borrows' final contents, so no resolution is needed, and `⊥` inside a live borrow means no information (Q10).]
#oq(
  7,
  [the typing invariant],
)[_Changes form, and mostly settled._ It splits into well-formedness, part (c) of @thm-mp, which is about the borrow discipline and needs no types, and membership, part (b), which is proved inside the induction rather than assumed. Test 2 settled the two parts of membership that test 0 named: no stored type depends on a hole, and every accepted function returning a borrow has an injective backward function, both with no new rule. What remains is what test 2 assumed: the preservation of well-formedness, where (WF2) needs (WF3), the soundness of `valType?`, and footprint coverage. The four corrections of @sec-risks were evidence that the first draft needed it.]
#oq(
  8,
  [universes in Lean],
)[_Unchanged in substance._ The paper model fixes one inaccessible per universe level a program uses, and test 0's Lean encoding takes the bounded option (levels 0 and 1). For the uniform statement over all programs the choices remain: one inaccessible per level for all levels at once (unprovable in Lean by Gödel if Ochr is as strong as Lean, which is unknown: Ochr has impredicative `Prop` and every $ty("Type")_i$, but no W-types, so the inaccessibles may even be unnecessary), bounded levels, a statement relative to an assumed model, or one statement per program.]
#oq(
  9,
  [a well-founded definition of the model],
)[_Settled on a slice by test 0_ (@sec-test-model). Both circularities came from how the model was first phrased. A function type means only its good functions, so $R$ at every type is the meaning, and a type variable means a set all of whose elements are good; pairing types with good subsets, the repair first proposed here, would have made [Conv-fun] unsound. Meanings are defined on terms, by recursion on program position, term structure and, inside a `fix`, the rank of the decreasing argument, and $ty("Type")_i$ means $V_(kappa_i)$ outright. What remains for the whole calculus: covering in Lean what the slice covers only on paper (user inductives beyond `Pair` and `Unit`, dependent constructors, type functions of any signature, `Eq` beyond `Nat`), a clause for inductives declared `abstract` or `implemented by`, and the state (Q11). @def-inj.]
#oq(
  10,
  [what `⊥` means],
)[_New, and settled: no information._ A moved-out place could mean the value that was moved out, making moves invisible, or no information, the least element of @def-lessinfo, making moves over-approximations. The census showed the first contradicts a stuck block that takes a place by move while another arm writes it, and test 1 that it needs the old value, which the checker's `⊥` does not record (@sec-tests). So `⊥` means no information, and every computing step must be monotone over it, which the checker's steps already are.]
#oq(
  11,
  [the meaning of code],
)[_New, and settled on the slices._ The meaning of running a term is its reference run (@def-refrun): a state transformer on meanings, with a state meaning a function of a future, defined by structural recursion inside the model's recursion on program position and decreasing argument. Test 0 gave its pure part (@sec-test-model), and test 2 the state, `Id`, and the steps of a higher-order slice, much of it in Lean (@sec-test-ho). A function's meaning is read off the reference run of its body; the frame property (a call changes only its result and its borrowed places, proved on the heap slice) is the statement that this meaning is compositional. What remains: erased runs inside the reference run, argued but not checked, and the rules test 2 covered only by citation ([Open] and [Repack] beyond the lent index, `split f in t`, `rewrite`, records).]

= The superseded route and the referee reports <sec-old>

The first draft of this plan, of 2 November 2026, proved consistency as a corollary of a soundness theorem, by walking the checker's case tree in step with a concrete run at each instance. Three referees showed that it could not be completed as written. Truth is defined in the set model, which quantifies over every set function, while the walk compared the checker's run only with runs built from machine values; the second run needed an agreement relation that held only up to resolution and renaming of fresh names; and its central lemma, that a run which never inspects an unknown behaves uniformly at every instance, was costly to prove against the current machine and false as first stated. The present route removes all three by comparing the checker's run with its meaning instead of with a second run.

The walk also targeted runtime safety at instances. The present route now targets it too, as type safety (@target-safe), through the same meanings rather than a second run (@sec-safety).

The first draft, with its walk, simulation relation, lemma graph, Lean results on decisions and heap-port plan, is preserved on the git branch `checkpoint/before-meaning-route` (`da8b260b`). The three referee reports are in `ochr/docs/reviews/` (`2026-11-02-plan18-foundations.md`, `2026-11-02-plan18-simulation.md` and `2026-11-02-plan18-structure.md`); @sec-referees summarises what each found and how the present route answers it.
