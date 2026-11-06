// docs/23 test 0: does the set model exist? Standalone: compile with
//   typst compile ochr/docs/24-model-slice.typ
// The preamble (colours, numbered statements, explainer, why and reminder boxes, and the
// notation macros) is copied from docs/18, because Typst does not let a document import files
// outside its own directory. Macros added here are named by meaning, below the copied ones.

#set document(title: [The set model on a slice])


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
#let agr(a) = $attach(approx, br: #a)$
#let res = $rho$
#let ok(x) = $tack.double #x$
// The meaning of x in the set model; under an assignment `at` of the unknowns when given.
#let deno(x, at: none) = if at == none { $lr(⟦ #x ⟧)$ } else { $lr(⟦ #x ⟧)_(#at)$ }
// "Less informative than": the information order on meanings of states.
#let lessinfo = $subset.sq.eq$

// Numbered statements, one counter, as in the paper.
#let thm(kind, name, body) = figure(kind: "plan-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "plan-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
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
#let s-lean = tagc(rgb("#c9e8c9"), [proved in Lean])
#let s-heap = tagc(rgb("#cfe0f5"), [proved on the heap slice])
#let s-red(x) = tagc(rgb("#fbe5c0"), [reduced to #x])
#let s-paper = tagc(rgb("#e6dcf2"), [paper argument])
#let s-open = tagc(rgb("#f6cfcf"), [open])
#let s-design = tagc(rgb("#f2f2c4"), [open design question])

// Status colours, for figures and legends.
#let st-lean = rgb("#c9e8c9")
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

// Notation added for this document.
// The error value: the meaning of a term that goes wrong.
#let err = $upright("err")$
// The proof, the one element of a true proposition.
#let pf = $bullet$
// The two truth values, the meaning of Prop.
#let truthvals = ${emptyset, {bullet}}$
// The i-th inaccessible level of the cumulative hierarchy, the meaning of Type_i.
#let univ(i) = $V_(kappa_#i)$
// The tag of a constructor C.
#let ctag(c) = $⌜ #c ⌝$
// Set-theoretic (von Neumann) rank.
#let rank(v) = $op("rank")(#v)$
// Applying a meaning to arguments: the error value unless it is a function defined there.
#let app(f, d) = $op("app")(#f, #d)$
// The parts of a function type's meaning: domain, final contents, forward value, backward function.
#let dom = $op("Dom")$
#let fin = $op("Fin")$
#let fwd = $op("fwd")$
#let back = $op("back")$
// The guarded restriction of a recursive function's meaning below an argument.
#let guard(f, d) = $#f harpoon.tr_(#d)$

#align(center, text(size: 16pt, weight: "bold")[The set model on a slice])
#align(center, text(size: 11pt)[Test 0 of docs/23: the two circularities of Q9, and a well-founded model for a slice of Ochr])
#v(0.3em)
#align(center, text(
  size: 9pt,
  fill: muted-ink,
)[6 November 2026 · a paper result, with a Lean encoding of part of it · ochr/docs/24])
#v(0.6em)

#align(center, box(width: 90%, align(left)[
  *Summary.* The set model exists on the slice. The slice is `Nat`; a type function defined by recursion (`Cells`); a type variable $A : ty("Type")_0$ with the injectivity relation $R$ at it; a function type returning a borrow; and a Π into `Prop` over `Type₀`. docs/18's Q9 gave two reasons why the model as written was not yet a definition, and neither is an obstacle. First, the meaning of a type and $R$ were defined in terms of each other. If the meaning of a function type is taken to be its _good_ functions only, $R$ at every type is the meaning itself. No pairing of a type with a set of good elements is needed, and the Lean encoding shows that pairing would in fact break conversion of functions. Second, "induction on the type" had nothing smaller to recurse on. The meaning is instead defined on _terms_, by recursion on the position of an item in the program, the structure of the term, and, inside a recursive function, the rank of its decreasing argument. A type computed by code then means what its code computes, and a type variable means what the environment gives it. Universe levels matter only for sizes, not for well-foundedness. One consequence changes docs/23 and docs/18: a recursive function has a meaning whether or not it passed [Rec], so [Rec] belongs to membership, not to well-formedness. Not covered: the meaning of the state (borrows, loans, holes, moved-out places) and therefore of `Id`, which test 2 must add (@sec-inherit).
]))
#v(0.4em)

#outline(depth: 2, indent: auto)
#pagebreak()

= What this test is <sec-intro>

docs/23 chose to prove Ochr consistent by meaning preservation in the set model, and named the model itself as the main risk, shared with the superseded route. docs/18's open question Q9 says that the model as first written was not a valid definition, for two reasons, restated in @sec-circ. Test 0 asks whether a well-founded definition exists, on a slice chosen to contain each feature Q9 worries about:
- `Nat`;
- a type function defined by recursion on data, `Cells`;
- a type variable $A : ty("Type")_0$, with the injectivity relation $R$ at it;
- a function type returning a borrow, whose backward functions must be injective;
- a Π into `Prop` over `Type₀` (impredicativity).
Test 2 builds on this document, so two things are defined in general rather than for the slice only: function types (borrow parameters, a borrow result, function-typed parameters, and $R$), and the meaning of type-level code (calls of type functions) with its well-founded measure.

*What "exists" means here.* A definition, in ZFC with inaccessible cardinals, of two things:
- a meaning for every term and value of the slice: a set, or a distinguished _error value_;
- for every type, a set.
The definition must be well founded: no clause refers, directly or through others, to the meaning it is defining.

Existence does _not_ include _membership_: that the meaning of an accepted definition lies in the meaning of its type. Membership is the soundness theorem's job (docs/23, point 5, and docs/18's central theorem), and test 2 starts on it.

*Result.* The model exists on the slice, #s-paper, with a Lean encoding of most of it (@sec-lean). Neither circularity is an obstacle; both came from how the model was first phrased (@sec-circ). The definition needed eleven choices, named in @sec-choices. One of them changes docs/23 and docs/18 (@sec-rec). Nothing in the slice failed. What is not covered is listed in @sec-open; the next hardest piece is the meaning of the state, which `Id` needs inside the meaning of types (@sec-inherit).

#reminder[Notation from docs/18. $deno(x, at: gamma)$ is the meaning of $x$ under an assignment γ of the unknowns. An _abstract value_ σ is an unknown introduced by the checker, with type Δ(σ). A Π-type's _class_ is read off its codomain term: it returns types, returns proofs, or neither ("other"). [Rec] is the recursion check: every recursive call passes, at the declared decreasing position, a strict subterm of that parameter's entry value. docs/18's conditions on declarations, used below: (I1) strict positivity: the declared type $ty("D")$ occurs in a field type only as the whole field type, or nested at a _nestable_ parameter of an earlier inductive, never left of a Π, under `&`, or as the argument of a type function; (I2) the arguments of an occurrence of $ty("D")$ never mention $ty("D")$; (I3) a parameter is never called in a field type; (I4) parameter types do not mention $ty("D")$; (I5) fields form a telescope; (I6) every field of an inductive in `Type₀` or `Prop` lives in `Prop` or `Type₀`; (I7) a match on a proof produces data or a type only from a subsingleton (no constructors, or one whose fields are all proofs); (I8) recursion is never on a proof.]

= The two circularities, and why they go <sec-circ>

== Meaning and $R$, defined in terms of each other <sec-circ-r>

docs/18 interprets a function type that returns a borrow as a subset $R$ of a set of functions, namely those whose backward functions are injective. It defines $R_A subset.eq deno(A)$, for each type $A$, by induction on $A$, and at a function type it reads $R$ at the parameter and result types. So the meaning of a function type needs $R$, and $R$ needs meanings.

The two need not be separate. The meaning of a function type can be defined directly as its good part. For a function type returning a borrow:
$ deno(Pi(overline(x) : overline(A)). \& U) = { F in product_(overline(d) in dom) (deno(U) times (deno(U) -> fin)) mid(|) back_F (overline(d)) "is injective for every" overline(d) }, $
where the domain $dom$ is built from the _meanings_ of the parameter types (@sec-fun). Every argument the clause quantifies over is then already good, because it ranges over the meaning of its parameter type, which is a good set by the same definition. docs/18's clauses for $R$, one by one:

#table(
  columns: (45%, 55%),
  stroke: none,
  inset: (x: 4pt, y: 3pt),
  table.hline(stroke: 0.5pt + ink),
  [*docs/18's clause for $R$*], [*in the merged definition*],
  table.hline(stroke: 0.4pt + ink),
  [Propositions and universes: $R_A = deno(A)$.], [Unchanged.],
  [Inductive: $R$ holds of a constructor value when it holds of each field.], [Automatic. The least fixed point is built from the fields' meanings, which are good sets.],
  [$R_(\& T) = R_T$.], [Automatic. A borrow parameter ranges over $deno(T)$.],
  [Function type: for all arguments in $R$, the forward value is in $R$ and the backward function is injective.], [This _is_ the function-type clause: arguments range over the domains' meanings, the forward value over the result's.],
  table.hline(stroke: 0.5pt + ink),
)

So $R_A = deno(A)$ at every type, and $R$ disappears as a separate object.

*Type variables.* This is where docs/18 saw the need for pairs: a type as a set together with its subset of good elements, and a universe as a set of such pairs, because "$R$ at a type variable is undefined". In the merged definition, a type variable $A : ty("Type")_0$ means whatever the environment gives it, an arbitrary set in $univ(0)$, and $R$ at $A$ is the whole of that set. This is sound if no argument ever needs the elements of that set to be good beyond belonging to it.

An Ochr program can use a value $x : A$ as a function only after $A$ has become a Π-type. In this route that can happen in exactly one way: by transport along a proof $h : ty("Eq")(ty("Type")_0, A, Pi(dots) dots)$. The type of $h$ means ${pf}$ only when the set $A$ stands for _is_ the meaning of that Π-type, which is a good set. Under any other choice the hypothesis is false and there is nothing to prove. Conversion cannot do it either: there is no second path that instantiates the unknown, and the checker's conversion never identifies an unknown type with a Π-type.

A type computed by code is no exception. Take $F(b)$ where one arm of $F$ returns a Π-type: it means $deno(F)$ at the meaning of $b$, which in that arm is the good set, because every clause that produces a type produces a good set.

#why[$R$ exists to throw out functions whose backward function ignores its argument, which the checker's reasoning about `Id` rules out (docs/18's example `PF`). Putting the condition in the function-type clause throws them out at the only place they could come from. A universe of pairs would hold sets with bad elements, and nothing in Ochr can reach them.]

*Pairing is not just unnecessary but harmful.* The Lean encoding (@sec-lean) first paired a carrier with a predicate for $R$, and found two functions out of the meaning of `TailM`'s type, `g0` and `g1`, that agree on every good argument yet are distinct. The file keeps this counterexample as `Paired.agree_on_good` and `Paired.differ`. They differ only at a _junk_ argument: a borrow-returning function whose backward function is constant. Ochr's conversion compares two functions at generic arguments, and an assignment gives those only good values, so it identifies functions that agree on good arguments ([Conv-fun]). With pairs, convertible functions would have different meanings and conversion would be unsound. The repair would be a partial equivalence relation on each carrier. With carriers that hold only good elements, the two functions are equal (the same pair, as `f0` and `f1`, gives `f0_eq_f1`), and [Conv-fun] is function extensionality (`pi_ext`, `brwRet_ext`). That settles choice C1 below.

== "Induction on the type" has nothing smaller <sec-circ-ind>

docs/18's second reason: a function type's codomain is computed by running code at each argument, so it is not a subterm of the type; and a type variable has no structure. Both are true of _types as values_. Both stop mattering when the recursion is on _terms_. A type is a term whose meaning is a set, and its meaning is defined like the meaning of any other term:
- *Π-types.* A Π-type _term_ $Pi(x : A). B$ has its codomain $B$ as a subterm, even though the Π-type _value_ computes $B$ by running code at each argument. The value is a closure $chevron.l kappa tack.r Pi(x : A). B chevron.r$, and it means what the term means, with the captured values' meanings for its captures. So $deno(Pi(x : A). B)$ refers to the meanings of $A$, and of $B$ at each argument: both subterms.
- *Computed types.* A computed type $F(a)$, for an earlier global $F$, means $app(deno(F), deno(a))$, where $deno(F)$ is the meaning of an earlier item of the program: a function that already exists. Nothing at the use site recurses into $F$'s body.
- *Recursive type functions.* $F$'s own meaning is defined once, at $F$'s place in the program, from its body. It is defined by recursion on the rank of its decreasing argument, guarded so that a call that does not decrease means the error value (@sec-rec).
- *Type variables.* A type variable means what the environment gives it.

So the definition recurses on three things, lexicographically: the position of the item in the program, the structure of the term, and, inside a recursive function, the rank of its decreasing argument. All three are well founded (@thm-wf).

*Where a regress would come from.* docs/23 recorded the worry that interpreting code that returns $ty("Type")_i$ needs the meaning of $ty("Type")_i$, and so on. That would be a regress if $deno(ty("Type")_i)$ were defined as the set of meanings of the level-$i$ types: a universe of _codes_, defined together with its decoding (an inductive–recursive definition). Set theory does not need one. $deno(ty("Type")_i) = univ(i)$ is given outright, as a level of the cumulative hierarchy, and code that returns a type returns some member of it. The Lean encoding confirms this: Lean has no induction–recursion, and none was needed, because `Type₀` is read as Lean's `Type`, every type of level 0 (@sec-lean).

Universe levels are needed only for _sizes_: that a type at $ty("Type")_i$ means a member of $univ(i)$ (@sec-sizes).

#explainer[well-founded recursion and rank][A definition by _well-founded recursion_ defines $f(x)$ using $f$ only at arguments below $x$ in a relation that has no infinite descending chain. Such a definition has exactly one solution (the recursion theorem). The _rank_ of a set is the stage of the cumulative hierarchy at which it first appears: $rank(s) = sup{rank(e) + 1 | e in s}$. Every element of a set has smaller rank than the set, so a component of a tuple has smaller rank than the tuple. Ranks are ordinals, and ordinals have no infinite descending chain.]

= The model <sec-model>

== Universes, the proof, and the error value <sec-base>

- *Universes.* Fix inaccessible cardinals $kappa_0 < dots < kappa_N$, one for each $ty("Type")_i$ the program writes. Then $deno(ty("Type")_i) = univ(i)$ and $deno(ty("Prop")) = truthvals$, where $pf$ is a fixed object, "the proof".
- *Where meanings live.* Every meaning is a member of $U = V_(kappa_N + omega)$. Since $kappa_N + omega$ is a limit ordinal, $U$ is closed under pairing, subsets, function sets between its members, and products indexed by its members, and it contains $univ(N)$.
- *The error value.* $err$ is a fixed object not in $U$. It is the meaning of a term that goes wrong: applying something that is not a function, matching a value against arms none of which fits, calling a recursive function at an argument that does not decrease (@sec-rec). Every clause below is _strict_: unless it says otherwise, its result is $err$ if a meaning it needs is $err$ or has the wrong shape.
- *Tags.* Each constructor $ty("C")$ of each inductive gets a tag $ctag(ty("C")) in V_omega$, distinct from every other constructor's.

== Environments and assignments <sec-env>

An _environment_ η maps variables and abstract values to members of $U$. We write $deno(t, at: eta)$ for the meaning of a term $t$ in η. For the abstract values of a state, an environment is docs/18's _assignment_ γ. It gives the abstract values $sigma_1, dots, sigma_m$, in the order they were created, elements $gamma(sigma_i) in deno(Delta(sigma_i), at: gamma)$. Since $Delta(sigma_i)$ mentions only abstract values created before $sigma_i$, each condition is about a set that is already determined. This is the sense in which unknowns range over arbitrary set elements: $gamma(sigma)$ may be any member of the set, including a function no program computes.

docs/18's definition of an assignment also asks that $gamma(sigma)$ be "in $R$ at σ's type". By @sec-circ-r that condition is now the same as $gamma(sigma) in deno(Delta(sigma), at: gamma)$, so it can be dropped.

== Meanings of terms and values <sec-terms>

The meaning is defined one item of the program at a time. Before item $k$, the _signature meaning_ $M$ gives each earlier definition $g$ a meaning $M(g) in U union {err}$, and each earlier inductive $ty("D")$ a family $M(ty("D"))$ (@sec-ind). We write $app(F, overline(d))$ for $F(overline(d))$ when $F$ is a function whose domain contains $overline(d)$, and for $err$ otherwise. Given $M$, the meaning of a term is defined by the clauses below. They cover the pure terms of the slice; the clauses for the state are test 2's (@sec-inherit).

#table(
  columns: (36%, 64%),
  stroke: none,
  inset: (x: 4pt, y: 3pt),
  table.hline(stroke: 0.5pt + ink),
  [*Term*], [*Meaning in η*],
  table.hline(stroke: 0.4pt + ink),
  [a variable $x$, an abstract value σ], [$eta(x)$, $eta(sigma)$],
  [$ty("Type")_i$, `Prop`], [$univ(i)$, #truthvals],
  [an inductive type $ty("D")(overline(a))$, `Nat` included], [$M(ty("D"))(overline(e))$, where $overline(e)$ are the meanings of $overline(a)$, when $overline(e)$ is in $ty("D")$'s parameter domain],
  [a constructor $ty("C")(overline(a); overline(t))$], [$(ctag(ty("C")), e_1, dots, e_n)$, where $e_i$ is the meaning of $t_i$. The parameters $overline(a)$ are not read (docs/18, (V2)).],
  [a call $g(overline(t))$ of a global], [$app(M(g), overline(e))$, where $overline(e)$ are the meanings of $overline(t)$],
  [a call $x(overline(t))$ of a variable], [$app(eta(x), overline(e))$],
  [$kw("match") p space {ty("C")_i (overline(y)_i) => t_i}$ on data], [the meaning of $t_i$ in η extended with $overline(y)_i |-> overline(v)$, when $p$ means $(ctag(ty("C")_i), overline(v))$; $err$ when no arm fits],
  [a match on a proof that produces data or a type], [the inductive is a subsingleton (I7): with one constructor, the meaning of its arm with every field bound to $pf$; with none, $err$],
  [any term whose declared sort is `Prop` (a proof)], [$pf$, whatever its structure],
  [$ty("Eq")(A, a, b)$], [${pf}$ if $a$ and $b$ have the same meaning, $emptyset$ otherwise. $A$'s meaning must not be $err$, but is not otherwise read.],
  [$ty("J")(A, a, b, P, h, t)$, $kw("rewrite") h kw("in") t$, at data], [the meaning of $t$],
  [$Pi(overline(x) : overline(A)). B$], [@sec-fun],
  [$kw("fix") f (overline(x) : overline(A)) : B kw("by") x_j := t$, and λ], [@sec-rec],
  [$kw("let") x = a; b$, pure], [the meaning of $b$ in η extended with $x |->$ the meaning of $a$],
  [a sealed program #seal[$t$]], [the meaning of $t$, a closed term],
  table.hline(stroke: 0.5pt + ink),
)

*Values* mean what the terms they come from mean:
- a constructor value means its tag and its fields' meanings;
- `⋆` means $pf$;
- a closure $chevron.l kappa tack.r c chevron.r$ means the meaning of its code $c$ in the environment that gives its captures $kappa$ their meanings, and so does a Π-closure;
- a global's name means $M(g)$;
- a type value means the meaning of the type term it is;
- an abstract value means $gamma(sigma)$;
- a sealed program means its program's meaning.
Borrows, loans and `⊥` are test 2's (@sec-inherit).

#why[data is read _untyped_: a constructor value means a tagged tuple whatever type it is used at, which is what lets the step lemma speak of values before their types are known to be right. Functions are read on the domain their annotations give. A function must have some domain, and the annotation is the only one available without typing the body.]

*Proofs are read by their declared sort.* A proof means $pf$ because its declared sort is `Prop`, which is syntactic (D55), not because of anything in its structure. This is forced by impredicativity. A proof of $Pi(x : A). P$ must mean $pf$, not a function, so applying a proof cannot be function application, and the clause cannot look inside.

== Inductive declarations <sec-ind>

Take a declaration $kw("inductive") ty("D") (overline(x) : overline(X)) : s := ty("C")_1 (overline(g)_1 : overline(B)_1) | dots$ with $s in {ty("Prop"), ty("Type")_0}$.
- Its _parameter domain_ $P_ty("D")$ is the set of tuples $overline(a)$ with each $a_i$ in the meaning of $X_i$ at $overline(a)_(< i)$.
- A _family_ is a function $X : P_ty("D") -> cal(P)(univ(0))$. Families form a complete lattice under pointwise inclusion; it is a set, since $P_ty("D")$ and $cal(P)(univ(0))$ are in $U$.
- The operator Φ sends a family $X$ to the family
$ Phi(X)(overline(a)) = univ(0) inter union.big_i {(ctag(ty("C")_i), e_1, dots, e_k) | e_j in deno(B_(i,j), at: eta_j)^X }, $
where $eta_j$ binds the parameters to $overline(a)$ and the earlier fields to $e_1, dots, e_(j-1)$. In $deno(dot)^X$, every occurrence $ty("D")(overline(b))$ in a field type is read as $X$ at the meaning of $overline(b)$.

#thm([Lemma], [the operator is monotone], [
  Under (I1)–(I5), if $X subset.eq Y$ pointwise then $Phi(X) subset.eq Phi(Y)$.
]) <lem-mono>
#proof[By induction on the field type, show that its meaning grows with $X$.
- A whole-field occurrence of $ty("D")$ reads $X$ directly.
- A nested occurrence, at a nestable parameter of an earlier inductive $ty("E")$, reads $M(ty("E"))$ at a set that grows with $X$. $M(ty("E"))$ is monotone in its nestable parameters: it is the least fixed point of an operator monotone jointly in the family and in those parameters (this lemma for $ty("E")$, by induction on the program), and such a least fixed point is monotone in the parameter.
- Nothing else depends on $X$: the arguments of an occurrence never mention $ty("D")$ (I2), parameters are never called (I3), and $ty("D")$ is never the argument of a type function (I1).
- An equation field $ty("Eq")(T, a, b)$ reads only the meanings of $a$ and $b$, which are earlier fields' values, not $T$. So an equation over $ty("D")$ itself, as Fording writes, is constant in $X$. (This is why the `Eq` clause does not read its type, choice C10.)
- Fields form a telescope (I5). A Σ over a growing index set of growing fibres grows.]

#thm([Definition], [meaning of an inductive], [
  For $s = ty("Type")_0$, $M(ty("D"))$ is the least fixed point of Φ, which exists by the Knaster–Tarski theorem. For $s = ty("Prop")$, it is that least fixed point _truncated_: ${pf}$ at $overline(a)$ if the fixed point is non-empty there, $emptyset$ otherwise. Truncation is applied after the fixed point, so while the fixed point is built, a recursive field of a proposition ranges over the untruncated family, as in Werner's model.
]) <def-ind>

The intersection with $univ(0)$ makes the lattice a set without first proving sizes. @sec-sizes shows that it removes nothing, by (I6).

#explainer[least fixed points by Knaster–Tarski][In a complete lattice (every subset has a least upper bound and a greatest lower bound), every monotone map Φ has a least fixed point: the meet of all $X$ with $Phi(X) <= X$. Unlike iterating Φ from the bottom ω times, this needs no continuity, so it does not matter how many stages the construction would take.]

== Function types <sec-fun>

Take a Π-type term $Pi(x_1 : A_1, dots, x_n : A_n). B$. Its class and whether it returns a borrow are read off the codomain term, as the checker reads them. Let $I = {i | A_i = \& T_i}$ be its borrow parameters, and let $A_i^circle.small = T_i$ for $i in I$ and $A_i$ otherwise. In η:
- $dom$ is the set of tuples $overline(d)$ with each $d_i$ in the meaning of $A_i^circle.small$, in η extended with $overline(x)_(< i) |-> overline(d)_(< i)$. A borrow parameter contributes its _starting content_, and later parameter types read it as $*x_i$.
- $fin(overline(d)) = product_(i in I) T_i (overline(d))$ is the set of tuples of _final contents_, where $T_i (overline(d))$ is the meaning of $T_i$ at $overline(d)_(< i)$.
- $B(overline(d))$ is the meaning of $B$ in η extended with $overline(x) |-> overline(d)$: the codomain read at the call's start, as [Call-type] reads it.

The meaning is given by one of four clauses:
- *(Π-proof)* Class "returns proofs": ${pf}$ if $B(overline(d)) = {pf}$ for every $overline(d) in dom$; $emptyset$ if every $B(overline(d))$ is a truth value and some is $emptyset$; $err$ otherwise.
- *(Π-type)* Class "returns types": $product_(overline(d) in dom) B(overline(d))$. There are no final contents: a call of a type-returning function is erased, so it runs on a private copy and its writes never reach the caller (RULES P2).
- *(Π-data)* Class "other", $B$ borrow-free: $product_(overline(d) in dom) (B(overline(d)) times fin(overline(d)))$.
- *(Π-borrow)* Class "other", $B = \& U$: the functions $F in product_(overline(d) in dom) (U(overline(d)) times (U(overline(d)) -> fin(overline(d))))$ with $back_F (overline(d))$ injective for every $overline(d)$. Here $F(overline(d)) = (fwd_F (overline(d)), back_F (overline(d)))$, and $U(overline(d))$ is the meaning of $U$ at $overline(d)$. There is at least one borrow parameter (D44).

Some cases:
- A function-typed parameter, $A_i = Pi(dots)dots$, contributes its meaning by these same clauses: a good set.
- A borrowed function, $\&(Pi(dots)dots)$, allowed since D66, contributes that meaning as both its starting and its final content.
- If a later parameter type is false, $dom$ is empty, and the meaning is the set holding only the empty function.
- Each clause uses only the meanings of $A_i$, $T_i$, $U$ and $B$, which are subterms of the Π-term.

#why[the shape follows Aeneas. A borrow passed in is a value in and a value out. A borrow returned is a forward value, and a backward function from what the caller leaves in the borrow to what the lenders get back. Only injectivity is required, not the laws of a lens: `TailM`'s backward function $v |-> n + v$ does not give back $v$ when read again, and is still an Ochr function (docs/17, decision 5).]

== Recursive functions: guarded recursion <sec-rec>

Take $kw("fix") f (overline(x) : overline(A)) : B kw("by") x_j := t$ in η. A global's body is this with η empty and the signature meaning before it. Write $dom$ for its domain (@sec-fun). For $x_j : \& ty("D")$, the decreasing argument $d_j$ is the starting content.

#thm([Definition], [meaning of a recursive function], [
  $deno(kw("fix") f dots, at: eta)$ is the unique function $F$ on $dom$ with
  $ F(overline(d)) = deno(t, at: eta[overline(x) |-> overline(d), f |-> guard(F, overline(d))]), $
  where the _guarded restriction_ $guard(F, overline(d))$ is the function on $dom$ that sends $overline(e)$ to $F(overline(e))$ if $rank(e_j) < rank(d_j)$, and to $err$ otherwise. A `fix` without `by` (a λ) means $overline(d) |-> deno(t, at: eta[overline(x) |-> overline(d)])$, and $f$ is not in scope in it (D33).
]) <def-rec>

*It is well defined.* The right-hand side reads $F$ only at arguments whose $j$-th component has smaller rank. That relation on $dom$ is well founded, so by the recursion theorem exactly one $F$ satisfies the equation. Nothing about the body is needed: the definition exists whether or not the body passed [Rec].

*Consequence for docs/23 and docs/18.* Both put "every closure and global in the state has passed [Rec]" in the well-formedness invariant, on the ground that a `fix` has a meaning only through well-founded recursion. With the guard, every `fix` has a meaning, checked or not. [Rec] instead ensures that the guard never fires, which is part of membership.

#thm([Lemma], [the defining equation], [
  Suppose that at every $overline(d) in dom$, the meaning of $t$ uses the value of $f$ only at arguments $overline(e)$ with $rank(e_j) < rank(d_j)$. Then $F(overline(d))$ equals the meaning of $t$ with $f |-> F$ itself.
]) <lem-rec-eq>
#proof[$F$ and $guard(F, overline(d))$ agree at every argument the body uses.]

The hypothesis is the semantic form of [Rec]. [Rec] gives it in the following way.
- An accepted recursive call passes, at position $j$, a strict subterm of the entry value as refined.
- Under an assignment that satisfies the path's refinements (docs/23, point 5), that argument's meaning is a component, at some depth, of the tuple that is the entry value's meaning.
- A component has smaller rank.
- A closure formed in the body that calls $f$ captures $guard(F, overline(d))$. It is checked against the same entry value (R4), so it too calls $f$ only below.
- [Rec] forbids every other use of $f$: the name occurs only as the head of a call.
- (I8) excludes recursion on a proof. A proof means $pf$, and its rank never decreases, so the guard would fire.

The Lean encoding proves this lemma for type functions recursive on `Nat` (@sec-lean, `tfun_eq`).

The third historical closed proof of `False` (docs/18, the recursive local function that captured a value it split on) is an instance. There the recursion was missed, so in this model the program's meaning hits the guard at that call and is $err$: membership fails at the step where the bug was.

= Well-foundedness <sec-wf>

#thm([Theorem], [the model is well defined], [
  For every program of the slice, and every choice of inaccessibles for its universe levels, there is exactly one signature meaning $M$ and one meaning of terms and values satisfying the clauses of @sec-model.
]) <thm-wf>
#proof[By induction on the position $k$ of the item; assume $M$ for the items before $k$.
- *Terms and values.* These are finite trees: a term may embed values (a sealed program's arguments), and a value may embed code (a closure). Define their meanings by structural recursion on the tree. Every clause refers to one of three things:
  - the meanings of immediate subtrees, in an extended environment;
  - earlier items, through $M$;
  - inside a `fix`, the function being defined, at smaller rank, by the recursion of @def-rec, nested inside the structural one.
  No clause refers to the meaning of a type except through a subterm.
- *Item $k$.* A definition means its body read as a `fix` in the empty environment. An inductive means the least fixed point of an operator built from its field types' meanings, with $ty("D")$ read as the variable family $X$; the operator is monotone by @lem-mono.]

#figure(
  kind: table,
  supplement: [Table],
  table(
    columns: (40%, 60%),
    stroke: none,
    inset: (x: 4pt, y: 3pt),
    table.hline(stroke: 0.5pt + ink),
    [*docs/18's reason (Q9)*], [*where it went*],
    table.hline(stroke: 0.4pt + ink),
    [The meaning and $R$ are defined in terms of each other.], [One definition: a function type means its good functions (@sec-circ-r). $R_A = deno(A)$.],
    [$R$ is undefined at a type variable.], [A type variable means a set, and $R$ at it is that whole set (@sec-circ-r).],
    [A codomain is computed by running code, so it is not a subterm.], [The codomain _term_ is a subterm of the Π-term; a Π-value means its term under its captures (@sec-circ-ind).],
    [A type function recurses on data.], [Its meaning is a function, defined once at its place in the program by guarded recursion on rank (@def-rec).],
    [A type variable has no structure.], [It is looked up in the environment, not recursed into.],
    table.hline(stroke: 0.5pt + ink),
  ),
  caption: [Where docs/18's two reasons went.],
)

= The slice, worked <sec-slice>

== `Nat`

`Nat` is the inductive $ty("Z") | ty("S")(n : ty("Nat"))$. Its operator sends $X$ to ${(ctag(ty("Z")))} union {(ctag(ty("S")), e) | e in X}$, and its least fixed point is the set of numerals $hat(0) = (ctag(ty("Z")))$, $hat(1) = (ctag(ty("S")), hat(0))$, …, a copy of $NN$. We write $hat(NN)$ for it.

== A type function defined by recursion: `Cells`

From the suite (`Examples/CaseSplits.lean`):
```
inductive CellsEnd := End
inductive SliceOf (R : Type) := MkSlice(c : R)
inductive Cell (R : Type) := MkC(h : Nat, t : SliceOf(R))
def Cells (n : Nat) : Type by n := match n { Z => CellsEnd, S m => Cell(Cells(m)) }
```
- *The meaning of `Cells`.* `Cells` is a definition, so its meaning comes from @def-rec. At $hat(0)$ it is the meaning of `CellsEnd`, ${(ctag(ty("End")))}$. At $(ctag(ty("S")), hat(m))$ it is the meaning of `Cell` at the meaning of `Cells` at $hat(m)$. That recursive call is under the guard, and it passes, since $hat(m)$ is a component of $(ctag(ty("S")), hat(m))$ and so has smaller rank.
- *The defining equation holds.* @lem-rec-eq applies, so $deno(ty("Cells"))(hat(n))$ is $n$ nested cells ending in `End`.
- *A type that mentions it.* $Pi(n : ty("Nat"))(c : ty("Cells")(n)). ty("Nat")$ has domain ${(k, c) | k in hat(NN), c in deno(ty("Cells"))(k)}$ and means $product_((k, c) in dom) hat(NN)$. Its meaning reads `Cells` only through $M$; nothing about `Cells`'s body is consulted again.
- *At the generic call.* The checker stores $c$'s type as the sealed program #seal[$ty("Cells")(sigma_n)$]. Under an assignment γ that means $deno(ty("Cells"))(gamma(sigma_n))$, and nothing runs.
- *With an element type.* The array version `Cells(E, n)` (`Examples/ArrayBench.lean`) is the same with a type parameter $E$, which means $eta(E)$.

== A type variable, with $R$ at it

Take $T = Pi(A : ty("Type")_0)(g : Pi(y : \& A). \& A)(x : \& A). \& A$. For a set $X in univ(0)$, write $"Good"(X)$ for the meaning of $Pi(y : \& A). \& A$ with $A |-> X$:
$ "Good"(X) = {G in product_(d in X) (X times (X -> X)) | back_G (d) "is injective for every" d}. $
Then the domain of $T$ is ${(X, G, d) | X in univ(0), G in "Good"(X), d in X}$. The meaning of $T$ is the set of functions $F$ on that domain with $F(X, G, d) in X times (X -> X)$ and $back_F (X, G, d)$ injective.
- $R$ at $A$ is all of $X$. Nothing in $T$ needs more of $X$'s elements.
- $T$'s class is "other" and its level is $ty("Type")_1$, because the parameter $A : ty("Type")_0$ has sort $ty("Type")_1$ (@sec-sizes). Its meaning is a member of $univ(1)$, not of $univ(0)$.
- Instantiating $A := ty("Nat")$ gives $"Good"(hat(NN))$, which is the meaning of $Pi(y : \& ty("Nat")). \& ty("Nat")$.

The last point is the _substitution lemma_: the meaning of $T[A := V]$ in η equals the meaning of $T$ in η extended with $A |->$ the meaning of $V$. It is proved by induction on $T$:
- every clause reads $A$ only through the environment;
- declared sorts are unchanged by substituting a type for a type variable of the same sort (D55).
No condition on the elements of $X$ appears anywhere, which is @sec-circ-r's point.

== A function type returning a borrow

`TailM (x : &Nat) : &Nat` returns a borrow of the final `Z` inside `*x`. The meaning of its type is
$ {F in product_(n in hat(NN)) (hat(NN) times (hat(NN) -> hat(NN))) mid(|) back_F (n) "is injective for every" n}. $
- `TailM`'s own meaning, $n |-> (hat(0), v |-> n + v)$, is in this set.
- A function that returns a leaked borrow, $n |-> (hat(0), v |-> n)$, is not, by construction.

docs/18's `PF` shows why the second must be excluded:
```
def PF (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
```
- *At its generic call.* `PF`'s hypothesis compares the two observations of the owner of `x`, which leave `0` and `1`. It computes to `Eq(Nat, 0, 1)`, which means $emptyset$. So `PF`'s domain is empty, and its type means ${pf}$.
- *At a call through a good function.* Called with the borrow returned by some $g$ in the set above, the hypothesis means $back_g (n)(hat(0)) = back_g (n)(hat(1))$, which injectivity makes false. So no argument for `e` exists, and nothing follows.
- *If the set held the junk function.* The hypothesis would be true at that function, and `PF` would produce a member of $emptyset$.

Stating the meaning of `Id` exactly needs the meaning of the state (@sec-inherit). The point here is only that the type's meaning already excludes the junk function.

A function that _takes_ such a function, $Pi(g : Pi(x : \& ty("Nat")). \& ty("Nat")). ty("Nat")$, means $product_(G in "Good"(hat(NN))) hat(NN)$. Its domain holds only good functions, so two of its elements that agree on every good argument are equal: this is [Conv-fun] (@sec-circ-r).

== A Π into `Prop` over `Type₀`

- *A true one.* $Pi(A : ty("Type")_0)(x : A). ty("Eq")(A, x, x)$ has class "returns proofs". It means ${pf}$ if the meaning of $ty("Eq")(A, x, x)$ is ${pf}$ for every $X in univ(0)$ and every $d in X$, which it is. So it means ${pf}$.
- *A false one.* $Pi(A : ty("Type")_0)(x : A)(y : A). ty("Eq")(A, x, y)$ means $emptyset$: take $X = hat(NN)$, $hat(0)$ and $hat(1)$.
- *One over `Prop` itself.* $Pi(P : ty("Prop"))(h : P). P$ means ${pf}$.

The clause quantifies over $univ(0)$, which is a set, and its result is a truth value however large the domain. Impredicativity is harmless because the clause reads the codomain's meaning at each argument, never the meaning of the Π-type it is defining.

By contrast, the polymorphic identity's type $Pi(A : ty("Type")_0)(x : A). A$ has class "other" and level $ty("Type")_1$. It means $product_((X, d)) X$, a member of $univ(1)$ but not of $univ(0)$, as predicativity requires.

= Sizes: where universe levels matter <sec-sizes>

#thm([Lemma], [sizes], [
  Let $T$ be a type term whose declared sort is $ty("Type")_i$, or `Prop`. Let η give every free variable of $T$ a member of the meaning of its declared type. Then the meaning of $T$ is $err$, or a member of $univ(i)$, or, for `Prop`, a subset of ${pf}$.
]) <lem-sizes>
#proof[By induction on $T$. Since $kappa_i$ is inaccessible, $univ(i)$ is closed under finite tuples, subsets, and Σ and Π indexed by a member with members as fibres.
- An inductive's least fixed point lies inside $univ(0)$ by construction. (I6), that every field lives in `Prop` or `Type₀`, makes each field's meaning a subset of $univ(0)$ by induction, so the intersection in Φ removes nothing.
- A Π-type's level is the largest of its parameter types' sorts and its codomain's: `piSort` in `Machine.lean`, and `Decide.sortOf`, which the checker asserts agree. So every domain and fibre lies in $univ(i)$, and so does the product. The one exception, a codomain in `Prop`, means a truth value.
- A level-$j$ type with $j < i$ means a member of $univ(j) subset.eq univ(i)$. The model is cumulative although Ochr is not. This is harmless, because erasure is read from declared sorts, never from meanings.]

This lemma is part of membership, not of the definition: no clause of @sec-model needed it.

A remark on RULES.md. P2 says "the sort of a Π-type is read from its codomain's declared sort". In context the sentence is about whether the sort is `Prop`, but read literally it would put $Pi(A : ty("Type")_0). A -> A$ in $ty("Type")_0$. That is impredicative `Type₀`, which has no set model. The checker takes the maximum with the parameters' sorts (`piSort`, `Decide.sortOf`), so only the wording is off; it should say so.

= The Lean encoding <sec-lean>

`ochr/core/lean/Ochr/Model/Slice.lean`, at commit `e90f0cf8` on main (it supersedes `2e950326` and `36eb0ecb`). It imports Lean core only, is not imported by `Ochr.lean`, and is checked with `lake env lean Ochr/Model/Slice.lean`. It builds with no `sorry`; its axioms are `propext`, and `Quot.sound`, which comes from function extensionality.

*What it encodes.*
- A type means a Lean type holding only its good elements, as in C1. $Pi(x : \& T). \& U$ is the subtype of functions $d |-> (fwd, back)$ whose backward function is injective (`Sem.brwRet`, `Sem.Back`).
- `Type₀` means Lean's `Type`, every type of level 0, as $univ(0)$ does here. So there is no universe of codes and no induction–recursion.
- One interpretation function `I`, structurally recursive on a raw syntax of the slice, with earlier globals passed in as their meanings (induction on the program).
- Recursive type functions on `Nat` are defined by stages: the value at $n$ is stage $n + 1$, and stage $k + 1$ reads the body with stage $k$ answering the recursive call.

*What it proves.*
- `False` is empty (`false_empty`, `I_false_empty`).
- `tailM` is an element of `TailM`'s type, and that type excludes constant backward functions (`tailMTy_no_junk`).
- A type variable means its set (`I_tyvar`, by `rfl`).
- A Π into `Prop` over `Type₀` is a `Prop` (`I_piP_type0`), and the polymorphic identity lives at level 1 (`I_poly_id_level1`).
- The meaning of $Pi(g : Pi(x : \& ty("Nat")). \& ty("Nat")). ty("Nat")$ (`I_takes_brwRet`).
- Extensionality for functions and for borrow-returning functions with no side condition (`pi_ext`, `brwRet_ext`), which is what [Conv-fun] needs.
- The semantic form of [Rec]. `Decreasing` says reading the body at $n$ consults the recursive call only below $n$. Under it, `stage_stable` (stage $k$ at $m$ equals stage $m + 1$ at $m$ for every $k > m$) and `tfun_eq` (the defining equation at every $n$) hold. They are checked on `Cells` (a call at $n - 1$: `cells_succ`, `pi_cells`) and on `Alt` (a call at $n - 2$), where the file asserts that `rfl` fails, so the lemma is genuinely needed.
- The paired encoding's counterexample is kept as `Paired.agree_on_good` and `Paired.differ` (@sec-circ-r).

*Where the paper and the encoding differ, and why.*
- *Meaning and membership.* Lean is typed: every meaning must have a Lean type, so the meaning of a term that builds a borrow-returning function must be produced _together with_ the proof that its backward function is injective. On paper, data is read untyped and functions as partial functions into $U union {err}$, so membership can be proved after the meaning is defined, in the same induction (docs/23, point 5). A mechanisation of test 2 must follow the Lean pattern: meaning and membership are built together.
- *Recursion.* Lean recurses by stages, on `Nat` only. The paper uses guarded recursion on set rank, for any inductive. Both define the meaning unconditionally and put [Rec] in a lemma about the defining equation (`Decreasing` with `tfun_eq`; @lem-rec-eq). They differ only at a call that does not decrease: Lean answers with a lower stage, the paper with $err$.
- *Errors.* Lean reads an ill-formed type as the empty type, and an ill-formed numeral as 0; the paper keeps $err$ distinct. Accepted programs never reach either, but a membership proof against the Lean encoding could succeed vacuously, for instance under a hypothesis whose ill-formed type reads as empty. A mechanised membership proof should keep an explicit error.
- *Environments.* Lean tags each environment entry with its syntactic sort, so that it knows the entry's Lean type; the paper's environments are untyped sets. This makes no difference to the meanings.
- *Levels.* Lean is bounded at levels 0 and 1 (docs/18 Q8, bounded option). The paper fixes $kappa_0, dots, kappa_N$ per program.
- *Coverage.* The Lean slice is narrower than the paper's (@sec-open).

= The choices <sec-choices>

- *C1. A type means its good elements.* $R$ is folded into the function-type clause, not paired in. Pairing is not needed at type variables (@sec-circ-r), and it would make conversion of functions unsound unless replaced by a partial equivalence relation (Lean: `Paired.differ`).
- *C2. Universes are all sets of their level*, $univ(i)$, not only the meanings of Ochr types. So there is no universe of codes.
- *C3. Data is untyped, functions are typed by their annotations.* A constructor value means a tagged tuple whatever type it is used at. A closure means a function on its annotated domain, possibly partial (into $U union {err}$). In a typed mechanisation, meaning and membership are built together (@sec-lean).
- *C4. Proofs mean $pf$ by their declared sort*, never by their structure.
- *C5. The error value is strict*: it propagates unless a clause says otherwise.
- *C6. Recursive functions by guarded recursion on the set rank of the decreasing argument* (Lean: by stages, on `Nat`).
- *C7. Injectivity only.* A borrow-returning function's backward function must be injective, and need satisfy no lens law.
- *C8. Type-returning functions carry no final contents*, since their calls are erased.
- *C9. `J` and `rewrite` mean their transported term.* So docs/18's question about a `J` stuck at endpoints that are equal but not convertible does not arise at the level of meaning: a closed-off `J` means the same as its arm.
- *C10. `Eq`'s meaning does not read its type slot.* This is what makes an equation field over the inductive being declared (Fording) monotone.
- *C11. Constructor values ignore their recorded parameters* (V2). Propositions are truncated after the fixed point.

= What this test does not settle <sec-open>

- *The state, and so `Id`.* Borrows, loans waiting in fills, holes, inert loans, `⊥`, assignment, [End] and [Close] have no meaning yet, and `Id`'s meaning needs the meaning of imperative terms inside the meaning of types. On paper this adds clauses to the same recursion: types are terms, so term meanings and type meanings were always one structural recursion. `Id`'s sides are subterms, and the functions they call are earlier items, environment values, or closures that mean what their code means. So `Id` adds no new _kind_ of reference, and the stratification of @thm-wf still covers it. Two things keep it from being free, and they are the next hardest piece:
  - the _semantic state_ those clauses run on must be defined: a state with live borrows as a function from the final contents of its holes, after Aeneas;
  - every type must be shown to read the state only through contents it can read when it is formed (Π-types capture no borrow, RULES P2; an annotation is formed on a private copy, after [Access] has ended the borrows it reads through), so that a type's meaning never depends on a hole.
  In Lean, `Id` needs the meanings of state transformers inside `Den`, a semantic store over all level-0 types: an encoding cost.
- *Membership.* No membership statement is proved here. It includes:
  - the injectivity of every accepted borrow-returning function (docs/18 (T4));
  - that the guard never fires (@lem-rec-eq);
  - in Lean, a syntactic condition implying `Decreasing`, which needs a congruence lemma over all 17 term forms (routine).
- *Covered on paper but not in Lean:*
  - user inductives as least fixed points beyond `Pair` and `Unit`;
  - dependent constructors (telescopes and Fording);
  - type functions of arbitrary signature (Lean has $(A : ty("Type")_0)(n : ty("Nat"))$, recursive on $n$);
  - `Eq` beyond `Nat`.
- *Universes in the uniform statement.* The model needs one inaccessible per level the program uses. The uniform statement over all programs needs one for every level, which is docs/18's Q8, unchanged.
- *Outside the slice.* Inductives declared `abstract` or `implemented by` (the array library) need a clause of their own.

= What test 2 inherits <sec-inherit>

- *The clauses of @sec-model and choices C1–C11.*
- *The interface for the state.* The meaning of a term becomes a _state transformer_: from an environment and a semantic state to a value and a semantic state, or $err$. The pure clauses are the case where the state is unchanged. Test 2 adds the clauses for borrowing, assignment, [End], [Close] and observation.
- *Function meanings with borrow parameters* are read off the body's state transformer:
  - $fin$ is the final contents of the parameter cells;
  - for a borrow result, $fwd$ is the returned borrow's content at return, and $back(v)$ is the final contents after the caller leaves $v$ in it. This is Aeneas's backward function, and Ochr's [Close] fills with a hole.
- *Obligations, proved with the meaning (Lean) or in the same induction (paper):*
  - every borrow-returning closure the run builds has an injective backward function;
  - every closure that calls $f$ calls it below the entry rank (@lem-rec-eq);
  - [Conv-fun] is sound, which is function extensionality under C1;
  - `⊥` means "no information", as docs/18 now says.
- *For the higher-order slice:*
  - function parameters range over good sets (C1);
  - a closure built in the run and called later means a function on its annotated domain (C3);
  - a function that takes a function returning a borrow has been interpreted in Lean (`I_takes_brwRet`).

= Summary for docs/18 <sec-summary>

+ Test 0 passes on the slice: on paper, and for most of the slice in Lean (`Ochr/Model/Slice.lean`, `e90f0cf8`: no `sorry`; axioms `propext` and `Quot.sound`).
+ Q9's first circularity goes by letting a function type mean only its good functions, so $R$ at every type is the meaning. Pairing $R$ in is not needed at type variables, and would make conversion of functions unsound (Lean: `Paired.differ`).
+ Q9's second circularity goes by defining meanings on terms, by recursion on program position, term structure and, inside a `fix`, the rank of the decreasing argument. $ty("Type")_i$ means $univ(i)$ outright, so there is no universe of codes, and levels matter only for sizes.
+ A `fix` means a function, by guarded recursion, whether or not it passed [Rec]. So [Rec] moves from well-formedness to membership (the guard never fires), and an assignment's "in $R$" condition is redundant.
+ The next hardest piece is the meaning of the state (borrows, holes, `⊥`) and so of `Id` inside types. It adds clauses to the same recursion, and in a typed mechanisation meaning and membership must be built together.
