#import "@preview/curryst:0.5.0": prooftree, rule
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#set document(title: "Och: A Core Calculus with Iota/Fix and Equirecursive Subtyping")
#let dark-mode = false
#set text(font: "New Computer Modern", size: 10pt, fill: if dark-mode { white } else { black })
#set page(margin: 2.5cm, fill: if dark-mode { rgb("#1a1a2e") } else { white })
#set par(justify: true)
#set heading(numbering: "1.1")

// Helper for inference rules: named rule with premises above, conclusion below
#let irule(name, conclusion, ..premises) = {
  let prems = premises.pos()
  if prems.len() == 0 {
    prooftree(rule(name: smallcaps(name), $#conclusion$))
  } else {
    prooftree(rule(
      name: smallcaps(name),
      $#conclusion$,
      ..prems.map(p => $#p$),
    ))
  }
}

// Judgment shorthands
#let sub(S, G, a, b) = $#S ; #G tack.r #a subset.sq.eq #b$
#let wf(G, e) = $#G tack.r #e "wf"$
#let eval(e, v) = $#e arrow.b.double #v$
#let subst(body, x, v) = $#body [#x arrow.r.bar #v]$

#align(center, text(size: 17pt, weight: "bold")[Och])
#v(1em)

= Introduction <intro>
After playing around with dependent types in an imperative programming setting during the masters thesis, I came to the conclusion that a fairly uncommon combination of language features would lead to an excellent combination of developer ergonomics and expressivity.

I want to study the most unusual + unweildly of these features in isolation with a core calculus before building full Ochre, specifically:
- The "terms are types" philosophy, as exonerated by PSS @hutchins-2010. In Och this comes out roughly to "types are terms with holes".
- Terms/types form a subtyping lattice, where supertypes can be freely substituted for any subtype without any coercions.
TODO: get rid of the "but why are these features important" feeling

== Goals
*Soundness* - Ochre is only valuable if they can trust that the compiler will catch runtime errors at compile time. Proving the soundness of systems with the above features, let alone ownership + mutation is new research, Och is a place to do that research.

*Expressivity* - The type system must be able to articulate properties and catch bugs that people care about. E.g. it must be expressive enough to tell the difference between $x + y$ and $x + x$ if one is correct and the other incorrect.

*Extensibility* - Och is the first in a series of languages which will eventually culminate in full Ochre. As such, there is no point working with features which won't be re-usable. This has already manifested in the decision to tackle arbitrary unbounded recursion via $"fix"$ instead of having to add primitive inductive types and only well-founded induction.

= Related Work <related>
*Pure Subtype Systems* @hutchins-2010

= Language Semantics <lang-sem>

The term language is

$
  e, tau ::= & x                      &         "variable" \
           | & lambda(x lt.eq tau). e &           "lambda" \
           | & e_1 space e_2          &      "application" \
           | & top                    &   "universe (top)" \
           | & bot                    & "primitive bottom" \
           | & iota(x lt.eq tau). e   & "self-type binder" \
           | & "fix"(x lt.eq tau). e  & "recursive binder" \
$

There is no separate type category: every $tau$ above is itself a term.
Throughout the paper $Gamma$ denotes a typing context (a finite map from
variable names to their declared types).

*Variables, lambdas, application* as per the standard λ-calculus, except $lambda$ has a domain type annotation which is respected by the type checker.

*$top$ and $bot$* are the top and bottom of the subtyping lattice. $top$ represents the widest possible type, which tells you nothing about the term being typed, and $bot$ is the empty type.

*Fix* $"fix"(x lt.eq tau). e$ allows a term to be defined in terms of itself. $x$ is the reference to self, and $tau$ is the "upper bound" which the whole expression can be assumed to have while it's being type checked (which prevents loops during type checking).

*Iota* $iota(x lt.eq tau). e$ allows a type to be defined in terms of *the term inhabiting it*. This means $e subset.sq.eq iota (x:tau_0). tau_1$ is reduced to $e subset.sq.eq tau_1[x arrow.r.bar e]$ during checking (notice: the LHS has moved to the RHS). This is a Cedille-style self type @fu-stump-2014, and allows for church encodings with dependent elimination instead of having to add datatypes to the language as a primitive.

== Concrete semantics — the evaluation judgment <conc-eval>

The concrete evaluator is a substitution-based call-by-value big-step
interpreter on closed terms. Lambdas, ι, and fix are values;
applications in function position unroll the recursive binder by
substituting its self-reference, then re-apply.

Concrete evaluation is _supposed_ to represent Och's runtime semantics, but Och has no concept of levels/universes/stages, so the type checker cannot enforce that ${top, bot, iota}$ don't turn up at runtime.
Since soundness is defined roughly as "terms accepted by the type checker never crash at runtime", we must handle these values in the concrete semantics to avoid making our soundness completely unprovable.

This can and should be solved in the future by adding levels to all binders (see §3.6 "Adding Universes" of @hutchins-2010 for roughly how I plan on doing this).

We write the judgment $e arrow.b.double v$ for "closed term $e$ concretely evaluates to
value $v$."



#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("E-Val", eval($v$, $v$)),

  irule("E-App", eval($f space a$, $v$), eval($f$, $lambda(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $b[x arrow.r.bar v_a]$,
    $v$,
  )),

  irule("E-App-Iota", eval($f space a$, $v$), eval($f$, $iota(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $(b[x arrow.r.bar iota(x lt.eq tau).b]) space v_a$,
    $v$,
  )),
  irule("E-App-fix", eval($f space a$, $v$), eval($f$, $"fix"(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $(b[x arrow.r.bar "fix"(x lt.eq tau).b]) space v_a$,
    $v$,
  )),
))

$
  "where" v in "Value" ::= & lambda(x lt.eq tau). e &           "lambda" \
                         | & bot                    & "primitive bottom" \
                         | & top                    &   "universe (top)" \
                         | & iota(x lt.eq tau). e   & "self-type binder" \
                         | & "fix"(x lt.eq tau). e  & "recursive binder" \
$


Free variables are not values.

*$bot$ is a self-evaluating value.* Like $top$, $bot$ evaluates to
itself via [E-Val] and has no application dispatch arm, so applying
an argument to $bot$ is _stuck_ (parallel to $top$-application). This is
intentional: $bot$ is a type, not a callable. The typing discipline must
ensure well-typed programs never reach $bot space a$ at runtime.

This is the *operational specification* of the language.

= Typing Rules <decl-sub>

Och's type system is structured around two relations:

*Well-formedness* $Gamma tack.r e "wf"$ --- is $e$ well-formed under $Gamma$? Defined by structural rules (@well-formed), delegating all type-comparison questions to subtyping. No type is assigned; in Och, a value IS its own type (by [S-Refl]).

*Subtyping* $S ; Gamma tack.r a subset.sq.eq b$ --- is $a$ a subtype of $b$ under $Gamma$, assuming coinductive hypotheses $S$? Subtyping in Och means set inclusion: $A subset.sq.eq B$ iff every value of $A$ is also a value of $B$.

== Context $Gamma$ <context>

$Gamma$ is the typing context --- a finite ordered list of
$(upright("variable"), upright("type"))$ pairs, with the most recent binder at the front.
Lookup is $Gamma(x)$ for the declared type of $x$; extension is $Gamma, x lt.eq A$.

== Seen set $S$ <seen-set>

$S$ is a set of pairs $(a, b)$ --- ancestor subtyping goals introduced
by productive unfolding rules (ι-introduction and the four unfold
rules, @productive). The invariant: only those five rules extend $S$; every
other rule propagates it unchanged. This is the Brandt--Henglein device @brandt-henglein-1998
for equirecursive subtyping --- coinductive assumptions are only legal
after at least one productive step, so reflexivity of a non-productive
goal cannot be closed by a hypothesis. In effect, $S$ is a finite representation of a coinductive (potentially infinite) proof tree: when a goal recurs, the branch closes rather than recursing forever, encoding a regular infinite derivation as a finite one.

The "real" subtyping judgment is $emptyset ; Gamma tack.r a subset.sq.eq b$ (empty hypothesis set);
non-empty $S$ arises only inside a derivation.


== Well-formedness <well-formed>

The well-formedness judgment $Gamma tack.r e "wf"$ determines whether term $e$ is well-formed under context $Gamma$. It does not assign a type --- in Och's "terms are types" world, a value IS its own most-precise type (by [S-Refl]), and all type-comparison questions are handled by subtyping. Well-formedness validates purely structural conditions: annotations are types, binders are in scope, and applications have Π-typed functions with domain-inhabiting arguments.

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("W-Var", wf($Gamma$, $x$), $x in "dom"(Gamma)$),
  irule("W-Type", wf($Gamma$, $top$)),
  irule("W-Bot", wf($Gamma$, $bot$)),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("W-Lam", wf($Gamma$, $lambda(x lt.eq A). b$), wf($Gamma$, $A$), wf(
    $Gamma\, x lt.eq A$,
    $b$,
  )),
  irule(
    "W-App",
    wf($Gamma$, $f space a$),
    wf($Gamma$, $f$),
    wf($Gamma$, $a$),
    sub($emptyset$, $Gamma$, $f$, $lambda(x lt.eq A). B$),
    sub($emptyset$, $Gamma$, $a$, $A$),
  ),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("W-Iota", wf($Gamma$, $iota(x lt.eq A). b$), wf($Gamma$, $A$), wf(
    $Gamma\, x lt.eq A$,
    $b$,
  )),
  irule("W-Fix", wf($Gamma$, $"fix"(x lt.eq A). b$), wf($Gamma$, $A$), wf(
    $Gamma\, x lt.eq A$,
    $b$,
  )),
))

*[W-Var]* requires the variable to be in scope.

*[W-Type]* and *[W-Bot]* are always well-formed.

*[W-Lam], [W-Iota], [W-Fix]* check that the annotation is well-formed and that the body is well-formed under the extended context.

*[W-App]* is the only rule with subtyping premises: the function must subtype some $lambda(x lt.eq A). B$ (it has a Π-type), and the argument must subtype the domain $A$. No type is assigned to the result --- the result's type is the result itself (by [S-Refl]), and if the caller needs to know it subtypes something, that is a separate subtyping question.


== Rule taxonomy <rule-taxonomy>

The rules fall into four categories. Each serves a distinct purpose;
knowing which category a rule belongs to predicts its shape.

#figure(
  table(
    columns: (auto, 1fr, 1fr, auto),
    align: (left, left, left, center),
    table.header([*Category*], [*Purpose*], [*Rules*], [*Extends $S$?*]),
    table.hline(),
    [Structural (@structural)],
    [Plumbing: compose, lookup, without inspecting constructors on either side],
    [S-Refl, S-Top, S-BotL, S-Trans, S-Hyp, S-Var],
    [no],
    [Congruence (@congruence)],
    [Match constructor on both sides; reduce to sub-obligations with variance],
    [S-Lam, S-App-Cong, S-Iota-Cong, S-Fix-Cong],
    [no],
    [Productive unfolding (@productive)],
    [Unfold a recursive binder (ι/fix); extend $S$; enable coinductive closure],
    [S-Iota-Intro, S-Unfold-Iota-L/R, S-Unfold-Fix-L/R],
    [*yes*],
    [Conversion (@conversion)],
    [Close under head reduction so subtyping is closed under computation],
    [S-Beta-L/R],
    [no],
  ),
  caption: [Rule taxonomy for declarative subtyping],
)

The $S$-extension column matters: S-Hyp can only fire against entries
that some ancestor productive rule installed, so any path to S-Hyp
must cross an unfold --- the productivity requirement made mechanical.

== Structural rules <structural>

"Structural" rules talk about $subset.sq.eq$ as a relation on terms without
inspecting either side's head constructor: reflexivity, transitivity,
the top element, hypothesis lookup, and variable lookup.

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("S-Refl", sub($S$, $Gamma$, $e$, $e$)),
  irule("S-Top", sub($S$, $Gamma$, $e$, $top$)),
  irule("S-BotL", sub($S$, $Gamma$, $bot$, $e$)),
))

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("S-Trans", sub($S$, $Gamma$, $a$, $c$), sub($S$, $Gamma$, $a$, $b$), sub($S$, $Gamma$, $b$, $c$)),
  irule("S-Hyp", sub($S$, $Gamma$, $a$, $b$), $(a, b) in S$),
  irule("S-Var", sub($S$, $Gamma$, $x$, $Gamma(x)$)),
))

*Ex falso via subsumption.* There is no dedicated "absurd"
eliminator. If $a subset.sq.eq bot$ is derivable, then
$a subset.sq.eq e$ for every $e$ via [S-Trans] on [S-BotL]. The "contradiction"
discharge is subsumption alone. This matches the DOT tradition: $bot$
inhabits every type trivially in subtyping, so any term whose type is
already $bot$ flows into any expected type without further ceremony.

*Why [S-Trans] is a constructor, not a derived theorem.* In a
normal simply-typed subtyping relation, transitivity is admissible: a
standard induction on the shape of the two derivations composes them.
That argument requires a decreasing syntactic measure --- typically,
both derivations get strictly smaller in each case of the composition.
Och's four unfold rules and iota-intro break this: unfolding
$"fix"(x lt.eq A). "body"$ replaces it with
$"body"[x arrow.r.bar "fix"(x lt.eq A). "body"]$, which is _larger_ than the
original. There's no obvious structural measure on derivations that
decreases through an unfold, so transitivity is not derivable by
induction on derivations. The seen-set discipline of @productive is the
coinductive counterpart that keeps the relation consistent, but it
doesn't by itself give admissibility of transitivity.

Eliminating transitivity as a primitive rule (_transitivity elimination_) is highly desirable: it simplifies metatheory and makes the relation syntax-directed. Hutchins' Pure Subtype Systems @hutchins-2010 --- a closely related system --- did not manage to eliminate transitivity. Pasquale and García-Pérez @pasquale-garcia-perez-2026 succeeded in a continuation of that work, but required switching the entire theory to a Krivine machine.

== Congruence rules <congruence>

Congruence rules _do_ inspect
the head constructor on both sides, require it to match, and reduce the
goal to sub-obligations on the immediate sub-terms with appropriate
variance.

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule(
    "S-Lam",
    sub($S$, $Gamma$, $lambda(x lt.eq A_1). b_1$, $lambda(x lt.eq A_2). b_2$),
    sub($S$, $Gamma$, $A_2$, $A_1$),
    sub($S$, $Gamma\, x lt.eq A_2$, $b_1$, $b_2$),
  ),
  irule(
    "S-App-Cong",
    sub($S$, $Gamma$, $f_2 space a_2$, $f_1 space a_1$),
    sub($S$, $Gamma$, $f_2$, $f_1$),
    sub($S$, $Gamma$, $a_2$, $a_1$),
    sub($S$, $Gamma$, $a_1$, $a_2$),
  ),
))

#align(center, stack(
  dir: ttb,
  spacing: 1.5em,
  irule(
    "S-Iota-Cong",
    sub($S$, $Gamma$, $iota(x lt.eq A_1). B_1$, $iota(x lt.eq A_2). B_2$),
    sub($S$, $Gamma$, $A_1$, $A_2$),
    sub($S$, $Gamma\, x lt.eq A_2$, $B_1$, $B_2$),
  ),
  grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    irule(
      "S-Fix-Cong",
      sub($S$, $Gamma$, $"fix"(x lt.eq A_1). b_1$, $"fix"(x lt.eq A_2). b_2$),
      sub($S$, $Gamma$, $A_1$, $A_2$),
      sub($S$, $Gamma\, x lt.eq A_2$, $b_1$, $b_2$),
    ),
  ),
))

The equivalence premise on [S-App-Cong] (both directions on the
argument) is necessary because a neutral head
can use its argument at any variance, so equivalence is the only sound
congruence.

== Productive unfolding (extend $S$) <productive>

A rule is _productive_ when it replaces a goal whose head is a
recursive binder (ι or fix) with a goal where that binder has been
unfolded once. Unfolding makes the term _larger_ in syntactic size, so
no structural induction can traverse an arbitrary chain of unfolds.
Productivity instead provides a _coinductive_ handle: once at least
one unfold has fired, the original goal is guaranteed to eventually
re-appear as an ancestor, at which point [S-Hyp] can close the
derivation.

The rules below are the only ones that extend $S$. Let $S' = S union {(a, b)}$ where $(a, b)$ is the current goal.

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("S-Iota-Intro", sub($S$, $Gamma$, $a$, $iota(x lt.eq A). B$), sub($S'$, $Gamma$, $a$, $A$), sub(
    $S'$,
    $Gamma$,
    $a$,
    $B[x arrow.r.bar a]$,
  )),
  irule("S-Unfold-Iota-L", sub($S$, $Gamma$, $iota(x lt.eq A). B$, $c$), sub(
    $S'$,
    $Gamma$,
    $B[x arrow.r.bar iota(x lt.eq A).B]$,
    $c$,
  )),
))

#align(center, stack(
  dir: ttb,
  spacing: 1.5em,
  irule("S-Unfold-Iota-R", sub($S$, $Gamma$, $a$, $iota(x lt.eq A). B$), sub(
    $S'$,
    $Gamma$,
    $a$,
    $B[x arrow.r.bar iota(x lt.eq A).B]$,
  )),
  grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    irule("S-Unfold-Fix-L", sub($S$, $Gamma$, $"fix"(x lt.eq A). b$, $c$), sub(
      $S'$,
      $Gamma$,
      $b[x arrow.r.bar "fix"(x lt.eq A).b]$,
      $c$,
    )),
    irule("S-Unfold-Fix-R", sub($S$, $Gamma$, $a$, $"fix"(x lt.eq A). b$), sub(
      $S'$,
      $Gamma$,
      $a$,
      $b[x arrow.r.bar "fix"(x lt.eq A).b]$,
    )),
  ),
))

S-Unfold-Iota-R is the weaker sibling of S-Iota-Intro (same conclusion, no annotation
premise), needed to close the equivalence of ι-unfolding.

// *Worked example: $"dtrue" subset.sq.eq "dBool"$.* With

// $
//   "dtrue" &:= iota(x lt.eq top). lambda(P lt.eq x arrow top). lambda(t lt.eq P space x). lambda(f lt.eq top). t \
//   "dBool" &:= "fix"(B lt.eq top). iota(x lt.eq B). lambda(P lt.eq B arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space x
// $

// the subtyping check $emptyset ; Gamma tack.r "dtrue" subset.sq.eq "dBool"$ loops through a
// contravariant domain: dBool's motive parameter is $P lt.eq "dBool" arrow top$,
// while dtrue's is $P lt.eq x arrow top$ where $x$ is the inhabitant ---
// ultimately dtrue. So the [S-Lam] contravariant premise for the
// $P$ binder demands $"dBool" subset.sq.eq "dtrue"$… which needs the original relationship
// back. Without the seen set this loops forever; with it, the productive
// unfold at the top installs $("dtrue", "dBool")$ into $S$, and the loop
// closes via [S-Hyp]:

// #let dstep(depth, judgment, rulename) = {
//   pad(left: depth * 1.5em, grid(
//     columns: (1fr, auto),
//     $#judgment$, text(size: 8pt, fill: luma(100))[#rulename],
//   ))
// }
// #let dnote(depth, note) = {
//   pad(left: depth * 1.5em, text(size: 9pt, style: "italic", fill: luma(100))[#note])
// }
// #block(inset: (y: 0.5em), stack(
//   dir: ttb,
//   spacing: 0.4em,
//   dstep(0, sub($emptyset$, $Gamma$, $"dtrue"$, $"dBool"$), [root goal]),
//   dstep(
//     1,
//     sub(
//       $S_1$,
//       $Gamma$,
//       $"dtrue"$,
//       $iota(x lt.eq "dBool"). lambda(P lt.eq "dBool" arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space x$,
//     ),
//     [S-Unfold-Fix-R],
//   ),
//   dnote(1, [where $S_1 = {("dtrue", "dBool")}$]),
//   dnote(1, [Annotation premise:]),
//   dstep(2, sub($S_1$, $Gamma$, $"dtrue"$, $"dBool"$), [S-Hyp #sym.checkmark]),
//   dnote(2, [root goal reappears --- closed by $(upright("dtrue"), upright("dBool")) in S_1$]),
//   dnote(1, [Body premise (after $[x arrow.r.bar "dtrue"]$):]),
//   dstep(
//     2,
//     sub(
//       $S_1$,
//       $Gamma$,
//       $"dtrue"$,
//       $lambda(P lt.eq "dBool" arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space "dtrue"$,
//     ),
//     [S-Lam …],
//   ),
//   dnote(2, [further structural reduction; any recurrence of $"dtrue" subset.sq.eq "dBool"$ closes via S-Hyp]),
// ))

// Both branches of [S-Iota-Intro] find the root goal waiting in $S_1$ and
// close via [S-Hyp]. This is the Brandt--Henglein discipline in action:
// recursion in the subtyping judgment is legal _only across a
// productive unfold_, so non-productive loops (e.g. reflexivity-by-loop)
// cannot sneak through.

== Conversion <conversion>

The subtyping relation must be closed under head reduction: if $a$ computes to $a'$, then $a subset.sq.eq b$ should hold iff $a' subset.sq.eq b$. These rules provide that closure.

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("S-Beta-L", sub($S$, $Gamma$, $(lambda(x lt.eq A). "body") space "arg"$, $b$), sub(
    $S$,
    $Gamma$,
    $"body"[x arrow.r.bar "arg"]$,
    $b$,
  )),
  irule("S-Beta-R", sub($S$, $Gamma$, $a$, $(lambda(x lt.eq A). "body") space "arg"$), sub(
    $S$,
    $Gamma$,
    $a$,
    $"body"[x arrow.r.bar "arg"]$,
  )),
))

= Metatheory <metatheory>

Soundness connects the concrete semantics (@conc-eval), subtyping (@decl-sub), and well-formedness (@well-formed).

*Evaluation equivalence.* If $e$ evaluates to $e'$, both directions of subtyping hold.

$
  e "closed" and e arrow.b.double e' arrow.double emptyset ; emptyset tack.r e' subset.sq.eq e and emptyset ; emptyset tack.r e subset.sq.eq e'
$

*Preservation.* Evaluation preserves well-formedness (derives from evaluation equivalence).

$
  tack.r e "wf" and e arrow.b.double e' arrow.double tack.r e' "wf"
$

*Progress.* A well-formed closed term doesn't get stuck during evaluation. The evaluator may return a value or run out of fuel but never reaches an error state.

*End-to-end.* Composing the above: if $e$ is well-formed and subtypes $tau$, and $e$ evaluates to $e'$, the result subtypes $tau$.

$
  tack.r e "wf" and emptyset ; emptyset tack.r e subset.sq.eq tau and e arrow.b.double e' arrow.double emptyset ; emptyset tack.r e' subset.sq.eq tau
$

== What soundness promises to the programmer <promises>

Two separable runtime properties a type system can promise:

+ *Termination.* Running a well-typed program eventually produces
  a value. A totality / normalization claim.
+ *No runtime type errors.* Conditional on the program _not_
  diverging, the value it produces is well-formed and the program never
  reaches a stuck state.

Och *does not aim to prove (1).* Consistency and normalization
are explicitly deferred; the calculus admits non-terminating terms by
design (type-in-type; general recursion via fix).

Och *does aim to prove (2)*, and this is the real runtime
guarantee of the type system. The language expects the following
discipline: *type-check first; only evaluate if it succeeded.*

= Appendix A. Lean Formalisation <lean-formal>

The entire calculus described in this paper is formalised in Lean 4. This appendix maps the paper's named-variable presentation to the
mechanised definitions, and notes the one systematic difference: the formalisation uses *de Bruijn indices* throughout, so named variables
$x$ become positional indices, substitution $"body"[x arrow.r.bar v]$ becomes index arithmetic, and context lookup $Gamma(x)$ becomes list indexing.

== Representation <lean-repr>

All terms, types, and values share a single inductive `Expr`. Named variables $x$ are represented by `Expr.bvar` (a natural-number index); substitution uses `Expr.subst`/`Expr.shift` for standard de Bruijn arithmetic. The context $Gamma$ is `List Expr`, indexed by position with the innermost binder at index 0.

A named variable $x$ bound at the innermost binder becomes `bvar 0`; a variable bound $k$ binders out becomes `bvar k`; substitution $"body"[x arrow.r.bar v]$ becomes `body.subst 0 v`.

== Correspondence <lean-corr>

#figure(
  table(
    columns: (1fr, 1fr, auto),
    align: (left, left, left),
    table.header([*Paper concept*], [*Lean definition*], [*File*]),
    table.hline(),
    [Term syntax ($e, tau$)], [`Expr`], [`Syntax.lean`],
    [Concrete evaluation ($e arrow.b.double v$)], [`concEval`], [`Eval.lean`],
    [Declarative subtyping ($S ; Gamma tack.r a subset.sq.eq b$)], [`Subtype'`], [`Subtyping.lean`],
    [Evaluation equivalence], [`concEval_equiv`], [`Soundness/ConcEvalPreservation.lean`],
    [Preservation], [`concEval_preservation`], [`Soundness.lean`],
    [Progress], [`synth_progress`], [`Soundness.lean`],
    [End-to-end soundness], [`soundness`], [`Soundness.lean`],
  ),
  caption: [Paper-to-Lean correspondence],
)

The formalisation also includes an algorithmic decision procedure for these judgments (`evalSubst`, `subCheckSubst`, `Och.check` in `EvalSubst.lean` and `API.lean`), with partial soundness verification against the declarative `Subtype'` relation.

== De Bruijn details <lean-db>

The formalisation's seen-set $S$ is `List (Nat × Expr × Expr)` --- each entry is depth-tagged with
$|Gamma|$ at which it was recorded, and the hypothesis rule shifts entries to the current depth on use.
This bookkeeping is invisible in the named presentation: free variables carry their own names, so no
shift is ever required at lookup time.

== Proof status <lean-proof>

Evaluation equivalence, preservation, and progress are *sorry-free*. The end-to-end composition is sorry-free in its own body.

#bibliography("refs.bib")
