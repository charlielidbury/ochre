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

// Subtyping judgment shorthand
#let sub(S, G, a, b) = $#S ; #G tack.r #a subset.sq.eq #b$
#let sube(S, G, a, b) = $#S ; #G tack.r #a attach(subset.sq.eq, br: e) #b$
#let synth(G, e, v) = $#G tack.r #e arrow.squiggly #v$
#let eval(e, v) = $#e arrow.b.double #v$
#let subst(body, x, v) = $#body [#x arrow.r.bar #v]$

#align(center, text(size: 17pt, weight: "bold")[Och: A Core Calculus with Iota/Fix and Equirecursive Subtyping])
#v(1em)

Och is a dependently-typed λ-calculus with two recursive-binder
forms --- *ι* (Cedille-style self-types) and *fix* (general
recursion at the type and term level) --- and a single syntactic
category in which terms and types coincide. The checker is a
structural type-synthesis walk layered on a substitution-based WHNF
evaluator, and the subtyping relation is equirecursive with
Brandt--Henglein coinductive hypotheses.

This document specifies Och as a type system: the term syntax, the
concrete operational semantics, the declarative subtyping relation, and
the algorithmic typing/subtyping judgments. Throughout, binders and
variables are written with ordinary names ($x$, $y$, $x$, $A$, $B$,
$f$, $a$, …) and substitution is written $"body"[x arrow.r.bar v]$.
Binders are annotated with their bound name: $lambda(x lt.eq A). e$,
$iota(x lt.eq A). B$, $"fix"(x lt.eq A). b$,
$"let" x = v "in" "body"$. Context lookup is $Gamma(x)$; context
extension is $Gamma, x lt.eq A$.

= Syntax

The term language is

$
  e, tau ::= & x                      &                       "variable" \
           | & top                    &                 "universe (top)" \
           | & bot                    &               "primitive bottom" \
           | & lambda(x lt.eq tau). e &                         "lambda" \
           | & e_1 space e_2          &                    "application" \
           | & iota(x lt.eq tau). e   &               "self-type binder" \
           | & "fix"(x lt.eq tau). e  &               "recursive binder" \
           | & (e lt.eq tau)          & "ascription (erased at runtime)" \
           | & "let" x = e_1 "in" e_2 &                    "let-binding"
$

There is no separate type category: every $tau$ above is itself a term.
Throughout the paper $Gamma$ denotes a typing context (a finite map from
variable names to their declared types).

*Variables, lambdas, application* are the standard λ-calculus.

*$top$ and $bot$* are the top and bottom of the subtyping lattice:
every term subtypes $top$, and $bot$ subtypes everything.

*Iota and fix* both bind a self-reference with an annotation
$tau$ recording its type, but differ in how they unfold.
A value $v lt.eq iota(x lt.eq A). B$ inhabits $B[x arrow.r.bar v]$ ---
the body's self-reference points at the inhabitant itself, giving
dependent elimination (Cedille-style self-types @fu-stump-2014).
A value $v lt.eq "fix"(x lt.eq A). B$ equi-recursively equals its
unfolding $B[x arrow.r.bar v]$ --- general recursion at the type and
term level.

*Ascription* $(e lt.eq tau)$ asserts that $e$ subtypes $tau$ and
instructs the type checker to forget information: the checker sees $tau$
rather than the precise type of $e$.

*Let* $"let" x = e_1 "in" e_2$ is sugar that allows defining a
variable without first giving it a type --- the checker infers the type
of $e_1$ and binds $x$ to it.

= Concrete semantics --- the evaluation judgment

The concrete evaluator is a substitution-based call-by-value big-step
interpreter on closed terms. Lambdas, ι, and fix are values;
applications in function position unroll the recursive binder by
substituting its self-reference, then re-apply.

Write the judgment $e arrow.b.double v$ for "closed term $e$ concretely evaluates to
value $v$." Values
$v ::= lambda(x lt.eq tau).e | iota(x lt.eq tau).e | "fix"(x lt.eq tau).e | top | x space arrow(e)$ (neutral
application spine with a stuck variable head).

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("E-Val", eval($e$, $e$)), irule("E-Asc", eval($(e lt.eq tau)$, $v$), eval($e$, $v$)),
  irule("E-Let", eval($("let" x = e_1 "in" e_2)$, $v$), eval($e_1$, $v_1$), eval($e_2[x arrow.r.bar v_1]$, $v$)),
  irule("E-App-β", eval($f space a$, $v$), eval($f$, $lambda(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $b[x arrow.r.bar v_a]$,
    $v$,
  )),

  irule("E-App-ι", eval($f space a$, $v$), eval($f$, $iota(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $(b[x arrow.r.bar iota(x lt.eq tau).b]) space v_a$,
    $v$,
  )),
  irule("E-App-fix", eval($f space a$, $v$), eval($f$, $"fix"(x lt.eq tau). b$), eval($a$, $v_a$), eval(
    $(b[x arrow.r.bar "fix"(x lt.eq tau).b]) space v_a$,
    $v$,
  )),

  irule("E-App-Neutral", eval($f space a$, $f' space v_a$), eval($f$, $f'$), eval($a$, $v_a$)),
))

Where [E-Val] applies when $e in {top, lambda .., iota .., "fix" ..}$, and [E-App-Neutral] when the head is stuck.

Free variables are not values. Ascription is erased at evaluation
([E-Asc]); the declarative [S-Asc-L] rule (§4.4) provides the
corresponding transparency.

*$bot$ is a self-evaluating value.* Like $top$, $bot$ evaluates to
itself via [E-Val] and has no application dispatch arm, so applying
an argument to $bot$ is _stuck_ (parallel to $top$-application). This is
intentional: $bot$ is a type, not a callable. The typing discipline must
ensure well-typed programs never reach $bot space a$ at runtime.

This is the *operational specification* of the language.

= Overview of the algorithmic relations

Three judgments make up the algorithmic side of Och. This section
introduces each one's semantic role and explains how they compose; the
full rules appear in §§5--7.

== $S ; Gamma tack.r a attach(subset.sq.eq, br: e) b$ --- structural subtype check (§6)

Decides whether well-typed WHNF term $a$ is a subtype of well-typed WHNF
term $b$ under context $Gamma$, given coinductive hypotheses $S$. Both
inputs must already be well-typed and in WHNF --- the caller ($arrow.squiggly$) is
responsible for ensuring this.

The check is purely structural: it pattern-matches on the head
constructors of $a$ and $b$ and recurses. Under binders it opens both
sides with a fresh variable and extends $Gamma$ with the narrower of
the two domains (always the RHS, since the contravariance check
$"dom"_B subset.sq.eq "dom"_A$ has already passed). The seen-set $S$ provides coinductive
closure for equirecursive types (§4.3 of the declarative subtyping).
Internally, $attach(subset.sq.eq, br: e)$ normalises intermediate terms (e.g. after substituting
into an unfolded body) via a WHNF evaluator (§5) --- this
is safe because substituting a well-typed term into a well-typed body
preserves well-typedness.

The key property: $attach(subset.sq.eq, br: e)$ is *monotone in $Gamma$* --- narrowing any
context entry preserves the judgment.

== $Gamma tack.r e arrow.squiggly v$ --- type synthesis (§7)

Validates that $e$ is well-typed under context $Gamma$ and returns its WHNF
$v$ as a type-witness (since in Och a value _is_ its own
most-precise type, by [S-Refl]). This is where type checking happens:
at every application $f space a$, the walk synthesises both sides, exposes a Π
from the function, and asks $attach(subset.sq.eq, br: e)$ whether the argument inhabits the
domain. Binder annotations must subtype $top$.

The semantic guarantee of $arrow.squiggly$ is that the term it accepts will remain
well-typed under any narrowing of the context --- that is, when abstract
variables are replaced by narrower (more specific) values. This is the
bridge between static checking and runtime execution: when we check a
function body $b$ under $(Gamma, x : A)$ with $x$ abstract, the synthesis
walk asks $attach(subset.sq.eq, br: e)$ questions like "does this expression inhabit the domain
$A$?" Later, when the evaluator runs $b[x arrow.r.bar v]$ with a concrete $v$ that is
narrower than $A$, every subtype question the walk asked is at least as
easy --- a narrower context can only make more things provable, never
fewer. So the abstract check is a sound over-approximation of every
possible concrete execution.

== $e arrow.b.double v$ --- concrete evaluation (§2)

The reference big-step interpreter on closed terms (no open context).
This is what actually runs programs. It is defined independently of the
type-checker and has no access to a context or type information --- it is
a pure untyped evaluator.

The connection to the type-checker is through two soundness theorems:
*preservation* ($e subset.sq.eq tau$ and $e arrow.b.double v$ imply $v subset.sq.eq tau$) and
*progress* ($arrow.squiggly$ accepted $e$ implies $arrow.b.double$ never gets stuck).
Together these say: if you type-check first, the evaluator either
produces a well-typed value or runs out of fuel --- it never reaches a
stuck state.

== How they compose

#figure(
  diagram(
    node-stroke: 0.5pt,
    node-inset: 8pt,
    spacing: (2.5em, 2em),

    node((0, 0), [source term], stroke: none),
    node((0, 1), [$Gamma tack.r e arrow.squiggly v$ (§7) -- _type synthesis_], shape: rect),
    node((0, 2), [$S ; Gamma tack.r a attach(subset.sq.eq, br: e) b$ (§6) -- _domain checks_], shape: rect),
    node((0, 3), [accept / reject], stroke: none),
    node((0, 4), [$e arrow.b.double v$ (§2) -- _runtime, closed terms only_], shape: rect),

    edge((0, 0), (0, 1), "->"),
    edge((0, 1), (0, 2), "->", label: [calls], label-side: right),
    edge((0, 2), (0, 3), "->"),
    edge((0, 3), (0, 4), "->", label: [if accepted], label-side: right),
  ),
  caption: [Static and runtime phases],
)

The top box is the static phase: $arrow.squiggly$ walks the term, calling $attach(subset.sq.eq, br: e)$ for
each typing obligation. If the walk accepts, the term enters the runtime
phase: $arrow.b.double$ evaluates it without any type information. Soundness (§8)
connects the two phases --- the static acceptance guarantees that the
runtime evaluation is well-behaved.

= Declarative subtyping

Subtyping in Och means set inclusion: $A subset.sq.eq B$ iff every value of $A$ is
also a value of $B$. The relation is written

$ S ; Gamma tack.r a subset.sq.eq b $

== Context $Gamma$

$Gamma$ is the typing context --- a finite ordered list of
$(upright("variable"), upright("type"))$ pairs, with the most recent binder at the front.
Lookup is $Gamma(x)$ for the declared type of $x$; extension is $Gamma, x lt.eq A$.

== Seen set $S$

$S$ is a set of pairs $(a, b)$ --- ancestor subtyping goals introduced
by productive unfolding rules (ι-introduction and the four unfold
rules, §4.3). The invariant: only those five rules extend $S$; every
other rule propagates it unchanged. This is the Brandt--Henglein device @brandt-henglein-1998
for equirecursive subtyping --- coinductive assumptions are only legal
after at least one productive step, so reflexivity of a non-productive
goal cannot be closed by a hypothesis. In effect, $S$ is a finite representation of a coinductive (potentially infinite) proof tree: when a goal recurs, the branch closes rather than recursing forever, encoding a regular infinite derivation as a finite one.

The "real" subtyping judgment is $emptyset ; Gamma tack.r a subset.sq.eq b$ (empty hypothesis set);
non-empty $S$ arises only inside a derivation.

== Rule taxonomy

The rules fall into four categories. Each serves a distinct purpose;
knowing which category a rule belongs to predicts its shape.

#figure(
  table(
    columns: (auto, 1fr, 1fr, auto),
    align: (left, left, left, center),
    table.header([*Category*], [*Purpose*], [*Rules*], [*Extends $S$?*]),
    table.hline(),
    [Structural (§4.1)],
    [Plumbing: compose, lookup, without inspecting constructors on either side],
    [S-Refl, S-Top, S-BotL, S-Trans, S-Hyp, S-Var],
    [no],
    [Congruence (§4.2)],
    [Match constructor on both sides; reduce to sub-obligations with variance],
    [S-Lam, S-App-Cong, S-Iota-Cong, S-Fix-Cong, S-LetE-Cong],
    [no],
    [Productive unfolding (§4.3)],
    [Unfold a recursive binder (ι/fix); extend $S$; enable coinductive closure],
    [S-Iota-Intro, S-Unfold-Iota-L/R, S-Unfold-Fix-L/R],
    [*yes*],
    [Conversion (§4.4)],
    [Close under head reduction so the algorithmic evaluator is sound],
    [S-Beta-L/R, S-Let-L/R, S-Asc-L, S-Asc-L-Ann, S-Asc-R],
    [no],
  ),
  caption: [Rule taxonomy for declarative subtyping],
)

The $S$-extension column matters: S-Hyp can only fire against entries
that some ancestor productive rule installed, so any path to S-Hyp
must cross an unfold --- the productivity requirement made mechanical.

== Structural rules

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
induction on derivations. The seen-set discipline of §4.3 is the
coinductive counterpart that keeps the relation consistent, but it
doesn't by itself give admissibility of transitivity.

Eliminating transitivity as a primitive rule (_transitivity elimination_) is highly desirable: it simplifies metatheory and makes the relation syntax-directed. Hutchins' Pure Subtype Systems @hutchins-2010 --- a closely related system --- did not manage to eliminate transitivity. Pasquale and García-Pérez @pasquale-garcia-perez-2026 succeeded in a continuation of that work, but required switching the entire theory to a Krivine machine.

== Congruence rules

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
    irule(
      "S-LetE-Cong",
      sub($S$, $Gamma$, $"let" x = v_1 "in" b_1$, $"let" x = v_2 "in" b_2$),
      sub($S$, $Gamma$, $v_1$, $v_2$),
      sub($S$, $Gamma\, x lt.eq v_2$, $b_1$, $b_2$),
    ),
  ),
))

The equivalence premise on [S-App-Cong] (both directions on the
argument) is necessary because a neutral head
can use its argument at any variance, so equivalence is the only sound
congruence.

== Productive unfolding (extend $S$)

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

*Worked example: $"dtrue" subset.sq.eq "dBool"$.* With

$
  "dtrue" &:= iota(x lt.eq top). lambda(P lt.eq x arrow top). lambda(t lt.eq P space x). lambda(f lt.eq top). t \
  "dBool" &:= "fix"(B lt.eq top). iota(x lt.eq B). lambda(P lt.eq B arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space x
$

the subtyping check $emptyset ; Gamma tack.r "dtrue" subset.sq.eq "dBool"$ loops through a
contravariant domain: dBool's motive parameter is $P lt.eq "dBool" arrow top$,
while dtrue's is $P lt.eq x arrow top$ where $x$ is the inhabitant ---
ultimately dtrue. So the [S-Lam] contravariant premise for the
$P$ binder demands $"dBool" subset.sq.eq "dtrue"$… which needs the original relationship
back. Without the seen set this loops forever; with it, the productive
unfold at the top installs $("dtrue", "dBool")$ into $S$, and the loop
closes via [S-Hyp]:

#let dstep(depth, judgment, rulename) = {
  pad(left: depth * 1.5em, grid(
    columns: (1fr, auto),
    $#judgment$, text(size: 8pt, fill: luma(100))[#rulename],
  ))
}
#let dnote(depth, note) = {
  pad(left: depth * 1.5em, text(size: 9pt, style: "italic", fill: luma(100))[#note])
}
#block(inset: (y: 0.5em),
  stack(dir: ttb, spacing: 0.4em,
    dstep(0, sub($emptyset$, $Gamma$, $"dtrue"$, $"dBool"$), [root goal]),
    dstep(1, sub($S_1$, $Gamma$, $"dtrue"$, $iota(x lt.eq "dBool"). lambda(P lt.eq "dBool" arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space x$), [S-Unfold-Fix-R]),
    dnote(1, [where $S_1 = {("dtrue", "dBool")}$]),
    dnote(1, [Annotation premise:]),
    dstep(2, sub($S_1$, $Gamma$, $"dtrue"$, $"dBool"$), [S-Hyp #sym.checkmark]),
    dnote(2, [root goal reappears --- closed by $(upright("dtrue"), upright("dBool")) in S_1$]),
    dnote(1, [Body premise (after $[x arrow.r.bar "dtrue"]$):]),
    dstep(2, sub($S_1$, $Gamma$, $"dtrue"$, $lambda(P lt.eq "dBool" arrow top). lambda(t lt.eq P space "dtrue"). lambda(f lt.eq P space "dfalse"). P space "dtrue"$), [S-Lam …]),
    dnote(2, [further structural reduction; any recurrence of $"dtrue" subset.sq.eq "dBool"$ closes via S-Hyp]),
  ),
)

Both branches of [S-Iota-Intro] find the root goal waiting in $S_1$ and
close via [S-Hyp]. This is the Brandt--Henglein discipline in action:
recursion in the subtyping judgment is legal _only across a
productive unfold_, so non-productive loops (e.g. reflexivity-by-loop)
cannot sneak through.

== Conversion

The algorithm normalises before comparing, so the declarative relation
must be closed under head reduction. These rules provide that closure.

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

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("S-Let-L", sub($S$, $Gamma$, $"let" x = "val" "in" "body"$, $b$), sub(
    $S$,
    $Gamma$,
    $"body"[x arrow.r.bar "val"]$,
    $b$,
  )),
  irule("S-Let-R", sub($S$, $Gamma$, $a$, $"let" x = "val" "in" "body"$), sub(
    $S$,
    $Gamma$,
    $a$,
    $"body"[x arrow.r.bar "val"]$,
  )),
))

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("S-Asc-L", sub($S$, $Gamma$, $(e lt.eq tau)$, $b$), sub($S$, $Gamma$, $e$, $b$)),
  irule("S-Asc-L-Ann", sub($S$, $Gamma$, $(e lt.eq tau)$, $b$), sub($S$, $Gamma$, $tau$, $b$)),
  irule("S-Asc-R", sub($S$, $Gamma$, $a$, $(e lt.eq tau)$), sub($S$, $Gamma$, $a$, $e$)),
))

*Ascription rules: mixed transparency.* Ascription has three
rules, not two. On the *RHS*, [S-Asc-R] sees through to the
inner value $e$ --- the ascription doesn't widen the set of values it
contains. On the *LHS*, both rules coexist: [S-Asc-L]
(transparent, sees $e$) is needed because the runtime erases
ascriptions, while [S-Asc-L-Ann] (narrowing, sees $tau$) is what the
algorithmic checker uses --- it peels an LHS ascription to the
annotation, so the caller sees $tau$, not the precise inner value.

Given $A subset.sq.eq B subset.sq.eq C$, the mixed rules give the expected behavior:

#figure(
  table(
    columns: 4,
    align: (left, left, left, left),
    table.header([*Goal*], [*Rule*], [*Reduces to*], [*Holds?*]),
    table.hline(),
    [$(A lt.eq B) subset.sq.eq C$], [Asc-L-Ann], [$B subset.sq.eq C$], [yes],
    [$A subset.sq.eq (B lt.eq C)$], [Asc-R], [$A subset.sq.eq B$], [yes],
    [$B subset.sq.eq (A lt.eq C)$], [Asc-R], [$B subset.sq.eq A$], [*no*],
    [$(A lt.eq C) subset.sq.eq B$], [Asc-L-Ann], [$C subset.sq.eq B$], [*no*],
  ),
)

= Substitution-based evaluation

The WHNF evaluator takes an expression and reduces it to weak head
normal form via syntactic substitution. Input and output are both
terms --- there is no separate value type, no closures, no environments,
and no quoting step.

== Design

The key simplification: because the term language serves as both AST and
value, β-reduction is literal syntactic substitution --- $"body"[x arrow.r.bar "arg"]$.
Lambdas, ι-binders, and fix-binders are already in WHNF and
evaluate to themselves. Applications reduce by substituting the
evaluated argument into the function's body.

Two fuel parameters bound the computation:

- *fuel*: overall step budget. Every recursive call decrements it.
- *unf*: unfold budget for ι/fix heads in application
  position. Decremented on each self-referential unfold; when exhausted,
  the application is left as a stuck neutral $(f space a)$. Prevents
  divergence on non-terminating self-application chains.

The lex ordering $("fuel", "unf")$ gives a structurally decreasing
termination measure.

== De Bruijn indices for open terms

The subtype checker (§6) needs to compare terms under binders --- e.g.
to check $lambda(x lt.eq A).b_1 subset.sq.eq lambda(x lt.eq A).b_2$, it recurses on both bodies
directly, extending the context $Gamma$ with the domain type. No
substitution is performed when entering a binder: the raw body is
used as-is. Any `bvar k` encountered by `evalSubst` is a free variable
in the current scope (since the evaluator never descends under
binders) and is treated as neutral --- it evaluates to itself.

To look up the type of a free `bvar k`, the checker accesses
$Gamma(k)$ (the $k$-th most recently bound variable). When a neutral
`bvar k` ascends to its declared type $tau$, the result is shifted by
$k + 1$ to account for the binders between the variable's binding
site and the current scope.

This encoding lets the entire algorithmic pipeline --- evaluation,
subtype checking, type synthesis --- operate on a single term type
with no separate value/neutral/closure machinery. The algorithmic and
declarative representations share the same de Bruijn variable
encoding directly.

== Evaluation rules

Write the judgment $e arrow.double.r v$ for "the evaluator reduces $e$ to WHNF $v$."

#let es(e, v) = $#e arrow.double.r #v$

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("ES-Type", es($top$, $top$)),
  irule("ES-Bot", es($bot$, $bot$)),
  irule("ES-Lam", es($lambda(x lt.eq A). b$, $lambda(x lt.eq A). b$)),
))

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("ES-Iota", es($iota(x lt.eq A). b$, $iota(x lt.eq A). b$)),
  irule("ES-Fix", es($"fix"(x lt.eq A). b$, $"fix"(x lt.eq A). b$)),
  irule("ES-BVar", es($x$, $x$)),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("ES-Asc", es($(e lt.eq tau)$, $(e' lt.eq tau')$), es($e$, $e'$), es($tau$, $tau'$)),  // ascription preserved as WHNF
  irule("ES-Let", es($"let" x = "val" "in" "body"$, $v$), es($"val"$, $v_1$), es($"body"[x arrow.r.bar v_1]$, $v$)),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule("ES-App-β", es($f space a$, $v$), es($f$, $lambda(x lt.eq A). "body"$), es($a$, $v_a$), es(
    $"body"[x arrow.r.bar v_a]$,
    $v$,
  )),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("ES-App-ι-Unfold", es($f space a$, $v$), es($f$, $iota(x lt.eq A). "body"$), es($a$, $v_a$), es(
    $("body"[x arrow.r.bar f]) space v_a$,
    $v$,
  )),
  irule("ES-App-fix-Unfold", es($f space a$, $v$), es($f$, $"fix"(x lt.eq A). "body"$), es($a$, $v_a$), es(
    $("body"[x arrow.r.bar f]) space v_a$,
    $v$,
  )),
))

Where ι/fix unfold rules require $not "neutral"(v_a) and "unf" > 0$. When $"neutral"(v_a) or "unf" = 0$, the application is stuck:

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("ES-App-ι-Stuck", es($f space a$, $f' space v_a$), es($f$, $f'$), es($a$, $v_a$)),
  irule("ES-App-fix-Stuck", es($f space a$, $f' space v_a$), es($f$, $f'$), es($a$, $v_a$)),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("ES-App-Asc", es($f space a$, $v$), es($f$, $("inner" lt.eq tau)$), es($"inner" space a$, $v$)),
  irule("ES-App-Neutral", es($f space a$, $f' space v_a$), es($f$, $f'$), es($a$, $v_a$)),
))

Where [ES-App-Neutral] applies when $"neutral"(f') or f' in {top, bot}$.

*Ascription is preserved.* Unlike the concrete evaluator (§2) which
erases ascription via [E-Asc], the WHNF evaluator preserves
ascriptions: [ES-Asc] reduces both the inner term and the annotation
to WHNF but keeps the ascription wrapper. This is essential for the
algorithmic subtype checker's LHS peeling (§6.1): if the WHNF
evaluator stripped ascriptions, the checker would lose narrowing
information that the programmer explicitly wrote.

= Algorithmic subtyping on expressions

The algorithmic subtype checker is the realisation of §4. It operates directly on terms in WHNF.
The subtype checker and the WHNF evaluator form a mutual block with a lex $("fuel", "phase")$ termination
measure --- the checker calls the evaluator to force WHNF before
comparing, and calls itself recursively under binders.

Write the judgment $S ; Gamma tack.r a attach(subset.sq.eq, br: e) b$ for the algorithmic check, where
$a, b$ are in WHNF, $S$ is a list of pairs (the
seen-set), and $Gamma$ maps level indices to their declared types.

== Top-level dispatch

Before case-splitting on shapes, the checker forces both sides to
WHNF, then *peels ascriptions asymmetrically*:

- LHS ascription → replace with the annotation (narrowing)
- RHS ascription → replace with the inner value (content)

After peeling, three fast paths fire in order:

+ *Syntactic equality* ($a'' = b''$): immediate accept.
+ *Seen-set hit* ($(a'', b'') in S$): coinductive accept.
+ *Top* ($b'' = top$): immediate accept.

If none fires, it delegates to the per-shape case analysis.

== Per-shape rules

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("AS-BotL", sube($S$, $Gamma$, $bot$, $b$)),
  irule(
    "AS-Lam",
    sube($S$, $Gamma$, $lambda(x lt.eq A_1). b_1$, $lambda(x lt.eq A_2). b_2$),
    sube($S$, $Gamma$, $A_2$, $A_1$),
    sube($S$, $Gamma\, x lt.eq A_2$, $b_1["fresh"]$, $b_2["fresh"]$),
  ),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "AS-Iota-Iota",
    sube($S$, $Gamma$, $iota(x lt.eq A_1). B_1$, $iota(x lt.eq A_2). B_2$),
    sube($S$, $Gamma$, $A_1$, $A_2$),
    sube($S$, $Gamma\, x lt.eq A_2$, $B_1["fresh"]$, $B_2["fresh"]$),
  ),
))

With fallback to iota-intro if structural match fails. Similarly:

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "AS-Fix-Fix",
    sube($S$, $Gamma$, $"fix"(x lt.eq A_1). b_1$, $"fix"(x lt.eq A_2). b_2$),
    sube($S$, $Gamma$, $A_1$, $A_2$),
    sube($S$, $Gamma\, x lt.eq A_2$, $b_1["fresh"]$, $b_2["fresh"]$),
  ),
))

With fallback to unfold-R if structural match fails.

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("AS-Iota-Intro", sube($S$, $Gamma$, $a$, $iota(x lt.eq A). B$), sube($S'$, $Gamma$, $a$, $A$), sube(
    $S'$,
    $Gamma$,
    $a$,
    $B[x arrow.r.bar a]$,
  )),
  irule("AS-Unfold-Fix-R", sube($S$, $Gamma$, $a$, $"fix"(x lt.eq A). b$), sube(
    $S'$,
    $Gamma$,
    $a$,
    $b[x arrow.r.bar "fix"(x lt.eq A).b]$,
  )),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("AS-Unfold-Fix-L", sube($S$, $Gamma$, $"fix"(x lt.eq A). b$, $c$), sube(
    $S'$,
    $Gamma$,
    $b[x arrow.r.bar "fix"(x lt.eq A).b]$,
    $c$,
  )),
  irule("AS-Unfold-Iota-L", sube($S$, $Gamma$, $iota(x lt.eq A). B$, $c$), sube(
    $S'$,
    $Gamma$,
    $B[x arrow.r.bar iota(x lt.eq A).B]$,
    $c$,
  )),
))

Where $S' = (a, b) :: S$ in each productive rule.

== Neutral handling

When both sides are neutral (`bvar`-headed application spines), the
checker tries *spine comparison*: heads must be the same
`bvar` index; arguments must be pairwise _equivalent_ (checked in both
directions, matching [S-App-Cong]).

If spine comparison fails, or if only the LHS is neutral, the checker
falls back to *neutral ascent*: it looks up the head `bvar k` in
$Gamma$ to obtain its declared type, shifts by $k + 1$, and applies
the spine's arguments through the resulting Π-chain. It then recurses
with the synthesised type on the LHS. This corresponds to [S-Var] in
the declarative relation --- a neutral ascends to its declared type.

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule(
    "AS-Spine",
    sube($S$, $Gamma$, $x space e_1 dots e_n$, $x space e'_1 dots e'_n$),
    sube($S$, $Gamma$, $e_i$, $e'_i$),
    sube($S$, $Gamma$, $e'_i$, $e_i$),
  ),
  irule("AS-Ascent", sube($S$, $Gamma$, $n$, $b$), $"synthType"(Gamma, n) = "some" space tau$, sube(
    $S$,
    $Gamma$,
    $tau$,
    $b$,
  )),
))

== Π-exposure helper

The Π-exposure helper unfolds a fix/ι wrapper in a type
until a $lambda$ (Π) head is exposed. For fix, the self-reference is the
fix itself (μ-unfold); for ι, the self-reference is the
_inhabitant_ whose type is being computed --- $n lt.eq iota(x lt.eq A). B$
means $n lt.eq B[x arrow.r.bar n]$. Returns nothing on $bot$ (Bot is not a Π head).

= Algorithmic typing (synthesis)

The type-synthesis walk is a single structural recursion over terms
that delegates all typing questions to the subtype checker (§6).
Where a bidirectional checker dispatches between synthesis and checking
modes, this walk has no separate checking mode --- it asks the
_complete_ structural engine to decide each domain check directly.

== Design

The synthesis walk over $Gamma$ and $e$ returns the WHNF of $e$ --- which, by
Och's Refl-typing convention ($a subset.sq.eq a$), doubles as the most-precise
type. At every node that introduces a typing obligation (applications,
ascriptions), it calls the subtype checker to verify the obligation. The $Gamma$
argument maps de Bruijn indices to the WHNF types of free variables
introduced by binder-opening.

== Synthesis rules

#align(center, grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 1.5em,
  irule("I-Type", synth($Gamma$, $top$, $top$)),
  irule("I-Bot", synth($Gamma$, $bot$, $bot$)),
  irule("I-Var", synth($Gamma$, $x$, $x$)),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "I-Lam",
    synth($Gamma$, $lambda(x lt.eq A). b$, $"whnf"(lambda(x lt.eq A). b)$),
    sube($emptyset$, $Gamma$, $A$, $top$),
    synth($Gamma\, x lt.eq "whnf"(A)$, $b["fresh"]$, $dot.c$),
  ),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule(
    "I-Iota",
    synth($Gamma$, $iota(x lt.eq A). b$, $"whnf"(iota(x lt.eq A). b)$),
    sube($emptyset$, $Gamma$, $A$, $top$),
    synth($Gamma\, x lt.eq "whnf"(A)$, $b["fresh"]$, $dot.c$),
  ),
  irule(
    "I-Fix",
    synth($Gamma$, $"fix"(x lt.eq A). b$, $"whnf"("fix"(x lt.eq A). b)$),
    sube($emptyset$, $Gamma$, $A$, $top$),
    synth($Gamma\, x lt.eq "whnf"(A)$, $b["fresh"]$, $dot.c$),
  ),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "I-Asc",
    synth($Gamma$, $(e lt.eq tau)$, $"whnf"(e lt.eq tau)$),
    sube($emptyset$, $Gamma$, $tau$, $top$),
    synth($Gamma$, $e$, $v$),
    sube($emptyset$, $Gamma$, $v$, $"whnf"(tau)$),
  ),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "I-Let",
    synth($Gamma$, $"let" x = "val" "in" "body"$, $"whnf"("let" x = "val" "in" "body")$),
    synth($Gamma$, $"val"$, $v_"val"$),
    synth($Gamma\, x lt.eq v_"val"$, $"body"["fresh"]$, $dot.c$),
  ),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "I-App",
    synth($Gamma$, $f space a$, $"whnf"(pi_"expr" space a_v)$),
    synth($Gamma$, $f$, $v_F$),
    synth($Gamma$, $a$, $v_A$),
    $pi_"expr" arrow.l "exposePi"(v_F)$,
    sube($emptyset$, $Gamma$, $v_A$, $"dom"$),
  ),
))

*Refl-typing convention.* Canonical forms (lam, iota, fix)
synthesise themselves: the walk returns $"whnf"(e)$ for these nodes.
Since $a subset.sq.eq a$ holds declaratively by [S-Refl], the synthesised WHNF is
trivially a valid type-witness.

*$bot$ in synthesis.* $bot$ synthesises itself via [I-Bot].
$bot$ is not a Π head, so applying an argument to a $bot$-typed function
fails at the Π-exposure step in [I-App].

== Abstract interpretation of bodies

When the synthesis walk enters a binder (lam, iota, fix, let), it
extends $Gamma$ with the annotation's WHNF and recurses on the raw
body --- no substitution is performed. The bound variable `bvar 0` is
*neutral* with respect to evaluation: it evaluates to itself, blocks
β-reduction, and propagates through application spines as a stuck
head. This is the de Bruijn analogue of opening a closure with a
fresh free variable: the `bvar` acts as a symbolic "any value of this
type," and the structural subtype checker can compare bodies
containing free `bvar`s by spine-walking and ascending through $Gamma$.

= Metatheory

Soundness connects the concrete semantics (§2), the declarative subtyping (§4), and
the algorithmic checker (§§5--7).

*Subtyping soundness.* If the algorithm accepts two values, they are declaratively subtypes.

$ "subCheck" space a space b = "ok" arrow.double emptyset ; emptyset tack.r a subset.sq.eq b $

*Synthesis soundness.* If synthesis accepts $e$, then $e$ declaratively subtypes its
synthesised WHNF.

$ "synth" space e = "ok" space v arrow.double emptyset ; emptyset tack.r e subset.sq.eq v $

*Evaluation equivalence.* If $e$ evaluates to $e'$, both directions of subtyping hold (*sorry-free*).

$
  e "closed" and e arrow.b.double e' arrow.double emptyset ; emptyset tack.r e' subset.sq.eq e and emptyset ; emptyset tack.r e subset.sq.eq e'
$

*Preservation.* Standard type preservation (*sorry-free*; derives from evaluation equivalence via transitivity).

*Progress.* A synthesis-accepted term doesn't get stuck during evaluation. The evaluator may
return a value or run out of fuel but never reaches an error state (*sorry-free*).

*End-to-end.* Composing the above:

$
  "synth" space e = "ok" space a and "subCheck" space a space b = "ok" and e arrow.b.double e' arrow.double emptyset ; emptyset tack.r e' subset.sq.eq b
$

== What soundness promises to the programmer

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
discipline: *run synthesis first; only evaluate if it succeeded.*

= Appendix A. Declarative typing (derived)

Och has no declarative typing relation as a first-class definition; the
algorithmic synthesis walk (§7) is the typing spec, with soundness
against $subset.sq.eq$ in §8. For readers who want the textbook form, the following
relation $Gamma tack.r e : tau$ is the clean projection of the algorithm.

#let ty(G, e, t) = $#G tack.r #e : #t$

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("D-Var", ty($Gamma$, $x$, $Gamma(x)$)), irule("D-Type", ty($Gamma$, $top$, $top$)),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("D-Lam", ty($Gamma$, $lambda(x lt.eq A). b$, $lambda(x lt.eq A). B$), ty($Gamma$, $A$, $top$), ty(
    $Gamma\, x lt.eq A$,
    $b$,
    $B$,
  )),
  irule("D-App", ty($Gamma$, $f space a$, $B[x arrow.r.bar a]$), ty($Gamma$, $f$, $lambda(x lt.eq A). B$), ty(
    $Gamma$,
    $a$,
    $A$,
  )),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("D-Let", ty($Gamma$, $"let" x = v "in" b$, $tau$), ty($Gamma$, $v$, $A$), ty($Gamma\, x lt.eq A$, $b$, $tau$)),
  irule("D-Asc", ty($Gamma$, $(e lt.eq tau)$, $tau$), ty($Gamma$, $tau$, $top$), ty($Gamma$, $e$, $tau$)),
))

#align(center, grid(
  columns: (1fr,),
  gutter: 1.5em,
  irule(
    "D-Iota",
    ty($Gamma$, $v$, $iota(x lt.eq A). B$),
    ty($Gamma$, $A$, $top$),
    ty($Gamma\, x lt.eq A$, $B$, $top$),
    ty($Gamma$, $v$, $A$),
    ty($Gamma$, $v$, $B[x arrow.r.bar v]$),
  ),
))

#align(center, grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  irule("D-Fix", ty($Gamma$, $"fix"(x lt.eq A). b$, $A$), ty($Gamma$, $A$, $top$), ty($Gamma\, x lt.eq A$, $b$, $A$)),
  irule("D-Sub", ty($Gamma$, $e$, $B$), ty($Gamma$, $e$, $A$), sub($emptyset$, $Gamma$, $A$, $B$)),
))

= Appendix B. Lean formalisation

The entire calculus described in this paper is formalised in Lean 4. This appendix maps the paper's named-variable presentation to the
mechanised definitions, and notes the one systematic difference: the formalisation uses *de Bruijn indices* throughout, so named variables
$x$ become positional indices, substitution $"body"[x arrow.r.bar v]$ becomes index arithmetic, and context lookup $Gamma(x)$ becomes list indexing.

== Representation

All terms, types, and values share a single inductive `Expr`. Named variables $x$ are represented by `Expr.bvar` (a natural-number index); substitution uses `Expr.subst`/`Expr.shift` for standard de Bruijn arithmetic. The context $Gamma$ is `List Expr`, indexed by position with the innermost binder at index 0.

A named variable $x$ bound at the innermost binder becomes `bvar 0`; a variable bound $k$ binders out becomes `bvar k`; substitution $"body"[x arrow.r.bar v]$ becomes `body.subst 0 v`.

== Correspondence

#figure(
  table(
    columns: (1fr, 1fr, auto),
    align: (left, left, left),
    table.header([*Paper concept*], [*Lean definition*], [*File*]),
    table.hline(),
    [Term syntax ($e, tau$)], [`Expr`], [`Syntax.lean`],
    [Concrete evaluation ($e arrow.b.double v$)], [`concEval`], [`Eval.lean`],
    [Declarative subtyping ($S ; Gamma tack.r a subset.sq.eq b$)], [`Subtype'`], [`Subtyping.lean`],
    [WHNF evaluator ($e arrow.double.r v$)], [`evalSubst`], [`EvalSubst.lean`],
    [Algorithmic subtype check ($attach(subset.sq.eq, br: e)$)], [`subCheckSubst`], [`EvalSubst.lean`],
    [Type synthesis ($Gamma tack.r e arrow.squiggly v$)], [`synthCore`], [`API.lean`],
    [Public entry point], [`Och.synth`], [`API.lean`],
    [Evaluation equivalence], [`concEval_equiv`], [`Soundness/ConcEvalPreservation.lean`],
    [Preservation], [`concEval_preservation`], [`Soundness.lean`],
    [Progress], [`synth_progress`], [`Soundness.lean`],
    [End-to-end soundness], [`soundness`], [`Soundness.lean`],
  ),
  caption: [Paper-to-Lean correspondence],
)

== De Bruijn details

The formalisation's seen-set $S$ is `List (Nat × Expr × Expr)` --- each entry is depth-tagged with
$|Gamma|$ at which it was recorded, and the hypothesis rule shifts entries to the current depth on use.
This bookkeeping is invisible in the named presentation: free variables carry their own names, so no
shift is ever required at lookup time.

The algorithmic and declarative representations share the same de Bruijn variable encoding directly --- there is no translation layer between them. Free variables are plain `bvar k` indices looked up in the context as $Gamma(k)$ with a shift of $k + 1$ on neutral ascent.

== Proof status

Evaluation equivalence, preservation, and progress are *sorry-free*. Synthesis soundness and subtype-check soundness carry upstream sorries at engineering walls (app-arm of synthesis). The end-to-end composition is sorry-free in its own body.

#bibliography("refs.bib")
