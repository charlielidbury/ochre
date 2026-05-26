#import "@preview/curryst:0.5.0": prooftree, rule
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#set document(title: "Och: A Core Calculus with Iota/Fix and Equirecursive Subtyping")
#let dark-mode = false
#set text(font: "New Computer Modern", size: 10pt, fill: if dark-mode { white } else { black })
#set page(margin: 2.5cm, fill: if dark-mode { rgb("#1a1a2e") } else { white }, numbering: "1")
#set par(justify: true)
#set heading(numbering: "1.1")

#show link: underline

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

Static analysis catches bugs before software is deployed, notifying developers of mistakes earlier in the development pipeline than testing or user reports can. Type systems are the most widely adopted form of static analysis, and the strength of guarantees they provide varies enormously: from freedom from runtime type errors (TypeScript) through ownership-based resource safety (Rust) to full functional correctness (Lean, Agda, Coq). At the strong end of this spectrum lies _formal verification_: a compiler-checked mathematical proof that a program satisfies its specification across all possible inputs.

Formal verification has been applied at scale: a verified C compiler @leroy-2009, a verified operating system kernel @klein-2009, and a verified HTTPS stack @project-everest-2017 all demonstrate that proving the correctness of real systems software is feasible. These projects used a variety of proof technologies, but a common thread among the most ergonomic approaches is _dependent types_: a type-theoretic mechanism by which types may depend on values, allowing the programmer to state properties such as "this function returns a list of the same length as its input" directly in a type signature, with the compiler verifying the property as a condition of successful compilation.

There is a large intersection between software which requires low-level control and performance, and software where correctness is most critical. Operating system kernels, cryptographic libraries, network protocol implementations, and compiler backends all occupy this intersection --- they are _systems software_. Today, the languages which offer the necessary control (C, C++, Rust) lack the type-theoretic machinery for formal verification, while the languages which support dependent types (Lean, Agda, F\*) lack the control over memory layout, allocation, and mutation that systems programming demands.

_Ochre_ is a planned language which aims to inhabit this gap: a systems programming language with native support for dependent types. One might summarise the goal as combining Rust's ownership model and low-level control with Lean's proof capabilities in a single language and type system. The key mechanisms are a unified term/type language (following the Pure Subtype Systems tradition @hutchins-2010), structural subtyping, strong mutation, and ownership-based resource tracking.

Two recent trends make this research direction timely. First, the cost of unverified software is rising: AI-assisted vulnerability discovery has dramatically increased the rate at which security bugs are found in critical infrastructure --- Mozilla closed as many Firefox vulnerabilities in April 2026 as in the previous two years combined @firefox-vuln-2026, and a nine-year dormant Linux kernel privilege escalation was surfaced by automated analysis @linux-copyfail-2026. Second, the cost of writing software is falling: AI coding agents have reduced the labour involved in software engineering to the point where ambitious rewrites that were previously infeasible are now routine @bun-rewrite-2026. The bottleneck for software engineering is shifting from writing code to specifying what correct code looks like; the value proposition of a language whose type system _is_ a specification language is growing stronger.

During a previous attempt to develop Ochre @lidburyOchreDependentlyTyped2024, the project was held back by soundness bugs in the type system and a general lack of clarity on the semantics of the objects in the language. A counterexample was found in which narrowing a variable's type --- the operation which underlies strong mutation --- invalidated a previously valid subtyping judgment. The root cause was not in the mutation or ownership machinery, but in the foundational interaction between subtyping and type-level computation: the core semantic idea that terms and types share a common language had not been studied carefully enough to support the full system built on top of it.

This paper presents _Och_, a core calculus designed to isolate and study these foundational features before reintroducing the complexity of mutation and ownership. Och combines $lambda$-calculus with equirecursive subtyping, self-types ($iota$), and general recursion ($"fix"$) in a setting where terms and types are syntactically and semantically unified --- concretely, there is no separate $Pi$-type constructor for function types; the type of a function is itself a function, and types reduce by the same $beta$-rule as terms. Och is the first in a planned sequence of calculi --- Och, Ochr (adding ownership/linearity), and finally Ochre (adding mutable references) --- each of which answers a distinct research question while building toward the full language.

== Methodology

Och has been designed experimentally: a set of _goal programs_ drove the design of the typing rules. When a candidate rule set accepted all current goal programs and rejected their deliberately buggy variants, new and more demanding goal programs were added and the process iterated. This methodology has two consequences.

First, Och does not yet rest on a unifying semantic theory, and attempts at a soundness proof are ongoing. Establishing such a theory is a natural next step now that the rule set has stabilised around a substantial body of examples.

Second, the resulting test suite (see @examples) provides strong evidence of expressivity. Using Church/Scott encodings, Och expresses booleans, natural numbers, finite sets ($"Fin" n$), pairs, length-indexed arrays, and safe indexing --- all with dependent elimination. The type system catches bugs as subtle as adding the _wrong_ two numbers (see @appendvec), not merely checking that an addition is well-shaped.

== Goals

*Soundness.* Ochre is only valuable if programmers can trust the compiler to catch runtime errors. Proving the soundness of a system which combines equirecursive subtyping, self-types, and general recursion in a unified term/type language is, as far as I can tell, novel. Och is the setting in which to carry out this research.

*Expressivity.* The type system must articulate properties and catch bugs that programmers care about. It must be expressive enough to distinguish $x + y$ from $x + x$ when one is correct and the other is not.

*Extensibility.* Och is the first in a series of calculi building toward Ochre. Features which do not generalise to the full language are not worth investigating here. This consideration has already manifested in the decision to use general recursion via $"fix"$ rather than adding primitive inductive types with only well-founded induction.

= Background <related>

== Pure Subtype Systems <pss>

In a conventional type theory, there is a sharp syntactic distinction between terms and their types. Functions are introduced by $lambda$ and their types by $Pi$: the term $lambda(x : A). b$ has type $Pi(x : A). B$. These are different constructors with different reduction rules --- $lambda$ participates in $beta$-reduction, while $Pi$ does not compute.

Pure Subtype Systems @hutchins-2010 collapse this distinction. There is only $lambda$: the type of a function _is_ a function. Where a conventional system writes $Pi(x : A). B$ for the type of functions from $A$ to $B$, PSS writes $lambda(x : A). B$ --- the same constructor used for the functions themselves. This means types compute by exactly the same rules as terms: $beta$-reduction, substitution, and application all apply uniformly.

The consequence is that every term is trivially its own most precise type. A value like $3$ does not merely _have_ type $"Nat"$; it _is_ a type, the singleton type whose only inhabitant is $3$. The subtyping relation then does all the work that a typing judgment would normally do: $3 subset.sq.eq "Nat"$ is the statement that $3$ is a natural number. There is no need for a separate $Gamma tack.r e : tau$ judgment --- well-formedness (@well-formed) checks structural validity, and subtyping (@subtyping) answers every question about type compatibility.

Och adopts PSS's core design and extends it with self-types ($iota$), general recursion ($"fix"$), and coinductive subtyping.

== Self Types <self-types>

Church encodings represent data as their own eliminators: a boolean is a function that takes two branches and returns one of them, a natural number is a function that takes a zero case and a successor case and folds over itself. This is elegant but has a well-known limitation: the eliminator's return type cannot depend on the value being eliminated. A Church-encoded boolean can branch on itself to return values of some fixed type $X$, but it cannot branch to return values of type $P "true"$ or $P "false"$ for a type-level function $P$ --- the eliminator does not know which boolean it is.

Self types, introduced by @fu-stump-2014, solve this problem. The binder $iota(x lt.eq tau). e$ introduces a type in which the variable $x$ refers to _the term inhabiting the type_. When checking whether $a subset.sq.eq iota(x lt.eq tau). e$, the rule [S-Iota-Intro] substitutes $a$ for $x$ in the body, reducing the goal to $a subset.sq.eq e[x arrow.r.bar a]$. This feeds the value being typed _into_ its own type, enabling the return type to depend on the inhabitant.

For example, the dependent boolean type $"DBool"$ is defined so that its eliminator takes a motive $P : "DBool" arrow top$ and branches of type $P "true"$ and $P "false"$, returning *$P "self"$* where $"self"$ is the boolean value currently being typed. The constructors $"true"$ and $"false"$ are plain $lambda$-terms, identical to their non-dependent counterparts --- the dependent elimination machinery lives entirely in the type, not in the constructors. See @bool-encoding for the full definitions and @examples for further encodings built on this pattern.

= Language Semantics <lang-sem>

This section describes what each piece of the language does in natural language to give the reader an intuition for the objects involved before we get into the typing rules, examples, and metatheory. The full syntax is given in @syntax.

#figure(
  $
    e, tau ::= & x                      &         "variable" \
             | & lambda(x lt.eq tau). e &           "lambda" \
             | & e_1 space e_2          &      "application" \
             | & top                    &   "universe (top)" \
             | & bot                    & "primitive bottom" \
             | & iota(x lt.eq tau). e   & "self-type binder" \
             | & "fix"(x lt.eq tau). e  & "recursive binder" \
  $,
  caption: [Och syntax.],
) <syntax>

*Variables, lambdas, application* as per the standard λ-calculus, except $lambda$ has a domain type annotation which is respected by the type checker.

*$top$ and $bot$* are the top and bottom of the subtyping lattice. $top$ represents the widest possible type, which tells you nothing about the term being typed, and $bot$ is the empty type.

*Fix* $"fix"(x lt.eq tau). e$ allows a term to be defined in terms of itself. $x$ is the reference to the whole fix expression itself, and $tau$ is the "upper bound" which the whole expression can be assumed to have while it's being type checked (which prevents loops during type checking). // potentially needs to be made more crisp - look for explanations of fix in the wild

*Iota* $iota(x lt.eq tau). e$ allows the definition of a type to include a reference to _the term inhabiting it_. This means $e subset.sq.eq iota (x:tau_0). tau_1$ is reduced to $e subset.sq.eq tau_1[x arrow.r.bar e]$ during checking (notice: the LHS has moved to the RHS). This is a Cedille-style self type @fu-stump-2014, and allows for church encodings with dependent elimination instead of having to add inductive datatypes to the language as a primitive.

== Runtime semantics <conc-eval>

You may think the runtime semantics of Och are unimportant since this is type systems research, but with how I've laid out the soundness proofs $arrow.b.double$ plays a crucial role: soundness states "if a program type checks, it will succeed at runtime", therefore $arrow.b.double$ must _reject_ ill-formed programs, otherwise our soundness becomes vacuously solvable ($"true"$ on the RHS of an implication).

The concrete evaluator is a substitution-based call-by-value big-step interpreter on closed terms. ${lambda, top, bot}$ are the only values. $"fix"$ and $iota$ eagerly unroll by substituting their self-reference into the body. Application is pure β-reduction — only lambdas can be applied.

Och has no concept of levels/universes/stages, so the type checker cannot enforce that {$top$, $bot$, $iota$} don't go into runtime, so runtime needs to handle them gracefully. Adding universes (see §3.6 of PSS @hutchins-2010) would let us erase type-level arguments during compilation, after which {$top$, $bot$, $iota$} would never appear at level 0.

We write the judgment $e arrow.b.double v$ for "closed term $e$ concretely evaluates to value $v$". Note: there is no context and no free/abstract variables: everything is eagerly substituted in. The rules are given in @eval-rules.

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule("E-Val", eval($v$, $v$)),
      irule("E-App", eval($f space a$, $v$), eval($f$, $lambda(x lt.eq tau). b$), eval($a$, $v_a$), eval(
        $b[x arrow.r.bar v_a]$,
        $v$,
      )),
    ),
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule("E-Iota", eval($iota(x lt.eq tau). b$, $v$), eval(
        $b[x arrow.r.bar iota(x lt.eq tau).b]$,
        $v$,
      )),
      irule("E-Fix", eval($"fix"(x lt.eq tau). b$, $v$), eval(
        $b[x arrow.r.bar "fix"(x lt.eq tau).b]$,
        $v$,
      )),
    ),
    $
      "where" v in "Value" ::= & lambda(x lt.eq tau). e &           "lambda" \
                             | & bot                    & "primitive bottom" \
                             | & top                    &   "universe (top)" \
    $,
  ),
  caption: [Evaluation rules. Big-step, substitution-based, call-by-value on closed terms.],
) <eval-rules>

The most important aspect of the runtime semantics are what is _missing_ from the runtime semantics:
- Free variables are not values and have no rule, therefore they cannot occur at runtime, which is what forces the type system to rule out ill-scoped variables.
- Application can only apply to lambdas, which is what forces the type system to verify applications are well typed w.r.t. the function domain.

Fix and iota eagerly unroll — a program like $"fix"(x lt.eq top). x$ loops forever, which is the correct behaviour for non-terminating recursion. This lines up with what a programmer would expect to happen if they wrote `while true {}` in Rust or a lesser programmer would expect if they wrote `let x = x in x` in Haskell.

= Typing Rules <decl-sub>

Och's type system is structured around two judgements:

*Well-formedness* $Gamma tack.r e "wf"$ states "$e$ is well-formed under $Gamma$" and is the "entry point" for the type system. Defined in @well-formed. Delegates all type-comparison questions to subtyping.

*Subtyping* $S ; Gamma tack.r a subset.sq.eq b$ states "$a$ is a subtype of $b$ under $Gamma$, assuming coinductive hypotheses $S$". Subtyping in Och means set inclusion: $A subset.sq.eq B$ iff every value of $A$ is also a value of $B$. @seen-set explains the $S$ coinductive hypothesis system.

== Context $Gamma$ <context>

$Gamma$ is the typing context defined as $Gamma ::= emptyset | Gamma, x lt.eq a$. Lookup is $Gamma(x)$. Each entry describes what the type checker knows about a variable statically.


== Well-formedness <well-formed>

The well-formedness judgment $Gamma tack.r e "wf"$ determines whether term $e$ is well-formed under context $Gamma$. In other systems this role would be served by a $Gamma tack.r a : tau$ rule which assigns a type to a term, but there is no need to assign a type to terms in Och because every term is already trivially its own type by [S-Refl].

Well-formedness validates purely structural conditions: annotations are types, binders are in scope, and applications have Π-typed functions with domain-inhabiting arguments. The rules are given in @wf-rules.

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    grid(
      columns: (1fr, 1fr, 1fr),
      gutter: 1.5em,
      irule("W-Var", wf($Gamma$, $x$), $x in "dom"(Gamma)$),
      irule("W-Type", wf($Gamma$, $top$)),
      irule("W-Bot", wf($Gamma$, $bot$)),
    ),
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule(
        "W-Lam",
        wf($Gamma$, $lambda(x lt.eq A). b$),
        wf($Gamma$, $A$),
        wf(
          $Gamma\, x lt.eq A$,
          $b$,
        ),
      ),
      irule(
        "W-App",
        wf($Gamma$, $f space a$),
        wf($Gamma$, $f$),
        wf($Gamma$, $a$),
        sub($emptyset$, $Gamma$, $f$, $lambda(x lt.eq A). B$),
        sub($emptyset$, $Gamma$, $a$, $A$),
      ),
    ),
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule(
        "W-Iota",
        wf($Gamma$, $iota(x lt.eq A). b$),
        wf($Gamma$, $A$),
        wf(
          $Gamma\, x lt.eq A$,
          $b$,
        ),
      ),
      irule(
        "W-Fix",
        wf($Gamma$, $"fix"(x lt.eq A). b$),
        wf($Gamma$, $A$),
        wf(
          $Gamma\, x lt.eq A$,
          $b$,
        ),
      ),
    ),
  ),
  caption: [Well-formedness rules.],
) <wf-rules>

*[W-Var]* requires variables be well-scoped.

*[W-Lam], [W-Iota], [W-Fix]* check that the annotation is well-formed and that the body is well-formed under the extended context.

*[W-App]* is the only rule with subtyping premises: the function must subtype some $lambda(x lt.eq A). B$ (it has a Π-type), and the argument must subtype the domain $A$. No type is assigned to the result --- the result's type is the result itself (by [S-Refl]), and if the caller needs to know it subtypes something, that is a separate subtyping question.

== Seen set $S$ <seen-set>

Due to the prevelant usage of unbounded recursion in type definitions and encodings, many subtype checks involve infinite proof trees (e.g. $sub(emptyset, emptyset, "add" "one" "two", "Nat")$).

To derive these infinite trees in finite time Claude said I should use "the Brandt-Henglein device for equirecursive subtyping" as used by #cite(<brandt-henglein-1998>, form: "prose"). Claude explains it as: "$S$ is a finite representation of a coinductive (potentially infinite) proof tree: when a goal recurs, the branch closes rather than recursing forever, encoding a regular infinite derivation as a finite one."

As far as I can tell the reason it is remarkable enough to have a name is not that using it is particularly hard, but that convincing oneself it is a sound technique is hard, and Brandt/Henglein did just that. I am informed it only works when the cycles it closes contain at least one "productive" step, which are grouped together into @productive.

The "real" subtyping judgment is $emptyset ; Gamma tack.r a subset.sq.eq b$ (empty hypothesis set); non-empty $S$ arises only inside a derivation.

== Subtyping Rules <subtyping>

The subtyping rules fall into four categories. Each serves a distinct purpose; knowing which category a rule belongs to predicts its shape.

#figure(
  table(
    columns: (auto, 1fr, 1fr, auto),
    align: (left, left, left, center),
    table.header([*Category*], [*Purpose*], [*Rules*], [*Extends $S$?*]),
    table.hline(),
    [Structural\
      (@structural)],
    [Plumbing: recurse without inspecting constructors on either side],
    [@structural-rules],
    [no],
    [Congruence\
      (@congruence)],
    [Match constructor on both sides; reduce to sub-obligations with variance],
    [@congruence-rules],
    [no],
    [Productive unfolding\
      (@productive)],
    [Unfold a recursive binder (ι/fix); extend $S$; enable coinductive closure],
    [@productive-rules],
    [*yes*],
    [Conversion\
      (@conversion)],
    [Close under head reduction so subtyping is closed under computation],
    [@conversion-rules],
    [no],
  ),
  caption: [Rule taxonomy for declarative subtyping],
)

The $S$-extension column matters: S-Hyp can only fire against entries that some ancestor productive rule installed, so any path to S-Hyp must cross an unfold --- the productivity requirement made mechanical.

== Structural rules <structural>

Structural rules (@structural-rules) talk about $subset.sq.eq$ as a relation on terms without inspecting either side's head constructor: reflexivity, transitivity, the top element, hypothesis lookup, and variable lookup.

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    grid(
      columns: (1fr, 1fr, 1fr),
      gutter: 1.5em,
      irule("S-Refl", sub($S$, $Gamma$, $e$, $e$)),
      irule("S-Trans", sub($S$, $Gamma$, $a$, $c$), sub($S$, $Gamma$, $a$, $b$), sub($S$, $Gamma$, $b$, $c$)),
      irule("S-Hyp", sub($S$, $Gamma$, $a$, $b$), $(a, b) in S$),
    ),
    grid(
      columns: (1fr, 1fr, 1fr),
      gutter: 1.5em,
      irule("S-Var", sub($S$, $Gamma$, $x$, $Gamma(x)$)),
      irule("S-Top", sub($S$, $Gamma$, $e$, $top$)),
      irule("S-BotL", sub($S$, $Gamma$, $bot$, $e$)),
    ),
  ),
  caption: [Structural subtyping rules.],
) <structural-rules>

*Ex falso via subsumption.* There is no dedicated "absurd" eliminator. If $a subset.sq.eq bot$ is derivable, then $a subset.sq.eq e$ for every $e$ via [S-Trans] on [S-BotL]. The "contradiction" discharge is subsumption alone. This matches the DOT @amin-moors-odersky-2012 tradition: $bot$ inhabits every type trivially in subtyping, so any term whose type is already $bot$ flows into any expected type without further ceremony.

*[S-Trans] is a constructor, not a derived theorem.* Given the interpretation of types as sets of terms, and subtyping as subset over those sets, one would expect transitivity to be provable instead of axiomatic. Eliminating transitivity as a primitive rule (_transitivity elimination_) is highly desirable: it simplifies metatheory and makes the relation syntax-directed. PSS @hutchins-2010 --- a closely related system --- did not manage to eliminate transitivity. Pasquale and García-Pérez @pasquale-garcia-perez-2026 partially succeeded in a continuation of that work, but required switching the entire theory to a Krivine machine.

I have no satisfying answer to whether or not transitivity is eliminatable in Och, but I will try get one.

== Congruence rules <congruence>

Congruence rules (@congruence-rules) inspect the head constructor on both sides, _require it to match_, and reduce the goal to sub-obligations on the immediate sub-terms with appropriate variance.

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule(
        "S-Lam-Cong",
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
    ),
    grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      irule(
        "S-Iota-Cong",
        sub($S$, $Gamma$, $iota(x lt.eq A_1). B_1$, $iota(x lt.eq A_2). B_2$),
        sub($S$, $Gamma$, $A_1$, $A_2$),
        sub($S$, $Gamma\, x lt.eq A_2$, $B_1$, $B_2$),
      ),
      irule(
        "S-Fix-Cong",
        sub($S$, $Gamma$, $"fix"(x lt.eq A_1). b_1$, $"fix"(x lt.eq A_2). b_2$),
        sub($S$, $Gamma$, $A_1$, $A_2$),
        sub($S$, $Gamma\, x lt.eq A_2$, $b_1$, $b_2$),
      ),
    ),
  ),
  caption: [Congruence subtyping rules.],
) <congruence-rules>

The equivalence premise on [S-App-Cong] (both directions on the argument) is necessary because a neutral head can use its argument at any variance, so equivalence is the only sound congruence.

== Productive unfolding (extend $S$) <productive>

A rule is _productive_ when it replaces a goal whose head is a recursive binder (ι or fix) with a goal where that binder has been unfolded once. Unfolding makes the term _larger_ in syntactic size, so no structural induction can traverse an arbitrary chain of unfolds. Productivity instead provides a _coinductive_ handle: once at least one unfold has fired, the original goal is guaranteed to eventually re-appear as an ancestor, at which point [S-Hyp] can close the derivation.

The rules (@productive-rules) are the only ones that extend $S$.

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    grid(
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
    ),
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
  ),
  caption: [Productive unfolding rules. $S' = S, (a, b)$ where $sub(S, Gamma, a, b)$ is the current goal.],
) <productive-rules>

S-Unfold-Iota-R is the weaker sibling of S-Iota-Intro (same conclusion, no annotation premise), needed to close the equivalence of ι-unfolding.

S-Iota-Intro is *the* rule which allows dependent elimitation: it pust the thing being typed *into* the type, allowing the type to depend on the inhabitant.

*Worked S-Iota-Intro example:* $"true" subset.sq.eq "DBool"$. With

$
  "true" &:= lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). t \
  "false" &:= lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). f \
  "DBool" &:= "fix"(B lt.eq top). iota("self" lt.eq B). lambda(P lt.eq B arrow top). lambda(t lt.eq P space "true"). lambda(f lt.eq P space "false"). P space "self"
$

the constructors are plain lambdas with $top$ domains --- they carry no recursive reference to $"DBool"$. The subtyping check $emptyset ; Gamma tack.r "true" subset.sq.eq "DBool"$ still requires the coinductive seen-set to close, because [S-Iota-Intro]'s annotation premise cycles back to the root goal:

#let dstep(depth, judgment, rulename) = {
  pad(left: depth * 1.5em, grid(
    columns: (1fr, auto),
    $#judgment$, text(size: 8pt, fill: luma(100))[#rulename],
  ))
}
#let dnote(depth, note) = {
  pad(left: depth * 1.5em, text(size: 9pt, style: "italic", fill: luma(100))[#note])
}
#block(inset: (y: 0.5em), stack(
  dir: ttb,
  spacing: 0.4em,
  dstep(0, sub($emptyset$, $Gamma$, $"true"$, $"DBool"$), [root goal]),
  dstep(
    1,
    sub(
      $S_1$,
      $Gamma$,
      $"true"$,
      $iota("self" lt.eq "DBool"). lambda(P lt.eq "DBool" arrow top). lambda(t lt.eq P space "true"). lambda(f lt.eq P space "false"). P space "self"$,
    ),
    [S-Unfold-Fix-R],
  ),
  dnote(1, [where $S_1 = {("true", "DBool")}$]),
  dnote(1, [S-Iota-Intro --- annotation premise:]),
  dstep(2, sub($S_1$, $Gamma$, $"true"$, $"DBool"$), [S-Hyp #sym.checkmark]),
  dnote(2, [root goal reappears --- closed by $(upright("true"), upright("DBool")) in S_1$]),
  dnote(1, [S-Iota-Intro --- body premise (after $["self" arrow.r.bar "true"]$):]),
  dstep(
    2,
    sub(
      $S_1$,
      $Gamma$,
      $"true"$,
      $lambda(P lt.eq "DBool" arrow top). lambda(t lt.eq P space "true"). lambda(f lt.eq P space "false"). P space "true"$,
    ),
    [S-Lam],
  ),
  dnote(2, [contravariant: $("DBool" arrow top) subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(2, [covariant body under $P lt.eq "DBool" arrow top$:]),
  dstep(
    3,
    sub(
      $S_1$,
      $Gamma$,
      $lambda(t lt.eq top). lambda(f lt.eq top). t$,
      $lambda(t lt.eq P space "true"). lambda(f lt.eq P space "false"). P space "true"$,
    ),
    [S-Lam],
  ),
  dnote(3, [contravariant: $P space "true" subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(3, [covariant body under $t lt.eq P space "true"$: S-Lam again]),
  dnote(4, [contravariant: $P space "false" subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(
    4,
    [covariant body: $t subset.sq.eq P space "true"$ by S-Var ($t lt.eq P space "true" in Gamma$) #sym.checkmark],
  ),
))

Because the constructors have $top$ domains, every contravariant [S-Lam] premise is discharged by [S-Top]. The only coinductive step is the [S-Iota-Intro] annotation premise, which closes via [S-Hyp] after one productive unfold. This is the Brandt--Henglein discipline in action: recursion in the subtyping judgment is legal _only across a productive unfold_, so non-productive loops (e.g. reflexivity-by-loop) cannot sneak through.

== Conversion <conversion>

The subtyping relation must be closed under head reduction: if $a$ computes to $a'$, then $a subset.sq.eq b$ should hold iff $a' subset.sq.eq b$. The conversion rules (@conversion-rules) provide that closure.

#figure(
  grid(
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
  ),
  caption: [Conversion rules.],
) <conversion-rules>

= Example Programs <examples>

All encodings below are Church/Scott-style: data types are represented as their own eliminators, with no primitive inductive types in the language. Every definition is mechanised and tested in Lean 4 (see @lean-formal). This section builds from simple encodings to two programs that demonstrate Och's ability to catch subtle bugs in dependently-typed code.

== Booleans <bool-encoding>

$
   "true" & := lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). t \
  "false" & := lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). f \
   "Bool" & := lambda(X lt.eq top). lambda(t lt.eq X). lambda(f lt.eq X). X
$

$"Bool"$ is a standard Church-encoded boolean: the eliminator takes two branches and a return type $X$, and the type itself is $X$. Elimination is non-dependent --- the return type $X$ is the same regardless of whether the value is $"true"$ or $"false"$.

$
  "DBool" &:= "fix"(B lt.eq top). iota("self" lt.eq B). lambda(P lt.eq B arrow top). lambda(t lt.eq P "true"). lambda(f lt.eq P "false"). P "self"
$

$"DBool"$ is the _dependent_ counterpart: its motive $P$ is a function from values to types, so the return type $P "self"$ varies with the value being eliminated. This is what $iota$ enables --- the $"self"$ binder in $iota("self" lt.eq B)$ refers to the actual value inhabiting the type, and [S-Iota-Intro] substitutes it into $P "self"$ during type checking.

Crucially, $"Bool"$ and $"DBool"$ _share the same constructors_ ${"true", "false"}$. The dependent elimination machinery lives entirely in the type ($"DBool"$'s $iota$ and motive), not in the constructors. At runtime, a $"DBool"$ value is identical to a $"Bool"$ value --- the difference is purely compile-time. This pattern recurs later with $"Fin"$ reusing $"Nat"$'s constructors (@fin-encoding).

== Pairs <pair-encoding>

$
                  "Pair" A space B & := lambda(X lt.eq top). lambda(k lt.eq A arrow B arrow X). X \
  "pair" A space B space a space b & := lambda(X lt.eq top). lambda(k lt.eq A arrow B arrow X). k space a space b \
$

Church-encoded binary products. Pair projections $"fst"$/$"snd"$ erase the unused component's type to $top$, so call sites only supply the type of the component being projected.

== Natural numbers <nat-encoding>

$
  "zero" & := lambda(P lt.eq top). lambda(z lt.eq top). lambda(s lt.eq top). z \
  "succ" & := lambda(n lt.eq top). lambda(P lt.eq top). lambda(z lt.eq top). lambda(s lt.eq n arrow top). s space n \
   "Nat" & := "fix"(N lt.eq top). iota("self" lt.eq N). \
         & quad lambda(P lt.eq N arrow top). lambda(z lt.eq P space "zero"). \
         & quad lambda(s lt.eq lambda(n lt.eq N). P space ("succ" n)). P space "self"
$

Nat uses both key features of Och. The outer $"fix"$ ties the recursive knot (Nat refers to itself in the motive domain). The inner $iota$ binds $"self"$ to the value being typed, enabling _dependent_ elimination: the return type $P space "self"$ varies with the value.

The constructors are plain lambdas with $top$ domains --- they carry no reference to $"Nat"$, so $"zero" subset.sq.eq "Nat"$ and $"succ" n subset.sq.eq "Nat"$ hold by the coinductive seen-set discipline (productive unfold of $"fix"$/$iota$, then all contravariant domain checks discharge via [S-Top]).

Addition is defined with an explicit $"fix"$ since the Scott-style eliminator provides no induction hypothesis:

$
  "add" &:= "fix" "add" lt.eq "Nat" arrow "Nat" arrow "Nat". \
  & quad lambda(n lt.eq "Nat"). lambda(m lt.eq "Nat"). \
  & quad n space (lambda(\_ lt.eq "Nat"). "Nat") space m space (lambda("pred" lt.eq "Nat"). "succ" ("add" "pred" m))
$

== Finite sets <fin-encoding>

$
  "Fin" & := "fix"(F lt.eq "Nat" arrow top). lambda(n lt.eq "Nat"). \
        & quad n space (lambda(\_ lt.eq "Nat"). top) space bot \
        & quad (lambda("pred" lt.eq "Nat"). iota("self" lt.eq "Nat"). \
        & quad quad lambda(P lt.eq "Nat" arrow top). lambda("fz" lt.eq P space "zero"). \
        & quad quad lambda("fs" lt.eq lambda(q lt.eq F space "pred"). P space ("succ" q)). P space "self")
$

$"Fin" n$ is the type of naturals strictly less than $n$. The zero-length case is $bot$ (primitive bottom), so $"Fin" "zero"$ is uninhabited. The successor case is an $iota$-type whose $"self"$ is a $"Nat"$ --- this means every $"Fin"$ value is automatically a $"Nat"$ value ($"Fin" n subset.sq.eq "Nat"$). *(I consider this a majorly cool result)*

Natural number literals inhabit $"Fin"$ by subsumption: $"zero" subset.sq.eq "Fin" ("succ" n)$ holds for any $n$, and $n subset.sq.eq "Fin" n$ is correctly rejected (the diagonal). No separate $"FZ"$/$"FS"$ constructors are needed.

== Length-indexed arrays <array-encoding>

$
  "Array" &:= "fix"("Arr" lt.eq "Nat" arrow top arrow top). lambda(n lt.eq "Nat"). lambda(T lt.eq top). \
  & quad n space (lambda(\_ lt.eq "Nat"). top) space "Unit" (lambda("pred" lt.eq "Nat"). "Pair" T space ("Arr" "pred" T))
$

$"Array" n space T$ computes by eliminating the length index: $"Array" "zero" T equiv "Unit"$ and $"Array" ("succ" k) space T equiv "Pair" T space ("Array" k space T)$. Arrays are built with $"unit"$/$"pair"$ directly.

Vectors package a length with an array of that length, using a dependent pair ($"Sigma"$):

$
  "Vec" T & := "Sigma" "Nat" (lambda(n lt.eq "Nat"). "Array" n space T)
$

== appendVec: catching the wrong addition <appendvec>

The north-star example. $"appendVec"$ unpacks two vectors, concatenates their arrays with $"appendArrays"$, and repacks the result with the summed length:

$
  "appendVec" := lambda(T lt.eq top). lambda(v_1 lt.eq "Vec" T). lambda(v_2 lt.eq "Vec" T). \
  quad v_1 space ("Vec" T) space (lambda(n_1 lt.eq "Nat"). lambda("arr"_1 lt.eq "Array" n_1 space T). \
    quad quad v_2 space ("Vec" T) space (lambda(n_2 lt.eq "Nat"). lambda("arr"_2 lt.eq "Array" n_2 space T). \
      quad quad quad "mkVec" T space ("add" n_1 space n_2) space ("appendArrays" T space n_1 space n_2 space "arr"_1 space "arr"_2)))
$

This type-checks: the length $"add" n_1 space n_2$ matches the length of the concatenated array.

Now consider a version with a deliberate bug --- $"add" n_1 space n_1$ instead of $"add" n_1 space n_2$:

$
  "appendVec"_"wrong" := dots.h "mkVec" T space ("add" n_1 space n_1) space ("appendArrays" T space n_1 space n_2 space "arr"_1 space "arr"_2) dots.h
$

The type checker _rejects_ this: $"arr"_2 subset.sq.eq "Array" n_1 space T$ fails because $"arr"_2$ has type $"Array" n_2 space T$ and $n_2 eq.not n_1$. The system catches a bug as subtle as adding the wrong two numbers.

== indexArr: safe array indexing <indexarr>

$"indexArr"$ looks up the $i$-th element of an $"Array" n space T$, where $i$ has type $"Fin" n$:

$
  "indexArr" := "fix" ("self" lt.eq (lambda(T lt.eq top). lambda(n lt.eq "Nat"). "Array" n space T arrow "Fin" n arrow T)). \
  quad lambda(T lt.eq top). lambda(n lt.eq "Nat"). n space (lambda(m lt.eq "Nat"). "Array" m space T arrow "Fin" m arrow T) \
  quad quad (lambda("arr" lt.eq "Array" "zero" T). lambda(i lt.eq "Fin" "zero"). i) \
  quad quad (lambda(p lt.eq "Nat"). lambda("arr" lt.eq "Array" ("succ" p) space T). lambda(i lt.eq "Fin" ("succ" p)). dots.h)
$

In the zero-length branch, $i$ has type $"Fin" "zero" = bot$, so the branch body is $i$ itself --- ex falso via [S-BotL]. In the successor branch, the array is destructured as a pair and $i$ eliminates to either the head or a recursive call on the tail.

The payoff is at call sites:

$
   "indexArr" "Nat" "three" "arr" "zero" quad & checkmark quad ("zero" subset.sq.eq "Fin" "three") \
    "indexArr" "Nat" "three" "arr" "two" quad & checkmark quad ("two" subset.sq.eq "Fin" "three") \
  "indexArr" "Nat" "three" "arr" "three" quad & times quad ("three" subset.sq.eq.not "Fin" "three")
$

Out-of-bounds access is a _compile-time_ error: the index literal fails to subtype $"Fin" n$, and no runtime check is needed.

= Metatheory <metatheory>

Soundness connects the concrete semantics (@conc-eval), subtyping (@subtyping), and well-formedness (@well-formed).

*Evaluation equivalence.* If $e$ evaluates to $e'$, both directions of subtyping hold.

$
  e arrow.b.double e' "implies" emptyset ; emptyset tack.r e' subset.sq.eq e "and" emptyset ; emptyset tack.r e subset.sq.eq e'
$

*Progress.* A well-formed closed term doesn't get stuck during evaluation. The evaluator may return a value or run out of fuel but never reaches an error state.

*End-to-end.* Composing the above: if $e$ is well-formed and subtypes $tau$, and $e$ evaluates to $e'$, the result subtypes $tau$.

$
  wf(emptyset, e) "and" sub(emptyset, emptyset, e, tau) "and" e arrow.b.double e' "implies" emptyset ; emptyset tack.r e' subset.sq.eq tau
$

== What soundness promises to the programmer <promises>

Two separable runtime properties a type system can promise:

+ *Termination.* Running a well-typed program eventually produces
  a value. A totality / normalization claim.
+ *No runtime type errors.* Conditional on the program _not_
  diverging, the value it produces is well-formed and the program never
  reaches a stuck state.

Och *does not aim to prove (1).* Consistency and normalization are explicitly deferred; the calculus admits non-terminating terms by design (type-in-type; general recursion via fix).

Och *does aim to prove (2)*, and this is the real runtime guarantee of the type system. The language expects the following discipline: *type-check first; only evaluate if it succeeded.*

= Lean Formalisation <lean-formal>

The calculus described above has been formalised in Lean 4, which is used to maintain a test suite of example programs and allow AI agents to iterate on the metatheory. The source is available at #link("https://github.com/charlielidbury/ochre")[github.com/charlielidbury/ochre].

= Related Work <related-work>

Existing approaches to verified systems software can be grouped by how they relate the verified artifact to the executable one. To make the comparison concrete, each subsection illustrates how safe array indexing --- accessing element $i$ of an array of length $n$ with a static guarantee that $i < n$, eliminating the runtime bounds check --- is expressed under each approach. Ochre's position, a single language serving both roles, is informed by the trade-offs each approach makes.

== Verification-first, then extraction <rw-extraction>

In this approach the program is written inside a theorem prover, and executable code is extracted or compiled from it. CompCert @leroy-2009 is a C compiler written and verified in Coq, with executable code extracted via Coq's extraction mechanism. seL4 @klein-2009 verified a C microkernel by maintaining a formal model in Isabelle/HOL alongside the C implementation, with a proof that the C code refines the model. Project Everest @project-everest-2017 verified an HTTPS stack using F\* and extracted C code via KReMLin.

In F\*, safe indexing into a length-indexed vector can be expressed directly via a refinement type on the index:

#figure(
  ```fstar
  type vec (a:Type) : nat -> Type =
    | Nil : vec a 0
    | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

  let rec get #a #n (i:nat{i < n}) (v:vec a n) : a =
    let Cons hd tl = v in
    if i = 0 then hd else get (i - 1) tl
  ```,
  caption: [Safe array indexing in F\*. The refinement `i:nat{i < n}` is a compile-time proof obligation; callers must prove `i < n` to the type checker. The `Nil` case is statically unreachable.],
)

For systems code, Low\*'s buffer operations carry the same refinement pattern: `b.(n)` requires a proof that `n < length b`, and after verification KReMLin extracts this to a bare C array access `b[n]` with no bounds check. The result is zero-overhead verified code, but the programmer must express their algorithm in F\*'s purely functional, monadic-effect style, thread heap invariants through a state monad, and maintain separation-logic-like permissions on buffer liveness --- all of which are far removed from the C code they ultimately target. The development cost is very high: the ratio of proof to code is typically 10:1 or greater.

== Translation-based verification <rw-translation>

Aeneas @aeneas-2022 takes an existing Rust program, translates it to a pure functional model in a theorem prover (Lean, Coq, F\*, or HOL4), and lets the programmer verify properties of the model. The key insight is that Rust's ownership discipline guarantees that each mutable borrow has exclusive access, so an in-place mutation `x[i] = v` can be modelled as a pure functional update that returns a new collection.

#figure(
  grid(
    columns: (1fr, 1fr),
    gutter: 2em,
    [
      ```rust
      // Rust source
      pub fn zero(x: &mut Vec<u32>) {
          let mut i = 0;
          while i < x.len() {
              x[i] = 0;
              i += 1;
          }
      }
      ```
    ],
    [
      ```lean
      -- Aeneas-generated Lean
      def zero_loop (x : Vec U32) (i : Usize)
        : Result (Vec U32) :=
        if i < Vec.len x then do
          let (_, back) ←
            Vec.index_mut x i
          let x1 := back 0#u32
          zero_loop x1 (i + 1#usize)
        else Result.ok x
      ```
    ],
  ),
  caption: [Aeneas translation of in-place vector zeroing. The `&mut Vec<u32>` becomes a value that is returned; `x[i] = 0` becomes a call to `index_mut` returning a backward continuation `back` which, applied to the new value, produces the updated vector. Failable operations (indexing, arithmetic) live inside the `Result` monad.],
)

This avoids the need to write systems code in a theorem prover, but introduces an architectural boundary: the programmer writes Rust, the toolchain generates functional models, and the prover reasons about those models. The verified artifact and the executable artifact are different objects in different languages, so proof obligations live outside the source language and cannot influence compilation (e.g., by eliding a bounds check). The programmer must also trust the translation and the Rust compiler.

== Bolt-on verification for Rust <rw-bolton>

Prusti @astrauskas-2022, Creusot @denis-2022, and Verus @lattuada-2023 add specification and verification capabilities to Rust via annotations, macros, or embedded DSLs. The programmer writes Rust code as normal and adds pre/postconditions and loop invariants; an automated verifier (typically backed by an SMT solver) checks them.

#figure(
  ```rust
  // Verus: verified binary search (from verus-lang/verus examples)
  verus! {
  fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
      requires
          forall|i: int, j: int|
              0 <= i <= j < v.len() ==> v[i] <= v[j],
          exists|i: int| 0 <= i < v.len() && k == v[i],
      ensures
          r < v.len(),
          k == v[r as int],
  {
      let mut lo: usize = 0;
      let mut hi: usize = v.len() - 1;
      while lo != hi
          invariant
              hi < v.len(),
              exists|i: int| lo <= i <= hi && k == v[i],
              forall|i: int, j: int|
                  0 <= i <= j < v.len() ==> v[i] <= v[j],
          decreases hi - lo,
      {
          let mid = lo + (hi - lo) / 2;
          if v[mid] < k { lo = mid + 1; } else { hi = mid; }
      }
      lo
  }
  } // verus!
  ```,
  caption: [Verified binary search in Verus. Specifications are written in a first-order logic DSL inside `requires`/`ensures`/`invariant` blocks. Each `v[mid]` access is verified to be in bounds from the loop invariant. Specifications operate over a ghost `Seq<T>` model, not Rust's native `Vec<T>`.],
)

These tools have the lowest adoption barrier: the programmer stays in Rust and adds specifications incrementally. However, the specification and implementation remain in separate languages that the programmer must keep in sync. Specifications operate over ghost models (`Seq<T>`, accessed via `v@`) since Rust's native types cannot appear in logical formulas. The expressivity of specifications is limited by what the SMT backend can decide, and the verification is incomplete --- the solver may time out or fail to find a proof, requiring manual intervention in the form of assertions or lemma calls. In a language with native dependent types, by contrast, the precondition $i < n$ is the type of the index argument, not a side-channel annotation, and the type checker itself is the verification engine.

== Dependently typed systems languages <rw-depsys>

ATS @xi-2017 and Low\* (the systems fragment of F\* @protzenko-2017) are the closest prior art to Ochre's vision: languages which combine dependent types with low-level control in a single system.

#figure(
  ```ats
  (* ATS: safe array access via dependent sorts *)
  fun{a:t@ype} arrayref_get_at
    {n:int}{i:nat | i < n}
    (A: arrayref(a, n), i: size_t i): (a)

  (* Binary search with compile-time bounds proof *)
  fun{a:t@ype} bsearch_arr{n:nat}
    (A: arrayref(a, n), n: int n, x0: a,
     cmp: (a, a) -> int) : int = let
    fun loop {i,j:int | 0 <= i; i <= j+1; j+1 <= n}
      (A: arrayref(a, n), l: int i, u: int j)
      :<cloref1> int =
      if l <= u then let
        val m = l + half(u - l)
        val x = A[m]  // bounds proof discharged by {i,j} constraint
        val sgn = cmp(x0, x)
      in
        if sgn >= 0 then loop(A, m+1, u) else loop(A, l, m-1)
      end else u
  in loop(A, 0, n-1) end
  ```,
  caption: [Safe array access in ATS. The constraint `{i,j:int | 0 <= i; i <= j+1; j+1 <= n}` on the inner loop statically guarantees every `A[m]` access is in bounds. ATS's constraint solver discharges these obligations automatically.],
)

ATS demonstrates that statically guaranteed bounds safety in systems code is achievable, but at a significant ergonomic cost: programmers must work within a bespoke constraint language (the `{...}` sort annotations) that is syntactically and semantically separated from the term language. Low\* achieves similar guarantees via refinement types and SMT discharge, but inherits F\*'s purely functional programming model --- mutation is expressed via a monadic state effect, not via direct mutable references as in Rust.

Ochre aims to differ from both by adopting Rust's ownership model as the mechanism for safe mutation, rather than linear types (ATS) or monadic effects (Low\*), and by unifying the type and term languages so that specifications are written in the same language as the code they describe. The hypothesis is that ownership is a more natural fit for systems programmers, since Rust has demonstrated that the model is learnable at scale, and that a unified language reduces the cognitive overhead of switching between specification and implementation.

#bibliography("refs.bib", style: "chicago-author-date")
