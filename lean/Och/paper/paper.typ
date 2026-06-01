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

Static analysis catches bugs before software is deployed, notifying developers of mistakes earlier in the development pipeline than testing or user reports can. Type systems are the most widely adopted form of static analysis, and the strength of guarantees they provide varies enormously: from freedom from runtime type errors (TypeScript) through ownership-based memory safety (Rust) to full functional correctness (Lean, Agda, Coq). At the strong end of this spectrum lies _formal verification_: a compiler-checked mathematical proof that a program satisfies its specification across all possible inputs.

Formal verification has been applied at scale: a verified C compiler @leroy-2009, a verified operating system kernel @klein-2009, and a verified HTTPS stack @project-everest-2017 all demonstrate that proving the correctness of real systems software is feasible. These projects used a variety of proof technologies, but a common thread among the most ergonomic approaches is _dependent types_: a type-theoretic mechanism by which types may depend on values, allowing the programmer to state properties such as "this function returns a list of the same length as its input" directly in a type signature, with the compiler verifying the property as a condition of successful compilation.

There is a large intersection between i) software which requires low-level control and performance, and ii) software where correctness is critical. Operating system kernels, cryptographic libraries, network protocol implementations, and compiler backends all occupy this intersection --- they are _systems software_. Today, the languages which offer the necessary control (C, C++, Rust) lack the type-theoretic machinery for formal verification, while the languages which support dependent types (Lean, Agda, F\*) lack the control over memory layout, allocation, and mutation that systems programming demands.

_Ochre_ is a planned language which aims to inhabit this gap: a systems programming language with native support for dependent types. One might summarise the goal as combining Rust's ownership model and low-level control with Lean's proof capabilities in a single language and type system. The key mechanism that enables Ochre is the isomorphism between (safe) Rust and Lean @aeneas-2022 --- if we can translate freely between Rust and Lean, and we know how to dependently type check Lean, then we must be able to dependently type check Rust.

Two recent trends make this research direction timely. First, the cost of unverified software is rising: AI-assisted vulnerability discovery has dramatically increased the rate at which security bugs are found in critical infrastructure --- Mozilla closed as many Firefox vulnerabilities in April 2026 as in the previous two years combined @firefox-vuln-2026, and a nine-year dormant Linux kernel privilege escalation was surfaced by automated analysis @linux-copyfail-2026. Second, the cost of writing software is falling: AI coding agents have reduced the labour involved in software engineering to the point where ambitious rewrites that were previously infeasible are now routine @bun-rewrite-2026. The bottleneck for software engineering is shifting from writing code to specifying what correct code looks like; the value proposition of a language whose type system _is_ a specification language is growing stronger.

During a previous attempt to develop Ochre @lidburyOchreDependentlyTyped2024, the project was held back by soundness bugs in the type system and a general lack of clarity on the semantics of the objects in the language. A counterexample was found in which narrowing a variable's type --- the operation which underlies strong mutation --- invalidated a previously valid subtyping judgment. The root cause was not in the mutation or ownership machinery, but in the foundational interaction between subtyping and type-level computation: the core semantic idea that terms and types share a common language had not been studied carefully enough to support the full system built on top of it.

This paper presents _Och_, a core calculus designed to isolate and study these foundational features before reintroducing the complexity of mutation and ownership. Och combines $lambda$-calculus with equirecursive subtyping, self-types ($iota$), and general recursion ($"fix"$) in a setting where terms and types are syntactically and semantically unified --- concretely, there is no separate $Pi$-type constructor for function types; the type of a function is itself a function, and types reduce by the same $beta$-rule as terms. Och is the first in a planned sequence of calculi --- Och, Ochr (adding ownership/linearity), and finally Ochre (adding mutable references) --- each of which answers a distinct research question while building toward the full language.

== Methodology

Och has been designed experimentally: a set of _goal programs_ drove the design of the typing rules. When a candidate rule set accepted all current goal programs and rejected their deliberately buggy variants, new and more demanding goal programs were added and the process iterated. This methodology has two consequences.

First, Och does not yet rest on a unifying semantic theory, and attempts at a soundness proof are ongoing. Establishing such a theory is a natural next step now that the rule set has stabilised around a substantial body of examples.

Second, the resulting test suite (see @examples) provides strong evidence of expressivity. Using Church/Scott encodings, Och expresses booleans, natural numbers, finite sets ($"Fin" n$), pairs, length-indexed arrays, and safe indexing --- all with dependent elimination. The type system catches bugs as subtle as adding the _wrong_ two numbers (see @vec-encoding), not merely checking that an addition is well-shaped.

== Goals

*Soundness.* Ochre is only valuable if programmers can trust the compiler to catch runtime errors. Proving the soundness of a system which combines equirecursive subtyping, self-types, and general recursion in a unified term/type language is, as far as I can tell, novel. Och is the setting in which to carry out this research.

*Expressivity.* The type system must articulate properties and catch bugs that programmers care about. It must be expressive enough to distinguish $x + y$ from $x + x$ when one is correct and the other is not.

*Extensibility.* Och is the first in a series of calculi building toward Ochre. Features which do not generalise to the full language are not worth investigating here. This consideration has already manifested in the decision to use general recursion via $"fix"$ rather than adding primitive inductive types with only well-founded induction.

= Background <related>
These are works which Och builds off directly, and are worth understanding on at least a surface level.

§1-3 of #cite(<hutchins-2010>, form: "prose") is a particularly good read. It's a 12 page compression of his 336 page thesis and is surprisingly self contained considering how novel the concepts presented are. §4-8 are not needed at all to understand Och, since they focus primarily on results and proofs.

== Pure Subtype Systems <pss>

In a conventional type theory, there is a sharp syntactic distinction between terms and their types. Functions are introduced by $lambda$ and their types by $Pi$: the term $lambda(x : A). b$ has type $Pi(x : A). B$. These are different constructors with different reduction rules --- $lambda$ participates in $beta$-reduction, while $Pi$ does not compute.

Pure Subtype Systems @hutchins-2010 collapse this distinction. There is only $lambda$: the type of a function _is_ a function. Where a conventional system writes $Pi(x : A). B$ for the type of functions from $A$ to $B$, PSS writes $lambda(x : A). B$ --- the same constructor used for the functions themselves. This means types compute by exactly the same rules as terms: $beta$-reduction, substitution, and application all apply uniformly.

The consequence is that every term is trivially its own most precise type. A value like $3$ does not merely _have_ type $"Nat"$; it _is_ a type, the singleton type whose only inhabitant is $3$. The subtyping relation then does all the work that a typing judgment would normally do: $3 subset.sq.eq "Nat"$ is the statement that $3$ is a natural number. There is no need for a separate $Gamma tack.r e : tau$ judgment --- well-formedness (@well-formed) checks structural validity, and subtyping (@subtyping) answers every question about type compatibility.

Och adopts PSS's core design and extends it with self-types ($iota$), general recursion ($"fix"$), and coinductive subtyping.

== Self Types <self-types>

Church encodings represent data as their own eliminators: a boolean is a function that takes two branches and returns one of them, a natural number is a function that takes a zero case and a successor case and folds over itself. This is elegant but has a well-known limitation: the eliminator's return type cannot depend on the value being eliminated. A Church-encoded boolean can branch on itself to return values of some fixed type $X$, but it cannot branch to return values of type $P "true"$ or $P "false"$ for a type-level function $P$ --- the eliminator does not know which boolean it is.

Self types, introduced by @fu-stump-2014, solve this problem. The binder $iota(x lt.eq tau). e$ introduces a type in which the variable $x$ refers to _the term inhabiting the type_. When checking whether $a subset.sq.eq iota(x lt.eq tau). e$, the rule [S-Iota-Intro] substitutes $a$ for $x$ in the body, reducing the goal to $a subset.sq.eq e[x arrow.r.bar a]$. This feeds the value being typed _into_ its own type, enabling the return type to depend on the inhabitant. Self types are also used by Kind @kind-blog, a (now-defunct) proof language by Victor Maia (AKA Victor Taelin online), which provides an accessible introduction to the idea.

For example, the dependent boolean type $"DBool"$ is defined so that its eliminator takes a motive $P : "DBool" arrow top$ and branches of type $P "true"$ and $P "false"$, returning *$P "self"$* where $"self"$ is the boolean value currently being typed. The constructors $"true"$ and $"false"$ are plain $lambda$-terms, identical to their non-dependent counterparts --- the dependent elimination machinery lives entirely in the type, not in the constructors. See @bool-encoding for the full definitions and @examples for further encodings built on this pattern.

= Language Semantics <lang-sem>

This section describes what each piece of the language does in natural language to give the reader an intuition for the objects involved before we get into the typing rules, examples, and metatheory. The full syntax is given in @syntax. When the annotation $tau$ in a binder is $top$, we omit it: $lambda x. e$ abbreviates $lambda(x lt.eq top). e$, and similarly for $iota$ and $"fix"$.

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

*Iota* $iota(x lt.eq tau). e$ allows the definition of a type to include a reference to _the term inhabiting it_. This means $e subset.sq.eq iota (x:tau_0). tau_1$ is reduced to $e subset.sq.eq tau_1[x arrow.r.bar e]$ during checking (notice: the LHS has moved to the RHS). This is a Cedille-style self type @fu-stump-2014, and allows for church encodings with dependent elimination instead of having to add inductive datatypes to the language as a primitive. See @self-types for a longer explanation of self types.

== Concrete evaluation <conc-eval>

The concrete evaluator defines what it means for a closed term to produce a value at runtime. It plays a crucial role in the soundness statement: soundness asserts "if a program is well-formed, it will not get stuck during evaluation." For this to be non-vacuous, the evaluator must be _partial_ --- it must reject ill-formed programs by having no applicable rule, rather than silently succeeding on all inputs.

Concrete evaluation is a substitution-based, call-by-value, big-step semantics on closed terms. The judgment $e arrow.b.double v$ states that closed term $e$ evaluates to value $v$. There is no context and no free variables: binders are eliminated by eager substitution. The rules are given in @eval-rules.

The value forms are ${lambda, top, bot}$. [E-Val] states that values evaluate to themselves. [E-App] evaluates the function to a $lambda$, evaluates the argument, substitutes, and evaluates the body. [E-Iota] and [E-Fix] eagerly unroll by substituting the binder's self-reference into the body and evaluating the result.

As a worked example, evaluating the application $(lambda(x lt.eq top). x) space top$:
$
  (lambda(x lt.eq top). x) space top arrow.b.double top
$
by [E-App]: the function $(lambda(x lt.eq top). x)$ is already a value, the argument $top$ is a value by [E-Val], and the substituted body $x[x arrow.r.bar top] = top$ evaluates to $top$ by [E-Val].

Aside: Och has no concept of levels or universes, so the type checker cannot enforce that ${top, bot, iota}$ do not appear at runtime; the evaluator must handle them gracefully. Adding a universe hierarchy (see §3.6 of PSS @hutchins-2010) would allow type-level arguments to be erased during compilation, after which ${top, bot, iota}$ would never appear at level 0. I plan on doing this in the future.

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

The most important aspect of the evaluation rules is what is _absent_:
- Free variables are not values and have no evaluation rule, so they cannot occur at runtime. This is what forces the type system to rule out ill-scoped variables.
- [E-App] requires the function position to evaluate to a $lambda$. Applying $top$, $bot$, or any non-function term is stuck --- there is no rule for it. This is what forces the type system to verify that the function position has an appropriate type before allowing an application.

A term like $"fix"(x lt.eq top). x$ unrolls indefinitely via [E-Fix]: the body $x$ is replaced by the whole expression, producing the same term again. This is the correct behaviour for non-terminating recursion.

= Typing Rules <decl-sub>

Och's type system is structured around two judgements:

*Well-formedness* $Gamma tack.r e "wf"$ states "$e$ is well-formed under $Gamma$" and is the "entry point" for the type system. Defined in @well-formed. Delegates all type-comparison questions to subtyping.

*Subtyping* $S ; Gamma tack.r a subset.sq.eq b$ states "$a$ is a subtype of $b$ under $Gamma$, assuming coinductive hypotheses $S$". Subtyping in Och means set inclusion: $A subset.sq.eq B$ iff every value of $A$ is also a value of $B$. @seen-set explains the $S$ coinductive hypothesis system.

== Context $Gamma$ <context>

$Gamma$ is the typing context defined as $Gamma ::= emptyset | Gamma, x lt.eq a$. Lookup is $Gamma(x)$. Each entry describes what the type checker knows about a variable statically.

A context is _well-formed_ when every annotation is itself well-formed under the prefix that precedes it:

#figure(
  grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    irule("Ctx-Empty", $tack.r emptyset "wf"$),
    irule("Ctx-Ext", $tack.r Gamma, x lt.eq A "wf"$, $tack.r Gamma "wf"$, wf($Gamma$, $A$)),
  ),
  caption: [Context well-formedness rules.],
) <ctx-wf-rules>

The leaf well-formedness rules ([W-Var], [W-Type], [W-Bot]) require $tack.r Gamma "wf"$ as a premise, following PSS @hutchins-2010, so that $Gamma tack.r e "wf"$ implies $tack.r Gamma "wf"$ by straightforward induction on the derivation. The binder rules ([W-Lam], [W-Iota], [W-Fix]) maintain the invariant by checking the annotation before extending the context.

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
      irule("W-Var", wf($Gamma$, $x$), $tack.r Gamma "wf"$, $x in "dom"(Gamma)$),
      irule("W-Type", wf($Gamma$, $top$), $tack.r Gamma "wf"$),
      irule("W-Bot", wf($Gamma$, $bot$), $tack.r Gamma "wf"$),
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

*[W-Var], [W-Type], [W-Bot]* are the leaf rules and require $tack.r Gamma "wf"$ to ensure context well-formedness is intrinsic to the judgment. *[W-Var]* additionally requires variables be well-scoped.

*[W-Lam], [W-Iota], [W-Fix]* check that the annotation is well-formed and that the body is well-formed under the extended context.

*[W-App]* is the only rule with subtyping premises: the function must subtype some $lambda(x lt.eq A). B$ (it has a Π-type), and the argument must subtype the domain $A$. No type is assigned to the result --- the result's type is the result itself (by [S-Refl]), and if the caller needs to know it subtypes something, that is a separate subtyping question.

== Seen set $S$ <seen-set>

$S$ is the coinductive hypothesis set, defined as $S ::= emptyset | S, (a, b)$. Each entry $(a, b)$ records a subtyping goal $a subset.sq.eq b$ that has already been encountered on the current derivation path.

Due to the prevalent usage of unbounded recursion in type definitions and encodings, many subtype checks involve infinite proof trees (e.g. $sub(emptyset, emptyset, "add" "one" "two", "Nat")$).

To derive these infinite trees in finite time Claude said I should use "the Brandt-Henglein device for equirecursive subtyping" as used by #cite(<brandt-henglein-1998>, form: "prose"). Claude explains it as: "$S$ is a finite representation of a coinductive (potentially infinite) proof tree: when a goal recurs, the branch closes rather than recursing forever, encoding a regular infinite derivation as a finite one."

As far as I can tell the reason it is remarkable enough to have a name is not that using it is particularly hard, but that convincing oneself it is a sound technique is hard, and Brandt/Henglein did just that. I am informed it only works when the cycles it closes contain at least one "productive" step, which are grouped together into @productive.

The "real" subtyping judgment is $emptyset ; Gamma tack.r a subset.sq.eq b$ (empty hypothesis set); non-empty $S$ arises only inside a derivation.

== Subtyping Rules <subtyping>

The subtyping rules fall into four categories. Each serves a distinct purpose; knowing which category a rule belongs to predicts its shape.

#figure(
  table(
    columns: (auto, 1fr, auto, auto),
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

*Worked S-Iota-Intro example:* $underline("true") subset.sq.eq underline("DBool")$. With

$
  underline("true") &:= lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). t \
  underline("false") &:= lambda(P lt.eq top). lambda(t lt.eq top). lambda(f lt.eq top). f \
  underline("DBool") &:= "fix"(B lt.eq top). iota("self" lt.eq B). lambda(P lt.eq B arrow top). lambda(t lt.eq P space underline("true")). lambda(f lt.eq P space underline("false")). P "self"
$

the constructors are plain lambdas with $top$ domains --- they carry no recursive reference to $underline("DBool")$. The subtyping check $emptyset ; Gamma tack.r underline("true") subset.sq.eq underline("DBool")$ still requires the coinductive seen-set to close, because [S-Iota-Intro]'s annotation premise cycles back to the root goal:

#let dstep(depth, judgment, rulename) = {
  pad(left: depth * 1.5em, grid(
    columns: (1fr, 14em),
    $#judgment$, text(size: 8pt, fill: luma(100))[#rulename],
  ))
}
#let dnote(depth, note) = {
  pad(left: depth * 1.5em, text(size: 9pt, style: "italic", fill: luma(100))[#note])
}
#block(inset: (y: 0.5em), stack(
  dir: ttb,
  spacing: 0.4em,
  dstep(0, sub($emptyset$, $Gamma$, $underline("true")$, $underline("DBool")$), [root goal]),
  dstep(
    1,
    sub(
      $S_1$,
      $Gamma$,
      $underline("true")$,
      $iota("self" lt.eq underline("DBool")). lambda(P lt.eq underline("DBool") arrow top). lambda(t lt.eq P space underline("true")). lambda(f lt.eq P space underline("false")). P space "self"$,
    ),
    [S-Unfold-Fix-R],
  ),
  dnote(1, [where $S_1 = {(underline("true"), underline("DBool"))}$]),
  dnote(1, [S-Iota-Intro --- annotation premise:]),
  dstep(2, sub($S_1$, $Gamma$, $underline("true")$, $underline("DBool")$), [S-Hyp #sym.checkmark]),
  dnote(2, [root goal reappears --- closed by $(underline("true"), underline("DBool")) in S_1$]),
  dnote(1, [S-Iota-Intro --- body premise (after $["self" arrow.r.bar underline("true")]$):]),
  dstep(
    2,
    sub(
      $S_1$,
      $Gamma$,
      $underline("true")$,
      $lambda(P lt.eq underline("DBool") arrow top). lambda(t lt.eq P space underline("true")). lambda(f lt.eq P space underline("false")). P space underline("true")$,
    ),
    [S-Lam],
  ),
  dnote(2, [contravariant: $(underline("DBool") arrow top) subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(2, [covariant body under $P lt.eq underline("DBool") arrow top$:]),
  dstep(
    3,
    sub(
      $S_1$,
      $Gamma$,
      $lambda(t lt.eq top). lambda(f lt.eq top). t$,
      $lambda(t lt.eq P space underline("true")). lambda(f lt.eq P space underline("false")). P space underline("true")$,
    ),
    [S-Lam],
  ),
  dnote(3, [contravariant: $P space underline("true") subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(3, [covariant body under $t lt.eq P space underline("true")$: S-Lam again]),
  dnote(4, [contravariant: $P space underline("false") subset.sq.eq top$ by S-Top #sym.checkmark]),
  dnote(
    4,
    [covariant body: $t subset.sq.eq P space underline("true")$ by S-Var ($t lt.eq P space underline("true") in Gamma$) #sym.checkmark],
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

All encodings below are Church/Scott-style: data types are represented as their own eliminators, with no primitive inductive types in the language. Every definition is mechanised and tested in Lean 4 (see @lean-formal). This section builds from simple encodings to two programs that demonstrate Och's ability to catch subtle bugs in dependently-typed code. Throughout, underlined names ($underline("true")$, $underline("Nat")$, etc.) denote meta-level definitions, as opposed to object-level bound variables ($x$, $n$, $P$, etc.).

== Booleans <bool-encoding>

#grid(
  columns: (2fr, 1fr),
  gutter: 1.5em,
  [
    $
       underline("true") & := lambda \_. lambda t. lambda \_. t \
      underline("false") & := lambda \_. lambda \_. lambda f. f \
       underline("Bool") & := lambda X. lambda(t lt.eq X). lambda(f lt.eq X). X
    $
  ],
  [
    ```agda
    data Bool : Set where
      true  : Bool
      false : Bool
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

$underline("Bool")$ is a standard Church-encoded boolean: the eliminator takes two branches and a return type $X$, and the type itself is $X$. Elimination is non-dependent --- the return type $X$ is the same regardless of whether the value is $underline("true")$ or $underline("false")$.

#grid(
  columns: (2fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("DBool") & := "fix" B. space iota("self" lt.eq B). \
      & lambda(P lt.eq B arrow top). lambda(t lt.eq P space underline("true")). lambda(f lt.eq P space underline("false")). P "self" \
      & quad \
      & quad
    $
  ],
  [
    ```agda
    data DBool : Set where
      true  : DBool
      false : DBool
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

$underline("DBool")$ is the _dependent_ counterpart: its motive $P$ is a function from values to types, so the return type $P "self"$ varies with the value being eliminated. This is what $iota$ enables --- the $"self"$ binder in $iota("self" lt.eq B)$ refers to the actual value inhabiting the type, and [S-Iota-Intro] substitutes it into $P "self"$ during type checking.

Crucially, $underline("Bool")$ and $underline("DBool")$ _share the same constructors_ ${underline("true"), underline("false")}$ (@bool-lattice). The dependent elimination machinery lives entirely in the type ($underline("DBool")$'s $iota$ and motive), not in the constructors. At runtime, a $underline("DBool")$ value is identical to a $underline("Bool")$ value --- the difference is purely compile-time. This pattern recurs later with $underline("Fin")$ reusing $underline("Nat")$'s constructors (@fin-encoding).

#figure(
  diagram(
    node-stroke: none,
    node-inset: 4pt,
    edge-stroke: 0.6pt,
    node((0, 0), $top$),
    node((-0.75, 1), $underline("Bool")$),
    node((0.75, 1), $underline("DBool")$),
    node((-0.75, 2), $underline("true")$),
    node((0.75, 2), $underline("false")$),
    node((0, 3), $bot$),
    edge((-0.75, 1), (0, 0), "->"),
    edge((0.75, 1), (0, 0), "->"),
    edge((-0.75, 2), (-0.75, 1), "->"),
    edge((-0.75, 2), (0.75, 1), "->"),
    edge((0.75, 2), (-0.75, 1), "->"),
    edge((0.75, 2), (0.75, 1), "->"),
    edge((0, 3), (-0.75, 2), "->"),
    edge((0, 3), (0.75, 2), "->"),
  ),
  caption: [Subtyping lattice for booleans. Arrows denote $subset.sq.eq$.],
) <bool-lattice>

== Pairs <pair-encoding>

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("Pair") & := lambda A. lambda B. \
                        & quad lambda(X lt.eq top). lambda(k lt.eq A arrow B arrow X). X \
      underline("pair") & := lambda A. lambda B. lambda(a lt.eq A). lambda(b lt.eq B). \
                        & quad lambda(X lt.eq top). lambda(k lt.eq A arrow B arrow X). k a b \
    $
  ],
  [
    ```agda
    record Pair (A B : Set) : Set where
      constructor pair
      field fst : A; snd : B
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

Church-encoded binary products. Projection is performed by applying the pair to a continuation that selects the desired component: $underline("pair") space A space B space a space b space X space (lambda(a lt.eq A). lambda(\_ lt.eq B). a)$ returns $a$.

== Natural numbers <nat-encoding>
For natural numbers we use Scott encodings in which a natural is still it's own eliminator, but only eliminates a single level instead of encoding a full fold. This lines up closer to how pattern matching works with standard datatypes in languages like Haskell than Church encodings.

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("zero") & := lambda(P lt.eq top). lambda(z lt.eq top). lambda(s lt.eq top). z \
      underline("succ") & := lambda(n lt.eq top). lambda(P lt.eq top). lambda(z lt.eq top). \
                        & quad lambda(s lt.eq n arrow top). s space n \
       underline("Nat") & := "fix"(N lt.eq top). iota("self" lt.eq N). \
                        & quad lambda(P lt.eq N arrow top). lambda(z lt.eq P space underline("zero")). \
                        & quad lambda(s lt.eq lambda(n lt.eq N). P space (underline("succ") space n)). \
                        & quad P "self"
    $
  ],
  [
    ```agda
    data Nat : Set where
      zero : Nat
      succ : Nat → Nat
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

$underline("Nat")$ uses both key features of Och. The outer $"fix"$ ties the recursive knot ($underline("Nat")$ refers to itself in the motive domain). The inner $iota$ binds $"self"$ to the value being typed, enabling _dependent_ elimination: the return type $P space "self"$ varies with the value.

One thing to note is the constructors have very wide types compared to $underline("Nat")$:
- $underline("zero")$ will return $z$ regardless of it's type, whereas in $underline("Nat")$ that $z$ argument is restricted down to $P space underline("zero")$.
- $underline("succ")$ calls the continuation $s$ with the predecessor $n$, and therefore only requires that $s$ accepts $n$ (i.e. $lambda(s lt.eq n arrow top). s space n$) instead of requiring that it accept any $underline("Nat")$ (i.e. $lambda(s lt.eq underline("Nat") arrow top). s space n$).

Addition is defined with an explicit $"fix"$ since the Scott-style eliminator provides no induction hypothesis:

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("add") & := "fix"("add" lt.eq underline("Nat") arrow underline("Nat") arrow underline("Nat")). \
                       & quad lambda(n lt.eq underline("Nat")). lambda(m lt.eq underline("Nat")). \
                       & quad n space (underline("Nat") arrow underline("Nat")) \
                       & quad quad m \
                       & quad quad (lambda("pred" lt.eq underline("Nat")). \
                       & quad quad quad underline("succ") space ("add" "pred" m))
    $
  ],
  [
    ```agda
    add : Nat → Nat → Nat
    add zero      m = m
    add (succ pred) m = succ (add pred m)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

== Finite sets <fin-encoding>

$underline("Fin") space n$ is the type of naturals strictly less than $n$. The encoding strategy is: eliminate $n$ to compute the type.
- The zero case yields $bot$ (uninhabited --- there are no naturals less than zero).
- The successor case yields an $iota$-type which is the same as $underline("Nat")$ except it is more precise about which number is passed to the succ case $"fs"$.
The overall structure --- case-split on the index, $bot$ for the empty case, $iota$ for the successor case --- is shared with Kind @kind-legacy, which uses self-types nearly identically to $iota$ (see `base/Fin.kind` in the Kind-Legacy repository). The general machinery for elaborating inductive definitions to lambda-encodings with self-types is developed by @fu-stump-2014 and extended to indexed families in Cedille's implementation, though no published work gives an explicit lambda-encoding of $underline("Fin")$ specifically.

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("Fin") & := "fix"(F lt.eq underline("Nat") arrow top). lambda(n lt.eq underline("Nat")). \
                       & quad n space (lambda(\_ lt.eq underline("Nat")). top) space bot \
                       & quad (lambda("pred" lt.eq underline("Nat")). \
                       & quad quad iota("self" lt.eq underline("Nat")). \
                       & quad quad lambda(P lt.eq underline("Nat") arrow top). \
                       & quad quad lambda("fz" lt.eq P space underline("zero")). \
                       & quad quad lambda(
                           "fs" lt.eq lambda(q lt.eq F space "pred"). \
                                                                      & quad quad quad P space (underline("succ") space q)
                         ). \
                       & quad quad P space "self")
    $
  ],
  [
    ```agda
    data Fin : Nat → Set where
      fzero : Fin (succ n)
      fsucc : Fin n → Fin (succ n)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

In this encoding $"self"$ is typed as a $underline("Nat")$, not as a $underline("Fin")$. This is imprecise because in reality the term will always be a Fin, but it's not _wrong_ to approximate it as a Nat because $underline("Fin") space n subset.sq.eq underline("Nat")$, and difficulties were encountered when trying to type $"self"$ as a $underline("Fin")$.

Natural number literals inhabit $underline("Fin")$ by subsumption: $underline("zero") subset.sq.eq underline("Fin") space (underline("succ") space n)$ holds for any $n$, and $n subset.sq.eq underline("Fin") space n$ is correctly rejected (the diagonal). No separate $underline("FZ")$/$underline("FS")$ constructors are needed --- the $underline("Nat")$ constructors are reused directly, just as $underline("Bool")$ and $underline("DBool")$ share constructors (@bool-encoding). @nat-lattice illustrates the subtyping relationships.

#figure(
  diagram(
    node-stroke: none,
    node-inset: 4pt,
    edge-stroke: 0.6pt,
    node((0, 0), $top$),
    node((1.2, 1), $underline("Nat")$),
    node((0, 1.5), $underline("Fin") space n$),
    node((-1.5, 2.2), $underline("Fin") space 1$),
    node((-0.5, 3.2), $0$),
    node((0.5, 3.2), $1$),
    node((1.5, 3.2), $n$),
    node((0.5, 4.2), $bot$),
    // Nat, Fin n → ⊤
    edge((1.2, 1), (0, 0), "->"),
    edge((0, 1.5), (0, 0), "->"),
    // Fin n → Nat
    edge((0, 1.5), (1.2, 1), "->"),
    // Fin 1 → Fin n, ⊤
    edge((-1.5, 2.2), (0, 0), "->"),
    edge((-1.5, 2.2), (0, 1.5), "->"),
    // 0 → Fin 1, Fin n, Nat
    edge((-0.5, 3.2), (-1.5, 2.2), "->"),
    edge((-0.5, 3.2), (0, 1.5), "->"),
    edge((-0.5, 3.2), (1.2, 1), "->"),
    // 1 → Fin n, Nat
    edge((0.5, 3.2), (0, 1.5), "->"),
    edge((0.5, 3.2), (1.2, 1), "->"),
    // n → Nat (but NOT Fin n — the diagonal)
    edge((1.5, 3.2), (1.2, 1), "->"),
    // ⊥ → 0, 1, n
    edge((0.5, 4.2), (-0.5, 3.2), "->"),
    edge((0.5, 4.2), (0.5, 3.2), "->"),
    edge((0.5, 4.2), (1.5, 3.2), "->"),
  ),
  caption: [Subtyping lattice for natural numbers and finite sets. Laid out such that subtypes are physically beneath their supertypes.],
) <nat-lattice>

== Length-indexed arrays <array-encoding>

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("Array") & := "fix"("Arr" lt.eq underline("Nat") arrow top arrow top). \
                         & quad lambda(n lt.eq underline("Nat")). lambda(T lt.eq top). \
                         & quad n space (underline("Nat") arrow top) \
                         & quad quad underline("Unit") \
                         & quad quad (lambda("pred" lt.eq underline("Nat")). \
                         & quad quad quad underline("Pair") space T space ("Arr" "pred" T))
    $
  ],
  [
    ```agda
    Array : Nat → Set → Set
    Array zero     T = Unit
    Array (succ n) T = Pair T (Array n T)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

$underline("Array") space n space T$ computes by eliminating the length index: $underline("Array") space underline("zero") space T equiv underline("Unit")$ and $underline("Array") space (underline("succ") space k) space T equiv underline("Pair") space T space (underline("Array") space k space T)$. Arrays are built with $underline("unit")$/$underline("pair")$ directly.

== Dependent pairs <sigma-encoding>

The dependent pair $underline("Sigma")$ packages a witness with a payload whose type depends on the witness:

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("Sigma") & := lambda A. lambda(B lt.eq A arrow top). \
                         & quad lambda(X lt.eq top). \
                         & quad lambda(k lt.eq lambda(a lt.eq A). B space a arrow X). X \
      underline("dpair") & := lambda A. lambda(B lt.eq A arrow top). \
                         & quad lambda(a lt.eq A). lambda(b lt.eq B space a). \
                         & quad lambda(X lt.eq top). \
                         & quad lambda(k lt.eq lambda(a lt.eq A). B space a arrow X). \
                         & quad k space a space b
    $
  ],
  [
    ```agda
    record Sigma (A : Set) (B : A → Set)
        : Set where
      constructor dpair
      field fst : A
      field snd : B fst
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

It is unusual that $Sigma$ can be defined in terms of $Pi$ in Och instead of $Sigma$ needing to be a primitive, further research required to get to the bottom of whether this is a contribution or a symptom of an inconsistency.

$underline("appendArrays")$ concatenates two arrays by recursion on the first array's length index:

#grid(
  columns: (1.4fr, 1fr),
  gutter: 0.0em,
  [
    #block[
      #show math.equation: set align(left)
      $ underline("appendArrays") := $
      $ quad "fix"("appendArrays" lt.eq underline("Nat") arrow underline("Nat") arrow top arrow top). $
      $ quad lambda(T lt.eq top). lambda(n_1 lt.eq underline("Nat")). lambda(n_2 lt.eq underline("Nat")). $
      $
        quad lambda("arr"_1 lt.eq underline("Array") space n_1 space T). lambda("arr"_2 lt.eq underline("Array") space n_2 space T).
      $
      $ quad n_1 $
      $
        quad quad (lambda(n_1 ' lt.eq underline("Nat")). underline("Array") space n_1 ' space T arrow underline("Array") space (underline("add") space n_1 ' space n_2) space T)
      $
      $ quad quad (lambda("arr"_1 ' lt.eq underline("Array") space underline("zero") space T). "arr"_2) $
      $
        quad quad (lambda(p lt.eq underline("Nat")). lambda("arr"_1 ' lt.eq underline("Array") space (underline("succ") space p) space T).
      $
      $ quad quad quad "arr"_1 ' space (underline("Array") space (underline("add") space p space n_2) space T) $
      $ quad quad quad quad (lambda("hd" lt.eq T). lambda("tl" lt.eq underline("Array") space p space T). $
      $
        quad quad quad quad quad underline("pair") space T space (underline("Array") space (underline("add") space p space n_2) space T)
      $
      $ quad quad quad quad quad quad "hd" $
      $ quad quad quad quad quad quad ("appendArrays" space T space p space n_2 space "tl" space "arr"_2))) $
      $ quad quad "arr"_1 $
    ]
  ],
  [
    ```agda
    appendArrays : ∀ {T n₁ n₂}
      → Array n₁ T → Array n₂ T
      → Array (add n₁ n₂) T
    appendArrays {n₁ = zero}    _   arr₂ =
      arr₂
    appendArrays {n₁ = succ p} arr₁ arr₂ =
      let (hd , tl) = arr₁ in
      (hd , appendArrays tl arr₂)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]

    ```agda
    appendArrays : ∀ {T n₁ n₂}
      → Array n₁ T → Array n₂ T
      → Array (add n₁ n₂) T
    appendArrays {n₁} arr₁ arr₂ = (
      case n₁ of
        | zero   => λ arr₁' → arr₂
        | succ p => λ arr₁' →
          let (hd , tl) = arr₁' in
          (hd , appendArrays tl arr₂)
    ) arr₁
    ```
    #text(size: 8pt, fill: luma(100))[(a more literal translation)]
  ],
)

The zero case returns the second array unchanged. The successor case destructures the first array as a pair, keeps the head, and recursively appends the tail.

One peculiarity with the above definition is that when we eliminate $n_1$ our motive is $lambda(n_1 ' lt.eq underline("Nat")). underline("Array") space n_1 ' space T arrow underline("Array") space (underline("add") space n_1 ' space n_2) space T$ (aka "eliminting $n_1$ will give us a function") instead of the simpler $lambda(n_1 ' lt.eq underline("Nat")). underline("Array") space (underline("add") space n_1 ' space n_2) space T$ (aka "eliminating $n_1$ will give us an array"). The reason is that in the $"arr"_1$-is-not-empty case ($n_1 = underline("succ") space p$) we need to get the head and tail of $"arr"_1$, but the type system does not know statically that $"arr"_1$ is non-empty. A Sufficiently Smart Compiler would narrow the type of $"arr"_1$ down to $underline("Array") space (underline("succ") space p) space T$ (a pair), but alas Och is not there yet, so instead we must make a function expecting $"arr"_1'$ and immediately pass it $"arr"_1$. This is reflected in the _second_ Agda translation, which has the pattern match expression return a function expecting $"arr"_1'$ and immediately passes it $"arr"_1$.

== Vectors <vec-encoding>

Vectors package a length with an array of that length:

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("Vec") space T & := underline("Sigma") space underline("Nat") space (lambda(n lt.eq underline("Nat")). underline("Array") space n space T)
    $
  ],
  [
    ```agda
    Vec : Set → Set
    Vec T = Sigma Nat (λ n → Array n T)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

The north-star example. $underline("appendVec")$ unpacks two vectors, concatenates their arrays with $underline("appendArrays")$, and repacks the result with the summed length using $underline("dpair")$:

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    $
      underline("appendVec") &:= lambda(T lt.eq top). \
      & quad lambda(v_1 lt.eq underline("Vec") space T). lambda(v_2 lt.eq underline("Vec") space T). \
      & quad v_1 space (underline("Vec") space T) \
      & quad quad (lambda(n_1 lt.eq underline("Nat")). lambda("arr"_1 lt.eq underline("Array") space n_1 space T). \
        & quad quad v_2 space (underline("Vec") space T) \
        & quad quad quad (lambda(n_2 lt.eq underline("Nat")). lambda("arr"_2 lt.eq underline("Array") space n_2 space T). \
          & quad quad quad underline("dpair") space underline("Nat") space (lambda(n lt.eq underline("Nat")). underline("Array") space n space T) \
          & quad quad quad quad (underline("add") space n_1 space n_2) \
          & quad quad quad quad (underline("appendArrays") space T space n_1 space n_2 space "arr"_1 space "arr"_2)))
    $
  ],
  [
    ```agda
    appendVec : ∀ {T} → Vec T → Vec T → Vec T
    appendVec (n₁ , arr₁) (n₂ , arr₂) =
      (add n₁ n₂ , appendArrays arr₁ arr₂)
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

This type-checks: the length $underline("add") space n_1 space n_2$ matches the length of the concatenated array.

Now consider a version with a deliberate bug --- $underline("add") space n_1 space n_1$ instead of $underline("add") space n_1 space n_2$:

$
  underline("appendVec")_"wrong" := dots.h underline("dpair") space underline("Nat") space (lambda(n lt.eq underline("Nat")). underline("Array") space n space T) space (underline("add") space n_1 space n_1) space (underline("appendArrays") space T space n_1 space n_2 space "arr"_1 space "arr"_2) dots.h
$

The type checker _rejects_ this: $"arr"_2 subset.sq.eq underline("Array") space n_1 space T$ fails because $"arr"_2$ has type $underline("Array") space n_2 space T$ and $n_2 eq.not n_1$. The system catches a bug as subtle as adding the wrong two numbers.

== indexArr: safe array indexing <indexarr>

$underline("indexArr")$ looks up the $i$-th element of an $underline("Array") space n space T$, where $i$ has type $underline("Fin") space n$:

#grid(
  columns: (2fr, 1fr),
  gutter: 1.5em,
  [
    #block[
      #show math.equation: set align(left)
      $ underline("indexArr") := "fix" "indexArr". lambda(T lt.eq top). lambda(n lt.eq underline("Nat")). $
      $
        quad n space (lambda(m lt.eq underline("Nat")). underline("Array") space m space T arrow underline("Fin") space m arrow T)
      $
      $
        quad quad (lambda("arr" lt.eq underline("Array") space underline("zero") space T). lambda(i lt.eq underline("Fin") space underline("zero")). i)
      $
      $
        quad quad (lambda(p lt.eq underline("Nat")). lambda("arr" lt.eq underline("Array") space (underline("succ") space p) space T). lambda(i lt.eq underline("Fin") space (underline("succ") space p)).
      $
      $
        quad quad quad "arr" space T space (lambda("hd" lt.eq T). lambda("tl" lt.eq underline("Array") space p space T).
      $
      $
        quad quad quad quad i space (lambda(\_ lt.eq underline("Nat")). T)
      $
      $
        quad quad quad quad quad "hd"
      $
      $
        quad quad quad quad quad (lambda(q lt.eq underline("Fin") space p). "indexArr" space T space p space "tl" space q))
      $
    ]
  ],
  [
    ```agda
    indexArr : ∀ {T n}
      → Array n T → Fin n → T
    indexArr {n = zero}  arr i =
      absurd i
    indexArr {n = succ p} (hd , tl) fzero =
      hd
    indexArr {n = succ p} (hd , tl) (fsucc j) =
      indexArr tl j
    ```
    #text(size: 8pt, fill: luma(100))[(roughly equivalent Agda)]
  ],
)

In the zero-length branch, $i$ has type $underline("Fin") space underline("zero") = bot$, so the branch body is $i$ itself --- ex falso via [S-BotL]. In the successor branch, the array is destructured as a pair and $i$ eliminates to either the head or a recursive call on the tail.

The payoff is at call sites:

$
  underline("indexArr") space underline("Nat") space underline("three") space "arr" space underline("zero") quad & checkmark quad (underline("zero") subset.sq.eq underline("Fin") space underline("three")) \
  underline("indexArr") space underline("Nat") space underline("three") space "arr" space underline("two") quad & checkmark quad (underline("two") subset.sq.eq underline("Fin") space underline("three")) \
  underline("indexArr") space underline("Nat") space underline("three") space "arr" space underline("three") quad & times quad (underline("three") subset.sq.eq.not underline("Fin") space underline("three"))
$

Out-of-bounds access is a _compile-time_ error: the index literal fails to subtype $underline("Fin") space n$, and no runtime check is needed.

== Eater: concrete evaluation with fix <eater>

The following example demonstrates concrete evaluation of a recursive term defined via $"fix"$.

$
   underline("bool") & := lambda t. lambda f. top \
   underline("true") & := lambda t. lambda f. t \
  underline("false") & := lambda t. lambda f. f \
  underline("eater") & := "fix" e. lambda(b lt.eq underline("bool")). b top e
$

$underline("eater")$ is a recursive function that consumes $underline("false")$ arguments until it hits a $underline("true")$, at which point it returns $top$. At each step, $"fix"$ unrolls via [E-Fix], and the boolean argument selects between $top$ (stop) and the self-reference $e$ (continue). E.g. $eval(underline("eater") space underline("true"), top)$ and similarly $eval(underline("eater") space underline("false") space underline("false") space underline("false") space underline("true"), top)$.

*Evaluation of* $underline("eater") space underline("false") space underline("true")$. We abbreviate $underline("eater")$'s unrolled form $lambda(b lt.eq underline("bool")). b top space underline("eater")$ as $underline("eater")^circle.small$ for readability.

#let eu = $underline("eater")^circle.small$
#block(inset: (y: 0.5em), stack(
  dir: ttb,
  spacing: 0.4em,
  dstep(0, eval($underline("eater") space underline("false") space underline("true")$, $top$), [E-App]),
  dstep(1, eval($underline("eater") space underline("false")$, $#eu$), [E-App]),
  dstep(2, eval($underline("eater")$, $#eu$), [E-Fix]),
  dstep(2, eval($underline("false")$, $underline("false")$), [E-Val]),
  dstep(
    2,
    eval($(b top space underline("eater"))[b arrow.r.bar underline("false")]$, $#eu$),
    [$underline("false")$ selects second arg],
  ),
  dstep(1, eval($underline("true")$, $underline("true")$), [E-Val]),
  dstep(
    1,
    eval($(b top space underline("eater"))[b arrow.r.bar underline("true")]$, $top$),
    [$underline("true")$ selects first arg #sym.checkmark],
  ),
))

Each [E-Fix] step replaces the bound variable $e$ with the entire $"fix"$ expression, producing a $lambda$ that is ready to accept the next argument. The recursion terminates when $underline("true")$ selects $top$ instead of the self-reference.

*Evaluation of* $underline("eater") space underline("true") space underline("false")$ *(explodes):*

#block(inset: (y: 0.5em), stack(
  dir: ttb,
  spacing: 0.4em,
  dstep(0, eval($underline("eater") space underline("true") space underline("false")$, $?$), [E-App]),
  dstep(
    1,
    eval($underline("eater") space underline("true")$, $top$),
    [as above --- $underline("true")$ selects first arg],
  ),
  dstep(1, eval($underline("false")$, $underline("false")$), [E-Val]),
  dstep(1, eval($top space underline("false")$, $?$), [*stuck* — $top$ is not a $lambda$ #sym.times]),
))

There is no rule whose conclusion matches $top space underline("false") arrow.b.double v$: [E-App] requires the function position to evaluate to a $lambda$, and $top$ is not one. The derivation is stuck --- this is exactly the kind of runtime error the type system is designed to prevent.

= Metatheory <metatheory>
(This section is a stub, significant attempts at soundness have been made but have so far only resulted in proofs of un-soundness.)

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

Large-scale verification projects have demonstrated that formal verification of systems software is feasible: CompCert @leroy-2009 is a verified C compiler (written in Coq, extracted to OCaml), seL4 @klein-2009 is a verified OS microkernel (C code with a separate Isabelle/HOL refinement proof), and Project Everest @project-everest-2017 produced a verified HTTPS stack
(F\*, extracted to C via KReMLin). These projects use a wide variety of verification techniques, which we overview in this section, with the most relevant/directly comparible to Ochre first.

== Dependently typed systems languages <rw-depsys>

Low\* (the systems fragment of F\* @protzenko-2017) and ATS @xi-2017 are the closest prior art to Ochre's vision: languages which combine dependent types with low-level control in a single system. Low\* is by far the more widely used of the two --- it is the language behind HACL\* @hacl-2017 and Project Everest @project-everest-2017 --- so we illustrate with it.

#figure(
  ```fstar
  (* Low*: safe buffer indexing (systems fragment of F*) *)
  val index (#a:Type) (b:buffer a) (i:U32.t)
    : Stack a
      (requires fun h -> live h b /\ U32.v i < length b)
      (ensures  fun h0 r h1 ->
        h0 == h1 /\ r == Seq.index (as_seq h0 b) (U32.v i))

  let index #a b i = b.(i)
  ```,
  caption: [Safe buffer indexing in Low\*. The refinement `U32.v i < length b` in the `requires` clause is a compile-time proof obligation, discharged by F\*'s SMT backend; callers must prove the index is in bounds. The liveness precondition `live h b` and the heap `h` are threaded through the `Stack` effect --- mutation lives in a monadic state effect rather than in the term language. After verification, KaRaMeL extracts `b.(i)` to a bare C array access `b[i]` with no runtime bounds check.],
)

Low\* achieves statically guaranteed bounds safety with zero runtime overhead, but inherits F\*'s purely functional programming model: mutation is expressed via a monadic state effect (the `Stack`/heap-passing discipline above), not via direct mutable references as in Rust, and the programmer must thread heap invariants and buffer-liveness obligations through that effect by hand. ATS reaches comparable guarantees by a different route --- a bespoke constraint language of dependent sorts (the `{i:nat | i < n}` annotations) discharged by its own constraint solver, and linear types rather than an effect for safe mutation --- but at the cost of a sort language that is syntactically and semantically separated from the term language.

Ochre aims to differ from both by adopting Rust's ownership model as the mechanism for safe mutation, rather than monadic effects (Low\*). The hypothesis is that ownership is a more natural fit for systems programmers, since Rust has demonstrated that the model is learnable at scale, and that a unified language reduces the cognitive overhead of switching between specification and implementation.

== Parallel Codebases <rw-translation>

Aeneas @aeneas-2022 takes an existing Rust program, translates it to a pure functional model in a theorem prover (Lean, Coq, F\*, or HOL4), and lets the programmer verify properties of the model. The programmer is left with two version of their codebase: the executable artifact and the verified artifact. This decouples the two languages, allowing them the best tool for the job (in Aeneas' case, Rust for execution and Lean for verification).

The key insight is that Rust's ownership discipline guarantees that each mutable borrow has exclusive access, so an in-place mutation `x[i] = v` can be modelled as a pure functional update that returns a new collection.

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

This avoids the need to write efficient code in a theorem prover, or reason about the correctness of imperative Rust code. It is the verification technique chosen for Signal Shot @signal-shot-2026, an initiative to formally verify the Signal protocol's Rust implementation (`libsignal`) in Lean by translating it with Aeneas.

The downside of this two-copies-of-the-code approach is that the programmer must maintain and understand two versions of the codebase in two languages with different semantics. This might involve a proof engineer tweaking the Rust so different Lean is emitted which is more ameenable to the particular proof they are attempting. This is a messy workaround --- it would be cleaner if it was all under a single language.

== Bolt-on verification for Rust <rw-bolton>

Prusti @astrauskas-2022, Creusot @denis-2022, and Verus @lattuada-2023 add specification and verification capabilities to Rust via annotations, macros, or embedded DSLs. The programmer writes Rust code as normal and adds pre/postconditions and loop invariants; an automated verifier (typically backed by an SMT solver) checks them. These tools verify only _safe_ Rust; Gillian-Rust @gillian-rust-2025 complements Creusot by verifying the type safety and functional correctness of `unsafe` Rust through separation-logic symbolic execution (embedding the lifetime logic of RustBelt @rustbelt-2018 and the prophecies of RustHornBelt @rusthornbelt-2022), discharging exactly the unsafe-code specifications Creusot can express but not verify.

#figure(
  ```rust
  // Verus: safe array indexing
  verus! {
  fn get(v: &Vec<u64>, i: usize) -> (r: u64)
      requires i < v.len(),
      ensures  r == v@[i as int],
  {
      v[i]
  }
  } // verus!
  ```,
  caption: [Safe array indexing in Verus. The precondition `i < v.len()` is a first-order proof obligation discharged by Verus's SMT backend; every caller must prove the index in bounds, after which the access is statically guaranteed safe (and the runtime bounds check can be elided via a trusted `get_unchecked` primitive, #cite(<lattuada-2023>, form: "prose") §3. The postcondition relates the result to a ghost `Seq<u64>` model `v@`, since Rust's native `Vec<u64>` cannot appear in logical formulas.],
) <verus-index>

As a demonstration of quite how ergonomic Verus is, @verus-binary-search gives an entire `binary_search` algorithm verified in Verus --- the sortedness and membership preconditions, the loop invariant, and the `decreases` termination measure all sit inline as annotations on otherwise-ordinary Rust, and each `v[mid]` access is proven in bounds from the invariant.

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
  caption: [Verified binary search in Verus. Specifications are written in a first-order logic DSL inside `requires`/`ensures`/`invariant` blocks. Each `v[mid]` access is verified to be in bounds from the loop invariant.],
) <verus-binary-search>

These tools have the lowest adoption barrier: the programmer stays in Rust and adds specifications incrementally. However, specifications operate over ghost models (`Seq<T>`, accessed via `v@`) since Rust's native types cannot appear in logical formulas. The expressivity of specifications is limited by what the SMT backend can decide, and the verification is incomplete --- the solver may time out or fail to find a proof, requiring manual intervention in the form of assertions or lemma calls. In a language with native dependent types, by contrast, the precondition $i < n$ is the type of the index argument, not a side-channel annotation, and the type checker itself is the verification engine.

*The expressivity ceiling, made concrete.* It is worth asking precisely how far this bolt-on approach can reach, because the answer delimits what a unified dependently-typed language buys over it. A potential test case is Project Everest @project-everest-2017: could its verified HTTPS stack --- built in F\*/Low\* @protzenko-2017 --- be rebuilt in Verus instead? A large fraction of Everest is exactly Verus's strength: the functional correctness of imperative byte-manipulation code (record-layer formatting, parsers, the handshake state machines). For this class Verus would likely fare _better_ than F\*, because Rust's borrow checker discharges the aliasing reasoning that is Everest's worst accidental complexity, rather than requiring a separation-logic memory model to be threaded through by hand. But two of Everest's deliverables lie structurally beyond Verus. First, HACL\* @hacl-2017 guarantees _secret independence_ (constant-time execution): branching and memory-access patterns must not depend on secret data. This is a _relational_ (2-safety) property --- it quantifies over _pairs_ of executions that differ only in secrets and asserts their observable traces coincide --- and Low\* discharges it by parametricity over an abstract secret-integer type, preserved through extraction to C @protzenko-2017. Verus generates its verification condition by weakest-precondition reasoning over a _single_ execution and discharges it with an SMT solver; a single-trace logic cannot so much as _state_ a 2-safety property without an explicit product-program encoding, and Verus offers no secret/public type discipline for it. Second, Vale @vale-2019 verifies hand-optimised cryptographic _assembly_ using a verified verification-condition generator implemented by proof-by-reflection over F\*'s dependent types; Verus has no machine model and, lacking dependent types, tactics, or explicit proof terms, no analogue of the proof-structuring machinery the task relies on.

Tellingly, Verus's authors draw exactly this line themselves: Verus is "closely tied to Rust's type system, which is more limited in some ways than the dependent type systems of Coq and F\*[, which] may preclude some more sophisticated styles of structuring proofs," and --- in contrast to the engineering limitations they expect to lift --- "limitations tied to Rust's type system are imposed by Verus's design choices" @lattuada-2023. The leading "stay in Rust" verifier thus trades away dependent-type proof power for ergonomics, by construction. Ochre's bet is that unifying the term and type languages need not force that trade: when the specification _is_ the type and the type checker _is_ the verifier, the proof power of dependent types and the ergonomics of working in one language are no longer in tension. Whether Och's subtyping can be made expressive/sound enough to deliver on that bet in practice is exactly the metatheoretic question this paper opens (@metatheory).

== Refinement Types <rw-refinement>

Refinement types augment a base type with a logical predicate that constrains its inhabitants --- an in-bounds index, for instance, has the refinement type `{v: Nat | v < n}` --- and discharge the resulting subtyping obligations automatically with an SMT solver. Liquid Haskell @liquidhaskell-2014 is the canonical example, and Flux @flux-2023 brings the same liquid-types discipline to Rust, attaching refinements to Rust's types and checking them alongside the ownership information the borrow checker already provides. Safe array indexing is the textbook application: the index is refined to be smaller than the length, and the resulting obligation is dispatched by the solver.

The defining design choice is that refinement predicates are drawn from a _decidable_ logic, which is what keeps checking fully automatic. This is precisely a restriction relative to dependent types: the predicate language is deliberately weaker than the term language, so specifications that require quantifier reasoning, induction, or arbitrary value-dependent computation. Och sits on the dependently-typed side of this trade-off: its types are arbitrary terms rather than predicates in a fixed decidable theory, buying expressive power at the (here, still open) cost of decidable checking.

Aside: I should find examples of examples where refinement types are not expressive enough to prove desireable properties, but I do not know refinement types well enough to effectively make that argument --- so take the claim with a grain of salt!


#bibliography("refs.bib", style: "chicago-author-date")
