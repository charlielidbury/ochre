#import "../style.typ": *

Typing is the machine run on abstract inputs, with case splitting where the checked program itself inspects an abstract value. The judgement `Ω ⊢ t ⇓ v : A ⊣ Ω'` says that from `Ω` the term `t` runs to the value `v` of type `A`, leaving `Ω'`. It returns the value, not just the type, because later types may depend on it: after `let z = (let y = &x; *y := 2; x)`, the type `Id Nat z 2` holds by `refl` only because the checker knows that `z` is `2`. The rules for the basic forms are the evident ones, each the corresponding machine rule annotated with types; @fig-typing gives the rules particular to Ochr. There is no separate declarative system: this judgement, the machine run with types, is the definition, so what a substitution lemma would say is here the stability of the checker's decisions under refinement (@sec-meta-nat). The side conditions follow from one principle (@sec-typing-two).

#let ir(name: none, ..args) = {
  let a = args.pos()
  let concl = a.last()
  let prems = a.slice(0, a.len() - 1)
  let top = if prems.len() == 0 { none } else { prems.join(h(1.5em)) }
  box(inset: (x: 5pt, y: 4pt), context {
    let w = calc.max(if top == none { 0pt } else { measure(top).width }, measure(concl).width)
    let tree = stack(dir: ttb, spacing: 4pt,
      if top != none { block(width: w, align(center, top)) },
      line(length: w, stroke: 0.5pt),
      block(width: w, align(center, concl)))
    grid(columns: 2, column-gutter: 5pt, align: (center + bottom, left + horizon), tree,
      if name != none { text(size: 7.5pt, smallcaps(name)) })
  })
}
#let pv(..xs) = stack(dir: ttb, spacing: 0.6em, ..xs.pos().map(x => align(center, x)))
#let ev = math.scripts(sym.arrow.b.double)
#figure(kind: image, supplement: [Figure],
  block(width: 100%, { set text(size: 9pt)
    align(center, ir(name: "Call-type", pv($Omega";" (x_1 : T_1 |-> w_1, dots, x_(i-1) : T_(i-1) |-> w_(i-1)) tack.r A_i ev T_i "type", quad A'_i equiv T_i quad (1 <= i <= n)$, $Omega";" (overline(x) : overline(T) |-> overline(w)) tack.r B ev T_B "type"$), $"callty"_Omega (Pi(overline(x) : overline(A)). B, space overline(w) : overline(A')) = T_B$))
    align(center, ir(name: "T-Call", $Omega tack.r overline(u) ev overline(w) : overline(A') tack.l Omega_1$, $"callty"_(Omega_1)(Pi, overline(w) : overline(A')) = B'$, $"rec"_(Omega_1)(F, overline(w))$, $cfg(Omega_1, F(overline(w))) ev cfg(Omega', v)$, $Omega tack.r F(overline(u)) ev v : B' tack.l Omega'$))
    align(center, ir(name: "Split", pv($"content"_Omega (p) = sigma quad Omega[sigma := ty("C")_i (overline(sigma)_i)] tack.r t_i ev v_i : A_i tack.l Omega_i, quad A_i equiv B[ty("C")_i (overline(sigma)_i) slash sigma] quad (1 <= i <= m)$, $cfg(Omega, "block"(kw("match") p {dots})) ev cfg(Omega', v)$), $Omega tack.r kw("match") p space {ty("C")_1 (overline(y)_1) => t_1, dots, ty("C")_m (overline(y)_m) => t_m} ev v : B tack.l Omega'$))
    align(center, ir(name: "Def", pv($Gamma";" phi tack.r B ev G "type" quad Gamma";" phi tack.r b ev v : A tack.l Omega' "on each path of its case splits"$, $"pop"(Omega', v) "succeeds" quad A equiv G "as refined on that path"$), $tack.r kw("fix") f (overline(x) : overline(A)) : B space kw("by") x_j := b space "ok"$))
  }),
  caption: [The typing rules particular to Ochr. [Call-type] evaluates the codomain with the parameters bound to the arguments' values, on a private copy: the type of every call, recursive calls included. [T-Call] then runs the callee in the machine, where a stuck body closes off; `rec` is [Rec]: in the body of `fix f … by xⱼ`, `f` occurs only as the head of a call, and each recursive call passes in position `j` a strict subterm of `xⱼ`'s value on entry. [Split] checks each arm under a refinement of the abstract scrutinee `σ` (with fresh $overline(sigma)_i$; a sealed scrutinee is first generalised to a fresh `σ`), and runs what follows from the state in which the match is closed off as a stuck block. [Def] checks a definition at its generic call: Γ binds a fresh owned place `cᵢ ↦ σᵢ` for each borrow parameter, and φ binds each parameter to `&cᵢ`, to `⋆` for a proof, or to a fresh `σᵢ`. The full rules are in @app-typing.],
) <fig-typing>


== One rule for goals and induction hypotheses

A definition is checked by running it at its most general call [Def]. For `AddMZero(x : &Nat)` that is `AddMZero(&c)` from `{ c ↦ σ }`: the parameter becomes a borrow of a fresh owned place, which stands for whatever the real caller lends. The goal is computed by [Call-type], the rule that types every call. The same rule types the recursive call in the successor case, at a different environment, where `&p` borrows the predecessor field of `c`'s content; the callee's statement, evaluated there, observes `c` through the successor around the field, so the induction hypothesis arrives already wrapped in `S`. That a statement proved at the generic call remains true at every call site rests on the frame property (@sec-meta): a call affects only what it is passed, so the caller's observation is the callee's, placed in a context.

== Types are formed once, and matches split

A type is evaluated once, when it is formed, on a private copy of the environment, and becomes a closed statement about values that later mutation cannot change; a Π-type is a closure over values, whose parameters alone are bound later. So a body that mutates its argument and then proves something about the new contents does not prove the goal: `λ(x : &Nat). (*x := 5; refl)` does not have type `Π(x : &Nat). Id Nat (*x) 5`.

A `match` on an abstract value cannot pick an arm, so each arm is checked with the value refined [Split], and what follows the match is checked once, from a state in which the match has been closed off as a stuck block. Its sealed programs reduce as soon as a later split decides the match, so there is no join and no loss of information. A match and a call to a function containing it run alike, but they are not convertible: conversion has no δ-rule for stuck calls, so `F(x)` is not convertible with `F`'s body inlined, nor are two functions with the same body and different names, and extracting a helper can change which equations hold by `refl`.

== The two paths must agree <sec-typing-two>

Every statement is evaluated along two paths: at a definition's generic call, where calls and matches on abstract values close off, and directly at each instance, where they run. [Call-type] and [Split] identify the results, so if the paths take a decision differently, and the decision changes a result, a statement proved on one path is used on the other, where it may be false. Where the generic call sees abstract values and sealed programs, an instance sees constructors, so a decision read from a normal form can differ between the paths, and one read from syntax and declared types cannot. Most of Ochr's side conditions are this one principle, _no decision that changes a result is read from a normal form_, applied to each decision the machine makes:

- _What is erased._ A term is erased exactly when it is a proof, that is, its declared type is a proposition, or when it forms a type: a type former, a call to a function whose declared codomain is a sort, or anything in a type position. A `let`, sequence or match that computes a type is not erased as a whole; its parts decide. A _declared type_ is read from the declared types of the term's heads, without normalising (@app-erasure), and the checker decides erasure exactly so, in a pass before it runs a term.
- _What a stuck block captures, and how._ Pattern variables are resolved to places first; the block takes the maximal places its arms mention, moved if an arm moves them, borrowed if an arm writes or borrows them, and copied otherwise.
- _Which places an observation reads._ The footprint is read off the syntax of the two sides, and every owner of each place is observed.
- _Which calls recurse, and on what._ A recursive function occurs only as the head of a call, in nested functions too, and passes a strict subterm of its parameter's value on entry.
- _How a call is closed off._ Whether [Close] returns a borrow is read from the callee's declared codomain, and `&` occurs only at the top of a declared type.
- _Whether a match is on a proof._ It is read from the declarations of the constructors the arms name, and the arm from the head of the scrutinee's type (@sec-typing-prop).

Each of these was once read from a normal form, and each time the result was a closed proof of `False` or an accepted program that goes wrong (@fig-why).

*Erased terms leave no trace.* An erased term runs on a private copy of the environment, which is then discarded, so running a proof and skipping it are indistinguishable, and the machine skips proofs, as a compiled program would. Erased terms are also _confined_: they may not write, borrow or move a place that outlives them, except by handing it to another erased call. This is redundant for a correctly classified term, and is kept as a fail-safe: if the paths ever disagreed about whether a term is erased, the path that erases it would reject it instead of discarding its effects.

== Types carry what the machine needs <sec-typing-types>

Decisions read from declared types agree on the two paths only if conversion preserves declared types, that is, never identifies two things that the machine treats differently. Two independent reviews of an earlier version of Ochr found closed proofs of `False` exactly where this failed (@fig-why): conversion let a function whose codomain computes to `Prop`, and whose calls therefore run, stand where a function into `Prop`, whose calls are erased, was expected; and a type such as `T(Z)`, with `T(n) : P(n)` and `P(n)` computing to `Prop`, was a proposition by computation but not by declaration. Two rules close the gap:

- _A Π-type records its class_ (returns types, returns proofs, or other) _and whether it returns a borrow_, as its codomain term determines them when it is formed, and Π-types that differ in either are not convertible. A function value is then used only at a type of its own class, so the class that the machine reads from the value at a call is the one that the static type promised.
- _Sorts are syntactic._ Whatever is written where a type is expected must have a declared type that is syntactically a sort. Evaluation preserves declared types, and universes are not cumulative, so a type's declared sort is its computed sort: there is one notion of proposition, and every value of a proposition is `⋆`.

Both rules only remove identifications, so the set model validates every conversion that remains. The cost is that a codomain must be written in its class, `Prop` rather than a constant that evaluates to `Prop`, and that a family whose sort is computed, such as `T`, cannot be used as a type. By the same principle, two function values are convertible only if their generic calls leave the same observation, results and writes alike (@app-conv).

== Stuck, never ill-typed <sec-typing-stuck>

Where the rules cannot decide, the machine stays stuck rather than produce a value of the wrong type. `J` computes only when its endpoints are convertible, as Lean's `Eq.rec` does: under an absurd hypothesis a cast stays stuck, where reducing it would put `5` at type `Bool`, or embed the untyped λ-calculus in conversion. A match with no arms is erased in a proof position, and anywhere else it is stuck when reached, which happens only when a refinement has made a hypothesis false. [Access] ends every borrow whose loan might lie in the accessed place, including anywhere inside a neutral, whose layout is unknown. Closed runs never meet these situations; open ones do, when a sealed program is re-run under a refinement, and staying stuck there is what keeps the invariants of @app-wf, values at their types among them, in open terms.

== Proofs are matched by their type <sec-typing-prop>

A proof is matched like any constructor value, except that it cannot be inspected: its value is `⋆`. A match on a place whose type is an inductive `D(ā)` declared in `Prop` is therefore decided by that type, never by the content. `match h {}` on `h : False` has no arms and is well typed at any result type: this is ex falso. `True` and `And` have one constructor, so the match has one arm, whose fields are places holding `⋆` of the field types. A declaration with several constructors, such as a user's `Or`, gets one arm per constructor, each checked with its proof fields holding `⋆` and its data fields holding fresh abstract values; every arm must then be a proof, so the match is erased and never runs. A type that is still a neutral, such as `Le(σ, σ')` before a split, licenses no match on a proof at all.

*Subsingleton elimination.* A match on a proof may produce data or a type only if the inductive has no constructors, or one constructor whose fields are all proofs, as in Lean @theory-of-lean. With `inductive Or (P Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)`, the function `IsL(h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }` would mean `true` on `Inl(refl)` and `false` on `Inr(refl)`, two proofs that proof irrelevance identifies. In Ochr this gives no closed proof of `False` by itself, since no match sees which constructor built a proof, but `IsL` has no set-theoretic meaning, and `IsL(Inl(refl))` would be a closed `Bool` stuck for ever.

== The conditions, by principle <sec-why>

@fig-why, in the appendix beside the notes that work each case, lists the side conditions by principle, each with the counterexample that forced it, found while designing the calculus or by a review; only subsingleton elimination is Lean's. Each counterexample is a regression test, and the ledger (@sec-impl) shows that each condition is needed for some verdict. It does not show that together they suffice: that is the stability conjecture (@lem-stable), and the reviews' counterexamples were cases that no earlier test anticipated.

