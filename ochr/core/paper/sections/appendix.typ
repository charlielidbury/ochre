#import "../style.typ": *

// Notation local to the appendix.
// An inference rule whose bar is as wide as its widest line (premises or conclusion).
#let ir(name: none, ..args) = {
  let a = args.pos()
  let concl = a.last()
  let prems = a.slice(0, a.len() - 1)
  let top = if prems.len() == 0 { none } else { prems.join(h(1.5em)) }
  box(inset: (x: 5pt, y: 5pt), context {
    let w = calc.max(if top == none { 0pt } else { measure(top).width }, measure(concl).width)
    let tree = stack(dir: ttb, spacing: 4.5pt,
      if top != none { block(width: w, align(center, top)) },
      line(length: w, stroke: 0.5pt),
      block(width: w, align(center, concl)))
    grid(columns: 2, column-gutter: 5pt, align: (center + bottom, left + horizon), tree,
      if name != none { text(size: 7.5pt, smallcaps(name)) })
  })
}
// Premises stacked vertically, for rules with many premises.
#let pv(..xs) = stack(dir: ttb, spacing: 0.65em, ..xs.pos().map(x => align(center, x)))
// A group of rules, with the checker functions that implement them.
#let lean(..names) = align(right, text(size: 7.5pt, fill: luma(35%), [checker: ] + names.pos().map(n => raw(n)).join[, ]))
#let dr = $class("normal", *)$
#let ev = math.scripts(sym.arrow.b.double)
#let err = $sans("err")$
#let stk = $sans("stuck")$
#let acc = $"acc"$
#let cont = $"content"$

This appendix defines Ochr completely: its syntax and runtime structures (@app-syntax), the machine (@app-machine), observation, `Id` and conversion (@app-conv), typing (@app-typing) and well-formed environments (@app-wf). Every derivation in the paper can be checked against it. Each group of rules names, in small type, the functions of the accompanying Lean checker (@sec-impl) that implement it (in `Machine.lean` unless noted). @app-notes records the points where a choice had to be made, and, for each side condition of @fig-why, a counterexample showing why the weaker reading fails.

== Syntax and runtime structures <app-syntax>

=== Terms

#figure(kind: image, supplement: [Figure],
  block(width: 100%, inset: (y: 4pt), grammar(
    ($t, u, A, B$, $x | ty("Prop") | ty("Type")_i$, [variable, sorts ($i >= 0$)]),
    ([], $Pi(x_1 : A_1 ... x_n : A_n). B$, [dependent function type ($n >= 1$)]),
    ([], $kw("fix") f (x_1 : A_1 ... x_n : A_n) : B space kw("by") x_j := t$, [function, recursive on $x_j$]),
    ([], $kw("fix") f (x_1 : A_1 ... x_n : A_n) : B := t$, [function, not recursive ($lambda$)]),
    ([], $t(u_1, ..., u_n)$, [saturated call]),
    ([], $ty("D")(a_1, ..., a_l) | ty("C")(a_1, ..., a_l; t_1, ..., t_k) | A times B | (t, u) | t.1 | t.2$, [inductives; pairs]),
    ([], $ty("Eq") A space t space u | ty("J")(A, a, b, P, h, t)$, [equality (primitive), transport]),
    ([], $\&A | p | \&p | p := t$, [borrow type; read, borrow, assign]),
    ([], $kw("let") x = t; u | kw("let") x : A = t; u | t; u$, [sequencing]),
    ([], $kw("match") p space {ty("C")_1 (overline(y)_1) => t_1 | ... | ty("C")_m (overline(y)_m) => t_m}$, [case analysis, one arm per constructor ($m >= 0$)]),
    ([], $ty("Id") A space t space u$, [equality of computations]),
    ([], $v$, [embedded value]),
    ($p, q$, $x | dr p | p.g$, [places ($g$ a field name)]),
    ($cal(P)$, $d | (f := kw("fix") ...) | cal(P) thick cal(P)$, [programs]),
    ($d$, $kw("inductive") ty("D") (x_1 : X_1 ... x_l : X_l) : s := ty("C")_1 (overline(g_1 : A_1)) | ... | ty("C")_m (overline(g_m : A_m))$, [declaration]),
  )),
  caption: [Terms and programs. Embedded values occur only in sealed programs and in the code of closures, never in source programs.],
) <fig-app-terms>

*Inductive types.* A declaration introduces a type former $ty("D")$ with uniform parameters $x_1 : X_1, dots, x_l : X_l$, a sort $s in {ty("Type")_0, ty("Prop")}$, and $m >= 0$ constructors $ty("C")_i$, each with named fields $g_(i 1) : A_(i 1), dots, g_(i k_i) : A_(i k_i)$, whose types may mention the parameters. Every constructor builds a value of $ty("D")(overline(x))$; there are no indices. At parameters $overline(a)$ the type is $ty("D")(overline(a))$, written $ty("D")$ when $l = 0$, and the field types are $A_(i j)[overline(a) slash overline(x)]$. A constructor takes the parameters as leading arguments, $ty("C")(overline(a); overline(t))$, and a constructor value records them; we omit them in examples when they can be inferred from the fields or an annotation (`Intro(h, k)` for `Intro(P, Q; h, k)`), and when there are none (`S t`). The library declares
#align(center, grid(columns: 3, column-gutter: 2em, row-gutter: 6pt, align: left,
  $kw("inductive") ty("Nat") : ty("Type")_0 := ty("Z") | ty("S")(1 : ty("Nat"))$, $kw("inductive") ty("Unit") : ty("Type")_0 := ()$, $kw("inductive") ty("False") : ty("Prop")$,
  $kw("inductive") ty("True") : ty("Prop") := ty("I")$, grid.cell(colspan: 2, $kw("inductive") ty("And") (P : ty("Prop")) (Q : ty("Prop")) : ty("Prop") := ty("Intro")(l : P, r : Q)$),
))
`S t` abbreviates `S(t)` and `p.1` is the predecessor place; `⊤`, `refl`, `P ∧ Q` and `⟨h, k⟩` are notation for `True`, `I`, `And(P, Q)` and `Intro(h, k)`. `False`, `True` and `And` are known to conversion, because the computation rules of `Eq` produce them (@app-conv); nothing else distinguishes them from other declarations.

*Binding.* In `Π(x̄:Ā). B` and `fix f (x̄:Ā) : B … := t`, each `xᵢ` is bound in `Aᵢ₊₁ … Aₙ`, in `B` and in `t`. With `by xⱼ`, `f` is bound in `t` and nowhere else; without `by`, `f` is not bound at all, and in no case is `f` bound in `Ā` or `B`. `let x = t; u` binds `x` in `u`. In a declaration, each parameter $x_i$ is bound in $X_(i+1), dots, X_l$ and in the field types. Terms are identified up to renaming of bound variables.

*Pattern variables are places*. The variables $overline(y)_i = y_1, dots, y_(k_i)$ of the arm for $ty("C")_i$ are not binders: we identify the arm $t_i$ with $t_i [p.g_(i 1) slash y_1, dots, p.g_(i k_i) slash y_(k_i)]$, which replaces the root $y_j$ of every place in $t_i$ by the field place $p.g_(i j)$ (for `Nat`, `y` becomes `p.1` and `y.1` becomes `p.1.1`), and write the resolved match $kw("match") p {ty("C")_1 => t_1 | dots | ty("C")_m => t_m}$, abbreviated $m$ below. Every definition below (free places, footprints, captures) is on such resolved terms.

*Borrow types.* `&A` is well formed only when `A` is a _data type_: its value, once evaluated, is headed by an inductive declared in `Type₀` (at any parameters, so `&Box(Prop)` is allowed) or is a product of data types; never a sort, a Π-type or a proposition ([T-Ref]). A type variable or a stuck type is not known to be data and is rejected; this fails safe, since a less refined path rejects rather than deciding differently, and it costs any generic `&A` for `A : Type₀` (note 11). And `&` occurs only syntactically at the top of a declared type, as the whole declared type of a variable, a parameter or a function's result: never inside another type, and never as the value of a type term that is not written `&A` (a codomain that computes to `&Nat` is an error), so that [Close]'s row, read from the declared codomain, always sees a borrow result. There are no borrows inside data and no borrows of borrows. The machine also checks this where values are built ([Pair], [Borrow], closure capture). #lean("isDataType", "Term.refsOk", "refTopOk (Basic.lean)")

*Type positions*. The following positions of a term are _type positions_: the annotation `A` of `let x : A = t; u`; the parameter types and the codomain of `Π` and of `fix`; every argument of `×`, `&` and `Eq`, and the parameters of an inductive type $ty("D")(overline(a))$; the first argument of `Id` (whose two sides run on private copies anyway, @app-conv); and the arguments `A`, `a`, `b` and `P` of `J`. What stands in a type position is erased (@app-erasure).

=== Values, neutrals and types

#figure(kind: image, supplement: [Figure],
  block(width: 100%, inset: (y: 4pt), grammar(
    ($v, w, kappa$, $ty("C")(overline(v); v_1, ..., v_k) | (v, w)$, [data (`Z`, `S v`, `()`, …)]),
    ([], $star$, [the value of every proof]),
    ([], $"borrow"_ell v | "loan"_ell | bot$, [borrow, loan, moved-out place]),
    ([], $n | F | T$, [neutrals, function values, types]),
    ($n$, $sigma | seal(t)$, [abstract value, sealed program]),
    ($F$, $f | chevron.l overline(kappa) tack.r kw("fix") f (overline(x) : overline(A)) : B ... := t chevron.r$, [top-level function, closure]),
    ($T$, $s | ty("D")(v_1, ..., v_l) | T times T | \&T | ty("Eq") T space v space w$, [types (`Nat`, `False`, `And(T, T')`, …)]),
    ([], $chevron.l overline(kappa) tack.r Pi(overline(x) : overline(A)). B chevron.r | n$, [Π-closure, neutral type]),
    ($s$, $ty("Prop") | ty("Type")_i$, [sorts]),
    ($Omega$, $phi_1; ...; phi_k$, [frames, oldest first]),
    ($phi$, $(x : A |-> v)^* thick v^*$, [bindings, then temporaries]),
  )),
  caption: [Values and environments. $ell$ ranges over loan labels and $sigma$ over abstract values.],
) <fig-app-values>

A _closure_ $chevron.l overline(kappa) tack.r t chevron.r$ is code `t` whose free variables are bound, in order, to the captured values $overline(kappa)$; a _Π-closure_ is the same for a Π-type. They are the paper's "closures" and "Π-types are closures over values". A top-level function `f` is a value by itself; its code is in the signature Σ. A neutral is a type exactly when its type is a sort; for instance the sealed program ⌈`Le(σ, σ')`⌉ is a proposition.

A _sealed program_ ⌈`t`⌉ contains a closed term `t`: it has no free variables, though it may embed values, including abstract values and loans. [Close] produces sealed programs of the form ⌈`L; C; K`⌉ with a distinguished _head call_ `C`, which we mark $f(overline(a))^h$.

*Loans.* $"loans"(v)$ is the set of labels ℓ such that $"loan"_ell$ occurs in `v`, looking inside sealed programs, closures and types. In an environment Ω, ℓ is _live_ if $"borrow"_ell$ occurs in Ω, and _inert_ otherwise; inert loans occur only inside the runs of [Seal]. A value is _loan-free_ if it contains no live loan, and _borrow-free_ if moreover it contains no $"borrow"_ell$.

=== Environments and states

An environment $Omega = phi_1";" dots";" phi_k$ is a stack of frames, oldest first. A frame holds a sequence of _bindings_ `x : A ↦ v`, where the stored type `A` is omitted for the parameters bound by the untyped machine, followed by a sequence of _temporaries_ `v`, the values in flight during evaluation (evaluated arguments, the right-hand side of an assignment, a result while its frame is popped). The _positions_ π of Ω are its bindings and temporaries, ordered by frame, then bindings before temporaries, then by index; "in the order of Ω" refers to this order. Variables are resolved in the top frame. We write $Omega(pi)$ and $Omega(x)$ for contents, $Omega + (x : A |-> v)$ for a new binding in the top frame, $Omega dot v$ for a new temporary, and $Omega";" phi$ for a pushed frame.

A _state_ is an environment together with: Δ, the type of every abstract value; ρ, the refinements made so far, of abstract values and of generalised sealed programs; the goal $G$ while a definition is being checked; and the [Rec] stack. We write Ω for the whole state and mention the other components only where a rule changes them. Δ and the generalisation records of ρ are _global_: a private copy discards its changes to the environment, the goal and the refinements of abstract values, but keeps every abstract value it introduced and every generalisation it recorded, and fresh names (abstract values and loan labels) are never reused. The global signature Σ records every inductive declaration, and for each top-level definition its Π-type and its code. A program is checked item by item ([Ind], [Def], [Const]) against the signature of the items before it. #lean("Env.lean", "Check.lean")

=== Auxiliary definitions <app-aux>

+ *Content and update.* $cont_Omega (x) = Omega(x)$; $cont_Omega (dr p) = w$ if $cont_Omega (p) = "borrow"_ell w$; $cont_Omega (p.g) = v_j$ if $cont_Omega (p) = ty("C")(overline(a); v_1, dots, v_k)$ and $g$ is the $j$-th field of $ty("C")$, and $cont_Omega (p.g) = star$ if $cont_Omega (p) = star$ (a field of a proof is a proof, @app-match-prop); otherwise $cont_Omega (p)$ is undefined (so reading `p.g` needs a known constructor with field $g$, as reading `p.1` needs a known `S`, and `*p` needs a borrow). $Omega[p |-> v]$ replaces that sub-value. The _prefixes_ of a place are $"pre"(x) = {x}$, $"pre"(dr p) = "pre"(p) union {dr p}$, $"pre"(p.g) = "pre"(p) union {p.g}$; $q subset.eq.sq p$ means $q in "pre"(p)$. #lean("content", "setPlace")

+ *Loans an access must end* ([Access]). For reading, borrowing and assigning,
  $ L^R_Omega (p) = {ell mid(|) cont_Omega (q) = "loan"_ell, q in "pre"(p)} union "loans"(cont_Omega (p)), $
  and for matching, $L^M_Omega (p) = {ell mid(|) cont_Omega (q) = "loan"_ell, q in "pre"(p)} union "hl"(cont_Omega (p))$, where $"hl"(seal(t)) = "loans"(t)$ (a loan's position inside a neutral is unknown, so it is treated as the head) and $"hl"(v) = emptyset$ for every other `v`. Both keep only live labels, ordered from the root of `p` outward and then left to right inside the content. #lean("accessPath", "accessInside")

+ *Owners.* For a live label ℓ,
  $ "owners"_Omega (ell) = union.big_(pi : thin ell in "loans"(Omega(pi))) cases("owners"_Omega (m) & "if" Omega(pi) = "borrow"_m w, {pi} & "otherwise,") $
  a set of positions of Ω (well-defined by acyclicity, @app-wf). The owners of a variable are $"own"_Omega (x) = "owners"_Omega (ell)$ if $Omega(x) = "borrow"_ell w$, $emptyset$ if $Omega(x) = bot$, and ${x}$ otherwise. #lean("owners (Obs.lean)")

+ *Place occurrences.* $"occ"(t)$ is the set of free place occurrences of a resolved term `t`, each with its kind: read (rd), borrowed (bw), assigned (as) or matched (sc). $"occ"(p) = {(p, "rd")}$, $"occ"(\&p) = {(p, "bw")}$, $"occ"(p := t) = {(p, "as")} union "occ"(t)$, $"occ"(kw("match") p {ty("C")_1 => t_1 | dots | ty("C")_m => t_m}) = {(p, "sc")} union union.big_i "occ"(t_i)$; a binder removes the places rooted at the variable it binds; every other form takes the union over its subterms, including the types and the code of `Π` and `fix`. A variable `x` is a _borrow variable_ in Ω if its stored type is `&T` or $Omega(x)$ is a borrow. #lean("Term.placeOccs", "Term.freeOccs (Basic.lean)")

+ *Footprint*.
  $ W_Omega (t, u) = union.big {"own"_Omega ("root"(p)) mid(|) (p, k) in "occ"(t) union "occ"(u), thick k in {"bw", "as"} "or root"(p) "is a borrow variable"}, $
  ordered as Ω. A place rooted at an owned variable that is only read contributes nothing. #lean("footprint (Obs.lean)")

+ *Substitution and normal form.* For an atom $a in {sigma, "loan"_ell}$, or a neutral `n` (for generalisation), $v[w slash a]$ replaces every occurrence of `a` in `v`, including inside sealed programs, closures and types, and then restores normal form: every sealed program that changed is replaced by its normal form ([Seal]), and every `Eq` type is rebuilt by the smart constructor $"eq"$ of @app-conv. $Omega[w slash a]$ does this to every value of Ω; $Omega[w slash a]^+$ also to the stored types, to Δ and to the goal. #lean("substV", "substT", "substEnv")

+ *Refinement and generalisation* ([Split]). A refinement of an abstract value σ of inductive type $ty("D")(overline(a))$, with $ty("D")$ declared in `Type₀`, is $sigma := ty("C")(overline(a); sigma_1, dots, sigma_k)$ for a constructor $ty("C")(g_1 : A_1, dots, g_k : A_k)$ of $ty("D")$, with $sigma_j$ fresh and $Delta(sigma_j) = A_j [overline(a) slash overline(x)]$ (proofs are never refined: their value is ⋆); $Omega[sigma := r]$ is $Omega[r slash sigma]^+$, and ρ records it. _Generalising_ a neutral $n = seal(t)$ (or an inert loan) at a place of type $T$ takes σ fresh with $Delta(sigma) = T$, forms $Omega[sigma slash n]^+$, and records $n := sigma$ in ρ, so that it persists: whenever normalisation derives $n$ again it yields $rho^*(sigma)$ ([Seal-stuck]), and whenever ρ grows every sealed program of the state is re-normalised. The _refined value_ $rho^*(v)$ applies ρ repeatedly, through constructors; the _strict subterms_ are $"sub"(ty("C")(v_1, dots, v_k)) = union.big_j ({v_j} union "sub"(v_j))$ and $"sub"(v) = emptyset$ otherwise. #lean("refine", "expandRefs", "strictSubterms", "generalizeNeutral", "canonNeutral", "renormAll")

+ *Drop.* $"drop"(Omega, v) = Omega'$ where $Omega dot v arrow.squiggly_ell Omega' dot bot$ ([End]) if $v = "borrow"_ell w$; $"drop"(Omega, v) = Omega$ if `v` is loan-free; otherwise $"drop"(Omega, v) = err$ (something still borrows a dying value). Popping a frame drops its bindings, newest first, with the call's result held as a temporary of the caller's frame: $"pop"(Omega";" phi, v)$. #lean("dropTopBind", "dropValue", "popFrame")

+ *Types of places and values.* $"type"_Omega (x)$ is the stored type of `x`, or $"typeof"(Omega(x))$ if it has none; $"type"_Omega (dr p) = T$ if $"type"_Omega (p) = \&T$; $"type"_Omega (p.g) = A_j [overline(a) slash overline(x)]$ if $"type"_Omega (p) = ty("D")(overline(a))$ with $g_j : A_j$ the field $g$ of a constructor $ty("C")$ of $ty("D")$, and either $cont_Omega (p) = ty("C")(dots)$ or $cont_Omega (p) = star$ and $ty("C")$ is the only constructor of $ty("D")$ (so a field's type is known once its constructor is, and a proof's constructor is known from its type). For values: $ty("C")(overline(a); overline(v))$ has type $ty("D")(overline(a))$ for $ty("C")$ a constructor of $ty("D")$; $(v, w)$ has $"typeof"(v) times "typeof"(w)$; σ has $Delta(sigma)$; `f` has its type in Σ; a closure $chevron.l overline(kappa) tack.r kw("fix") f (overline(x) : overline(A)) : B dots chevron.r$ has the Π-closure $chevron.l overline(kappa) tack.r Pi(overline(x) : overline(A)). B chevron.r$; $"borrow"_ell w$ has $\&"typeof"(w)$; a type has its sort (@app-typing). #lean("placeType", "valType")

+ *The generic call*. For a Π-closure $Pi = chevron.l overline(kappa) tack.r Pi(x_1 : A_1 dots x_n : A_n). B chevron.r$, the _generic arguments_ $overline(a)$ are built left to right. In the frame $overline(kappa), x_1 : T_1 |-> a_1, dots, x_(i-1) : T_(i-1) |-> a_(i-1)$, evaluate $A_i$ in a type position to $T_i$ (@app-typing). If $T_i = \&T$, add an owned place $c_i : T |-> "loan"_(ell_i)$ to a bottom frame and let $a_i = "borrow"_(ell_i) sigma_i$ with $sigma_i : T$ and $ell_i$ fresh (this is the argument $\&c_i$ after [Borrow]); if $T_i$ has sort Prop, let $a_i = star$; otherwise $a_i = sigma_i$ with $sigma_i : T_i$ fresh. The _generic state_ is the frame of owned places $Gamma(Pi) = (c_i : T |-> "loan"_(ell_i))_(i : T_i = \&T)$, and the _parameter frame_ is $phi(Pi) = (overline(kappa), overline(x) : overline(T) |-> overline(a))$, each type stored with its binding. The generic call is $F(overline(a))$ at $Gamma(Pi)$. #lean("checkFix")

== The machine <app-machine>

The machine is the big-step judgement $cfg(Omega, t) ev r$, where the outcome `r` is $cfg(Omega', v)$, $stk$ (the run needs to inspect a neutral) or $err$ (a borrow error). It is deterministic. *Propagation:* when a premise that evaluates a subterm has outcome $stk$ or $err$, so does the conclusion; the only rules that inspect a $stk$ premise are [App-close], [App-head] and [Seal]. We write $cfg(Omega, t) ev cfg(Omega', v)$ only for successful runs.

=== Borrows

Ending a borrow replaces it by ⊥ and substitutes its content for its loan everywhere, in normal form (@app-aux, item 6). A borrow occurs only as the whole value of a binding or temporary (@app-wf), so it has a position π.

#rules(
  ir(name: "End ℓ", $Omega(pi) = "borrow"_ell w$, $Omega arrow.squiggly_ell (Omega[pi |-> bot])[w slash "loan"_ell]$),
)

*[Access]*. $acc^R_p (Omega)$ and $acc^M_p (Omega)$ end, one at a time and in the order of item 2 of @app-aux, the borrow of the first label of $L^R_Omega (p)$, respectively $L^M_Omega (p)$, until that set is empty:
$ acc^X_p (Omega) = cases(Omega & "if" L^X_Omega (p) = emptyset, acc^X_p (Omega') & "if" ell "is the first label of" L^X_Omega (p) "and" Omega arrow.squiggly_ell Omega') quad (X in {R, M}). $
Every rule that reads, borrows or assigns a place `p` first computes $acc^R_p$, and a match on `p` computes $acc^M_p$. This is the borrow checker: an ended borrower holds ⊥, and every later use of it is an error. #lean("endBorrow", "accessPath", "accessInside", "accessNeutralHead")

#rules(
  ir(name: "Read", $acc^R_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = v in.not {bot, "borrow"_ell w}$, $cfg(Omega, p) ev cfg(Omega_1, v)$),
  ir(name: "Move", $acc^R_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = "borrow"_ell w$, $cfg(Omega, p) ev cfg(Omega_1 [p |-> bot], "borrow"_ell w)$),
  ir(name: "Read-err", $acc^R_p (Omega) = Omega_1$, $cont_(Omega_1)(p) "undefined or" bot$, $cfg(Omega, p) ev err$),
  ir(name: "Borrow", pv($acc^R_p (Omega) = Omega_1 quad ell "fresh"$, $cont_(Omega_1)(p) = v in.not {bot, "borrow"_m w}$), $cfg(Omega, \&p) ev cfg(Omega_1 [p |-> "loan"_ell], "borrow"_ell v)$),
  ir(name: "Borrow-err", $acc^R_p (Omega) = Omega_1$, $cont_(Omega_1)(p) "undefined," bot "or a borrow"$, $cfg(Omega, \&p) ev err$),
  ir(name: "Assign", pv($cfg(Omega, t) ev cfg(Omega_1, v) quad acc^R_p (Omega_1 dot v) = Omega_2 dot v'$, $cont_(Omega_2)(p) = w quad "drop"(Omega_2, w) = Omega_3$), $cfg(Omega, p := t) ev cfg(Omega_3 [p |-> v'], ())$),
)
In [Assign] the new value travels as a temporary while `p` is accessed, so that ending a borrow can substitute into it; $"drop"(Omega_2, w)$ ends the old content if it is a borrow, and fails if it still holds a live loan. #lean("readPlace", "borrowPlace", "assignPlace")

=== Sequencing and data

#rules(
  ir(name: "Let", pv($cfg(Omega, t) ev cfg(Omega_1, v) quad cfg(Omega_1 + (x |-> v), u) ev cfg(Omega_2 + (x |-> v'), w)$, $"drop"(Omega_2 dot w, v') = Omega_3 dot w'$), $cfg(Omega, kw("let") x = t";" u) ev cfg(Omega_3, w')$),
  ir(name: "Seq", $cfg(Omega, t) ev cfg(Omega_1, v)$, $"drop"(Omega_1, v) = Omega_2$, $cfg(Omega_2, u) ev r$, $cfg(Omega, t";" u) ev r$),
)
The annotated `let x : A = t; u` runs as `let x = t; u`: its annotation is a type position. A discarded value (`t; u`) is dropped like a binding: a borrow ends, and a live loan is an error. #lean("eval (.letIn, .seq)", "dropTopBind", "dropValue")

#rules(
  ir(name: "Ctor", $cfg(Omega, overline(t)) ev^* cfg(Omega', overline(v))$, $cfg(Omega, ty("C")(overline(t))) ev cfg(Omega', ty("C")(overline(v)))$),
  ir(name: "Unit", $cfg(Omega, ()) ev cfg(Omega, ())$),
  ir(name: "Pair", $cfg(Omega, t) ev cfg(Omega_1, v)$, $cfg(Omega_1 dot v, u) ev cfg(Omega_2 dot v', w)$, $v', w "borrow-free"$, $cfg(Omega, (t, u)) ev cfg(Omega_2, (v', w))$),
  ir(name: "Proj", $cfg(Omega, t) ev cfg(Omega', (v_1, v_2))$, $cfg(Omega, t.i) ev cfg(Omega', v_i)$),
  ir(name: "Proj-stuck", $cfg(Omega, t) ev cfg(Omega', n)$, $cfg(Omega, t.i) ev stk$),
)
A constructor evaluates its fields left to right, each into a temporary ([Args], below); its field types are borrow-free, so a constructor value holds no borrow. #lean("evalCore (.ctor, .zero, .succ, .tt, .pair, .fst, .snd)")

=== Functions, types and proofs

A closure or Π-type captures, when it is formed, the current contents of its free variables $y_1, dots, y_m$ (in the order of Ω), each accessed as a read: $Omega_0 = Omega$, $Omega_i = acc^R_(y_i)(Omega_(i-1))$, $kappa_i = cont_(Omega_i)(y_i)$, each recorded with the declared type and proof flag of $y_i$'s binding (note 27). A captured value may be neither ⊥ nor a borrow (closures capture no borrows); otherwise the rule fails. The other type formers compute type values; `Eq` uses the smart constructor of @app-conv.

#rules(
  ir(name: "Global", $f in Sigma$, $cfg(Omega, f) ev cfg(Omega, f)$),
  ir(name: "Fix", $overline(kappa) "captured," Omega_m$, $cfg(Omega, kw("fix") f (overline(x) : overline(A)) : B dots := t) ev cfg(Omega_m, chevron.l overline(kappa) tack.r kw("fix") f (overline(x) : overline(A)) : B dots := t chevron.r)$),
  ir(name: "Pi", $overline(kappa) "captured," Omega_m$, $cfg(Omega, Pi(overline(x) : overline(A)). B) ev cfg(Omega_m, chevron.l overline(kappa) tack.r Pi(overline(x) : overline(A)). B chevron.r)$),
  ir(name: "Sort", $cfg(Omega, s) ev cfg(Omega, s)$),
  ir(name: "Ind", $cfg(Omega, overline(a)) ev^* cfg(Omega', overline(v))$, $cfg(Omega, ty("D")(overline(a))) ev cfg(Omega', ty("D")(overline(v)))$),
  ir(name: "Prod", $cfg(Omega, A) ev cfg(Omega_1, T)$, $cfg(Omega_1, B) ev cfg(Omega_2, T')$, $cfg(Omega, A times B) ev cfg(Omega_2, T times T')$),
  ir(name: "Ref", $cfg(Omega, A) ev cfg(Omega', T)$, $cfg(Omega, \&A) ev cfg(Omega', \&T)$),
  ir(name: "Eq", $cfg(Omega, A) ev cfg(Omega_1, T)$, $cfg(Omega_1, a) ev cfg(Omega_2, v)$, $cfg(Omega_2, b) ev cfg(Omega_3, w)$, $cfg(Omega, ty("Eq") A thin a thin b) ev cfg(Omega_3, "eq"(T, v, w))$),
  ir(name: "J", $cfg(Omega, t) ev r$, $cfg(Omega, ty("J")(A, a, b, P, h, t)) ev r$),
)
In [Ind] the parameters are evaluated like arguments ([Args], below); a type $ty("And")(T, T')$ is kept as written, and the unit laws apply to it only in conversion ([Conv-unit]). `Id A t u` is a type former too; its value is given in @app-conv. A constructor of an inductive declared in `Prop` (such as `refl` or `⟨h, k⟩`) is a declared proof, so the machine never evaluates it ([Erase-proof]). `J` returns the value of `t` unchanged: its other arguments are in type positions or are the proof `h`, so the machine never runs them (the typing judgement checks them, on private copies). A top-level constant `c : A := t` evaluates to the value stored in Σ, which is ⋆ when `A` has declared sort `Prop`. #lean("capture", "evalCore (.pi, .fix, .sort, .prod, .ref, .eq, .tind, .prim \"J\", .const)", "evalTInd", "ctorIsProof")

*Erased terms*. Whether an occurrence is erased is read from syntax and declarations, never from a normal form or a computed type (@app-erasure); the machine needs no types for it, only one flag per binding, saying whether the binding was declared a proof. An erased term runs on a private copy of the environment: its effects are discarded and only its value is kept, which for a proof is ⋆, so a proof need not be run at all.

#rules(
  ir(name: "Erase-proof", $t "erased, a declared proof"$, $cfg(Omega, t) ev cfg(Omega, star)$),
  ir(name: "Erase-type", $t "erased, a type"$, $cfg(Omega, t) ev_0 cfg(Omega', T) "confined"$, $cfg(Omega, t) ev cfg(Omega, T)$),
  ir(name: "Erase-err", $t "erased"$, $cfg(Omega, t) ev_0 cfg(Omega', v) "not confined"$, $cfg(Omega, t) ev err$),
)
Here $ev_0$ is the judgement in which the rule for `t`'s own form is applied at the root instead of [Erase-type]. A run of `t` from Ω is _confined_ if none of its steps assigns, borrows or moves out of a place rooted at a position of Ω, except a borrow or move that evaluates an argument of an erased call; a step inside nested erased occurrences is judged by the outermost erased occurrence containing it, so an erased term may mutate its own locals freely. A proof that the machine skips ([Erase-proof]) was checked to be confined by [T-Erase] when its enclosing definition was checked. #lean("eval", "callFn", "fnClass", "paramFlags", "onCopy (Env.lean)")

=== Calls

Arguments are evaluated left to right, each into a temporary of the caller's top frame, so that [Access] can see, and end, the earlier ones:

#rules(
  ir(name: "Args-nil", $cfg(Omega, epsilon) ev^* cfg(Omega, epsilon)$),
  ir(name: "Args", $cfg(Omega, u) ev cfg(Omega_1, w)$, $cfg(Omega_1 dot w, overline(u)) ev^* cfg(Omega_2 dot w', overline(w))$, $cfg(Omega, u thin overline(u)) ev^* cfg(Omega_2, w' thin overline(w))$),
)
#rules(
  ir(name: "Call", pv($cfg(Omega, t_0) ev cfg(Omega_0, F) quad cfg(Omega_0 dot F, overline(u)) ev^* cfg(Omega_1 dot F', overline(w))$, $"no" w_i "is" bot quad cfg(Omega_1, F'(overline(w))) ev_"app" r$), $cfg(Omega, t_0(overline(u))) ev r$),
  ir(name: "Call-err", $cfg(Omega_0 dot F, overline(u)) ev^* cfg(Omega_1 dot F', overline(w))$, $"some" w_i = bot$, $cfg(Omega, t_0(overline(u))) ev err$),
)
An argument is ⊥ when a later argument ended its borrow, as in `f(&x, &x)`: it is not of its parameter's type. The judgement $cfg(Omega, F(overline(w))) ev_"app" r$ applies a function value at its _call point_, the state after the arguments have been evaluated. Let `F` have code $kw("fix") f (overline(x) : overline(A)) : B space [kw("by") x_j] := b$ and captured values $overline(kappa)$ (none for a top-level `f`), and let φ be the frame $overline(kappa), [f |-> F], overline(x) |-> overline(w)$, where `f` is bound only with `by`.

#rules(
  ir(name: "App", $cfg(Omega";" phi, b) ev cfg(Omega'";" phi', v)$, $"pop"(Omega'";" phi', v) = cfg(Omega'', v')$, $cfg(Omega, F(overline(w))) ev_"app" cfg(Omega'', v')$),
  ir(name: "App-close", $cfg(Omega";" phi, b) ev stk$, $"the call is not a head call"$, $cfg(Omega, F(overline(w))) ev_"app" "close"(Omega, F, overline(w))$),
  ir(name: "App-head", $cfg(Omega";" phi, b) ev stk$, $"the call is a head call" F(overline(w))^h$, $cfg(Omega, F(overline(w))^h) ev_"app" stk$),
  ir(name: "App-neutral", $F = n "a neutral"$, $"the call is not a head call"$, $cfg(Omega, n(overline(w))) ev_"app" "close"(Omega, n, overline(w))$),
  ir(name: "App-neutral-head", $F = n "a neutral"$, $cfg(Omega, n(overline(w))^h) ev_"app" stk$),
)
[App-close] discards the partial run of the body: $"close"$ starts again from the call point Ω. The head guard of [Seal] covers neutral-headed calls too: a sealed program whose head call has a neutral head stays as it is. #lean("evalCall", "callFn", "runBody", "popFrame")

=== Closing off <app-close>

$"close"(Omega, F, overline(w))$ closes off the call $F(overline(w))$ at its call point Ω. Its precondition is that every argument is loan-free or is $"borrow"_ell u$ with `u` loan-free; [Access] guarantees it. Let $I = {i mid(|) w_i = "borrow"_(ell_i) u_i}$, let $c_i$ ($i in I$) be fixed names, and let
$ L := (kw("let") c_i = u_i";")_(i in I) quad quad C := F(a_1, dots, a_n)^h quad "with" a_i = cases(\&c_i & "if" i in I, w_i & "otherwise.") $
The row is chosen by the _declared_ codomain `B` of `F`'s type: the codomain term of `f`'s definition, of the closure's code, of $Delta(sigma)$ for an abstract function, or the type of a stuck block.

#figure(kind: image, supplement: [Figure],
  table(
    columns: 3, stroke: none, align: left, inset: 4pt,
    table.hline(stroke: 0.5pt),
    [declared codomain `B`], [result `r`], [each $"loan"_(ell_i)$, $i in I$, becomes $f_i$],
    table.hline(stroke: 0.4pt),
    [`Unit`], [`()`], [$seal("L; C; " c_i)$],
    [`&T` (`k` fresh)], [$"borrow"_k seal("L; let r = C; *r")$], [$seal("L; let r = C; *r := " "loan"_k "; " c_i)$],
    [any other], [$seal("L; C")$], [$seal("L; C; " c_i)$],
    table.hline(stroke: 0.5pt),
  ),
  caption: [[Close]: $"close"(Omega, F, overline(w)) = cfg(Omega[f_i slash "loan"_(ell_i)]_(i in I), r)$. The borrows $"borrow"_(ell_i)$ are consumed: at the call point they are no longer in Ω.],
) <fig-app-close>
#lean("closeCall", "declKind", "resultKind", "kindOf")

=== Matching

#rules(
  ir(name: "Match", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = ty("C")_i (overline(v))$, $cfg(Omega_1, t_i) ev r$, $cfg(Omega, kw("match") p {ty("C")_1 => t_1 | dots | ty("C")_m => t_m}) ev r$),
  ir(name: "Match-stuck", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) "is a neutral or an inert loan"$, $cfg(Omega, kw("match") p {dots}) ev stk$),
  ir(name: "Match-err", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) "is undefined or" bot$, $cfg(Omega, kw("match") p {dots}) ev err$),
  ir(name: "Match-prop", $acc^M_p (Omega) = Omega_1$, $ty("C")_1 "is the only constructor of a" ty("D") "declared in" ty("Prop")$, $cfg(Omega_1, t_1) ev r$, $cfg(Omega, kw("match") p {ty("C")_1 => t_1}) ev r$),
)
In arm $i$ the pattern variables are the field places $p.g_(i j)$, so `&y` reborrows a field in place (for `Nat`, the predecessor `p.1`). A match whose arms name the constructors of an inductive declared in `Prop` is a _match on a proof_. The machine recognises it from those names, which is a fact about declarations, and never inspects the content of `p`, which is ⋆: with one constructor it takes the only arm ([Match-prop]), in which the fields of `p` hold ⋆ (@app-aux, item 1); with several, the match is a declared proof (@app-erasure) and is never run. A match with no arms is a declared proof too, whatever its scrutinee, so no rule runs it. [Match], [Match-stuck] and [Match-err] apply to the other matches. #lean("evalMatch", "evalMatchInd", "accessNeutralHead", "byTypeMatch", "evalMatchByType")

=== Sealed programs <app-seal>

Values are kept in normal form. The normal form of a sealed program is computed by running it from the empty environment ε (one empty frame), where its head call may not close off ([App-head]):

#rules(
  ir(name: "Seal", $cfg(epsilon, t) ev cfg(Omega', v)$, $"nf"(seal(t)) = v$),
  ir(name: "Seal-stuck", $cfg(epsilon, t) ev stk$, $"nf"(seal(t)) = cases(rho^*(sigma) & "if" rho "records" seal(t) := sigma, seal(t) & "otherwise")$),
  ir(name: "Seal-err", $cfg(epsilon, t) ev err$, $"nf"(seal(t)) = err$),
)
Every loan in `t` whose borrow lives outside the run is inert in it: [Access] does not end it (it is not live), [Read] copies it (it is loan-free), $"drop"$ accepts it, and a match on it is stuck, as on an abstract value. An error is a type error at the point that triggered the normalisation. Normalisation happens whenever a sealed program is created or changed: by [Close], by [End] (substituting a loan), and by refinement or generalisation (@app-aux, items 6 and 7); a generalised sealed program stays generalised wherever it is derived again. The embedded values of a stuck sealed program are already normal, because substitution normalises inner sealed programs first. #lean("nfSealed", "substV", "canonNeutral")

=== Stuck blocks <app-block>

A stuck match that is not the body of a call is closed off as a call of an anonymous function of its free places, captured as Rust captures closure variables. This happens only in the typing judgement ([Split], @app-typing), after the match's arms have been checked, which gives its type `B` and the set `M` of variables that some arm leaves ⊥ (moves out of).

Let $m = kw("match") p {ty("C")_1 => t_1 | dots | ty("C")_m => t_m}$ be stuck in Ω, and give each occurrence $(q, k) in "occ"(m)$ a _mode_: `mv` (moved) if `q` is a whole variable `x` and either `x` is a borrow variable and $k in {"rd", "as"}$, or $x in M$; otherwise `ref` (borrowed) if $k in {"bw", "as"}$; otherwise `cp` (copied). The _captures_ $q_1, dots, q_n$ are the maximal places of $"occ"(m)$, those with no strict prefix among its places. Each takes the largest mode of the occurrences at or below it ($"cp" < "ref" < "mv"$), and they are ordered by the position of their root, then by length. Capture $q_i$ becomes a parameter $z_i$ with argument $a_i$:
$ (z_i : U_i, a_i) = cases((z_i : \&"type"_Omega (q_i), thick \&q_i) & "if" q_i "is" "ref,", (z_i : "type"_Omega (q_i), thick q_i) & "otherwise (a move if its content is a borrow, a copy if not)".) $
The body $m'$ is `m` with each place $q_i pi$ renamed to $(dr z_i) pi$ if $q_i$ is `ref`, and to $z_i pi$ otherwise. Then
$ "block"(Omega, m, B, M) := F_m (a_1, dots, a_n) quad "where" F_m = chevron.l thin tack.r kw("fix") \_ (z_1 : U_1 dots z_n : U_n) : B := m' chevron.r, $
a non-recursive closure with no captured values. Evaluating the block by [Call] gets stuck on the head of `m` inside $F_m$'s body and closes off by [App-close], with [Close]'s row chosen by `B`. #lean("closeOffMatch", "splitThenClose")

== Observation, `Id` and conversion <app-conv>

*`Eq` computes*. Every `Eq` type is built by the smart constructor $"eq"$, whose pair clause conjoins the components' equations with $"and"$, which drops `True` conjuncts:
$ "eq"(T_1 times T_2, (v_1, v_2), (w_1, w_2)) & = "and"("eq"(T_1, v_1, w_1), "eq"(T_2, v_2, w_2)) \
  "eq"(T, v, w) & = ty("True") quad "if" v equiv w "(and the first clause does not apply)" \
  "eq"(T, ty("C")(overline(v)), ty("C")'(overline(w))) & = ty("False") quad "if" ty("C") != ty("C")' "are constructors of the same inductive" \
  "eq"(T, v, w) & = ty("Eq") T thin v thin w quad "otherwise" \
  "and"(ty("True"), P) = P quad quad "and"(P, ty("True")) & = P quad quad "and"(P, Q) = ty("And")(P, Q) quad "otherwise" $
These realise the conversion rules of @fig-id for `Eq`, and they are why `Id`'s observation computes to the single interesting equation. A type `And(P, Q)` written in a program is not rebuilt by $"and"$: it keeps its head, so a proof of `⊤ ∧ P` can be taken apart by a match, and the unit laws reach it only through conversion ([Conv-unit]). The first clause of $"eq"$ applies only when both sides are pairs, and the third only when both are constructor values; a neutral is never split, and two values with the same constructor are compared only by the second clause (there is no injectivity rule, note 26 of @app-notes). `refl`, the constructor of `True`, has type `True`, so by conversion it proves every reflexive equation; an equation between distinct constructors is `False`, eliminated by `match h {}`. #lean("mkEqM", "mkAnd", "distinctCtors (Basic.lean)")

*Observation*. Let $W = pi_1 < dots < pi_k$ be positions of Ω. The observation of `t` at Ω on `W` runs `t` on a private copy of Ω, ends every remaining borrow, and reads off the result and the footprint. A borrow-typed result (only [Conv-fun] observes one, since `Id` needs a borrow-free type) is observed as its current content, after a given abstract value $sigma_w$ is written through it, so that its owners show where it points:
#rules(
  ir(name: "Obs", pv($Omega tack.r t ev v : A tack.l Omega_1 quad v "is not a borrow"$, $Omega_1 dot v arrow.squiggly^* Omega_2 dot v' "with no borrow left in" Omega_2 dot v'$), $obs(t)^W_Omega = "tuple"(v', Omega_2 (pi_1), dots, Omega_2 (pi_k))$),
  ir(name: "Obs-borrow", pv($Omega tack.r t ev "borrow"_k u : \&T tack.l Omega_1$, $Omega_1 dot u dot "borrow"_k sigma_w arrow.squiggly^* Omega_2 dot u' dot bot "with no borrow left"$), $obs(t)^(W; sigma_w)_Omega = "tuple"(u', Omega_2 (pi_1), dots, Omega_2 (pi_k))$),
)
where $arrow.squiggly^*$ repeatedly ends the first borrow in the order of Ω (so in [Obs-borrow] $sigma_w$ reaches the owners of $"loan"_k$, as `*r := σ_w` would), $"tuple"(v) = v$ and $"tuple"(v, w_1, dots, w_k) = (v, (w_1, (dots, w_k)))$. The run of `t` pops every frame it pushes, so the positions of `W` are still positions of $Omega_2$. A stuck match in `t` is closed off by [Split] (@app-typing), so an observation exists unless `t` has an error. #lean("observe", "endAll", "tupleVal (Obs.lean)")

*`Id` computes*. Both sides run from the same Ω, on independent copies:
#rules(
  ir(name: "Id", pv($Omega tack.r A ev T "type," T "contains no" \& quad W = W_Omega (t, u) = pi_1 < dots < pi_k$, $obs(t)^W_Omega "with" t : A_t equiv T quad obs(u)^W_Omega "with" u : A_u equiv T quad T_W = "type"_Omega (pi_1) times dots times "type"_Omega (pi_k)$), $Omega tack.r ty("Id") A thin t thin u ev "eq"(T times T_W, obs(t)^W_Omega, obs(u)^W_Omega) : ty("Prop") tack.l Omega$),
)
When `W` is empty, $T times T_W$ is just `T` and the observations are just results. #lean("idType", "footprint", "tupleType (Obs.lean)")

*Conversion*. Definitional equality is equality of normal forms, and values are always kept in normal form, so conversion $v equiv w$ is the least relation closed under the following rules. It is the relation of every "≡" premise in @app-typing and of the reflexive clause of $"eq"$.

- [Conv-refl] $v equiv v$, where values are identified up to renaming of bound variables (binder names are ignored).
- [Conv-cong] Two values with the same outermost former (a constructor, a pair, a borrow, an inductive type, `×`, `&`, `Eq`, a sealed program, a closure) are convertible if their immediate components are pairwise convertible: terms (the code of closures, the programs inside sealed programs) component by component, with embedded values compared by ≡.
- [Conv-unit] $ty("And")(ty("True"), P) equiv P equiv ty("And")(P, ty("True"))$: two types are convertible if they are after the unit laws are applied to each, through nested `And`s. This is the only way the unit laws act on a type written in a program; stored types keep their `And`.
- [Conv-pi] Two Π-closures with the same number of parameters are convertible if, at the generic state Γ and generic arguments $overline(a)$ of the first (@app-aux, item 10), their parameter types, each evaluated with the earlier parameters bound to $overline(a)$, are pairwise convertible, and so are their codomains. So Π-types are compared under binders by instantiating the binders, as function values are ([Conv-fun]), and captured values matter only through the types they help compute: $chevron.l m |-> sigma tack.r Pi(n : ty("Nat")). ty("Nat") chevron.r equiv chevron.l thin tack.r Pi(n : ty("Nat")). ty("Nat") chevron.r$. Two Π-closures with convertible captured values and the same code are convertible by [Conv-cong]; the checker tries that first, as a fast path.
- [Conv-fun] Two function values `F`, `G` are convertible if their Π-types are, their captured values are pairwise convertible (none, for a top-level function), and at the generic call of their Π-type (@app-aux, item 10), with the same generic state Γ, arguments $overline(a)$ and owned places $overline(c)$, their observations agree: $obs(F(overline(a)))^(overline(c))_Gamma equiv obs(G(overline(a)))^(overline(c))_Gamma$. For a codomain `&T` both observations use [Obs-borrow] with one shared fresh $sigma_w : T$, so `λ(x y : &Nat). x` and `λ(x y : &Nat). y` differ: one leaves $(sigma_w, sigma_y)$ in the owned places, the other $(sigma_x, sigma_w)$. So a function value's normal form is its captured values together with the observation of its generic call, and two functions with different effects are never convertible.
There is no η rule and no η for `Unit` (an abstract `σ : Unit` is not `()`). Proof irrelevance needs no rule: every proof value is ⋆. The relation is _least_: a function value that occurs in its own generic observation, as the head of a sealed program when its body is stuck at its generic call, is compared there by [Conv-refl] and [Conv-cong]. Read coinductively, [Conv-fun] would identify any two closures whose bodies are stuck at the generic call, such as `λ(x:&Nat). match *x { Z => () | S _ => *x := Z }` and `λ(x:&Nat). match *x { Z => *x := S Z | S _ => () }`, and `J` along that identification proves `Eq Nat (S Z) Z`. #lean("conv", "convT", "convFn", "convPi", "mkEqM", "unitTop (Basic.lean)")



== Typing <app-typing>

The typing judgement $Omega tack.r t ev v : A tack.l Omega'$ says that from Ω the term `t` runs to the value `v`, of type `A`, leaving Ω'; its only other outcome is $err$, a type error. It is the machine with types: each rule below performs the step of the machine rule of the same name and also computes a type. Where the machine would be stuck on the checked program, typing splits instead ([Split]), so the typing judgement is never stuck. Callee bodies run in the machine, where stuck calls close off ([App-close]). We write $Omega tack.r A ev T "type"$ for $Omega tack.r A ev T : s tack.l Omega'$ with `s` a sort and Ω' discarded (a type position).

*Sorts.* Sorts are ordered $ty("Prop") < ty("Type")_0 < ty("Type")_1 < dots$, and $s union.sq s'$ is the larger. Universes are _not cumulative_: a type has exactly one sort, and no rule converts between sorts. The sort of a type value is: the declared sort `s` of `D` for an inductive type $ty("D")(overline(v))$ (`Type₀` for `Nat` and `Unit`, `Prop` for `False`, `True` and `And`); `Type₀` for `&T` (with `T` a data type); $ty("Type")_0 union.sq "sort"(T) union.sq "sort"(T')$ for $T times T'$; `Prop` for `Eq`; $ty("Type")_0$ for `Prop` and $ty("Type")_(i+1)$ for $ty("Type")_i$; for a Π-closure, `Prop` if its codomain at the generic call has sort `Prop` (impredicativity), and otherwise the largest sort of its parameter types and codomain there; $Delta(sigma)$ for an abstract σ whose type is a sort; and for a sealed program `⌈L; C⌉` whose head call's function has a declared codomain that is literally a sort `s`, the sort `s`. #lean("sortOf", "sealedSort?", "isPropV")

=== Erasure <app-erasure>

An occurrence of a term is _erased_ when:
+ it stands in a type position (@app-syntax), or inside one; or
+ it is a type former (a sort, `Π`, an inductive type $ty("D")(overline(a))$, `×`, `&`, `Eq`, `Id`), since every type is formed on a private copy; or
+ it is a call whose callee _returns types_ or _returns proofs_; or
+ it is a _declared proof_, judged from syntax alone: a constructor of an inductive declared in `Prop` (among them `refl` and $chevron.l h, k chevron.r$); a match with no arms (vacuously, every arm is a proof); a match on a proof whose inductive has several constructors (@app-match-prop requires every arm to be a declared proof); a `J` whose motive is syntactically a function into `Prop`, or whose last argument is a declared proof; a call whose callee returns proofs; a variable whose binding is flagged as a proof (a parameter whose declared type has declared sort `Prop`, or a `let` whose right-hand side is a declared proof; a captured value is flagged as its binding was); a `fix` whose Π-type returns proofs; `let x = t; u`, `t; u` or a match run directly when its tail (`u`, or the arm taken) is a declared proof; a stuck block when every arm is; or the bound term of `let x : A = t; u` when `A` has declared sort `Prop`.

A function value, top-level or local, _returns types_ if the codomain term of its Π-type is syntactically a sort, and _returns proofs_ if that term's _declared sort_ is `Prop`. A type term has declared sort `Prop` when it is `Id`, `Eq`, or an inductive type $ty("D")(overline(a))$ with `D` declared in `Prop` (such as `False`, `⊤` or `P ∧ Q`); a `Π` into such a term; a variable declared `: Prop`; a call whose head's codomain term has declared sort `Prop`; a `let`, `;` or `match` whose tail does; or an ascription at `Prop`. Nothing is normalised: `U(n)` with `U : Π(n : Nat). Type₀` has declared sort `Type₀`, whatever `U(n)` computes to, and `V(Z)` with `V : Π(n : Nat). U(n)` does not have declared sort `Prop` although it computes to `⊤`. A stuck block is erased exactly when _each_ of its arms, as checked by [Split], is a declared proof; it is never erased by clause 3 applied to its codomain, nor by its type inferred from the arms, since both are computed. No clause consults the type the typing judgement computes: reading clause 4 by the computed type while calls are classed by syntax, or reading a variable as a proof because its value is ⋆, each admits a closed proof of false (notes 2 and 3). A block that is not erased is always safe: its sealed programs re-run the arms, which make their own decisions. Every clause reads syntax, a declaration or a sort, so the two paths of @lem-stable take the same decisions. Notes 1–3 of @app-notes show what goes wrong otherwise.

#rules(
  ir(name: "T-Erase", $t "erased"$, $Omega scripts(tack.r)_0 t ev v : A tack.l Omega' "by a confined run"$, $Omega tack.r t ev v^bullet : A tack.l Omega$),
)
Here $v^bullet = star$ if `t` is a declared proof (clause 4) and $v^bullet = v$ otherwise, $scripts(tack.r)_0$ applies the rule for `t`'s own form at the root, and a run that is not confined (@app-machine, [Erase-err]) is a type error. So an erased term is typed like any other term, on a private copy of the environment, and leaves no trace. Confinement is redundant for a correctly classified term, since the private copy already discards its effects; it is a fail-safe: if the two evaluation paths ever disagreed about whether a term is erased, the path that erases a term with outside effects would reject it, instead of silently discarding effects that the other path keeps. A proof may still mutate its own locals, and may hand outer places to other erased calls, as `AddMZero`'s recursive call `AddMZero(&p)` does. #lean("eval", "fnClass", "propDecl", "typeClass", "jErased", "evalType", "onCopy (Env.lean)")



=== Places, sequencing and data

#rules(
  ir(name: "T-Read", $cfg(Omega, p) ev cfg(Omega', v)$, $Omega tack.r p ev v : "type"_Omega (p) tack.l Omega'$),
  ir(name: "T-Borrow", $cfg(Omega, \&p) ev cfg(Omega', v)$, $"type"_Omega (p) = T "a data type"$, $Omega tack.r \&p ev v : \&T tack.l Omega'$),
  ir(name: "T-Assign", pv($Omega tack.r t ev v : A tack.l Omega_1 quad A equiv "type"_(Omega_1)(p)$, $acc^R_p (Omega_1 dot v) = Omega_2 dot v' quad "drop"(Omega_2, cont_(Omega_2)(p)) = Omega_3$), $Omega tack.r p := t ev () : ty("Unit") tack.l Omega_3 [p |-> v']$),
  ir(name: "T-Let", pv($Omega tack.r t ev v : A tack.l Omega_1 quad Omega_1 + (x : A |-> v) tack.r u ev w : B tack.l Omega_2 + (x : A' |-> v')$, $"drop"(Omega_2 dot w, v') = Omega_3 dot w'$), $Omega tack.r kw("let") x = t";" u ev w' : B tack.l Omega_3$),
  ir(name: "T-Let-ann", pv($Omega tack.r A ev T "type" quad Omega scripts(tack.r)^T t ev v : T' tack.l Omega_1 quad T' equiv T$, $Omega_1 + (x : T |-> v) tack.r u ev w : B tack.l Omega_2 + (x : T'' |-> v') quad "drop"(Omega_2 dot w, v') = Omega_3 dot w'$), $Omega tack.r kw("let") x : A = t";" u ev w' : B tack.l Omega_3$),
  ir(name: "T-Seq", $Omega tack.r t ev v : A tack.l Omega_1$, $"drop"(Omega_1, v) = Omega_2$, $Omega_2 tack.r u ev w : B tack.l Omega_3$, $Omega tack.r t";" u ev w : B tack.l Omega_3$),
)
A binding stores the type of its value, and [Split] refines stored types, so `A'` in [T-Let] is `A` as refined. In [T-Let-ann], $scripts(tack.r)^T$ checks `t` against `T`: if `t` is a match, it is [Split] with annotation `T`. #lean("placeType", "evalCore (.place, .borrow, .assign, .letIn, .seq, .ascribe)")

#rules(
  ir(name: "T-Ctor", pv($ty("C")(g_1 : A_1, dots, g_k : A_k) "a constructor of" ty("D") (overline(x) : overline(X))$, $Omega tack.r overline(t) ev^* overline(v) : overline(A') tack.l Omega' quad A'_j equiv A_j [overline(a) slash overline(x)]$), $Omega tack.r ty("C")(overline(a); overline(t)) ev ty("C")(overline(a); overline(v)) : ty("D")(overline(a)) tack.l Omega'$),
  ir(name: "T-Pair", pv($Omega tack.r t ev v : A tack.l Omega_1 quad Omega_1 dot v tack.r u ev w : B tack.l Omega_2 dot v'$, $A, B "contain no" \&$), $Omega tack.r (t, u) ev (v', w) : A times B tack.l Omega_2$),
  ir(name: "T-Proj", $Omega tack.r t ev (v_1, v_2) : A_1 times A_2 tack.l Omega'$, $Omega tack.r t.i ev v_i : A_i tack.l Omega'$),
)
The typed argument judgement $ev^*$ is that of [T-Call]. In [T-Ctor] the parameters $overline(a)$ are evaluated and typed against $overline(X)$ as in [T-Ind] (premises omitted); where the examples omit them, they are inferred from the fields' types or the annotation. A constructor of an inductive declared in `Prop` is a declared proof, so [T-Erase] gives it the value ⋆: `refl : ⊤`, and $chevron.l h, k chevron.r : P and Q$ for `h : P` and `k : Q`. A projection of a neutral pair is a type error in the typing judgement (there are no neutral projections in the core); in the machine it is stuck. #lean("evalCore (.ctor, .zero, .succ, .tt, .pair, .fst, .snd)")

=== Type formers and transport

All type formers are erased, so each of these rules runs on a private copy ([T-Erase]).

#rules(
  ir(name: "T-Sort", $Omega tack.r ty("Prop") ev ty("Prop") : ty("Type")_0 tack.l Omega$),
  ir(name: "T-Type", $Omega tack.r ty("Type")_i ev ty("Type")_i : ty("Type")_(i+1) tack.l Omega$),
  ir(name: "T-Ind", pv($kw("inductive") ty("D") (overline(x) : overline(X)) : s := dots quad Omega tack.r overline(a) ev^* overline(v) : overline(A') tack.l Omega'$, $Omega";" (x_1 : T_1 |-> v_1, dots, x_(i-1) : T_(i-1) |-> v_(i-1)) tack.r X_i ev T_i "type" quad A'_i equiv T_i$), $Omega tack.r ty("D")(overline(a)) ev ty("D")(overline(v)) : s tack.l Omega'$),
  ir(name: "T-Prod", $Omega tack.r A ev T : s$, $Omega tack.r B ev T' : s'$, $Omega tack.r A times B ev T times T' : ty("Type")_0 union.sq s union.sq s'$),
  ir(name: "T-Ref", $Omega tack.r A ev T "type"$, $T "a data type"$, $Omega tack.r \&A ev \&T : ty("Type")_0$),
  ir(name: "T-Eq", $Omega tack.r A ev T "type"$, $Omega tack.r a ev v : T_a equiv T$, $Omega tack.r b ev w : T_b equiv T$, $Omega tack.r ty("Eq") A thin a thin b ev "eq"(T, v, w) : ty("Prop")$),
  ir(name: "T-Pi", pv($cfg(Omega, Pi(overline(x) : overline(A)). B) ev cfg(Omega', Pi) quad "sort"(Pi) = s$, $B = \&T "implies some" A_i = \&T_i$), $Omega tack.r Pi(overline(x) : overline(A)). B ev Pi : s tack.l Omega'$),
)
A Π-type whose codomain is a borrow type must have a borrow parameter: a returned borrow always derives from a borrow argument, as in Rust's lifetime elision, except that Ochr has no `'static` borrows (note 7 of @app-notes); [Def] imposes the same condition on the type of every `fix`. [T-Ref] admits borrows of data types only (note 11). In [T-Ind] the parameters are typed as the arguments of a call are ([Call-type]). In [T-Eq] the sides are typed one after the other on the same private copy (the whole `Eq` is a type); in [T-Pi] the sort is computed at the generic arguments. The rule for `Id` is [Id] of @app-conv. #lean("evalCore (.sort, .nat, .unit, .prod, .ref, .eq, .pi, .id, .tind)", "evalTInd", "isDataType", "sortOf")

#rules(
  ir(name: "T-J", pv($Omega tack.r A ev T "type" quad Omega tack.r a ev v_a : T_a equiv T quad Omega tack.r b ev v_b : T_b equiv T quad Omega tack.r P ev F : Pi$, $Omega tack.r h ev star : H equiv "eq"(T, v_a, v_b) quad Omega tack.r F(v_a) ev P_a : s quad Omega tack.r F(v_b) ev P_b : s quad Omega tack.r t ev v : T_t tack.l Omega' quad T_t equiv P_a$), $Omega tack.r ty("J")(A, a, b, P, h, t) ev v : P_b tack.l Omega'$),
)
`refl` proves `⊤` ([T-Ctor]), and so by conversion every reflexive equation. `J` takes its endpoints explicitly, because `Eq A a a` computes to `⊤` and no longer records them. Its motive may have any sort; with a motive into `Prop`, `J` is a proof and is erased. `A`, `a`, `b` and `P` are in type positions and `h` is a proof, so all five are typed on private copies, and the motive's calls $F(v_a)$, $F(v_b)$ are erased calls. #lean("evalCore (.prim \"J\")", "evalCtor", "unifyParams")

=== Functions and calls

#rules(
  ir(name: "T-Global", $f in Sigma$, $Omega tack.r f ev f : Sigma(f)."type" tack.l Omega$),
  ir(name: "T-Const", $c in Sigma$, $Omega tack.r c ev Sigma(c)."value" : Sigma(c)."type" tack.l Omega$),
  ir(name: "T-Fix", $cfg(Omega, kw("fix") dots) ev cfg(Omega', F)$, $tack.r F "ok"$, $Omega tack.r kw("fix") dots ev F : "typeof"(F) tack.l Omega'$),
)
A `fix` is checked where it is formed, by [Def] at its own generic call, with its captured values; its value is ⋆ if its Π-type returns proofs. #lean("evalCore (.const, .fix)", "checkFix")

*[Call-type]*. At the call point Ω of a call with function type $Pi = chevron.l overline(kappa) tack.r Pi(x_1 : A_1 dots x_n : A_n). B chevron.r$ and arguments $overline(w)$ of types $overline(A')$, push the frame of captured values and bind the parameters one by one, on a private copy:
#rules(
  ir(name: "Call-type", pv($Omega";" (overline(kappa), x_1 : T_1 |-> w_1, dots, x_(i-1) : T_(i-1) |-> w_(i-1)) tack.r A_i ev T_i "type" quad A'_i equiv T_i quad (1 <= i <= n)$, $Omega";" (overline(kappa), overline(x) : overline(T) |-> overline(w)) tack.r B ev T_B "type"$), $"callty"_Omega (Pi, overline(w) : overline(A')) = T_B$),
)
The free variables of `B` other than $overline(x)$ were captured when Π was formed; the caller's frames below are not in scope, but the footprints and owners of observations in `B` see them, which is how an induction hypothesis sees its caller's context. A borrow argument is moved into its parameter. #lean("callType")

Typed arguments are evaluated like [Args], each into a temporary, collecting their types: $Omega tack.r overline(u) ev^* overline(w) : overline(A') tack.l Omega'$.
#rules(
  ir(name: "T-Call", pv($Omega tack.r t_0 ev F : Pi tack.l Omega_0 quad Omega_0 dot F tack.r overline(u) ev^* overline(w) : overline(A') tack.l Omega_1 dot F' quad "no" w_i "is" bot$, $"callty"_(Omega_1)(Pi, overline(w) : overline(A')) = B' quad "rec"_(Omega_1)(F', overline(w)) quad cfg(Omega_1, F'(overline(w))) ev_"app" cfg(Omega', v)$), $Omega tack.r t_0(overline(u)) ev v : B' tack.l Omega'$),
  ir(name: "T-Call-proof", pv($Omega tack.r t_0 ev F : Pi tack.l Omega_0 quad Omega_0 dot F tack.r overline(u) ev^* overline(w) : overline(A') tack.l Omega_1 dot F' quad "no" w_i "is" bot$, $"callty"_(Omega_1)(Pi, overline(w) : overline(A')) = B' quad F' "returns proofs" quad "rec"_(Omega_1)(F', overline(w))$), $Omega tack.r t_0(overline(u)) ev star : B' tack.l Omega_1$),
)
[T-Call-proof] applies to a call whose callee returns proofs (@app-erasure), and [T-Erase] then discards $Omega_1$: a proof call's arguments are evaluated and checked, and its body is not run. In [T-Call] the callee's body runs in the machine ($ev_"app"$), since the callee was checked by its own [Def]; a call with a neutral head closes off at once. #lean("evalCall", "callFn", "callType")

*[Rec]*. The [Rec] stack holds an entry $(F, j, sigma_j)$ for every enclosing function being checked that declares `by xⱼ`, where $sigma_j$ is the entry value of $x_j$ at its generic call (through the borrow, for $\&ty("D")$). $"rec"_Omega (F, overline(w))$ holds when, for every entry $(F, j, sigma_j)$ of the stack for this `F`, the argument $w_j$, or its content if $w_j = "borrow"_ell u$, is in $"sub"(rho^*(sigma_j))$: a strict subterm, through any field, of the entry value as refined so far. Entries stay on the stack while nested functions and block arms are checked, so recursive calls there are checked too. #lean("recCheck", "headOnly")

=== Matches and case splitting

Let $m = kw("match") p {ty("C")_1 => t_1 | dots | ty("C")_m => t_m}$ match on a place of inductive type $ty("D")(overline(a))$, with `D` declared in `Type₀` and constructors $ty("C")_1, dots, ty("C")_m$ (the place's stored type must be $ty("D")(overline(a))$ for the `D` whose constructors the arms name: a match is never typed from its arms), and let $r_i = ty("C")_i (sigma_(i 1), dots, sigma_(i k_i))$ be the refinement to $ty("C")_i$ with fresh field values (@app-aux, item 7). On a constructor the typing judgement takes the arm, as the machine does, and checks only that arm. On an abstract value it splits ([Split]): each arm is checked under its refinement, and the match is then closed off as a stuck block, from which the rest of the program is checked once.

#rules(
  ir(name: "T-Match", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = ty("C")_i (overline(w))$, $Omega_1 tack.r t_i ev v : A tack.l Omega'$, $Omega tack.r m ev v : A tack.l Omega'$),
  ir(name: "Split", pv($acc^M_p (Omega) = Omega_1 quad cont_(Omega_1)(p) = sigma quad Omega_1 [sigma := r_i] tack.r t_i ev v_i : A_i tack.l Omega_i quad (1 <= i <= m)$, $B = T "with" A_i equiv T[r_i slash sigma] "for all" i, quad "or, without annotation," B = A_1 equiv dots equiv A_m$, $M = {x mid(|) Omega_1 (x) != bot, thick "some" Omega_i (x) = bot} quad cfg(Omega_1, "block"(Omega_1, m, B, M)) ev cfg(Omega', v)$), $Omega tack.r m ev v : B tack.l Omega'$),
  ir(name: "Split-gen", pv($acc^M_p (Omega) = Omega_1 quad cont_(Omega_1)(p) = n "a sealed program or an inert loan"$, $sigma "fresh," Delta(sigma) = "type"_(Omega_1)(p) quad Omega_1 [sigma slash n]^+ "with" n := sigma "recorded in" rho quad tack.r m ev v : B tack.l Omega'$), $Omega tack.r m ev v : B tack.l Omega'$),
)
In [Split] every arm is checked from $Omega_1$, and the arms' states and values are discarded; each refinement is applied to the environment, the goal and every stored type. `T` is the annotation of an enclosing `let x : T = m` (checking mode, $scripts(tack.r)^T$), whose type is then `T`; without one, the arms' types must be convertible. The block is run by the machine, from the unrefined $Omega_1$. [Split-gen] generalises a neutral head first (Lean's `generalize`): it replaces the neutral everywhere in Ω, the goal, the stored types and the annotation, and records it in ρ, so that the replacement persists when the neutral is derived again; the record is global, and survives a private copy in which it was made. Types are terms, so a match inside a type is checked in the same way. #lean("evalMatch", "evalMatchInd", "splitArmsThenClose", "ctorRefinement", "generalizeNeutral", "refine")

*Tail position.* The body of a definition is checked by a judgement $Omega tack.r t arrow.squiggly cal(L)$ whose result is the finite set $cal(L)$ of the _leaves_ of its case tree: triples $(Omega', v, A)$, each in the state of its own path, with the goal refined along that path. A match is in tail position when only trailing drops follow it.

#rules(
  ir(name: "Tail-split", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = sigma$, $Omega_1 [sigma := r_i] tack.r t_i arrow.squiggly cal(L)_i quad (1 <= i <= m)$, $Omega tack.r m arrow.squiggly cal(L)_1 union dots union cal(L)_m$),
  ir(name: "Tail-gen", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = n$, $Omega_1 [sigma slash n]^+ tack.r m arrow.squiggly cal(L)$, $Omega tack.r m arrow.squiggly cal(L)$),
  ir(name: "Tail-match", $acc^M_p (Omega) = Omega_1$, $cont_(Omega_1)(p) = ty("C")_i (overline(w))$, $Omega_1 tack.r t_i arrow.squiggly cal(L)$, $Omega tack.r m arrow.squiggly cal(L)$),
  ir(name: "Tail-let", $Omega tack.r t ev v : A tack.l Omega_1$, $Omega_1 + (x : A |-> v) tack.r u arrow.squiggly cal(L)$, $Omega tack.r kw("let") x = t";" u arrow.squiggly {"pop"_x (ell) mid(|) ell in cal(L)}$),
  ir(name: "Tail-seq", $Omega tack.r t ev v : A tack.l Omega_1$, $"drop"(Omega_1, v) = Omega_2$, $Omega_2 tack.r u arrow.squiggly cal(L)$, $Omega tack.r t";" u arrow.squiggly cal(L)$),
  ir(name: "Tail-end", $Omega tack.r t ev v : A tack.l Omega'$, $t "is not a match, let or sequence"$, $Omega tack.r t arrow.squiggly {(Omega', v, A)}$),
)
Here $"pop"_x (Omega_2 + (x : A' |-> v'), w, B) = (Omega_3, w', B)$ with $"drop"(Omega_2 dot w, v') = Omega_3 dot w'$, and an annotated `let` checks `t` against its annotation as in [T-Let-ann]. In [Tail-gen], σ is fresh and $n := sigma$ is recorded in ρ, as in [Split-gen]. An error on any path is an error. #lean("checkTail")

=== Matches on proofs <app-match-prop>

A match whose arms name the constructors of an inductive declared in `Prop` is a match on a proof. Its scrutinee's value is ⋆ (a proof parameter is bound to ⋆ at the generic call, and an erased term returns ⋆), so it is decided by the scrutinee's type, $"type"_(Omega_1)(p) = ty("D")(overline(v))$, and never by its content, and nothing is refined. `D` is a _subsingleton_ if it has no constructors, or one constructor all of whose field types have declared sort `Prop`; `False`, `True` and `And` are subsingletons. Arm $i$ is checked from $Omega_1^i$, which is $Omega_1$ if every field of $ty("C")_i$ is a proof, so that its fields hold ⋆ (@app-aux, item 1), and otherwise $Omega_1 [p |-> ty("C")_i (overline(v); overline(w))]$ with $w_j = star$ for a proof field and $w_j$ a fresh abstract value of the field's type for a data field, as [Def] binds parameters. The second case arises only in an erased match, on its private copy.

#rules(
  ir(name: "T-Match-prop", pv($acc^M_p (Omega) = Omega_1 quad "type"_(Omega_1)(p) = ty("D")(overline(v)), thick ty("D") "declared in" ty("Prop") "with the one constructor" ty("C")_1$, $Omega_1^1 tack.r t_1 ev v : A tack.l Omega' quad t_1 "is a declared proof unless" ty("D") "is a subsingleton"$), $Omega tack.r kw("match") p {ty("C")_1 => t_1} ev v : A tack.l Omega'$),
  ir(name: "T-Match-erased", pv($acc^M_p (Omega) = Omega_1 quad "type"_(Omega_1)(p) = ty("D")(overline(v)), thick ty("D") "declared in" ty("Prop") "with constructors" ty("C")_1, dots, ty("C")_m, thick m != 1$, $Omega_1^i tack.r t_i ev star : A_i tack.l Omega_i, thick t_i "a declared proof" quad (1 <= i <= m)$, $B = T "with" A_i equiv T, "or, for" m >= 2 "without annotation," B = A_1 equiv dots equiv A_m$), $Omega tack.r m ev star : B tack.l Omega_1$),
  ir(name: "Tail-prop", $acc^M_p (Omega) = Omega_1$, $"type"_(Omega_1)(p) = ty("D")(overline(v)), thick ty("D") "declared in" ty("Prop")$, $Omega_1^i tack.r t_i arrow.squiggly cal(L)_i quad (1 <= i <= m)$, $Omega tack.r m arrow.squiggly cal(L)_1 union dots union cal(L)_m$),
)
In [T-Match-erased], `T` is the annotation of an enclosing `let x : T = m`; with no arms, the annotation, or tail position, is the only source of the result type. [T-Match-erased] is a declared proof (@app-erasure), so [T-Erase] applies to it. In [Tail-prop], each $t_i$ is a declared proof unless `D` is a subsingleton; with no arms $cal(L) = emptyset$, and [Def]'s check on every leaf holds vacuously, which is ex falso. _Subsingleton elimination_ is the side condition "a declared proof unless `D` is a subsingleton": it is Lean's, and without it proof irrelevance is inconsistent (note 10 of @app-notes). The decision is stable under refinement, which changes a type's parameters but never its head; a scrutinee whose type is not (yet) an inductive, such as ⌈`Le(σ, σ')`⌉ before a split, has no rule, so it is a type error until a split has computed its type. The machine takes the same decisions from syntax alone: [Match-prop] runs a one-constructor match, and every other match on a proof, and every match with no arms, is a declared proof it never runs.
#lean("byTypeMatch", "scrutType", "evalMatchByType", "checkTail", "bindDataFields", "largeElim", "fieldTermIsProp")

=== Definitions

*[Def]*. Let `F` be a top-level function or a closure with captured values $overline(kappa)$ and code $kw("fix") f (x_1 : A_1 dots x_n : A_n) : B space [kw("by") x_j] := b$, and let $Pi = "typeof"(F)$, with generic state $Gamma = Gamma(Pi)$, parameter frame $phi = phi(Pi)$ and parameter types $overline(T)$ (@app-aux, item 10). Let $phi^+$ be φ with $f : Pi |-> F$ added when `F` declares `by`.

#rules(
  ir(name: "Def", pv($f "occurs in" b "only as the head of a call" quad [kw("by") x_j]: T_j in {ty("D")(overline(v)), \&ty("D")(overline(v))}, thick ty("D") "declared in" ty("Type")_0$, $B = \&T "implies some" T_i = \&T'_i$, $Gamma";" phi tack.r B ev G "type" quad Gamma";" phi^+ tack.r b arrow.squiggly cal(L) quad "with goal" G "and the [Rec] entry" (F, j, sigma_j) "pushed"$, $"for every" (Omega', v, A) in cal(L) "with refined goal" G': quad "pop"(Omega', v) "succeeds and" A equiv G'$), $tack.r F "ok"$),
)
In the first premise, `f` must also occur only as a call head inside nested functions and block arms. The goal `G` is the [Call-type] of the generic call $F(overline(a))$: `B` evaluated with each parameter bound to its generic argument, borrow parameters to borrows of the fresh owned places $c_i$, proof parameters to ⋆. Parameter types are evaluated left to right and stored with their bindings, where [Split] refines them. Popping the body's frame drops its bindings, so each borrow parameter ends and its owned place receives the final content; the result's type must then convert to the goal as refined on that path. A top-level `f` is added to Σ, with its type, code and erasure flag, before its body is checked, so that its recursive calls resolve; it is kept only if the check succeeds. #lean("checkFix", "checkDef (Check.lean)")

#rules(
  ir(name: "Ind", pv($ty("D") in.not Sigma quad s in {ty("Type")_0, ty("Prop")} quad m >= 0 quad epsilon";" (x_1 : T_1 |-> sigma_1, dots, x_(i-1) : T_(i-1) |-> sigma_(i-1)) tack.r X_i ev T_i "type" quad (1 <= i <= l)$, $"for every field" g_(i j) : A_(i j): quad A_(i j) "is a parameter, or is built from" ty("D")(overline(x)) ", declared inductive types and" times$, $Sigma + ty("D") ";" (overline(x) : overline(T) |-> overline(sigma)) tack.r A_(i j) ev T_(i j) : s_(i j) quad s_(i j) in {ty("Prop"), ty("Type")_0}$), $tack.r (kw("inductive") ty("D") (overline(x) : overline(X)) : s := ty("C")_1 (overline(g_1 : A_1)) | dots | ty("C")_m (overline(g_m : A_m))) "ok"$),
  ir(name: "Const", $epsilon tack.r A ev T "type"$, $epsilon tack.r t ev v : T' tack.l Omega'$, $T' equiv T$, $Sigma(c) = (T, v^bullet)$, $tack.r (c : A := t) "ok"$),
)
Parameters are checked like the parameters of a [Def], each bound to a fresh abstract value (or ⋆) while later ones and the fields are checked, and the recursive occurrences of `D` are at exactly those parameters (they are uniform: there are no indices). Field types are first-order data or parameters: they may mention the type being declared, but contain no `Π` and no `&`, which is strict positivity in its simplest form (note 4 of @app-notes). There may be no constructors (`False`), and the sort may be `Prop`, for any fields; what a match on a proof may produce is restricted instead (@app-match-prop). A definition without parameters is a constant: its body is checked against its type from the empty environment, and its value is stored ($v^bullet = star$ if `T` has declared sort `Prop`). A definition may not mention itself in its type. #lean("checkInd", "checkDef (Check.lean)")

== Well-formed environments <app-wf>

A state (Ω, Δ, Σ) is _well formed_ when the following hold. They are the four conditions of @sec-meta-model, spelled out, plus typing.

+ *Borrows are unique and outermost.* Each label ℓ has at most one $"borrow"_ell$ in Ω, and a borrow occurs only as the whole value of a binding or temporary: never inside data, a sealed program, a closure or a type.
+ *Loans are bound.* Every $"loan"_ell$ in Ω has its $"borrow"_ell$ in Ω, except inside a [Seal] run, where a loan whose borrow lies outside the run is inert. Outside sealed programs a label occurs as a loan at most once; inside sealed programs it may occur any number of times, since the hole of a returned borrow sits in the fill of every borrowed argument (@fig-app-close).
+ *Loans are acyclic.* The relation "$"loan"_ell$ occurs in the content of $"borrow"_m$" is acyclic, so $"owners"$ is well defined.
+ *Captures are values.* Closures and Π-closures capture no borrow and no ⊥, and sealed programs are closed.
+ *Arguments are exclusive.* At every call point, each argument is loan-free or is $"borrow"_ell u$ with `u` loan-free. This is [Close]'s precondition, and [Access] maintains it.
+ *Values have their types.* For each binding `x : A ↦ v`: $v = bot$ (moved out or ended), or $v = "loan"_ell$ and the content of $"borrow"_ell$ has type `A`, or `v` has type `A` (a neutral having the type recorded for it). Every σ occurring in Ω, in a stored type or in the goal has a type in Δ, and every top-level name has an entry in Σ.

That the machine preserves conditions 1 to 5 is property 2 of @fig-claims, mechanised for the first-order fragment of @sec-meta-mech.

== Notes on the definition <app-notes>

Notes 1–11 explain the side conditions of @fig-why that are finest-grained in this appendix: each gives a program that, without the condition, is a closed proof of a false equation (or, for note 8, makes normalisation diverge); by the disjointness rule of @app-conv, an equation between distinct constructors, such as `Eq Nat Z (S Z)`, is `False` itself. Notes 12–27 record choices where the definition could have gone either way.

+ *A function's erasure class is read from its codomain term.* A local `fix` is formed, and so checked by [Def], each time the term containing it is evaluated, and its codomain may depend on captured values. Deciding its class from the codomain's _value_ would give different answers on the two paths:
  ```
  U(n : Nat) : Type₀ := match n { Z => Prop | S _ => Prop }
  V(n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }
  LieL(n : Nat) : Id Nat (let h = λ(x : &Nat) : U(n) => (*x := S Z; V(n)); let c = Z; h(&c); c) (S Z) := refl
  BoomL : Eq Nat Z (S Z) := LieL(Z)
  ```
  At the generic `n` the codomain is ⌈`U(σ)`⌉, not a sort, so `h(&c)` runs and the statement is `⊤`. At `n = Z` the codomain is `U(Z) = Prop`, a sort, so `h(&c)` would be erased, `c` would stay `Z`, and `LieL(Z) : Eq Nat Z (S Z)`. Read from the term, `U(n)` is not syntactically a sort and has declared sort `Type₀`, so `h(&c)` runs on both paths.
+ *A stuck block is erased only when every arm is a declared proof.* Treating the block as a call, whose codomain is the match's type, erases a block whose type is a sort, while the same match run directly is not a call and is not erased:
  ```
  LieB(n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; c) Z := refl
  BoomB : Eq Nat (S Z) Z := LieB(Z)
  ```
  Nor may the block be erased by its type inferred from the arms, which is computed. With `g : Π(y : Nat). V(Z)` and `f := λ(x : &Nat) : V(Z) => (*x := S Z; g(0))`, the block `match m { Z => f(&c) | S _ => f(&c) }` has inferred type `V(Z)`, which computes to `⊤`, of sort `Prop`; but `f` returns data (the declared sort of `V(Z)` is not `Prop`), so at `m = Z` the match runs `f(&c)` and writes `c`, while the block erased at the generic call would not. A block that is not erased is always safe, because its sealed programs re-run the arms, which decide for themselves.
+ *A proof is declared, not computed.* Classifying a variable as a proof because its value is ⋆ differs between the paths:
  ```
  LieH(g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  BoomH : Eq Nat Z (S Z) := LieH((λ(y : Nat) : V(Z) => refl))
  ```
  At the generic call `h` holds a sealed program, so `(c := S Z; h)` runs and the statement is `⊤`; at the instance `g(0)` returns ⋆, a value-based reading erases the sequence, `c` stays `Z`, and the statement is `Eq Nat Z (S Z)`. Reading clause 4 of @app-erasure by the type the typing judgement computes would be stable on its own, but combined with the syntactic class of calls it is the block example of note 2; so every clause is read from declarations.
+ *Inductive declarations are strictly positive.* A negative field gives a closed proof of `False` that is never run:
  ```
  inductive Bad : Type₀ := Mk(f : Π(x : Bad). False)
  L(b : Bad) : False := match b { Mk(f) => f(b) }
  Bad4 : False := L(Mk(λ(x : Bad) : False => L(x)))
  ```
  `L(…)` is a proof call, so it is typed by [Call-type] alone and its diverging body never runs. [Ind]'s first-order fields exclude `Bad`.
+ *Generalisation records are global, and fresh names are never reused.* A match inside a type whose scrutinee is a sealed program is generalised on the type's private copy, and the formed type mentions the new σ:
  ```
  inductive Box := Mk(x : Nat)
  Double(n : Nat) : Nat by n := match n { Z => Z | S p => S (S (Double(p))) }
  Esc(n : Nat, m : Box) : Id Nat (let b = Double(n); match b { Z => 0 | S _ => 1 }) (match m { Mk(x) => match x { Z => 0 | S _ => 1 } }) :=
    match m { Mk(x) => match x { Z => refl | S _ => refl } }
  Bad5 : Eq Nat 1 0 := Esc(1, Mk(0))
  ```
  If the record `⌈Double(σ)⌉ := σ_g` were discarded with the copy, and σ_g's name reissued to the field `x` when the body splits `m`, the goal would equate the two and `Esc` would check; its instance is `Eq Nat 1 0`.
+ *A borrow-typed result is observed through a written value* ([Obs-borrow]). Ending a returned borrow with its current content forgets where it points, so `PickX(x, y : &Nat) : &Nat := x` and `PickY(x, y : &Nat) : &Nat := y` would be convertible; transport from `Π(x y : &Nat). Id Unit (let r = h(x, y); *r := S Z) (*x := S Z)`, true of `PickX`, then proves it of `PickY`, whose instance at two zeros is `Eq Nat 0 1 ∧ Eq Nat 1 0`, which is `False`.
+ *A borrow-returning function type needs a borrow parameter* ([T-Pi], [Def]). Closing off a call `g(5)` with `g : Π(n : Nat). &Nat` would return a borrow whose hole lies in no owner, so writes through it are unobservable. The function `PF(x : &Nat, e : Id Unit (*x := 0) (*x := 1)) : False := e` checks, since at its generic call the statement observes the owner of `x` and computes to `Eq Nat 0 1`, which is `False`. Then `QF(g : Π(n : Nat). &Nat) : False := PF(g(5), refl)` checks too, because at this call site the statement observes nothing and computes to `⊤`: it proves that `Π(n : Nat). &Nat` is empty, although safe Rust inhabits it with a leaked `'static` borrow, and any such opaque inhabitant gives a closed proof of `False`.
+ *The head guard covers neutral-headed calls* ([App-neutral-head]). Closing off a sealed program's head call when its head is an abstract function with codomain `&T` and two or more borrow arguments creates a new hole; reading an owner ends it, re-normalises a sealed program of the same shape, and so on for ever.
+ *Confinement is a fail-safe.* For a correctly classified term the private copy already discards its effects. If the two paths ever disagreed about whether a term is erased, the path that erases a term with outside effects rejects it rather than silently discarding effects the other path keeps. A place _outlives_ an erased term when its root is a position of the environment the term starts from; the exception for erased calls covers exactly the borrows and moves that evaluate their arguments.
+ *Subsingleton elimination* (@app-match-prop). A match on a proof of an inductive with two constructors cannot produce data. With `inductive Bool := false | true`:
  ```
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  IsL(h : Or(True, True)) : Bool := match h { Inl(p) => true | Inr(q) => false }
  Irr(h : Or(True, True), k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
  Boom : False := Irr(Inl(refl), Inr(refl))
  ```
  Without the condition, `IsL` and `Irr` check: at the generic call `h` and `k` are both ⋆, so both sides are the stuck ⌈`IsL(⋆)`⌉. `Boom` is still rejected, because `Inl(refl)` is a proof, whose value is ⋆, so `Irr`'s instance is `Eq Bool` ⌈`IsL(⋆)`⌉ ⌈`IsL(⋆)`⌉, which is `True`. Only if a proof also kept its constructor would `Boom` prove `False`, as it would in a system where proofs keep their constructors. The condition is required all the same: `IsL` has no meaning in the set model once proofs are irrelevant (`Eq Bool (IsL(Inl(refl))) (IsL(Inr(refl)))`, provable by `refl`, reads `Eq Bool true false` there); `IsL(Inl(refl))` is a closed `Bool` that is stuck for ever, against canonicity and adequacy; and a two-constructor match on a proof, which cannot take an arm, has a value only because every arm is a proof. For `False`, `True` and `And` the type determines the arm and the fields are proofs, so nothing is chosen.
+ *Borrows are only of data, and `&` only at the top of a declared type* ([T-Ref], [T-Borrow]). If `&A` were allowed for every type `A`, a borrow of a type would quantify over `Type₀` inside `Type₀`:
  ```
  Impred : Type₀ := Π(x : &Type₀) (a : *x). *x
  PolyId(x : &Type₀, a : *x) : *x := a
  SelfApp(u : Unit) : Impred := let T = Impred; PolyId(&T, PolyId)
  ```
  `Π(X : Type₀)(a : X). X` lives in `Type₁`, but through the borrow it would live in `Type₀`, which becomes impredicative: with the impredicative `Prop : Type₀` below it, the rules contain Girard's System U⁻, in which Hurkens' paradox is a closed term, and no set model exists. And if a codomain could compute to a borrow type, as in `F(n : Nat, x : &Nat) : (match n { Z => &Nat | S _ => Nat })`, [Close] would read the data row at the generic call, where the match is stuck, while `F(0, &a)` returns a live borrow at the instance; `G(n, a) := let r = F(n, &a); let r2 = r; let r3 = r; a` is accepted at the generic call and reads a moved borrow at `n = 0`. Because data is read from the evaluated head of `A`, a type variable is rejected too: `SwapT(A : Type₀, x : &A, y : &A)` is not well formed, since `A` could be `Type₀` itself.
+ *Proofs are not run.* A proof call's arguments are evaluated and its [Call-type] and [Rec] checked, on a private copy; its body is never run ([T-Call-proof]), and the machine skips proofs altogether ([Erase-proof]). Running and skipping agree, since erased terms run on a private copy.
+ *The order of [Access].* Loans are ended from the root of the place outward, then left to right inside its content. The resolution should not depend on the order (property 7 of @fig-claims, proved for two endings).
+ *A match on a constructor checks only the arm taken*, in typing as in the machine ([T-Match]).
+ *[Close]'s row is chosen by the declared codomain* (`Unit`, `&T`, anything else), as @lem-stable (4) requires. A codomain that computes to `Unit` without being syntactically `Unit` gets the data row, and there is no η for `Unit`, so a statement such as `Id Unit (let c = *x; G(&c, Z)) ()`, where `G`'s codomain `UU(n)` has `UU(Z) = Unit`, needs induction on `*x` rather than `refl`.
+ *A discarded value* (`t; u`) holding a live loan is an error, like a dying owned binding.
+ *Stuck-block moves.* A whole variable is moved into a block if some arm, when checked, leaves it ⊥, or if it is a borrow variable read or assigned as a whole. Captures are ordered by the position of their root, then by length, and their arguments are evaluated in that order.
+ *Footprint.* A place rooted at a borrow variable contributes its owners even when it is only read, and a variable holding ⊥ contributes nothing. Owners are positions, so a temporary can be an owner, when a type is formed while arguments are in flight.
+ *`J`.* `A`, `a`, `b` and `P` are type positions and `h` is a proof, so none of them runs in the machine; `J`'s value is `t`'s. The motive may have any sort. `J` is a declared proof when its motive is syntactically a function into `Prop`, or when `t` is a declared proof.
+ *Universes.* $A times B$ lives in $ty("Type")_0 union.sq s_A union.sq s_B$, `&A` in `Type₀`, an inductive type in its declared sort, and `Π` is impredicative in `Prop`. `And`'s parameters have type `Prop`, so [T-Ind] requires both conjuncts to be propositions.
+ *Recursion* requires the declared decreasing parameter to have an inductive type declared in `Type₀`, or to be a borrow of one (so recursion is never on a proof); strict subterms range over all fields.
+ *Conversion* is the least relation of @app-conv. Π-types are compared by instantiating their binders at generic arguments ([Conv-pi]); comparing their captured values and code instead would reject a closure that captures a variable where a closed Π-type is expected, and would not unfold type abbreviations under binders. There is no η rule, and no η for `Unit`.
+ *An unannotated non-tail match* needs its arms' types, each computed in its own refined state, to be convertible; an annotated one checks each arm against the annotation refined for that arm.
+ *Syntax.* `Nat` and `Unit` are presented as declared types (`Nat` with field `1`). The implementation builds them in, declares `False`, `True` and `And` in its library exactly as in @fig-syntax, and checks those declarations like any other ([Ind]); it also has pair sub-places (`p.1`, `p.2` of a pair) and conveniences outside the core (`cong`, `trans`, `symm`, the ascription `(t : A)`, `λ` and `→`).
+ *A match on a proof is decided by the scrutinee's stored type* (@app-match-prop), the type kept with its binding and refined by [Split], not by its declared type term. In `SubM` (@sec-overview), `h` is declared `Le(y, *x)`, and its stored type becomes `False` after the two splits, so `match h {}` checks there. Requiring the declared term itself to be an inductive would also be stable, and would make `SubM` write `let e : False = h; match e {}`. This consults a normal form, but only in a way that fails safe: a split only refines the stored type, which keeps an inductive head, so a less refined path sees a neutral and rejects, and never sees a different head. A match with no arms is a declared proof; if one is reached while a sealed program is re-normalised under a refinement that makes a hypothesis false, its value is ⋆, which only a context holding a proof of `False` can observe.
+ *Disjointness without injectivity.* $"eq"$ sends two distinct constructors to `False` but does not decompose two equal ones: `Eq Nat (S a) (S b)` stays an equation. Injectivity is sound in the same model, and would let a pure proof that recurses on a copy (`AddZero(p)` in @sec-overview) drop its congruence step; in-place proofs do not need it, because the borrow structure performs that step. It is a separate, optional extension. The model validates disjointness as an instance of `propext`: both sides denote ∅.
+ *Captured values keep their declared types.* A closure or Π-closure records, with each captured value, the declared type and proof flag of the binding it was read from. So a `λ` or `Π` whose body reads a captured proof, or captured neutral data such as a sealed program, can be typed: `let n = *x` after `AddM(&*x, 1)`, followed by `λ(y : Nat) : Nat => n`, is accepted. Whether a captured variable is a proof is read from its declaration, never from its value ⋆ (note 3).
