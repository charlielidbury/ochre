#import "../style.typ": *

// Numbered statements (definitions, theorems, lemmas, corollaries) sharing one counter, referable by label.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let dg(x) = $#x^dagger$

We show that Ochr is consistent and that the checker's symbolic evaluation computes what programs do. Following Aeneas @aeneas, a computation is read as a pure function from the current contents of its borrows to its result and their final contents; types get a set-theoretic interpretation after Carneiro @theory-of-lean. We give precise statements and the hardest case of each argument; @sec-meta-mech says what is mechanised.

== The model <sec-meta-model>

*What consistency is relative to.* Computations translate into $"CIC"_L$, the intensional type theory of Lean 4 @lean4, with an impredicative, definitionally proof-irrelevant `Prop` and `propext`, and every machine step becomes a conversion there (@thm-sim). Types need more. Ochr's conversion identifies propositions that CIC only proves equivalent, through the `Eq` rules (@sec-obs) and through [Call-type], which identifies a call site's type with the one proved at the generic call (@thm-frame). So no translation into intensional CIC preserves conversion. Equality reflection would, but Carneiro's set model relies on unique typing, which reflection breaks, and eliminating reflection @reflection-elim is established only for sources without an impredicative, proof-irrelevant `Prop`. We therefore interpret Ochr's types directly in sets, following Carneiro's construction and extending his interpretation of the $"CIC"_L$ translation of computations. Carneiro needs unique typing to decide whether a `λ` or `Π` denotes a proof or a set-theoretic function; in Ochr that decision is syntactic, because definitions declare their codomains, erasure is read from declared sorts and syntactic positions, and universes are not cumulative (@sec-typing). The interpretation is therefore defined by recursion on derivations, and consistency is relative to ZFC with one inaccessible cardinal per universe level. It exists on paper only.

*Types.* An inductive declaration in `Type₀` denotes the least set closed under its constructors, at each value of its parameters, so `Nat` denotes $NN$; distinct constructors have disjoint images. One in `Prop` denotes a subsingleton, ${•}$ if that least set is inhabited and $emptyset$ otherwise: `False` denotes $emptyset$, `True` denotes ${•}$, and `And(P, Q)` denotes $dg(P) inter dg(Q)$. `Eq A a b` denotes $[dg(a) = dg(b)] subset.eq {•}$. For a function type with borrow parameters `xᵢ : &Tᵢ` at positions $i in I$, let $D_i = dg(T_i)$ for $i in I$, $D_j = dg(A_j)$ otherwise, and $"Fin" = product_(i in I) dg(T_i)$, the final contents of the borrowed places:

$ dg((Pi(overline(x) : overline(A)). B)) = R_(Pi(overline(x) : overline(A)). B) subset.eq Pi(overline(d) : overline(D)). "Out"_B (overline(d)), quad
  "Out"_B (overline(d)) = cases(
    dg(B)(overline(d)) & "if" B "is a proposition,",
    dg(B)(overline(d)) times "Fin" & "if" B "is borrow-free data,",
    dg(T) times (dg(T) -> "Fin") quad & "if" B = \&T.
  ) $

Here $dg(B)(overline(d))$ is $B$ at the generic call of [Def]. We write $"fwd"_F$ and $"back"_F$ for the two components of $F(overline(d))$. For a returned borrow, $"back"_F (overline(d))$ is Aeneas's backward function: it maps the value the caller eventually leaves in the borrow to the final contents. A proposition has no $"Fin"$ component: proofs run on a private copy (@sec-typing), so they are not state transformers, and proof irrelevance is sound.

#thm([Definition], [injectivity relation], [
  $R_A subset.eq dg(A)$ is defined by induction on $A$. For base types, propositions and universes $R_A = dg(A)$; $R$ is componentwise on pairs, and $R_(\&T) = R_T$. For a function type, $F in R_(Pi(overline(x) : overline(A)). B)$ iff, for all $overline(d)$ with $d_i in R_(T_i)$ for $i in I$ and $d_j in R_(A_j)$ otherwise, $"fwd"_F (overline(d)) in R_B$, and, if $B = \&T$, $"back"_F (overline(d))$ is injective: equal tuples of final contents come only from equal final values of the returned borrow.
]) <def-inj>

$R$ is forced. By [Call-type], Ochr proves that every _abstract_ `h : Π(x : &Nat). &Nat` has an injective backward function, which is false of arbitrary set-theoretic functions (@lem-backinj). Consequently an opaque definition of a borrow-returning type is an injectivity assumption, and binding it to an arbitrary external function is unsound.

*Terms.* Abstract values become variables. A loan $ell$ becomes a variable $h_ell$, a _hole_ for the final content of its borrow. The _view_ $dg(Omega)$ reads a borrow as its current content and a loan as its hole; the _resolution_ $rho_Omega$ substitutes each hole by its borrow's content, that is, it ends every borrow. On the _shapes_ of one run (which bindings exist, and where borrows and loans sit), a term translates to a state-passing function on views (@fig-model). A sealed program denotes what it computes, $dg(seal(t)) = "Run"(t)$, the result of $dg(t)$ run from the empty view; a definition is a well-founded recursion on the entry value of its decreasing parameter; and `Id` is the equation between the tuples of result and resolved footprint. A symbolic run and a concrete run of one term can pass through different shapes (@sec-meta-nat), so the translation is defined per run, and runs are related through their resolutions.

#figure(kind: image, supplement: [Figure],
  block(width: 100%)[
    $ "End"_ell & : quad s |-> (s without "holder"(ell))[h_ell := s."holder"(ell)] \
      "match" p {dots} & : quad s |-> "natCase" (s.p) space (dg(t_Z)(s[p := 0])) space (lambda sigma'. space dg(t_S)(s[p := "succ" sigma'])) \
      f(overline(a)), space B "data" & : quad s |-> "let" (r, overline(phi)) = dg(f)(overline(u), overline(w)) "in" (r, (s without overline(a))[h_(ell_i) := phi_i]) \
      f(overline(a)), space B = \&T & : quad s |-> "let" (c, beta) = dg(f)(overline(u), overline(w)) "in" (c, (s without overline(a))[h_(ell_i) := beta_i (h_k)]) $
  ],
  caption: [Key clauses of the translation. $overline(u)$ are the contents of the borrow arguments, whose loans are $ell_i$, and $overline(w)$ the other arguments; $k$ is fresh. Ending a borrow is a substitution, and a call is one application, with Aeneas's region abstraction as the substitution $h_(ell_i) := beta_i (h_k)$. An erased term leaves the view unchanged.],
) <fig-model>

An environment is _well formed_ when each borrow is held once, every loan is bound by a held borrow or lies inside a sealed program (the only place a loan may occur twice), loans nest in borrows acyclically, and every value read, moved or passed is loan-free.

#thm([Lemma], [invariance; termination], [
  Machine steps preserve well-formedness. For programs accepted by [Rec], every concrete run terminates.
]) <lem-wf>

Concrete runs never evaluate types or proofs, so termination reduces to the recursion [Rec] enforces. Whether type checking is decidable is open: types may combine large elimination, `J` with type-valued motives and an impredicative, proof-irrelevant `Prop`, which Abel and Coquand show can defeat normalisation @abel-coquand. Nothing below depends on decidability, since the model interprets derivations.

== Sealed programs are backward functions

#thm([Theorem], [simulation], [
  If Ω is well formed and $cfg(Omega, t) arrow.b.double cfg(Omega', v)$, then on that run's shapes $dg(t)(dg(Omega)) equiv (dg(v), dg(Omega'))$ in $"CIC"_L$. The sealed programs that [Close] produces at $f(overline(a))$, with borrow contents $overline(u)$ and other arguments $overline(w)$, satisfy
  $ dg(seal("L; C")) equiv "fwd"_f (overline(u), overline(w)), quad dg(seal("L; C; " c_i)) equiv "back"_f (overline(u), overline(w))_i, quad dg(seal("L; let r = C; *r := " "loan"_k "; " c_i)) equiv "back"_f (overline(u), overline(w))(h_k)_i. $
]) <thm-sim>

The equations are definitional: a sealed program is a name, in source syntax, for an application of a backward function. The routine steps are conversions ([End] is substitution, a match on a constructor is ι, unfolding is δβ). The hardest case ends a borrow $k$ whose loan is a hole inside sealed programs. The model substitutes $h_k := dg(w)$ into $"Run"(t)$; the machine substitutes $w$ into $t$ and runs it again. These agree only because [Seal] treats a loan whose borrow lies outside the run as inert: a run that could end $k$ would reach outside the sealed program, and $"Run"(t)$ would not be a function of $t$.

== A call affects only what it is passed

For a call at Ω whose borrow arguments hold the loans $overline(ell)$, and a set $O$ of owners of those loans, let $"Ctx"_O (overline(phi)) = (rho_Omega (o)[h_(overline(ell)) := overline(phi)])_(o in O)$: the owners' resolved contents, as a function of the final contents $overline(phi)$ of the borrowed places.

#thm([Theorem], [frame], [
  Let Ω be well formed.
  + _Locality._ If $Omega = Omega_1 union.plus Omega_2$, $t$'s free variables are bound in $Omega_1$, and every loan in $Omega_1$ has its borrow in $Omega_1$, then $t$ runs from Ω iff it runs from $Omega_1$, with the same result, and $Omega_2$ changes only by filling the loans of the borrows the run ended.
  + _Call effect._ A call runs its body from its own frame alone, then substitutes each borrow argument's final content for its loan.
  + _Call typing._ Let $O$ be _all_ owners of the loans of a call's borrow arguments. Each `Id`-atom of the callee's codomain, observed at the call site, is the one observed at the generic call mapped through $"Ctx"_O$; so when $"Ctx"_O$ is injective, the two types denote the same set.
]) <thm-frame>

#thm([Lemma], [owners and injectivity], [
  If every function value in Ω lies in $R$ and $O$ contains every owner of every occurrence of $overline(ell)$, then $"Ctx"_O$ is injective. The condition on $O$ is necessary.
]) <lem-inj>

#thm([Lemma], [backward functions are injective], [
  If every opaque definition lies in $R$, so does every definition accepted by [Def] and [Rec].
]) <lem-backinj>

Part (3) is what [Call-type] rests on, and why an induction hypothesis arrives in its caller's context, as $((), S space square)$ in `AddMZero`: both observations run on private copies, which by (1) change nothing outside the arguments, and resolving at the end plugs the arguments' final contents into their owners. @lem-inj holds because $"Ctx"_O$ is built from constructors, from backward maps (injective by $R$), and from components constant in the hole, which is why an owner carrying the hole must be kept; for `Pick(n, &a, &b)` closed off on an abstract `n`, $"Ctx"_({a})$ is constant. @lem-backinj is the fundamental lemma of $R$, proved jointly with @thm-sound; function-typed parameters range over $R$ by definition.

The hardest case is part (2) for a returned borrow. As the frame pops, the parameter's borrow still holds the returned borrow's loan, so the caller's owner receives $K["loan"_r]$, which depends on a value the caller has not yet produced. Its injectivity, $beta_i (h_r) = K[h_r]$, must hold for every future of $r$, so it cannot be read off Ω: it needs the induction over definitions, and the fact that no rule discards a hole's final value ([Access] ends the loans in a content before overwriting or dropping it).

== The two paths agree <sec-meta-nat>

A statement is evaluated along two paths: at a definition's generic call, where calls and matches on abstract values close off, and directly at each instance. [Call-type] and [Split] identify the results, so any decision taken differently on the two paths is an inconsistency. A _refinement_ α substitutes values for abstract values, definable closures for abstract functions, and values for holes; it covers both case splits and instantiation at a call site. $Omega arrow.b$ re-normalises Ω's sealed programs, and $approx$ is equality up to renaming of loans.

#thm([Lemma], [closing off commutes with refinement], [
  For $t$ at Ω and a refinement α, the following are the same for $t$ at Ω and $t alpha$ at $Omega alpha$: (1) which subterms are erased, and which matches are decided by the type of a proof; (2) which places each closed-off stuck block captures, in which modes, and the places of each footprint; (3) whether each match's arms are well typed; (4) each call's [Close] row.
]) <lem-stable>

Each decision is read from syntax or declarations, never from a normal form, and α changes only normal forms: (1) a call is erased iff its callee's codomain _term_, read without evaluating it, is a sort or has declared sort `Prop`, a stuck block is erased exactly when each of its arms is, universes are not cumulative, and a match on a proof requires its scrutinee's type to be an inductive declared in `Prop`, a head that α cannot change; (2) pattern variables are resolved to the sub-places they denote before captures and footprints are computed, so a write through `p` in `match *x { S p => … }` is a write to `*x` on both paths; (3) arms are checked under every refinement of the scrutinee, inside types too, and a match still neutral after α stays closed off; (4) the row is read from the declared result type. Deciding any of these from normal forms admits a closed proof of `False` (@sec-typing).

#thm([Theorem], [schedule independence and naturality], [
  Let Ω be well formed.
  + Ending two borrows in either order gives the same resolution. If a run of $t$ succeeds while ending some borrows earlier than the lazy strategy would, the lazy run succeeds with the same resolution and the same borrow-free result. Hence observations do not depend on when borrows end, and `Id` is well defined.
  + If $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ symbolically and α refines Ω, then $((Omega' alpha) arrow.b, (v alpha) arrow.b)$ is, up to $approx$, the result of a run of $t alpha$ from $(Omega alpha) arrow.b$ that ends some borrows early. With (1), for every footprint $W$ fixed on both sides, $(⟦t⟧_Omega^W alpha) arrow.b = ⟦t alpha⟧_(Omega alpha)^W$.
]) <thm-natural>

#thm([Corollary], [adequacy], [
  If α is ground and instantiates every opaque definition with a definable function, the lazy run of $t alpha$ is concrete, terminates, and computes the instantiated symbolic observation: every `Id` the checker computes on abstract inputs holds on every concrete input.
]) <cor-adequacy>

Every step except [Close] commutes with α on the nose, by @lem-stable. At a [Close], re-normalising the sealed programs runs the call's body alone on the refined arguments (@thm-frame), as the direct run does, and [Seal] unfolds only the head call, so inner calls close off where the direct run's do. The hardest case is a returned borrow. The concrete run puts its loan into the one owner it points into, but the symbolic hole sits in the fill of every borrow argument it might point into, so the symbolic run ends the borrow when _any_ possible owner is accessed. That is an extra [End], which (1) absorbs. The owners of a footprint are therefore not syntactic: when α removes a hole from a sealed program, the owner that loses it is unchanged on both sides, and the ⊤ rules strip its component.

The extra [End] is real and costs completeness. With `Pick(n, x, y) := match n { Z => x | S _ => y }` and `n` abstract,
```
r := Pick(n, &a, &b); z := b; match n { Z => *r := 5 | S _ => () }
```
runs for every concrete `n` but is rejected: reading `b` ends `r` symbolically, since `Pick`'s hole sits in the fills of both `a` and `b`, so `r` is dead in the `Z` arm. After `z := b` the symbolic and concrete states agree only after resolution (machine-checked, @sec-meta-mech), which is why (2) is stated up to early ends; Rust likewise treats `r` as borrowing both places while it is live.

*Naturality and thunkability.* With effects in types, stability under substitution can fail in a new way. If erasure were read from normal forms, take `U(n)` of @sec-typing, which is `Prop` for every `n`, and `W(x : &Nat, n : Nat) : U(n) := *x := S Z; V(n)`. At the generic `n`, `U(σ)` is stuck, so `W(&c, n)` runs and writes `c`; at `n = Z` it would be erased. Then `Id Nat (let c = Z; W(&c, n); c) (S Z)`, proved by `refl` generically, states `Eq Nat Z (S Z)` at `Z`. This is exactly Pédrot and Tabareau's "desynchronisation between effects performed in the term and effects performed in the type" @fire-triangle, which @lem-stable rules out. They show that a computation is thunkable iff it is natural, that is, running then restricting equals restricting then running @fire-triangle[Prop. 18]; @lem-stable and @thm-natural are the naturality Ochr needs. We claim a correspondence of invariants, not an embedding into their calculus.

== Soundness and consistency

#thm([Theorem], [soundness of the model], [
  For a program accepted by [Def] and [Rec], and every valuation of the abstract values: types of sort $s$ denote elements of $s$'s universe; convertible types denote the same set; if $Omega tack.r t arrow.b.double v : A tack.l Omega'$, then on that run's shapes $t$ denotes a function from views of Ω to elements of $A$'s denotation and views of $Omega'$; and every definition lies in $R$.
]) <thm-sound>

The proof is by induction on derivations, jointly with @lem-backinj; most cases read the translation backwards. [Split] on a sealed program generalises it first, which is well typed because stored types are normal forms, so every dependency on the program is syntactic, and sound only because matching first ends every loan inside a neutral head. Closures are convertible when their generic calls have the same observation, which determines their denotation; comparing results alone would identify `λx. (*x := S Z)` with `λx. ()`. The `Eq` rules hold because convertible terms denote equal elements and propositions with the same truth value are equal; disjointness is one such instance, both sides denoting $emptyset$, and in $"CIC"_L$ it is `propext` applied to the no-confusion property of constructors. A match on a proof is interpreted through the proof's type: for `False` it is the empty function, and for a declaration with one constructor whose fields are proofs it is the arm, at the only element. Subsingleton elimination is what makes this well defined, since the value of a match producing data cannot depend on which proof it was given. [Rec] recurses on data, never on proofs, so no subterm check passes through a cast along a `propext` equality. The hardest case is [Call-type], which combines @thm-frame (3), @lem-inj, @lem-backinj and @thm-natural, and needs Π-types to capture their free variables when formed, so that a call site's type is an instance of the proved one.

#thm([Corollary], [consistency], [
  Relative to ZFC with one inaccessible per universe level, no closed term has type `False` (nor, therefore, `Eq Nat Z (S Z)`, which computes to it), and every closed proposition with a closed proof holds in the set model.
]) <cor-consistent>

== What is mechanised <sec-meta-mech>

A Lean 4 development mechanises the effectful layer for a first-order fragment, following an earlier version of the rules: natural numbers, unit, pairs, places, borrows, matching, recursive definitions (including borrow-returning ones), opaque definitions and erased proofs, with no closures, types, inductive propositions or stuck blocks. The machine is a clocked big-step interpreter. Proved with no `sorry`, using only Lean's standard axioms: parts (1) and (2) of @thm-frame, as equations at every amount of fuel; that the sealed program [Close] writes into a borrowed place normalises to the content the call leaves there (the machine-level form of the second equation of @thm-sim), assuming the call's results are loan-free, which should follow from @lem-wf; that two borrow endings commute (the first claim of @thm-natural (1), without re-normalisation); and that the machine is deterministic, monotone in fuel, and equivariant under renaming of loans. Executable tests check the other [Close] equations on ground inputs, owner sets, erasure and the `Pick` example. The invariance part of @lem-wf is stated with its proof still a `sorry`, and the remaining [Close] equations are in progress. Not started: the translation into $"CIC"_L$, the rest of @thm-natural, @lem-stable, @lem-inj and @lem-backinj. The set-theoretic interpretation, and so @thm-sound and @cor-consistent, exists on paper only.
