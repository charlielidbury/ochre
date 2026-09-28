#import "../style.typ": *

// Numbered statements (definitions, theorems, lemmas, corollaries) sharing one counter, referable by label.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let dg(x) = $#x^dagger$

We show that Ochr is consistent and that its symbolic evaluator computes what programs actually do. Following Aeneas @aeneas, we read a computation as a pure function, in Lean's type theory, from the current contents of its borrows to its result and their final contents; backward functions appear here and only here. Types get a set-theoretic interpretation in the style of Carneiro's model of Lean @theory-of-lean. Sealed programs are backward functions (@thm-sim), a call affects only what it is passed (@thm-frame), borrows may end in any order (@thm-canon), the checker's decisions and its evaluation are stable under refinement (@lem-stable, @thm-natural), and the model validates typing and conversion (@thm-sound), so no false proposition has a closed proof (@cor-consistent). @sec-meta-mech says which of these are mechanised.

== The model <sec-meta-model>

*What consistency is relative to.* The model has two parts. _Computations_ translate into $"CIC"_L$, the intensional type theory of Lean 4 @lean4: universes `Prop : Type₀ : Type₁ …`, an impredicative `Prop` with definitional proof irrelevance, inductive types, and the axiom `propext`. Every machine step becomes a conversion of $"CIC"_L$ (@thm-sim), so nothing extensional is needed, and this is the translation the Lean development targets.

_Types_ need more, because Ochr's conversion identifies propositions that CIC only proves equivalent: the `Eq` rules (@sec-obs), and the type [Call-type] computes at a call site, which Ochr identifies with the one proved at the generic call (@thm-frame). No translation into intensional CIC keeps these as conversions. Equality reflection would, but Carneiro's set model does not cover the resulting extensional theory: it relies on unique typing, which reflection breaks. Eliminating reflection @reflection-elim does not help either, since it is established only for sources without an impredicative, definitionally proof-irrelevant `Prop`.

We therefore interpret Ochr's types _directly_ in set theory, following Carneiro's construction. Given values for the abstract values, a type denotes a set, a proposition a subset of ${•}$, a term an element of its type's denotation, and a function type a set of forward and backward functions (below); on computations this is Carneiro's interpretation of their $"CIC"_L$ translation. Carneiro needs unique typing to decide whether a `λ` or `Π` denotes a proof, `•`, or a set-theoretic function or product. In Ochr that decision is syntactic: every definition declares its codomain, erasure is decided from declared sorts and syntactic positions, never from normal forms, and universes are not cumulative (@sec-typing). So the interpretation is defined by recursion on typing derivations, and consistency is relative to ZFC with one inaccessible cardinal per universe level used. Unlike the translation of computations, this interpretation exists on paper only.

*Types.* Data and propositions denote themselves: $dg(sans("Nat")) = NN$, $dg((sans("Eq") A space a space b)) = (dg(a) = dg(b))$, and so on. Consider a function type whose borrow parameters are `xᵢ : &Tᵢ` at the positions $I$. Let $D_i = dg(T_i)$ for $i in I$ and $D_j = dg(A_j)$ otherwise, and let $"Fin" = product_(i in I) dg(T_i)$ be the final contents of the borrowed places. The function type denotes forward and backward functions, restricted by the relation $R$ of @def-inj:

$ dg((Pi(overline(x) : overline(A)). B)) = R_(Pi(overline(x) : overline(A)). B) subset.eq Pi(overline(d) : overline(D)). "Out"_B (overline(d)), quad
  "Out"_B (overline(d)) = cases(
    dg(B)(overline(d)) & "if" B "is a proposition,",
    dg(B)(overline(d)) times "Fin" & "if" B "is borrow-free data,",
    dg(T) times (dg(T) -> "Fin") quad & "if" B = \&T.
  ) $

Here $dg(B)(overline(d))$ denotes $B$ at the generic call of [Def], with the borrowed places holding $overline(d)$. We write $"fwd"_F (overline(d))$ for the first component of $F(overline(d))$ and $"back"_F (overline(d))$ for the tuple of final contents. In the third case $"back"_F (overline(d))$ is a function of the value the caller eventually leaves in the returned borrow: Aeneas's backward function, whose region abstraction is here just a $lambda$. A proposition-valued function has no $"Fin"$ component, because proofs run on a private copy (@sec-typing); so a proof is not a state transformer, and proof irrelevance at its type is sound. Were proofs effectful, irrelevance would identify `λx. ⋆` with `λx. (*x := 7; ⋆)` at `Π(x : &Nat). ⊤`.

#thm([Definition], [injectivity relation], [
  For each type $A$ define $R_A subset.eq dg(A)$ by induction on $A$. For base types, propositions and universes, $R_A = dg(A)$; $R$ is taken componentwise on pairs, and $R_(\&T) = R_T$. For a function type, $F in R_(Pi(overline(x) : overline(A)). B)$ iff, for all $overline(d)$ with $d_i in R_(T_i)$ for $i in I$ and $d_j in R_(A_j)$ otherwise, $"fwd"_F (overline(d)) in R_B$ and, if $B = \&T$, $"back"_F (overline(d))$ is injective. Injectivity is joint: equal tuples of final contents come only from equal final values of the returned borrow.
]) <def-inj>

This is the one place where the model is a logical relation rather than a translation, and it is forced. By [Call-type], Ochr refutes `Id Unit (let r = h(&a); *r := Z) (let r = h(&a); *r := S Z)` for every _abstract_ `h : Π(x : &Nat). &Nat`, which says that `h`'s backward function is injective. That is false of arbitrary set-theoretic functions and true of definable ones (@lem-backinj); thunkability @fire-triangle and parametricity @bowman-cps are modelled the same way, by cutting a function space down to its definable part. The principle is internal, so an opaque definition of a borrow-returning type is an injectivity _assumption_, and binding it to an arbitrary external function is unsound.

*Environments and terms.* Abstract values become variables, listed in $Gamma_Omega$. A loan name $ell$ becomes a variable $h_ell$, a _hole_ for the final content of borrow $ell$, wherever the loan sits. The _view_ $dg(Omega)$ is the tuple of translated contents: a borrow is read as its current content, $dg(("borrow"_ell v)) = dg(v)$, and a loan as its hole, $dg("loan"_ell) = h_ell$. The _resolution_ $rho_Omega$ substitutes $h_ell := dg(v_ell)[rho_Omega]$ for each $"borrow"_ell v_ell$ in Ω; it means "end every borrow".

A run determines the _shapes_ of the environments it passes through: which bindings exist, and where borrows and loans sit. On one run's shapes a term translates to a state-passing function on views (@fig-model). A symbolic run and a concrete run of the same term can pass through different shapes (the remark in @sec-meta-nat gives one), so the translation is defined per run, and @thm-natural relates runs through their resolutions. A sealed program means what it computes: $dg(seal(t)) = "Run"(t)$, the result of $dg(t)$ run from the empty view. A definition becomes a strong recursion on the entry value of its decreasing parameter. An observation becomes the tuple of its result and resolved footprint, and `Id` the equation between two such tuples.

#figure(kind: image, supplement: [Figure],
  block(width: 100%)[
    $ "End"_ell & : quad s |-> (s without "holder"(ell))[h_ell := s."holder"(ell)] \
      "match" p {dots} & : quad s |-> "natCase" (s.p) space (dg(t_Z)(s[p := 0])) space (lambda sigma'. space dg(t_S)(s[p := "succ" sigma'])) \
      f(overline(a)), space B "data" & : quad s |-> "let" (r, overline(phi)) = dg(f)(overline(u), overline(w)) "in" (r, (s without overline(a))[h_(ell_i) := phi_i]) \
      f(overline(a)), space B = \&T & : quad s |-> "let" (c, beta) = dg(f)(overline(u), overline(w)) "in" (c, (s without overline(a))[h_(ell_i) := beta_i (h_k)]) \
      t "a type or a proof" & : quad s |-> (dg(v), s) $
  ],
  caption: [Key state-passing clauses. $overline(u)$ are the current contents of the borrow arguments, whose loans are $ell_i$, and $overline(w)$ are the other arguments; $k$ is fresh. $s without x$ removes $x$'s binding, and $"holder"(ell)$ is the binding that holds $"borrow"_ell$. Ending a borrow is a substitution. A call is one application: Aeneas's forward and backward translations fused, with the region abstraction as the substitution $h_(ell_i) := beta_i (h_k)$. An erased term leaves the view unchanged.],
) <fig-model>

*Well-formedness.* An environment is _well formed_ when each borrow is held once; every loan is bound by a borrow the environment holds, or lies inside a sealed program, and only there may it occur twice; the relation "loan $ell$ occurs in the content of borrow $m$" is acyclic; and every value that is read, moved, borrowed or passed is loan-free, which [Access] enforces.

#thm([Lemma], [invariance; termination of concrete runs], [
  Machine steps preserve well-formedness. For programs accepted by [Rec], every concrete run terminates in a value or a borrow error.
]) <lem-wf>

_Proof sketch._ Acyclicity holds because a loan enters a borrow's content only through a reborrow of a sub-place, and [Access] stops reads from copying loans. A concrete run never runs types or proofs, which are erased, so a reducibility argument over the simple structure of runtime data and closures reduces termination to the well-founded recursion that [Rec] enforces. ∎

We do not know whether type checking is decidable. The checker normalises types, which may use large elimination, `J` with type-valued motives, and an impredicative, proof-irrelevant `Prop`, and Abel and Coquand show that these ingredients can defeat normalisation @abel-coquand. Ochr never normalises proofs, which may avoid their counterexample, but we have no proof. Nothing below depends on decidability, because the model interprets derivations, which are finite.

== Sealed programs are backward functions

#thm([Theorem], [simulation], [
  Let Ω be well formed and $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ by the symbolic machine. Then, on that run's shapes, $dg(t)(dg(Omega)) equiv (dg(v), dg(Omega'))$ in $"CIC"_L$, with $Gamma_Omega$ and the holes of Ω free. The sealed programs that [Close] produces at a call $f(overline(a))$ with borrow contents $overline(u)$ and other arguments $overline(w)$ satisfy
  $ dg(seal("L; C")) equiv "fwd"_f (overline(u), overline(w)), quad dg(seal("L; C; " c_i)) equiv "back"_f (overline(u), overline(w))_i, quad dg(seal("L; let r = C; *r := " "loan"_k "; " c_i)) equiv "back"_f (overline(u), overline(w))(h_k)_i. $
  The same holds for every concrete run, on its own shapes.
]) <thm-sim>

The equations are definitional. A sealed program is not an approximation of a backward function: it is a name, in source syntax, for an application of one.

_Proof sketch._ By induction on the derivation. Reads, borrows and assignments project and update the view. [End] is the substitution of @fig-model. A match on a constructor is ι-reduction, and an unfolding call is δβ followed by the induction hypothesis. For [Close], the equations hold by unfolding $"Run"$; the call clause yields these projections whether or not $dg(f)(overline(u), overline(w))$ reduces further, so the partial run can safely be discarded. [Seal] runs $t$, and the induction hypothesis on that run gives the normal form. ∎

The hardest case ends a borrow $k$ whose loan is a hole inside sealed programs. The model substitutes $h_k := dg(w)$ into $"Run"(t)$; the machine substitutes $w$ into $t$ and runs it again. These agree, $"Run"(t)[h_k := dg(w)] equiv "Run"(t[w slash "loan"_k])$, only because [Seal] treats a loan whose borrow lies outside the run as inert. A run that could end $k$ would reach outside the sealed program, and $"Run"(t)$ would not be a function of $t$.

== A call affects only what it is passed

Consider a call at Ω whose borrow arguments hold the loans $overline(ell)$, and a set $O$ of owners of those loans. The tuple of the owners' resolved contents, once the final contents $overline(phi)$ of the borrowed places are known, is
$ "Ctx"_O (overline(phi)) = (rho_Omega (o)[h_(overline(ell)) := overline(phi)])_(o in O). $
Because loans are variables, this is an ordinary function of $overline(phi)$.

#thm([Theorem], [frame], [
  Let Ω be well formed.
  + _Locality._ Let $Omega = Omega_1 union.plus Omega_2$, with the free variables of $t$ bound in $Omega_1$ and every loan occurring in $Omega_1$ having its borrow in $Omega_1$. Then $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ iff $cfg(Omega_1, t) arrow.b.double cfg(Omega_1', v)$ with $Omega' = Omega_1' union.plus Omega_2 theta$, where $theta$ fills the loans in $Omega_2$ of the borrows the run ended.
  + _Call effect._ A call runs as its body from its own frame alone, then substitutes each borrow argument's final content for its loan (the call clause of @fig-model).
  + _Call typing._ Let $f : Pi(overline(x) : overline(A)). B$ be called at Ω, after its arguments are evaluated, and let $O$ be the set of _all_ owners of their loans. Each `Id`-atom of $B$ observed at Ω is the one observed at the generic call, mapped through $"Ctx"_O$ on the footprint components. So when $"Ctx"_O$ is injective, the type computed at Ω and the type proved at the generic call denote the same set.
]) <thm-frame>

#thm([Lemma], [owners and injectivity], [
  If every function value in Ω lies in $R$ and $O$ contains every owner of every occurrence of $overline(ell)$, then $"Ctx"_O$ is injective. The condition on $O$ is necessary: for `Pick(n, &a, &b)` closed off on an abstract `n`, $"Ctx"_({a})$ is constant in the branch where the result points into `b`.
]) <lem-inj>

#thm([Lemma], [backward functions are injective], [
  If every opaque definition denotes an element of $R$, then so does every definition accepted by [Def] and [Rec]. In particular the backward map of every definable $f : Pi(overline(x) : overline(A)). \&T$ is injective.
]) <lem-backinj>

Part (3) is what [Call-type] relies on, and it is why an induction hypothesis arrives wrapped in its caller's context: in `AddMZero`, $((), S space square)$.

_Proof sketch._ Part (1) is by induction on the run: there are no globals and closures capture no borrows, so a rule touches only places reachable from $t$. Part (2) is part (1) applied to the callee's frame, which is loan-closed because arguments are loan-free. For part (3), both observations run on private copies and so, by part (1), change nothing outside the arguments; resolving at the end plugs the arguments' final contents into their owners, which is $"Ctx"_O$. Two equations mapped through an injective function are equivalent, and propositions with the same truth value denote the same set.

For @lem-inj, $"Ctx"_O$ is built from constructors, from backward maps applied at a hole, which are injective because function values lie in $R$, and from components constant in the hole; the last kind keeps injectivity only if an owner carrying the hole is kept. @lem-backinj is the fundamental lemma of $R$, proved by induction on derivations together with @thm-sound: interpreting a body needs $R$ for the functions it calls and for its function-typed parameters, which range over $R$ by definition. A returned borrow's hole sits either under constructors (a reborrow of a sub-place of a parameter) or at an injective backward map (an inner call or block), and no rule discards its final value: [Access] ends the loans in a content before overwriting or dropping it, and [End] substitutes into every occurrence. ∎

The hardest case is part (2) when $f$ returns a borrow. As the frame pops, the parameter's borrow still holds the returned borrow's loan, and [End] moves that content, loan included, into the caller's owner. The owner then holds $K["loan"_r]$, which depends on something the caller has not yet produced; in the model this is $beta_i (h_r) = K[h_r]$. Its injectivity has to hold for every future of $r$, so it needs an induction over definitions and cannot be read off Ω.

== Borrows may end in any order

#thm([Theorem], [canonical observation], [
  Let Ω be well formed.
  + Ending two borrows in either order and re-normalising gives environments with the same resolution.
  + If a run of $t$ from Ω succeeds while ending some borrows earlier than the lazy strategy would, then the lazy run succeeds too, with the same borrow-free result and the same resolution.
  Hence $⟦t⟧_Omega^W$ does not depend on when borrows end, and `Id` is well defined.
]) <thm-canon>

_Proof sketch._ (1) Ending $ell$ is the substitution $h_ell := dg(v_ell)$, and two such substitutions commute because loans are contained in borrows acyclically. (2) Suppose a run ends $ell$ earlier than the lazy run does. After that point it cannot use $ell$, which now holds $bot$, nor reach the positions of $ell$'s loan, since any access to their container would make the lazy run end $ell$ there too. So both runs substitute the same content. ∎

The hardest case of (1) ends a hole inside a sealed program, which re-runs it; a completed sealed run ends its own borrows before reading its result, and $"Run"$ is compositional (@thm-sim), so the order of two re-runs does not matter. Part (2) absorbs the extra borrow endings of the symbolic machine in @thm-natural.

== The two paths agree <sec-meta-nat>

A statement is evaluated along two paths: once at a definition's generic call, where calls and matches on abstract values close off, and again at each instance, where they run. [Call-type] identifies the two results, and so does [Split] for a stored type refined by a case split. So any decision taken differently on the two paths is an inconsistency. We write α for a _refinement_, which substitutes values for abstract values, definable closures for abstract functions, and values for holes; it covers both a case split and the instantiation of a statement at a call site. $Omega arrow.b$ is Ω with its sealed programs re-normalised, and $approx$ is equality up to renaming of loans.

#thm([Lemma], [closing off commutes with refinement], [
  For a term $t$ at Ω and a refinement α, the following agree between $t$ at Ω and $t alpha$ at $Omega alpha$:
  + which subterms are erased;
  + which places each closed-off stuck block captures, and in which modes, and the places of each footprint;
  + whether the arms of each match are well typed;
  + the [Close] row of each call.
]) <lem-stable>

_Proof sketch._ Each decision is read from syntax or declarations, never from a normal form, and a refinement changes only normal forms.
+ A call is erased iff its callee's declared codomain, at the callee's generic call, is a sort or has sort `Prop`. Any other term is erased iff it stands in a type position or its declared type has sort `Prop`. Universes are not cumulative, so these sorts are fixed.
+ Pattern variables are resolved to the sub-places they denote before captures and footprints are computed, so a write through `p` in `match *x { S p => … }` counts as a write to `*x` on both paths.
+ [Split] checks the arms under every refinement of the scrutinee, including for matches inside types, and a match whose scrutinee is still neutral after α stays closed off.
+ The row is read from the declared result type, and `&A` occurs only syntactically. ∎

Each clause is needed: deciding any of them from a normal form admits a closed proof of `Eq Nat Z (S Z)` or a program that goes wrong at runtime (@sec-typing lists the attacks).

#thm([Theorem], [naturality], [
  Let Ω be well formed, $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ by the symbolic machine, and α a refinement of Ω.
  + _Operationally_, $((Omega' alpha) arrow.b, (v alpha) arrow.b)$ is, up to $approx$, the result of a run of $t alpha$ from $(Omega alpha) arrow.b$ that ends some borrows earlier than the lazy strategy would. Hence the lazy run $cfg((Omega alpha) arrow.b, t alpha) arrow.b.double cfg(Omega'', v'')$ exists. It has the same resolution, and the same result when $v$ is borrow-free.
  + _Observationally_, for every footprint $W$ fixed on both sides, $(⟦t⟧_Omega^W alpha) arrow.b = ⟦t alpha⟧_(Omega alpha)^W$.
]) <thm-natural>

#thm([Corollary], [adequacy], [
  Let α be ground, instantiating every opaque definition with a definable function. Then the lazy run of $t alpha$ closes nothing off: it is a concrete run, it terminates, and it computes the instantiated symbolic observation. So every `Id` the checker computes on abstract inputs holds of the program on every concrete input. The checker is sound in this sense, but not complete.
]) <cor-adequacy>

_Proof sketch._ Part (1) is by induction on the symbolic derivation. Every step except closing off commutes with α on the nose: α substitutes atoms, [Match] takes an arm only on a constructor, which α preserves, and by @lem-stable the same terms are erased and the same blocks captured on both paths. At a [Close] of a call $C$ with argument contents $overline(u)$, the refined run reaches $C$ with $overline(u) alpha$ and runs its body alone (@thm-frame). Re-normalising the sealed programs runs the same body on the same values, since [Seal] unfolds the head call once and lets inner calls close off exactly where the direct run does. By determinism, the two runs stop at the same stuck match or complete alike.

They differ only in where a returned borrow's loan lives: concretely in the one owner the borrow points into, symbolically as a hole in the fill of every borrow argument it might point into. So the symbolic run can end a returned borrow at an access that the concrete run performs without ending it: an extra [End], and nothing else. Part (2) follows from (1) and @thm-canon (2), since an observation resolves every borrow. The footprint must be fixed on both sides, because its places are syntactic but their owners are not: when α removes a hole from a sealed program, the owner that loses it contributes a component neither side changes, and the ⊤ rules strip it. ∎

The hardest case is a returned borrow when no possible owner but the target was accessed before α. Concretely, the callee's frame pops while its parameter's borrow still holds the returned loan, so the target owner receives $K["loan"_q]$. Symbolically, re-normalising $seal("L; let r = C; *r := " "loan"_k "; " c_i)$ runs $C$, leaving $c_i$ holding $K["loan"_(q')]$, writes the inert $"loan"_k$ through $r$, and reads $c_i$, where [Access] ends $q'$; the result $K["loan"_k]$ matches up to renaming. If another possible owner was accessed, the symbolic run has already ended the borrow, and only the resolutions agree.

*Remark (holes over-approximate returned borrows).* This counterexample to naturality up to renaming alone is machine-checked (@sec-meta-mech). Take `Pick(n, x, y) := match n { Z => x | S _ => y }`, $Omega = {n |-> sigma, a |-> 1, b |-> 2, r |-> (), z |-> ()}$, `t = r := Pick(n, &a, &b); z := b` and $alpha = (sigma := sans("Z"))$. Symbolically, `Pick` closes off with its hole in the fills of both `a` and `b`, so reading `b` ends the returned borrow, and after refinement the state is ${a |-> 1, b |-> 2, r |-> bot, z |-> 2}$. Concretely `r` borrows `a` and stays live: ${a |-> "loan"_q, b |-> 2, r |-> "borrow"_q 1, z |-> 2}$. No renaming relates the two, but they resolve alike. The cost is completeness: `r := Pick(n, &a, &b); z := b; match n { Z => *r := 5 | S _ => () }` runs for every concrete `n` but is rejected, because `r` is already $bot$ in the `Z` arm. Rust draws the same line, treating `r` as borrowing both `a` and `b` for as long as `r` is live.

*Naturality and thunkability.* In a pure type theory, stability of normal forms under substitution is the standard requirement behind normalisation by evaluation and dependent matching. In Ochr the terms inside types have effects, so it can fail in a new way. Suppose erasure were decided from normal forms, and take the family `U(n)` of @sec-typing, which is `Prop` for every `n`, with `W(x : &Nat, n : Nat) : U(n) := *x := S Z; V(n)`. At the generic `n`, `U(σ)` is stuck, so the call `W(&c, n)` runs and writes `c`; at `n = Z` it has type `Prop`, so it is erased and `c` is untouched. A lemma `Id Nat (let c = Z; W(&c, n); c) (S Z)`, proved by `refl` at the generic call, then states `Eq Nat Z (S Z)` at `Z`. This is precisely the "desynchronisation between effects performed in the term and effects performed in the type" from which Pédrot and Tabareau derive the fire triangle @fire-triangle, and each clause of @lem-stable closes one route to it. They also show that, in their forcing model, a computation is thunkable exactly when it is natural: running then restricting equals restricting then running @fire-triangle[Prop. 18]. @lem-stable and @thm-natural (2) are the naturality Ochr needs: on everything a type can see the two paths agree, and operationally they differ only by borrow endings, which no type can see. We claim a correspondence of invariants, not an embedding into their calculus.

== The model validates typing and conversion

#thm([Theorem], [soundness of the model], [
  Let the program be accepted by [Def] and [Rec]. For every valuation of the abstract values:
  + a type of sort $s$ at Ω denotes an element of the universe $s$ denotes;
  + convertible types denote the same set;
  + if $Omega tack.r t arrow.b.double v : A tack.l Omega'$, then on that run's shapes $t$ denotes a function from views of Ω to elements of $A$'s denotation and views of $Omega'$;
  + every definition denotes an element of its type's denotation, and so lies in $R$.
]) <thm-sound>

_Proof sketch._ By induction on derivations, together with @lem-backinj.
- *[Def].* The goal is the [Call-type] of the generic call, which is $dg(B)(overline(d))$ by definition.
- *[Split] on an abstract value* is dependent elimination on a variable; applying the refinement to the environment, the goal and every stored type _is_ its motive.
- *[Split] on a sealed program* first generalises the program. This is well typed because stored types are kept in normal form, so every dependency on the program is a syntactic occurrence. It is sound only because matching first ends every loan inside a neutral head; otherwise generalising would take a loan out of its borrow's scope.
- *A non-tail [Split].* The checked arms define the closed-off block's function, and the rest of the program starts from its application (@thm-sim).
- *[Rec]* makes the interpretation a well-founded recursion on data read from the environment, never on a proof, so no subterm check passes through a cast along a `propext` equality, the route by which Coq's guard condition was found to clash with `propext`.
- *Erased terms* leave the view unchanged, and by @lem-stable they are the same terms at every instance.
- *Conversion.* Equal normal forms denote equally (@thm-sim). Closures are compared by the observation of their generic call, which is what determines their denotation; comparing results alone would identify `λx. (*x := S Z)` with `λx. ()`. The `Eq` rules hold because propositions with the same truth value denote the same set, and convertible terms denote equal elements, so a reflexive `Eq` denotes ${•}$. `J` denotes transport, which needs the endpoints `J` carries. All proofs denote `•`. ∎

The hardest case is [Call-type], which uses everything above, and also the capture of a Π-type's free variables at formation, without which a call site's type is not an instance of the proved statement.

#thm([Corollary], [consistency], [
  No closed term has type `Eq Nat Z (S Z)` or `Π(P : Prop). P`. More generally, if $tack.r t : P$ for a closed proposition $P$, then $P$ holds in the set model. Both claims are relative to ZFC with one inaccessible cardinal per universe level used.
]) <cor-consistent>

_Proof._ By @thm-sound, a closed proof denotes an element of its proposition's denotation, and `Eq Nat Z (S Z)` denotes $[0 = 1] = emptyset$. ∎

Proofs are never run, so consistency cannot lean on the checker diverging; it rests on @thm-sound alone.

== What is mechanised <sec-meta-mech>

The accompanying Lean 4 development mechanises the effectful layer for a first-order fragment of Ochr, following an earlier version of the rules: natural numbers, unit and pairs; places, borrows and matching; recursive definitions, including ones that return borrows; opaque definitions standing for abstract functions; and erased proofs, with erasure a per-definition flag. There are no closures, types or stuck blocks, so the later rule changes concerning those do not arise. The machine is a clocked big-step interpreter over Lean data. Proved with no `sorry`, using only Lean's three standard axioms:
- parts (1) and (2) of @thm-frame, as equations at every amount of fuel, so stuck runs and errors coincide too;
- that the sealed program [Close] writes into a borrowed place normalises to the content the call itself leaves there, the machine-level form of the second equation of @thm-sim, assuming the call's result and final contents contain no loans (which should follow from @lem-wf);
- that two borrow endings commute, which is @thm-canon (1) without re-normalisation of sealed programs;
- that the machine is deterministic, monotone in fuel, computed by its interpreter, and equivariant under injective renamings of loans (the $approx$ of @thm-natural).

Executable tests check the other [Close] equations on small ground inputs, owner sets, [Access], erasure, and the counterexample in the remark of @sec-meta-nat. The invariance part of @lem-wf is stated, but its proof is still a `sorry`, and the remaining [Close] equations are in progress. The translation into $"CIC"_L$ itself, and with it the rest of @thm-sim, is not started, nor are @thm-canon (2), @lem-stable, @thm-natural, @cor-adequacy, @lem-inj and @lem-backinj. The set-theoretic interpretation, and so @thm-sound and @cor-consistent, exists on paper only, as do termination for higher-order programs and the correspondence with the forcing model.
