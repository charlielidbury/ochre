#import "../style.typ": *

// Numbered statements (theorems, lemmas, corollaries) sharing one counter, referable by label.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let dg(x) = $#x^dagger$

We show that Ochr is consistent and that its symbolic evaluator computes what programs actually do, using a model in Lean's type theory. The model reads a program that mutates what it borrows as a pure function from the current contents of its borrows to its result and their final contents. This is Aeneas's functional translation @aeneas; its backward functions appear here and only here. The results below say that sealed programs _are_ backward functions (@thm-sim). They say that a call affects only what it is passed (@thm-frame), that borrows may end in any order (@thm-canon), and that symbolic evaluation commutes with instantiation on everything a type can observe (@thm-natural). And they say that typing and conversion are preserved, so no false proposition has a closed proof (@thm-sound, @cor-consistent).

== The model <sec-meta-model>

*Target.* We translate into $"CIC"_L$, the type theory of Lean 4 @lean4 as axiomatised by Carneiro @theory-of-lean. It has universes `Prop : Type₀ : Type₁ …`, an impredicative `Prop` with definitional proof irrelevance, inductive types, and the axiom `propext`, which says that logically equivalent propositions are equal. Computations need nothing extensional: each machine step becomes an intensional conversion (@thm-sim). Propositions, however, need `propext`, because Ochr's conversion identifies propositions that CIC only proves equivalent: the rules for `Eq` (@sec-obs) and, above all, a codomain computed at a call site with the codomain proved at the generic call (@thm-frame). Conversion is therefore preserved into $"ECIC"_L$, which adds equality reflection, or into $"CIC"_L$ up to transports along `propext` equalities, as in the elimination of reflection @reflection-elim. Both have Carneiro's set model. In it propositions with the same truth value are equal sets, and an inhabited equation forces its two sides equal.

*Types.* Data and propositions translate homomorphically, $dg(sans("Nat")) = NN$, $dg((sans("Eq") A space a space b)) = (dg(a) = dg(b))$, and so on. Consider a function type with borrow parameters `xᵢ : &Tᵢ` at the positions $I$. Let $D_i = dg(T_i)$ for $i in I$ and $D_j = dg(A_j)$ otherwise, and let $"Fin" = product_(i in I) dg(T_i)$, the final contents of the borrowed places. It translates to forward and backward functions:

$ dg((Pi(overline(x) : overline(A)). B)) = Pi(overline(d) : overline(D)). "Out"_B (overline(d)), quad
  "Out"_B (overline(d)) = cases(
    dg(B)(overline(d)) & "if" B "is a proposition,",
    dg(B)(overline(d)) times "Fin" & "if" B "is borrow-free data,",
    dg(T) times (dg(T) -> "Fin") quad & "if" B = \&T\, "with" dg(T) -> "Fin" "injective".
  ) $

Here $dg(B)(overline(d))$ translates $B$'s normal form at the generic call of [Def], with the borrowed places holding $overline(d)$. We write $"fwd"_f$ and $"back"_f^i$ for the result and the $i$-th final content of $dg(f)$; in the third case $"back"_f^i$ is a function of the returned borrow's final value. Three features carry weight.

- _A proof is not a state transformer._ Erased terms run on a private copy (@sec-typing), so a proposition-valued function has no $"Fin"$ component, and proof irrelevance at its type is sound. If proofs had effects, proof irrelevance would identify `λx. ⋆` with `λx. (*x := 7; ⋆)` at `Π(x : &Nat). ⊤`, although they are different functions into $NN$, and transport would prove `⊥`.
- _Backward functions await the final value_ of the returned borrow, which the caller supplies later. Aeneas's region abstraction is here just a $lambda$.
- _Injectivity_ is where the model is a logical relation rather than a translation, and it is forced. By [Call-type], Ochr refutes `Id Unit (let r = h(&a); *r := Z) (let r = h(&a); *r := S Z)` for every _abstract_ `h : Π(x : &Nat). &Nat`, which says that `h`'s backward function is injective. That fails for arbitrary CIC functions but holds for definable ones (@lem-backinj), much as thunkability @fire-triangle and parametricity @bowman-cps hold only on the definable part of a function space.

*Environments and terms.* Abstract values become CIC variables, listed in $Gamma_Omega$. A loan name $ell$ becomes a variable $h_ell$, a _hole_ for the final content of borrow $ell$, wherever the loan sits. The _view_ $dg(Omega)$ is the tuple of translated contents, with $dg(("borrow"_ell v)) = dg(v)$ (a borrow is seen as its current content) and $dg("loan"_ell) = h_ell$. The _resolution_ $rho_Omega$, the substitution $h_ell := dg(v_ell)[rho_Omega]$ for each $"borrow"_ell v_ell$ in Ω, means "end every borrow". A run fixes the _shape_ of its environments (where bindings, borrows and loans sit) independently of the abstract values; that is what the borrow checker guarantees. On fixed shapes a term becomes a state-passing function on views (@fig-model). A sealed program means what it computes, $dg(seal(t)) = "Run"(t)$, the result of $dg(t)$ run from the empty view. A definition becomes strong recursion on its decreasing parameter's entry value. An observation becomes the tuple of its result and resolved footprint, and `Id` becomes the CIC equation between two such tuples.

#figure(kind: image, supplement: [Figure],
  block(width: 100%)[
    $ "End"_ell & : quad s |-> (s without "holder"(ell))[h_ell := s."holder"(ell)] \
      "match" p {dots} & : quad s |-> "natCase" (s.p) space (dg(t_Z)(s[p := 0])) space (lambda sigma'. space dg(t_S)(s[p := "succ" sigma'])) \
      f(overline(a)), space B "data" & : quad s |-> "let" (r, overline(phi)) = dg(f)(overline(u), overline(w)) "in" (r, (s without overline(a))[h_(ell_i) := phi_i]) \
      f(overline(a)), space B = \&T & : quad s |-> "let" (c, beta) = dg(f)(overline(u), overline(w)) "in" (c, (s without overline(a))[h_(ell_i) := beta_i (h_k)]) \
      t "a type or a proof" & : quad s |-> (dg(v), s) $
  ],
  caption: [Key state-passing clauses; $overline(u)$ are the current contents of the borrow arguments, with loans $ell_i$, $overline(w)$ the other arguments, $k$ fresh. Ending a borrow is a substitution; a call is one CIC application, Aeneas's forward and backward translations fused, with the region abstraction as the substitution $h_(ell_i) := beta_i (h_k)$; an erased term leaves the view unchanged.],
) <fig-model>

*Well-formedness.* An environment is _well formed_ when four conditions hold. Each borrow is held once. Every loan is bound by a borrow it holds, or lies inside a sealed program, and only there may a loan occur twice. The relation "loan $ell$ occurs in the content of borrow $m$" is acyclic. And every value read, moved, borrowed or passed is loan-free, as [Access] enforces.

#thm([Lemma], [invariance and termination], [
  Machine steps preserve well-formedness. For programs accepted by [Rec], every run terminates in a value, a borrow error, or a stuck state.
]) <lem-wf>

_Proof sketch._ Acyclicity is preserved because a loan enters a borrow's content only through a reborrow of a sub-place, and [Access] stops reads from copying loans. Termination is a reducibility argument over the simple structure of runtime values. It reduces to well-founded recursion, which is exactly [Rec]: every recursive call is strictly below the entry value, and $f$ occurs nowhere else. ∎

== Sealed programs are backward functions

#thm([Theorem], [simulation], [
  If Ω is well formed and $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ by the symbolic machine, then $dg(t)(dg(Omega)) equiv (dg(v), dg(Omega'))$ in $"CIC"_L$, in context $Gamma_Omega$ and the holes of Ω. In particular, the sealed programs that [Close] produces at a call $f(overline(a))$ with borrow contents $overline(u)$ and other arguments $overline(w)$ satisfy
  $ dg(seal("L; C")) equiv "fwd"_f (overline(u), overline(w)), quad dg(seal("L; C; " c_i)) equiv "back"_f^i (overline(u), overline(w)), quad dg(seal("L; let r = C; *r := " "loan"_k "; " c_i)) equiv "back"_f^i (overline(u), overline(w))(h_k). $
  The same holds for the concrete machine.
]) <thm-sim>

These equations are definitional. A sealed program is not an approximation of a backward function; it is a name for one, written in the source language.

_Proof sketch._ By induction on the derivation. Reads, borrows and assignments project and update the view, [End] is the substitution of @fig-model, a match on a constructor is ι-reduction, and an unfolding call is δβ followed by the induction hypothesis. For [Close], the equations hold by unfolding $"Run"$. The call clause yields these projections whether or not $dg(f)(overline(u), overline(w))$ reduces further, which is why discarding the partial run is harmless. [Seal] runs $t$, and the induction hypothesis on that run gives the normal form. Translation commutes with refinement because abstract values and loans are variables.

The hardest case ends a borrow $k$ whose loan is a hole inside sealed programs. The model substitutes $h_k := dg(w)$ into $"Run"(t)$; the machine substitutes $w$ into $t$ and runs it again. The two agree, $"Run"(t)[h_k := dg(w)] equiv "Run"(t[w slash "loan"_k])$, only because the hole is inert _during_ the run of $t$: [Seal] treats a loan whose borrow is outside the run like an abstract value. A run able to end $k$ would reach outside the sealed program, and $"Run"(t)$ would not be a function of $t$. ∎

== A call affects only what it is passed

#thm([Theorem], [frame], [
  Let Ω be well formed.
  + _Locality._ Suppose $Omega = Omega_1 union.plus Omega_2$, $t$'s free variables are bound in $Omega_1$, and every loan occurring in $Omega_1$ has its borrow in $Omega_1$. Then $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ iff $cfg(Omega_1, t) arrow.b.double cfg(Omega_1', v)$ with $Omega' = Omega_1' union.plus Omega_2 theta$. Here $theta$ fills the loans in $Omega_2$ of the borrows the run ended.
  + _Call effect._ A call runs as its body from its own frame alone, then substitutes each borrow argument's final content for its loan: the call clause of @fig-model.
  + _Call typing._ For $f : Pi(overline(x) : overline(A)). B$ called at Ω, once its arguments are evaluated, every `Id`-atom of $B$ observed at Ω equals the atom observed at the generic call, mapped through the context $"Ctx"$. $"Ctx"$ resolves _all_ owners of the arguments' loans around their final contents. So, if $"Ctx"$ is injective, $dg(B"@"Omega) = dg(B)(overline(u))$ by `propext`.
]) <thm-frame>

#thm([Lemma], [owners and injectivity], [
  $"Ctx"$ is jointly injective when it resolves every owner of every hole it carries, and in general only then.
]) <lem-inj>

#thm([Lemma], [backward functions are injective], [
  For every definable $f : Pi(overline(x) : overline(A)). \&T$ and all $overline(d)$, the backward map of $dg(f)(overline(d))$ is jointly injective.
]) <lem-backinj>

Part (3) is what [Call-type] relies on. It is why an induction hypothesis arrives wrapped in its caller's context, which in `AddMZero` is $((), S space square)$.

_Proof sketch._ (1) By induction on the run: with no globals and no closure capturing a borrow, a rule touches only places reachable from $t$. (2) is (1) for the callee's frame, which is loan-closed because arguments are loan-free. (3) Both observations run on private copies and, by (1), change nothing outside the arguments. With @lem-inj the two `Eq`-atoms are equivalent, and congruence does the rest. For @lem-inj, $"Ctx"$ composes constructors, backward functions at their hole (@lem-backinj, or the model's restriction), and components constant in the hole. Those keep joint injectivity only if the owner holding the hole is kept, hence owner sets (@sec-obs). With one owner of a two-argument returned borrow observed, [Call-type] proves `Id Nat (S Z) Z`. @lem-backinj is the fundamental lemma of the relation, by induction on typing. A returned borrow's hole sits under constructors or at an injective backward function, and no rule discards its final value ([Access] ends inner loans before overwriting or dropping). ∎

The hardest case is (2) when $f$ returns a borrow. As the frame pops, the parameter's borrow still holds the returned borrow's loan. [End] moves that content, loan included, into the caller's owner, which ends up holding $K["loan"_r]$, a value that depends on something the caller has not yet produced. In the model this is $beta_i (h_r) = K[h_r]$. Its injectivity ranges over every future of $r$, so it takes an induction over definitions (@lem-backinj) rather than an inspection of Ω.

== Borrows may end in any order

#thm([Theorem], [canonical observation], [
  Let Ω be well formed.
  + Ending two borrows in either order and re-normalising gives environments with the same resolution.
  + If a run of $t$ from Ω succeeds while ending some borrows earlier than the lazy strategy would, then the lazy run succeeds too, with the same borrow-free result and the same resolution.
  Hence the observation $⟦t⟧_Omega^W$ does not depend on when borrows end, and `Id` is well defined.
]) <thm-canon>

_Proof sketch._ (1) Up to re-normalisation, ending $ell$ is the substitution $h_ell := dg(v_ell)$, and two such substitutions commute by acyclicity. (2) Suppose the first run ends $ell$ at a point $A$, while the lazy run ends it later, at a demand, at a drop, or at the final resolution. After $A$ the first run cannot use $ell$, since it would read $bot$. Nor can it reach the positions of $ell$'s loan: any access to their container would make the lazy run end $ell$ there too. So every step of the first run is available to the lazy run, and both substitute the same content for $ell$'s loan. ∎

For (1), the hardest case is a hole inside a sealed program. Ending its borrow re-runs the sealed program, and the order of two such re-runs must not matter. It does not: a completed sealed run ends its own borrows before reading its result, so its normal form is a resolved value, and $"Run"$ is compositional (@thm-sim). Either order therefore computes $"Run"$ of the fully substituted program. Part (2) is the part the rest of the metatheory leans on: it absorbs the extra borrow endings of the symbolic machine in @thm-natural.

== Symbolic evaluation commutes with instantiation

A _refinement_ α of Ω substitutes constructor patterns or closed values for abstract values, closed definable functions for abstract functions, and values for holes in sealed programs. $Omega arrow.b$ is Ω with its sealed programs re-normalised, and $approx$ is equality up to renaming of loans.

#thm([Theorem], [naturality], [
  Let Ω be well formed, $cfg(Omega, t) arrow.b.double cfg(Omega', v)$ by the symbolic machine, and α a refinement of Ω.
  + _Operationally_, $((Omega' alpha) arrow.b, (v alpha) arrow.b)$ is, up to $approx$, the result of a run of $t alpha$ from $(Omega alpha) arrow.b$ that ends some borrows earlier than the lazy strategy. So the lazy run $cfg((Omega alpha) arrow.b, t alpha) arrow.b.double cfg(Omega'', v'')$ exists. It has the same resolution, and when $v$ is borrow-free it has the same result.
  + _Observationally_, for every footprint $W$, re-normalising the instantiated observation gives the observation of the instantiated term: $(⟦t⟧_Omega^W alpha) arrow.b = ⟦t alpha⟧_(Omega alpha)^W$.
]) <thm-natural>

#thm([Corollary], [adequacy], [
  If α is ground, the lazy run of $t alpha$ closes nothing off: it is a concrete run, it terminates, and it computes the instantiated symbolic observation. Every observation, and hence every `Id`, that the checker computes on abstract inputs is therefore the observation the program makes on every concrete input. The checker is sound in this sense, but it is not complete (see the remark below).
]) <cor-adequacy>

_Proof sketch._ Part (1) is by induction on the symbolic derivation. Every step except closing off commutes with α on the nose. α substitutes atoms, and [Match], the only rule that is not uniform in atoms, takes an arm only on a constructor, which α preserves. At a [Close] of a call $C$ with argument contents $overline(u)$, the refined run reaches $C$ with $overline(u) alpha$ and runs $f$'s body alone (@thm-frame). Re-normalising the sealed programs runs the same body on the same values. [Seal] unfolds the head call exactly once, and closes off inner calls exactly where the direct run does. By determinism, both stop at the same stuck match or complete with the same results. They can differ in one place only: where a returned borrow's loan lives. The concrete run puts it into the one owner the borrow actually points into. The symbolic hole sits in the fill of every borrow argument the borrow _might_ point into, and an [Access] to any of those places ends the borrow. So the symbolic run can end a returned borrow at an access that the concrete run performs without ending it. That is an extra [End] step, and nothing else changes. Part (2) follows from (1) and @thm-canon (2), since an observation resolves every borrow. ∎

The hardest case is again a returned borrow, and it has two sub-cases.

_No non-target owner accessed._ Suppose no possible owner other than the target was accessed before α. Then re-normalising reproduces the concrete state up to renaming. The concrete run pops $f$'s frame while its parameter's borrow holds the returned loan $"loan"_q$, so the target owner receives $K["loan"_q]$. On the symbolic side, re-normalising $seal("L; let r = C; *r := " "loan"_k "; " c_i)$ runs $C$, leaving $c_i$ holding $K["loan"_(q')]$. It then writes the inert $"loan"_k$ through $r$ and reads $c_i$, where [Access] ends the run's own $q'$. The result is $K["loan"_k]$, which matches $K["loan"_q]$ under $k <-> q$. This rests on loans being variables, on [Access] ending only the run's own loans, and on [Seal] not closing off its head call.

_A non-target owner accessed._ Suppose the symbolic run accessed a possible owner that α reveals is not the target. Then it has already ended the borrow, and only the resolutions of the two states agree.

*Remark (holes over-approximate the target of a returned borrow).* This example is machine-checked in the Lean development.

The setup:
- `Pick(n, x, y) := match n { Z => x | S _ => y }`;
- $Omega = {n |-> sigma, a |-> 1, b |-> 2, r |-> (), z |-> ()}$;
- `t = r := Pick(n, &a, &b); z := b`;
- $alpha = (sigma := sans("Z"))$.

The symbolic run:
- `Pick` is stuck on σ and is closed off.
- The hole of its returned borrow sits in the fills of both `a` and `b`, since either may be the target.
- Reading `b` therefore ends the returned borrow, and `r ↦ ⊥`.
- After refinement, the state is ${a |-> 1, b |-> 2, r |-> bot, z |-> 2}$.

The concrete run of $t alpha$:
- `Pick` returns a borrow of `a`, so `b` holds no loan and `r` stays live.
- The final state is ${a |-> "loan"_q, b |-> 2, r |-> "borrow"_q 1, z |-> 2}$.

No renaming of loans relates these two states, though they resolve to the same contents. That is why @thm-natural is stated up to resolution.

The cost is completeness, not soundness. The program `r := Pick(n, &a, &b); z := b; match n { Z => *r := 5 | S _ => () }` runs for every concrete `n`. But the checker rejects it: `r` is already $bot$ when the `Z` arm uses it. The error lands on that use. It goes away if the program uses `r` before reading `b`, or splits on `n` before the call. Recovering the program as written would need holes that record under which refinement they belong to which owner. Rust's borrow checker draws the same line: after `let r = if n == 0 { &mut a } else { &mut b }`, it treats `r` as borrowing from both `a` and `b` for as long as `r` is live, and rejects reading `b` in between. The checker is as conservative as Rust here, and the concrete machine is more permissive than both.

*Thunkability is naturality.* In Pédrot and Tabareau's forcing model of dependent call-by-push-value, a computation is a family over forcing conditions. It is _thunkable_ (it behaves like a value) exactly when it is _natural_: running then restricting equals restricting then running @fire-triangle[Prop. 18]. Ochr's type-level evaluation has this shape. The normaliser runs at a condition Ω, which records which abstract values exist and what is known of them, and refinements are the restriction maps. [Split] refines stored types in lockstep with the term, and so plays the role of their dependent `let`.

A type contains only observations, and observations are resolved. So part (2) of @thm-natural, the naturality square for everything a type can see, commutes on the nose. That is the precise sense in which types are free of effects although they run effectful programs. Operational states commute only up to extra borrow endings, by part (1). The difference is invisible to types and costs only the completeness just described.

This is a correspondence of invariants, not an embedding into their calculus, but it is a usable design test: a rule may act in type-level evaluation only if it is natural on observations. Three candidate rules failed it:
- joining a stuck match's results into fresh abstract values forgets what refinement would recover;
- skipping proposition-valued _calls_, but not the same code outside a call, made a block observe differently sealed and unsealed;
- non-structural recursion closes off on abstract arguments but diverges once they are instantiated.

== Typing and conversion are preserved

#thm([Theorem], [preservation], [
  For a program accepted by [Def] and [Rec]:
  + a type $A$ of sort $s$ at Ω translates to $Gamma_Omega tack.r dg(A) : dg(s)$;
  + if $Omega tack.r A equiv B$, then $dg(A) = dg(B)$ is provable in $"CIC"_L$ (definitionally in $"ECIC"_L$);
  + if $Omega tack.r t arrow.b.double v : A tack.l Omega'$, then $dg(t)$ maps views of Ω's shape to $dg(A)$ and views of $Omega'$'s shape;
  + a definition $f : Pi(overline(x) : overline(A)). B$ translates to an inhabitant of $dg((Pi(overline(x) : overline(A)). B))$, in the injective part when $B$ is a borrow type.
]) <thm-sound>

_Proof sketch._ By induction on derivations. [Def]'s goal is the [Call-type] of the generic call, which is $dg(B)(overline(d))$ by definition. [Split] on an abstract value is dependent elimination on a CIC variable, and applying the refinement to the environment, the goal and every stored type _is_ its motive; generalising a sealed program first is CIC's generalisation. After a non-tail split, the checked arms define the closed-off block's function, and the continuation starts from its application (@thm-sim), so nothing is lost. [Rec] makes the translation a strong recursion, and erased terms leave the view unchanged. For conversion, equal normal forms translate equally (@thm-sim), and the `Eq` rules are `propext` instances: $((a, b) = (a', b')) = (a = a' and b = b')$, $(a = a) = top$, $(top and P) = P$. `J` becomes Lean's eliminator, which needs the endpoints `J` carries. Proof irrelevance is sound because Ochr propositions translate to CIC propositions. ∎

The hardest case is [Call-type]. It uses @thm-frame, and @lem-inj and @lem-backinj, and so owner sets and the injective restriction. It also needs `propext`, [Rec] for the induction hypotheses, and the capture of a Π-type's free variables at formation, without which a call site's type is no instance of the type proved.

== Consistency

#thm([Corollary], [consistency], [
  No closed term has type `Eq Nat Z (S Z)` or `Π(P : Prop). P`. More generally, if $tack.r t : P$ for a closed proposition $P$, then $dg(P)$ holds in the set model.
]) <cor-consistent>

_Proof._ A closed term has an empty view, so by @thm-sound it translates to an inhabitant of $dg(P)$ in $"ECIC"_L$. Carneiro's model interprets $"ECIC"_L$ in ZFC with one inaccessible cardinal per universe level used, and in that model $dg((sans("Eq Nat") space sans("Z") space (sans("S") space sans("Z")))) = emptyset$. ∎

The strong form matters: proofs are never run, so consistency cannot lean on the checker diverging.

== What is mechanised

Mechanised in the accompanying Lean development: _[to be filled in: the theorems proved in `ochr/core/meta-lean/`, e.g. @thm-frame (1)–(2), the equations of @thm-sim, @cor-adequacy, @thm-canon, @lem-backinj, for the first-order fragment]_. The fragment has natural numbers, unit, pairs, places, borrows, matching, recursive definitions (including ones returning borrows), opaque definitions for abstract functions, and erased proofs. A computation means its concrete run on Lean data, so the target is Lean itself, and `Id` is Lean's equality on observation tuples. On paper only: the dependent layer (parts (1), (2) and (4) of @thm-sound for Π-types over `Id`, universes and [Split]'s motive), @cor-consistent, termination of higher-order programs, @thm-natural for non-ground refinements, and the forcing-model correspondence. The dependent layer is standard given Carneiro's model. The new part is the effectful layer, and that is where the mechanisation goes.
