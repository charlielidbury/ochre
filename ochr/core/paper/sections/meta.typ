#import "../style.typ": *

// Numbered statements (definitions, conjectures) sharing one counter, referable by label.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let dg(x) = $#x^dagger$

This section states the properties Ochr is designed to have and the evidence for each (@fig-claims). Few of them are proved, and those only for a first-order fragment of an earlier version of the rules (@sec-meta-mech). Consistency, the agreement of the checker's two evaluation paths, and adequacy are conjectures; for them we sketch the model in which we expect to prove them, and the argument we expect. The rest of the evidence is the checker's regression suite and ledger (@sec-impl).

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(columns: (46%, 16%, 38%), stroke: none, inset: (x: 4pt, y: 3pt), align: (left, left, left),
    table.hline(stroke: 0.5pt),
    [*Property*], [*Status*], [*Evidence*],
    table.hline(stroke: 0.4pt),
    [1. The machine is deterministic, monotone in fuel, and invariant under renaming of loans.], [mechanised], [`eval_det`, `exec_mono`, `exec_rename`],
    [2. Machine steps preserve well-formedness (@app-wf).], [mechanised], [`exec_wf`, for source terms that do not name the machine's argument temporaries],
    [3. Concrete runs of programs accepted by [Rec] terminate.], [partly mechanised], [for borrow-free and for non-recursive programs; in general `sorry`],
    [4. Frame: a call affects only what it is passed, and its effect is its isolated run, plugged back into the caller.], [mechanised], [`frame_local`, `call_effect`],
    [5. The sealed programs of [Close] compute the call's result, the final contents of its borrowed places and its backward function.], [mechanised, with hypotheses], [`close_res`, `close_fin`, `close_cur`, `close_back`; the hypotheses follow from 2, not yet in Lean],
    [6. Substituting a value for a returned borrow's hole is injective, and so is the caller's context around it when every owner of the hole is observed; with fewer owners it can be constant.], [mechanised (syntactic)], [`back_inj`, `ctx_inj`, `ctx_needs_all_owners`; injectivity of the backward function after [Seal] re-normalises is not proved],
    [7. The order in which borrows end does not change the resolved state.], [mechanised], [`end_order_indep`, `endAll_endSeq`, from two endings commuting (`end_comm`)],
    [8. Stability: the two evaluation paths take the same decisions (@lem-stable).], [conjecture], [the counterexamples of @fig-why and the ledger (@sec-impl)],
    [9. Naturality and adequacy: refining and running commute up to resolution, so an `Id` computed on abstract inputs holds on every concrete input.], [conjecture], [tests; the form without resolution is false (mechanised counterexample)],
    [10. Consistency: no closed term has type `False` (@cor-consistent).], [conjecture], [the model sketch below; the regression suite],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [What Ochr is meant to satisfy, and the evidence. "Mechanised" means proved in Lean without `sorry`, for the fragment of @sec-meta-mech.],
) <fig-claims>

== The model, as a sketch <sec-meta-model>

Following Aeneas @aeneas, a computation is read as a pure function from the current contents of its borrows to its result and their final contents; types get a set-theoretic interpretation after Carneiro @theory-of-lean.

*What consistency would be relative to.* Computations translate into $"CIC"_L$, the intensional type theory of Lean 4 @lean4, with an impredicative, definitionally proof-irrelevant `Prop` and `propext`. Types need more: Ochr's conversion identifies propositions that CIC only proves equivalent, through the `Eq` rules (@sec-obs) and through [Call-type], so no translation into intensional CIC preserves conversion. We therefore interpret types directly in sets, following Carneiro's construction, which extends Werner's set model of the calculus of inductive constructions @werner-sets, with one inaccessible cardinal per universe level. Carneiro needs unique typing to decide whether a `λ` or `Π` denotes a proof or a set-theoretic function; in Ochr that decision is syntactic (@sec-typing), so the interpretation can be defined by recursion on derivations. Borrows are only of data (@sec-calculus): a borrow of a type would let `Π(x : &Type₀)(a : *x). *x` live in `Type₀`, which is then impredicative and has no set model.

*Types.* An inductive declaration in `Type₀` denotes the least set closed under its constructors, at each value of its parameters, so `Nat` denotes $NN$; constructors are injective and have disjoint images. One in `Prop` denotes a subsingleton, ${•}$ if that least set is inhabited and $emptyset$ otherwise: `False` denotes $emptyset$, `True` denotes ${•}$, and `And(P, Q)` denotes $dg(P) inter dg(Q)$. `Eq A a b` denotes $[dg(a) = dg(b)] subset.eq {•}$. For a function type with borrow parameters `xᵢ : &Tᵢ` at positions $i in I$, let $D_i = dg(T_i)$ for $i in I$, $D_j = dg(A_j)$ otherwise, and $"Fin" = product_(i in I) dg(T_i)$, the final contents of the borrowed places:

$ dg((Pi(overline(x) : overline(A)). B)) = R_(Pi(overline(x) : overline(A)). B) subset.eq Pi(overline(d) : overline(D)). "Out"_B (overline(d)), quad
  "Out"_B (overline(d)) = cases(
    dg(B)(overline(d)) & "if" B "is a proposition,",
    dg(B)(overline(d)) times "Fin" & "if" B "is borrow-free data,",
    dg(T) times (dg(T) -> "Fin") quad & "if" B = \&T.
  ) $

Here $dg(B)(overline(d))$ is $B$ at the generic call of [Def]. We write $"fwd"_F$ and $"back"_F$ for the two components of $F(overline(d))$. For a returned borrow, $"back"_F (overline(d))$ is Aeneas's backward function: it maps the value the caller eventually leaves in the borrow to the final contents. A proposition has no $"Fin"$ component, because proofs run on a private copy (@sec-typing).

#thm([Definition], [injectivity relation], [
  $R_A subset.eq dg(A)$ is defined by induction on $A$. For base types, propositions and universes $R_A = dg(A)$; $R$ is componentwise on pairs, and $R_(\&T) = R_T$. For a function type, $F in R_(Pi(overline(x) : overline(A)). B)$ iff, for all $overline(d)$ with $d_i in R_(T_i)$ for $i in I$ and $d_j in R_(A_j)$ otherwise, $"fwd"_F (overline(d)) in R_B$, and, if $B = \&T$, $"back"_F (overline(d))$ is injective: equal tuples of final contents come only from equal final values of the returned borrow.
]) <def-inj>

$R$ is forced: by [Call-type], Ochr proves of every abstract `g : Π(x : &Nat). &Nat` that writing `0` or `1` through `g(x)` leaves different states, which is false of a Rust function that returns a leaked `'static` borrow (@sec-discussion).

*Terms.* Abstract values become variables, and a loan $ell$ becomes a variable $h_ell$, a _hole_ for the final content of its borrow. The _view_ $dg(Omega)$ reads a borrow as its current content and a loan as its hole; the _resolution_ $rho_Omega$ substitutes each hole by its borrow's content, that is, it ends every borrow. A term translates to a state-passing function on views (@fig-model in @app-model); a sealed program denotes the result of running it from the empty view; a definition is a well-founded recursion on the entry value of its decreasing parameter; and `Id` is the equation between the tuples of result and resolved footprint. A symbolic and a concrete run of one term can place their borrows differently (@sec-meta-nat), so runs are related through their resolutions.

Four invariants of the machine make this well defined (@app-wf): each borrow is held once, every loan is bound by a held borrow or lies inside a sealed program (the only place a loan may occur twice), loans nest in borrows acyclically, and every value read, moved or passed is loan-free. That machine steps preserve them is property 2 of @fig-claims, which is mechanised.

*Soundness, as a conjecture.* For a program accepted by [Def] and [Rec] and every valuation of its abstract values, we conjecture that types of sort $s$ denote elements of $s$'s universe, that convertible types denote the same set, that every term denotes a function from views before its run to its type's denotation and views after it, and that every definition lies in $R$. The proof we expect is by induction on derivations, with most cases reading the translation backwards. The `Eq` rules hold because propositions with the same truth value are equal; injectivity and disjointness are instances, since constructors are injective and have disjoint images (in $"CIC"_L$, `propext` applied to the no-confusion property of constructors). A match on a proof is interpreted through the proof's type, which subsingleton elimination makes well defined. The hardest case is [Call-type], which needs the frame property (property 4) extended to types, the injectivity of contexts (property 6) and naturality (property 9).

#thm([Conjecture], [consistency], [
  Relative to ZFC with one inaccessible per universe level, no closed term has type `False` (nor, therefore, `Eq Nat Z (S Z)`, which computes to it).
]) <cor-consistent>

Since `J` computes only on convertible endpoints, conversion has no equality reflection. Whether normalisation, and so type checking, terminates is open: types may combine large elimination, `J` with type-valued motives and an impredicative, proof-irrelevant `Prop`, which Abel and Coquand show can defeat normalisation @abel-coquand. The model interprets derivations, so consistency does not depend on it.

== The two paths agree <sec-meta-nat>

A statement is evaluated along two paths, at a definition's generic call and directly at each instance, and [Call-type] and [Split] identify the results (@sec-typing-two). A _refinement_ α substitutes values for abstract values, definable closures for abstract functions, and values for holes, each of a type convertible with the one it replaces; it covers both case splits and instantiation at a call site, where an argument's type need only be convertible with the parameter's.

#thm([Conjecture], [stability], [
  For $t$ at Ω and a refinement α, the following are the same for $t$ at Ω and $t alpha$ at $Omega alpha$: (1) which subterms are erased, and which matches are decided by the type of a proof; (2) which places each closed-off stuck block captures, in which modes, and the places of each footprint; (3) whether each match's arms are well typed; (4) each call's class and [Close] row.
]) <lem-stable>

The argument we expect is that each decision is a function of syntax and declared types (@sec-typing-two), that a refinement changes only normal forms, and that conversion preserves declared types, since Π-types of different class or borrow flag are not convertible and a type's declared sort is its computed sort (@sec-typing-types). Earlier statements of this conjecture took refinement to substitute values of the same type, not a convertible one, and the reviews' closed proofs of `False` lay exactly in that gap. The argument is still an enumeration of the decisions we know of, and each earlier version of it missed one.

*Testing it.* A differential fuzzer generates random typed programs and statements, with borrows, returned borrows, stuck matches, closures, `Id`, proofs, and the shapes of both reviews' attacks. It checks each statement at its generic call and compares every refinement with a direct run of the refined instance, with oracles for value agreement, truth at ground instances, proof irrelevance, the frame property and adequacy, and it runs each accepted data function at ground inputs and compares the result with the function's erased run. In 10⁶ cases (1,165 s on 12 cores) no refinement disagrees with the direct path on a value, no execution disagrees, and the checker rejects no true statement the fuzzer poses; 65 findings are harmless imprecisions of scope. With each ledger rule switched off in turn, it finds that rule's failure for 17 of the 20 soundness rows, both reviews' attacks among them; the misses are three rules about declarations, which it does not generate and the ledger's witnesses cover. It has also found a closed proof of `False` in the checker's implementation, a ledger row classed as completeness whose rule soundness needs, a new witness for a row that another change had left without one, and it decided when the move semantics could be turned on: accepted programs that failed at runtime, where stuck blocks hid moves, went from 15,567 in 10⁶ to 950, 10 and 0 as the gaps it exposed were closed. Its record is not clean either: a reviewer found a closed proof of `False` through a refinement that leaked from one match arm into another, a class of findings the fuzzer's own analysis had dismissed as fail-safe. The absence of disagreements holds only within what the generator produces.

Naturality holds only up to resolution, which costs completeness. With `Pick(n, x, y) := match n { Z => x, S _ => y }` and `n` abstract,
```
let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
```
runs for every concrete `n` but is rejected: `Pick`'s hole sits in the fills of both `a` and `b`, so reading `b` ends `r` symbolically, and `r` is dead in the `Z` arm. The refined symbolic state and the concrete one agree only after every borrow is ended (a mechanised counterexample to the stronger form), which is why property 9 is stated up to resolution; Rust likewise treats `r` as borrowing both places while it is live.

== What is mechanised <sec-meta-mech>

The directory `ochr/core/meta-lean` of the artifact (about 11,600 lines of Lean 4, no Mathlib, only Lean's standard axioms) mechanises the effectful layer of version 1.3 of the rules, which predates the erasure and inductive-proposition rules of @sec-typing, for a first-order fragment: natural numbers, unit, pairs, places, borrows, matching, recursive and opaque definitions (including borrow-returning ones) and erased proofs, with no closures, types, inductive propositions or stuck blocks. The machine is a clocked big-step interpreter. The side condition of `exec_wf`, that the term does not name the machine's argument temporaries, holds of every surface program. One statement remains `sorry`: termination in general. Nothing about types, conversion, stability or the model is mechanised.
