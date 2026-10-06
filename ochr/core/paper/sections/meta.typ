#import "../style.typ": *

// Numbered statements (definitions, conjectures) sharing one counter, referable by label.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let dg(x) = $#x^dagger$

This section states the properties Ochr is designed to have and the evidence for each (@fig-claims). Few of them are proved, and those only for a first-order fragment of an earlier version of the rules (@sec-meta-mech). Consistency, the agreement of the checker's two evaluation paths, and adequacy are conjectures; for them we sketch the model and the argument we expect. The rest of the evidence is the checker's regression suite and ledger (@sec-impl).

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(columns: (46%, 16%, 38%), stroke: none, inset: (x: 4pt, y: 3pt), align: (left, left, left),
    table.hline(stroke: 0.5pt),
    [*Property*], [*Status*], [*Evidence*],
    table.hline(stroke: 0.4pt),
    table.cell(colspan: 3, emph[Mechanised: substantive]),
    [1. Machine steps preserve well-formedness (@app-wf).], [mechanised], [`exec_wf`, for source terms that do not name the machine's argument temporaries],
    [2. Frame: a call affects only what it is passed, and its effect is its isolated run, plugged back into the caller.], [mechanised], [`frame_local`, `call_effect`],
    [3. The sealed programs of [Close] compute the call's result, the final contents of its borrowed places and its backward function.], [mechanised, with hypotheses], [`close_res`, `close_fin`, `close_cur`, `close_back`; the hypotheses follow from 1, not yet in Lean],
    [4. The order in which borrows end does not change the resolved state.], [mechanised], [`end_order_indep`, `endAll_endSeq`, from two endings commuting (`end_comm`)],
    table.cell(colspan: 3, emph[Mechanised: routine]),
    [5. The machine is deterministic, monotone in fuel, and invariant under renaming of loans.], [mechanised], [`eval_det` (the interpreter is a function), `exec_mono`, `exec_rename`],
    [6. Substituting a value for a returned borrow's hole is injective, and so is the caller's context around it when every owner of the hole is observed; with fewer owners it can be constant.], [mechanised (syntactic)], [`back_inj`, `ctx_inj` (substituting for a loan that occurs is injective), `ctx_needs_all_owners`; injectivity of the backward function after [Seal] re-normalises is not proved],
    table.cell(colspan: 3, emph[Partly mechanised, and conjectured]),
    [7. Concrete runs of programs accepted by [Rec] terminate.], [partly mechanised], [for borrow-free and for non-recursive programs; in general `sorry`],
    [8. Stability: the two evaluation paths take the same decisions (@lem-stable), a substitution lemma for typing decisions.], [conjecture], [the counterexamples of @fig-why, the ledger (@sec-impl) and the differential fuzzer; a probe corrected item (6), footprints (`FootprintProbe`)],
    [9. Naturality and adequacy (@conj-nat): refining and running commute once every borrow is ended, so an `Id` computed on abstract inputs holds on every concrete input.], [conjecture], [the fuzzer; the form without resolution is false (mechanised counterexample)],
    [10. Consistency: no closed term has type `False` (@cor-consistent).], [conjecture], [proved for a fragment, conditional on naturality and transfer (@sec-tf); the model sketch below; the regression suite],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [What Ochr is meant to satisfy, and the evidence. "Mechanised" means proved in Lean without `sorry`, for the fragment of @sec-meta-mech.],
) <fig-claims>

== The model, as a sketch <sec-meta-model>

Following Aeneas @aeneas, a computation is read as a pure function from the current contents of its borrows to its result and their final contents; types get a set-theoretic interpretation after Carneiro @theory-of-lean.

*What consistency would be relative to.* Computations translate into $"CIC"_L$, the intensional type theory of Lean 4 @lean4, with an impredicative, definitionally proof-irrelevant `Prop` and `propext`. Types need more: Ochr's conversion identifies propositions that CIC only proves equivalent, through the `Eq` rules (@sec-obs) and through [Call-type], so no translation into intensional CIC preserves conversion. We therefore interpret types directly in sets, following Carneiro's construction, which extends Werner's set model of the calculus of inductive constructions @werner-sets, with one inaccessible cardinal per universe level. Carneiro needs unique typing to decide whether a `λ` or `Π` denotes a proof or a set-theoretic function; in Ochr that decision is syntactic (@sec-typing), so the interpretation can be defined by recursion on derivations. Borrows are only of `Type₀` (@sec-calculus): borrowing a universe would let `Π(x : &Type₀)(a : *x). *x` live in `Type₀`, which would be impredicative, with no set model.

*The interpretation* (@app-model). An inductive type in `Type₀` denotes its least set, one in `Prop` a subsingleton, and `Eq` a truth value. A function type with borrow parameters denotes functions that return, besides their result, the final contents of the borrowed places, and, for a returned borrow, a backward function from its final value to those contents, which must be injective: [Call-type] forces this, and it is false of a Rust function that returns a leaked `'static` borrow (@sec-discussion). Terms translate to state-passing functions on _views_, in which a loan is a _hole_ for its borrow's final content, and a symbolic and a concrete run are related through their _resolutions_, which end every borrow. Four invariants of the machine make this well defined (@app-wf), and that machine steps preserve them is property 1.

*Soundness, as a conjecture.* For a program accepted by [Def] and [Rec] and every valuation of its abstract values, we conjecture that types of sort $s$ denote elements of $s$'s universe, that convertible types denote the same set, that every term denotes a function from views before its run to its type's denotation and views after it, and that every definition lies in $R$. The proof we expect is by induction on derivations, with most cases reading the translation backwards. The `Eq` rules hold because propositions with the same truth value are equal; injectivity and disjointness are instances, since constructors are injective and have disjoint images (in $"CIC"_L$, `propext` applied to the no-confusion property of constructors). A match on a proof is interpreted through the proof's type, which subsingleton elimination makes well defined. The hardest case is [Call-type], which needs the frame property (property 2) extended to types, the injectivity of contexts (property 6) and naturality (property 9).

#thm([Conjecture], [consistency], [
  Relative to ZFC with one inaccessible per universe level, no closed term has type `False` (nor, therefore, `Eq(Nat, Z, S(Z))`, which computes to it).
]) <cor-consistent>

Since `J` computes only on convertible endpoints, conversion has no equality reflection. Whether normalisation, and so type checking, terminates is open: types may combine large elimination, `J` with type-valued motives and an impredicative, proof-irrelevant `Prop`, which Abel and Coquand show can defeat normalisation @abel-coquand. Lean is in the same position, since Abel and Coquand's counterexample applies to it too. The model interprets derivations, so consistency does not depend on termination.

== The two paths agree <sec-meta-nat>

A statement is evaluated along two paths, at a definition's generic call and directly at each instance, and [Call-type] and [Split] identify the results (@sec-typing-two). A _refinement_ α substitutes values for abstract values, definable closures for abstract functions, and values for holes, each of a type convertible with the one it replaces; it covers case splits and call-site instantiation, where an argument's type need only convert to the parameter's.

#thm([Conjecture], [stability], [
  Let $t$ be checked at Ω and let α be a refinement. Compare the run of $t$ at Ω, with α applied afterwards, with the run of $t alpha$ at $Omega alpha$. At every subterm both runs reach: (1) the same subterms are erased, and the same matches are decided by the type of a proof; (2) each closed-off stuck block captures the same places, in the same modes; (3) each match's arms are well typed on both runs or on neither; (4) each call has the same class and [Close] row; (5) each observed place is compared at the same type; (6) the footprint of each observation made at Ω contains the one made at $Omega alpha$, and α turns the equation for each extra place into ⊤, so the two `Id` types are convertible by `And`'s unit laws.
]) <lem-stable>

The stability conjecture is a substitution lemma: typing decisions commute with instantiation, for a type theory whose conversion is an evaluator. We expect a proof by induction on the machine's rules, in which the decisions are the rules' side conditions that read something other than a normal form: a declared type, the syntax of a term, or a place. Item (6) is containment, not equality. A returned borrow's hole sits in the fill of every place it may point into, so at an abstract `n` the owners of `Pick(n, &a, &b)` are `a` and `b`, and an `Id` about writes through it has an equation for each. At `n = 0` the only owner is `a`. Refining `n := 0` after the type is formed leaves `b`'s fill without the hole, so both sides leave `b` with the same value and its equation computes to ⊤; the checker then shows the refined type as `False ∧ ⊤` where the direct path gives `False`. The type formed before the refinement is the stronger one, so the difference costs nothing.

Each decision is a function of syntax and declared types (@sec-typing-two), a refinement changes only normal forms, and conversion preserves declared types (@sec-typing-types). Earlier statements took refinement to substitute values of the same type, not a convertible one, and the reviews' closed proofs of `False` lay in that gap; each earlier list of decisions also missed one, most recently item (5).

*Testing it.* A differential fuzzer generates random typed programs and statements, with borrows, returned borrows, stuck matches, closures, `Id`, proofs, and the shapes of both reviews' attacks. It checks each statement at its generic call and compares every refinement with a direct run of the refined instance, with oracles for value agreement, truth at ground instances, proof irrelevance, the frame property and adequacy, and it runs each accepted data function at ground inputs and compares the result with the function's erased run. In 10⁶ generated cases (1,165 s on 12 cores) no refinement disagrees with the direct path on a value, no execution of a generated program disagrees, and the checker rejects no true statement the fuzzer poses; 65 findings of one class, values local to one match arm that appear in a stuck block's inferred type, were re-triaged with a targeted generator against the closed proof of @sec-typing-types, and are fail-safe in the shapes it generates (5,000 cases, no false acceptance). With each ledger rule switched off in turn, it finds that rule's failure for 17 of the then 20 soundness rows, both reviews' attacks among them; the misses are three rules about declarations, which it does not generate and the ledger's witnesses cover. It has also found a closed proof of `False` in the checker's implementation and a misclassified ledger row, and it decided when the move semantics could be turned on: accepted generated programs that failed at runtime, where stuck blocks hid moves, went from 15,567 in 10⁶ to 950, 10 and 0 as the gaps it exposed were closed. Its record is not clean either. A refinement that leaks from one match arm into another gave a closed proof of `False` twice, first through a closure's capture, found while building the array library, and then through generalisation records reused across arms, found by a reviewer (@sec-typing-types); both times the fuzzer's own analysis had called the family fail-safe. An argument about a class of findings is not a proof. Two later findings are fixed: an accepted function could fail when a borrowed local was dropped (now the [Drop] rule), and a match on a value of stuck type took its constructors from its patterns.

Naturality holds only up to resolution, which costs completeness. With `Pick(n, x, y) := match n { Z => x, S _ => y }` and `n` abstract,
```
let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
```
runs for every concrete `n` but is rejected: `Pick`'s hole sits in the fills of both `a` and `b`, so reading `b` ends `r` symbolically, and `r` is dead in the `Z` arm. The refined symbolic state and the concrete one agree only after every borrow is ended (a mechanised counterexample to the stronger form), which is why naturality is stated up to resolution; Rust likewise treats `r` as borrowing both places while it is live.

#thm([Conjecture], [naturality], [
  Let every definition of the program be accepted, let $Omega tack.r t arrow.b.double chevron.l Omega', v chevron.r$ on the symbolic path, and let α be a refinement. If the run of $t alpha$ at $Omega alpha$ ends, it ends without error, as $chevron.l Omega'', v'' chevron.r$, and after every borrow is ended in both, the final states and results are equal up to a renaming of loans: $rho(Omega' alpha) = rho(Omega'')$ and $rho(v alpha) = rho(v'')$, where α re-normalises sealed programs and ρ ends every borrow. In particular (adequacy), an `Id` that computes to ⊤ at Ω computes to ⊤ at $Omega alpha$.
]) <conj-nat>

Whether the run of $t alpha$ ends is property 7; the requirement that every definition be accepted is needed because a call closed off at Ω runs at $Omega alpha$, and only its own [Def] check says it runs without error there.

*A theorem for a fragment.* For a first-order fragment F (natural numbers, `Unit`, `True`, `False`, `And`, `Eq`, `Id`, top-level functions with borrow parameters and returned borrows, [Close] and [Split], but no closures, stuck blocks, user inductives or type families), @sec-tf proves on paper:

#thm([Theorem], [soundness of F, conditional on naturality and transfer], [
  If naturality holds step by step (@tf-ass-n) and the mechanised lemmas transfer to the current rules (@tf-ass-t), then for every accepted program of F and every concrete input, each data function runs without error and a borrow it returns is live, and each lemma whose hypotheses hold has a true conclusion. Consistency of F and adequacy of `Id` follow.
]) <thm-f>

== What is mechanised <sec-meta-mech>

The directory `ochr/core/meta-lean` of the artifact (about 11,600 lines of Lean 4, no Mathlib, only Lean's standard axioms) mechanises the effectful layer of an earlier rule set, which predates the erasure and inductive-proposition rules of @sec-typing, for a first-order fragment: natural numbers, unit, pairs, places, borrows, matching, recursive and opaque definitions (including borrow-returning ones) and erased proofs, with no closures, types, inductive propositions or stuck blocks. The machine is a clocked big-step interpreter. The side condition of `exec_wf`, that the term does not name the machine's argument temporaries, holds of every surface program. Only general termination is `sorry`. Nothing about types, conversion, stability or the model is mechanised.
