#import "../style.typ": *

We implemented the calculus as an executable reference checker in Lean 4, about 4,000 lines with no dependencies, plus about 1,800 lines of examples and tests. Its purpose is not performance but fidelity: a hand derivation can be charitable where the rules are silent, and a program cannot. Every example in this paper is checked by it, written in a concrete syntax close to the one used here:

```lean
ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl | S p => AddMZero(&p) }

  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}
```

A `def` is expected to be accepted and a `reject def` to be rejected, and each verdict is an assertion checked during the build, so a build succeeds only if every verdict is as expected. Each test file also asserts how many verdicts it contains, which guards against a test file that silently checks nothing.

*Structure.* The machine, closing off, sealed-program normalisation, splitting, closing off stuck blocks, observation, `Id`, [Call-type], [Def] and [Rec] form one mutually recursive block of about two thousand lines. Terms use de Bruijn indices, and the variables introduced by [Close] have fixed names, so "same normal form" is structural equality, except that function values and Π-types are compared at their generic arguments and the unit laws of `And` are applied. The implementation follows the rules closely enough that its trace of `AddMZero` reproduces the derivation of @sec-overview symbol for symbol, including the successor that the environment supplies to the induction hypothesis.

*Test suite.* The suite contains every program this paper prints, each mapped to its test in the artifact's notes: `AddM`, `AddMZero`, `Add` and `AddZero`; the returned-borrow examples `TailM`, `AddM'` and `AddMEq`; branching with borrows whose origin depends on the branch; opaque function arguments; the programs of @sec-overview that pass a proof about the current, mutated state; user-declared inductive types, among them in-place append on a polymorphic `List(A)` and the binary-search-tree insertion of @sec-overview with its size theorem; and the logic of @sec-calculus: ex falso, disjointness, matches on proofs, and the `Or` attack of @sec-typing-prop. It also contains every program that must be rejected, in particular every closed false proof, and every accepted program that went wrong, found while designing the calculus. All 459 verdicts are as expected. The compiled checker decides all of them in about 19 ms; a clean build takes about 40 s, most of it re-running the suite for each row of the counterfactual ledger.

*The counterfactual ledger.* Each rule that is not the evident typing of a form has a switch that turns it off. For each of the 46 switches, the build asserts exactly which verdicts flip when it is off, and the class of the row, which follows from what flips:
- _Soundness_, 23 rows: with the rule off, the checker accepts a closed proof of `False` (17 rows) or an open program that goes wrong when run (6 rows), and the row names these witnesses. Without entry-value recursion, the non-terminating "proofs" of @sec-typing are accepted; without exclusive access, an accepted program writes through an ended borrow; without the rule that a recursive function occurs only as the head of a call, a function that passes itself to a helper proves `False`; and without owner sets (@sec-obs), a function that returns a borrow into one of two arguments yields a closed proof of `False`.
- _False lemma_, 1 row: without reading erasure from declarations, the checker accepts a false statement, whose closed instance confinement now rejects.
- _Model_, 3 rows: with the rule off, the checker accepts definitions that have no set-theoretic meaning, though the suite contains no closed proof of `False` from them. These are the borrow parameter of a borrow-returning function type, subsingleton elimination (@sec-typing-prop), and borrows only of data.
- _Policy_, 3 rows: with the rule off, the checker accepts only programs that are true under the other rules. These are reading [Close]'s row from the declared codomain, which stability needs; confinement; and classifying a variable as a proof by its declaration when confinement is also off.
- _Completeness_, 16 rows: with the rule off, the checker only rejects good programs. Among them are the private copy for erased terms, generalising a sealed program before splitting on it, binding proof parameters to `⋆`, [Seal]'s head guard, matching on a proof by its type, and the unit laws as conversion. One of them switches _on_ an extension, confining the bodies of functions that return proofs or types, to record what it would cost.

No row flips nothing. Confinement backs up two other rules: the soundness witnesses of the private copy and of reading proofs by their declaration appear only when confinement is off too. The ledger shows that each rule is needed for some verdict, not that the rules suffice, and one side condition has no switch: non-cumulative universes.

*What running the rules found.* Writing the checker exposed gaps in earlier versions of the rules, each now fixed: the recursive-function-as-a-value loophole above; an argument evaluated earlier in the same call being invalidated by a later one (`f(&x, x)` ends the first borrow while reading the second argument); recursive calls inside nested closures, which must be checked against the entry values of the enclosing function; with trees, the need to apply a split on a sealed program to re-derivations of it as well; and, with the connectives as declarations, that the unit laws must be conversion rather than a rewriting of stored types, or a proof of `⊤ ∧ P` could not be matched. It also found a bug in an earlier version of the checker itself: a match's scrutinee was typed from its arms, so a match on a number could run a list's arms. The counterexamples summarised in @fig-why, including several that an earlier version of the checker accepted, are regression tests, and each soundness row of the ledger flips at least one of them.
