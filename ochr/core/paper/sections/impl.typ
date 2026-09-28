#import "../style.typ": *

We implemented the calculus as an executable reference checker in Lean 4, about 3,000 lines with no dependencies, plus about 900 lines of examples and tests. Its purpose is not performance but fidelity: a hand derivation can be charitable where the rules are silent, and a program cannot. Every example in this paper is checked by it, written in a concrete syntax close to the one used here:

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

*Structure.* The machine, closing off, sealed-program normalisation, splitting, closing off stuck blocks, observation, `Id`, [Call-type], [Def] and [Rec] form one mutually recursive block of about a thousand lines. Terms use de Bruijn indices, and the variables introduced by [Close] have fixed names, so "same normal form" is structural equality. The implementation follows the rules closely enough that its trace of `AddMZero` reproduces the derivation of @sec-overview symbol for symbol, including the successor that the environment supplies to the induction hypothesis.

*Test suite.* The suite contains every example of this paper: `AddM`, `AddMZero`, `Add` and `AddZero`; the returned-borrow examples `TailM`, `AddM'` and `AddMEq`; branching with borrows whose origin depends on the branch; opaque function arguments; and the programs of @sec-overview that pass a proof about the current, mutated state. It also contains every program that must be rejected, and in particular every false proof found while designing the calculus, each of which is a regression test. The suite also contains user-declared inductive types: in-place list append and its returned-borrow variant, and the binary-search-tree insertion of @sec-overview with its size theorem. All 185 verdicts are as expected. The compiled checker decides the whole suite in about 9 ms, the heaviest declaration (the size theorem) in under a millisecond, and a clean build of the checker and the suite takes about ten seconds.

*Every side condition is load-bearing.* Each non-standard rule has a switch that turns it off, and the build also asserts a _counterfactual ledger_: with one rule switched off, exactly the tests that rule is responsible for change their verdict, and no others. Without entry-value recursion (@sec-typing), the non-terminating "proofs" of @sec-typing are accepted. Without exclusive access, a well-typed program writes through an ended borrow. Without running erased terms on a private copy, a proof that writes changes the verdict on programs around it. And without the rule that a recursive function occurs only as the head of a call, a function that passes itself to a helper proves `Eq Nat 0 1`. Switching off owner sets (@sec-obs) admits a closed proof of `Eq Nat 0 1` built from a function that returns a borrow into one of two arguments and an annotated `match` whose type is formed while the hole is in both owners; with owner sets, the arm that picks the second owner must prove a false equation and is rejected.

*What running the rules found.* Writing the checker exposed gaps in earlier versions of the rules, each now fixed: the recursive-function-as-a-value loophole above; an argument evaluated earlier in the same call being invalidated by a later one (`f(&x, x)` ends the first borrow while reading the second argument); recursive calls inside nested closures, which must be checked against the entry values of the enclosing function; and, with trees, the need to apply a split on a sealed program to re-derivations of it as well. Two attacks from a separate review that were live in an earlier version of the checker (@sec-typing) are now regression tests; every row of the counterfactual ledger flips at least one test.
