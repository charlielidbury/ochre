#import "../style.typ": *

== The checker

We implemented the calculus as an executable reference checker in Lean 4, about 4,000 lines with no dependencies, plus about 3,500 lines of examples and tests. Its purpose is fidelity, not performance: a hand derivation can be charitable where the rules are silent, and a program cannot. Programs are written in a concrete syntax close to the one used here:

```lean
ochr Numbers {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y, S p => AddM(&p, y) }

  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}
```

A `def` must be accepted and a `reject def` rejected. Each verdict is an assertion checked during the build, and each test file also asserts how many verdicts it contains, so a file that silently checks nothing fails the build.

*Structure.* "Same normal form" is structural equality, except that function values and Π-types are compared at their generic arguments and the unit laws of `And` are applied. The checker's trace of `AddMZero` reproduces the derivation of @sec-overview symbol for symbol.

*Test suite.* The suite contains every program this paper prints (the artifact's notes map each to its test), every program that must be rejected, among them every closed proof of `False` in @fig-why, and every accepted program that went wrong while we designed the calculus. All 519 verdicts are as expected. The compiled checker decides all of them in about 19 ms; a clean build takes about 55 s, most of it re-running the suite for each row of the ledger below.
// TODO(lead): quiet re-measurement of both times at 519 verdicts and 50 ledger rows.

*The counterfactual ledger.* Every rule the checker applies that is not the evident typing of a form has a switch that turns it off, and a row in the ledger. For each row, the build asserts exactly which verdicts flip when the rule is off, and the row's class, which follows from what flips (@fig-ledger).
// TODO(prop-paper): class counts in fig-ledger wait for the post-pre-pass row list. No row flips nothing. Confinement backs up two other rules: the private copy has soundness witnesses, and reading proofs by their declaration a false lemma, only when confinement is off too. Several rows are clauses of the one erasure rule of @sec-typing-two, which the checker implements clause by clause. The ledger shows that each rule is needed for some verdict, not that the rules suffice, and one side condition, non-cumulative universes, has no switch.

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(columns: (17%, 38%, 45%), stroke: none, inset: (x: 4pt, y: 2.5pt), align: (left, left, left),
    table.hline(stroke: 0.5pt),
    [*Class, rows*], [*With the rule off, the checker*], [*Among the rules*],
    table.hline(stroke: 0.4pt),
    [Soundness, 22], [accepts a closed proof of `False` (16 rows) or an open program that goes wrong when run (6); the row names the witnesses], [entry-value recursion; exclusive access; owner sets; the class recorded in Π-types],
    [False lemma, 1], [accepts a false open statement, whose closed instances another rule rejects], [reading proofs by their declaration, with confinement off],
    [Model, 4], [accepts definitions with no set-theoretic meaning, but no known proof of `False`], [a borrow parameter for a returned borrow; subsingleton elimination; borrows only of data; syntactic sorts],
    [Policy, 4], [accepts only programs that are true under the other rules], [erasure by declared type rather than by value; [Close]’s row from the declared codomain; confinement, alone and together with the rule that a variable declared a proposition is a proof],
    [Completeness, 19], [only rejects good programs], [the private copy; generalising before a split; [Seal]’s head guard; the unit laws; injectivity; `J` and zero-arm matches stuck],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The counterfactual ledger, by class. One completeness row switches an extension _on_ instead, confining the bodies of functions that return proofs or types, to record what it would cost.],
) <fig-ledger>

*What running the rules found.* Writing the checker exposed gaps in earlier versions of the rules, each now fixed and a regression test, among them a recursive function passed to a helper as a value, an argument invalidated by a later one (`f(&x, x)`), and a split on a sealed program that must also apply to later re-derivations of it.

== Arrays and quicksort <sec-eval-qs>

*Arrays are a library.* Ochr has no built-in array. `Cells(E, n)` is a type computed by recursion on `n`, with exactly `n` elements; a view `Slice(E, n)` and an owned `Array(E, n)` wrap it, so the length lives only in the type and nothing stores it at runtime. The model functions (reading, writing, taking, dropping and joining elements) are ordinary Ochr definitions, and proofs reason about them directly. Eight functions are primitive at runtime: taking the view of an array, `Read`, `Set`, `GetMut` (a borrow of one element), `WithSplit`, and the empty array, push and pop. The checker runs each one's Ochr body as its model, and compiled code would call native code instead, which is trusted to implement the model. Nothing recurses over an array, only over an index, and a part of an array is borrowed only while a continuation runs: `WithSplit` takes the view apart, passes borrows `l : &Slice(E, k)` and `r : &Slice(E, Sub(n, k))` of the two pieces to a function, and joins what they hold when it returns.

*The untouched rest, by definition.* Since the pieces are joined back, calling any `g` on the first `k` elements leaves the view equal to `JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))`: the old rest, joined to `g`'s result, whatever `g` is. The checker proves this by `refl`. To state it about the rest alone takes one lemma (dropping `k` elements from a join), which a built-in array would make definitional too.

*Quicksort.* This case study is a capability result: a fully verified in-place array sort, with sub-range borrows, in a dependent type theory where the program itself appears in the proofs. Lomuto's quicksort partitions the view in place by swapping, then borrows the two sides of the pivot with `WithSplit` and sorts each. Until Ochr has recursion on a measure, it recurses on fuel. With fuel equal to the length, the checker accepts its correctness, stated about the in-place program: the result is sorted, and no value's count changes.

```
QSCorrect(n : Nat, s : &Slice(Nat, n), q : Nat) :
    (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
    (let old = *s; Eq Nat (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) :=
  ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
```

The proofs are long. Counted with one tokenizer, without blanks and comments, the program is 52 lines (0.7k tokens), `Sorted` and its two bounds 30 lines (0.2k), and the proofs 780 lines (13.1k), on top of a 521-line array library. Verus's quicksort @verus proves the same two properties of a loop-based version in 108 lines and 1.1k tokens, with Z3 discharging the obligations and `vstd` supplying multiset lemmas: Ochr's development is eight times as long in lines and thirteen times in tokens. Half of Ochr's proofs (392 lines) establish the partition's positional invariant, which Verus states as two quantified loop invariants and leaves to the solver, while in Ochr every case split and every step of index arithmetic is written out. This comparison is not a test of the thesis of @sec-intro-two, which concerns developments that write the program twice; it measures what SMT automation buys, and automation is what Ochr lacks. Ochr needs no solver and no translation, and checks the development in about 0.2 s. Writing rewrites with `rewrite` (@sec-overview) rather than as `J` with hand-written motives shortened these proofs by a fifth.
