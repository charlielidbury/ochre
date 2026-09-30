#import "../style.typ": *

== The checker

We implemented the calculus as an executable reference checker in Lean 4, about 5,400 lines with no dependencies, plus about 4,900 lines of examples and tests and 4,300 lines of case studies. Its purpose is fidelity, not performance: a hand derivation can be charitable where the rules are silent, and a program cannot. Programs are written in a concrete syntax close to the one used here, in named blocks of definitions. A `def` must be accepted and a `reject def` rejected. Each verdict is an assertion checked during the build, and each test file also asserts how many verdicts it contains, so a file that silently checks nothing fails the build. The checker's trace of `AddMZero` reproduces the derivation of @sec-overview symbol for symbol. The suite contains every program this paper prints (the artifact's notes map each to its test), every program that must be rejected, among them every counterexample of @fig-why, and every accepted program that went wrong while we designed the calculus. All 1,058 verdicts are as expected: 700 in the examples and tests, and 358 in the two case studies. The compiled checker decides the examples in about 60 ms and the case studies in about 0.5 s.

*The counterfactual ledger.* Every rule the checker applies that is not the evident typing of a form has a switch that turns it off, and a row in the ledger. For each row, the build asserts exactly which verdicts flip when the rule is off, and the row's class, which follows from what flips (@fig-ledger); it also enforces that every row flips something and that every row outside completeness names its witnesses. Confinement backs up the reading of proofs by their declaration: with both off, a false lemma is accepted. The checker decides erasure as @sec-typing-two states it, in a pass over declared types before it runs a term; its earlier classification after the fact is kept as an internal assertion, which agrees on the whole suite, and the rows for four of its clauses were deleted as subsumed. The ledger shows that each rule is needed for some verdict, not that the rules suffice. Nor can it show that a rule is sound when on: switching off a rule that admits more programs can only make the checker reject some. One side condition, non-cumulative universes, has no switch.

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(columns: (20%, 80%), stroke: none, inset: (x: 4pt, y: 2.2pt), align: (left, left),
    table.hline(stroke: 0.5pt),
    [*Class, rows*], [*With the rule off, the checker*],
    table.hline(stroke: 0.4pt),
    [Soundness, 20], [accepts a closed proof of `False`, or a program that goes wrong when run; the row names the witnesses],
    [False lemma, 1], [accepts a false open statement, whose closed instances another rule rejects],
    [Model, 4], [accepts definitions with no set-theoretic meaning, but no known proof of `False`],
    [Policy, 2], [accepts only programs that are true under the other rules],
    [Cost, 1], [accepts programs that copy data without `clone`],
    [Completeness, 21], [only rejects good programs],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The counterfactual ledger, by class. One completeness row switches an extension _on_ instead, confining the bodies of functions that return proofs or types, to record what it would cost.],
) <fig-ledger>


== A verified hash map, against Aeneas <sec-eval-hashmap>

We wrote the resizing hash map that Aeneas verifies @aeneas as one Ochr program, and proved Aeneas's theorems about it. The baseline is Aeneas's 2022 development with its F\* backend, where Z3 discharges the proof obligations; Aeneas has since gained a Lean backend, which we have not compared against. The program is Aeneas's, recursive as theirs is: buckets are association lists; the table is a sequence of buckets, and an operation reaches the key's bucket through a function that returns a mutable borrow of it, as Rust's `&mut slots[i]` does; `Insert` doubles the table once the entries reach the number of buckets, by inserting every entry again; and there are `Get`, `GetMut`, `Remove`, `ContainsKey`, `New` and `Clear`. The theorems are stated about these operations directly. Aeneas states them about a model: it translates the Rust into pure functions, the user writes a second, simpler pure model of the map (`find_s`, the invariant), proves that the translated functions agree with that model, and proves the properties of the model.

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(
    columns: (21%, 15%, 16%, 14%, 17%, 17%), stroke: none, inset: (x: 4pt, y: 2.2pt),
    align: (left, right, right, right, right, right),
    table.hline(stroke: 0.5pt),
    [], [*Spec, model*], [*Implementation*], [*Agreement*], [*Property proofs*], [*Total*],
    table.hline(stroke: 0.4pt),
    table.cell(colspan: 6, emph[Hash map]),
    [Aeneas], [321 / 3.0k], [210 / 1.5k], [459 / 2.7k], [1,680 / 12.5k], [2,670 / 19.7k],
    [Ochr, first version], [144 / 1.1k], [242 / 1.6k], [0], [1,771 / 20.8k], [2,157 / 23.5k],
    [Ochr, final], [146 / 1.1k], [248 / 1.7k], [0], [1,315 / 14.8k], [1,709 / 17.6k],
    table.cell(colspan: 6, emph[Quicksort]),
    [Verus], [6 / 0.1k], [36 / 0.2k], [0], [66 / 0.7k], [108 / 1.1k],
    [Ochr, first version], [30 / 0.2k], [52 / 0.8k], [0], [841 / 16.4k], [923 / 17.4k],
    [Ochr, final], [30 / 0.2k], [53 / 0.8k], [0], [780 / 13.8k], [863 / 14.8k],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The case studies in lines / tokens, counted with one tokenizer, without blanks and comments. _Spec, model_: Aeneas's trusted model of the map (82 / 0.9k) and the pure models its proofs go through; the vocabulary of Ochr's statements and the definitions its proofs use; Verus's two spec functions. _Implementation_: for Aeneas, the Rust and 9 termination measures. _Agreement_: proofs that the translated functions equal the model; not counted are the 550 lines of F\* that Aeneas generates and trusts. _Property proofs_ include the theorem statements. _First version_: before `rewrite`, destructuring `let` and `split`, and for the hash map before `get_mut` was specified by `insert`. The final rows are checked with reads that move, the first versions with reads that copy. Not counted: Ochr's 533-line array library, which holds the counting lemmas that Ochr's permutation proof uses (126 lines, 1.3k tokens) where Verus's `perm` and swap lemma are counted; Verus's `vstd`; and Aeneas's primitives. The split of Verus's file into columns is ours.],
) <fig-sizes>

*What is written.* In tokens, the fairer measure, Ochr's development is 11% smaller than Aeneas's (36% in lines; @fig-sizes). The difference is that Ochr writes no model and no agreement proof, and trusts no translation: in Aeneas those layers are 29% of the hand-written tokens, and dropping them, net of Ochr's own statement vocabulary, saves about 4.5k. Ochr's property proofs pay back about 2.3k of that, since without automation they are 1.18 times Aeneas's, statements included on both sides. The margin is small and depends on counting: Aeneas's file contains 183 lines (1.5k tokens) of dead code, and without them Ochr's development is 31% smaller in lines but only 3% in tokens. The case study also shaped the language. The first complete version was 19% _larger_ in tokens, its proofs 1.66 times Aeneas's, and three forms added during the study closed most of the gap: `rewrite` (@sec-overview), a destructuring `let`, and `split f in t`, described below. A fourth change was to the proofs, not the language: `get_mut`'s theorems now follow from `insert`'s, because writing `w` through the borrow `GetMut` returns is proved equal to `InsertNoResize` of `k` and `w`, a theorem between two in-place operations of the same program. The case study checks in about 0.2 s. Aeneas reports four person-days for its proofs; we have no comparable measure of effort.

*Coverage.* Every theorem of Aeneas's interface has a counterpart that the checker accepts: lookups after `insert` (with resizing), `get_mut` and `remove`, at the key and at any other key; the length, which grows by one exactly when the key was absent; the invariant (the length counts the entries, the keys of a bucket are distinct, every key lies only in its own bucket), kept by every operation; the load factor; and `new` and `clear`. Aeneas's statement about `remove` (`hash_map_remove_back_lem` in `Hashmap.Properties.fsti`) asserts the invariant of the map it was given rather than of the map it returns, and its proof establishes that statement; Ochr's theorem is about the result.

*The program is its own specification.* Where Aeneas says that inserting `key` leaves every other binding unchanged, `forall k'. k' <> key ==> find_s hm' k' == find_s self k'`, about the model `find_s`, Ochr's statement uses the map's own lookup. `Find(m, k)` is `Get(&m, k)`, the in-place lookup run on the map it is given, as `Add` runs `AddM` on its argument in @sec-overview; in a statement, where reads copy, that is a copy of `*hm`:

```
InsertFindOther(hm : &HashMap, k : Word, v : Nat, k2 : Word,
                h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
           (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) :=
  match *hm { HM(n, len, slots) =>
    split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }
```

`InsertNoResize` records the new length according to whether the bucket insert added an entry, a result that is stuck on the unknown bucket. `split f in t` finds, in the goal, the first sealed program whose run is stuck on the result of a call of `f`, generalises that result as [Split] generalises a sealed scrutinee, and checks `t` in every arm; like `rewrite`, it is a typing form that never runs. Here `split BInsert` splits on the insert's result, and in both arms the lemma for the slots applies. That lemma is the bucket lemma lifted through the borrow-returning index by a recursion that follows the index's own, so the untouched buckets stay in place without a congruence step. The invariant is stated the same way: the proposition that every key lies only in the bucket the index returns for it is `Π(k : Word). OnlyIn(s, Idx(k, n), k)`, whose definition uses the bucket lookup.

*Where the programs differ.* Ochr's numbers are unbounded, so there are no overflow obligations and no failing operations; in Aeneas's proofs, overflow bounds take about 3% of the lines, and the cases where an operation fails about 6% more. The table is a list of buckets rather than an array, since arrays came to Ochr later, as a library; indexing is linear and saturates at the last bucket instead of needing a bounds proof. Values are `Nat`s, not a type parameter, because a borrow of a type variable is not a type in Ochr, so a generic `get_mut` cannot be written; and `GetMut` takes a proof that the key is present, since Rust's `Option<&mut V>` stores a borrow inside data. The load factor is fixed at one. As in Rust, reading a value moves it, and reading a number that is only computed with copies it: keys, sizes and lengths are `Word`s. The one value used twice, the one `Get` returns while it stays in the map, is copied by an explicit `clone`.

*What is still costly.* Each lemma is stated three times, for a bucket, for the list of buckets and for the map, and statements are almost half (45%) of Ochr's proof tokens; a single lemma about lifting through the index would need quantification over programs. And there is no automation: every case analysis that Aeneas leaves to Z3 is written out, as a match or a `split`. The thesis holds on these numbers only as far as they go: one development instead of three layers, with fewer lines and slightly fewer tokens than Aeneas's, but with property proofs 1.18 times as long, because Ochr has no solver.

== Arrays and quicksort <sec-eval-qs>

*Arrays are a library.* Ochr has no built-in array. `Cells(E, n)` is a type computed by recursion on `n`, with exactly `n` elements; a view `Slice(E, n)` and an owned `Array(E, n)` wrap it, so the length lives only in the type. The model functions (reading, writing, taking, dropping and joining elements) are ordinary Ochr definitions, and proofs reason about them directly. Eight functions are primitive at runtime: taking the view of an array, `Read`, `Set`, `GetMut` (a borrow of one element), `WithSplit`, and the empty array, push and pop. The checker runs each one's Ochr body as its model; compiled code would call native code, which must be trusted to implement the model and to be the only code that touches the representation. The checker does not yet enforce the second: the representation is ordinary data that user code can match on. A part of an array is borrowed only while a continuation runs, since a pair of borrows cannot be returned (@fig-scope): `WithSplit` passes borrows `l : &Slice(E, k)` and `r : &Slice(E, Sub(n, k))` of the two pieces to a function, and joins what they hold when it returns. So calling any `g` on the first `k` elements leaves the view equal to `JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))`, the old rest joined to `g`'s result, by `refl`.

*Quicksort* is a capability result: a sort of this cons-cell model of arrays, through an interface designed to be implemented by flat arrays, verified in full, with sub-range borrows, in a dependent type theory where the program itself appears in the proofs. Lomuto's quicksort partitions the view in place by swapping, then borrows the two sides of the pivot with `WithSplit` and sorts each. Until Ochr has recursion on a measure, it recurses on fuel. Reads move, as in Rust: indices, lengths and the elements sorted are `Word`s, which are copied, and seven `clone`s copy a generic element, a whole view or the recursion where one is used twice (six in the library, one in quicksort). With fuel equal to the length, the checker accepts its correctness, stated about the in-place program: the result is sorted, and no value's count changes.

```
QSCorrect(n : Word, s : &Slice(Word, n), q : Word) :
    (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
    (let old = *s; Eq Word (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) :=
  ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
```

The proofs are long (@fig-sizes). Verus's quicksort @verus, whose partition is a loop, proves the same two properties in an eighth of the lines and a fourteenth of the tokens, with Z3 discharging the obligations and `vstd` supplying multiset lemmas. Half of Ochr's proofs (392 lines) establish the partition's positional invariant, which Verus states as two quantified loop invariants and leaves to the solver, while in Ochr every case split and every step of index arithmetic is written out. This comparison is not a test of the thesis of @sec-intro-two, which concerns developments that write the program twice (@sec-eval-hashmap); it measures what SMT automation buys, and automation is what Ochr lacks. Ochr needs no solver and no translation, and checks the development in about 0.5 s. With `rewrite` the proofs are a fifth shorter in tokens; the move to `Word` numbers costs 5% back, all of it notation (`Succ(x)` where `S x` was).
