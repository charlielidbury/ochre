#import "../paper/style.typ": *

// Draft of a half-page case study on arrays and quicksort, for the paper lane to integrate (suggested heading: "== Arrays and quicksort"). Numbers are from notes/arrays-library.md §10 (notes/arrays-count.py over lean/Ochr/Examples/16Arrays.lean, and hashmap-count.py over competitors/verus/src/main.rs); the program printed here is 16Arrays's `QSCorrect`, verbatim (de-indented), and every inline fragment is a substring of that file. The table's "sortedness" row includes the 9-line `QSSortedFull`/`QSCorrect`; "before" is ochr-arrays 9b9b0073, "after" 824166e0. The excerpt is the D53 version (`Word` numbers, reads move); the table's numbers predate D53, and notes/arrays-library.md §12 has the D53 sizes. The paper's own copy of this section is paper/sections/impl.typ.

*Arrays are a library.* Ochr has no built-in array. `Cells(E, n)` is a type computed by recursion on `n`, with exactly `n` elements; a view `Slice(E, n)` and an owned `Array(E, n)` wrap it, so the length lives only in the type and nothing stores it at runtime. The model functions (reading, writing, taking, dropping and joining elements) are ordinary Ochr definitions, and proofs reason about them directly. Eight functions are primitive at runtime: taking the view of an array, `Read`, `Set`, `GetMut` (a borrow of one element), `WithSplit`, and the empty array, push and pop. The checker runs each one's Ochr body as its model, and compiled code would call native code instead, which is trusted to implement the model. Nothing recurses over an array, only over an index, and a part of an array is borrowed only while a continuation runs. `WithSplit` takes the view apart, passes borrows `l : &Slice(E, k)` and `r : &Slice(E, Sub(n, k))` of the two pieces to a function, and joins what they hold when it returns.

*The untouched rest, by definition.* Since the pieces are joined back, calling any `g` on the first `k` elements leaves the view equal to `JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))`: the old rest, joined to `g`'s result, whatever `g` is. The checker proves this by `refl`. To state it about the rest alone takes one lemma (dropping `k` elements from a join), which a built-in array would make definitional too.

*Quicksort.* Lomuto's in-place quicksort partitions the view by swapping, then borrows the two sides of the pivot with `WithSplit` and sorts each. Until Ochr has recursion on a measure, it recurses on fuel. With fuel equal to the length, the checker accepts its correctness, stated about the in-place program itself. The result is sorted, and no value's count changes:

```
def QSCorrect (n : Word) (s : &Slice(Word, n)) (q : Word) :
    (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
      (let old = *s; Eq Word (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := (
  ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
)
```

The proofs are long. @fig-quicksort counts the development with one tokenizer, without blanks and comments, before and after rewriting was written `rewrite h in t` instead of a cast with a hand-written motive.

#figure(kind: table, placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(
    columns: (46%, 27%, 27%), stroke: none, inset: (x: 4pt, y: 2.5pt),
    align: (left, right, right),
    table.hline(stroke: 0.5pt),
    [], [*Casts with motives*], [*`rewrite`*],
    table.hline(stroke: 0.4pt),
    [The program], [52 / 0.8k], [52 / 0.7k],
    [`Sorted` and its two bounds], [30 / 0.2k], [30 / 0.2k],
    [Proof: permutation], [107 / 2.4k], [83 / 1.4k],
    [Proof: sortedness, given the partition's contract], [302 / 4.8k], [305 / 4.5k],
    [Proof: the partition's contract], [432 / 9.2k], [392 / 7.2k],
    table.hline(stroke: 0.4pt),
    [Total], [923 / 17.4k], [862 / 14.1k],
    [Verus @verus], [], [108 / 1.1k],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [Quicksort, in lines / tokens. The program's own erased index proofs were casts too. Not counted: Ochr's 521-line array library and Verus's `vstd`.],
) <fig-quicksort>

Verus's quicksort @verus, a 159-line file, proves the same two properties of a loop-based version, with Z3 discharging the obligations and `vstd` supplying multiset lemmas. Ochr's development is eight times as long in lines, and thirteen times in tokens. Half of Ochr's proofs (392 lines) establish the partition's positional invariant. Verus states that invariant as two quantified loop invariants and leaves it to the solver; in Ochr, every case split and every step of index arithmetic is written out. Ochr needs no solver and no translation, and checks the development in about 0.2 s. With `rewrite` the proofs are a fifth shorter in tokens, and no cast is left, nor any lemma that only oriented one.
