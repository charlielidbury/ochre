#import "../paper/style.typ": *

// Draft of a half-page case study on arrays and quicksort, for the paper lane to integrate (suggested heading: "== Arrays and quicksort"). Numbers are from notes/arrays-library.md §10 (notes/arrays-count.py over lean/Ochr/Examples/16Arrays.lean, and hashmap-count.py over competitors/verus/src/main.rs); the program printed here is 16Arrays's `QSCorrect`, verbatim (de-indented), and every inline fragment is a substring of that file.

*Arrays are a library.* Ochr has no built-in array. `Cells(E, n)` is a type computed by recursion on `n`, with exactly `n` elements; a view `Slice(E, n)` and an owned `Array(E, n)` wrap it, so the length lives only in the type and nothing stores it at runtime. The model functions (reading, writing, taking, dropping and joining elements) are ordinary Ochr definitions, and proofs reason about them directly. Eight functions are primitive at runtime: taking the view of an array, `Read`, `Set`, `GetMut` (a borrow of one element), `WithSplit`, and the empty array, push and pop. The checker runs each one's Ochr body as its model, and compiled code would call native code instead, which is trusted to implement the model. Nothing recurses over an array, only over an index, and a part of an array is borrowed only while a continuation runs. `WithSplit` takes the view apart, passes borrows `l : &Slice(E, k)` and `r : &Slice(E, Sub(n, k))` of the two pieces to a function, and joins what they hold when it returns.

*The untouched rest, by definition.* Since the pieces are joined back, calling any `g` on the first `k` elements leaves the view equal to `JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))`: the old rest, joined to `g`'s result, whatever `g` is. The checker proves this by `refl`. To state it about the rest alone takes one lemma (dropping `k` elements from a join), which a built-in array would make definitional too.

*Quicksort.* Lomuto's in-place quicksort partitions the view by swapping, then borrows the two sides of the pivot with `WithSplit` and sorts each. Until Ochr has recursion on a measure, it recurses on fuel. With fuel equal to the length, the checker accepts its correctness, stated about the in-place program itself. The result is sorted, and no value's count changes:

```
def QSCorrect (n : Nat) (s : &Slice(Nat, n)) (q : Nat) :
    (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
      (let old = *s; Eq Nat (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := (
  ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
)
```

The proofs are long. Counted with one tokenizer, without blanks and comments, the program is 52 lines (0.7k tokens), `Sorted` and its two bounds 30 lines (0.2k), and the proofs 780 lines (13.1k), on top of a 521-line array library. Verus's quicksort @verus, a 159-line file, proves the same two properties of a loop-based version in 108 lines and 1.1k tokens, with Z3 discharging the obligations and `vstd` supplying multiset lemmas. Ochr's development is eight times as long in lines, and thirteen times in tokens. Half of Ochr's proofs (392 lines) establish the partition's positional invariant. Verus states that invariant as two quantified loop invariants and leaves it to the solver; in Ochr, every case split and every step of index arithmetic is written out. Ochr needs no solver and no translation, and checks the development in about 0.2 s. Writing rewrites as `rewrite h in t` rather than as casts with hand-written motives shortened these proofs by a fifth.
