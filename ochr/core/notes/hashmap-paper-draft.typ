#import "../paper/style.typ": *

// Draft of the case-study section, for prop-paper to integrate (suggested heading: "= Case study: a verified hash map <sec-case-study>"). Numbers and programs are from notes/hashmap-case-study.md and lean/Ochr/Examples/17HashMap.lean; the program printed here is that file's `InsertFindOther`, verbatim (de-indented).

We wrote the resizing hash map that Aeneas verifies @aeneas as one Ochr program, and proved Aeneas's theorems about it. The program is Aeneas's, recursive as theirs is: buckets are association lists; the table is a sequence of buckets, and an operation reaches the key's bucket through a function that returns a mutable borrow of it, as Rust's `&mut slots[i]` does; `Insert` doubles the table once the entries outnumber the buckets, by inserting every entry again; and there are `Get`, `GetMut`, `Remove`, `ContainsKey`, `New` and `Clear`. The theorems are stated about these operations directly. Aeneas states them about a model: it translates the Rust into pure functions, the user writes a second, simpler pure model of the map (`find_s`, the invariant), proves that the translated functions agree with that model, and proves the properties of the model.

*What is written.* @fig-hashmap counts both developments with one tokenizer, excluding blanks and comments.

#figure(kind: table, placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(
    columns: (19%, 16%, 17%, 17%, 15%, 16%), stroke: none, inset: (x: 4pt, y: 2.5pt),
    align: (left, right, right, right, right, right),
    table.hline(stroke: 0.5pt),
    [], [*Model*], [*Implementation*], [*Agreement*], [*Properties*], [*Total*],
    table.hline(stroke: 0.4pt),
    [Aeneas], [82 + 239], [201 + 9], [459 + (550)], [1,556 + 124], [2,670 lines \ 19.7k tokens],
    [Ochr], [74 + 72], [248], [0], [1,315], [1,709 lines \ 17.6k tokens],
    [Ochr, first version], [74 + 70], [242], [0], [1,771], [2,157 lines \ 23.5k tokens],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The two developments, in lines. _Model_: Aeneas's trusted model of the map (`find_s`, the invariant) plus 239 lines of internal models its proofs go through; Ochr's statement vocabulary (the invariant, counts) plus 72 lines of definitions used inside proofs. _Implementation_: Aeneas's Rust plus 9 hand-written termination measures. _Agreement_: 459 lines proving that translated functions equal model functions, and in parentheses the 550 lines of F\* the tool generates, which are trusted. _Properties_: the proofs, and Aeneas's 124-line interface. The first version predates the three forms described below, and was checked with reads that copy; the final one with reads that move.],
) <fig-hashmap>

Ochr writes no model and no agreement proof, and trusts no translation. In Aeneas those layers are a quarter of the hand-written tokens. Ochr's property proofs are the longer part instead, 1.26 times Aeneas's in tokens. Overall Ochr's development is 36% smaller in lines and 11% smaller in tokens. The first complete version was 19% _larger_ in tokens than Aeneas's, its proofs 1.8 times as long. Three forms closed most of the gap: `rewrite h in t`, which rewrites the goal with an equation instead of a cast with a hand-written motive; a destructuring `let`; and `split f in t`, which case-splits the goal on a stuck result of a call of `f`, instead of re-running part of the operation to name that result. A fourth change was to the proofs, not the language: `get_mut`'s theorems now follow from `insert`'s, because writing `w` through the borrow `GetMut` returns is proved equal to `InsertNoResize` of `k` and `w`, a theorem between two in-place operations of the same program. The case study checks in about 0.2 s. Aeneas reports four person-days for its proofs; we have no comparable measure of effort.

*Coverage.* Every theorem of Aeneas's interface has a counterpart that the checker accepts: lookups after `insert` (with resizing), `get_mut` and `remove`, at the key and at any other key; the length, which grows by one exactly when the key was absent; the invariant (the length counts the entries, the keys of a bucket are distinct, every key lies only in its own bucket), kept by every operation; the load factor; and `new` and `clear`. Aeneas's statement about `remove` asserts the invariant of the map it was given rather than of the map it returns, and its proof establishes that statement; Ochr's theorem is about the result.

*The program is its own specification.* Where Aeneas says that inserting `key` leaves every other binding unchanged, `forall k'. k' <> key ==> find_s hm' k' == find_s self k'`, about the model `find_s`, Ochr's statement uses the map's own lookup. `Find(m, k)` is `Get(&m, k)`, the in-place lookup run on a copy, as `Add` runs `AddM` on a copy in @sec-overview:

```
def InsertFindOther (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word)
    (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
           (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) := (
  match *hm {
    HM(n, len, slots) => split BInsert in
      SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h),
  }
)
```

`InsertNoResize` records the new length according to whether the bucket insert added an entry, a result that is stuck on the unknown bucket; `split BInsert` splits on it, and in both arms the lemma for the slots applies. That lemma is the bucket lemma lifted through the borrow-returning index by a recursion that follows the index's own, so the untouched buckets stay in place without a congruence step. The invariant is stated the same way: that every key `k` lies only in the bucket the index returns for it is a proposition about every key, `Π(k : Word). OnlyIn(s, Idx(k, n), k)`, whose definition uses the bucket lookup.

*Where the programs differ.* Ochr's numbers are unbounded, so there are no overflow obligations and no failing operations; in Aeneas's proofs, overflow bounds take about 3% of the lines, and the cases where an operation fails about 6% more. The table is a list of buckets rather than an array, since arrays came to Ochr later, as a library; indexing is linear and saturates at the last bucket instead of needing a bounds proof. Values are numbers, not a type parameter, because a borrow of a type variable is not a type in Ochr, so a generic `get_mut` cannot be written; and `GetMut` takes a proof that the key is present, since Rust's `Option<&mut V>` stores a borrow inside data. The load factor is fixed at one. As in Rust, reading a value moves it, and reading a number that is only computed with copies it: keys, sizes and lengths are `Word`s, a library type declared copyable, as `usize` is `Copy`. The one value used twice, the one `Get` returns while it stays in the map, is copied by an explicit `clone`.

*What is still costly.* Two things remain. Each lemma is stated three times, for a bucket, for the list of buckets and for the map, and statements are almost half (45%) of Ochr's proof tokens; a single lemma about lifting through the index would need quantification over programs. And there is no automation: every case analysis that Aeneas leaves to Z3 is written out, as a match or a `split`.
