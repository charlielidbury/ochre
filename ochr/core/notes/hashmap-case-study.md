# Hashmap case study: Ochr against Aeneas (ICFP 2022)

This note covers the paper's flagship case study. It reimplements the resizing hash map that Aeneas verifies (Ho and Protzenko, ICFP 2022, §6) as a single in-place Ochr program, and proves Aeneas's theorem suite about that program. It then measures both developments.

- Branch `ochr-hashmap-v2`: cut from `ochr-core` @ 96d788a1 (RULES v2.1, checker with D52), then merged with `ochr-core` @ 84470253 (D54–D56, D58) and later. On this branch the checker also implements D60 (`rewrite`, destructuring `let`) and D61 (`split f`), both merged into `ochr-core`. Last merged with `ochr-core` @ 8467317d, where D53 (runtime reads move) is on by default; the case study checks with it (§6, "What D53 changed").
- The code is `ochr/core/lean/Ochr/Examples/17HashMap.lean` (it was `16HashMap.lean` until the arrays case study took number 16).
- The counting scripts are `notes/hashmap-count.py`, used for both sides, and `notes/hashmap-count-ochr.py`, which assigns each Ochr declaration to a category.
- `notes/hashmap-aeneas-categories.py` maps every line of Aeneas's `Hashmap.Properties.fst` to a category.
- The earlier v1.8 port is on branch `ochr-hashmap`. `notes/hashmap-design.md` and `notes/hashmap-impl.md` are on that branch too; its findings F1–F3 are revisited below.

## Summary

**Status.** 188 declarations in four `ochr` blocks, all as expected, checked with D53 (runtime reads of non-copy data move). The whole suite is 1039/1039.

**Implementation.** The implementation is Aeneas's, recursive as theirs is:
- new, clear, len, contains_key;
- get, get_mut, insert with resize, remove.

**What is proved.** Every theorem in Aeneas's interface is covered, stated directly about the in-place operations. There is no model, no abstraction function and no refinement proof.
- Every lookup after every operation, get_mut included.
- The length field's evolution.
- The invariant (Aeneas's `hash_map_t_inv` less its overflow bounds), preserved by every operation. The invariant is: len = number of entries, keys distinct per bucket, and every key only in its own bucket.
- Resizing keeps the invariant, every lookup, and the length.
- The load factor is maintained.

**get_mut was briefly walled.** It hit a rules gap: an unreachable arm normalised to `⋆` at a borrow type (§4). The gap was fixed by D58, after which the three theorems checked as written.

**Size.** Hand-written, in lines / tokens. The tokens here are *source* tokens, a size measure only. They are not the effort metric the user intended, which is the tokens an agent spends reaching a verified solution (`ochr/bench/`, user ruling 2026-09-30). The paper reports lines only.

| | Total | Of which property proofs |
|---|---|---|
| Aeneas | 2,670 / 19,701 | 1,556 / 11,736 |
| Ochr, before D60 | 2,157 / 23,525 | 1,771 / 20,807 |
| Ochr, after D60 | 2,024 / 20,804 | 1,638 / 18,086 |
| Ochr, after D60 with get_mut specified by insert | 1,878 / 18,888 | 1,492 / 16,170 |
| Ochr, also with `split` (D61) | 1,694 / 17,441 | 1,308 / 14,723 |
| Ochr, final: with D53 (`Word` keys and sizes, one `clone`) | **1,709 / 17,603** | 1,315 / 14,800 |

The `split` row was measured at 18c53e81. Reformatting `InsertFindOther` for the paper excerpt later added 3 lines, so the file just before D53 counts 1,697 / 17,441 (proofs 1,311 / 14,723); the D53 row's differences below are against that.

- **What Aeneas writes and Ochr does not.** Aeneas writes four things: a Rust program, a hand-written pure model, 459 lines of refinement lemmas linking its generated translation to that model, and the property proofs. The model and the refinement lemmas are a quarter of Aeneas's tokens (4.7k). Ochr writes one program and the property proofs, so those layers are gone, and so is the trusted translation.
- **What Ochr spends instead.** Proofs without automation. Every case split is written out, and before D60 every rewrite was a `J` with an explicit motive. Each lemma is also stated three times, once per level (bucket, slots, map).
- **D60** (`rewrite h in t` and destructuring `let`) removed 13% of the proof tokens: all 37 `J`s, the three combinators that only oriented `J`, and all 45 `Intro` matches.
- **Specifying get_mut by insert** removed a further 11%. Writing through `GetMut` is `InsertNoResize` of the same key (`GetMutIsInsert`), so its theorems follow from insert's. That is a proof-structure change, which rewrite made a one-line step, and it is reported separately from D60.
- **`split f`** (D61) removed a further 9%. It splits the goal on a result it is stuck on, instead of re-running part of the operation on a copy to name that result. All 32 re-run sites are gone.
- **D53** (runtime reads of non-copy data move) cost 12 lines and 162 tokens (+0.9%). Keys, the table size, the length and indices became `Word`s, which reading copies; the one value used twice, the one `Get` returns while it stays in the map, is a `clone` (§6).
- **The final result** against Aeneas: 36% fewer lines and 11% fewer tokens, for full coverage. Ochr's property proofs are 1.26 times Aeneas's.

## 1. What was built

`17HashMap.lean`, four blocks, each `uses` the previous ones. Verdicts: all 188 as expected, with D53 on.

| Block | Contents | Decls | Check time (compiled, median of 21) |
|---|---|---|---|
| `HashMap` | the data; the implementation (32 declarations); 10 concrete runs (2 rejected on purpose) and their helper `W`; 1 negative test (`BGetMoves`, the lookup without its `clone`) | 44 | 24 ms |
| `HashMapLookup` | what `Find` returns after insert, remove, get_mut, new and clear, for the touched key and any other key; `GetMut` is insert (`GetMutIsInsert`); `Get` and `ContainsKey` agree with `Find` and leave the map unchanged; 3 negative tests | 46 | 55 ms |
| `HashMapLength` | the len field after insert, remove and get_mut; `len = Count(slots)` kept by insert, remove, new and clear; 1 negative test | 19 | 25 ms |
| `HashMapResize` | the invariant and its preservation (get_mut's by insert's); resizing keeps the invariant, every lookup and the length; insert with resize (all four of Aeneas's insert clauses); the load factor | 79 | 111 ms |

The check times are from `lake exe tests`, per own declaration, on a machine loaded by other agents (the D53 build, 2026-09-30; the pre-D53 build measured 12/29/13/69 ms on a quieter machine). The whole case study checks in about 0.12–0.3 s, depending on load.

**Build time.**
- `lake build` of the file takes about 30–40 s. It uses the interpreter, and each block re-checks the blocks it uses.
- The case study is registered as `Registry.caseStudies`. It is checked and counted with the tour (expected total 1039) and timed by `lake exe tests`.
- It is kept out of the per-build counterfactual ledger: with it, each ledger row went from about 1.2 s to 5.8 s, and every row would also need its "blocked by" list asserted.
- Its ledger flips are measured once, by `Ochr/Examples/CaseStudyLedger.lean` (§7).

**The idiom.** A statement "after M, P equals Q" is `Id A (M; P) (M; Q)`. The key read in statements is `Find(m, k) := Get(&m, k)`, the in-place `Get` run on a copy, just as `Std`'s `Add` runs `AddM` on a copy. For example:

```
def InsertFindOther (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word)
    (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
           (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r)
```

A proposition that holds after an operation is stated on a copy: `(let c = m; Insert(&c, k, v); Inv(c))`. The reason is D41: a type may not borrow the parameter itself (see §6).

## 2. The table

Counted with `hashmap-count.py`, the same for both sides:
- lines exclude blanks and comments;
- tokens are identifiers, numbers, common multi-character operators (one each) and every other non-space character.

For Ochr, only the text inside `ochr` blocks counts, split by declaration (`hashmap-count-ochr.py`). For Aeneas, `hashmap-aeneas-categories.py` assigns every line of `Hashmap.Properties.fst` to a category, and the categories were checked against a full reading of the file. `#push-options`/`#pop-options` lines are counted as boilerplate. Cells are lines / tokens.

There are five Ochr measurements, all with full coverage (get_mut included):
- **before D60**: the checker at ochr-core @ 84470253, where rewriting is `J` with a motive;
- **after D60**: the same proofs with `rewrite` and destructuring `let`;
- **get_mut by insert**: after D60, with get_mut specified by insert (`GetMutIsInsert`);
- **with `split`**: also with `split f` (D61);
- **final, with D53**: checked with runtime reads moving (D53), so keys, sizes, lengths and indices are `Word`s and `Get` clones the value it returns.

The implementation and the spec are the same in the first four. The note's first version, with get_mut walled, had 1,506 / 17,144 of proofs.

| | Spec / model | Implementation | Agreement proof | Property proofs | Total, hand-written |
|---|---|---|---|---|---|
| **Aeneas** | 82 / 924 trusted views and invariant; + 239 / 2,039 proof-internal models | 201 / 1,484 Rust; + 9 / 39 hand-written termination measures | hand-written: 459 / 2,699 (generated function = hand-written model). Automatic but trusted: the translation, 550 / 2,882 generated F*, and 222 / 1,886 of `Primitives.fst` | 1,556 / 11,736, plus 124 / 780 of theorem statements in the `.fsti` | **2,670 / 19,701** |
| **Ochr, before D60** | 74 / 586 statement vocabulary; + 70 / 539 proof-internal definitions | 242 / 1,593 | **0** | 1,771 / 20,807 | **2,157 / 23,525** |
| **Ochr, after D60** | same | same | **0** | 1,638 / 18,086 | **2,024 / 20,804** |
| **Ochr, get_mut by insert** | same | same | **0** | 1,492 / 16,170 | **1,878 / 18,888** |
| **Ochr, with `split`** | same | same | **0** | 1,308 / 14,723 | **1,694 / 17,441** |
| **Ochr, final (with D53)** | 74 / 590 statement vocabulary; + 72 / 551 proof-internal definitions | 248 / 1,662 | **0** | 1,315 / 14,800 | **1,709 / 17,603** |

**Aeneas, in detail.**
- *Spec/model* is the trusted part: `find_s`, `len_s`, `hash_map_t_inv` and what they use (77 / 858), plus the `.fsti`'s 5 declarations. The proof-internal models are the pure versions of insert, resize and remove that the proofs route through (`hash_map_insert_in_list_s`, `move_elements_s`, `remove_s`, …).
- *Agreement* is the 19 refinement lemmas whose statement says a generated `hash_map_*_fwd/back` equals a hand-written model function (`--target model`).
- *Property proofs* are everything else in the proof file: 1,298 / 10,371. They also include the 5 lemmas that say a read-only operation returns the trusted view (`get` returns `find_s`, 258 / 1,365). Those are the specs of reads, and their Ochr counterparts (`GetFind`, `ContainsFind`, `RemoveResult`) are counted as property proofs too.
- Counting all 23 refinement-shaped lemmas as agreement instead gives 717 / 4,064 for agreement and 1,298 / 10,371 for properties.
- Aeneas's file contains dead code: 163 proof lines and 20 model lines are never used. Without it the Aeneas total is 2,487 / 18,175.
- Aeneas's `test1` (28 Rust lines) is excluded, as the paper excludes it.

**Ochr, in detail.**
- *Implementation* is the 32 definitions of the `HashMap` block, including `IsSome`, `BFind` and `Find`, which `GetMut`'s precondition uses, and `WAdd`, which `Resize` uses (31 before D53).
- *Statement vocabulary* is what the headline theorems' statements mention: `Count`, `BLen`, `Buckets`, `IfNew`, `Shrink`, `Has`, `Unique`, `AllUnique`, `Nowhere`, `OnlyIn`, `Placed`, `Inv`, `NOf`, `NotOver`.
- *Proof-internal definitions*: `Nth`, `IsNone`, `IfFound`, `OrElse`, `BFindLast`, `SFindLast`, `Fresh`, `FreshS`, `AbsentFrom`, `Apart`, `GUnique`.
- Excluded from the Ochr totals: the 10 runs with their helper `W` (74 / 916; 68 / 712 before D53) and the 4 negative tests (37 / 362; 3 tests, 25 / 289, before D53).

**Property proofs by operation** (lines / tokens). The Aeneas column is property proofs as defined above: prop plus view-refinement. Its model-refinement agreement lemmas are shown separately in brackets.

| | Aeneas | Ochr, before D60 | Ochr, after D60 | Ochr, get_mut by insert | Ochr, with `split` | Ochr, final (D53) |
|---|---|---|---|---|---|---|
| insert, bucket level and without resize | 300 / 2,358 [+ 151 / 887] | 344 / 4,075 | 323 / 3,657 | 323 / 3,657 | 279 / 3,276 | 282 / 3,300 |
| resize, and insert with resize | 485 / 3,496 [+ 137 / 854] | 497 / 5,799 | 450 / 4,662 | 450 / 4,662 | 384 / 4,168 | 384 / 4,176 |
| load factor | 33 / 318 | 99 / 969 | 90 / 792 | 90 / 792 | 68 / 658 | 68 / 660 |
| remove | 139 / 847 [+ 109 / 572] | 343 / 3,777 | 324 / 3,388 | 324 / 3,388 | 275 / 2,983 | 275 / 3,005 |
| get, contains_key | 104 / 548 | 54 / 547 | 54 / 547 | 54 / 547 | 54 / 547 | 54 / 551 |
| get_mut | 78 / 439 [+ 62 / 386] | 271 / 3,774 | 243 / 3,481 | 97 / 1,565 | 94 / 1,532 | 94 / 1,536 |
| new, clear, len | 150 / 977 | 58 / 647 | 56 / 594 | 56 / 594 | 56 / 594 | 56 / 608 |
| helpers (lists, arithmetic, keys, equality) | 267 / 2,753 | 105 / 1,219 | 98 / 965 | 98 / 965 | 98 / 965 | 102 / 964 |
| **total** | 1,556 / 11,736 [+ 459 / 2,699] | 1,771 / 20,807 | 1,638 / 18,086 | 1,492 / 16,170 | 1,308 / 14,723 | 1,315 / 14,800 |

- The final column's insert row includes the 3 lines of the `InsertFindOther` reformat. Its other changes are the `Word` renaming (`Succ(x)` is two tokens more than `S x`, `Zero` the same as `0`) and the helpers: `WAddS` and `WAddZero` are proved by recursion on the `Word`, where `AddS` and `AddZero` went through `Std`'s in-place `AddM`.

- Ochr's remove proves more than Aeneas's: the invariant after remove, including placement. Aeneas's statement does not claim it (§3).
- Ochr's load factor needs the bucket count after a resize, which is a sealed program (`ResizeN`, via `InsertN`/`MoveBucketN`/`MoveSlotsN`).
- Before the final measurement, Ochr's get_mut was proved directly: its own lookup, count, uniqueness and placement lemmas at three levels (12 lemmas). The final version proves `GetMutIsInsert` and reuses insert's theorems, which is the move Aeneas makes too (`get_mut_back_lem_refin` models get_mut's backward function as `insert_no_fail_s`).

**Reading the table.**
- **Totals.** In the final version, Ochr's development is 1,709 / 17,603 against Aeneas's 2,670 / 19,701: 36% fewer lines and 11% fewer tokens. The other versions:
  - before D60: 19% fewer lines but 19% *more* tokens;
  - after D60 with get_mut still direct: 24% fewer lines and 6% more tokens;
  - with get_mut by insert, before `split`: 30% fewer lines and 4% fewer tokens;
  - with `split`, before D53: 37% fewer lines and 11% fewer tokens.

  Ochr's lines carry more tokens each, because statements with `Id` are long.
- **What Ochr does not write.** It writes no model and no agreement proof. In Aeneas those are 698 / 4,738 (models plus model refinement), a quarter of the hand-written tokens. It is nearly a third if the read-operation lemmas are counted as agreement. Ochr also trusts no translation: Aeneas's 550 generated lines and its `Primitives` are trusted.
- **What Ochr spends instead.** Its property proofs are still 1.26 times Aeneas's in tokens (14.8k against 11.7k; 1.25 times before D53), for two remaining reasons:
  - there is no automation, where Aeneas has Z3 with fuel and `rlimit` tuning: 56 `#push-options` and 183 `assert` lines;
  - each lemma is stated at three levels. Statements (a proof declaration's tokens before its `:=`, printed by `hashmap-count-ochr.py`) are 45% of Ochr's proof tokens, before and after D53 (45.0% and 44.6%).

  Before `split`, every case split on a sealed result was also written out, including the copy of the program it is taken from (§6).

## 3. Coverage map

Every theorem of Aeneas's interface, `Hashmap.Properties.fsti`, is listed with its Ochr counterpart. All Ochr theorems not marked otherwise are accepted.

"Never fails" has no counterpart in Ochr, because Ochr's operations are total: there is no `Fail`, no overflow, and no panic. Every one of Aeneas's lemmas has a `Fail` clause, which is omitted from the rows below.

| Aeneas (`.fsti`) | Meaning | Ochr |
|---|---|---|
| `hash_map_not_overloaded_lem` | inv ⇒ len ≤ max load, or the map cannot be doubled | `InsertNotOver` (insert with resize keeps `NotOver`, given `Inv`), `RemoveNotOver`, `NewNotOver`, `ClearNotOver`. Load factor 1 (§5). Aeneas's lemma is `()` because the clause is inside `hash_map_t_inv`; the work is in their insert proof (`new_max_load_lem`, 32 + 37 lines). |
| `hash_map_new_fwd_lem` | new: inv, len 0, every `find_s` is None | `NewInv`, `NewFind(n, k)` (for every `k`: `Find(New(n), k)` is `None`), `NewCount`. The length being 0 is definitional (`New(n) = HM(n, 0, …)`). |
| `hash_map_clear_fwd_back_lem` | clear: inv, len 0, empty | `ClearInv`, `ClearFind`, `ClearCount` |
| `hash_map_len_fwd_lem` | `len` returns `len_s` | nothing needed. `Len` is the field, just as `len_s` is `num_entries` in Aeneas (whose proof is `()`). |
| `hash_map_insert_fwd_back_lem` | inv kept; key ↦ value; other keys unchanged; len + 1 iff the key was new | `InsertInvR`, `InsertFindR`, `InsertFindOtherR`, `InsertLenR` (`Len` after = `IfNew(Find(m, k), Len(m))`), all for `Insert` with resize, given `Inv(m)`. Without resize, and without the invariant: `InsertFind`, `InsertFindOther`, `InsertLen`, `InsertCount`, `InsertInv`. Resize alone: `ResizeInv` (no hypothesis), `ResizeFind`, `ResizeLen`. |
| `hash_map_contains_key_fwd_lem` | returns `Some? (find_s k)` | `ContainsFind`: `ContainsKey(&*hm, k)` returns `Has(Find(*hm, k))` **and leaves the map as it was** |
| `hash_map_get_fwd_lem` | returns `find_s k` (Fail iff absent) | `GetFind`: `Get(&*hm, k)` returns `Find(*hm, k)` and leaves the map as it was. `Get` returns an `Opt` by value (§5). |
| `hash_map_get_mut_fwd_lem` | the borrow's value is `find_s k` | `GetMutRead`: the value read through the borrow is what `Find(*hm, k)` returned. |
| `hash_map_get_mut_back_lem` | after writing: inv, len unchanged, key ↦ new value, others unchanged | `GetMutIsInsert` (writing `w` through the borrow is `InsertNoResize(hm, k, w)`), and from it `GetMutFind`, `GetMutFindOther` and `GetMutInv`. Also `GetMutLen` and `GetMutNotOver`. The count is part of `GetMutInv`. |
| `hash_map_remove_fwd_lem` | returns `find_s k` | `RemoveResult`: `Remove(&*hm, k)` returns what `Find(*hm, k)` returned. |
| `hash_map_remove_back_lem` | key gone; others unchanged; len − 1 iff present; "inv" | `RemoveFind` (needs only the per-bucket uniqueness part of the invariant), `RemoveFindOther`, `RemoveLen` (len' = `Pred(len)` iff found, which is what the code does, unconditionally), `RemoveCount`, `RemoveInv`. |

**Aeneas's `remove_back` statement is misstated.** The census of the Aeneas artifact confirmed this, lines .fsti 255 and .fst 3229. `hash_map_remove_back_lem` ensures `hash_map_t_inv self`, the precondition, not the invariant of the result. The .fst does not prove the stronger statement either. So in Aeneas no operation can be verified after a `remove`, because they all require the invariant. The paper's `test1` sequence (insert ×4, get, get_mut, remove, get ×3) is checked only by evaluation, via `assert_norm`. Ochr's `RemoveInv` proves that the invariant is kept.

**Proved in Ochr with no Aeneas counterpart:**
- `GetFind` and `ContainsFind` show that the reads leave the map unchanged. Aeneas's reads are pure functions, so there is nothing to prove there.
- `ResizeInv` holds with **no** hypothesis on the old map.
- `GetMutIsInsert` says one program does what another does. Aeneas proves the same thing between its generated code and a model (`get_mut_back_lem_refin`); here it is between two operations of the same program.
- The negative tests show that the hypotheses are needed and the splits are necessary: `InsertFindNoSplit`, `BRemoveFindDup`, `InsertCountNoHyp`.

**Aeneas's resize lemmas.** They are internal to the insert proof (`try_resize_fwd_back_lem`, `move_elements_fwd_back_lem`), 549 lines. Ochr's `MoveBucketInv` … `ResizeLen` cover the same ground (§2).

## 4. GetMut, and the wall it hit

`GetMut(hm, k, h : IsSome(Find(*hm, k))) : &Nat` takes a proof that the key is present.

**Why it takes a proof.** Rust's `get_mut` returns `Option<&mut V>`, which Ochr cannot express: D48 allows no borrows inside data. Aeneas's version panics instead.

**The impossible arm.** At the end of a bucket, `BGetMut`'s `BNil` arm is impossible. There `h : IsSome(None)`, which is `False`, and the arm is `match h {}`. The v1.8 port did ex falso into `&Nat` by `J` with a `Type`-valued motive instead, which D48 (2) now forbids.

**The wall.** Before D58, every theorem about writing through the borrow was rejected. They are proved by recursion on the bucket, and in the `BNil` arm the checker re-normalises the goal after the split `σ := BNil`. That ran `BGetMut` into its unreachable `match h {}`. D49 (5) then gave that match the value `⋆` at every type, including `&Nat`. The goal read `*q` from `⋆`, which is a normalisation error, and D29 makes a normalisation error a type error. All of this happened before the arm's own `match h {}` could discharge the goal.

Minimal program, as reported:

```
def IsZ (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
def G (x : &Nat) (h : IsZ(*x)) : &Nat := match *x { Z => x, S _ => match h {} }
def T (x : &Nat) (h : IsZ(*x)) : Id Nat (let q = G(&*x, h); *q) 0 := match *x { Z => refl, S _ => match h {} }
-- T, before D58: rejected, "no such place *r: its path does not exist in ⋆"
```

**The fix, D58.** A zero-arm match outside a proof position is stuck, not `⋆`.
- It changes no closed result, because the arm is unreachable in every closed run.
- An open goal simply stays neutral, and the arm's `match h {}` fits it.

After the merge, `BGetMutRead`, `BGetMutFind` and `BGetMutFindOther` were accepted as written, and nothing else in the case study changed verdict.

**The coverage now.** get_mut is fully covered:
- `GetMutRead`: the forward value.
- `GetMutIsInsert`, with `GetMutFind`, `GetMutFindOther` and `GetMutInv` following from insert's theorems.
- `GetMutLen` and `GetMutNotOver`.

The case-study ledger (§7) shows what D58 is doing here: switching it off rejects exactly the get_mut theorems.

## 5. Divergences

- **Numbers.** Keys, sizes and lengths are `Word`s, `Std`'s copy type of numbers, and values are `Nat`s; both are unbounded, so there are no overflow obligations, no `Fail` cases and no saturation.
  - Aeneas's `usize` arithmetic can fail. In their development, 88 generated lines are `Fail` arms and 115 proof lines handle them (69 of those are literally `| Fail -> ()`).
  - About 50–65 proof lines are overflow bounds, and the `try_resize` guard ("cannot double") is part of their invariant and their insert statement.
  - Ochr has none of this, which flatters it by roughly 3–5% of their proofs.
- **Slots.** The slots are a non-empty list of buckets, not a `Vec`, because Ochr has no arrays yet.
  - `Slot(s, i)`, the index borrow, is O(n) and saturates at the last bucket instead of panicking out of range. So no bounds proof is needed, and the placement invariant is stated relative to `Slot`'s own indexing: it needs no "n + 1 buckets" clause.
  - Aeneas's `Vec::index_mut` is O(1) and has a bounds obligation.
  - A primitive O(1) array with the same interface is the arrays work (D57); nothing in the proofs depends on the list beyond `Slot`'s recursion.
- **Hash and index.** Both use the identity hash. Ochr's index is `k mod (n + 1)`, by structural recursion with a running remainder (`ModGo`); Aeneas's is `hash_key k % length slots`. No Ochr theorem looks inside `Idx`.
- **Load factor.** Ochr's is fixed at 1: `Insert` resizes when `len > n` with `n + 1` buckets, and a resize goes to `2n + 2` buckets. Aeneas's is a configurable fraction (4/5 by default) stored in the map as `(dividend, divisor)`, with `max_load` precomputed, and resize doubles the capacity unless that would overflow.
- **Values.** Values are `Nat`, where Aeneas has a generic `t`. With D46, `Bucket(V)` could be polymorphic, except for `GetMut`: D48 forbids `&A` for a type variable `A`, so a generic `get_mut` cannot be written. The value type is fixed for the whole map rather than specialised for `GetMut` alone.
- **Get and GetMut.** `Get` returns an `Opt` by value, not `&T`, because Ochr has no shared borrows and no `Option<&T>`. `GetMut` takes a presence proof instead of panicking.
- **Remove.** `Remove` returns the removed value, as Aeneas's does.
- **Clear.** `Clear` replaces the slots with `EmptySlots(n)`; Aeneas's `clear_slots` walks and empties them in place.
- **Reads.** The checker runs with D53: a runtime read of data that is not a copy type moves it. Keys, the table size, the length and bucket indices are `Word`s, which reading copies, as Rust's `usize` is `Copy`; values are `Nat`s, which move, as a non-`Copy` `V` does in Rust. Before D53 this bullet predicted a `clone` at every reuse of a key or size: in `EqB(k', k)` in the five bucket functions, `Idx(k, n)` in the five map operations and `Lt(n, len)` in `Insert`. `Word` removed all of them. What remains:
  - one `clone`, in `BGet`: `Some(clone(v'))`. The value stays in the bucket and a copy is returned. Rust's `get` returns a shared borrow, which Ochr does not have. Without it the borrow of the bucket ends partly moved out (`BGetMoves`, rejected);
  - `Nth`, a proof-internal definition, takes bucket `i` out through `Slot`'s borrow and puts `BNil` back (Rust's `mem::take`), instead of reading `*r` and ending the borrow partly moved;
  - `let old = slots` in `Resize`, `*b := t` in `BRemove`, and `len := Succ(len)` / `len := Pred(len)` are moves that D53 accepts as written.

  The proofs are unaffected: they are erased, so their reads copy, and so are the statements' `Find(*hm, k)` and `Some(v)` after `v` was moved into the bucket.
- **Tests.** Aeneas's `test1` is 28 Rust lines, excluded from their 201. Ochr's ten runs, 68 lines, are excluded from its implementation count.

## 6. Findings about the language

### What v2.x fixed, measured against the v1.8 port

The v1.8 port had 105 declarations, 11.3k tokens, and covered insert without resize and remove. The same theorem chains, measured in tokens (definitions and helper lemmas included; v2.1 is before D60):

| Chain | v1.8 | v2.1 | Why |
|---|---|---|---|
| H5, insert leaves another key's lookup | 1,720 | 960 | F1' is gone (below); `EqBContra` replaces `ExFalsoFT`/`BoolAbsurd` |
| H4, insert then lookup | 617 | 495 | `match p {}` on a refined `false = true` replaces `ExFalsoFT` |
| H1', remove then lookup | 413 | 217 | ∧-elimination (`match h { Intro(a, r) => … }`) lets the invariant be the natural "keys distinct" (`Unique`), instead of the query-indexed `AtMostOnce`/`BAbsent` pair |

- **False, and matching on it** (D45, D47). `Eq Bool false true` computes to `False`, so every "impossible" arm is `match h {}` on a hypothesis whose type the split refined.
  - v1.8 needed `ExFalso`/`ExFalsoFT`/`BoolAbsurd`, each a `J` with a crafted motive.
  - Now there are 38 zero-arm matches and no ex-falso lemma.
  - `EqBContra` ("a stored key equal to both `k` and `k2` contradicts `k ≠ k2`") is two splits and two `match _ {}`.
- **Taking And apart** (D45). Before D60 there were 45 `Intro(…)` matches: the invariant's three parts, the slots' per-bucket facts, and the recursive hypotheses. Since D60 they are 39 destructuring `let`s.
  - v1.8 had no ∧-elimination, so a lemma whose type carried a conjunct could be used only where the goal carried the same conjunct. That made F1 expensive.
  - Now proofs take hypotheses apart freely.
- **Injectivity** (D52). `S a = S b` is `a = b`. So:
  - `EqBSound`'s successor case is the recursive call as it stands, where v1.8 needed one `J`.
  - Each arm of `BInsertCount`/`BRemoveCount` is the induction hypothesis as it stands.
  - `AddAssoc` is bare recursion.
  - No congruence lemma for `S` is needed anywhere. Before D60, congruence under `Add` and in `Opt` positions, which injectivity does not cover, took `J`s and `TransO`; since D60 it is `rewrite`.
- **F1 now, reading through a mutable borrow.** Statements read with `Find(*hm, k)`, which is `Get` on a copy. The read leaves no residue in the observed map, so every statement computes to the single interesting equation. The consequences:
  - The v1.8 statements carried a bucket conjunct, which forced "call the lemma on a copy" workarounds.
  - F1' is gone. H5's right-hand side, the lookup and then the insert, is now the same sealed insert as the left's. The proof has one split instead of four arms, and needs no `NthInsertAfterGet` lemma pair.
  - What F1 still costs is the link between the in-place reads and the copies: `GetFind` and `ContainsFind`, each a bucket, a slot and a map lemma of bare recursion. Together that is 6 declarations, 54 lines, 547 tokens: 3% of the proofs.
  - With shared borrows, `Find` would be `Get` itself and these six lemmas would go.

### What D60 changed

D60 added two forms to the checker on this branch (tests: `Rewriting` in `05Equality.lean`, `Destructuring` in `11Propositions.lean`):
- `rewrite h in t` / `rewrite ← h in t`: a typing rule that abstracts `b`'s occurrences in the goal and substitutes `a`, which is `J` with the motive read off the goal;
- destructuring `let ⟨x, y, …⟩ = p; u` and `let (x, y) = p; u`.

The case study was then rewritten with them:

| | before D60 | after D60 |
|---|---|---|
| `J` with an explicit motive | 37 | 0 |
| `TransO` / `TransN` / `SymmN` (which only orient `J`) | 3 definitions, 27 uses | deleted |
| `match h { Intro(a, b) => … }` | 45 | 0 (39 `let ⟨…⟩`) |
| names bound only for a motive (`let bl = BLen(b)`, `let mb = m; MoveBucket(b, &mb)`, …) | about 70 lines | gone |
| property proofs, lines / tokens | 1,771 / 20,807 | 1,638 / 18,086 (-7.5% / -13%) |

For example, `MoveBucketLen`'s cons arm was a `let grew = J(…)` with a motive, then `TransN` of a `J` and a `SymmN` of `AddS`, 7 lines. It is now one chain of rewrites that reads as the calculation:

```
rewrite ← WAddS(Len(m), BLen(t)) in
rewrite ← MoveBucketLen(t, m2, FreshInsert(t, m, k, v, ft, a), ut) in
rewrite ← InsertLen(&mc, k, v) in
rewrite ← f in refl
```

`rewrite` also made `GetMutIsInsert` pay off. Once writing through `GetMut` is proved to be the insert, each get_mut theorem is `rewrite ← GetMutIsInsert(…) in` the insert theorem. That replaced 12 direct lemmas: get_mut's proofs went from 3,481 tokens to 1,565.

What `rewrite` does not do well, from this rewrite:
- **It rewrites by occurrence.** Where the equated value also occurs elsewhere in the goal, it is too coarse. This happened once. In `MoveBucketFind`, the abstract key `k` also occurs inside the map's sealed program, so rewriting `k` to `k'` would change the map too. That step keeps a `let found : Eq Opt (Find(m2, k)) (Some(v')) = (rewrite …)` annotation to narrow the goal.
- **It sees normal forms.** `Add(S x, y)` normalises to `S (Add(x, y))`, so `S (Len(m))` does not occur in a goal that mentions `Add(S (Len(m)), BLen(t))`. The rewrites must be ordered so that each target occurs: in `MoveBucketLen`, rewrite `Len(mb)` away first, then `Len(m2)`. Likewise, an annotation that computes to `False` has nothing left to rewrite. `NeqFlip` was reproved with two splits instead.
- **It needs a known goal.** That means tail position, a call's argument, a constructor's field (a small checker change: `evalCtor` now passes a field's type to a `rewrite` argument), or `let x : T = (rewrite …);`. As a `let`'s right-hand side it needs parentheses, like any `:10` form.
- **A rewrite that finds nothing is an error.** That is how a wrong direction shows up (`RwWrongDir`). Rewriting a sealed program in the wrong direction can also leave a goal nothing proves (`RwSealedWrongDir`).

### What remained after D60, and `split`

After D60, Ochr's property proofs were 1.38 times Aeneas's in tokens. The remaining overhead had three sources.

- **Statements, restated at three levels.** Statements are 44% of the proof tokens (8.0k of 18.1k, before get_mut went through insert).
  - The 14 `Slot…` lemmas alone state 1.9k tokens, repeating a bucket lemma with `Slot(&*s, i)`/`Nth(*s, i)` in place of the bucket. Their bodies are 6–10 lines of recursion that needs no insight.
  - This is the price of the environment doing the congruence (no rewriting in the lifts). A generic "lift through the index borrow" lemma would need quantification over programs, which Ochr does not have. This one remains.
- **Re-running a sealed result to split on it.**
  - *The pattern.* An operation branches on a sealed result: the `added` flag, the removed value, the `full` test. A map-level proof re-ran that part on a copy of the slots (`let c = slots; let b = Slot(&c, Idx(k, n)); let added = BInsert(b, k, v);`) and split on the copy. Then the goal computes, and D34 carries the split into the goal's own copy of the program. `InsertFindNoSplit` (rejected) shows the split is necessary.
  - *How much there was.* 32 sites (31 before `GetMutIsInsert` added one), plus 33 splits on a spec-side sealed value (`let r = BFind(…); match r { … }`), done so that `IfNew`/`OrElse`/`IfFound` compute. Together that was 8.5% of the proofs.
- **No automation.** Aeneas's bucket-level lemmas are closed by Z3 with fuel and `rlimit` tuning. Ochr's are case splits written out, which is the bulk of the bodies. This one remains.

**`split f in t` / `split f { C₁ => t₁, … }` (D61), implemented** (checker `findSplit`/`splitTarget`; tests: block `Splitting` in `08CaseSplits.lean`).
- **Find.** Walk the goal's sealed programs in pre-order, left to right. From each, follow the chain of scrutinees its run is stuck on; each link is the content of the scrutinee of the match the previous run stopped at. Take the first link that is a sealed program whose head call is `f`. A link may also be an abstract value standing for a sealed program generalised earlier (a split in a sibling arm), and then it is split directly.
- **Split.** Generalise the neutral as [Split] does (D34) and split it over its type's constructors.
- **What the machine gained.** A stuck untyped match reports the neutral it was stuck on. This is a pure diagnostic and changes no result: the neutral rides on the machine's existing "stuck" signal (`Fail.stuck`), every other handler ignores it, and only `split`'s search (`stuckScrutinee`) reads it. When `split` landed (e87bece1), the 733 existing verdicts kept their results and the ledger rows changed only by gaining the new `Splitting` tests.
- **Why `f` must be named.** The design first proposed "the first stuck sealed scrutinee", but that picks the wrong neutral here. InsertFind's goal is stuck on the sealed map, the map on the `added` flag, and the flag on the bucket. The proof needs the middle link, and the lookup splits need the outermost. So `split` names the head function of the neutral to split.

**Result.**
- All 32 re-run sites are now `split BInsert`, `split BRemove` or `split Lt`.
- 28 of the 33 spec-side splits are `split BGet`, `split BFindLast` or `split SFindLast`.
- 5 stay as `let r = …; match r`. There the goal does not mention the neutral at all; only a lemma's type does (the contradiction lemma in `GetMutIsInsert`, `InsertCount` and `RemoveCount`; `ResizeFind`; `FreshMove`).
- Proofs went from 1,492 / 16,170 to 1,308 / 14,723 (-12% lines, -9% tokens): 1.25 times Aeneas's, as estimated.
- `InsertFindR`, for example, is now:

```
split BInsert in split Lt {
  false => InsertFind(&mc, k, v),
  true => rewrite ← ResizeFind(m2, k, InsertInv(m, k, v, h)) in InsertFind(&mc, k, v),
}
```

  It was two copies, two re-run `let`s, two nested matches and four arms.
- *Check time.* `split` re-runs the goal's sealed programs to follow their chains. The case study's compiled check time stays at about 0.15–0.25 s; the variance from machine load is larger than the difference.

### What D53 changed

D53 (runtime reads of non-copy data move) went on by default at `ochr-core` @ 8467317d, with the case studies held back in `Test.preD53`. Switching it on for the hash map as written changed 145 of its 186 verdicts: 9 declarations were rejected directly and 136 because they use one of those. The 9 are the functions that read a key or a size twice (`BGet`, `BContains`, `BInsert`, `BRemove` and `BFindLast` read `k` in `EqB(k', k)` and again in the recursive call; `ModGo` and `New` read `n` twice), `Clear`, whose `n` was moved into `EmptySlots(n)` and left the map partly moved, and `Nth`, which moved a bucket out through a borrow.

The change, all in `17HashMap.lean` (7ec22e28):
- **`Word` for numbers that are only computed with.** `Std` declares `copy inductive Word := Zero | Succ(pred : Word)`. Keys, `n`, `len`, bucket indices, counts and bucket lengths became `Word`s, with the case study's own `Word` versions of `EqB`, `Lt`, `ModGo`, `Idx`, `Pred` and `WAdd` (for `Resize`'s `2n + 2` and for `Count`). The rest is renaming: `Z`/`S` to `Zero`/`Succ`, and `Id Nat`/`Eq Nat` to `Id Word`/`Eq Word` for lengths and counts. Values stay `Nat` and are moved into buckets. The runs write `W(3)` for the `Word` 3.
- **One `clone`**, where data is used twice: `BGet` returns `Some(clone(v'))`, leaving the value in the bucket. `BGetMoves`, the same function without it, is rejected: "a borrow ends while its content is partly moved out (`BCons(σ2, ⊥, σ4)`)".
- **`Nth` takes and refills.** `Nth(s, i)` read `*r` through `r = Slot(&s, i)`, a move out of a borrow that ends partly moved. It now takes the bucket and puts `BNil` back. It must still go through `Slot`: at abstract slots its normal form is then the same sealed program as the bucket that the closed-off `Get` reads (`⌈let c1 = σ; let r = Slot(&c1, i); *r⌉`), and the lifting lemmas rely on that. A version by recursion on the slots, the obvious alternative, left `⌈Nth(σ, i)⌉` stuck as a different neutral: it rejected 13 theorems directly (`InsertFind`, `GetFind`, `NewFind`, `ResizeFind`, …) and 33 with the ones that use them.
- **Arithmetic lemmas by recursion.** `WAddS` (`x + (y + 1) = (x + y) + 1`) and `WAddZero` are proved by recursion on the `Word`. Their `Nat` versions went through `Std`'s in-place `AddM` (`AddMS`, `AddMZero`), which has no `Word` counterpart; `AddMS` is gone.
- **No proof changed beyond renaming.** Proofs and statements are erased, so their reads copy (P3), and the statements' reuse of a moved value (`BInsert(&*b, k, v); Some(v)`) is an erased read of a ghost.

**Cost.** 1,697 / 17,441 before, 1,709 / 17,603 after (+12 lines, +162 tokens, +0.9%): implementation +6 / +69 (`WAdd`, the `clone`, `Succ(…)`), proof-internal definitions +2 / +12 (`Nth`), statement vocabulary +0 / +4, proofs +4 / +77. The `W` helper and `BGetMoves` are outside the totals, with the runs and the negative tests.

**One `clone`.** The five bucket functions, the five map operations, `Insert`'s load test, `Resize` and every proof need none.

### Other awkward points

- **Postconditions on a copy** (D41). A proposition about the state after an operation can only be a type that runs the operation on a local copy: `(let c = m; Insert(&c, k, v); Inv(c))`. D41 rejects `(BInsert(&*b, k, v); Unique(*b))`, because a type may not borrow a place that outlives it. `Id` is the exception.
  - So the case study has two statement styles: `Id` statements over a borrowed parameter (lookups, lengths) and propositions over a value parameter (the invariant). The two meet through calls on local copies, for example `InsertCount(&mc, …)` inside `InsertInv`.
  - `rewrite` bridges them too: `GetMutInv` rewrites `Inv` of the post-get_mut copy with `GetMutIsInsert(&m, …)`, which is an `Id` statement about the value parameter `m`.
  - This is sound and it works, but a reader must learn both styles.
- **Motives cannot mention a place under a borrow** (before D60). `J`'s motive is a type, and a type may not capture a borrow. So `λ(z) : Prop => Eq Opt (BFind(t, z)) None`, where `t` is a pattern variable under the borrow `b`, was rejected: "captures the borrow b". Copying first (`let c = t;`) fixed it. `rewrite` has no motive to write, so the copy is gone.
- **Zero-arm matches outside tail position.** A `match h {}` nested inside a non-tail `let x : T = match …` still asks for an annotation, because the expected type does not reach the inner match. `HeadApart` was split out as a lemma to put the match in tail position.
- **Small things.**
  - `at` is not a usable variable name (it is a Lean keyword).
  - Proofs that mutate their own locals and then call lemmas about them (`let m2 = m; InsertNoResize(&m2, k, v); MoveBucketInv(t, m2, InsertInv(m, k, v, h))`) read naturally and are allowed. They were the key to `MoveBucketInv`/`MoveBucketFind`/`MoveBucketLen`, whose induction hypothesis is about the map after one insert.

### Quantifying over every key was not a wall

The task named "anything needing ∀ over keys" as a candidate wall. It was not one.
- Placement is `Placed(s, n) = Π(k : Word). OnlyIn(s, Idx(k, n), k)`. It is proved by `λ(k2 : Word) : OnlyIn(c, Idx(k2, n), k2) => …`, with a split on `EqB(k, k2)` inside the λ and a rewrite along `k = k2` (a `J` before D60). It is used by applying it: `hp(k)`.
- Deriving global key uniqueness from placement (`GUniqueOf`, for `ResizeLen`) takes the bucket-index function as a parameter, `D : Π(k : Word). Word`. The tail's hypothesis is then `Π(k). OnlyIn(t, Pred(D(k)), k)`.
- It also passes a proof-valued function, `Π(k : Word) (nw : Nowhere(t, k)). Eq Opt (BFind(cur, k)) None` ("this bucket is part of `t`").
- Every one of these was accepted as first written.

The task also named resize correctness as a candidate wall. `ResizeInv`, `ResizeFind` and `ResizeLen` hold, and the whole resize and insert-with-resize section is 497 lines. Aeneas spends 549 lines on the same ground.

## 7. Which rules the case study depends on

`Ochr/Examples/CaseStudyLedger.lean` switches off each of the ledger's 50 rules in turn and re-checks the four blocks. One pass takes about 15 minutes in the interpreter. The raw output for the final version is in `notes/hashmap-case-study-ledger.txt`.

**No switch makes the case study accept anything it rejects.** Every flip is to *rejected*. The three negative tests stay rejected under every switch, and nothing in the case study is accepted only because some rule is missing. 35 of the 50 rows flip nothing at all.

The 15 rows that do flip declarations (final version; blocked = rejected only because a declaration it uses flipped):

| Rule switched off | Flips | Blocked | What depends on it |
|---|---|---|---|
| C8, generalise a sealed scrutinee before splitting | 30 | 109 | every function that branches on a key comparison, so almost everything |
| G1, a generalised neutral stays generalised when re-derived | 49 | 42 | every proof that splits on a key comparison the goal re-derives |
| captured values keep their declared types (D51) | 48 | 0 | the placement and uniqueness lemmas (λs and motives capturing proofs and sealed values) |
| D45, a match on a proof is by its type | 41 | 0 | every destructuring of a proof |
| D27, proof parameters are ⋆ at the generic call | 38 | 0 | the same, from the other side |
| D47, distinct constructors are disjoint | 36 | 32 | every `match h {}` on a refined `false = true` or `Some = None` |
| D52, `Eq` is injective | 20 | 32 | `EqBSound`, the count lemmas, `AddAssoc` |
| D48 (3), Π-types compared under binders | 19 | 0 | every use of `Placed = Π(k). OnlyIn(…)` |
| P1 / P3 (erasure findings, 5 rows) | 17 each | 0 | the λ-proofs of placement |
| D58, a zero-arm match outside a proof is stuck | 8 | 1 | get_mut's theorems |
| D19, [Access] ends loans inside the content | 3 | 0 | `GetMutFind`, `GetMutFindOther`, `GetMutNotOver` (writing through the returned borrow) |

**Before D60.** The same pass on the pre-D60 version (merged checker, get_mut direct) flipped the same rows. The counts differ where the proofs changed:
- D58 flipped 15 there, because the direct get_mut lemmas each met the unreachable arm;
- D19 flipped 12 there, against 3 now, for the same reason.

## 8. For the paper: a one-page summary

**The claim tested.** In the two-program setups (Aeneas, and likewise ATS, Low*, VeriFast), a verified program is three artefacts: an efficient implementation, a pure specification or model, and a proof that the two agree. Properties are then proved about the model. In Ochr it is one artefact: the in-place program, with theorems stated and proved about that program.

**The case study.** Aeneas's resizing hash map, the ICFP 2022 flagship, written once in Ochr: 32 definitions, 248 lines, with keys and sizes of a copy type and one `clone`. It covers:
- buckets as association lists;
- an index borrow for the slots;
- insert with a doubling resize that re-inserts every entry;
- get, get_mut, remove, contains_key, new, clear.

Aeneas's theorem suite is proved about that code:
- lookups after each operation;
- the length;
- the invariant (the length counts the entries, keys are distinct in each bucket, every key is only in its own bucket);
- resizing keeps the invariant, every lookup and the length;
- the load factor.

**Results.**
- **Coverage.** Aeneas's whole interface is covered, in 188 declarations, all accepted except the negative tests, which are rejected as intended.
- **Size, first measurement.** With rewriting done by `J` and explicit motives, Ochr's hand-written total was 2,157 lines / 23.5k tokens, against Aeneas's 2,670 lines / 19.7k tokens: 19% *more* tokens.
- **Size, final.** With `rewrite` and destructuring `let` (D60), get_mut specified by insert, and `split` (D61), it was 1,694 lines / 17.4k tokens; checked with reads that move (D53), with `Word` keys and sizes and one `clone`, it is 1,709 lines / 17.6k tokens: 36% fewer lines and 11% fewer tokens than Aeneas.
- **Where the size goes.** Aeneas's pure model and its refinement lemmas are a quarter of its hand-written tokens, and they have no counterpart in Ochr. What Ochr spends instead is proof text without automation, 1.26 times Aeneas's property proofs: statements restated at each level, and case analysis written out. Aeneas has Z3 for the case analysis.
- **Check time.** The case study checks in about 0.1–0.3 s.

**One thing Ochr proves that Aeneas's interface does not.** Aeneas's `remove` lemma states the invariant of its *input* (a slip), so no Aeneas client can call an operation after a `remove`. Ochr's `RemoveInv` is about the result.

**Suggested excerpts.** Each is the declaration in `17HashMap.lean`, verbatim, de-indented.

(a) *The program is its own specification.* In Aeneas, "other keys are unchanged" is stated about `find_s`, a hand-written model of lookup: `find_s hm k = slot_t_find_s k (index (hash_mod_key k (length slots)) slots)`, 77 trusted lines of such definitions. In Ochr it is stated with the lookup itself, run on a copy of the map:

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

The invariant is stated with the program's own index function and lookup too. "Every key lies only in the bucket that `Slot` returns for it" is:

```
def OnlyIn (s : Slots) (d : Word) (k : Word) : Prop by s := (
  match s {
    SOne(b) => ⊤,
    SCons(b, t) => match d {
      Zero => Nowhere(t, k),
      Succ(d') => Eq Opt (BFind(b, k)) None ∧ OnlyIn(t, d', k),
    },
  }
)

def Placed (s : Slots) (n : Word) : Prop := Π(k : Word). OnlyIn(s, Idx(k, n), k)
```

(b) *One theorem, bucket to map.* Insert, then look the key up, for one bucket: an induction on the bucket, with `match p {}` where the split has refined a hypothesis to `false = true`.

```
def BInsertFind (b : &Bucket) (k : Word) (v : Nat) :
    Id Opt (BInsert(&*b, k, v); BFind(*b, k)) (BInsert(&*b, k, v); Some(v)) by b := (
  match *b {
    BNil => (
      let e = EqB(k, k);
      match e {
        false => (
          let p = EqBRefl(k);
          match p {}
        ),
        true => refl,
      }
    ),
    BCons(k', v', t) => (
      let e = EqB(k', k);
      match e {
        false => BInsertFind(&t, k, v),
        true => refl,
      }
    ),
  }
)
```

It is lifted to the slots by recursion that follows `Slot`'s own, with no congruence step (the borrow of the tail keeps the other buckets in place). It is then stated for the map, splitting on the one sealed result the operation branches on:

```
def InsertFind (hm : &HashMap) (k : Word) (v : Nat) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
  match *hm {
    HM(n, len, slots) => split BInsert in SlotInsertFind(&slots, Idx(k, n), k, v),
  }
)
```

(c) *Dependent types in borrow-returning code.* `GetMut` returns a mutable borrow of a present key's value. The precondition is stated with the program's own lookup, and the impossible arm is ex falso:

```
def BGetMut (b : &Bucket) (k : Word) (h : IsSome(BFind(*b, k))) : &Nat by b := (
  match *b {
    BNil => match h {},
    BCons(k', v', t) => (
      let e = EqB(k', k);
      match e {
        false => BGetMut(&t, k, h),
        true => &v',
      }
    ),
  }
)
```

(d) *One operation specified by another.* Writing through `GetMut` is inserting the same key. Its theorems follow from insert's, where Aeneas relates its generated get_mut to a hand-written model of insert instead:

```
def GetMutIsInsert (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
    Id Unit (let q = GetMut(&*hm, k, h); *q := w) (InsertNoResize(&*hm, k, w))

def GetMutFind (hm : &HashMap) (k : Word) (w : Nat) (h : IsSome(Find(*hm, k))) :
    Id Opt (let q = GetMut(&*hm, k, h); *q := w; Find(*hm, k)) (let q = GetMut(&*hm, k, h); *q := w; Some(w)) := (
  rewrite ← GetMutIsInsert(&*hm, k, w, h) in InsertFind(&*hm, k, w)
)
```

(e) *The one `clone`.* Keys are `Word`s, so comparing and reusing them copies; the value is a `Nat`, so returning it while it stays in the bucket needs a copy:

```
def BGet (b : &Bucket) (k : Word) : Opt by b := (
  match *b {
    BNil => None,
    BCons(k', v', t) => (
      let e = EqB(k', k);
      match e {
        false => BGet(&t, k),
        true => Some(clone(v')),
      }
    ),
  }
)
```

**Caveats to state with the numbers.**
- Ochr's `Nat` has no overflow, so Aeneas's `Fail` cases and overflow bounds have no counterpart. That is roughly 3–5% of Aeneas's proofs.
- The slots are a list, not an array.
- The values are `Nat`, not generic.
- The load factor is fixed at 1.
- The first measurement predates D60 and D61, and the final one is checked with D53 (reads move), which the first was not. Both ends should be reported. Specifying get_mut by insert is a proof-structure change, not a language change; it saved 1.9k tokens of the 6.1k between the two ends.

## 9. Person-time

- **Aeneas** (paper, §6): 4 person-days by the tool's authors, for the 201-line implementation, with F* and Z3 and no interactive proof context. The paper reports no check times. The vendored 2022 F* files do not check with the F* available here (2026.05 dev: `FStar.Mul` no longer exists), so Aeneas's check time was not reproduced.
- **Ochr**, by an agent, in agent wall-clock time, which is not comparable to human person-days:
  - The v1.8 port took about 30 minutes: implementation plus the H1–H6 theorems for insert without resize and remove.
  - The v2.1 port took about 60 minutes: the port, the invariant, resize, the load factor, contains_key.
  - The second round took about 3 hours of agent time: get_mut after D58; D60 in the checker with its tests; the rewrite of the case study; get_mut by insert. Most of that time went to the checker work and the re-measurement.
  - The D53 round took about an hour: the probe, the `Word` conversion (mostly mechanical), `Nth`, the `clone` and its negative test, and the re-measurement. After the conversion, every proof was accepted unchanged.
  - Almost every theorem was accepted as first written. The exceptions are the motive capture, the nested zero-arm match, the `at` name, get_mut before D58, and one rewrite written in the wrong direction, all in §4 and §6.

## 10. Reproducing

```
cd ochr/core/lean
lake build Ochr.Examples.«17HashMap»          # the four blocks, verdict tables, count guards
lake exe tests                                  # all 1039, with per-declaration check times
lake env lean Ochr/Examples/CaseStudyLedger.lean   # §7 (slow: every rule switch re-checks the case study)
python3 ../notes/hashmap-count-ochr.py          # the Ochr column of §2 (final), and the statement share
# before D53: git show 0349532e:ochr/core/lean/Ochr/Examples/17HashMap.lean > /tmp/pre53.lean && python3 ../notes/hashmap-count-ochr.py /tmp/pre53.lean
# the earlier measurements: before D60 (07771cb6) and after D60 with direct get_mut (e53d8560)
git show 07771cb6:ochr/core/lean/Ochr/Examples/16HashMap.lean > /tmp/pre.lean && python3 ../notes/hashmap-count-ochr.py /tmp/pre.lean
python3 ../notes/hashmap-count.py fstar <Aeneas file> <ranges>   # Aeneas, ranges from ../notes/hashmap-aeneas-categories.py
```
