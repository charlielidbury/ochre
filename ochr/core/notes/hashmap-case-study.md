# Hashmap case study: Ochr against Aeneas (ICFP 2022)

This note covers the paper's flagship case study. It reimplements the resizing hash map that Aeneas verifies (Ho and Protzenko, ICFP 2022, §6) as a single in-place Ochr program, and proves Aeneas's theorem suite about that program. It then measures both developments.

- Branch `ochr-hashmap-v2`, cut from `ochr-core` @ 96d788a1 (RULES v2.1, checker with D52).
- The code is `ochr/core/lean/Ochr/Examples/16HashMap.lean`.
- The counting scripts are `notes/hashmap-count.py`, used for both sides, and `notes/hashmap-count-ochr.py`, which assigns each Ochr declaration to a category.
- `notes/hashmap-aeneas-categories.py` maps every line of Aeneas's `Hashmap.Properties.fst` to a category.
- The earlier v1.8 port is on branch `ochr-hashmap`. `notes/hashmap-design.md` and `notes/hashmap-impl.md` are on that branch too; its findings F1–F3 are revisited below.

## Summary

**Status.** 182 declarations in four `ochr` blocks, 622/622 verdicts as expected across the whole suite.

**Implementation.** The implementation is Aeneas's, recursive as theirs is:
- new, clear, len, contains_key;
- get, get_mut, insert with resize, remove.

**What is proved.** The theorems are stated directly about the in-place operations. There is no model, no abstraction function and no refinement proof.
- Every lookup after every operation.
- The length field's evolution.
- The invariant (Aeneas's `hash_map_t_inv` less its overflow bounds), preserved by every operation. The invariant is: len = number of entries, keys distinct per bucket, and every key only in its own bucket.
- Resizing keeps the invariant, every lookup, and the length.
- The load factor is maintained.

**One wall: `get_mut`'s theorems.** They are written and true, but rejected, because of a gap in how unreachable arms normalise ("GetMut", below).

**Size.**
- **Aeneas** writes four things: a Rust program, a hand-written pure model, 459 lines of refinement lemmas linking Aeneas's generated translation to that model, and the property proofs.
- **Ochr** writes one program and the property proofs.
- **Tokens:** the two developments are the same size, 19.9k vs 19.7k hand-written tokens.
- **Lines:** Ochr's is 29% smaller, 1,892 vs 2,670 lines, but its lines are denser.
- **The model and refinement layers** are a quarter of Aeneas's tokens (4.7k), and they are gone in Ochr. So is the trusted translation.
- **Ochr's property proofs are longer than Aeneas's property proofs**, 17.1k vs 11.7k tokens. They have no automation: every case split and every rewrite (`J`) is written out. Each lemma is also stated three times, once per level (bucket, slots, map).

## 1. What was built

`16HashMap.lean`, four blocks, each `uses` the previous ones. Verdicts: all 182 as expected.

| Block | Contents | Decls | Check time (compiled, median of 21) |
|---|---|---|---|
| `HashMap` | the data; the implementation (31 declarations); 10 concrete runs (2 rejected on purpose) | 41 | 25 ms |
| `HashMapLookup` | what `Find` returns after insert, remove, get_mut, new and clear, for the touched key and any other key; `Get` and `ContainsKey` agree with `Find` and leave the map unchanged; 3 negative tests; 3 walled get_mut theorems | 38 | 48 ms |
| `HashMapLength` | the len field after insert, remove and get_mut; `len = Count(slots)` kept by insert, remove, new and clear; 1 negative test | 24 | 40 ms |
| `HashMapResize` | the invariant and its preservation; resizing keeps the invariant, every lookup and the length; insert with resize (all four of Aeneas's insert clauses); the load factor | 79 | 155 ms |

The check times are from `lake exe tests`, per own declaration, on a machine loaded by other agents. The whole case study checks in about 0.27 s.

**Build time.**
- `lake build` of the file takes about 30–40 s. It uses the interpreter, and each block re-checks the blocks it uses.
- The case study is registered as `Registry.caseStudies`. It is checked and counted with the tour (expected total 622) and timed by `lake exe tests`.
- It is kept out of the per-build counterfactual ledger: with it, each ledger row went from about 1.2 s to 5.8 s, and every row would also need its "blocked by" list asserted.
- Its ledger flips are measured once, by `Ochr/Examples/CaseStudyLedger.lean` (§7).

**The idiom.** A statement "after M, P equals Q" is `Id A (M; P) (M; Q)`. The key read in statements is `Find(m, k) := Get(&m, k)`, the in-place `Get` run on a copy, just as `Std`'s `Add` runs `AddM` on a copy. For example:

```
def InsertFindOther (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2)) (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r)
```

A proposition that holds after an operation is stated on a copy: `(let c = m; Insert(&c, k, v); Inv(c))`. The reason is D41: a type may not borrow the parameter itself (see §6).

## 2. The table

Counted with `hashmap-count.py`, the same for both sides:
- lines exclude blanks and comments;
- tokens are identifiers, numbers, common multi-character operators (one each) and every other non-space character.

For Ochr, only the text inside `ochr` blocks counts, split by declaration (`hashmap-count-ochr.py`). For Aeneas, `hashmap-aeneas-categories.py` assigns every line of `Hashmap.Properties.fst` to a category, and the categories were checked against a full reading of the file. `#push-options`/`#pop-options` lines are counted as boilerplate. Cells are lines / tokens.

| | Spec / model | Implementation | Agreement proof | Property proofs | Total, hand-written |
|---|---|---|---|---|---|
| **Aeneas** | 82 / 924 trusted views and invariant; + 239 / 2,039 proof-internal models | 201 / 1,484 Rust; + 9 / 39 hand-written termination measures | hand-written: 459 / 2,699 (generated function = hand-written model). Automatic but trusted: the translation, 550 / 2,882 generated F*, and 222 / 1,886 of `Primitives.fst` | 1,556 / 11,736, plus 124 / 780 of theorem statements in the `.fsti` | **2,670 / 19,701** |
| **Ochr** | 74 / 586 statement vocabulary; + 70 / 539 proof-internal definitions | 242 / 1,593 | **0** | 1,506 / 17,144 | **1,892 / 19,862** |

**Aeneas, in detail.**
- *Spec/model* is the trusted part: `find_s`, `len_s`, `hash_map_t_inv` and what they use (77 / 858), plus the `.fsti`'s 5 declarations. The proof-internal models are the pure versions of insert, resize and remove that the proofs route through (`hash_map_insert_in_list_s`, `move_elements_s`, `remove_s`, …).
- *Agreement* is the 19 refinement lemmas whose statement says a generated `hash_map_*_fwd/back` equals a hand-written model function (`--target model`).
- *Property proofs* are everything else in the proof file: 1,298 / 10,371. They also include the 5 lemmas that say a read-only operation returns the trusted view (`get` returns `find_s`, 258 / 1,365). Those are the specs of reads, and their Ochr counterparts (`GetFind`, `ContainsFind`, `RemoveResult`) are counted as property proofs too.
- Counting all 23 refinement-shaped lemmas as agreement instead gives 717 / 4,064 for agreement and 1,298 / 10,371 for properties.
- Aeneas's file contains dead code: 163 proof lines and 20 model lines are never used. Without it the Aeneas total is 2,487 / 18,175.
- Aeneas's `test1` (28 Rust lines) is excluded, as the paper excludes it.

**Ochr, in detail.**
- *Implementation* is the 31 definitions of the `HashMap` block, including `IsSome`, `BFind` and `Find`, which `GetMut`'s precondition uses.
- *Statement vocabulary* is what the headline theorems' statements mention: `Count`, `BLen`, `Buckets`, `IfNew`, `Shrink`, `Has`, `Unique`, `AllUnique`, `Nowhere`, `OnlyIn`, `Placed`, `Inv`, `NOf`, `NotOver`.
- *Proof-internal definitions*: `Nth`, `IsNone`, `IfFound`, `OrElse`, `BFindLast`, `SFindLast`, `Fresh`, `FreshS`, `AbsentFrom`, `Apart`, `GUnique`.
- Excluded from the Ochr total:
  - the 10 runs (68 / 712);
  - the 3 negative tests (25 / 289);
  - the 3 walled `GetMut` theorems (53 / 548).
- The `GetMut` part that is not written (the map-level lifts, and invariant preservation) would add about 150 lines by analogy with insert.

**Property proofs by operation** (lines / tokens). The Aeneas column is property proofs as defined above: prop plus view-refinement. Its model-refinement agreement lemmas are shown separately in brackets.

| | Aeneas | Ochr |
|---|---|---|
| insert, bucket level and without resize | 300 / 2,358 [+ 151 / 887] | 344 / 4,075 |
| resize, and insert with resize | 485 / 3,496 [+ 137 / 854] | 497 / 5,799 |
| load factor | 33 / 318 | 99 / 969 |
| remove | 139 / 847 [+ 109 / 572] | 343 / 3,777 |
| get, contains_key | 104 / 548 | 54 / 547 |
| get_mut | 78 / 439 [+ 62 / 386] | 6 / 111 (+ 53 / 548 walled) |
| new, clear, len | 150 / 977 | 58 / 647 |
| helpers (lists, arithmetic, keys, equality) | 267 / 2,753 | 105 / 1,219 |
| **total** | 1,556 / 11,736 [+ 459 / 2,699] | 1,506 / 17,144 |

- Ochr's remove proves more than Aeneas's: the invariant after remove, including placement. Aeneas's statement does not claim it (§3).
- Ochr's load factor needs the bucket count after a resize, which is a sealed program (`ResizeN`, via `InsertN`/`MoveBucketN`/`MoveSlotsN`).
- Aeneas's get_mut is fully covered; Ochr's is walled (§4).

**Reading the table.**
- **Totals.** The totals are equal in tokens (19.9k against 19.7k) and 29% apart in lines. Ochr's lines carry more tokens each, because statements with `Id` are long.
- **What Ochr does not write.** It writes no model and no agreement proof. In Aeneas those are 698 / 4,738 (models plus model refinement), a quarter of the hand-written tokens. It is nearly a third if the read-operation lemmas are counted as agreement. Ochr also trusts no translation: Aeneas's 550 generated lines and its `Primitives` are trusted.
- **What Ochr spends instead.** Its property proofs are 1.5 times Aeneas's in tokens (17.1k against 11.7k), for three reasons:
  - there is no automation, where Aeneas has Z3 with fuel and `rlimit` tuning: 56 `#push-options` and 183 `assert` lines;
  - each rewrite is a `J` with an explicit motive, 35 of them;
  - each lemma is stated at three levels.

  §6 says which features would shrink this.

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
| `hash_map_get_mut_fwd_lem` | the borrow's value is `find_s k` | **Wall.** `BGetMutRead` (bucket level) is written and true, but rejected (§4). The map-level statement is not written. |
| `hash_map_get_mut_back_lem` | after writing: inv, len unchanged, key ↦ new value, others unchanged | **Wall** for key ↦ new value and others unchanged: `BGetMutFind` and `BGetMutFindOther` are rejected. `GetMutLen` (len unchanged) is accepted. The inv part is not written; its bucket lemmas would hit the same wall. |
| `hash_map_remove_fwd_lem` | returns `find_s k` | `RemoveResult`: `Remove(&*hm, k)` returns what `Find(*hm, k)` returned. |
| `hash_map_remove_back_lem` | key gone; others unchanged; len − 1 iff present; "inv" | `RemoveFind` (needs only the per-bucket uniqueness part of the invariant), `RemoveFindOther`, `RemoveLen` (len' = `Pred(len)` iff found, which is what the code does, unconditionally), `RemoveCount`, `RemoveInv`. |

**Aeneas's `remove_back` statement is misstated.** The census of the Aeneas artifact confirmed this, lines .fsti 255 and .fst 3229. `hash_map_remove_back_lem` ensures `hash_map_t_inv self`, the precondition, not the invariant of the result. The .fst does not prove the stronger statement either. So in Aeneas no operation can be verified after a `remove`, because they all require the invariant. The paper's `test1` sequence (insert ×4, get, get_mut, remove, get ×3) is checked only by evaluation, via `assert_norm`. Ochr's `RemoveInv` proves that the invariant is kept.

**Proved in Ochr with no Aeneas counterpart:**
- `GetFind` and `ContainsFind` show that the reads leave the map unchanged. Aeneas's reads are pure functions, so there is nothing to prove there.
- `ResizeInv` holds with **no** hypothesis on the old map.
- The negative tests show that the hypotheses are needed and the splits are necessary: `InsertFindNoSplit`, `BRemoveFindDup`, `InsertCountNoHyp`.

**Aeneas's resize lemmas.** They are internal to the insert proof (`try_resize_fwd_back_lem`, `move_elements_fwd_back_lem`), 549 lines. Ochr's `MoveBucketInv` … `ResizeLen` cover the same ground (§2).

## 4. The wall: GetMut

`GetMut(hm, k, h : IsSome(Find(*hm, k))) : &Nat` takes a proof that the key is present.

**Why it takes a proof.** Rust's `get_mut` returns `Option<&mut V>`, which Ochr cannot express: D48 allows no borrows inside data. Aeneas's version panics instead.

**The impossible arm.** At the end of a bucket, `BGetMut`'s `BNil` arm is impossible. There `h : IsSome(None)`, which is `False`, and the arm is `match h {}`. The v1.8 port did ex falso into `&Nat` by `J` with a `Type`-valued motive instead, which D48 (2) now forbids. `GetMut` is accepted, and so are the concrete runs: `RunGetMut` writes through the borrow and reads back 55, and `RunGetMutAbsent` is rejected because its precondition computes to `False`.

**What fails.** Every theorem about writing through the borrow is rejected: `BGetMutRead`, `BGetMutFind`, `BGetMutFindOther`. They are proved by recursion on the bucket, and in the `BNil` arm the checker re-normalises the goal after the split `σ := BNil`. That runs `BGetMut` into its unreachable `match h {}`. D49 (5) gives that match the value `⋆` at every type, including `&Nat`. The goal then reads `*q` from `⋆`, which is a normalisation error, and D29 makes a normalisation error a type error. All of this happens before the arm's own `match h {}` could discharge the goal.

Minimal program (reported to the team lead):

```
def IsZ (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
def G (x : &Nat) (h : IsZ(*x)) : &Nat := match *x { Z => x, S _ => match h {} }
def T (x : &Nat) (h : IsZ(*x)) : Id Nat (let q = G(&*x, h); *q) 0 := match *x { Z => refl, S _ => match h {} }
-- T: rejected, "no such place *r: its path does not exist in ⋆"
```

**Suggested fix.** In untyped runs (normalisation), a zero-arm match is *stuck*: the enclosing call stays a sealed program, rather than yielding `⋆`.
- It changes no closed result, because the arm is unreachable in every closed run.
- An open goal simply stays neutral, and the arm's `match h {}` fits it.

With that fix, the three written theorems should go through as they stand. Their bodies are the same bare recursion as `BInsertFind`'s. Lifting them to the map is the same pattern as for insert: three more slot lemmas and three map theorems, plus the invariant parts, about 150 lines by analogy. No workaround keeps `GetMut`'s signature: the goal must be well-formed in every arm the split produces. A bucket with a dummy value in `BNil` would avoid the ex falso; it was not done, because it would change the data structure to suit the checker.

## 5. Divergences

- **Numbers.** `Nat` is unbounded, so there are no overflow obligations, no `Fail` cases and no saturation.
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
- **Reads.** The current checker copies data on reads. Under D53 (runtime reads move, `clone` explicit), the implementation would need `clone` wherever a `Nat` is read and still needed:
  - the key comparisons `EqB(k', k)` in the five bucket functions (the stored key, and the parameter `k`, which is reused in the recursive call);
  - `Some(v')` in `BGet`;
  - `Idx(k, n)` in the five map operations (`n` is a field; `k` is reused);
  - `Lt(n, len)` in `Insert`.

  Rust needs none of these because `usize` is `Copy`. A fixed-width key type that is a copy type (D53) would remove them all. `let old = slots` in `Resize`, `*b := t` in `BRemove`, and `len := S len` / `len := Pred(len)` are moves that D53 accepts as written. The proofs are unaffected: they are erased, so their reads copy, and so are the statements' `Find(*hm, k)`.
- **Tests.** Aeneas's `test1` is 28 Rust lines, excluded from their 201. Ochr's ten runs, 68 lines, are excluded from its implementation count.

## 6. Findings about the language

### What v2.x fixed, measured against the v1.8 port

The v1.8 port had 105 declarations, 11.3k tokens, and covered insert without resize and remove. The same theorem chains, measured in tokens (definitions and helper lemmas included):

| Chain | v1.8 | v2.1 | Why |
|---|---|---|---|
| H5, insert leaves another key's lookup | 1,720 | 960 | F1' is gone (below); `EqBContra` replaces `ExFalsoFT`/`BoolAbsurd` |
| H4, insert then lookup | 617 | 495 | `match p {}` on a refined `false = true` replaces `ExFalsoFT` |
| H1', remove then lookup | 413 | 217 | ∧-elimination (`match h { Intro(a, r) => … }`) lets the invariant be the natural "keys distinct" (`Unique`), instead of the query-indexed `AtMostOnce`/`BAbsent` pair |

- **False, and matching on it** (D45, D47). `Eq Bool false true` computes to `False`, so every "impossible" arm is `match h {}` on a hypothesis whose type the split refined.
  - v1.8 needed `ExFalso`/`ExFalsoFT`/`BoolAbsurd`, each a `J` with a crafted motive.
  - Now there are 38 zero-arm matches and no ex-falso lemma.
  - `EqBContra` ("a stored key equal to both `k` and `k2` contradicts `k ≠ k2`") is two splits and two `match _ {}`.
- **Taking And apart** (D45). There are 39 `Intro(…)` matches: the invariant's three parts, the slots' per-bucket facts, and the recursive hypotheses.
  - v1.8 had no ∧-elimination, so a lemma whose type carried a conjunct could be used only where the goal carried the same conjunct. That made F1 expensive.
  - Now proofs take hypotheses apart freely.
- **Injectivity** (D52). `S a = S b` is `a = b`. So:
  - `EqBSound`'s successor case is the recursive call as it stands, where v1.8 needed one `J`.
  - Each arm of `BInsertCount`/`BRemoveCount` is the induction hypothesis as it stands.
  - `AddAssoc` is bare recursion.
  - No congruence lemma for `S` is needed anywhere. The congruence lemmas that remain are for `Add` and `Opt` positions (`TransO`, the `J`s under `Add`), which injectivity does not cover.
- **F1 now, reading through a mutable borrow.** Statements read with `Find(*hm, k)`, which is `Get` on a copy. The read leaves no residue in the observed map, so every statement computes to the single interesting equation. The consequences:
  - The v1.8 statements carried a bucket conjunct, which forced "call the lemma on a copy" workarounds.
  - F1' is gone. H5's right-hand side, the lookup and then the insert, is now the same sealed insert as the left's. The proof has one split instead of four arms, and needs no `NthInsertAfterGet` lemma pair.
  - What F1 still costs is the link between the in-place reads and the copies: `GetFind` and `ContainsFind`, each a bucket, a slot and a map lemma of bare recursion. Together that is 6 declarations, 54 lines, 547 tokens: 3% of the proofs.
  - With shared borrows, `Find` would be `Get` itself and these six lemmas would go.

### What was awkward, and what would fix it

- **Reproducing a sealed result to split on it.** The operations branch on a sealed result: the `added` flag, the removed value, the `full` test. A map-level proof re-runs the relevant part on a copy of the slots (`let c = slots; let b = Slot(&c, Idx(k, n)); let added = BInsert(b, k, v);`) and splits on it. Then the goal computes, and D34 carries the split into the goal's own copy of the program.
  - This happens 31 times, at 3–4 lines each, and the arms of the split are usually identical.
  - `InsertFindNoSplit` (rejected) shows that it is necessary.
  - A form that splits the goal on a named sealed subterm would remove it. That would be like Lean's `split` or `cases h : e`, or a `match` on a term, not a place, that records the equation.
- **Rewriting with J.** There are 35 `J`s, each with an explicit motive `λ(z : T) : Prop => …` that restates the goal around the hole. There are also 27 uses of the small combinators `TransO`, `TransN` and `SymmN`, which exist only to orient `J`.
  - `MoveBucketLen`'s cons arm is 7 lines of `J`/`TransN`/`SymmN` for "rewrite `Len(m2)` to `S (Len(m))`, then use `x + S y = S (x + y)`".
  - A `rewrite h in e` or `calc` form (the motive inferred from occurrences) would cut most of these to one line each. This is the largest single source of Ochr's extra tokens.
- **Stating each lemma three times.** Each bucket theorem is lifted through `Slot` by recursion on the slots, and then stated for the map. The recursion is 6–10 lines and needs no insight, but the statement is restated each time.
  - 14 `Slot…` lemmas repeat their bucket lemma's statement, with `Slot(&*s, i)`/`Nth(*s, i)` in place of the bucket, and so do the slot-level `Nowhere…`/`OnlyIn…` lemmas.
  - This is the price of the environment doing the congruence (no `J` in the lifts). A generic "lift through the index borrow" lemma would need quantification over programs, which Ochr does not have.
- **Destructuring.** The invariant has three parts, so every use is `match h { Intro(hl, hr) => match hr { Intro(hu, hp) => … } }`, two levels deep before any work. A destructuring `let ⟨hl, hu, hp⟩ = h;` would flatten this. The three-part invariant is taken apart this way 4 times, and there are 39 `Intro` matches in all.
- **Postconditions on a copy** (D41). A proposition about the state after an operation can only be a type that runs the operation on a local copy: `(let c = m; Insert(&c, k, v); Inv(c))`. D41 rejects `(BInsert(&*b, k, v); Unique(*b))`, because a type may not borrow a place that outlives it. `Id` is the exception.
  - So the case study has two statement styles: `Id` statements over a borrowed parameter (lookups, lengths) and propositions over a value parameter (the invariant). The two meet through calls on local copies, for example `InsertCount(&mc, …)` inside `InsertInv`.
  - This is sound and it works, but a reader must learn both styles.
- **Motives cannot mention a place under a borrow.** `J`'s motive is a type, and a type may not capture a borrow. So `λ(z) : Prop => Eq Opt (BFind(t, z)) None`, where `t` is a pattern variable under the borrow `b`, is rejected: "captures the borrow b". Copying first (`let c = t;`) fixes it. This came up once.
- **Zero-arm matches outside tail position.** A `match h {}` nested inside a non-tail `let x : T = match …` still asks for an annotation, because the expected type does not reach the inner match. `HeadApart` was split out as a lemma to put the match in tail position.
- **Small things.**
  - `at` is not a usable variable name (it is a Lean keyword).
  - Proofs that mutate their own locals and then call lemmas about them (`let m2 = m; InsertNoResize(&m2, k, v); MoveBucketInv(t, m2, InsertInv(m, k, v, h))`) read naturally and are allowed. They were the key to `MoveBucketInv`/`MoveBucketFind`/`MoveBucketLen`, whose induction hypothesis is about the map after one insert.

### Quantifying over every key was not a wall

The task named "anything needing ∀ over keys" as a candidate wall. It was not one.
- Placement is `Placed(s, n) = Π(k : Nat). OnlyIn(s, Idx(k, n), k)`. It is proved by `λ(k2 : Nat) : OnlyIn(c, Idx(k2, n), k2) => …`, with a split on `EqB(k, k2)` inside the λ and a `J` along `k = k2`. It is used by applying it: `hp(k)`.
- Deriving global key uniqueness from placement (`GUniqueOf`, for `ResizeLen`) takes the bucket-index function as a parameter, `D : Π(k : Nat). Nat`. The tail's hypothesis is then `Π(k). OnlyIn(t, Pred(D(k)), k)`.
- It also passes a proof-valued function, `Π(k : Nat) (nw : Nowhere(t, k)). Eq Opt (BFind(cur, k)) None` ("this bucket is part of `t`").
- Every one of these was accepted as first written.

The task also named resize correctness as a candidate wall. `ResizeInv`, `ResizeFind` and `ResizeLen` hold, and the whole resize and insert-with-resize section is 497 lines. Aeneas spends 549 lines on the same ground.

## 7. Which rules the case study depends on

(Measurement running: `lake env lean Ochr/Examples/CaseStudyLedger.lean`. Results to follow in the next commit.)

## 8. For the paper: a one-page summary

**The claim tested.** In the two-program setups (Aeneas, and likewise ATS, Low*, VeriFast), a verified program is three artefacts: an efficient implementation, a pure specification or model, and a proof that the two agree. Properties are then proved about the model. In Ochr it is one artefact: the in-place program, with theorems stated and proved about that program.

**The case study.** Aeneas's resizing hash map, the ICFP 2022 flagship, written once in Ochr: 31 definitions, 242 lines. It covers:
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
- **Coverage.** Everything is covered except get_mut's theorems, which hit a rules gap (below). Everything else is 179 accepted declarations.
- **Size.** 1,892 lines / 19.9k tokens by hand, against Aeneas's 2,670 lines / 19.7k tokens: the same in tokens, 29% smaller in lines.
- **Where the size goes.** Aeneas's pure model and its refinement lemmas are a quarter of its hand-written tokens, and they have no counterpart in Ochr. What Ochr spends instead is proof text without automation: explicit case splits and `J` rewrites. Aeneas has Z3 for those.
- **Check time.** The case study checks in about 0.3 s.

**One thing Ochr proves that Aeneas's interface does not.** Aeneas's `remove` lemma states the invariant of its *input* (a slip), so no Aeneas client can call an operation after a `remove`. Ochr's `RemoveInv` is about the result.

**Suggested excerpts.**

(a) *The program is its own specification.* In Aeneas, "other keys are unchanged" is stated about `find_s`, a hand-written model of lookup: `find_s hm k = slot_t_find_s k (index (hash_mod_key k (length slots)) slots)`, 77 trusted lines of such definitions. In Ochr it is stated with the lookup itself, run on a copy of the map:

```
def InsertFindOther (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat) (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2)) (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r)
```

The invariant is stated with the program's own index function and lookup too. "Every key lies only in the bucket that `Slot` returns for it" is:

```
def OnlyIn (s : Slots) (d : Nat) (k : Nat) : Prop by s := (
  match s {
    SOne(b) => ⊤,
    SCons(b, t) => match d {
      Z => Nowhere(t, k),
      S d' => Eq Opt (BFind(b, k)) None ∧ OnlyIn(t, d', k),
    },
  }
)

def Placed (s : Slots) (n : Nat) : Prop := Π(k : Nat). OnlyIn(s, Idx(k, n), k)
```

(b) *One theorem, bucket to map.* Insert, then look the key up, for one bucket: an induction on the bucket, with `match p {}` where the split has refined a hypothesis to `false = true`.

```
def BInsertFind (b : &Bucket) (k : Nat) (v : Nat) :
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
def InsertFind (hm : &HashMap) (k : Nat) (v : Nat) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k)) (InsertNoResize(&*hm, k, v); Some(v)) := (
  match *hm {
    HM(n, len, slots) => (
      let c = slots;
      let b = Slot(&c, Idx(k, n));
      let added = BInsert(b, k, v);
      match added {
        false => SlotInsertFind(&slots, Idx(k, n), k, v),
        true => SlotInsertFind(&slots, Idx(k, n), k, v),
      }
    ),
  }
)
```

(c) *Dependent types in borrow-returning code* (the function checks; its theorems wait on the fix in §4). `GetMut` returns a mutable borrow of a present key's value. The precondition is stated with the program's own lookup, and the impossible arm is ex falso:

```
def BGetMut (b : &Bucket) (k : Nat) (h : IsSome(BFind(*b, k))) : &Nat by b := (
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

**Caveats to state with the numbers.**
- Ochr's `Nat` has no overflow, so Aeneas's `Fail` cases and overflow bounds have no counterpart. That is roughly 3–5% of Aeneas's proofs.
- The slots are a list, not an array.
- The values are `Nat`, not generic.
- The load factor is fixed at 1.
- The get_mut theorems wait on the rules fix in §4.

## 9. Person-time

- **Aeneas** (paper, §6): 4 person-days by the tool's authors, for the 201-line implementation, with F* and Z3 and no interactive proof context. The paper reports no check times. The vendored 2022 F* files do not check with the F* available here (2026.05 dev: `FStar.Mul` no longer exists), so Aeneas's check time was not reproduced.
- **Ochr**, by an agent, in agent wall-clock time, which is not comparable to human person-days:
  - The v1.8 port took about 30 minutes: implementation plus the H1–H6 theorems for insert without resize and remove.
  - The v2.1 work in this note took about 60 minutes: the port, the invariant, resize, the load factor, contains_key.
  - Almost every theorem was accepted as first written. The exceptions are the motive capture, the nested zero-arm match, the `at` name, and the get_mut wall, all in §6 and §4.

## 10. Reproducing

```
cd ochr/core/lean
lake build Ochr.Examples.«16HashMap»          # the four blocks, verdict tables, count guards
lake exe tests                                  # all 622, with per-declaration check times
lake env lean Ochr/Examples/CaseStudyLedger.lean   # §7 (slow: every rule switch re-checks the case study)
python3 ../notes/hashmap-count-ochr.py          # the Ochr column of §2
python3 ../notes/hashmap-count.py fstar <Aeneas file> <ranges>   # Aeneas, ranges from ../notes/hashmap-aeneas-categories.py
```
