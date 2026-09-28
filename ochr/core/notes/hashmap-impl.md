# Hashmap flagship: implementation log (agent: hashmap implementer)

Spec: `notes/hashmap-design.md`. Code: `ochr/core/lean/Ochr/Examples/HashMap.lean` (one `ochr HashMap { … }` block, registered in `Registry.lean`). Checker: RULES v1.8 + D42 (the checker on `ochr-hashmap` at 861a6a40); no rule or `Machine.lean` change.

(5-line summary goes here at the end.)

## Phase 1: data types and operations (all accepted)

Data exactly as the spec: `Bool`, `Opt`, `Bucket` (association list), `Slots` (non-empty list of buckets), `HashMap := HM(n, len, slots)`.

| Operation | Shape | Check time (compiled) |
|---|---|---|
| `EqB`, `Lt` | structural on the first argument | 52, 27 µs |
| `ModGo(k, n, r)`, `Idx(k, n) := ModGo(k, n, 0)` | k mod (S n), structural on k with a running remainder; dispatches on `EqB(r, n)` | 62, 13 µs |
| `NthM(s : &Slots, i) : &Bucket by s` | the index borrow; saturates at the last slot | 45 µs |
| `Nth(s, i)` | pure read | 27 µs |
| `BGet(b : &Bucket, k) : Opt by b` | lookup through the borrow | 55 µs |
| `BInsertM(b, k, v) : Bool by b` | overwrite in place, or append at the end; `True` iff added | 65 µs |
| `BRemoveM(b, k) : Bool by b` | `*b := t` at the key; `True` iff removed | 51 µs |
| `InsertNoResize(hm, k, v)` | `r = NthM(&slots, Idx(k, n)); added = BInsertM(r, k, v); if added then len := S len` | 142 µs |
| `Get(hm, k)`, `Remove(hm, k)` | through `NthM` | 53, 122 µs |
| `BLen`, `Count` | pure sizes (`Count` sums with `Add`) | 19, 42 µs |
| `EmptySlots(n)`, `New(n)` | `S n` empty buckets | 19, 13 µs |
| `MoveBucket(b, hm)`, `MoveSlots(s, hm)` | re-insert every entry with `InsertNoResize`, structural on the moved-out data | 40, 40 µs |
| `Resize(hm)` | `old = slots; *hm := New(S (n + n)); MoveSlots(old, hm)` (doubles the slot count) | 60 µs |
| `Insert(hm, k, v)` | `InsertNoResize`, then `Resize` if `Lt(n, len)` (load factor 1) | 110 µs |

Everything was accepted as first written. Things worth noting:
- `NthM` returns `&b`, a borrow of a field of the borrowed slot list (a reborrow), in both arms; the recursion `NthM(&t, i')` is the TailM pattern. No bounds proof anywhere.
- `Resize` assigns `*hm` inside the arm of a `match *hm` whose pattern variables alias `(*hm).slots` (the copy `old = slots` is taken first). Fine: pattern variables are places, not borrows.
- `Insert` matches on `*hm` again after `InsertNoResize(&*hm, …)` and reborrows `&*hm` inside that arm for `Resize`.

Concrete runs (12, as `Id … := refl` over closed programs; 1 rejected on purpose): three inserts into a 2-slot table, the second reaching the load factor and resizing to 4 slots (`RunLayout` checks the exact final table `HM(3, 3, [∅, [1↦10], [2↦20], [3↦30]])`); each key is found (`RunGet1..3`), an absent one is not, a wrong value is rejected (`RunGetWrong`: "the goal is Eq Opt Some(10) Some(20)"); overwrite keeps `len`; a colliding key shares a bucket (`RunCollide`); remove (present and absent) and get-after-remove; and `len = Count(slots)` after a mixed run of five operations (`RunCount`). The runs take 0.4–0.9 ms each; `RunCount` 4.8 ms (two full runs plus `Count`).

Ledger: switching off generalise-then-split (C8) rejects every definition that dispatches on `EqB`/`Lt` (their results are sealed at the generic call) and every run built on them: 23 flips, asserted in `Registry.lean` as `hashMapGeneralize`. No other ledger row flips on the hashmap.

## Phase 2: bucket-level theorems (all accepted)

| Theorem | Statement (`b : &Bucket`) | Verdict | Proof shape | Time |
|---|---|---|---|---|
| H1 `BInsertGet` | `Id Opt (BInsertM(&*b,k,v); BGet(&*b,k)) (BInsertM(&*b,k,v); Some(v))` | accepted | recursion on `*b`; BNil: split on `EqB(k,k)`, the False arm by `ExFalsoFT(goal, EqBRefl(k))`; BCons: split on `EqB(k',k)`, False = IH, True = `refl`. 0 J steps (1 inside `ExFalsoFT`) | 1.6 ms |
| H2 `BInsertGetOther` | given `h : Id Bool (EqB(k,k2)) False`: `Id Opt (BInsertM(&*b,k,v); BGet(&*b,k2)) (let r = BGet(&*b,k2); BInsertM(&*b,k,v); r)` | accepted | recursion; 2 nested `EqB` splits per cons cell; IH in one arm, `refl` in two, ex falso in two (`BoolAbsurd`, and `EqBTrans` for "k' = k and k' = k2 but k ≠ k2") | 3.5 ms |
| H1' `BRemoveGet` | given `h : AtMostOnce(*b, k)`: `Id Opt (BRemoveM(&*b,k); BGet(&*b,k)) (BRemoveM(&*b,k); None)` | accepted | recursion; found arm = `let c = t; BGetAbsent(&c, k, h)` (a lemma on a copy of the tail) | 1.2 ms |
| H2' `BRemoveGetOther` | given `k ≠ k2`: as H2 with `BRemoveM` | accepted | as H2 | 2.6 ms |

Helpers (all accepted): `ExFalso` (E5's), `ExFalsoFT(G, h : Eq Bool False True) : G` and `BoolAbsurd(x, x = False, x = True)` by one J each; `EqBRefl` by bare recursion; `EqBSound : EqB(a,b) = True → a = b` by recursion with one J (congruence under `S`: D16 removed Nat injectivity, so `Eq Nat (S a) (S b)` does not reduce); `EqBTrans` by one J; `BAbsent(b, k)`, `AtMostOnce(b, k) : Prop` (Le-style Prop-valued recursion that dispatches on `EqB`); `BGetAbsent : BAbsent(*b,k) → Id Opt (BGet(&*b,k)) None` by recursion.

Negative tests (rejected, reasons checked): `BInsertGetNoLemma` (BNil arm by `refl`: the goal still holds `⌈…BGet(&c1, σ1)⌉` stuck on `EqB(σ1, σ1)`), `BInsertGetWrongValue` (`Some(k)`: goal `Eq Opt Some(σ2) Some(σ1)`), `BInsertGetOtherNoHyp` (goal `Eq Opt Some(σ2) None` in the k = k2 arm), `BRemoveGetNoHyp` (duplicate keys: `⌈BGet(σ4, σ1)⌉` vs `None`).

**Finding F1 (a read through `&T` is only propositionally the identity).** `BGet(b : &Bucket, k)` reads through a mutable borrow (the core has no shared borrows). When it gets stuck on an abstract tail, [Close] fills the borrowed place with the backward program `⌈let c1 = u; BGet(&c1, k); c1⌉`, which is semantically `u` but not definitionally. So every statement whose one side reads with `BGet` and whose other does not has a second conjunct about the bucket, e.g. H1's goal is `Eq Opt ⌈…BGet…⌉ Some(v) ∧ Eq Bucket ⌈…BGet(&c1, k); c1⌉ ⌈…⌉` (trace above). The theorems as stated are therefore *stronger* than Aeneas's (they also say that the lookup leaves the bucket as it was), and this is harmless for H1–H2' because the proofs are bare recursion: the IH carries the same conjunct and the base cases compute it away. It costs where lemmas are composed: the core has no ∧-elimination (a proof of `P ∧ Q` cannot be projected: no neutral projections, and J cannot do it), so a lemma whose type carries the residue conjunct can only be used where the goal carries the same conjunct. Two techniques keep it usable, both used below: (a) call the lemma on a *copy* the proof owns (`let c = t; BGetAbsent(&c, k, h)`), so its footprint is exactly the place the goal observes, not the enclosing cell; (b) lift the lemma by recursion through the enclosing structure, so the environment performs the congruence (next phases).

**Ledger.** Switching G1 off (a generalised sealed program stays generalised when re-derived) rejects all five bucket theorems (`hashMapG1` in Registry.lean): the proofs split on `EqB(k', k)` in the proof body, and the goal's sealed programs re-derive that comparison inside `BInsertM`/`BGet`/`BRemoveM`. Switching generalise-then-split (C8) off rejects every hashmap declaration that dispatches on `EqB` (30).

Build: the full `lake build` went from 26 s to 68 s, because each of the 30 ledger rows re-checks the hashmap twice in the interpreter (about 0.3 s per check).
