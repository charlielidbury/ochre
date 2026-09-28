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
