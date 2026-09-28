# Hashmap flagship: design (lead, fork "ochr-init-moonshot-hashmap")

Goal: an Aeneas-style resizing hash table written as in-place Ochr code, with the Aeneas hashmap theorems proved about that code (no pure model), inside the core calculus (RULES.md on `ochr-core`, v1.9 + D42) with NO new rules. Anything that needs something outside the core is a finding for the paper's frontier section, not a silent checker extension. Branch `ochr-hashmap`, worktree `/home/charlielidbury/repos/ochre-ochr-hashmap`. Do not edit RULES.md / DECISIONS.md (report to the lead, who forwards to the ochr-core session).

## Data

```
inductive Bool   := False | True
inductive Opt    := None | Some(v : Nat)
inductive Bucket := BNil | BCons(k : Nat, v : Nat, t : Bucket)       -- an association list
inductive Slots  := SOne(b : Bucket) | SCons(b : Bucket, t : Slots)  -- the slot "array": NON-EMPTY list of buckets
inductive HashMap := HM(n : Nat, len : Nat, slots : Slots)            -- n = number of slots − 1 (so Slots has S n elements), len = number of entries
```

Why non-empty slots and a saturating index: `NthM(s : &Slots, i : Nat) : &Bucket` is then total without a bounds proof (an index past the end returns the last bucket), so no ex-falso into a Type is needed in the core path. The index function keeps `i ≤ n` anyway.

The slot array is a linked list, so indexing is O(n): the verification story is exactly Aeneas's `Vec` with `index_mut` returning `&mut T` (a returned borrow whose backward function is "update at i"); a primitive O(1) array with the same interface is future work (it needs array computation rules for symbolic indices).

## Operations (sketch; the implementer fixes details)

```
EqB(a, b) : Bool, Lt(a, b) : Bool                          -- structural comparisons
Idx(k : Nat, n : Nat) : Nat                                -- slot index, e.g. k mod (S n) by structural recursion on k with a counter; the theorems must not depend on its definition beyond being a pure function
NthM(s : &Slots, i : Nat) : &Bucket by s                   -- index borrow (returned borrow)
Nth(s : Slots, i : Nat) : Bucket by s                      -- pure read, for statements if needed
BGet(b : &Bucket, k : Nat) : Opt by b                      -- lookup through a borrow (no copy of the structure)
BInsertM(b : &Bucket, k : Nat, v : Nat) : Bool by b        -- insert or overwrite in place; True iff a new entry was added
BRemoveM(b : &Bucket, k : Nat) : Bool by b                 -- remove in place; True iff something was removed
InsertNoResize(hm : &HashMap, k, v) : Unit                 -- r = NthM(&slots, Idx(k, n)); added = BInsertM(r, k, v); if added then len := S len
Get(hm : &HashMap, k) : Opt                                -- BGet(NthM(&slots, Idx(k, n)), k)
Remove(hm : &HashMap, k) : Unit                            -- BRemoveM; if removed then len := pred len
Count(s : Slots) : Nat, BLen(b : Bucket) : Nat             -- number of entries (pure)
EmptySlots(n) : Slots                                      -- S n empty buckets
MoveBucket(b : Bucket, hm : &HashMap), MoveSlots(s : Slots, hm : &HashMap)   -- re-insert every entry
Resize(hm : &HashMap) : Unit                               -- old = slots; *hm := HM(2n+1, 0, EmptySlots(2n+1)); MoveSlots(old, hm)
Insert(hm, k, v) : Unit                                    -- InsertNoResize; if Lt(n, len) (load factor 1, say) then Resize
GetMut(hm : &HashMap, k, h : <k present>) : &Nat           -- phase 2: needs ex falso into &Nat in the impossible arm (J with a Type-valued motive), or a different API; FINDING either way
```

## Theorems (Aeneas's hashmap suite, stated about the in-place code; idiom: `Id A (M; P) (M; Q)` states "after M, P equals Q")

Bucket level:
- H1 `BInsertGet`: `Id Opt (BInsertM(&*b, k, v); BGet(&*b, k)) (BInsertM(&*b, k, v); Some(v))`
- H2 `BInsertGetOther`: given `EqB(k2, k) = False`, `Id Opt (BInsertM(&*b, k, v); BGet(&*b, k2)) (let r = BGet(&*b, k2); BInsertM(&*b, k, v); r)`
- H2' remove analogues.

Slot level (the index borrow):
- H3 `NthWrite`: writing through `NthM(s, i)` then reading index `i` gives the written bucket; reading index `j` with `EqB(i, j) = False` (and both ≤ last) is unchanged.

Map level:
- H4 `InsertGet`, H5 `InsertGetOther` (case split on whether the two keys' indices coincide: same slot → H2, different slots → H3), for InsertNoResize first, then Insert.
- H6 the length invariant: `len = Count(slots)` is preserved by InsertNoResize and Remove (the in-place `len := S len` against the pure count).
- H7 (stretch) Resize preserves Get for every key.
- H8 (stretch) the key-placement invariant (every key sits in its slot), which H7 needs.

Each theorem is proved by structural recursion + J/cong where needed, with no pure model of the table. Report for each: accepted/rejected, the proof's shape (bare recursion? how many J steps?), and any rule gap.

## Deliverables

- `ochr/core/lean/Ochr/Examples/HashMap.lean` (program + theorems, verdict assertions with a count guard), registered in the build/registry like the other example files.
- `ochr/core/notes/hashmap-impl.md` (log, findings).
- Later: `ochr/core/paper/sections/hashmap.typ` (≤1.5 pages) for the ochr-core session to merge.
