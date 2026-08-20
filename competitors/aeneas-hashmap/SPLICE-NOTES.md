# The allocation-free resize, spliced into the Aeneas hashmap

The DLLBC hashmap flagship landed a resize that performs exactly **one**
allocation — the new slots array — moving every bucket node by pointer
relinking rather than rebuilding it (main `6dd226a1`, see the docstring of
`dllbc/Dllbc/Tests/HashMap.lean`). The vendored Aeneas reference allocates a
fresh `Box` per moved entry. This directory now carries both shapes of the same
Rust program so the comparison is a measurement rather than a claim.

## Layout, and why the vendored file was not edited in place

- `current/hashmap.rs` — **unmodified upstream**, exactly as vendored on
  2026-08-17 from the Aeneas repo's `main` (`daa85d7e…`).
- `splice/hashmap.rs` — the same file with one function body replaced.
- `rust-check/` — a cargo package that compiles *both of those files* via
  `#[path]` module declarations and measures them side by side.

Editing `current/hashmap.rs` in place would have preserved the original in git
history, which is what the repo normally prefers. Two things argued the other
way and won. First, `current/` is a vendored artifact whose stated purpose in
`README.md` is that it "cannot drift or disappear upstream"; a local edit makes
`git diff` against upstream stop meaning what it says. Second, and decisively,
both deliverables want the two versions *simultaneously*: the allocation test
measures them in one process on one op stream, and the translation experiment
translates both and diffs the output. `diff -u current/hashmap.rs
splice/hashmap.rs` is the whole change and is 8 statements long.

The `rust-check` crate includes the two files by path rather than copying them,
so the source that is measured and the source that is read cannot diverge.

## The change

Upstream moves an entry by re-inserting it:

```rust
AList::Cons(k, v, tl) => {
    ntable.insert_no_resize(k, v);   // walks the destination bucket,
    ls = *tl;                        // ends at Box::new(AList::Nil)
}
```

The splice moves an entry by relinking it, reusing the box the node already
owns as the link to whatever the destination bucket used to hold:

```rust
AList::Cons(k, v, mut tl) => {
    let hash = hash_key(&k);
    let hash_mod = hash % ntable.slots.len();
    let dst = &mut ntable.slots[hash_mod];
    let dst_head = std::mem::replace(dst, AList::Nil);
    let rest = std::mem::replace(&mut *tl, dst_head);
    *dst = AList::Cons(k, v, tl);
    ntable.num_entries += 1;
    ls = rest;
}
```

100% safe Rust, no new dependencies, no `unsafe`, no change to any other
function. Three enum-sized writes per entry, no allocation and no drop. Two
consequences, both argued in the function's docstring in `splice/hashmap.rs`:

- **Duplicate keys need no handling.** `insert_no_resize` walks the destination
  bucket so an existing key is overwritten rather than duplicated. During a
  resize every key in the source table is distinct and the destination starts
  empty, so that walk always runs to `Nil`. Dropping it is what makes moving an
  entry O(1) instead of O(destination bucket length).
- **Bucket order changes**: moved entries prepend where they used to append, so
  same-slot survivors of a resize come out in reverse relative order. Keys are
  distinct and every lookup scans the whole bucket, so nothing observable
  through `get`/`get_mut`/`contains_key`/`remove`/`len` changes. This is the
  same trade the DLLBC version makes, where the spec (`FindL` + `NodupB`) is
  deliberately blind to bucket order.

## Measured allocation counts

`rust-check` installs a counting `#[global_allocator]` and classifies every
allocation by requested size. `try_resize` is private, so the measurement is
taken around the single `insert` call that crosses the load threshold — that
call performs one ordinary insertion and then the whole resize. Sizes separate
the two contributions cleanly: a bucket node is `size_of::<AList<u64>>()` = **24
bytes** (`Box`'s niche absorbs the discriminant, so a node is key + value +
pointer with no tag word), while the slots vector allocations are
`capacity * 24` bytes and appear as a doubling chain 96, 192, 384, … as
`allocate_slots` pushes.

Reproduce with:

```
cd competitors/aeneas-hashmap/rust-check
cargo test -- --nocapture --test-threads=1
```

### Per resize (`tests/alloc_counts.rs::resize_allocations`)

Counts are for the whole triggering `insert`. "node allocs" is allocations of
exactly 24 bytes; subtract 1 from it for the entry that insert legitimately adds
to get the cost of the *move*. Identical numbers were measured for a key set
where every key collides (all multiples of 32) and one where keys spread across
slots — the cost does not depend on the distribution.

| resize | entries moved | | total allocs | node allocs | deallocs | bytes |
|---|---|---|---|---|---|---|
| 32 → 64 | 26 | upstream | 32 | 27 | 31 | 3624 |
| | | splice | **6** | **1** | 5 | 3000 |
| 64 → 128 | 52 | upstream | 59 | 53 | 58 | 7320 |
| | | splice | **7** | **1** | 6 | 6072 |
| 128 → 256 | 103 | upstream | 111 | 104 | 110 | 14688 |
| | | splice | **8** | **1** | 7 | 12216 |

The splice's allocations are *exactly* the slots-vector doubling chain and
nothing else: at 32 → 64 the sizes are `[24 ×1, 96, 192, 384, 768, 1536]`, where
the single 24 is the triggering insert's own node and the rest is
`new_with_capacity(64)` growing its `Vec` by pushing. Upstream's histogram is
the same list with `24 ×27` in place of `24 ×1`. The test asserts that the
non-node allocations are equal in the two versions, so the change is provably
confined to the move path.

Deallocations tell the same story from the other side: upstream frees one old
box per moved entry (31 vs 5 at the first resize), the splice frees none.

### The slope (`…::allocation_count_is_linear_in_entries_for_baseline_and_flat_for_splice`)

This is the claim that does not depend on how `Vec` happens to grow.

```
upstream (entries moved, node allocations): [(26, 27), (52, 53), (103, 104)]
splice   (entries moved, node allocations): [(26, 1),  (52, 1),  (103, 1)]
```

Upstream's slope is exactly 1 — one allocation per entry moved. The splice's is
exactly 0, pinned at the constant 1 that the triggering insert costs. Both are
asserted, not just printed.

### Whole run (`…::whole_fill_totals`)

Building a 400-entry map from empty goes through four resizes, which move
26 + 52 + 103 + 205 = **386** entries in total:

| | node allocations | total allocations | deallocations |
|---|---|---|---|
| upstream | 786 | 816 | 415 |
| splice | **400** | 430 | **29** |

400 is one node per key stored, and no more: the splice allocates exactly the
map's own data. Upstream allocates **2.0×** that, 386 of its 786 nodes being
entries it rebuilt only to throw the originals away. Its 415 frees drop to 29 —
the splice's remaining frees are all vector reallocation, not nodes.

## Behavioural equivalence (`tests/equivalence.rs`)

Six tests, each run against both files, all green in debug and release:

- `paper_test1_both` — the test the vendored file itself carries (commented out
  upstream because Charon could not extract `#[test]` at the time), on keys 0,
  128, 1024, 1056, which are all congruent to 0 mod 32 and so pile into slot 0.
- `all_colliding_both` — 200 keys that all collide at every capacity the table
  reaches, inserted, read back, overwritten, and removed in reverse.
- `survives_first_resize_both` — straight across the 32 → 64 boundary.
- `clear_then_reuse` — `clear` on a grown table, then refill.
- `matches_std_oracle_and_each_other` — seven seeds × 4000-op randomised
  streams of insert/get/get_mut/remove/contains_key/len over a key pool
  deliberately half-drawn from multiples of 32, each stream checked step by
  step against `std::collections::HashMap` **and** against the other
  implementation, then the two final states compared key by key over the whole
  pool. Each stream contains >1500 inserts, so it crosses several resizes.
- `colliding_pool_insert_remove_churn` — 18000 ops of insert/remove churn on a
  40-key all-colliding pool, the shape most likely to expose an ordering bug.

Divergences are reported with the step index and the op that caused them rather
than as a diff of two long vectors.

## Aeneas pipeline

See "Pipeline experiment" below.
