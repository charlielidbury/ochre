# Aeneas hashmap case study — vendored reference

The resizable-hashmap case study from *Aeneas: Rust Verification by Functional Translation* (Son Ho and Jonathan Protzenko, ICFP 2022 — the paper is at `docs/papers/aeneas.pdf`, §6 pp. 25–27). Vendored here 2026-08-17 so agents working on the DLLBC hashmap flagship can read it without network access, and so it cannot drift or disappear upstream. Both upstream projects are Apache-2.0 (`LICENSE-aeneas.md`, `LICENSE-charon.md`).

Why files rather than a git subtree: the Aeneas repo is a full OCaml compiler development; only the hashmap case study is reference material for this repo, and pinning the exact paper-era files matters more than tracking upstream.

## icfp22/ — the paper-era artifact

Rust sources, from the Charon repo (at ICFP time the Rust inputs lived there), commit `6f210dce42f57bb09de9a91b52290fa58e635e77` (2022-09), `tests/src/`:

- `hashmap.rs` — the implementation the paper verifies (348 raw lines; the paper counts 201 LoC without blanks/comments). Fully recursive — no loops — which matches DLLBC's shape. Buckets are `AList<T>` cons-lists; identity hash mod capacity; load factor 4/5; doubling resize that re-inserts every entry.
- `hashmap_main.rs`, `hashmap_utils.rs` — the on-disk wrapper: `hashmap_utils::{serialize, deserialize}` are the functions the paper marks opaque for the §6 I/O case study.

F* artifact, from the Aeneas repo, commit `d8f92140abd7e65b6f1c5dd7e511c0c0aa69e73f` (2022-09), `tests/hashmap/` and `tests/hashmap_on_disk/`:

- `fstar/Hashmap.Funs.fst`, `Hashmap.Types.fst` — what Aeneas *generates* from the Rust (679 + 21 lines): the pure forward/backward functions the proofs are about. Read `Funs.fst` to see what their functional translation actually produces — e.g. `insert_in_list` becomes take-and-rebuild, which is what DLLBC writes at the source level.
- `fstar/Hashmap.Properties.fst`, `.fsti` — the *hand-written* proofs (3,247 + 267 lines): the invariant (`hash_map_t_base_inv`, `hash_map_t_inv`), the associative-list model (`hash_map_t_v`, `find_s`), and the per-operation lemmas, including `hash_map_insert_fwd_lem` quoted in the paper. This is the "4 person-days" artifact and the primary comparison target for the DLLBC flagship's spec + lemma layer.
- `fstar/Hashmap.Clauses.fst`, `Hashmap.Clauses.Template.fst` — the hand-filled termination (decreases) clauses; the analog of DLLBC's fuel threading.
- `fstar/Primitives.fst` — the support library (the `result` monad; every usize op can Fail on overflow — this is where their arithmetic obligations live).
- `fstar-on-disk/` — the same layering for the serialization case study (§6's I/O discussion): `HashmapMain.Opaque.fsti` is the assumed interface for the opaque serialize/deserialize.

## current/ — upstream today

- `hashmap.rs` — `tests/src/hashmap.rs` fetched 2026-08-17 from the Aeneas repo's `main` (which pointed at `daa85d7e89400fa978be83fedbc7e475a83f0889`). Differences from the paper era: written with `while`/`loop` (extracted with `-loops-to-rec`), and a `saturated` flag replacing the paper-era behavior when the capacity-doubling overflow guard fails. Useful as the current upstream shape; the icfp22/ version is the apples-to-apples target.

## splice/ and rust-check/ — the allocation-optimal resize

Added 2026-08-20. `splice/hashmap.rs` is `current/hashmap.rs` with one function
body replaced: `move_elements_from_list` relinks each bucket node into the new
table, reusing the box the node already owns, instead of re-inserting the entry
and allocating a fresh box for it. That makes a resize's only allocation the new
slots vector, matching what the DLLBC flagship does. `rust-check/` is a cargo
package that compiles both files (by `#[path]`, not by copying) and measures
them side by side under a counting global allocator: upstream allocates one node
per entry moved, the splice allocates none, and both pass the same behavioural
tests against a `std::collections::HashMap` oracle. `pipeline/` runs the real
Charon + Aeneas toolchain over both variants — it translates cleanly, and the
generated Lean and Rocq are checked in there. `SPLICE-NOTES.md` has the numbers
and the reasoning; `current/` and `icfp22/` remain untouched vendored artifacts.

## Comparison ledger (from the paper, for the flagship writeup)

- Implementation: 201 LoC (their count, no blanks/comments).
- Proof effort: 4 person-days, extrinsic style, F* with Z3.
- Ops verified: insert (with resize), get, get_mut, remove; invariant preservation; behaves-like-a-map (find view); no arithmetic overflow.
- Known divergences the DLLBC flagship must disclose: DLLBC `Nat` is unbounded (their overflow obligations and Fail cases vanish — see `Primitives.fst` and the `try_resize` guard in `icfp22/hashmap.rs`); DLLBC packs the invariant intrinsically in the type where their `hash_map_t_inv` is an extrinsic requires/ensures; DLLBC keys stay `Nat` (theirs are fixed `usize`; both use the identity hash).
