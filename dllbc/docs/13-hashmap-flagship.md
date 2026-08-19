# The hashmap flagship — problem statement

**Implement a verified, resizable, in-place hashmap in DLLBC, mirroring the Aeneas ICFP'22 case study closely enough that the two artifacts can be compared side by side.** This document is the complete problem statement: the ops, the layout, the spec obligations, and the acceptance tests are fixed here; how you write the bodies, the auxiliary lemmas, and the exact signature shapes are yours. Everything you need to learn the language is `04-language.md` (read it whole) plus the test suite — `Tests/ArraySort.lean` is the closest existing artifact in spirit and difficulty and is the model for what "done" looks like.

The reference is vendored at `competitors/aeneas-hashmap/` — read its README, then `icfp22/hashmap.rs` (the implementation to mirror, recursive, no loops) and skim `icfp22/fstar/Hashmap.Properties.fst` (their 3,247-line hand proof; the comparison target). Their headline lemma (`hash_map_insert_fwd_lem`, paper p. 26) is what the Insert spec below transliterates.

## What to build

**Layout (fixed, for the comparison):** slots are an array of association-list buckets; the hash is the identity; the slot is `Mod key cap`; load factor 4/5; when the entry count exceeds the load threshold, resize by doubling the capacity and re-inserting every entry into a fresh table. Keys are `Nat`. Values are `Nat` in v1 (do not rely on value copyability anywhere — treat values as move-only, so the code survives generalization; genericity in V via pure `Π (T : Type)` telescopes is a stretch goal, not v1).

**The container (fixed in content, adjustable in spelling with justification):**

```
HashMap := Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
           Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInv cap load n slots
```

The invariant is **packed in the type** — a `HashMap` value cannot exist broken, so every op's invariant-preservation proof is just returning a well-typed pack, and it survives even opaque group ends. `HMInv`'s clauses (formulation yours, content fixed): `Le 1 cap`; every entry in slot `i` has `Mod key cap = i`; `n` equals the total entry count across buckets; `load` is the 4/5 threshold ledger for `cap`; and **each bucket's keys are duplicate-free** (ratified 2026-08-19, after the fable run proved it FORCED: Remove's pointwise equation fails at a shadowed duplicate and resize-reordering breaks Insert's — Aeneas' own `slot_t_inv` carries the same clause). Note `n` bounds every bucket's length through the counting clause — that is how callers name fuel bounds (`Le (…n…cap…) fuel`) without reaching into buckets.

**Ops** — `New`, `Insert` (with resize), `Remove`, `GetMut` (present-key, evidence-carrying), `GetMutOrInsert`. `Len` is a projection. No `clear` needed.

**Option:** use the Σ(Bool) encoding with a `Some`/`None`/`Opt` definition vocabulary — the exact working spellings are on branch `hm-probe-opt` (`Tests/HmProbeOpt.lean`). Do NOT add a kernel Option (that decision is closed; branch `hm-option-kernel` is the parked road-not-taken).

## The specs (fixed — these conjuncts are the claim; changing them means coming back to the user)

Spec functions you will define (pure, over the pack): `FindHM q hm : Opt Nat` — lookup `q` in bucket `Mod q cap`; `SizeHM hm : Nat`. Model-update functions: `FindIns q key v hm` (the mathematical update: `Some v` at `key`, old answer elsewhere), `FindRem q key hm` likewise.

- **New** `(cap, HLe1cap) -> HashMap`: ∀q, `Id (Opt Nat) (FindHM q result) None`, and `SizeHM result = Z`.
- **Insert** `(fuel, …, key, val, self : &mut HashMap)` returns:
  `Π (q : Nat) → Id (Opt Nat) (FindHM q (*self)) (FindIns q key val (old *self))` — the pointwise equation subsumes Aeneas' "found" and "frame" conjuncts in one total claim — plus size accounting: `SizeHM (*self)` equals `SizeHM (old *self)` bumped iff `FindHM key (old *self)` was `None` (state via a spec function, not a conditional Π). Insert is total: Nat is unbounded, so Aeneas' Fail/saturation cases do not exist here — a recorded divergence, not an omission (see the vendored README's ledger).
- **Remove** `(fuel, …, key, self) -> Σ (r : Opt Nat). …`: `Id (Opt Nat) r (FindHM key (old *self))`; pointwise `Π q → Id (Opt Nat) (FindHM q (*self)) (FindRem q key (old *self))`; size decremented iff present.
- **GetMut** `(…, key, self, Hin : <evidence key is present>) -> &mut Nat` and **GetMutOrInsert** `(…, key, default, self) -> &mut Nat`: these return borrows, so their return types carry **no functional conjuncts** (`retMixesBorrow`) — they are verified for safety + the packed invariant, exercised by the executing differential, and their caller-side functional story is explicitly deferred to the loan-attached-debts milestone (`12-design-borrow-refounding.md`). Write the walk in the **total, or_insert style** — on `Nil`, write the cell and return a borrow into what you wrote — so no bucket-length precondition exists to transport (measured on branch `hm-probe-getmut`; the partial style is unstatable today).
- **Resize** is internal to Insert; it needs no public spec — its correctness is absorbed by Insert's pointwise equation, proven by folding Insert-without-resize's own conjuncts over the old table.

## Known-good ground (probed 2026-08-17; use it, don't rediscover it)

- **Slot arithmetic is written and green** on branch `hm-probe-mod`: `Mod`/`Div` (accumulator form — mandatory shape until the eager-evaluation lane lands), `ModLtNTy` (`Le 1 n → Le (S (Mod a n)) n`), `ModDecTy` (`Le (S i) n → Σ (r). Id Nat n (Add i (S r))`). Port them into `Std`/`StdLemmas` as your first commit — note the probe branches predate the Σ dot migration, so ported code needs its Σ arrows converted (`dllbc/scripts/sigmadot.py` does the sweep; main no longer parses the arrow). Two forced shapes from that probe: capacity is an **opaque `n` with `Le 1 n`** (an `S c` pattern is rigid — the carve's premise (3) cannot refine it), and the slot index/residue must be **minted across a call returning a Σ** (comptime spellings fail the occurs check) — the same shape `partitionA` uses for `splitA`'s returns.
- **Bucket surgery:** never *read* a bucket out of its slot (element-place take-and-refill does not exist; measured on `hm-probe-arrays`) — **borrow the element** (`&m (*cell)[0]`) and take-and-rebuild through that `&mut (List …)`, which also lets bucket ops be standalone functions. `insert_in_list` itself is already written and checking on that branch. Nested patterns (`Cons(Pair(kk, vv), tl)`) and `let Pair(a, b) = e;` are in main — use them.
- **Allocation:** `MkSlots : Π (n : Nat) → Array n (List …)` by `acons` recursion works both as comptime builder and `fn` (spelling on `hm-probe-opt`).
- **The invariant library** is the real work, and it is `SortedArrCat`'s shape: an array-level predicate (`AllShortA`-style, demonstrated on `hm-probe-arrays`) plus Find/Inv-crossing-a-carve lemmas mirroring the `SplitACat*` family. Budget for a dozen-plus lemmas. `Eqb`-reflexivity at a symbolic key is a known missing `Std` lemma you will need.
- Expect the two standard taxes: capture-before-consume staging (`MkC`-style builders — see ArraySort's pain diary) and Σ0-invariant repacking at every exit.

## Acceptance

1. **The chain checks:** one `progOk` over the whole declaration chain, ArraySort-style, against no table.
2. **Lying twins**, one per conjunct plus body twins, each `progRejects`/`= false`: find-equation lied onto `old *self`; frame direction flipped; size accounting off by one; and body twins — insert into the *unhashed* slot (drop the `Mod`), skip the `n` bump, skip the duplicate-key overwrite, and **skip the resize** (caught by the packed load ledger).
3. **Executing differential:** port Aeneas' `test1` (keys 0, 128, 1024, 1056 at cap 32 — all collide in slot 0 by construction; overwrite via the get_mut path; remove; re-check) plus a small-cap sequence that actually triggers ≥2 resizes, checked against a trusted Lean-side reference map, `runQsA`-style. E2E rule applies: accepted/rejected or runs-to-X only.
4. **The writeup:** a short comparison section at the bottom of this file (fill it in): LoC split (program / spec / lemmas / staging), check wall-clock, and the divergence ledger vs the vendored README's (Nat-vs-usize; intrinsic-packed vs extrinsic invariant; borrow-returning ops without functional specs).

## Prior attempts (for coordinators and reviewers — NOT for implementers)

Three implementations of this spec exist as parked branches, from the 2026-08-17 three-model comparison (identical prompts, base `1e5fad94`): **`hm-flagship-fable` @ `97be424a`** — S3 reached (New / Insert-with-resize / Remove, every fixed conjunct in one chain, 12/12 twins, the literal cap-32 `test1` differential; the benchmark artifact); **`hm-flagship-opus` @ `9c288065`** — S1-partial (New + Insert, 20/20 twins, scaled differential); **`hm-flagship-sonnet` @ `2dcfa82f`** — S1-core (everything below Insert, plus a no-cross-bucket-duplicates lemma family its `FindHM` deviation forced). Their worktrees are gone; the branches are pushed.

**If you are an agent implementing this spec: do NOT read these branches.** Independent attempts are the point — reading a prior implementation anchors yours and voids the comparison. They are listed for coordinators, reviewers, and post-hoc analysis. (The probe branches under "Known-good ground" above remain fair game: those are capability probes, not implementations of this spec.)

## Process

Worktree off `origin/main`; FF-CAS endgame (rebase-and-ff is yours; see the merge-protocol notes in team memory — pinned-lease pushes, re-count migrations after every rebase). Incremental writes ≤120 lines, build per chunk, push every commit. Staging: S1 fixed-capacity map without resize (full specs); S2 resize + full Insert; S3 twins + differential + writeup. No kernel changes — if you believe you need one, stop and report instead. Spec conjuncts above are fixed; everything else is yours to shape, with deviations named in commit messages.
