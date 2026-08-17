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

The invariant is **packed in the type** — a `HashMap` value cannot exist broken, so every op's invariant-preservation proof is just returning a well-typed pack, and it survives even opaque group ends. `HMInv`'s clauses (formulation yours, content fixed): `Le 1 cap`; every entry in slot `i` has `Mod key cap = i`; `n` equals the total entry count across buckets; `load` is the 4/5 threshold ledger for `cap`. Note `n` bounds every bucket's length through the counting clause — that is how callers name fuel bounds (`Le (…n…cap…) fuel`) without reaching into buckets.

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

## Process

Worktree off `origin/main`; FF-CAS endgame (rebase-and-ff is yours; see the merge-protocol notes in team memory — pinned-lease pushes, re-count migrations after every rebase). Incremental writes ≤120 lines, build per chunk, push every commit. Staging: S1 fixed-capacity map without resize (full specs); S2 resize + full Insert; S3 twins + differential + writeup. No kernel changes — if you believe you need one, stop and report instead. Spec conjuncts above are fixed; everything else is yours to shape, with deviations named in commit messages.

---

# The writeup (lane `hm-flagship-opus`)

**Stage reached: S1, partial.** The pure layer, the invariant library and the bucket
operation are complete and verified; `New` is complete with both its conjuncts; the
array-level `Insert` is not, and the exact obstruction is recorded below. S2 (resize)
and the twin/differential battery for the array-level ops are not attempted.

## What checks

`Dllbc/Tests/HashMap.lean`, 1,642 lines, **96 `example` assertions, all green**, module
build **4.4 s** from cold (the whole tree, 78 modules, is 4 m 42 s and unchanged by
this branch).

  * **The container.** `HMap = Σ (cap). Σ (load). Σ (n). Σ0 (slots). HMInv cap load n
    slots`, with `HMInv`'s four fixed clauses. Asserted inhabited at a concrete map,
    and each clause separately shown load-bearing by a pack that fails only it —
    including `HMInv Z 0 0 Arr()`, which is how no map is ever divided by zero.
  * **The spec vocabulary.** `FindHM`/`SizeHM`/`FindIns`/`FindRem`/`SizeIns`/`SizeRem`,
    with the `Σ (b : Bool). OptP b T` Option and a `Some`/`None`/`Opt` surface. All of
    it computes, pinned by `Refl` with wrong-value negatives alongside.
  * **`New`**, with BOTH conjuncts (`∀q. FindHM q result = None` and `SizeHM result =
    Z`), checking and running at a symbolic capacity; three twins refused.
  * **`InsertInList`**, the imperative bucket walk, verified against the model:
    `Id Bucket (*b) (InsL k v (old *b))`. Three twins refused, including the body twin
    where the overwrite branch does not write.
  * **The invariant library**, 22 lemmas: the slot arithmetic (`ModLtN`, `ModDec`,
    ported to `Std`/`StdLemmas`), the carve-crossing family (`AgetBMid`, `AgetBNe`,
    `SlotsOkSplit`, `SlotsOkJoin`, `SizeACat`, `LenLeSize`), the bucket layer
    (`FindLIns` — the mathematical core — plus `BucketAtIns`), and the Boolean
    bookkeeping (`TnotF`, `FnotT`, `EqbTrueEq`, `EqbSym`, `BoolRw`, `OptIf2`, `IfComm`,
    `NoBoth`).
  * **The executing differential**: Aeneas' `test1` at capacity 8, against a trusted
    Lean-side reference, plus four path-specific sequences and the `diffV2` simulation
    property.

## What does not, and exactly where it walls

**`Insert` over `&mut HMap` does not close.** The route is settled and every piece of it
is measured; what is missing is proof-term assembly, not a mechanism.

The container opens: destructuring the pack through the borrow hands back borrows of
all five components, the capacity reads with a refill, the invariant reads as knowledge
with none, and the slot is minted across a call (`SlotOf`, green). The carve then has to
go **behind a call boundary** — carving through the reborrowed component leaves the
array segmented and the pack's exit audit sees `Arr⟨σ ▷ σ, …⟩` where `Array cap Bucket`
is owed. With the carve in a callee, §6.2's opacity re-mints the array uncarved at the
declared type and the audit's complaint changes to the real one: the pack still holds
the OLD `HMInv`, whose type mentions the old slots.

So the operation must write a fresh invariant through `Hinv`, and — because opacity has
erased everything about the re-minted array — that proof can only come from the callee's
own return type:

```
fn InsertSlots (…, slots : &mut (Array cap Bucket), Hs : SlotsOk …, Hn : …)
  -> Σ (n1 : Nat). Σ0 (Hs2 : SlotsOk cap Z cap (*slots)).
       Σ (Hn2 : Id Nat n1 (SizeA cap (*slots))). Π (q : Nat) → …
```

Every lemma that body needs is proved and green (`SlotsOkSplit`/`Join` + `BucketAtIns`
for the slot clause, `SizeACat` + `LenLeSize` for the counting clause, `AgetBMid`/
`AgetBNe` + `FindLIns` for the pointwise equation). Two are missing: a bucket-length
accounting lemma (`LenE (InsL k v b)` against `FindL k b`) and the arithmetic chaining
it into `SizeA`. The residual is the assembly.

**A second wall, independent of the first, and more interesting.** A caller that
inserts TWICE does not check:

```
call: comptime argument (unit) does not have its parameter type (natRec …)
```

After the first call, opacity has re-minted the bucket's owner as a fresh σ, so at the
second call `Le (LenE (*b)) fuel` is a stuck `listRec` under `Le` and no `unit` inhabits
it. **The caller has lost the bucket's length at the call boundary.** This is
`HmProbeArrays` §A5's `λ B. unit` admission reached from the other side, and it is
precisely the capability `12-design-borrow-refounding.md` exists for. The local repair
is for `InsertInList` to return a length bound so a caller can chain it; the general one
is loan-attached debts.

## Comparison ledger

| | Aeneas ICFP'22 | this lane |
|---|---|---|
| Implementation | 201 LoC Rust | 319 lines of DLLBC `fn` bodies (incl. twins, which transcribe bodies) |
| Spec / model | `hash_map_t_v`, `find_s` (in `Properties.fst`) | 306 lines |
| Proofs | 3,247 lines hand-written F* + Z3 | 539 lines of DLLBC lemma terms |
| Harness | — | 109 lines (Lean-side decoders and the reference map) |
| Effort | 4 person-days | one agent session (7 commits, ~5 h wall-clock) |
| Ops verified | insert (with resize), get, get_mut, remove | `New` (full), `insert_in_list` (full); `Insert`/`Remove`/`GetMut` not closed |
| Check time | Z3, not reported | 4.4 s for the module |

The proof-line ratio is not a like-for-like win, because the operations that would carry
the most proof are the ones this lane did not close. What the numbers do support is that
the layers below the array operation — model, invariant, bucket algebra — cost hundreds
of lines rather than thousands.

## Divergence ledger

Beyond the three the vendored README anticipated:

  1. **`Nat` is unbounded** (theirs is `usize`): their overflow obligations and `Fail`
     cases vanish. This lane found the cost side of that trade — `Nat` is UNARY, so
     `Term.nat 1056` is a 1056-deep tower and running Aeneas' literal test keys
     exhausts the interpreter's fuel. The symbolic side is unaffected (`Mod 1056 32 = 0`
     is asserted at the real keys); only the concrete differential is scaled, to
     capacity 8 with keys 0/8/16/24, which preserves every structural feature `test1`
     was written to exercise.
  2. **Intrinsic vs extrinsic invariant**: their `hash_map_t_inv` is a
     requires/ensures on every operation; here it is packed in the type, so no
     signature in this file states it and no operation proves it separately. Per
     `HmProbeGetmut`'s G5 it also survives opaque group ends, because a fresh σ is
     minted AT THE DECLARED TYPE.
  3. **Borrow-returning ops carry no functional conjuncts** (`retMixesBorrow`), deferred
     to the loan-attached-debts milestone. Not reached here — `GetMut` and
     `GetMutOrInsert` are not written, though `hm-probe-getmut` established their borrow
     structure.

And two this lane adds:

  4. **The find equation does not need the slot invariant.** `EqbTrueEq` rules out
     `q = key` from a slot mismatch alone, so `SlotsOk` is required only to rebuild the
     PACK, never to prove the pointwise claim. Aeneas' proof uses the invariant on both
     sides.
  5. **`Insert` is not total in the same sense.** Theirs cannot fail because it checks
     the load factor and resizes; here totality is not yet reached at all, since the
     array-level operation does not close.

## Two findings worth keeping regardless of the flagship

  * **The kernel's `aget` cannot be a spec's slot selector.** `Pure.whnfN`'s rule fires
    only at a concrete index into a literal `Arr`; there is no rule taking
    `aget (S m) (S i) (acons m x t)` to `aget m i t`. A carve leaves exactly an
    `acons`/`arrCat` spine at a symbolic index, so `aget` there is inert and every lemma
    about it is unprovable — a stuck `aget` has no eliminator. Written as an `arrRec`
    fold with the index threaded (`AgetB` here), the same function reduces definitionally
    and the lemmas are ordinary inductions. A spec written with `aget` type-checks
    happily and then walls at the first lemma.
  * **The surface's list `elim` was monomorphic at `List Nat`** while the kernel's
    `listRec` rule was general all along. Fixed here in `Uni.elabUElim` (21 lines,
    value-preserving, whole tree rebuilds green). The read is SYNTACTIC, so a motive
    written `λ (Bz : Bucket). …` over a `Term` splice silently falls back to `Nat` and
    fails as a bare `false` with no message — documented at both the patch site and the
    use sites.
