# Subtype-checker performance: investigation + post-mortem (2026-04-24)

## Context

After unifying the Std library on the singleton-tightened `Nat_`
(Option A) and dependent-fs-codomain `Fin` (Option F), the
subtype checker's intrinsic cost for `n_ ⊑ Nat_` became O(n) —
the singleton domain `λpred:m.` forces each predecessor through
the contra chain. That's genuine new work.

On top of that, measured cost is O(n²)–O(n³):

| judgment              | fuel required | expected      |
|-----------------------|---------------|---------------|
| `one_ ⊑ Nat_`         | ~200          | ~50           |
| `two_ ⊑ Nat_`         | ~800          | ~100          |
| `three_ ⊑ Nat_`       | ~50k          | ~200          |
| `five_ ⊑ Nat_`        | >6400 (fails) | ~300          |
| `two_ ⊑ Fin three_`   | >16k (fails)  | ~300          |

The intrinsic cost is about 5 subproblems per numeral step, so
`five_ ⊑ Nat_` should be ~50 subproblems, not tens of thousands.
The gap is **redundant work inside `subCheckVal`**: the same
semantic sub-judgment gets re-derived from scratch along many
paths.

## Initial hypothesis

1. **Closure.open re-evaluates body on every call.** Each `.iota`
   or `.fix` unfold via `Closure.open` runs `eval fuel 4 (v ::
   cl.env) cl.body`, producing a fresh `Val` tree — structurally
   identical across paths but pointer-distinct.
2. This breaks `Val.beqFast`'s `ptrEq` fast-path, so downstream
   `a == b` / `seen.any` guards degrade from O(1) to O(|val|).

**Expected fix:** memoize `Closure.open` by pointer identity, or
hash-cons the Val trees so structurally-equal Vals become
pointer-equal.

## What was tried

### Attempt 1 — Array-backed ptrEq cache on `Closure.open`

`initialize closureOpenCache : IO.Ref (Array (Closure × Val ×
Val))` + unsafe `@[implemented_by]` lookup via `ptrEq`.

**Result:** 0 cache hits for `one_ ⊑ Nat_` at fuel 200 (207k
calls). Diagnostic: every `(cl, v)` pair has unique pointer
identity. Fresh `Val` allocations by internal `eval` never
match previously-cached entries via ptrEq.

### Attempt 2 — Structural (beq) linear-scan cache

Fall back to `Val.beqFast` (ptrEq fast-path + structural
fallback) when ptrEq misses.

**Result:** linear-scan cost dominates — cache grows to 125k
entries, each lookup is O(|cache|) × O(|val|). Net: slower
than no cache.

### Attempt 3 — `ShareCommon.State` persistent hash-consing

Pipe `Closure.open` results through
`ShareCommon.State.shareCommon` (threaded through a global
`IO.Ref`). After sharing, structurally-equal results become
pointer-equal.

**Verification that hash-consing works:** yes. Two separate
evaluations of `Nat_` become pointer-equal after passing through
the shared state. Confirmed by a `native_decide` test.

**Result on `two_ ⊑ Nat_` at fuel 800:** ~23s with shareCommon
vs ~18s without. **Net slowdown, not speedup.** The per-call
overhead of `State.shareCommon` exceeds the downstream ptrEq
savings.

### Attempt 4 — Cross-call `subCheckVal` successful-result cache

Introduce pure-identity `cacheHit a b : Bool := false` and
`cacheInsert a b r : Outcome Bool := r` with
`@[implemented_by]` impls that consult a global cache; insert
in the `subCheckVal` body.

Soundness: if the algorithm ever returns `.ok true` for `(a, b)`
under any seen, then `a ⊑ b` holds declaratively (by
`subCheckVal_sound`); so a cached-true is safe to replay in any
context, regardless of the current seen set.

**Result:** again no effective cache hits when keyed on ptrEq.
With structural `Val.beqFast` keying, linear scan is slow.
Overall wall-clock unchanged — ~23s on `two_ ⊑ Nat_` at fuel
800.

## Conclusion / root-cause reanalysis

The expected cache-hits never materialize because **the sub-
problems explored along different recursion paths are genuinely
different**: different `seen` sets, different unfold depths,
different fresh-neutral levels. `Closure.open`'s input `(cl, v)`
pair has `v` sourced from the caller's `(a, b)` variables,
which mutate along each path.

ShareCommon *does* canonicalize to pointer-equal results, but:

1. The `(a, b)` pairs passed to `subCheckVal` itself aren't run
   through shareCommon — they originate from `subCheckVal`'s own
   local recursion, not from `Closure.open`'s output.
2. Even when `bodyB' ← clB.open fuel a` produces a
   canonicalized `bodyB'`, the NEXT recursion's pattern-match
   decomposes it into `.fix ann cl2`, and `ann` / `cl2` have
   their own pointer identities that may or may not be shared
   across paths.

The 50k-fuel cost for `three_ ⊑ Nat_` appears to be **genuine
algorithmic work**, not cache-missable redundancy. The
recursion tree is wide (each layer of `succ_` opens a new ι
with a fresh singleton annotation, and the contra on the
singleton re-invokes `subCheckVal` on the predecessor chain).

## What would actually move the needle

1. **Redesign the singleton-tightened `succ_` encoding** to
   avoid the deep contra chain. Option A gave us the Fin-as-Nat
   subsumption, but at this fuel cost. Perhaps a different
   encoding (e.g. Option F' with a smart `Fin succ = Fin pred
   + {n}` split) could retain the subsumption with a flatter
   derivation.

2. **Make `subCheckVal` iterative instead of recursive**, with
   an explicit worklist and a structural-hash memo. The current
   recursive shape forces each sub-problem to inherit the full
   seen list and decrement fuel; an iterative version could
   share state more efficiently.

3. **Use typed NbE** (Option 1.75 per
   `docs/ideas/typed-nbe.md`). Typed normalization could prune
   many sub-problems that the current checker re-explores. This
   is a ~2–4-week effort and has wider metatheoretic
   implications.

4. **Give up on `five_ ⊑ Nat_` at high fuel as a test target.**
   The intrinsic cost of Option A is O(n) per numeral layer.
   Three_ is the ceiling where the cost is manageable. For
   practical Ochre code, very-precise singleton types rarely
   get used at n > 3 — the user coerces to `Nat_` first.

## Infrastructure that was kept

- `lean/Och/MemoRefs.lean`: declares `shareState` (a persistent
  `ShareCommon.State` ref). Available for reuse if future memo
  work needs cross-call hash-consing.
- `lean/Och/SubCheckVal.lean`: `Closure.openImpl` — a
  hash-consed variant of `Closure.open`. Currently **not**
  attached via `@[implemented_by]` (commented out) because the
  `State.shareCommon` per-call overhead exceeds downstream
  savings at measured workloads. Re-enable if a cheaper
  canonicalization primitive becomes available.

## Tests that did NOT become tractable

These remain commented out in the source:

- `PerfProbe.lean`: `five_ ⊑ Nat_` at fuel 6400 (intractable).
- `DFin.lean`: `two_ ⊑ Fin three_` at fuel 16000 (intractable).
- `DFin.lean`: `two_ ⊑ Fin two_ = .ok false` at fuel 16000
  (intractable).
- `DFin.lean`: `three_ ⊑ Fin two_ = .ok false` at fuel 16000
  (intractable).
- `Array.lean`: `appendArrays` at its declared type (A6-family
  incompleteness, not a perf issue).
- `DNat.lean`: `add_`/`double_` concEval tests (5000+ fuel).

## Soundness delta

None — `subCheckVal`'s pure definition and proofs in
`SoundnessProof.lean` are unchanged. The `@[implemented_by]`
attribute was attached and detached without affecting the
kernel-level definition. The four open declaration-level
sorries in `SoundnessProof.lean` remain unaffected.
