# Subtype-checker performance: design and plan

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

## Inventory of redundant-work sources

### Source 1 — `Closure.open` re-evaluates body on every call

Every time `subCheckVal` hits a `.iota` or `.fix` on either
side, it calls `clB.open fuel a` (iotaIntro / fix-unfoldR) or
`openFresh` (structural both-sides path). Each call runs
`eval fuel 4 (v :: cl.env) cl.body` — evaluating the **entire**
body from scratch, producing a fresh `Val` tree.

With Nat_'s body containing `let succ_ = fix succ_:(N→N). λm:N.
λP:((succ_ m) → Type). …`, each unfold re-walks the whole
let-chain and constructs the nested `.fix`/`.lam` Vals.

**Redundancy**: when the same `(cl, v)` pair reappears along
different recursion paths, we redo identical work. The result
is a pure function of `(cl, v)`, so memoization is sound.

### Source 2 — `vapp` re-evaluates recursive body on every call

`vapp fuel unf (.fix _ cl) a` unfolds by `eval fuel (unf-1) (f ::
env) body` then `vapp f' a`. Same as Source 1 but for recursive
heads. For `succ_ m` with a concrete `m`, this fully unfolds
succ_'s body and produces a `.lam` value. Repeated calls with
the same `(f, a)` redo all of this.

### Source 3 — `.iota, .iota` tries structural before iotaIntro

The structural arm runs `openFresh` on both sides and recursively
`subCheckVal`s. If structural fails, the whole structural subtree
was wasted and we fall through to iotaIntro (which does its
*own* `clB.open fuel a`).

For `three_ ⊑ Nat_`, the annotations are different (`.type` vs
`Nat_`), so structural always fails at the annotation check —
the `openFresh`s inside the `do` block never fire (they're behind
`if !annOk then return false`). Good.

But when annotations *do* match (e.g. in deeper iota-iota
comparisons derived from the same recursive type), structural
succeeds sometimes and fails other times, and the `openFresh`
work is redundant with iotaIntro's `clB.open` work.

### Source 4 — `subCheckVal` doesn't memoize `true` results across calls

`seen.any (fun (a', b') => a == a' && b == b')` is *path-local*
cycle detection. Once a sub-judgment `a' ⊑ b'` has been proven
true under seen set S, and we later hit `a ⊑ b` with `a == a'`
and `b == b'` at some seen set S' ⊇ S, we re-derive from scratch.

With sharing / pointer-eq on Val, "same sub-judgment" can be
detected in O(1). Caching across the whole `subCheck` call would
cut the O(n²)/O(n³) blowup down to O(n) in the number of
distinct `(a, b)` pairs.

### Source 5 — annotation re-checks in iotaIntro + fix-unfold

Both the `.iota, .iota` structural path and the iotaIntro
fallback call `subCheckVal seen' a ann` (the "okAnn" guard
— A5). When iotaIntro closes via seen, this is already one
step; but any non-trivial annotation check duplicates work.

## Proposed fixes

### Fix 1 (highest leverage): memoize `Closure.open` and `vapp`

Cache `(cl, v) → result` for `Closure.open` and `(f, a) → result`
for `vapp`. Both are pure deterministic functions (modulo fuel
success/failure).

**Implementation sketch**: thread a mutable cache through the
algorithm via `IO.Ref` and `unsafeIO`. The pure `Closure.open` /
`vapp` definitions are unchanged; a `@[implemented_by]` wrapper
provides the memoized runtime version.

**Soundness**: memoization of pure deterministic functions does
not change observable semantics. Proofs in `SoundnessProof.lean`
that reason about `Closure.open` / `vapp` are untouched
(the underlying definition is unchanged).

**Expected improvement**: each `(cl, v)` pair evaluated once
instead of O(n) times. `three_ ⊑ Nat_` drops from ~50k fuel
to ~500.

### Fix 2: memoize `subCheckVal` on successful results

Cache `(a, b) → true` results across the whole subCheckVal call.

**Subtlety — seen-set soundness**: a cached true was derived
with some seen set S. Reusing it at a different seen set S'
is sound only when S ⊆ S' (or when the true didn't depend on
seen — too hard to track). In practice, within a single top-
level `subCheck` call, the seen set used to derive a cache
entry is a prefix of the current path's seen, but *sibling
paths* may have added different entries.

**Conservative solution**: Only cache results derived with
`seen = []`. An entry at `seen = []` is unconditionally
valid (no assumptions).

**Better solution**: Cache `(a, b, |seen|) → true`. Since
the path's seen is append-only within a recursive subtree,
and the size monotonically increases, restricting cache
lookups to `current_seen_size ≥ cached_size` ensures the
cached derivation's seen-set is a prefix of (or equal to) the
current seen. This is sound IF cached entries are *only*
produced by deeper calls (which add to seen, not remove).

Given the implementation complexity, start with the
conservative `seen = []` version.

**Expected improvement**: cuts cross-subtree duplication in
the subtype derivation. Complements Fix 1.

### Fix 3: drop `.iota, .iota` structural when annotations mismatch

Before trying structural (which includes the `openFresh` work),
check whether `annA == annB` cheaply (ptrEq / structural).
If they differ, skip structural and go straight to iotaIntro.

**Soundness**: iotaIntro is always a valid fallback; skipping
structural only loses *completeness* if structural would have
succeeded. Structural only succeeds when annotations match
(the `annOk` guard requires `annA ⊑ annB`, and for most cases
— ι-nested-in-fix-unfold — `annA == annB`), so this is safe.

Actually, even current code tries structural always. Keeping
structural but skipping the `openFresh` work when it's known
to fail is equivalent.

Lower priority than Fix 1 (which subsumes the cost).

### Fix 4: share fresh-neutral values across arm entries

Inside one `subCheckVal` call, when we hit a `.lam, .lam`, we
create `.neutral (.var depth)` for the body-opening. If the same
`depth` appears later in a sibling branch, we can share the
`.neutral` value (not construct fresh). This is a micro-
optimization; ptrEq-on-neutral is already cheap since the
structural comparison checks just `l1 == l2`.

**Low priority.**

## Phased plan

1. **Phase A (this doc + Fix 1)**: implement memoized
   `Closure.open` / `vapp` via `@[implemented_by]` + `IO.Ref`.
   Measure on `three_/four_/five_ ⊑ Nat_` and
   `two_/three_ ⊑ Fin n`. Uncomment commented-out tests
   that start passing.

2. **Phase B (Fix 2)**: subCheckVal `seen=[]`-only memoization
   if Phase A leaves residual quadratic behavior.

3. **Phase C (Fix 3 if needed)**: annotation-mismatch
   skip in iota-iota structural.

Post-mortem + commit after each phase. Use test-based
benchmarks: uncomment previously-disabled regressions in
`lean/Och/Std/DNat.lean`, `DFin.lean`, `Array.lean` and
`PerfProbe.lean` as proof of improvement.

## Soundness constraints

- Preserve `subCheckVal_subV` at `SoundnessProof.lean:268`.
- Preserve the four open declaration-sorries (Phase 1 boundary
  per `docs/ideas/sorry-closure-plan.md`).
- Do not change `Outcome`-shape of any return type.
- Do not alter `Closure.open` / `vapp` pure definitions —
  all changes go through `@[implemented_by]`-attached
  unsafe runtime variants, leaving proof-side definitions
  untouched.

## Tests that should start passing after Phase A

- `example : NbE.subCheck 6400 five_ Nat_ = .ok true`
  (currently commented in `PerfProbe.lean`).
- `example : NbE.subCheck 16000 two_ (och{ Fin three_ }) =
  .ok true` (currently commented in `DFin.lean`).
- `example : NbE.subCheck 16000 three_ (och{ Fin two_ }) =
  .ok false` (currently commented in `DFin.lean`).
- `example : NbE.subCheck 16000 two_ (och{ Fin two_ }) =
  .ok false` (currently commented).
- `concEval` tests in `DNat.lean` and `Array.lean` (commented
  out for compile time) may or may not — `vapp`/`eval`
  memoization helps `subCheck`, but `concEval` is a different
  evaluator that does substitution. See Fix 6 (not in this
  plan) for extending memoization to concEval.
