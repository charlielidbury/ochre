# Memoization for subCheckNF

## Problem

`subCheckNF` explores the same or equivalent subtyping pairs many times
during self-intro cascades. The `seen` list only prevents cycles on the
*current path* — it doesn't cache results from *previous* completed
checks. When absEval normalizes a large substituted body, every domain
check is a fresh subCheckNF call that may redo work already done
elsewhere in the tree.

## Proposal

Add a global memo table that maps subtyping queries to their results.
Before starting a new subCheckNF, look up the pair; if found, return
the cached result immediately.

## What to cache

### Option 1: Cache normalized pairs

**Key**: `(NfExpr, NfExpr)` — both sides already in normal form.

**Value**: `Bool` (true = proved, false = disproved).

**When to store**: After subCheckNF completes for a pair, store the
result.

**Pros**: Normal forms are canonical, so syntactically equal NfExprs are
semantically equal. High cache hit rate.

**Cons**: Both sides must be normalized before lookup, which is itself
expensive. This is the bootstrapping problem — the normalization we're
trying to avoid is required for the cache key. However, it does help
when the *same* normalized pair appears multiple times (which happens
frequently in the dNat case because substitution creates many copies
of dzero/dsucc that all normalize to the same thing).

### Option 2: Cache raw pairs

**Key**: `(Expr, Expr)` — raw terms before normalization.

**Value**: `Bool`.

**When to store**: After subCheckNF completes.

**Pros**: No normalization overhead for cache lookup.

**Cons**: Low hit rate. The whole problem is that substitution creates
syntactically different terms (`dzero` with dNat in its annotation vs
`dzero` with dzero in its annotation). These are different cache keys
even though they're semantically identical. The cache would only help
for literal structural duplicates, which are less common.

### Option 3: Cache by hash (approximate)

**Key**: A structural hash of the pair (e.g., hash of the term tree
ignoring mu annotations, or hash after a cheap partial normalization).

**Value**: `Bool` + the original pair (for hash collision checking).

**Pros**: Could catch semantically-equal-but-syntactically-different
pairs if the hash is designed to be invariant under the differences
that substitution introduces.

**Cons**: Complex to design correctly. Hash collisions could cause
unsoundness if not checked. The hash function itself needs to be
cheaper than the check it's memoizing.

### Option 4: Cache at the absEval level

Instead of caching subCheckNF results, cache `absEval` results:

**Key**: `Expr` (the input expression).

**Value**: `(NfExpr, NfExpr)` (value, type).

**When to store**: After absEval successfully normalizes a term.

This attacks a different part of the problem: the cascading absEval
calls inside self-intro. If the same expression is absEval'd multiple
times (common when substitution duplicates sub-terms), the cache
prevents re-normalization.

**Pros**: Directly reduces the most expensive operation (normalization).
absEval is deterministic given the same ctx/seen, so caching is sound.

**Cons**: The cache key must include the context (TyCtx) and possibly
the seen set, or be restricted to closed terms. For closed terms
(the dNat case), ctx=[] and this works well.

## Walk-through: `dzero ⊑ dNat` with Option 1

1. `subCheckNF dzero dNat` — cache miss. Self-intro fires.
2. absEval normalizes the substituted body. During this, it hits domain
   check `dzero_modified ⊑ dzero_original`.
3. `subCheckNF dzero_modified dzero_original` — cache miss. Both normalize
   to the same NfExpr (dzero). After normalization, the key is `(dzero, dzero)`.
   This is reflexively true. **Store `(dzero, dzero) → true`.**
4. absEval continues. Hits another domain check that, after normalization,
   produces key `(dzero, dzero)`. **Cache hit. Return true immediately.**
5. Repeat for dsucc-related checks. Each unique normalized pair is
   computed once.

### Expected speedup

In the dNat case, the substituted body has ~46 mu nodes, each potentially
triggering self-intro. But after normalization, there are only a handful of
distinct pairs (dzero ⊑ dzero, dsucc ⊑ dsucc, etc.). With memoization,
each is computed once instead of being re-derived through cascading
substitution.

## Walk-through: `dzero ⊑ dNat` with Option 4

1. Self-intro substitutes dzero for dNat in the body → 635-node term.
2. absEval starts processing the letE chain. Each let-bound value
   (dzero_expanded, dsucc_expanded) gets normalized.
3. `absEval dzero_expanded` — cache miss. Normalizes to dzero. **Store.**
4. Later, another sub-expression produces dzero_expanded (or a copy with
   identical structure). `absEval dzero_expanded` — **cache hit.**
5. Domain checks that depend on these normalized values also complete
   faster because their inputs are already cached.

## Implementation sketch

```lean
-- Thread a memo table through subCheckNF and absEval
abbrev Memo := HashMap (Expr × Expr) Bool

def subCheckNF (fuel : Nat) (ctx : TyCtx) (seen : List (Expr × Expr))
    (memo : Memo) (a b : Expr) : (Bool × Memo) :=
  match memo.find? (a, b) with
  | some result => (result, memo)
  | none =>
    let (result, memo') := ... -- normal subCheckNF logic, threading memo
    (result, memo'.insert (a, b) result)
```

The memo table would need to be threaded through the mutual recursion
between subCheckNF and absEval, which complicates the API. An alternative
is to use a State monad or IO ref.

## Risks

1. **Soundness**: Cached results must be valid in all contexts where they're
   reused. For closed terms (the dNat use case), this is straightforward.
   For open terms, the result may depend on the TyCtx — a pair that's true
   under one context might be false under another. The cache key would need
   to include context-relevant information, or caching should be restricted
   to closed sub-terms.

2. **Memory**: The memo table grows monotonically. For the dNat case this is
   fine (small number of distinct pairs). For larger programs it might need
   eviction or scoping.

3. **Interaction with `seen`**: The `seen` list is path-local cycle detection.
   A memo'd "true" from a previous path might be based on assumptions (via
   `seen`) that don't hold on the current path. Need to be careful not to
   cache results that depended on `seen` assumptions. One safe approach:
   only cache results from calls where `seen = []`.

## Comparison with lazy normalization

Memoization and lazy normalization attack different aspects of the problem:

- **Lazy normalization** avoids doing work that isn't needed for the
  comparison (e.g., normalizing reflexively-equal domains).
- **Memoization** avoids redoing work that's already been done.

They are complementary. Lazy normalization would dramatically reduce the
number of subCheckNF calls generated. Memoization would prevent redundant
calls among whatever remains. In the ideal case, lazy normalization alone
might be sufficient (the dzero ⊑ dNat walk-through suggests it reduces
the check to ~5 trivial operations). Memoization is a safety net for
cases where lazy normalization still produces duplicate work.
