# Investigation: dNat-Based Arrays — Performance Hang

## Context

Session e58a2a19 attempted to rewrite Array/appendArrays using Scott-encoded
dNat instead of Church Nat_. The goal: eliminate the annotation fallback in
subCheckNF by getting branch-specific type info from Scott elimination (in the
succ branch, arr1 is known to be a Pair, so fst_/snd_ domain checks pass).

## What Was Tried

### Changes to Eval.lean (stashed)

1. **`whnf` helper**: Reduces top-level beta-redexes (`(λx. body) val → body[x:=val]`)
   with fuel 10. Used by inferType to see through let-bindings in mu bodies.

2. **`inferType` mu case**: Added `| .mu ann _body => some ann` so inferType
   can determine the type of a raw mu expression (needed for neutral mu apps).

3. **`inferType` self-type unfolding**: Uses `whnf 10 (body.subst 0 f)` instead
   of raw `body.subst 0 f` to reduce let-bindings (like dzero/dsucc inside
   dNat's body) before checking if the unfolded body is a lambda.

4. **Domain-check skip**: When `seen` is non-empty (inside mu body normalization),
   failing domain checks proceed with beta-reduction instead of erroring. This
   breaks circular domain checks (dzero ⊑ dNat inside dNat's own body).

5. **Mu body whnf**: In absEval's `.mu` case, stores `whnf 10 body` instead of
   raw `body`. Reduces let-bindings once at definition time.

### New Definitions (stashed)

- `dadd`: Addition on dNat via mu-recursion
- `dArray`: Length-indexed array using dNat and mu-recursion
- `appendArrays`: Rewritten to eliminate n1 before binding arr1/arr2

### What Worked

- `absEval 50 [] [] dArray` → ok (normalizes the mu itself)
- `absEval 20 [] [] (dArray dzero Nat_)` → ok (concrete application)
- `absEval 20 [] [] (dArray done_ Nat_)` → ok (concrete application)
- `absEval 50 [] [] appendArrays` → ok (normalizes appendArrays itself)
- `disZero`, `dpred`, `dadd` on concrete dNat values → all correct

### What Hangs

- `absEval 50 [] [] target` where target = `λT:Type. λn1:dNat. λn2:dNat. dArray n1 T → dArray n2 T → dArray (dadd n1 n2) T` — **hangs even at fuel 50**
- `subCheck 500 appendArrays target` — hangs (needs to normalize target)

The hang occurs when normalizing a type expression that contains **multiple
dArray/dadd applications with abstract arguments** in the same lambda body.
Each individual dArray/dadd application terminates fine. The combination hangs.

## Root Cause Analysis

### Is It an Infinite Loop?

**No.** Empirically confirmed:
- `absEval 3 [] [] (dArray dzero Nat_)` → "out of fuel" (terminates)
- `absEval 10 [] [] (dArray dzero Nat_)` → ok (terminates)
- All fuel-bounded functions (absEval, subCheckNF) decrement fuel each call
- `whnf` has hardcoded fuel 10, `.subst` is structural recursion
- `inferType` is structural recursion on the Expr (no fuel needed)

### Then Why Does It Hang?

**Exponential term-size blowup from `.subst` on shared definitions.**

The `och{}` macro inlines definitions by value. dNat (~200 chars), dzero (~400
chars), dsucc (~1000 chars), dadd (~2800 chars) each contain full copies of
their dependencies. dArray's body contains dNat, Pair, Unit_, etc.

When absEval normalizes `dArray n1 T → dArray n2 T → dArray (dadd n1 n2) T`
under binders:

1. **First `dArray n1 T`**: mu-app unfolds dArray body. `body.subst 0 mu_expr`
   replaces self-ref with the full dArray mu (~925 chars). Body also contains
   dNat, Pair, etc. Result: ~2-3KB.

2. **Inside the body**: `n1 (λ_:dNat. Type) Unit_ (λpred:dNat. Pair T (dArray pred T))`
   — normalizing the lambda `λpred:dNat. Pair T (dArray pred T)` involves
   normalizing the domain `dNat` (fast) and the body `Pair T (dArray pred T)`.
   The inner `dArray pred T` hits the seen set → neutral. But the Pair
   application creates another large term.

3. **Second `dArray n2 T`**: Same process, independent. Another ~2-3KB result.

4. **`dadd n1 n2`**: dadd mu unfolds. Body contains dsucc and recursive dadd.
   dsucc unfolds to a lambda with domain annotations containing dNat. Result:
   ~5-10KB.

5. **Third `dArray (dadd n1 n2) T`**: dArray applied to the dadd result. Another
   mu unfold + substitution.

Each step creates larger terms. The total is perhaps 20-50KB of expressions.
But each `.subst` call walks the ENTIRE expression tree. And these expressions
are DAGs in Lean's memory (shared references to dNat, etc.), but `.subst`
doesn't know about sharing — it traverses shared sub-trees multiple times.

**A 50KB DAG with sharing depth 5 could have effective size 50KB × 2^5 = 1.6MB
of traversal work per `.subst` call.** With dozens of `.subst` calls during
normalization (one per beta-reduction, one per variable lookup), the total
work becomes gigabytes of traversal — hence the hang.

## Attempted Fixes and Their Issues

### Fix 1: Normalize mu body at definition time (full absEval)
**Result**: Broke subtype checks (`dzero ⊑ dNat = false` instead of true).
The normalized body has different structure than the raw body. subCheckNF's
structural comparison depends on specific syntactic forms.

### Fix 2: whnf mu body at definition time (top-level let-binding reduction)
**Result**: Reduces let-bindings once, avoiding re-expansion. But doesn't help
with the sharing problem — the inlined definitions (dzero, dsucc) still create
large terms that get duplicated by subsequent `.subst` calls.

### Fix 3: Domain-check skip when `seen` non-empty
**Result**: Breaks circular domain checks (dzero ⊑ dNat cycle). Correct
conceptually but doesn't address the term-size issue.

## What Would Actually Fix This

### Short-term: Sharing-aware `.subst`
If `.subst` could recognize shared sub-trees and avoid re-traversing them, the
effective work per substitution would be proportional to the DAG size, not the
tree size. This requires either:
- Hash-consing the Expr type (structural sharing by construction)
- A memo table in `.subst` (detect and skip already-visited sub-trees)

### Medium-term: Environment-based evaluation
Instead of substituting values into terms (creating copies), keep an
environment mapping variables to values. Lookup on demand, never copy.
- `mu_expr` stored as `(body, env)` where env maps self → mu_closure
- Unfolding: extend env, O(1) instead of O(|body|)
- Eliminates ALL copying, not just shared sub-trees

### Long-term: Normalize mu bodies properly
With sharing or environments in place, normalizing mu bodies at definition time
becomes practical. Let-bindings are reduced once. The normalized body is clean
and compact. All downstream operations (inferType, mu-app, subCheckNF) benefit.

## Current State

The stashed changes include all the conceptual fixes (whnf, inferType mu case,
domain-check skip, mu-app with seen set, annotation fallback in subCheckNF).
These work correctly for the Church-nat Array_ (all existing tests pass). They
also work for individual dNat operations. But they can't handle expressions
with multiple dArray/dadd applications due to term-size explosion.

The Church-nat appendArrays test passes via the annotation fallback — which is
circular (trusts the declared type without verifying the body). The dNat
approach was supposed to eliminate this fallback by making body verification
succeed, but it's blocked by the performance issue.

### Stash contents
Stash ref: `stash@{0}` (commit `1b4cbe95`), on top of `6af6c4d`.
Restore with `git stash apply stash@{0}`. View with `git stash show -p`.
Key changes:
- `lean/Och/Eval.lean`: whnf, inferType fixes, domain-check skip, mu body whnf,
  mu-app with seen set + annotation fallback
- `lean/Och/Std/Array.lean`: dNat-based dArray and appendArrays (incomplete)
- `lean/Och/Std/DNat.lean`: dadd definition and tests
