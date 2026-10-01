# 06. Dependent fields

Written 2026-09-30 by team-lead. The user asked why Ochr has no dependent fields, calling their absence "a huge limitation" after the agent-effort benchmark (docs/05) had to pose the hashmap with a fixed capacity. This is the brief for implementing them. The design is arrays-library's (notes/arrays-library.md §3, "K7"); this doc makes it a decision.

## Why Ochr doesn't have them yet
There is no principled obstacle. The restriction is historical:
- **D36 (v1.7).** Constructor fields were restricted to first-order data, "the standard positivity condition in its simplest form". This closed a soundness hole: a Π-typed field let a diverging function type a proof of `0 = 1`. The simplest form also ruled out field types that mention earlier fields, and nothing needed them until arrays.
- **Arrays (D57).** Fixed-length `Array(T, n)` needs none: the length lives in the type. A container whose length changes at runtime (`Vec`, a resizable hashmap table) must store its length next to the array, i.e. `Mk(n : Word, items : Array(T, n))`. That is a dependent field. The arrays work designed the extension and deferred it.

## What makes it different from Lean: mutation
In Lean a structure's fields never change, so a dependent field type is just a telescope. In Ochr a field can be borrowed and written in place, and writing an index field alone *temporarily* breaks the dependency: after `(*v).n := 7`, `items` is still an `Array(T, old n)`. The user's ruling (2026-09-30) is that this must be allowed, or growable vectors cannot be updated in place: `*v.0 := 2; *v.1 := [0,1]` is fine, because `v` is of its Σ type again by the end of the two statements. So the new rule is *open and repack* (below), the same shape as D53's "whole again". The other cost is that `Eq`'s injectivity (D52) needs heterogeneous equality in general, and Ochr restricts it instead (fail-safe, incomplete).

## The rules (from arrays-library §3)
1. **[Ind]** checks the field types as a telescope. Each earlier field is bound to a fresh abstract value, as [Def] binds parameters. Positivity is unchanged: earlier fields occur only as arguments inside later field types. Fields stay first-order data (D36 otherwise unchanged: no Π, no `&`).
2. **Field types are computed from the earlier fields' current contents:** `type(p.items) = Array(T, content(p.n))`. [Split] refines `σ := Mk(σ₁, σ₂)` with `Δ(σ₂) = Array(T, σ₁)`. D62's on-demand one-arm split does the same.
3. **[Open]/[Repack]** (replaces an earlier [Frozen] draft that forbade writing index fields; user ruling 2026-09-30). Writing, moving out of, or borrowing any field of a value of a dependent type *opens* it. While it is open, each field is a place typed by its own content's stored type, not by the telescope. `*v.0 := 2` leaves `v.1 : Array(T, old n)`, and `*v.1 := [0,1]` makes it `Array(T, 2)`. At the D53 "whole again" points the value must be *repacked*: its contents are re-checked against the telescope, with each later field's stored type convertible to its field type computed from the earlier fields' contents. Those points are: a borrow of it ends, the function returns, and the whole value is read, moved, borrowed, passed, observed by `Id`, or captured by a sealed program or stuck block. A repack failure is a type error at that point. Uses of individual fields while open are ordinary (typed by their stored types). No one else can see the open value, since borrows are exclusive. The check compares normal forms of types, not erasure classes, so D35 is untouched. Which fields are index fields is read from the declaration.
4. **Injectivity (D52), restricted.** `Eq D (Mk(v̄)) (Mk(w̄))` decomposes into per-field equations only while the earlier fields on both sides are convertible. Otherwise the equation stays as it is. Proof fields are ⋆ on both sides (D27) and never block.
5. **Unchanged:** [Close], sealed programs, observation, and the set model (Σ-types).

Proof fields (`h : Sorted(xs)`) are the same extension. With open/repack they are in-place too: open the value, mutate `items`, then supply a new proof before the repack point (`*v.h := proof`). The repack checks the proof field's type against the new contents. This is the pattern DLLBC's packed-invariant work needed. It is in scope, but it is the second milestone, after the Σ shape.

## Acceptance
- Checked:
  - `Vec(T) := Mk(n : Word, items : Array(T, n))`, with `Push`/`Pop` by `ArrPush`/`ArrPop` (they exist in the arrays library) and an element borrow `&(*v).items[i]` with a bounds proof against `(*v).n`; (since docs/09 §7 an array never changes its length and `ArrPush`/`ArrPop` are gone; `Vec` is `MkVec(len, cap, buf : Array(Opt(E), cap), hl : Le(len, cap))`, user code, in `18DependentFields.lean`)
  - a resizable hashmap table, `MkHM(cap : Word, slots : Array(Bucket, cap), len : Word)`, with a `Resize` that allocates the new table and re-inserts by recursion over the old index;
  - lemmas about `Push` (the length grows by one, the old elements are unchanged, the new element is last).
- Checked, in-place growth with a temporary break: `*v.0 := Succ(n); *v.1 := ArrPush(T, n, items, x)` in either order, and the user's example `*v.0 := 2; *v.1 := [0,1]`.
- Rejected (negative tests), each with the repack error at the right point:
  - returning with `v` left broken (`*v.0 := 7` alone);
  - reading, moving or passing `*v` whole while it is broken;
  - forming an `Id` over `v` while it is broken;
  - an ill-formed telescope (a later field mentioning a field declared after it).
- The counterfactual ledger has a row per new rule: switching off [Repack] makes the length-lie program (`*v.0 := 7` then return) accepted (soundness); unrestricting injectivity makes an ill-typed `Eq` form (soundness or crash).
- The fuzzer gets a generator family for index-field writes, with an exec/truth acceptance run.
- RULES/DECISIONS (D64, by the lead) and the paper (a paragraph in §3 plus [Open]/[Repack] in the appendix, by prop-paper) land in step with the checker, per the checker-implements-the-paper rule.

## What it unlocks
- The benchmark hashmap (docs/05) can resize, like Aeneas's.
- A user-defined growable vector.
- Invariant fields on immutable data (sorted lists, search trees with bounds).
