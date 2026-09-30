# 06. Dependent fields

Written 2026-09-30 by team-lead. The user asked why Ochr has no dependent fields, calling their absence "a huge limitation" after the agent-effort benchmark (docs/05) had to pose the hashmap with a fixed capacity. This is the brief for implementing them. The design is arrays-library's (notes/arrays-library.md §3, "K7"); this doc makes it a decision.

## Why Ochr doesn't have them yet
There is no principled obstacle. The restriction is historical:
- **D36 (v1.7).** Constructor fields were restricted to first-order data, "the standard positivity condition in its simplest form". This closed a soundness hole: a Π-typed field let a diverging function type a proof of `0 = 1`. The simplest form also ruled out field types that mention earlier fields, and nothing needed them until arrays.
- **Arrays (D57).** Fixed-length `Array(T, n)` needs none: the length lives in the type. A container whose length changes at runtime (`Vec`, a resizable hashmap table) must store its length next to the array, i.e. `Mk(n : Word, items : Array(T, n))`. That is a dependent field. The arrays work designed the extension and deferred it.

## What makes it different from Lean: mutation
In Lean a structure's fields never change, so a dependent field type is just a telescope. In Ochr a field can be borrowed and written in place. If `(*v).n := 7` were allowed, or `&(*v).n` were passed to an opaque callee, `items` would still be an `Array(T, old n)` while claiming length 7. That is the one genuinely new rule ([Frozen] below). The other cost is that `Eq`'s injectivity (D52) needs heterogeneous equality in general, and Ochr restricts it instead (fail-safe, incomplete).

## The rules (from arrays-library §3)
1. **[Ind]** checks the field types as a telescope. Each earlier field is bound to a fresh abstract value, as [Def] binds parameters. Positivity is unchanged: earlier fields occur only as arguments inside later field types. Fields stay first-order data (D36 otherwise unchanged: no Π, no `&`).
2. **Field types are computed from the earlier fields' current contents:** `type(p.items) = Array(T, content(p.n))`. [Split] refines `σ := Mk(σ₁, σ₂)` with `Δ(σ₂) = Array(T, σ₁)`. D62's on-demand one-arm split does the same.
3. **[Frozen].** A field that a later field's type mentions (an *index field*) may not be borrowed, assigned or moved out alone, in any position. The value may only be replaced whole, and [T-Ctor] rechecks it. Reading is fine (a `Word` index is copy). The rule is syntactic: which fields are index fields is read from the declaration.
4. **Injectivity (D52), restricted.** `Eq D (Mk(v̄)) (Mk(w̄))` decomposes into per-field equations only while the earlier fields on both sides are convertible. Otherwise the equation stays as it is. Proof fields are ⋆ on both sides (D27) and never block.
5. **Unchanged:** [Close], sealed programs, observation, and the set model (Σ-types).

Proof fields (`h : Sorted(xs)`) are the same extension, but [Frozen] then freezes the data itself: no element borrows, only whole rebuilds with a new proof. They are allowed, and the paper says what they cost. Invariant-carrying in-place data (a proof field re-checked when a borrow ends) is out of scope.

## Acceptance
- Checked:
  - `Vec(T) := Mk(n : Word, items : Array(T, n))`, with `Push`/`Pop` by `ArrPush`/`ArrPop` (they exist in the arrays library) and an element borrow `&(*v).items[i]` with a bounds proof against `(*v).n`;
  - a resizable hashmap table, `MkHM(cap : Word, slots : Array(Bucket, cap), len : Word)`, with a `Resize` that allocates the new table and re-inserts by recursion over the old index;
  - lemmas about `Push` (the length grows by one, the old elements are unchanged, the new element is last).
- Rejected (negative tests): writing an index field alone (`(*v).n := 7`), borrowing it (`&(*v).n`), moving it out, and passing it to an opaque callee; an ill-formed telescope (a later field mentioning a field declared after it).
- The counterfactual ledger has a row per new rule: switching off [Frozen] makes the length-lie program accepted (soundness); unrestricting injectivity makes an ill-typed `Eq` form (soundness or crash).
- The fuzzer gets a generator family for index-field writes, with an exec/truth acceptance run.
- RULES/DECISIONS (D64, by the lead) and the paper (a paragraph in §3 plus [Frozen] in the appendix, by prop-paper) land in step with the checker, per the checker-implements-the-paper rule.

## What it unlocks
- The benchmark hashmap (docs/05) can resize, like Aeneas's.
- A user-defined growable vector.
- Invariant fields on immutable data (sorted lists, search trees with bounds).
