# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

---

## 2026-04-05: Move annotation normalization from absEval to subCheckNF

**Agent:** ochre-20260405-020120

**What:** Changed absEval's mu case to keep raw annotations (validate but don't
normalize), and moved annotation normalization to subCheckNF's self-elim
annotation path (normalize on demand before comparing).

**Why:** The annotation normalization mismatch between concEval (keeps raw) and
absEval (normalized) was blocking 5+ sorrys. The soundness mu case needed
VCompat(v, τ) where v = mu ann body (raw) and τ = mu ann'.val body (normalized).
This required proving "annotation normalization congruence" — a deep lemma.

By keeping raw annotations in absEval output, both evaluators produce the same
mu term, making soundness mu trivial by VCompat.refl.

**Impact:** 7 sorrys eliminated (24 → 17). Eliminated the entire "annotation
normalization congruence" blocker from absEval_preserves.

**Alternatives considered:**
- WellAnnotated precondition: would weaken the theorem unnecessarily
- Normalizing in concEval: concEval and absEval handle asc differently, so
  their normalizations would produce different results
- Adding a VCompat disjunct for "same expression with different annotations":
  too invasive, would require updating every VCompat case split

**Risk:** Raw annotations in absEval output mean subCheckNF's self-elim must
normalize on demand. This adds an absEval call to the self-elim annotation
path, changing fuel consumption. All tests pass including the north star
(appendVec). fuel_mono proof updated and fully proved.

---

## 2026-04-05: Fix self-elim to restore transitivity (two changes)

**Agent:** ochre-20260405-013043

**Decision:** Two changes to subCheckNF's self-elim case:

1. Body check uses original `seen` (not `seen'`):
```lean
| .ok u' => subCheckNF fuel ctx seen u'.val b   -- was: seen'
```

2. Annotation path guarded by `body != bvar 0`:
```lean
if body != .bvar 0 && subCheckNF fuel ctx seen' ann b then true
```

**Why (change 1):** The self-elim entry in seen' enabled circular reasoning.
Non-productive fixpoints like `mu Type (bvar 0)` unfold to themselves,
hit the seen entry, and succeed trivially.

**Why (change 2):** Even after change 1, `mu ann (bvar 0) ⊑ ann` succeeded
via the annotation path (ann ⊑ ann by equality). Since mu ann (bvar 0) is
universal (everything subtypes it via self-intro), this created a bridge for
transitivity violations: `a ⊑ mu ann (bvar 0) ⊑ ann` but `a ⋢ ann`.
Found via exhaustive testing on edge-case expressions.

**Why `body != bvar 0` specifically:** Only pure self-reference bodies are
non-productive. All standard library mus (dNat, dBool, Array, Vec) have
lambda bodies that expose constructor structure when unfolded. The guard
doesn't affect them.

**Alternatives considered:**
1. Validate annotations at mu creation (breaks Church-encoded types)
2. Remove annotation path entirely (breaks DNat/Vec body normalization)
3. Check post-normalization progress instead of syntactic guard
   (changes control flow, harder to maintain)

**Validation:** All tests pass. Added 3 exhaustive transitivity test suites
(~30 expressions × 3 triples each) covering Std types, nested mus, and
self-referential patterns.

**Impact on proofs:** Fuel_mono updated (handle Bool.and in annotation guard).
Self-elim body path in adequacy_gen unblocked from circular callback.

---

## 2026-04-05: Add asc-left disjunct to VCompat

**Agent:** ochre-20260405-003633

**Decision:** Added a 10th disjunct to VCompat:
```lean
∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)
```

**Why:** `absEval_preserves` was FALSE without it. Counterexample:
v = e = `asc (lam Type (bvar 0)) (lam Type Type)`, n=2. VCompat(2, v, v) holds
via refl, but absEval(v) = ok ⟨lam Type Type⟩ and VCompat(2, asc(...), lam Type Type)
had no way to hold — no existing disjunct could handle asc on the value side.

**Semantics:** The disjunct is correct because concEval erases ascriptions —
`(e : τ)` at runtime behaves like `e`. The asc-left disjunct costs one step
(VCompat n+1 → VCompat n) to prevent infinite chains.

**Why it's needed:** mu-left unfolding in adequacy_gen introduces `body.subst 0 (mu ...)`
as the value, and body can contain asc nodes from let-bindings etc.

**Alternatives considered:**
1. Restricting absEval_preserves to v being a concEval output (too narrow —
   mu-left recursion in adequacy_gen passes non-value v's)
2. Adding IsNotAsc precondition (doesn't hold for mu-left unfolded values)
3. Avoiding absEval_preserves entirely (would need completely different proof strategy)

**Impact:** All existing proofs updated (VCompat.mono, bvar_inferType, adequacy_gen).
The asc-left case is always handled by recursion (IH or ih_n).

---

## 2026-04-04: Clear `seen` in structural subCheckNF recursive calls

**Agent:** ochre-20260404-224040

**Decision:** Changed subCheckNF's lam-lam and app-app structural cases to
use empty `seen` `[]` instead of propagating the outer seen set.

**Why:** The outer `seen` set contains equi-recursive assumptions like
(σ, mu ann body) with VCompat callbacks in adequacy_gen tied to the original
value `v`. When the proof needs to recurse into structural sub-components
(e.g., f1→f2 in app-app), the callback would need VCompat for the
*sub-component* (fV), not the original v. This mismatch was the fundamental
blocker for proving app-app structural congruence in adequacy_gen.

By clearing seen in structural recursive calls, the callback becomes vacuous
(empty seen = no callback), enabling the proof.

**Alternatives considered:**
1. Strengthen the seen callback to `∀ v, VCompat n v p.1 → VCompat n v p.2`
   (too strong — fails for from_type_sub_gen)
2. Prove `subCheckNF with seen → subCheckNF with []` (wrong direction — more
   seen pairs make subCheckNF succeed more, not less)
3. Keep the definition and accept the app-app case can't be proved (unacceptable
   — app-app is a core case)

**Validation:** All tests pass including the north star (appendVec). The
structural recursive calls don't benefit from equi-recursive assumptions
anyway — they compare structural sub-parts (domains, bodies, function/arg
components), not the mu types that the seen set tracks.

**Impact:** Enables the app-app structural congruence proof in adequacy_gen
(all 4 VCompat sub-cases). Also prepares the lam-lam case for future work.
Fuel_mono proof required minor update (changing `seen` to `[]` in `show`
clauses).
