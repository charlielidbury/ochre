# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

---

## 2026-04-05: Fix self-elim seen handling to restore transitivity

**Agent:** ochre-20260405-013043

**Decision:** Changed subCheckNF's self-elim body path to use the original
`seen` (without the self-elim entry) for the final subCheckNF call:
```lean
-- Before:
| .ok u' => subCheckNF fuel ctx seen' u'.val b  -- seen' = (mu, b) :: seen
-- After:
| .ok u' => subCheckNF fuel ctx seen u'.val b   -- original seen
```
The annotation check and absEval call still use `seen'`.

**Why:** The self-elim entry `(mu ann body, b)` in seen' enabled circular
reasoning. For non-productive fixpoints like `mu Type (bvar 0)`, the body
unfolds to the same mu, hits the seen entry, and succeeds trivially —
making `mu Type (bvar 0) ⊑ anything` true. This broke transitivity:
`Type ⊑ mu Type (bvar 0) ⊑ lam Type (bvar 0)` but `Type ⋢ lam Type (bvar 0)`.

**Alternatives considered:**
1. Remove seen from self-elim entirely (breaks absEval cycle detection
   for recursive types during body normalization)
2. Tag seen entries as intro/elim and only match intro entries in the
   seen check (bigger change, harder to maintain)
3. Check for "progress" in body unfolding — reject if normalized body
   equals original mu (too narrow, misses subtle non-productive cases)

**Validation:** All tests pass (DNat, Array, Vec, appendVec, Bool, etc.).
The key insight: well-formed recursive types make PROGRESS when unfolded
(reveal a constructor like lam), so the body path succeeds WITHOUT the
seen entry. Only non-productive fixpoints needed the circular seen hit.

**Impact on proofs:** Fuel_mono (`subCheckNF_self_elim_step`) updated
trivially. Self-elim body path in adequacy_gen is now unblocked from
the circular seen callback dependency — the body check uses the original
seen, so ih_fuel needs only the outer `hseen` callback (already available).

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
