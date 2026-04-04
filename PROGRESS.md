# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (4 total, down from 5 at session start)

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:171)
- `VCompat.from_self_intro_gen` — Soundness.lean:265 — partially proved, inner sorry needs adequacy
- `VCompat.adequacy` — Soundness.lean:341 — subCheckNF preserves VCompat
- `soundness` (main theorem) — Soundness.lean:365

**Phase 3 (Subtyping helpers):**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — Subtyping.lean:194 — sorry, has app-app congruence bug (see below)

### What happened this session (agent ochre-20260404-201517)

**`VCompat.from_type_sub_gen` is PROVED.** This is the first Phase 2 lemma:
if `subCheckNF fuel ctx seen .type τ = true`, then `VCompat n v τ` for all v, n.

**Key insight: VCompat needs a normalization disjunct.** The core problem was
that VCompat's mu-right disjunct requires `VCompat n v (body.subst 0 (.mu ann body))`
(the raw substitution), but subCheckNF normalizes via absEval before checking.
We get VCompat for the *normalized* form u'.val, not the raw substitution.
This gap is unbridgeable without changing VCompat because:
- VCompat for `.asc` expressions fails (no matching disjunct)
- The raw body from `.mu` can contain `.asc` nodes
- So VCompat for raw ≠ VCompat for normalized

**Solution: added a 9th disjunct to VCompat (Soundness.lean:89-93):**
```lean
∨ (∃ (nfuel : Nat) (nctx : TyCtx) (nseen : List (Expr × Expr)) (τ' : NfExpr),
    absEval nfuel nctx nseen τ = .ok τ' ∧ VCompat n v τ'.val)
```
This says: if τ normalizes to τ' via absEval, then VCompat for τ' implies VCompat
for τ. Semantically sound because normalization preserves type meaning.

**Proof structure for from_type_sub_gen:** Double induction on fuel (outer) and
step index n (inner). For the mu case at step m+1:
1. mu-right disjunct: reduces to VCompat m at the raw substitution
2. normalization disjunct: reduces to VCompat (m-1) at the normalized form u'.val
3. ih_fuel (at fuel k): proves VCompat (m-1) at u'.val from the subCheckNF hypothesis
4. ih_n (at step m): provides VCompat m for the seen callback (handles the circularity
   in equi-recursive type unfolding)

**from_self_intro_gen partially proved.** The proof follows the same structure
(mu-right + normalization), but the inner sorry requires `VCompat m' σ u'.val`
from `subCheckNF k ctx seen' σ u'.val = true`. This is essentially adequacy
(with VCompat.refl as the base case). Once adequacy is proved, from_self_intro_gen
will follow.

**subCheckNF_neutral_inferType has a bug:** For the app-app congruence case,
subCheckNF can succeed via structural congruence (f₁⊑f₂ ∧ a₁⊑a₂) without
inferType firing. The theorem conclusion requires inferType to succeed, which
isn't guaranteed. The theorem needs either an extra precondition excluding
the app-app case, or a disjunctive conclusion handling both congruence and
inferType.

### What's working
- All tests pass (`lake build` succeeds with sorrys only in Subtyping/Soundness)
- appendVec type-checks with abstract arguments
- `concEval_fuel_mono` proved
- `absEval_fuel_mono` proved
- `subCheckNF_fuel_mono` proved
- **`VCompat.from_type_sub_gen` proved** (NEW)
- VCompat.mono (updated for normalization disjunct), VCompat.mono_le, VCompat.refl,
  VCompat.fixpoint_mu, VCompat.self_intro_eq, VCompat.fixpoint_mu_left all proved
- SubtypeCore.trans, Subtype'.trans proved

### Priority
Next agent should work on **VCompat.adequacy** (Soundness.lean:341). This is
the key bridge lemma and the biggest remaining blocker:
- `VCompat n v σ ∧ subCheckNF σ τ = true → VCompat n v τ`
- from_self_intro_gen depends on it (the inner sorry is essentially adequacy)
- The soundness main theorem likely depends on it

Approach for adequacy: case analysis on σ and τ, using VCompat n v σ to determine
what v looks like. Key cases:
- τ = .type: trivial (first disjunct)
- σ = τ: trivial (already have VCompat)
- σ = .type: use from_type_sub_gen (proved!)
- Both lam: decompose subCheckNF domain/body checks, use VCompat lam disjunct
- τ = .mu: use from_type_sub_gen or mu-right + normalization
- σ = .mu: self-elim case, use mu-left disjunct
- Neutral: inferType fallback

The lam-lam case will need the most work: showing that compatible bodies under
the subtype check give compatible results under evaluation.
