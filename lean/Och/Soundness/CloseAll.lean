import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.EvalSubstEquiv

/-!
# Proposal A: `closeAll` — translate level-vars to de-Bruijn indices

This module implements **Proposal A** from `docs/ideas/c7-wall.md` to break
the C7 wall: a translation `closeAll : Nat → Expr → Expr` that, given
`depth = tyCtx.size`, replaces every `bvar (levelOffset + lvl)` (encoded
free level-var) by `bvar (depth - 1 - lvl)` (an ordinary de-Bruijn index
into `tyCtxToCtx tyCtx`).  After `closeAll`, the engine's terms can be
related to `Subtype'` derivations directly via the existing `Subtype'.bvar`
constructor — no schema change needed.

The translation tracks an inner binder counter `c` because the
substitution is applied "outside in": each `bvar (levelOffset + lvl)`
appearing under `c` extra binders should land at index `d - 1 - lvl +
c` in the result, so the contextual reading remains correct.

## What we prove here

* `closeAll_eq` (definition equation that exposes the binder counter).
* `closeAll_levelBvar` — lookup is `Subtype'.bvar`-ready in the
  translated form.  This is the crux that breaks C7.
* `Subtype'_lvar_via_tyCtx` — the post-translation form of the walled
  lemma, *closed* using `Subtype'.bvar` and a small arithmetic identity
  on `tyCtxToCtx`.

## What we do NOT prove here (yet)

The substantive part of Proposal A is the *commutation* between
`closeAll` and the engine's substrate operations:

* `closeAll_substL` — `closeAll d (substL e j s) = ?`
* `closeAll_shiftL` — analogous for shift
* `closeAll_evalSubst` — engine reduction commutes with translation
* `closeAll_openFresh` — openFresh becomes a binder-internal step

These commutation lemmas are deferred and `sorry`'d with precise
statements.  The shape of each is in the spec doc and reflected
below; closing them is what unblocks the full C7 proof in
`SubCheckSubstNeutral.lean`.
-/

namespace Och.Soundness

open SubstEval

/-! ## `tyCtxToCtx`

Translate the engine's level-indexed `tyCtx` to a declarative
de-Bruijn-indexed `Ctx`. The reverse puts level-`(tyCtx.size-1)` at
index 0 (innermost binder).

Previously lived in `SubCheckSubstNeutral.lean`; moved here so the
arithmetic lemmas about `closeAll`'s output indices can sit
alongside.  `SubCheckSubstNeutral.lean` re-exports via `import`. -/

/-- Translate the engine's level-indexed `tyCtx` to a declarative
    de-Bruijn-indexed `Ctx`. -/
def tyCtxToCtx (tyCtx : Array Expr) : Ctx := tyCtx.toList.reverse

/-! ## The `closeAll` translation

`closeAllAt c d e` substitutes `bvar (levelOffset + lvl)` with
`bvar (d - 1 - lvl + c)` for every `lvl < d`.  The counter `c`
tracks how many binders we've descended under — it shifts the
target index up by one per binder.

Level-vars `lvl ≥ d` are unmapped (they shouldn't appear in
well-typed inputs at this depth, but we leave them in place rather
than crashing).

Ordinary bvars `k < levelOffset` are left in place: they're already
in the right de-Bruijn-index regime.  (The level-var encoding
guarantees `k < levelOffset` whenever `k` is a bound index — the
two index spaces are disjoint by construction.) -/

/-- Auxiliary structurally-recursive form of `closeAll` exposing the
    inner binder counter `c`.  `closeAllAt c d e` is `closeAll d e`
    with `c` extra binders crossed. -/
def closeAllAt (c d : Nat) : Expr → Expr
  | .bvar k =>
      if k ≥ levelOffset then
        let lvl := k - levelOffset
        if lvl < d then .bvar (d - 1 - lvl + c) else .bvar k
      else .bvar k
  | .lam dom body => .lam (closeAllAt c d dom) (closeAllAt (c + 1) d body)
  | .iota ann body => .iota (closeAllAt c d ann) (closeAllAt (c + 1) d body)
  | .fix ann body => .fix (closeAllAt c d ann) (closeAllAt (c + 1) d body)
  | .letE val body => .letE (closeAllAt c d val) (closeAllAt (c + 1) d body)
  | .app f a => .app (closeAllAt c d f) (closeAllAt c d a)
  | .asc t ty => .asc (closeAllAt c d t) (closeAllAt c d ty)
  | .type => .type
  | .bot => .bot

/-- `closeAll d e`: translate every encoded level-var `bvar
    (levelOffset + lvl)` (with `lvl < d`) into `bvar (d - 1 - lvl)`.
    Ordinary bvars and out-of-range level-vars are unchanged. -/
def closeAll (d : Nat) (e : Expr) : Expr := closeAllAt 0 d e

/-! ## Basic equations -/

@[simp] theorem closeAllAt_type (c d : Nat) : closeAllAt c d .type = .type := rfl
@[simp] theorem closeAllAt_bot (c d : Nat) : closeAllAt c d .bot = .bot := rfl

theorem closeAllAt_lam (c d : Nat) (dom body : Expr) :
    closeAllAt c d (.lam dom body)
      = .lam (closeAllAt c d dom) (closeAllAt (c + 1) d body) := rfl

theorem closeAllAt_app (c d : Nat) (f a : Expr) :
    closeAllAt c d (.app f a)
      = .app (closeAllAt c d f) (closeAllAt c d a) := rfl

/-- A free level-var translates to its de-Bruijn-index image. -/
theorem closeAllAt_levelBvar (c d lvl : Nat) (hlvl : lvl < d) :
    closeAllAt c d (.bvar (levelOffset + lvl)) = .bvar (d - 1 - lvl + c) := by
  simp only [closeAllAt]
  have hge : levelOffset + lvl ≥ levelOffset := Nat.le_add_right _ _
  have hsub : (levelOffset + lvl) - levelOffset = lvl := by omega
  simp only [hge, ↓reduceIte, hsub]
  simp [hlvl]

/-- Specialisation at the top-level `c = 0`. -/
theorem closeAll_levelBvar (d lvl : Nat) (hlvl : lvl < d) :
    closeAll d (.bvar (levelOffset + lvl)) = .bvar (d - 1 - lvl) := by
  simp [closeAll, closeAllAt_levelBvar 0 d lvl hlvl]

/-- An ordinary (non-level) bvar is unchanged by `closeAllAt`. -/
theorem closeAllAt_bvar_lt_levelOffset (c d k : Nat) (hk : k < levelOffset) :
    closeAllAt c d (.bvar k) = .bvar k := by
  simp only [closeAllAt]
  have : ¬ k ≥ levelOffset := by omega
  simp [this]

/-! ## `tyCtxToCtx` lookup arithmetic

For `tyCtx : Array Expr` of size `d`, `tyCtxToCtx tyCtx =
tyCtx.toList.reverse` has length `d`, and looking up index `d - 1 -
lvl` (the closed form of level `lvl`) should retrieve `tyCtx[lvl]`.
-/

theorem tyCtxToCtx_length (tyCtx : Array Expr) :
    (tyCtxToCtx tyCtx).length = tyCtx.size := by
  simp [tyCtxToCtx]

theorem tyCtxToCtx_get?_at (tyCtx : Array Expr) (lvl : Nat)
    (hlvl : lvl < tyCtx.size) :
    (tyCtxToCtx tyCtx).get? (tyCtx.size - 1 - lvl) = tyCtx[lvl]? := by
  -- `tyCtxToCtx tyCtx = tyCtx.toList.reverse`.  Indexing reversed list
  -- at position `n - 1 - i` retrieves the original list at position `i`.
  simp only [tyCtxToCtx, List.get?_eq_getElem?]
  rw [List.getElem?_reverse]
  · -- Goal: `tyCtx.toList[tyCtx.toList.length - 1 - (tyCtx.size - 1 - lvl)]?
    --        = tyCtx[lvl]?`
    have hlen : tyCtx.toList.length = tyCtx.size := by simp
    rw [hlen]
    have hidx : tyCtx.size - 1 - (tyCtx.size - 1 - lvl) = lvl := by omega
    rw [hidx]
    -- Now: `tyCtx.toList[lvl]? = tyCtx[lvl]?`.  These are equal:
    -- both are `Array.getElem?` on the same data.
    simp only [Array.getElem?_toList]
  · -- Index bound: `tyCtx.size - 1 - lvl < tyCtx.toList.length`.
    simp; omega

/-! ## The lemma that breaks the C7 wall

After translation by `closeAll`, the level-var `bvar (levelOffset +
lvl)` becomes `bvar (depth - 1 - lvl)`, and that index lives in the
range `[0, depth)` covered by `tyCtxToCtx tyCtx`.  Lookup yields
`tyCtx[lvl]`, which is what the engine recorded.  `Subtype'.bvar`
gives us the derivation.

The conclusion has a `(k+1)`-shift on `τ`: the standard de-Bruijn
correction for using a context entry at the current depth.  In the
top-level use (where `closeAll` has already been applied), this
shift is real arithmetic — but it's exactly the rule's natural
schema, so the lemma goes through.
-/

/-- **Wall broken**: the closed form of the C7 walled lemma.  Now
    provable directly via `Subtype'.bvar` + `tyCtxToCtx` arithmetic.

    The conclusion is stated against a shifted `τ`, which is what
    `Subtype'.bvar` natively produces.  The bridge to the engine's
    "`tyCtx[lvl]?  = some ty` ⇒ `Subtype' ... a ty`" pattern requires
    propagating this shift through the seen-list / tyCtx
    well-formedness invariant; that propagation is the C8 stitching
    work, NOT a wall on Proposal A. -/
theorem Subtype'_lvar_via_tyCtx
    {S : Seen} {tyCtx : Array Expr} {lvl : Nat} {ty : Expr}
    (hlvl : lvl < tyCtx.size)
    (h : tyCtx[lvl]? = some ty) :
    Subtype' S (tyCtxToCtx tyCtx)
      (closeAll tyCtx.size (.bvar (SubstEval.levelOffset + lvl)))
      (ty.shift (tyCtx.size - 1 - lvl + 1) 0) := by
  rw [closeAll_levelBvar tyCtx.size lvl hlvl]
  -- Goal: `Subtype' S (tyCtxToCtx tyCtx) (.bvar (tyCtx.size-1-lvl))
  --                    (ty.shift (tyCtx.size-1-lvl+1) 0)`.
  apply Subtype'.bvar
  rw [tyCtxToCtx_get?_at tyCtx lvl hlvl]
  exact h

/-! ## Substrate commutation lemmas (DEFERRED)

These are the substantive Proposal-A obligations beyond the
level-var translation itself.  Each captures how `closeAll`
interacts with one engine substrate operation; closing them all
unlocks the full neutral-arm soundness in
`SubCheckSubstNeutral.lean`.

We document precise statements; bodies are `sorry` with comments
on the proof shape.  These are the highest-value lemmas to attempt
next — each is structurally inductive and the level-var arms
should commute cleanly because both `closeAll` and `shiftL`/`substL`
*ignore* the level-var encoding in compatible ways.

### Lemma `closeAllAt_shiftL`

`shiftL` and `closeAllAt` should commute: shifting up to the same
binder counter on either side gives the same result, modulo
arithmetic on the indices that the level-var arm produces.

The non-trivial case is `bvar k` with `k ≥ levelOffset`:
* `shiftL` keeps the bvar (level-vars are immune to shift).
* `closeAllAt` produces `.bvar (d - 1 - lvl + c)`.

After shifting:
* LHS: `closeAllAt c d (shiftL d' c' (.bvar (levelOffset + lvl)))
      = closeAllAt c d (.bvar (levelOffset + lvl))
      = .bvar (d - 1 - lvl + c)`.
* RHS: `shiftL d' c' (closeAllAt c d (.bvar (levelOffset + lvl)))
      = shiftL d' c' (.bvar (d - 1 - lvl + c))`.

For these to be equal, we need `c' = c` (the cutoff matches the
binder counter) and the result `.bvar (d - 1 - lvl + c)` to be
either preserved (if `< c'`) or shifted (if `≥ c'`).  The
binder-counter discipline plus the cutoff pattern in `shiftL`'s
recursion makes this work; see `shiftL_eq_shift_bvarLT` in
`EvalSubstLemmas.lean` for the analogous pattern at level
`shiftL` ↔ `Expr.shift`.

### Lemma `closeAllAt_substL`

`substL` and `closeAllAt` commute when `j` corresponds to the
binder counter (i.e., the bvar being substituted is "local" to a
binder we've descended under).  The key arithmetic identity is
the same as `closeAllAt_shiftL`; the substitutee `s` itself gets
translated by `closeAllAt c d`.

### Lemma `closeAllAt_openFresh`

`openFresh body lvl` substitutes `bvar (levelOffset + lvl)` for
the outermost binder.  After `closeAll (lvl+1)`:
  - the outermost binder of `body` corresponds to `lvl`,
  - the level-var `bvar (levelOffset + lvl)` translates to
    `bvar 0` (the new innermost binder of the closed form).

So `closeAll (lvl+1) (openFresh body lvl)` should equal
`closeAllAt 1 (lvl+1) body` (= `closeAll (lvl+1) body` modulo the
binder counter we've already crossed).  This is the lemma that
glues the `lam`/`iota`/`fix` arm of `subCheckSubst` to the
declarative `lam`/`iota`/`fix` rule.
-/

/-! ## Headroom predicate `bvarLTOrLvl`

The substrate-level predicate `Expr.bvarLT m e` (defined in
`EvalSubstLemmas.lean`) requires *every* bvar `< m`.  That fails on
terms with level-vars (bvars `≥ levelOffset`), which is exactly the
regime `closeAll` operates in.

We define the natural variant: `bvarLTOrLvl m e` says every bvar `k`
in `e` satisfies `k < m ∨ k ≥ levelOffset`.  Ordinary bvars are
bounded; level-vars are allowed unrestricted.  This is the
operational invariant for `closeAll`-aware proofs: it's preserved
across substrate operations (`shiftL`/`substL` skip level-vars and
shift ordinary bvars by amounts whose total stays below
`levelOffset`).

It's exactly `closedAtLvl` of `Och/EvalSubst.lean` but with a uniform
bound (no per-binder increment).  We expose it under a fresh name to
keep the substitution-arithmetic invariants separate from the
closedness invariants. -/

/-- `bvarLTOrLvl m e`: every bvar `k` in `e` is either `< m` or a
    free level-var (`≥ levelOffset`).  Uniform across binders, unlike
    `closedAtLvl`. -/
def _root_.Expr.bvarLTOrLvl (m : Nat) : Expr → Bool
  | .bvar k => k < m || k ≥ levelOffset
  | .lam dom body => Expr.bvarLTOrLvl m dom && Expr.bvarLTOrLvl m body
  | .app f a => Expr.bvarLTOrLvl m f && Expr.bvarLTOrLvl m a
  | .asc t ty => Expr.bvarLTOrLvl m t && Expr.bvarLTOrLvl m ty
  | .type => true
  | .bot => true
  | .iota ann body => Expr.bvarLTOrLvl m ann && Expr.bvarLTOrLvl m body
  | .fix ann body => Expr.bvarLTOrLvl m ann && Expr.bvarLTOrLvl m body
  | .letE val body => Expr.bvarLTOrLvl m val && Expr.bvarLTOrLvl m body

/-- `bvarLTOrLvl` is monotone in the bound. -/
theorem bvarLTOrLvl_mono {e : Expr} {m m' : Nat}
    (h : e.bvarLTOrLvl m = true) (hle : m ≤ m') : e.bvarLTOrLvl m' = true := by
  induction e generalizing m m' with
  | bvar k =>
    simp only [Expr.bvarLTOrLvl, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    omega
  | type => simp [Expr.bvarLTOrLvl]
  | bot => simp [Expr.bvarLTOrLvl]
  | lam _ _ ih_dom ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_dom h.1 hle, ih_body h.2 hle⟩
  | app _ _ ih_f ih_a =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f h.1 hle, ih_a h.2 hle⟩
  | asc _ _ ih_t ih_y =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t h.1 hle, ih_y h.2 hle⟩
  | iota _ _ ih_ann ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hle, ih_body h.2 hle⟩
  | fix _ _ ih_ann ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hle, ih_body h.2 hle⟩
  | letE _ _ ih_val ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_val h.1 hle, ih_body h.2 hle⟩

/-! ### `closeAllAt_shiftL`: lockstep commutation with shift

The right form of the lemma turned out to be more subtle than the
spec doc suggested.  At a level-var `bvar (levelOffset + lvl)`,
`shiftL d' c' (closeAllAt c d (.bvar (levelOffset + lvl)))` produces
`bvar (d - 1 - lvl + c + d')` (the closed image got shifted up by
`d'`), but `closeAllAt c d (shiftL d' c' (.bvar (levelOffset + lvl)))
= closeAllAt c d (.bvar (levelOffset + lvl)) = bvar (d - 1 - lvl + c)`
— the shiftL skipped the level-var.  These differ by `d'`.

So the lemma must instead put `c + d'` on the LHS:
`closeAllAt (c + d') d (shiftL d' c' e) = shiftL d' c' (closeAllAt c d e)`,
under the side condition `c' ≤ c` (the shift cutoff is "inside" the
binder counter — true for the canonical use case `c' = 0, c ≥ 0`).

This commutation lemma also needs:
1. **`bvarLT` headroom**: ordinary bvars in `e` must satisfy `k + d'
   < levelOffset`, so shifting doesn't push them into the level-var
   range.
2. **closeAllAt-image headroom**: the closed image `d - 1 - lvl + c`
   must be `< levelOffset` (and `< c'` cases must work out).  In
   practice `d, c ≪ levelOffset`, so this is trivial.

The proof is structurally inductive; ordinary bvar and level-var arms
both reduce via `omega` with the headroom assumptions.  Recursion
through binders bumps `c` and `c'` in lockstep.

**Status**: sorry'd with a tight precondition.  Closing this is the
main remaining substrate engineering for Proposal A; the proof
follows the same shape as `shiftL_eq_shift_bvarLT` in
`EvalSubstLemmas.lean` (≈100 LOC of structural induction with
`omega`-driven arithmetic). -/

/-- `closeAllAt` commutes with `shiftL` when the binder counter on
    the LHS is `c + d'` (matching the shift's effect on the binder
    range).  `c' ≤ c` ensures the shift cutoff is inside the binder
    range.

    Headroom assumption: `m + d ≤ levelOffset` and `m + d' ≤
    levelOffset` and `bvarLT m e = true` (where `m` is some bound),
    so that ordinary bvars don't accidentally cross into the level-var
    range and closed-image bvars stay `< levelOffset`. -/
theorem closeAllAt_shiftL (c d c' d' m : Nat) (e : Expr)
    (hcle : c' ≤ c) (hbnd_d : c + d + d' + e.depth ≤ levelOffset)
    (hb : e.bvarLTOrLvl m = true)
    (hm : m + d' ≤ levelOffset) :
    closeAllAt (c + d') d (shiftL d' c' e) = shiftL d' c' (closeAllAt c d e) := by
  induction e generalizing c c' with
  | bvar k =>
    -- For bvar: depth = 0, so the budget reduces.
    have hbnd_simple : c + d + d' ≤ levelOffset := by
      have : (Expr.bvar k).depth = 0 := rfl
      rw [this] at hbnd_d; omega
    simp only [Expr.bvarLTOrLvl, Bool.or_eq_true, decide_eq_true_eq] at hb
    -- hb : k < m ∨ k ≥ levelOffset.
    rcases hb with hk_lt_m | hk_ge_lo
    · -- Ordinary bvar: k < m ≤ levelOffset - d'.
      have hk_lt : k < levelOffset := by omega
      have hLvl_k : isLevelIdx k = false := by
        simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
          decide_eq_false_iff_not, Nat.not_le]; exact hk_lt
      simp only [shiftL, hLvl_k, Bool.false_eq_true, ↓reduceIte]
      have hk_not_ge : ¬ k ≥ levelOffset := by omega
      have rhs_eq : closeAllAt c d (.bvar k) = .bvar k := by
        simp [closeAllAt, hk_not_ge]
      rw [rhs_eq]
      by_cases hkc : k < c'
      · simp only [hkc, ↓reduceIte]
        have lhs_eq : closeAllAt (c+d') d (.bvar k) = .bvar k := by
          simp [closeAllAt, hk_not_ge]
        rw [lhs_eq]
        simp [shiftL, hLvl_k, hkc]
      · simp only [hkc, ↓reduceIte]
        have hkd_lt : k + d' < levelOffset := by omega
        have hkd_not_ge : ¬ k + d' ≥ levelOffset := by omega
        have lhs_eq : closeAllAt (c+d') d (.bvar (k + d')) = .bvar (k + d') := by
          simp [closeAllAt, hkd_not_ge]
        rw [lhs_eq]
        simp [shiftL, hLvl_k, hkc]
    · -- Level-var: k ≥ levelOffset.
      have hLvl_k : isLevelIdx k = true := by
        simp only [isLevelIdx, decide_eq_true_eq]; exact hk_ge_lo
      simp only [shiftL, hLvl_k, ↓reduceIte]
      simp only [closeAllAt, hk_ge_lo, ↓reduceIte]
      by_cases hlt : k - levelOffset < d
      · -- closeAllAt produces .bvar (d - 1 - (k - levelOffset) + c).
        simp only [hlt, ↓reduceIte]
        -- Inline the image: image = d - 1 - (k - levelOffset) + c.
        have h_image_not_ge_lo : ¬ d - 1 - (k - levelOffset) + c ≥ levelOffset := by
          omega
        have h_image_not_lt_c' : ¬ d - 1 - (k - levelOffset) + c < c' := by
          omega
        have hLvl_image : isLevelIdx (d - 1 - (k - levelOffset) + c) = false := by
          simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
            decide_eq_false_iff_not, Nat.not_le]; omega
        -- Goal: .bvar (d - 1 - (k - levelOffset) + (c + d')) =
        --       shiftL d' c' (.bvar (d - 1 - (k - levelOffset) + c)).
        rw [show shiftL d' c' (.bvar (d - 1 - (k - levelOffset) + c))
              = .bvar (d - 1 - (k - levelOffset) + c + d') from by
            simp only [shiftL, hLvl_image, h_image_not_lt_c',
              Bool.false_eq_true, ↓reduceIte]]
        -- Goal: .bvar (... + (c + d')) = .bvar (... + c + d').  Just associativity.
        have : d - 1 - (k - levelOffset) + (c + d') = d - 1 - (k - levelOffset) + c + d' := by
          omega
        rw [this]
      · -- lvl ≥ d: both sides leave the level-var unchanged.
        simp only [hlt, ↓reduceIte]
        simp only [shiftL, hLvl_k, ↓reduceIte]
  | type => simp [shiftL, closeAllAt]
  | bot => simp [shiftL, closeAllAt]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_dom : c + d + d' + dom.depth ≤ levelOffset := by
      have : (Expr.lam dom body).depth = Nat.max dom.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : dom.depth ≤ Nat.max dom.depth body.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_body : (c + 1) + d + d' + body.depth ≤ levelOffset := by
      have : (Expr.lam dom body).depth = Nat.max dom.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : body.depth ≤ Nat.max dom.depth body.depth := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_dom c c' hcle hb_dom hb.1]
    rw [show c + d' + 1 = (c + 1) + d' from by omega]
    rw [ih_body (c + 1) (c' + 1) (by omega) hb_body hb.2]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_ann : c + d + d' + ann.depth ≤ levelOffset := by
      have : (Expr.iota ann body).depth = Nat.max ann.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : ann.depth ≤ Nat.max ann.depth body.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_body : (c + 1) + d + d' + body.depth ≤ levelOffset := by
      have : (Expr.iota ann body).depth = Nat.max ann.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : body.depth ≤ Nat.max ann.depth body.depth := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_ann c c' hcle hb_ann hb.1]
    rw [show c + d' + 1 = (c + 1) + d' from by omega]
    rw [ih_body (c + 1) (c' + 1) (by omega) hb_body hb.2]
  | fix ann body ih_ann ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_ann : c + d + d' + ann.depth ≤ levelOffset := by
      have : (Expr.fix ann body).depth = Nat.max ann.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : ann.depth ≤ Nat.max ann.depth body.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_body : (c + 1) + d + d' + body.depth ≤ levelOffset := by
      have : (Expr.fix ann body).depth = Nat.max ann.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : body.depth ≤ Nat.max ann.depth body.depth := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_ann c c' hcle hb_ann hb.1]
    rw [show c + d' + 1 = (c + 1) + d' from by omega]
    rw [ih_body (c + 1) (c' + 1) (by omega) hb_body hb.2]
  | letE val body ih_val ih_body =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_val : c + d + d' + val.depth ≤ levelOffset := by
      have : (Expr.letE val body).depth = Nat.max val.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : val.depth ≤ Nat.max val.depth body.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_body : (c + 1) + d + d' + body.depth ≤ levelOffset := by
      have : (Expr.letE val body).depth = Nat.max val.depth body.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : body.depth ≤ Nat.max val.depth body.depth := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_val c c' hcle hb_val hb.1]
    rw [show c + d' + 1 = (c + 1) + d' from by omega]
    rw [ih_body (c + 1) (c' + 1) (by omega) hb_body hb.2]
  | app f a ih_f ih_a =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_f : c + d + d' + f.depth ≤ levelOffset := by
      have : (Expr.app f a).depth = Nat.max f.depth a.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : f.depth ≤ Nat.max f.depth a.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_a : c + d + d' + a.depth ≤ levelOffset := by
      have : (Expr.app f a).depth = Nat.max f.depth a.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : a.depth ≤ Nat.max f.depth a.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_f c c' hcle hb_f hb.1, ih_a c c' hcle hb_a hb.2]
  | asc t ty ih_t ih_y =>
    simp only [Expr.bvarLTOrLvl, Bool.and_eq_true] at hb
    simp only [shiftL, closeAllAt]
    have hb_t : c + d + d' + t.depth ≤ levelOffset := by
      have : (Expr.asc t ty).depth = Nat.max t.depth ty.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : t.depth ≤ Nat.max t.depth ty.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    have hb_y : c + d + d' + ty.depth ≤ levelOffset := by
      have : (Expr.asc t ty).depth = Nat.max t.depth ty.depth + 1 := rfl
      rw [this] at hbnd_d
      have hmax : ty.depth ≤ Nat.max t.depth ty.depth + 1 := by
        simp [Nat.max_def]; split <;> omega
      omega
    rw [ih_t c c' hcle hb_t hb.1, ih_y c c' hcle hb_y hb.2]

/-! ### `lvarLT`: bound on level-var indices

For the corrected `closeAll_openFresh` lemma we need a freshness
invariant on `body`'s level-vars: every level-var index `lvl'` in
`body` must satisfy `lvl' < lvl` (so that opening with a fresh
level `lvl` doesn't collide with an existing one).

`lvarLT lvl e` says: every `bvar k` in `e` with `k ≥ levelOffset`
satisfies `k - levelOffset < lvl`.  Ordinary bvars are unrestricted.
Uniform across binders (level-vars are absolute, not bvar-relative). -/

def _root_.Expr.lvarLT (lvl : Nat) : Expr → Bool
  | .bvar k => !SubstEval.isLevelIdx k || (k - SubstEval.levelOffset < lvl)
  | .lam dom body => Expr.lvarLT lvl dom && Expr.lvarLT lvl body
  | .app f a => Expr.lvarLT lvl f && Expr.lvarLT lvl a
  | .asc t ty => Expr.lvarLT lvl t && Expr.lvarLT lvl ty
  | .type => true
  | .bot => true
  | .iota ann body => Expr.lvarLT lvl ann && Expr.lvarLT lvl body
  | .fix ann body => Expr.lvarLT lvl ann && Expr.lvarLT lvl body
  | .letE val body => Expr.lvarLT lvl val && Expr.lvarLT lvl body

theorem lvarLT_mono {e : Expr} {lvl lvl' : Nat}
    (h : e.lvarLT lvl = true) (hle : lvl ≤ lvl') : e.lvarLT lvl' = true := by
  induction e with
  | bvar k =>
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by omega)
  | type => simp [Expr.lvarLT]
  | bot => simp [Expr.lvarLT]
  | lam _ _ ih_dom ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_dom h.1, ih_body h.2⟩
  | app _ _ ih_f ih_a =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f h.1, ih_a h.2⟩
  | asc _ _ ih_t ih_y =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t h.1, ih_y h.2⟩
  | iota _ _ ih_ann ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1, ih_body h.2⟩
  | fix _ _ ih_ann ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1, ih_body h.2⟩
  | letE _ _ ih_val ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_val h.1, ih_body h.2⟩

/-! ### `closeAllAt_substL`: a similar wall

By the same off-by-one analysis as `closeAll_openFresh`,
`closeAllAt_substL` also fails as the naive equation in general.

For a level-var `bvar (levelOffset + lvl)` in `e` with `lvl < d - 1`
(strict, so the closeAllAt image is `bvar (d-1-lvl + c)` with `d - 1
- lvl + c > 0`):

* LHS: `closeAllAt c d (substL (.bvar (levelOffset+lvl)) j s)`
  = `closeAllAt c d (.bvar (levelOffset+lvl))` (substL skips
  level-vars) = `.bvar (d - 1 - lvl + c)`.
* RHS: `substL (closeAllAt c d (.bvar (levelOffset+lvl))) j
  (closeAllAt c d s)` = `substL (.bvar (d - 1 - lvl + c)) j _`.
  When `j = 0` and `d - 1 - lvl + c > 0`, this decrements the bvar
  to `.bvar (d - 1 - lvl + c - 1)`.  **Off by 1**.

The fundamental issue: `substL` decrements bvars `> j` (because
it eliminates the binder at `j`).  `closeAll`'s image places
level-vars at de-Bruijn indices, which `substL` then tries to
decrement.

**Conclusion**: same wall as `closeAll_openFresh`.  Both lemmas
require either:
* a `substL`-variant that doesn't decrement (and a proof that the
  engine's `substL` agrees on the relevant regime), or
* a closeAll variant that itself decrements appropriately under
  `substL`'s recursion pattern.

We sorry this lemma; see the agent report.
-/

/-- **WALL v2**: closeAllAt-substL commutation for arbitrary `s`.

    The naive statement is provably **false** on any term with level-
    vars and `d - 1 - lvl + c > j`: substL's decrement on the closed
    image causes an off-by-one.  No hypothesis on `(c, d, j)` rescues
    the equation; the off-by-one is structural.

    However, the *useful* case — where `s` is itself a level-var
    (`s = levelBvar lvl_s`) — is handled by
    `closeAllAt_substL_levelBvar` (lockstep `c = j`, RHS uses
    `closeAllAt (j+1) lvl_s`).

    For arbitrary `s` (e.g. iota_intro's substituee = LHS spine), this
    sorry remains.  See `docs/ideas/proposalA-wall-v2.md` for the
    detailed analysis and resolution options.

    Currently UNUSED in proofs.  Retained as a marker. -/
theorem closeAllAt_substL_OPEN_QUESTION (c d j : Nat) (e s : Expr)
    (_hj : j < c ∨ c = 0) :
    closeAllAt c d (substL e j s) = substL (closeAllAt c d e) j (closeAllAt c d s) := by
  -- See `docs/ideas/proposalA-wall-v2.md`: off-by-one between substL's
  -- decrement and closeAllAt's image at de-Bruijn indices.  The naive
  -- equation is genuinely false; correct restatements need either
  -- engine refactor (Option A) or a substituee-shift correction that
  -- itself fails on the substitution point.
  sorry

/-! ### `closeAll_openFresh`: open commutes with closeAll modulo well-scoping

The naive equation `closeAll (lvl + 1) (openFresh body lvl) =
closeAllAt 1 (lvl + 1) body` is **false** in general, due to a
fundamental mismatch:

* `openFresh body lvl = substL body 0 (levelBvar lvl)` *decrements*
  ordinary bvars `> 0` in `body` (because `substL` eliminates the
  binder at position 0).
* `closeAllAt 1 d body` (the structural traversal) *preserves*
  ordinary bvars; only level-vars get translated.

Counterexample: `body = .bvar 1`.
* `openFresh body lvl = .bvar 0` (decremented).  `closeAll (lvl+1)
  (.bvar 0) = .bvar 0`.
* `closeAllAt 1 (lvl+1) (.bvar 1) = .bvar 1` (ordinary bvar, `c = 1`,
  unchanged).

These differ on outer references.

**Well-scoping fix**: under the assumption `body.bvarLTOrLvl 1 = true`
(every ordinary bvar in `body` is `< 1`, i.e., only `.bvar 0` is
allowed; level-vars are unrestricted), the equation does hold.  This
is exactly the well-scoped invariant for a binder body that's been
descended into once — the standard precondition in locally-nameless
formulations.

Concretely, with the well-scoping precondition, body has only:
* `.bvar 0` — the binder being eliminated;
* `.bvar (levelOffset + lvl')` for various `lvl' < lvl + 1` — free
  level-vars.

For each:
* `.bvar 0`: openFresh substitutes with `levelBvar lvl`; closeAll
  translates that to `.bvar 0`.  RHS: closeAllAt 1 (lvl+1) leaves
  `.bvar 0` unchanged.  ✓
* `.bvar (levelOffset + lvl')` (lvl' < lvl + 1): openFresh skips;
  closeAll translates to `.bvar (lvl + 1 - 1 - lvl') = .bvar (lvl
  - lvl')`.  RHS: closeAllAt 1 (lvl+1) translates to `.bvar (lvl +
  1 - 1 - lvl' + 1) = .bvar (lvl - lvl' + 1)`.  **Off by 1**.

Wait, even with well-scoping, level-vars don't match!  This is the
real issue.

**Conclusion**: `closeAll_openFresh` as a single-equation lemma is
not the right shape.  The right lemma is at the **Subtype'-level**:
some bridging derivation that says "the engine's recursive call on
opened body, after `closeAll`, derives the same Subtype' as the
structural lam rule applied to the closed body".

This is research-grade: it requires either (a) shifting closeAllAt
under-binder semantics to *also* increment outer bvars (matching
openFresh's decrement, by applying the inverse `shiftL 1 0` once);
or (b) reformulating the engine's openFresh to NOT decrement (a
substantive change).

We sorry this lemma with the issue clearly documented.  See the
agent report and `docs/ideas/c7-wall.md` updates.

-- Open question: is there a closeAllAt variant `closeAllAt' c d e`
-- that *does* match openFresh's semantics?  Specifically: under a
-- binder, ordinary bvars' translation behaviour changes from
-- "preserve" to "decrement-and-translate-from-deeper-context".
-- Such a variant might recover the equation.
-/

/-! ### `closeAll_openFresh` — the corrected equation (CLOSED)

**Resolution to the wall.**  The originally-stated equation
`closeAll (lvl+1) (openFresh body lvl) = closeAllAt 1 (lvl+1) body`
is *provably false* (off by 1 on level-vars).  But the equation we
*actually need* for soundness — to relate the post-`openFresh`
recursive call to the structural lam/iota/fix subterm — is

    closeAll (lvl+1) (openFresh body lvl) = closeAllAt 1 lvl body

i.e., the RHS uses `closeAllAt 1 lvl`, NOT `closeAllAt 1 (lvl+1)`.
Concretely, on a level-var `levelBvar lvl'` (with `lvl' < lvl`):

* LHS: `openFresh` skips, `closeAll (lvl+1)` produces
  `bvar (lvl+1 - 1 - lvl') = bvar (lvl - lvl')`.
* RHS (corrected): `closeAllAt 1 lvl (levelBvar lvl') = bvar
  (lvl - 1 - lvl' + 1) = bvar (lvl - lvl')`.  ✓

The `+1` on the binder counter exactly cancels the `−1` from
`d − 1 − lvl'` shifting, because `d` itself is reduced from `lvl+1`
to `lvl`.

This makes intuitive sense: when we "open" the binder, we drop
the `+1` from `d`, but compensate with `+1` on the binder counter
because we've conceptually descended into the binder.  In the
original (incorrect) statement, `d` and `c` both increased,
double-counting.

The proof is a generalized inductive helper on `j` (substL position
= closeAllAt counter = same value, lockstep), with hypotheses:
  * `body.closedAtLvl (j+1) = true` — body's ordinary bvars are
    `≤ j`; ensures `substL` only substitutes (doesn't decrement).
  * `body.lvarLT lvl = true` — body's level-vars are `< lvl`;
    ensures `closeAllAt` translation is uniform across both sides.
-/

/-- **Helper**: `closeAllAt` and `substL` of a level-var commute when
    the substL position equals the closeAllAt binder counter (lockstep).
    The level-var being substituted matches the closeAllAt depth bump
    on the RHS — so the LHS's `closeAllAt j (lvl+1)` produces the same
    image as the RHS's `closeAllAt (j+1) lvl`.

    Hypotheses:
    * `body.closedAtLvl (j+1) = true` rules out bvars `> j`, which
      `substL` would decrement (causing the off-by-one).
    * `body.lvarLT lvl = true` rules out level-vars `≥ lvl`, which
      `closeAllAt (j+1) lvl` would leave alone but
      `closeAllAt j (lvl+1)` would translate. -/
theorem closeAllAt_substL_levelBvar (body : Expr) (j lvl : Nat)
    (hcl : body.closedAtLvl (j + 1) = true)
    (hlv : body.lvarLT lvl = true) :
    closeAllAt j (lvl + 1) (substL body j (.bvar (SubstEval.levelOffset + lvl)))
      = closeAllAt (j + 1) lvl body := by
  induction body generalizing j with
  | bvar k =>
    simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at hcl
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hlv
    simp only [substL]
    by_cases hLvl : SubstEval.isLevelIdx k
    · -- Level-var case.
      have hkge : k ≥ SubstEval.levelOffset := by
        simpa [SubstEval.isLevelIdx] using hLvl
      simp only [hLvl, ↓reduceIte]
      have hk_lvl_lt : k - SubstEval.levelOffset < lvl := by
        rcases hlv with h_not_lvl | h_bound
        · exact absurd hkge (by simpa [SubstEval.isLevelIdx] using h_not_lvl)
        · exact h_bound
      -- LHS: closeAllAt j (lvl+1) (.bvar k) with k ≥ levelOffset, lvl' < lvl < lvl+1.
      have hLHS : closeAllAt j (lvl + 1) (.bvar k) =
          .bvar (lvl + 1 - 1 - (k - SubstEval.levelOffset) + j) := by
        have hlt : k - SubstEval.levelOffset < lvl + 1 := by omega
        have := closeAllAt_levelBvar j (lvl + 1) (k - SubstEval.levelOffset) hlt
        rw [show SubstEval.levelOffset + (k - SubstEval.levelOffset) = k from by omega] at this
        exact this
      rw [hLHS]
      -- RHS: closeAllAt (j+1) lvl (.bvar k) with k ≥ levelOffset, lvl' < lvl.
      have hRHS : closeAllAt (j + 1) lvl (.bvar k) =
          .bvar (lvl - 1 - (k - SubstEval.levelOffset) + (j + 1)) := by
        have := closeAllAt_levelBvar (j + 1) lvl (k - SubstEval.levelOffset) hk_lvl_lt
        rw [show SubstEval.levelOffset + (k - SubstEval.levelOffset) = k from by omega] at this
        exact this
      rw [hRHS]
      -- Both indices: lvl - (k - levelOffset) + j.
      have : lvl + 1 - 1 - (k - SubstEval.levelOffset) + j
           = lvl - 1 - (k - SubstEval.levelOffset) + (j + 1) := by omega
      rw [this]
    · -- Ordinary bvar case.  k < levelOffset.
      have hk_lt_lo : k < SubstEval.levelOffset := by
        simpa [SubstEval.isLevelIdx] using hLvl
      simp only [hLvl, Bool.false_eq_true, ↓reduceIte]
      -- closedAtLvl (j+1) tells us k < j+1 or k ≥ levelOffset; the latter is excluded.
      have hk_le_j : k ≤ j := by
        rcases hcl with h1 | h2
        · omega
        · omega
      by_cases heq : k = j
      · -- substL substitutes with levelBvar lvl.
        subst heq
        simp only [beq_self_eq_true, ↓reduceIte]
        -- LHS becomes closeAllAt k (lvl+1) (.bvar (levelOffset + lvl))
        -- = bvar (lvl+1-1-lvl + k) = bvar k.
        have hLHS := closeAllAt_levelBvar k (lvl + 1) lvl (by omega)
        rw [hLHS]
        -- RHS: closeAllAt (k+1) lvl (.bvar k) with k < levelOffset, so .bvar k.
        rw [closeAllAt_bvar_lt_levelOffset (k + 1) lvl k hk_lt_lo]
        -- Goal: .bvar (lvl+1-1-lvl+k) = .bvar k.
        congr 1; omega
      · -- k ≠ j, so k < j.
        have hk_lt_j : k < j := by omega
        have hbeq : (k == j) = false := by simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have hk_not_gt : ¬ k > j := by omega
        simp only [hk_not_gt, ↓reduceIte]
        -- Both sides leave .bvar k unchanged.
        rw [closeAllAt_bvar_lt_levelOffset j (lvl + 1) k hk_lt_lo]
        rw [closeAllAt_bvar_lt_levelOffset (j + 1) lvl k hk_lt_lo]
  | type => simp [substL, closeAllAt]
  | bot => simp [substL, closeAllAt]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    have hshift : SubstEval.shiftL 1 0 (.bvar (SubstEval.levelOffset + lvl))
        = .bvar (SubstEval.levelOffset + lvl) := by
      simp [SubstEval.shiftL, SubstEval.isLevelIdx]
    rw [hshift]
    rw [ih_dom j hcl.1 hlv.1, ih_body (j + 1) (by simpa using hcl.2) hlv.2]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    have hshift : SubstEval.shiftL 1 0 (.bvar (SubstEval.levelOffset + lvl))
        = .bvar (SubstEval.levelOffset + lvl) := by
      simp [SubstEval.shiftL, SubstEval.isLevelIdx]
    rw [hshift]
    rw [ih_ann j hcl.1 hlv.1, ih_body (j + 1) (by simpa using hcl.2) hlv.2]
  | fix ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    have hshift : SubstEval.shiftL 1 0 (.bvar (SubstEval.levelOffset + lvl))
        = .bvar (SubstEval.levelOffset + lvl) := by
      simp [SubstEval.shiftL, SubstEval.isLevelIdx]
    rw [hshift]
    rw [ih_ann j hcl.1 hlv.1, ih_body (j + 1) (by simpa using hcl.2) hlv.2]
  | letE val body ih_val ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    have hshift : SubstEval.shiftL 1 0 (.bvar (SubstEval.levelOffset + lvl))
        = .bvar (SubstEval.levelOffset + lvl) := by
      simp [SubstEval.shiftL, SubstEval.isLevelIdx]
    rw [hshift]
    rw [ih_val j hcl.1 hlv.1, ih_body (j + 1) (by simpa using hcl.2) hlv.2]
  | app f a ih_f ih_a =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    rw [ih_f j hcl.1 hlv.1, ih_a j hcl.2 hlv.2]
  | asc t ty ih_t ih_y =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [substL, closeAllAt]
    rw [ih_t j hcl.1 hlv.1, ih_y j hcl.2 hlv.2]

/-- **Wall broken (Option D)**: corrected `closeAll_openFresh`.

The post-Proposal-A C7 use case needs `closeAll (lvl+1) (openFresh
body lvl) = closeAllAt 1 lvl body`, *not* `closeAllAt 1 (lvl+1) body`
(the original OPEN_QUESTION shape, which is provably false).

With the corrected RHS, the equation holds under the natural
preconditions: body's ordinary bvars are `≤ 0` (i.e., only `bvar 0`,
the binder being eliminated), and body's level-vars are all `< lvl`
(freshness).  The proof is a one-line specialization of
`closeAllAt_substL_levelBvar` at `j = 0`. -/
theorem closeAll_openFresh (body : Expr) (lvl : Nat)
    (hcl : body.closedAtLvl 1 = true)
    (hlv : body.lvarLT lvl = true) :
    closeAll (lvl + 1) (SubstEval.openFreshTop body lvl)
      = closeAllAt 1 lvl body := by
  have h := closeAllAt_substL_levelBvar body 0 lvl hcl hlv
  -- Unfold closeAll (= closeAllAt 0) and openFreshTop on the LHS.
  -- `openFreshTop body lvl = substL body 0 (levelBvar lvl)`; level-vars are
  -- structurally `bvar (levelOffset + lvl)`.
  have h_open : SubstEval.openFreshTop body lvl
      = SubstEval.substL body 0 (.bvar (SubstEval.levelOffset + lvl)) := by
    rfl
  rw [closeAll, h_open]
  exact h

/-- Backwards-compatible alias retaining the OPEN_QUESTION name with
    the corrected statement.  See `closeAll_openFresh` for the proof.

    The original statement (with `closeAllAt 1 (lvl+1) body`) was
    provably false; the corrected statement uses `closeAllAt 1 lvl
    body`, which is what soundness actually wants. -/
theorem closeAll_openFresh_OPEN_QUESTION (body : Expr) (lvl : Nat)
    (hcl : body.closedAtLvl 1 = true)
    (hlv : body.lvarLT lvl = true) :
    closeAll (lvl + 1) (SubstEval.openFreshTop body lvl)
      = closeAllAt 1 lvl body :=
  closeAll_openFresh body lvl hcl hlv

/-! ## Wall consolidation: closeAll-evalSubst commutation as a
    bidirectional `Subtype'` bridge

The two evaluation bridges `eval_bridge_a/b` in
`Soundness/SubCheckSubstSoundness.lean`'s `subCheckSubst_sound` need
to translate an `evalSubst e = .ok e'` step into bidirectional
`Subtype'` derivations on the *closeAll-translated* terms (at depth
`tyCtx.size`).

At depth `d = 0`, `closeAll 0 = id` (`closeAll_zero` in
`SubCheckSubstFallback.lean`) and `Soundness/EvalSubstEquiv.lean`'s
`evalSubst_equiv` already discharges this directly under
`closedAt 0`.

At depth `d > 0`, the input `e` has free level-vars (encoded as
`bvar (levelOffset + lvl)` for `lvl < d`), and the natural lifting
walls on the same v2 closeAllAt-substL commutation issue
(`docs/ideas/proposalA-wall-v2.md`):

* **Path A** — derive `evalSubst fuel unf (closeAll d e) =
  .ok (closeAll d e')` from `evalSubst fuel unf e = .ok e'`, then
  apply `evalSubst_equiv` on the closeAll'd terms.  The pointwise
  commutation `closeAll d (substL b 0 s) = (closeAllAt 1 d b).subst 0
  (closeAll d s)` walls on the substL-decrement / closeAll-image
  off-by-one (v2 wall).

* **Path B** — structural induction on `Subtype' [] [] e' e` (yielded
  by `evalSubst_equiv` at depth 0) lifting it to `Subtype' S Γ
  (closeAll d e') (closeAll d e)`.  The β / iota_intro / unfold /
  beta-let cases rely on the closeAllAt-substL commutation, same v2
  wall.

Rather than carry two structurally identical sorries inside
`subCheckSubst_sound`, we consolidate to a single named wall here.
Discharging this lemma is **equivalent** to closing the v2 walls in
`SubCheckSubstFallback.lean`.  When the engine-side fix (option 1
in `proposalA-wall-v2.md`: non-decrementing `openFresh`/`substL`)
lands — or a closeAllSubst variant is built — this lemma closes
unconditionally; the two consumer sorries in `subCheckSubst_sound`
drop simultaneously. -/

/-- **WALL** (consolidated v2): closeAll-evalSubst commutation as a
    bidirectional `Subtype'` bridge.

    Given `evalSubst fuel unf e = .ok e'`, the closeAll-translated
    forms are mutually `Subtype'`-related under any seen-set / context.

    *Status*: walls on `closeAllAt_substL` (v2; see
    `docs/ideas/proposalA-wall-v2.md`).  At depth 0 (where
    `closeAll 0 = id`) the lemma reduces to `evalSubst_equiv` under
    `closedAt 0`; at non-zero depth it is the same wall as the four
    fallback `*_substBridge_WALL` lemmas in `SubCheckSubstFallback.lean`.

    Closing this single lemma discharges **both** `eval_bridge_a` and
    `eval_bridge_b` consumers in `subCheckSubst_sound`. -/
theorem closeAll_evalSubst_subtype
    {fuel unf : Nat} {d : Nat} {e e' : Expr} {S : Seen} {Γ : Ctx}
    (_hstep : SubstEval.evalSubst fuel unf e = .ok e') :
    Subtype' S Γ (closeAll d e) (closeAll d e') ∧
    Subtype' S Γ (closeAll d e') (closeAll d e) := by
  -- Walls on closeAllAt_substL (v2 issue).  See module docstring
  -- above and `docs/ideas/proposalA-wall-v2.md`.
  sorry

/-- **Depth-0 specialization** of `closeAll_evalSubst_subtype`,
    discharged via `evalSubst_equiv` (in `Soundness/EvalSubstEquiv.lean`).

    At `d = 0`, `closeAll 0 = id`, so the consolidated wall reduces to
    the bidirectional `evalSubst_equiv` under `closedAt 0`.  This
    closes unconditionally and bridges directly into `Subtype'` over
    any seen-set / context via `Subtype'.weaken` (with the shape
    `Subtype' [] []` lifting trivially to `Subtype' S Γ`).

    Use this when the caller can establish `e.closedAt 0`; the general
    `closeAll_evalSubst_subtype` walls because non-zero depth requires
    the v2 closeAllAt-substL commutation. -/
theorem closeAll_evalSubst_subtype_at_zero
    {fuel unf : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : SubstEval.evalSubst fuel unf e = .ok e') :
    Subtype' [] [] (closeAll 0 e) (closeAll 0 e') ∧
    Subtype' [] [] (closeAll 0 e') (closeAll 0 e) := by
  -- closeAll 0 = id, and the bidirectional Subtype' comes directly
  -- from evalSubst_equiv.
  have ⟨h1, h2⟩ := evalSubst_equiv hcl hstep
  -- Inline the `closeAll 0 = id` lemma (the same lemma also exists as
  -- `Soundness.closeAll_zero` in `Soundness/SubCheckSubstFallback.lean`,
  -- which is downstream of this file).
  have hczAt : ∀ (c : Nat) (x : Expr), closeAllAt c 0 x = x := by
    intro c x
    induction x generalizing c with
    | bvar k =>
      simp only [closeAllAt]
      by_cases h : k ≥ SubstEval.levelOffset
      · simp only [h, ↓reduceIte]
        have : ¬ (k - SubstEval.levelOffset < 0) := by omega
        simp [this]
      · simp [h]
    | type => rfl
    | bot => rfl
    | lam _ _ ih_d ih_b => simp [closeAllAt, ih_d, ih_b]
    | iota _ _ ih_a ih_b => simp [closeAllAt, ih_a, ih_b]
    | fix _ _ ih_a ih_b => simp [closeAllAt, ih_a, ih_b]
    | letE _ _ ih_v ih_b => simp [closeAllAt, ih_v, ih_b]
    | app _ _ ih_f ih_a => simp [closeAllAt, ih_f, ih_a]
    | asc _ _ ih_t ih_y => simp [closeAllAt, ih_t, ih_y]
  have hcz : ∀ x, closeAll 0 x = x := fun x => hczAt 0 x
  rw [hcz e, hcz e']
  exact ⟨h2, h1⟩

end Och.Soundness
