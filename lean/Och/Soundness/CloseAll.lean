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

/-! ## `tyCtxToCtx`: depth-stratified `closeAll` translation

Translate the engine's level-indexed `tyCtx` to a declarative
de-Bruijn-indexed `Ctx`.  Each entry `tyCtx[i]` was inserted at
depth `i` (during the engine's `openFresh` descent), so we close
its level-vars w.r.t. depth `i`.  The `.reverse` puts level
`(tyCtx.size-1)` at index `0` (innermost binder).

This **Design A** convention (depth-stratified `closeAll` on
entries) keeps the canonical Ctx form uniform: every entry is a
closed-up term, and `tyCtxToCtx (tyCtx.push x)` extends as
`closeAll tyCtx.size x :: tyCtxToCtx tyCtx`, which is exactly the
shape consumed by structural arm-packages.  See
`docs/ideas/tyCtxPush-bridge-wall.md` for the design rationale. -/

/-- Translate the engine's level-indexed `tyCtx` to a declarative
    de-Bruijn-indexed `Ctx`, depth-stratified by `closeAll`. -/
def tyCtxToCtx (tyCtx : Array Expr) : Ctx :=
  (tyCtx.toList.mapIdx (fun i e => closeAll i e)).reverse

theorem tyCtxToCtx_length (tyCtx : Array Expr) :
    (tyCtxToCtx tyCtx).length = tyCtx.size := by
  simp [tyCtxToCtx, List.length_mapIdx]

/-- Cons-extension: pushing `x` at the current depth `tyCtx.size`
    prepends `closeAll tyCtx.size x` to the canonical Ctx.  This is
    the structural lemma that closes the `tyCtxPush_bridge_WALL`
    under Design A. -/
theorem tyCtxToCtx_push (tyCtx : Array Expr) (x : Expr) :
    tyCtxToCtx (tyCtx.push x)
      = closeAll tyCtx.size x :: tyCtxToCtx tyCtx := by
  simp only [tyCtxToCtx, Array.push_toList, List.mapIdx_append,
             List.mapIdx_cons, List.mapIdx_nil, List.reverse_append,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.length_mapIdx]
  have hlen : tyCtx.toList.length = tyCtx.size := by simp
  rw [hlen, Nat.zero_add]
  rfl

/-- Lookup at the (closed-form) image index `tyCtx.size - 1 - lvl`
    retrieves `closeAll lvl tyCtx[lvl]`: the entry at level `lvl`
    closed at the depth where it was inserted. -/
theorem tyCtxToCtx_get?_at (tyCtx : Array Expr) (lvl : Nat)
    (hlvl : lvl < tyCtx.size) :
    (tyCtxToCtx tyCtx).get? (tyCtx.size - 1 - lvl)
      = (tyCtx[lvl]?).map (closeAll lvl) := by
  simp only [tyCtxToCtx, List.get?_eq_getElem?]
  rw [List.getElem?_reverse]
  · have hlen : (tyCtx.toList.mapIdx (fun i e => closeAll i e)).length = tyCtx.size := by
      simp [List.length_mapIdx]
    rw [hlen]
    have hidx : tyCtx.size - 1 - (tyCtx.size - 1 - lvl) = lvl := by omega
    rw [hidx]
    -- Now: `mapIdx _ tyCtx.toList[lvl]? = (tyCtx[lvl]?).map (closeAll lvl)`.
    rw [List.getElem?_mapIdx]
    -- Goal becomes `(tyCtx.toList[lvl]?).map (fun e => closeAll lvl e)
    --              = (tyCtx[lvl]?).map (closeAll lvl)`.
    simp only [Array.getElem?_toList]
  · simp [List.length_mapIdx]; omega

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
      ((closeAll lvl ty).shift (tyCtx.size - 1 - lvl + 1) 0) := by
  rw [closeAll_levelBvar tyCtx.size lvl hlvl]
  -- Goal: `Subtype' S (tyCtxToCtx tyCtx) (.bvar (tyCtx.size-1-lvl))
  --                    ((closeAll lvl ty).shift (tyCtx.size-1-lvl+1) 0)`.
  apply Subtype'.bvar
  rw [tyCtxToCtx_get?_at tyCtx lvl hlvl, h]
  rfl

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

/-! ### `closeAllAt_succ_eq_shift`: bumping the binder counter

For terms `s` whose ordinary bvars are bounded by `m` and whose
level-vars are bounded by `d`, bumping the closeAllAt counter from
`c` to `c+1` is the same as applying `Expr.shift 1 m` to the
closeAllAt'd result, *provided* `c ≥ m` (so the closeAllAt image of
level-vars sits above the shift cutoff).

This is the key recursion-step lemma for `closeAllAt_substL_subst`
(below): under a binder, the engine's `substL` keeps the substituee
unchanged (since `shiftL` skips level-vars and `s` has no plain
bvars), but the declarative `Expr.subst` shifts the substituee with
cutoff `0`.  The helper bridges the two views.

For our use case (`s.closedAtLvl 0 = true`), instantiated at `m = 0`:
the precondition `c ≥ 0` is trivially satisfied.  The shift cutoff
`m` matches the substituee's closedness level; the proof's recursion
under binders bumps both. -/

theorem closeAllAt_succ_eq_shift (s : Expr) (c d m : Nat)
    (hcl : s.closedAtLvl m = true)
    (hlv : s.lvarLT d = true)
    (hcm : c ≥ m) :
    closeAllAt (c + 1) d s = (closeAllAt c d s).shift 1 m := by
  induction s generalizing c m with
  | bvar k =>
    simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at hcl
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hlv
    by_cases hLvl : isLevelIdx k
    · -- Level-var case: k ≥ levelOffset.
      have hk_ge : k ≥ levelOffset := by
        simpa [isLevelIdx] using hLvl
      have hlvl_lt : k - levelOffset < d := by
        rcases hlv with h_not_lvl | h_bound
        · exact absurd hk_ge (by simpa [isLevelIdx] using h_not_lvl)
        · exact h_bound
      have hLHS : closeAllAt (c + 1) d (.bvar k) =
          .bvar (d - 1 - (k - levelOffset) + (c + 1)) := by
        simp only [closeAllAt, hk_ge, ↓reduceIte, hlvl_lt]
      have hRHS_close : closeAllAt c d (.bvar k) =
          .bvar (d - 1 - (k - levelOffset) + c) := by
        simp only [closeAllAt, hk_ge, ↓reduceIte, hlvl_lt]
      rw [hLHS, hRHS_close]
      -- Shift the closed image: index = d-1-lvl+c, which is ≥ c ≥ m.
      simp only [Expr.shift]
      have h_not_lt : ¬ d - 1 - (k - levelOffset) + c < m := by omega
      simp [h_not_lt]
      omega
    · -- Ordinary bvar: k < levelOffset.  closedAtLvl m says k < m.
      have hk_lt_lo : k < levelOffset := by
        simpa [isLevelIdx] using hLvl
      have hk_lt_m : k < m := by
        rcases hcl with h | h
        · exact h
        · omega
      have hk_not_ge : ¬ k ≥ levelOffset := by omega
      simp only [closeAllAt, hk_not_ge, ↓reduceIte, Expr.shift]
      simp [hk_lt_m]
  | type => simp [closeAllAt, Expr.shift]
  | bot => simp [closeAllAt, Expr.shift]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    -- For body: closedAtLvl (m+1), counter c+1, hcm: c+1 ≥ m+1 (= c ≥ m).
    rw [ih_dom c m hcl.1 hlv.1 hcm,
        ih_body (c + 1) (m + 1) (by simpa using hcl.2) hlv.2 (by omega)]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    rw [ih_ann c m hcl.1 hlv.1 hcm,
        ih_body (c + 1) (m + 1) (by simpa using hcl.2) hlv.2 (by omega)]
  | fix ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    rw [ih_ann c m hcl.1 hlv.1 hcm,
        ih_body (c + 1) (m + 1) (by simpa using hcl.2) hlv.2 (by omega)]
  | letE val body ih_val ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    rw [ih_val c m hcl.1 hlv.1 hcm,
        ih_body (c + 1) (m + 1) (by simpa using hcl.2) hlv.2 (by omega)]
  | app f a ih_f ih_a =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    rw [ih_f c m hcl.1 hlv.1 hcm, ih_a c m hcl.2 hlv.2 hcm]
  | asc t y ih_t ih_y =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
    simp only [closeAllAt, Expr.shift]
    rw [ih_t c m hcl.1 hlv.1 hcm, ih_y c m hcl.2 hlv.2 hcm]

/-! ### `closeAllAt_substL_subst`: the v2 wall closes (with `Expr.subst` on the right)

The naive v2 wall (`closeAllAt_substL` for arbitrary substituees,
analysed in `docs/ideas/proposalA-wall-v2.md`) is genuinely false:
it commutes `closeAllAt` with `substL` on **both sides**.
`substL`'s decrement on level-var images causes off-by-ones.

But the **fallback bridges** in `Soundness/SubCheckSubstFallback.lean`
need a *different* equation: one that uses `Expr.subst` (the
declarative substitution) on the right.  And that equation
**does hold**, because `closeAllAt`'s `+c` shift on level-var
images and `Expr.subst`'s decrement on bvars `> j` cancel cleanly.

The lockstep form (`c = j`, the only regime that arises in the
recursion) generalises to:

```
closeAllAt c d (substL e c s)
  = (closeAllAt (c+1) d e).subst c (closeAllAt c d s)
```

under preconditions:
* `e.closedAtLvl (c + 1) = true` — bvars in `e` are `≤ c`;
* `e.lvarLT d = true` — level-vars in `e` are `< d`;
* `s.closedAtLvl 0 = true` — `s` has no plain bvars (only level-vars);
* `s.lvarLT d = true` — level-vars in `s` are `< d`.

The proof is structural induction on `e`, with the helper
`closeAllAt_succ_eq_shift` discharging the "shifted substituee" part
of the lam/iota/fix/letE cases.  The crucial observation: under a
binder, `substL`'s body recursion uses `shiftL 1 0 s`, which equals
`s` itself (since `shiftL` skips level-vars and `s` has no plain
bvars to shift), but `Expr.subst`'s body recursion uses `s.shift 1 0`
(which is *not* `s`).  The helper bridges these two views via
`closeAllAt`. -/

/-- Helper: `shiftL 1 c s = s` when `s.closedAtLvl c = true`.
    The extra hypothesis lets the lam/iota/fix/letE recursion through:
    body has `closedAtLvl (c+1)`, IH at `c+1` gives `shiftL 1 (c+1) body
    = body`. -/
private theorem shiftL_one_id_of_closedAtLvl (s : Expr) (c : Nat)
    (hcl : s.closedAtLvl c = true) :
    shiftL 1 c s = s := by
  induction s generalizing c with
  | bvar k =>
    simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at hcl
    by_cases hLvl : isLevelIdx k
    · simp only [shiftL, hLvl, ↓reduceIte]
    · have hk_lt_lo : k < levelOffset := by
        simpa [isLevelIdx] using hLvl
      have hk_lt_c : k < c := by
        rcases hcl with h | h
        · exact h
        · omega
      simp only [shiftL, hLvl, Bool.false_eq_true, ↓reduceIte, hk_lt_c]
  | type => rfl
  | bot => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_dom c hcl.1, ih_body (c + 1) (by simpa using hcl.2)]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_ann c hcl.1, ih_body (c + 1) (by simpa using hcl.2)]
  | fix ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_ann c hcl.1, ih_body (c + 1) (by simpa using hcl.2)]
  | letE val body ih_val ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_val c hcl.1, ih_body (c + 1) (by simpa using hcl.2)]
  | app f a ih_f ih_a =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_f c hcl.1, ih_a c hcl.2]
  | asc t y ih_t ih_y =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [shiftL]
    rw [ih_t c hcl.1, ih_y c hcl.2]

/-- The main commutation lemma: at the lockstep `c = j`, `closeAllAt`
    and `substL` commute through `Expr.subst` (declarative side) on
    the right.  The closeAllAt's `+c` on level-var images and
    `Expr.subst`'s decrement on bvars `> j` cancel.

    Preconditions:
    * `e.closedAtLvl (c + 1) = true` — bvars `≤ c` (only the
      to-be-substituted binder allowed at the substitution point).
    * `e.lvarLT d = true`, `s.lvarLT d = true` — level-vars are
      bounded by the closeAllAt depth.
    * `s.closedAtLvl 0 = true` — substituee has no plain bvars
      (matches the engine's invariant: substituees come from
      `subCheckSubst`'s WHNF inputs, which are level-encoded). -/
theorem closeAllAt_substL_subst (e : Expr) (c d : Nat) (s : Expr)
    (he_cl : e.closedAtLvl (c + 1) = true)
    (he_lv : e.lvarLT d = true)
    (hs_cl : s.closedAtLvl 0 = true)
    (hs_lv : s.lvarLT d = true) :
    closeAllAt c d (substL e c s)
      = (closeAllAt (c + 1) d e).subst c (closeAllAt c d s) := by
  induction e generalizing c with
  | bvar k =>
    simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at he_cl
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at he_lv
    by_cases hLvl : isLevelIdx k
    · -- Level-var case.  k ≥ levelOffset; substL skips.
      have hk_ge : k ≥ levelOffset := by
        simpa [isLevelIdx] using hLvl
      have hlvl_lt : k - levelOffset < d := by
        rcases he_lv with h | h
        · exact absurd hk_ge (by simpa [isLevelIdx] using h)
        · exact h
      have hsubst : substL (.bvar k) c s = .bvar k := by
        simp only [substL, hLvl, ↓reduceIte]
      rw [hsubst]
      -- LHS: closeAllAt c d (.bvar k) = .bvar (d-1-lvl+c).
      have hLHS : closeAllAt c d (.bvar k) =
          .bvar (d - 1 - (k - levelOffset) + c) := by
        simp only [closeAllAt, hk_ge, ↓reduceIte, hlvl_lt]
      -- RHS: closeAllAt (c+1) d (.bvar k) = .bvar (d-1-lvl+c+1), then subst c.
      have hRHS_close : closeAllAt (c + 1) d (.bvar k) =
          .bvar (d - 1 - (k - levelOffset) + c + 1) := by
        simp only [closeAllAt, hk_ge, ↓reduceIte, hlvl_lt]
        have h_eq : d - 1 - (k - levelOffset) + (c + 1)
                  = d - 1 - (k - levelOffset) + c + 1 := by omega
        rw [h_eq]
      rw [hLHS, hRHS_close]
      -- subst c on .bvar (d-1-lvl+c+1): index ≠ c, > c, decrement to d-1-lvl+c.
      simp only [Expr.subst]
      have hbeq : (d - 1 - (k - levelOffset) + c + 1 == c) = false := by
        simp; omega
      have hgt : d - 1 - (k - levelOffset) + c + 1 > c := by omega
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hgt, ↓reduceIte]
      have h_eq2 : d - 1 - (k - levelOffset) + c + 1 - 1
                 = d - 1 - (k - levelOffset) + c := by omega
      rw [h_eq2]
    · -- Ordinary bvar.  k < levelOffset.  closedAtLvl (c+1) says k ≤ c.
      have hk_lt_lo : k < levelOffset := by
        simpa [isLevelIdx] using hLvl
      have hk_le_c : k ≤ c := by
        rcases he_cl with h | h
        · omega
        · omega
      have hk_not_ge : ¬ k ≥ levelOffset := by omega
      by_cases heq : k = c
      · -- substitution point.
        subst heq
        have hsubst : substL (.bvar k) k s = s := by
          simp only [substL, hLvl, Bool.false_eq_true, ↓reduceIte,
            beq_self_eq_true]
        rw [hsubst]
        -- LHS: closeAllAt k d s.
        -- RHS: closeAllAt (k+1) d (.bvar k) = .bvar k (k < levelOffset).
        --       Then .bvar k.subst k _ = closeAllAt k d s.
        have hRHS_close : closeAllAt (k + 1) d (.bvar k) = .bvar k := by
          simp only [closeAllAt]
          have : ¬ k ≥ levelOffset := by omega
          simp [this]
        rw [hRHS_close]
        simp only [Expr.subst, beq_self_eq_true, ↓reduceIte]
      · -- k < c.
        have hk_lt_c : k < c := by omega
        have hbeq_lt : (k == c) = false := by simp [heq]
        have hgt_no : ¬ k > c := by omega
        have hsubst : substL (.bvar k) c s = .bvar k := by
          simp only [substL, hLvl, Bool.false_eq_true, ↓reduceIte, hbeq_lt,
            hgt_no]
        rw [hsubst]
        -- LHS: closeAllAt c d (.bvar k) = .bvar k.
        rw [closeAllAt_bvar_lt_levelOffset c d k hk_lt_lo]
        -- RHS: closeAllAt (c+1) d (.bvar k) = .bvar k.  Then subst c.
        rw [closeAllAt_bvar_lt_levelOffset (c+1) d k hk_lt_lo]
        simp only [Expr.subst, hbeq_lt, Bool.false_eq_true, ↓reduceIte, hgt_no]
  | type => simp [substL, closeAllAt, Expr.subst]
  | bot => simp [substL, closeAllAt, Expr.subst]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    -- shiftL 1 0 s = s (since s.closedAtLvl 0).
    have hshift_id : shiftL 1 0 s = s :=
      shiftL_one_id_of_closedAtLvl s 0 hs_cl
    rw [hshift_id]
    -- closeAllAt c d s shifted: (closeAllAt c d s).shift 1 c = closeAllAt (c+1) d s.
    have hshift_close :
        (closeAllAt c d s).shift 1 0 = closeAllAt (c + 1) d s := by
      rw [closeAllAt_succ_eq_shift s c d 0 hs_cl hs_lv (Nat.zero_le _)]
    -- IH on dom: at counter c.
    rw [ih_dom c he_cl.1 he_lv.1]
    -- IH on body: at counter c+1, with body.closedAtLvl (c+2).
    have hbody_cl : body.closedAtLvl (c + 1 + 1) = true := by
      simpa [show c + 1 + 1 = c + 2 from rfl] using he_cl.2
    have := ih_body (c + 1) hbody_cl he_lv.2
    rw [this, hshift_close]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    have hshift_id : shiftL 1 0 s = s :=
      shiftL_one_id_of_closedAtLvl s 0 hs_cl
    rw [hshift_id]
    have hshift_close :
        (closeAllAt c d s).shift 1 0 = closeAllAt (c + 1) d s := by
      rw [closeAllAt_succ_eq_shift s c d 0 hs_cl hs_lv (Nat.zero_le _)]
    rw [ih_ann c he_cl.1 he_lv.1]
    have hbody_cl : body.closedAtLvl (c + 1 + 1) = true := by
      simpa [show c + 1 + 1 = c + 2 from rfl] using he_cl.2
    have := ih_body (c + 1) hbody_cl he_lv.2
    rw [this, hshift_close]
  | fix ann body ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    have hshift_id : shiftL 1 0 s = s :=
      shiftL_one_id_of_closedAtLvl s 0 hs_cl
    rw [hshift_id]
    have hshift_close :
        (closeAllAt c d s).shift 1 0 = closeAllAt (c + 1) d s := by
      rw [closeAllAt_succ_eq_shift s c d 0 hs_cl hs_lv (Nat.zero_le _)]
    rw [ih_ann c he_cl.1 he_lv.1]
    have hbody_cl : body.closedAtLvl (c + 1 + 1) = true := by
      simpa [show c + 1 + 1 = c + 2 from rfl] using he_cl.2
    have := ih_body (c + 1) hbody_cl he_lv.2
    rw [this, hshift_close]
  | letE val body ih_val ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    have hshift_id : shiftL 1 0 s = s :=
      shiftL_one_id_of_closedAtLvl s 0 hs_cl
    rw [hshift_id]
    have hshift_close :
        (closeAllAt c d s).shift 1 0 = closeAllAt (c + 1) d s := by
      rw [closeAllAt_succ_eq_shift s c d 0 hs_cl hs_lv (Nat.zero_le _)]
    rw [ih_val c he_cl.1 he_lv.1]
    have hbody_cl : body.closedAtLvl (c + 1 + 1) = true := by
      simpa [show c + 1 + 1 = c + 2 from rfl] using he_cl.2
    have := ih_body (c + 1) hbody_cl he_lv.2
    rw [this, hshift_close]
  | app f a ih_f ih_a =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    rw [ih_f c he_cl.1 he_lv.1, ih_a c he_cl.2 he_lv.2]
  | asc t y ih_t ih_y =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at he_cl
    simp only [Expr.lvarLT, Bool.and_eq_true] at he_lv
    simp only [substL, closeAllAt, Expr.subst]
    rw [ih_t c he_cl.1 he_lv.1, ih_y c he_cl.2 he_lv.2]

/-- Specialisation at top-level (`c = 0`).  This is what the
    `_substBridge_WALL` lemmas in `SubCheckSubstFallback.lean` need. -/
theorem closeAll_substL_subst (e : Expr) (d : Nat) (s : Expr)
    (he_cl : e.closedAtLvl 1 = true)
    (he_lv : e.lvarLT d = true)
    (hs_cl : s.closedAtLvl 0 = true)
    (hs_lv : s.lvarLT d = true) :
    closeAll d (substL e 0 s)
      = (closeAllAt 1 d e).subst 0 (closeAll d s) := by
  have h := closeAllAt_substL_subst e 0 d s he_cl he_lv hs_cl hs_lv
  simpa [closeAll] using h

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

/-! ### Helpers for the depth-d induction

The depth-d analog of `evalSubst_equiv` needs `lvarLT d` preservation
across `shiftL`, `substL`, and `evalSubst`, alongside the existing
`closedAtLvl`-preservation infrastructure (`evalSubst_closedAtLvl` in
`EvalSubstLemmas.lean`).

We prove `lvarLT`-preservation under the closedness invariants we
already maintain (`closedAtLvl 0` for inputs and substituees), which
keeps the proofs short — `shiftL` and `substL` only touch ordinary
bvars, never level-vars, and under `closedAtLvl 0` the substituee has
no ordinary bvars at all (so `shiftL 1 0 s = s` via
`shiftL_one_id_of_closedAtLvl`). -/

/-- `shiftL` preserves `lvarLT lvl` under `closedAtLvl c`: ordinary
    bvars `< c` are below the cutoff and untouched, level-vars are
    skipped, so no bvar is ever shifted into the level-var range.

    The `closedAtLvl c` precondition is the natural one for our
    engine use case: substituees in `substL body j s` have
    `s.closedAtLvl 0 = true`, and the only `shiftL` call in `substL`
    is `shiftL 1 0 s` — handled by `shiftL_one_id_of_closedAtLvl`
    (which makes this lemma redundant in that context).  The lemma is
    nonetheless stated generally for the recursion under binders. -/
theorem shiftL_lvarLT (e : Expr) (d c lvl : Nat)
    (hcl : e.closedAtLvl c = true)
    (h : e.lvarLT lvl = true) : (SubstEval.shiftL d c e).lvarLT lvl = true := by
  induction e generalizing c with
  | bvar k =>
    simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at hcl
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    by_cases hLvl : SubstEval.isLevelIdx k
    · -- shiftL keeps level-vars unchanged.
      simp only [SubstEval.shiftL, hLvl, ↓reduceIte, Expr.lvarLT,
        Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      rcases h with h_not | h_bnd
      · -- h_not : isLevelIdx k = false; but hLvl says it's true.
        rw [h_not] at hLvl; cases hLvl
      · exact Or.inr h_bnd
    · -- Ordinary bvar.  closedAtLvl c says k < c (since k < levelOffset
      -- via ¬ isLevelIdx).  shiftL d c keeps k unchanged.
      have hk_lt_lo : k < SubstEval.levelOffset := by
        simpa [SubstEval.isLevelIdx] using hLvl
      have hk_lt_c : k < c := by
        rcases hcl with h | h
        · exact h
        · omega
      simp only [SubstEval.shiftL, hLvl, Bool.false_eq_true, ↓reduceIte, hk_lt_c]
      simp only [Expr.lvarLT, hLvl, Bool.not_false, Bool.true_or]
  | type => simp [SubstEval.shiftL, Expr.lvarLT]
  | bot => simp [SubstEval.shiftL, Expr.lvarLT]
  | lam _ _ ih_dom ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_dom c hcl.1 h.1, ih_body (c + 1) (by simpa using hcl.2) h.2⟩
  | iota _ _ ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_ann c hcl.1 h.1, ih_body (c + 1) (by simpa using hcl.2) h.2⟩
  | fix _ _ ih_ann ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_ann c hcl.1 h.1, ih_body (c + 1) (by simpa using hcl.2) h.2⟩
  | letE _ _ ih_val ih_body =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_val c hcl.1 h.1, ih_body (c + 1) (by simpa using hcl.2) h.2⟩
  | app _ _ ih_f ih_a =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_f c hcl.1 h.1, ih_a c hcl.2 h.2⟩
  | asc _ _ ih_t ih_y =>
    simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
    simp only [Expr.lvarLT, Bool.and_eq_true] at h
    simp only [SubstEval.shiftL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_t c hcl.1 h.1, ih_y c hcl.2 h.2⟩

/-- `substL` preserves `lvarLT lvl` when both `e` and `s` are
    `lvarLT lvl` (and `s.closedAtLvl 0`, so the under-binder
    `shiftL 1 0 s` is the identity on `s`).  Ordinary bvars:
    substitution puts `s` in or decrements; both are `lvarLT lvl`.
    Level-vars: skipped. -/
theorem substL_lvarLT (e : Expr) (j lvl : Nat) (s : Expr)
    (he : e.lvarLT lvl = true)
    (hs_cl : s.closedAtLvl 0 = true)
    (hs : s.lvarLT lvl = true) :
    (SubstEval.substL e j s).lvarLT lvl = true := by
  induction e generalizing j s with
  | bvar k =>
    simp only [Expr.lvarLT, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at he
    by_cases hLvl : SubstEval.isLevelIdx k
    · simp only [SubstEval.substL, hLvl, ↓reduceIte, Expr.lvarLT,
        Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      rcases he with h_not | h_bnd
      · rw [h_not] at hLvl; cases hLvl
      · exact Or.inr h_bnd
    · simp only [SubstEval.substL, hLvl, Bool.false_eq_true, ↓reduceIte]
      have hk_lt_lo : k < SubstEval.levelOffset := by
        simpa [SubstEval.isLevelIdx] using hLvl
      by_cases heq : k = j
      · simp [heq, hs]
      · have hbeq : (k == j) = false := by simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        by_cases hgt : k > j
        · -- Decrements to .bvar (k - 1).  Still ordinary, lvarLT trivially.
          simp only [hgt, ↓reduceIte]
          simp only [Expr.lvarLT, SubstEval.isLevelIdx]
          have : ¬ (k - 1 ≥ SubstEval.levelOffset) := by omega
          simp [this]
        · simp only [hgt, Bool.false_eq_true, ↓reduceIte]
          simp only [Expr.lvarLT, SubstEval.isLevelIdx]
          have : ¬ (k ≥ SubstEval.levelOffset) := by omega
          simp [this]
  | type => simp [SubstEval.substL, Expr.lvarLT]
  | bot => simp [SubstEval.substL, Expr.lvarLT]
  | lam _ _ ih_dom ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    have hshift_s_lv : (SubstEval.shiftL 1 0 s).lvarLT lvl = true :=
      shiftL_lvarLT s 1 0 lvl hs_cl hs
    have hshift_s_cl : (SubstEval.shiftL 1 0 s).closedAtLvl 0 = true := by
      have h := SubstEval.shiftL_closedAtLvl_gen s 0 1 0 (Nat.le_refl _) hs_cl
      -- shiftL_closedAtLvl_gen gives closedAtLvl (n + d) = closedAtLvl 1.
      -- But shiftL 1 0 s on s.closedAtLvl 0 means s = shiftL 1 0 s (no shift),
      -- so it remains closedAtLvl 0.  Use shiftL_one_id_of_closedAtLvl.
      rw [shiftL_one_id_of_closedAtLvl s 0 hs_cl]
      exact hs_cl
    refine ⟨ih_dom j s he.1 hs_cl hs, ?_⟩
    exact ih_body (j + 1) (SubstEval.shiftL 1 0 s) he.2 hshift_s_cl hshift_s_lv
  | iota _ _ ih_ann ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    have hshift_s_lv : (SubstEval.shiftL 1 0 s).lvarLT lvl = true :=
      shiftL_lvarLT s 1 0 lvl hs_cl hs
    have hshift_s_cl : (SubstEval.shiftL 1 0 s).closedAtLvl 0 = true := by
      rw [shiftL_one_id_of_closedAtLvl s 0 hs_cl]; exact hs_cl
    refine ⟨ih_ann j s he.1 hs_cl hs, ?_⟩
    exact ih_body (j + 1) (SubstEval.shiftL 1 0 s) he.2 hshift_s_cl hshift_s_lv
  | fix _ _ ih_ann ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    have hshift_s_lv : (SubstEval.shiftL 1 0 s).lvarLT lvl = true :=
      shiftL_lvarLT s 1 0 lvl hs_cl hs
    have hshift_s_cl : (SubstEval.shiftL 1 0 s).closedAtLvl 0 = true := by
      rw [shiftL_one_id_of_closedAtLvl s 0 hs_cl]; exact hs_cl
    refine ⟨ih_ann j s he.1 hs_cl hs, ?_⟩
    exact ih_body (j + 1) (SubstEval.shiftL 1 0 s) he.2 hshift_s_cl hshift_s_lv
  | letE _ _ ih_val ih_body =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    have hshift_s_lv : (SubstEval.shiftL 1 0 s).lvarLT lvl = true :=
      shiftL_lvarLT s 1 0 lvl hs_cl hs
    have hshift_s_cl : (SubstEval.shiftL 1 0 s).closedAtLvl 0 = true := by
      rw [shiftL_one_id_of_closedAtLvl s 0 hs_cl]; exact hs_cl
    refine ⟨ih_val j s he.1 hs_cl hs, ?_⟩
    exact ih_body (j + 1) (SubstEval.shiftL 1 0 s) he.2 hshift_s_cl hshift_s_lv
  | app _ _ ih_f ih_a =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_f j s he.1 hs_cl hs, ih_a j s he.2 hs_cl hs⟩
  | asc _ _ ih_t ih_y =>
    simp only [Expr.lvarLT, Bool.and_eq_true] at he
    simp only [SubstEval.substL, Expr.lvarLT, Bool.and_eq_true]
    exact ⟨ih_t j s he.1 hs_cl hs, ih_y j s he.2 hs_cl hs⟩

/-- `evalSubst` preserves `lvarLT lvl`.  Mirrors
    `evalSubst_closedAtLvl` (in `EvalSubstLemmas.lean`); routes
    substL-substitution arms through `substL_lvarLT`.  Requires
    `closedAtLvl 0` to thread through `substL_lvarLT`. -/
theorem evalSubst_lvarLT {n unf : Nat} {e v : Expr} {lvl : Nat}
    (hcl : e.closedAtLvl 0 = true)
    (hlv : e.lvarLT lvl = true)
    (h : SubstEval.evalSubst n unf e = .ok v) : v.lvarLT lvl = true := by
  induction n generalizing unf e v with
  | zero => rw [SubstEval.evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar j =>
      rw [SubstEval.evalSubst.eq_2] at h
      by_cases hLvl : SubstEval.isLevelIdx j
      · simp only [hLvl, ↓reduceIte, Outcome.ok.injEq] at h
        subst h; exact hlv
      · simp only [hLvl, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | .type =>
      rw [SubstEval.evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .bot =>
      rw [SubstEval.evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .lam _ _ =>
      rw [SubstEval.evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hlv
    | .iota _ _ =>
      rw [SubstEval.evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hlv
    | .fix _ _ =>
      rw [SubstEval.evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hlv
    | .asc t _ =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_8] at h
      exact ih hcl.1 hlv.1 h
    | .letE val body =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_9] at h
      match hv : SubstEval.evalSubst k unf val with
      | .outOfFuel => rw [hv] at h; cases h
      | .error _ => rw [hv] at h; cases h
      | .ok vVal =>
        have hvlv := ih hcl.1 hlv.1 hv
        have hvcl : vVal.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl hcl.1 hv
        rw [hv] at h
        simp only [Outcome.ok_bind] at h
        have hsub_cl : (SubstEval.substL body 0 vVal).closedAtLvl 0 = true :=
          SubstEval.substL_closedAtLvl (by simpa using hcl.2) hvcl
        have hsub : (SubstEval.substL body 0 vVal).lvarLT lvl = true :=
          substL_lvarLT body 0 lvl vVal hlv.2 hvcl hvlv
        exact ih hsub_cl hsub h
    | .app f a =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_10] at h
      match hf : SubstEval.evalSubst k unf f with
      | .outOfFuel => rw [hf] at h; cases h
      | .error _ => rw [hf] at h; cases h
      | .ok fv =>
        have hfcl : fv.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl hcl.1 hf
        have hflv := ih hcl.1 hlv.1 hf
        match ha : SubstEval.evalSubst k unf a with
        | .outOfFuel => rw [hf, ha] at h; cases h
        | .error _ => rw [hf, ha] at h; cases h
        | .ok av =>
          have hacl : av.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl hcl.2 ha
          have halv := ih hcl.2 hlv.2 ha
          rw [hf, ha] at h
          simp only [Outcome.ok_bind] at h
          cases fv with
          | bvar bk =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            simp only [Expr.lvarLT, Bool.and_eq_true]
            exact ⟨hflv, halv⟩
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            simp only [Expr.lvarLT, Bool.and_eq_true]
            exact ⟨by simp [Expr.lvarLT], halv⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            simp only [Expr.lvarLT, Bool.and_eq_true]
            exact ⟨by simp [Expr.lvarLT], halv⟩
          | lam _dom body =>
            simp only at h
            have hflv_lam : (Expr.lam _dom body).lvarLT lvl = true := hflv
            have hfcl_lam : (Expr.lam _dom body).closedAtLvl 0 = true := hfcl
            simp only [Expr.lvarLT, Bool.and_eq_true] at hflv_lam
            simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl_lam
            have hsub_cl : (SubstEval.substL body 0 av).closedAtLvl 0 = true :=
              SubstEval.substL_closedAtLvl (by simpa using hfcl_lam.2) hacl
            have hsub : (SubstEval.substL body 0 av).lvarLT lvl = true :=
              substL_lvarLT body 0 lvl av hflv_lam.2 hacl halv
            exact ih hsub_cl hsub h
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              show (Expr.app (.iota ann body) av).lvarLT lvl = true
              show ((Expr.iota ann body).lvarLT lvl && av.lvarLT lvl) = true
              simp [hflv, halv]
            · have hself_lv : (Expr.iota ann body).lvarLT lvl = true := hflv
              have hself_cl : (Expr.iota ann body).closedAtLvl 0 = true := hfcl
              have hflv_iota : (Expr.iota ann body).lvarLT lvl = true := hflv
              have hfcl_iota : (Expr.iota ann body).closedAtLvl 0 = true := hfcl
              simp only [Expr.lvarLT, Bool.and_eq_true] at hflv_iota
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl_iota
              have hsub_cl : (SubstEval.substL body 0 (.iota ann body)).closedAtLvl 0 = true :=
                SubstEval.substL_closedAtLvl (by simpa using hfcl_iota.2) hself_cl
              have hsub : (SubstEval.substL body 0 (.iota ann body)).lvarLT lvl
                  = true :=
                substL_lvarLT body 0 lvl _ hflv_iota.2 hself_cl hself_lv
              have hAppCl : (Expr.app (SubstEval.substL body 0 (.iota ann body)) av).closedAtLvl 0
                  = true := by
                show ((SubstEval.substL body 0 (.iota ann body)).closedAtLvl 0
                      && av.closedAtLvl 0) = true
                rw [hsub_cl, hacl]; rfl
              have hAppLv : (Expr.app (SubstEval.substL body 0 (.iota ann body)) av).lvarLT lvl
                  = true := by
                show ((SubstEval.substL body 0 (.iota ann body)).lvarLT lvl
                      && av.lvarLT lvl) = true
                rw [hsub, halv]; rfl
              exact ih hAppCl hAppLv h
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              show (Expr.app (.fix ann body) av).lvarLT lvl = true
              show ((Expr.fix ann body).lvarLT lvl && av.lvarLT lvl) = true
              simp [hflv, halv]
            · have hself_lv : (Expr.fix ann body).lvarLT lvl = true := hflv
              have hself_cl : (Expr.fix ann body).closedAtLvl 0 = true := hfcl
              have hflv_fix : (Expr.fix ann body).lvarLT lvl = true := hflv
              have hfcl_fix : (Expr.fix ann body).closedAtLvl 0 = true := hfcl
              simp only [Expr.lvarLT, Bool.and_eq_true] at hflv_fix
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl_fix
              have hsub_cl : (SubstEval.substL body 0 (.fix ann body)).closedAtLvl 0 = true :=
                SubstEval.substL_closedAtLvl (by simpa using hfcl_fix.2) hself_cl
              have hsub : (SubstEval.substL body 0 (.fix ann body)).lvarLT lvl
                  = true :=
                substL_lvarLT body 0 lvl _ hflv_fix.2 hself_cl hself_lv
              have hAppCl : (Expr.app (SubstEval.substL body 0 (.fix ann body)) av).closedAtLvl 0
                  = true := by
                show ((SubstEval.substL body 0 (.fix ann body)).closedAtLvl 0
                      && av.closedAtLvl 0) = true
                rw [hsub_cl, hacl]; rfl
              have hAppLv : (Expr.app (SubstEval.substL body 0 (.fix ann body)) av).lvarLT lvl
                  = true := by
                show ((SubstEval.substL body 0 (.fix ann body)).lvarLT lvl
                      && av.lvarLT lvl) = true
                rw [hsub, halv]; rfl
              exact ih hAppCl hAppLv h
          | asc t ty =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show ((Expr.asc t ty).lvarLT lvl && av.lvarLT lvl) = true
            simp [hflv, halv]
          | letE vv b =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show ((Expr.letE vv b).lvarLT lvl && av.lvarLT lvl) = true
            simp [hflv, halv]
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show ((Expr.app f' a').lvarLT lvl && av.lvarLT lvl) = true
            simp [hflv, halv]

/-! ### `closeAll_evalSubst_subtype_strong`: depth-d analog of `evalSubst_equiv`

Mirror of `Soundness.evalSubst_equiv` (depth-0), threaded through
`closeAll d`.  Each evalSubst arm has a structurally-matching
`Subtype'` derivation in the closeAll-translated form:

* Value arms (`.type`, `.bot`, `.lam`, `.iota`, `.fix`): refl on
  the closeAll'd form.
* `.bvar k` arm: only level-vars (`isLevelIdx k`) survive, and
  `closeAll d (.bvar k) = closeAll d (.bvar k)` is refl.
* `.asc` arm: `Subtype'.asc_L/R` lift the IH on the inner term.
* `.letE` arm: IH on the value step gives `Subtype'` on the
  closeAll'd form; the body step's substL is bridged via
  `closeAll_substL_subst`, then `letE_L`/`letE_R` /
  `letE_cong` close.
* `.app` arm: cases on the head value.  Stuck heads close via
  `app_cong` with the IH on `f` and `a`.  β / iota-unfold /
  fix-unfold bridge their substL through `closeAll_substL_subst`,
  then close via `beta_L`/`beta_R` / `unfold_iota_L`/`unfold_iota_R`
  / `unfold_fix_L`/`unfold_fix_R`. -/

theorem closeAll_evalSubst_subtype_strong
    {fuel unf : Nat} {d : Nat} {e e' : Expr} {S : Seen} {Γ : Ctx}
    (hcl : e.closedAtLvl 0 = true) (hlv : e.lvarLT d = true)
    (hstep : SubstEval.evalSubst fuel unf e = .ok e') :
    Subtype' S Γ (closeAll d e) (closeAll d e') ∧
    Subtype' S Γ (closeAll d e') (closeAll d e) := by
  induction fuel generalizing unf e e' with
  | zero => rw [SubstEval.evalSubst.eq_1] at hstep; cases hstep
  | succ n ih =>
    match e, hcl, hlv, hstep with
    | .bvar k, hcl, _hlv, h =>
      rw [SubstEval.evalSubst.eq_2] at h
      by_cases hLvl : SubstEval.isLevelIdx k
      · simp only [hLvl, ↓reduceIte, Outcome.ok.injEq] at h
        subst h
        exact ⟨.refl _, .refl _⟩
      · simp only [hLvl, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | .type, _, _, h =>
      rw [SubstEval.evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, _, _, h =>
      rw [SubstEval.evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .lam _ _, _, _, h =>
      rw [SubstEval.evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .iota _ _, _, _, h =>
      rw [SubstEval.evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .fix _ _, _, _, h =>
      rw [SubstEval.evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, hcl, hlv, h =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_8] at h
      have ⟨h₁, h₂⟩ := ih hcl.1 hlv.1 h
      -- Goal: closeAll d (.asc t ty) = .asc (closeAllAt 0 d t) (closeAllAt 0 d ty).
      show Subtype' S Γ (.asc (closeAllAt 0 d t) (closeAllAt 0 d ty)) _ ∧
           Subtype' S Γ _ (.asc (closeAllAt 0 d t) (closeAllAt 0 d ty))
      refine ⟨.asc_L h₁, .asc_R h₂⟩
    | .letE val body, hcl, hlv, h =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_9] at h
      match hvEv : SubstEval.evalSubst n unf val with
      | .outOfFuel => rw [hvEv] at h; cases h
      | .error _ => rw [hvEv] at h; cases h
      | .ok vv =>
        simp only [hvEv] at h
        have ⟨hvv₁, hvv₂⟩ := ih hcl.1 hlv.1 hvEv
        have hvv_cl : vv.closedAtLvl 0 = true :=
          SubstEval.evalSubst_closedAtLvl hcl.1 hvEv
        have hvv_lv : vv.lvarLT d = true :=
          evalSubst_lvarLT hcl.1 hlv.1 hvEv
        simp only [Outcome.ok_bind] at h
        -- substL body 0 vv has the right invariants.
        have hsub_cl : (SubstEval.substL body 0 vv).closedAtLvl 0 = true :=
          SubstEval.substL_closedAtLvl (by simpa using hcl.2) hvv_cl
        have hsub_lv : (SubstEval.substL body 0 vv).lvarLT d = true :=
          substL_lvarLT body 0 d vv hlv.2 hvv_cl hvv_lv
        have ⟨he₁, he₂⟩ := ih hsub_cl hsub_lv h
        -- Bridge: closeAll d (substL body 0 vv) = (closeAllAt 1 d body).subst 0 (closeAll d vv).
        have heq : closeAll d (SubstEval.substL body 0 vv)
            = (closeAllAt 1 d body).subst 0 (closeAll d vv) := by
          have := closeAllAt_substL_subst body 0 d vv
            (by simpa using hcl.2) hlv.2 hvv_cl hvv_lv
          simpa [closeAll] using this
        rw [heq] at he₁ he₂
        -- closeAll d (.letE val body) = .letE (closeAll d val) (closeAllAt 1 d body).
        show Subtype' S Γ (.letE (closeAll d val) (closeAllAt 1 d body)) _ ∧
             Subtype' S Γ _ (.letE (closeAll d val) (closeAllAt 1 d body))
        refine ⟨?_, ?_⟩
        · -- closeAll d (.letE val body) ⊑ closeAll d e'
          -- letE val body ⊑ letE vv body ⊑ body.subst 0 vv ⊑ e'
          have step1 : Subtype' S Γ
              (.letE (closeAll d val) (closeAllAt 1 d body))
              (.letE (closeAll d vv) (closeAllAt 1 d body)) :=
            .letE_cong hvv₁ (.refl _)
          have step2 : Subtype' S Γ
              (.letE (closeAll d vv) (closeAllAt 1 d body))
              ((closeAllAt 1 d body).subst 0 (closeAll d vv)) :=
            .letE_L (.refl _)
          exact .trans step1 (.trans step2 he₁)
        · have step1 : Subtype' S Γ
              ((closeAllAt 1 d body).subst 0 (closeAll d vv))
              (.letE (closeAll d vv) (closeAllAt 1 d body)) :=
            .letE_R (.refl _)
          have step2 : Subtype' S Γ
              (.letE (closeAll d vv) (closeAllAt 1 d body))
              (.letE (closeAll d val) (closeAllAt 1 d body)) :=
            .letE_cong hvv₂ (.refl _)
          exact .trans he₂ (.trans step1 step2)
    | .app f a, hcl, hlv, h =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      simp only [Expr.lvarLT, Bool.and_eq_true] at hlv
      rw [SubstEval.evalSubst.eq_10] at h
      match hfEv : SubstEval.evalSubst n unf f with
      | .outOfFuel => rw [hfEv] at h; cases h
      | .error _ => rw [hfEv] at h; cases h
      | .ok fv =>
        have ⟨hf₁, hf₂⟩ := ih hcl.1 hlv.1 hfEv
        match haEv : SubstEval.evalSubst n unf a with
        | .outOfFuel => rw [hfEv, haEv] at h; cases h
        | .error _ => rw [hfEv, haEv] at h; cases h
        | .ok av =>
          have ⟨ha₁, ha₂⟩ := ih hcl.2 hlv.2 haEv
          rw [hfEv, haEv] at h
          simp only [Outcome.ok_bind] at h
          have hfv_cl : fv.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl hcl.1 hfEv
          have hav_cl : av.closedAtLvl 0 = true :=
            SubstEval.evalSubst_closedAtLvl hcl.2 haEv
          have hfv_lv : fv.lvarLT d = true := evalSubst_lvarLT hcl.1 hlv.1 hfEv
          have hav_lv : av.lvarLT d = true := evalSubst_lvarLT hcl.2 hlv.2 haEv
          -- closeAll d (.app f a) = .app (closeAll d f) (closeAll d a).
          show Subtype' S Γ (.app (closeAll d f) (closeAll d a)) _ ∧
               Subtype' S Γ _ (.app (closeAll d f) (closeAll d a))
          cases fv with
          | bvar bk =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            -- closeAll d (.app (.bvar bk) av) = .app (closeAll d (.bvar bk)) (closeAll d av).
            show _ ∧ Subtype' S Γ (.app (closeAll d (.bvar bk)) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show _ ∧ Subtype' S Γ (.app (closeAll d .type) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show _ ∧ Subtype' S Γ (.app (closeAll d .bot) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            -- β case.
            simp only at h
            simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfv_cl
            simp only [Expr.lvarLT, Bool.and_eq_true] at hfv_lv
            -- substL body 0 av has the right invariants.
            have hsub_cl : (SubstEval.substL body 0 av).closedAtLvl 0 = true :=
              SubstEval.substL_closedAtLvl (by simpa using hfv_cl.2) hav_cl
            have hsub_lv : (SubstEval.substL body 0 av).lvarLT d = true :=
              substL_lvarLT body 0 d av hfv_lv.2 hav_cl hav_lv
            have ⟨he₁, he₂⟩ := ih hsub_cl hsub_lv h
            -- Bridge.
            have heq : closeAll d (SubstEval.substL body 0 av)
                = (closeAllAt 1 d body).subst 0 (closeAll d av) := by
              have := closeAllAt_substL_subst body 0 d av
                (by simpa using hfv_cl.2) hfv_lv.2 hav_cl hav_lv
              simpa [closeAll] using this
            rw [heq] at he₁ he₂
            -- closeAll d (.lam dom body) = .lam (closeAll d dom) (closeAllAt 1 d body).
            refine ⟨?_, ?_⟩
            · -- (closeAll d f) (closeAll d a) ⊑ closeAll d e'.
              -- chain: f a ⊑ (lam dom body) av ⊑ body[av] ⊑ e'
              have step1 : Subtype' S Γ
                  (.app (closeAll d f) (closeAll d a))
                  (.app (.lam (closeAll d dom) (closeAllAt 1 d body)) (closeAll d av)) :=
                .app_cong hf₁ ha₁ ha₂
              have step2 : Subtype' S Γ
                  (.app (.lam (closeAll d dom) (closeAllAt 1 d body)) (closeAll d av))
                  ((closeAllAt 1 d body).subst 0 (closeAll d av)) :=
                .beta_L (.refl _)
              exact .trans step1 (.trans step2 he₁)
            · have step1 : Subtype' S Γ
                  ((closeAllAt 1 d body).subst 0 (closeAll d av))
                  (.app (.lam (closeAll d dom) (closeAllAt 1 d body)) (closeAll d av)) :=
                .beta_R (.refl _)
              have step2 : Subtype' S Γ
                  (.app (.lam (closeAll d dom) (closeAllAt 1 d body)) (closeAll d av))
                  (.app (closeAll d f) (closeAll d a)) :=
                .app_cong hf₂ ha₂ ha₁
              exact .trans he₂ (.trans step1 step2)
          | iota ann body =>
            simp only at h
            split at h
            · -- Stuck.
              simp only [Outcome.ok.injEq] at h
              subst h
              show _ ∧ Subtype' S Γ
                (.app (closeAll d (.iota ann body)) (closeAll d av)) _
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · -- Unfolds.
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfv_cl
              simp only [Expr.lvarLT, Bool.and_eq_true] at hfv_lv
              have hself_cl : (Expr.iota ann body).closedAtLvl 0 = true := by
                simp [Expr.closedAtLvl, hfv_cl.1, hfv_cl.2]
              have hself_lv : (Expr.iota ann body).lvarLT d = true := by
                simp [Expr.lvarLT, hfv_lv.1, hfv_lv.2]
              have hsub_cl : (SubstEval.substL body 0 (.iota ann body)).closedAtLvl 0 = true :=
                SubstEval.substL_closedAtLvl (by simpa using hfv_cl.2) hself_cl
              have hsub_lv : (SubstEval.substL body 0 (.iota ann body)).lvarLT d = true :=
                substL_lvarLT body 0 d _ hfv_lv.2 hself_cl hself_lv
              have hAppCl : (Expr.app (SubstEval.substL body 0 (.iota ann body)) av).closedAtLvl 0
                  = true := by
                simp only [Expr.closedAtLvl, Bool.and_eq_true]
                exact ⟨hsub_cl, hav_cl⟩
              have hAppLv : (Expr.app (SubstEval.substL body 0 (.iota ann body)) av).lvarLT d
                  = true := by
                simp only [Expr.lvarLT, Bool.and_eq_true]
                exact ⟨hsub_lv, hav_lv⟩
              have ⟨he₁, he₂⟩ := ih hAppCl hAppLv h
              -- Bridge.
              have heq : closeAll d (SubstEval.substL body 0 (.iota ann body))
                  = (closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)) := by
                have := closeAllAt_substL_subst body 0 d (.iota ann body)
                  (by simpa using hfv_cl.2) hfv_lv.2 hself_cl hself_lv
                simpa [closeAll] using this
              -- closeAll d (.app (substL body 0 self) av)
              --   = .app ((closeAllAt 1 d body).subst 0 (closeAll d self)) (closeAll d av).
              have heqApp : closeAll d (.app (SubstEval.substL body 0 (.iota ann body)) av)
                  = .app ((closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)))
                      (closeAll d av) := by
                show closeAllAt 0 d
                    (.app (SubstEval.substL body 0 (.iota ann body)) av) = _
                simp only [closeAllAt]
                rw [show closeAllAt 0 d (SubstEval.substL body 0 (.iota ann body))
                      = (closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)) from heq]
                rfl
              rw [heqApp] at he₁ he₂
              -- closeAll d (.iota ann body) = .iota (closeAll d ann) (closeAllAt 1 d body).
              -- The unfold step:
              -- (closeAll d (.iota ann body)) ⊑ (closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body))
              have hUnfoldL : Subtype' S Γ
                  (closeAll d (.iota ann body))
                  ((closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body))) := by
                show Subtype' S Γ (.iota _ _) _
                exact .unfold_iota_L (.refl _)
              have hUnfoldR : Subtype' S Γ
                  ((closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)))
                  (closeAll d (.iota ann body)) := by
                show Subtype' S Γ _ (.iota _ _)
                exact .unfold_iota_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' S Γ
                    (.app (closeAll d f) (closeAll d a))
                    (.app (closeAll d (.iota ann body)) (closeAll d av)) :=
                  .app_cong hf₁ ha₁ ha₂
                have step2 : Subtype' S Γ
                    (.app (closeAll d (.iota ann body)) (closeAll d av))
                    (.app ((closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)))
                      (closeAll d av)) :=
                  .app_cong hUnfoldL (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₁)
              · have step1 : Subtype' S Γ
                    (.app ((closeAllAt 1 d body).subst 0 (closeAll d (.iota ann body)))
                      (closeAll d av))
                    (.app (closeAll d (.iota ann body)) (closeAll d av)) :=
                  .app_cong hUnfoldR (.refl _) (.refl _)
                have step2 : Subtype' S Γ
                    (.app (closeAll d (.iota ann body)) (closeAll d av))
                    (.app (closeAll d f) (closeAll d a)) :=
                  .app_cong hf₂ ha₂ ha₁
                exact .trans he₂ (.trans step1 step2)
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              show _ ∧ Subtype' S Γ
                (.app (closeAll d (.fix ann body)) (closeAll d av)) _
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfv_cl
              simp only [Expr.lvarLT, Bool.and_eq_true] at hfv_lv
              have hself_cl : (Expr.fix ann body).closedAtLvl 0 = true := by
                simp [Expr.closedAtLvl, hfv_cl.1, hfv_cl.2]
              have hself_lv : (Expr.fix ann body).lvarLT d = true := by
                simp [Expr.lvarLT, hfv_lv.1, hfv_lv.2]
              have hsub_cl : (SubstEval.substL body 0 (.fix ann body)).closedAtLvl 0 = true :=
                SubstEval.substL_closedAtLvl (by simpa using hfv_cl.2) hself_cl
              have hsub_lv : (SubstEval.substL body 0 (.fix ann body)).lvarLT d = true :=
                substL_lvarLT body 0 d _ hfv_lv.2 hself_cl hself_lv
              have hAppCl : (Expr.app (SubstEval.substL body 0 (.fix ann body)) av).closedAtLvl 0
                  = true := by
                simp only [Expr.closedAtLvl, Bool.and_eq_true]
                exact ⟨hsub_cl, hav_cl⟩
              have hAppLv : (Expr.app (SubstEval.substL body 0 (.fix ann body)) av).lvarLT d
                  = true := by
                simp only [Expr.lvarLT, Bool.and_eq_true]
                exact ⟨hsub_lv, hav_lv⟩
              have ⟨he₁, he₂⟩ := ih hAppCl hAppLv h
              have heq : closeAll d (SubstEval.substL body 0 (.fix ann body))
                  = (closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)) := by
                have := closeAllAt_substL_subst body 0 d (.fix ann body)
                  (by simpa using hfv_cl.2) hfv_lv.2 hself_cl hself_lv
                simpa [closeAll] using this
              have heqApp : closeAll d (.app (SubstEval.substL body 0 (.fix ann body)) av)
                  = .app ((closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)))
                      (closeAll d av) := by
                show closeAllAt 0 d
                    (.app (SubstEval.substL body 0 (.fix ann body)) av) = _
                simp only [closeAllAt]
                rw [show closeAllAt 0 d (SubstEval.substL body 0 (.fix ann body))
                      = (closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)) from heq]
                rfl
              rw [heqApp] at he₁ he₂
              have hUnfoldL : Subtype' S Γ
                  (closeAll d (.fix ann body))
                  ((closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body))) := by
                show Subtype' S Γ (.fix _ _) _
                exact .unfold_fix_L (.refl _)
              have hUnfoldR : Subtype' S Γ
                  ((closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)))
                  (closeAll d (.fix ann body)) := by
                show Subtype' S Γ _ (.fix _ _)
                exact .unfold_fix_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' S Γ
                    (.app (closeAll d f) (closeAll d a))
                    (.app (closeAll d (.fix ann body)) (closeAll d av)) :=
                  .app_cong hf₁ ha₁ ha₂
                have step2 : Subtype' S Γ
                    (.app (closeAll d (.fix ann body)) (closeAll d av))
                    (.app ((closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)))
                      (closeAll d av)) :=
                  .app_cong hUnfoldL (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₁)
              · have step1 : Subtype' S Γ
                    (.app ((closeAllAt 1 d body).subst 0 (closeAll d (.fix ann body)))
                      (closeAll d av))
                    (.app (closeAll d (.fix ann body)) (closeAll d av)) :=
                  .app_cong hUnfoldR (.refl _) (.refl _)
                have step2 : Subtype' S Γ
                    (.app (closeAll d (.fix ann body)) (closeAll d av))
                    (.app (closeAll d f) (closeAll d a)) :=
                  .app_cong hf₂ ha₂ ha₁
                exact .trans he₂ (.trans step1 step2)
          | asc t ty =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show _ ∧ Subtype' S Γ
              (.app (closeAll d (.asc t ty)) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | letE vv b =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show _ ∧ Subtype' S Γ
              (.app (closeAll d (.letE vv b)) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show _ ∧ Subtype' S Γ
              (.app (closeAll d (.app f' a')) (closeAll d av)) _
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩

/-- **Depth-0 specialization** of `closeAll_evalSubst_subtype_strong`,
    discharged via `evalSubst_equiv` (in `Soundness/EvalSubstEquiv.lean`).

    At `d = 0`, `closeAll 0 = id`, so the consolidated wall reduces to
    the bidirectional `evalSubst_equiv` under `closedAt 0`.  This
    closes unconditionally and bridges directly into `Subtype'` over
    any seen-set / context via `Subtype'.weaken` (with the shape
    `Subtype' [] []` lifting trivially to `Subtype' S Γ`).

    Use this when the caller can establish `e.closedAt 0`; for the
    depth-`d` analog with full closedness/lvarLT preconditions, see
    `closeAll_evalSubst_subtype_strong`. -/
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
