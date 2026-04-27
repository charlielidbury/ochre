import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas

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

/-- `closeAllAt` commutes with `shiftL` at matching binder counters.
    The cutoff `c'` of the shift must equal the binder counter `c` of
    the closure (matching cutoffs are what every Proposal-A use
    requires).  Both sides agree pointwise.

    Proof shape: structural induction on `e`.  The level-var arm
    produces `.bvar (d - 1 - lvl + c)`, and `shiftL d' c (.bvar (d -
    1 - lvl + c)) = .bvar (d - 1 - lvl + c + d')` when `d - 1 - lvl
    + c ≥ c` (always true).  That equals
    `closeAllAt c' d (shiftL d' c' (.bvar (levelOffset + lvl)))` since
    `shiftL` skips level-vars.  The bound bvar arms (k < levelOffset,
    k < c, etc.) match by the standard `shift` arithmetic.

    Sorry'd: TODO close this.  Estimated 60-80 LOC structural
    induction following the pattern of `shiftL_eq_shift_bvarLT`. -/
theorem closeAllAt_shiftL (c d d' : Nat) (e : Expr) :
    closeAllAt c d (shiftL d' c e) = shiftL d' c (closeAllAt c d e) := by
  sorry

/-- `closeAllAt` commutes with `substL` at the binder-counter
    position.  The substitutee `s` is translated by `closeAllAt c d`
    on the RHS to match the recursion's behaviour at the `bvar j` arm.

    Proof shape: structural induction on `e`, using
    `closeAllAt_shiftL` to handle the under-binder shift of `s`.
    The level-var arm of `e` is preserved by `substL` (level-vars
    are not the substituted index `j` since `levelOffset > j`), and
    its `closeAllAt` image (a small `.bvar`) is also outside the
    substituted range when `j < c` (the substitution position is
    binder-local).

    Sorry'd: TODO close this.  Estimated 100-150 LOC. -/
theorem closeAllAt_substL (c d j : Nat) (e s : Expr) (hj : j < c ∨ c = 0) :
    closeAllAt c d (substL e j s) = substL (closeAllAt c d e) j (closeAllAt c d s) := by
  sorry

/-- `closeAll` of `openFresh body lvl` collapses to the
    binder-internal `closeAllAt 1 (lvl+1) body`.  This is the lemma
    the `lam`/`iota`/`fix` arms of `subCheckSubst` need to
    decompose: opening the body under a fresh level-var, then
    `closeAll`-ing the result, is the same as `closeAll`-ing the
    body under one extra binder.

    Proof shape: unfold `openFresh = substL body 0 (levelBvar lvl)`,
    apply `closeAllAt_substL` (note `c = 0` so the `hj` branch
    `c = 0` fires; `substL ... 0 ...` substitutes the outermost
    bvar).  The substituted `levelBvar lvl = .bvar (levelOffset +
    lvl)` translates to `.bvar (lvl + 1 - 1 - lvl) = .bvar 0` under
    `closeAll (lvl+1)`, which is `bvar 0` — the right value to
    substitute for the outermost binder of `body`.

    Sorry'd: TODO close this; depends on `closeAllAt_substL`. -/
theorem closeAll_openFresh (body : Expr) (lvl : Nat) :
    closeAll (lvl + 1) (SubstEval.openFreshTop body lvl)
      = closeAllAt 1 (lvl + 1) body := by
  sorry

end Och.Soundness
