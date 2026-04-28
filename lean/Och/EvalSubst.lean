import Och.Syntax
import Och.Outcome
import Och.Eval

/-!
# Substitution-based evaluator and structural subtype check

This module provides Och's primary substitution-based evaluation pipeline:
a head-normal-form evaluator (`evalSubst`) and a structural subtype check
(`subCheck`) that operate directly on `Expr`, never lifting into a
`Val`/`Closure` ADT.

The bidirectional fast-path (`TyCheck.typeCheck`) and the typed
top-level entry (`SubstEval.subCheckT`) live in `Och/TyCheck.lean`,
which imports this module. Splitting the cycle that way keeps the
structural engine free of any dependency on the type-checker.

## Status

`evalSubst`, `substL`, `shiftL` are non-`partial` (Lean's elaborator
accepts them via lex measure on `(fuel, unf)` for `evalSubst`, and
structural recursion on the input `Expr` for the substitution helpers).

The `subCheckSubst` mutual block is non-`partial` as well, with each
function carrying a lex `(fuel, phase)` termination measure. `phase`
distinguishes `subCheckSubst` (phase 0) from `subCheckSubstMatch`
(phase 1): every `subCheckSubst → subCheckSubstMatch` call decrements
`fuel`, and every `subCheckSubstMatch → subCheckSubst` call decrements
phase at the same fuel. All other recursive calls in the block (spine,
ascent, synth, plus self-recursive ones) decrement `fuel` directly.
Equation lemmas (`subCheckSubst.eq_def` etc.) auto-generate, which
the soundness composition in `Soundness/SubCheckSubstSoundness.lean`
relies on.

## Why substitution-based?

The companion benchmark in `docs/ideas/eval-subst-vs-env-benchmark.md`
showed substitution-based subCheck running ~1100× faster than the
NbE-style closure-domain check on Och's heaviest workload
(`three_ ⊑ Nat_`: 14.5 s → 13 ms). Hash-consing was not needed to
deliver the speedup. The Och-specific reason is that NbE's
`subCheckVal` walks the closure DAG as a tree, retraversing shared
sub-Vals; substitution stops at HNF and produces small Exprs that the
recursive descent can short-circuit on structural equality.

## Design

- **Values are `Expr`.** No separate `Val`/`Closure` ADT. When applying
  a `λ` to an argument, we substitute the argument into the body. β
  substitutes; ι/fix unfolds substitute their own self-reference into
  their body, then reapply.

- **Free neutral variables** (the analogue of NbE's `Neutral.var lvl`)
  are encoded as `bvar (levelOffset + k)` where `levelOffset` is a
  large constant (`100_000_000`). The custom `shiftL` / `substL` walk
  the tree without disturbing these; the standard `Expr.shift` /
  `Expr.subst` would, breaking absolute-position semantics.

  This is a "level-bvar trick": effectively a single-namespace
  encoding of locally-nameless on top of the existing `Expr` type,
  without changing the AST. Programs in real Och have `bvar` indices
  far below `levelOffset` (typical depth < 100), so the encoding is
  unambiguous in practice. A future kernel rewrite that adds a
  separate `fvar` constructor (true locally-nameless) would replace
  `levelOffset` with a constructor distinction; the rest of the code
  here is essentially unchanged.

- **HNF only.** `evalSubst` returns Expr's in head-normal form. It does
  not go under λ-binders during evaluation. The under-binder cost
  shows up lazily in `subCheckSubst`, which opens binders one level at
  a time as it descends.

- **`unfBound`** caps fix/ι unfolds, mirroring `NbE.unfBound = 32`.

## Soundness

Verdict-equality vs `NbE.subCheck` is verified empirically: 16/16 cases
on the BeqBench panel agree. There is no formal soundness proof against
`subCheckVal` in this module — the verdict-parity argument is by
hand-mirroring the algorithm structure arm-for-arm, plus `evalBench`'s
runtime test. If you change the algorithm, re-run `lake exe eval_bench`
to check parity.

## Migration

`subCheckT` here mirrors `NbE.subCheckT` — try `typeCheck` first
(syntactic, fast on positive cases), fall back to `subCheck` (this
module's substitution-based check). New tests should call
`SubstEval.subCheckT`; existing `NbE.subCheckT` callers continue to
work unchanged. Both engines pass the same Std/* test corpus (April
2026 verification).
-/

namespace SubstEval

open Outcome

/-! ## Free-variable encoding via large bvar indices

  Programs in real Och never use `bvar` indices anywhere near
  `levelOffset = 100_000_000`. The substitution machinery treats indices
  ≥ `levelOffset` as **absolute level-vars** that no enclosing binder
  can rebind: `shiftL` and `substL` skip them. This makes them behave
  exactly like the `fvar` constructor of a locally-nameless
  representation, without the AST change.
-/

/-- Threshold above which `bvar` indices are interpreted as
    free level-vars (instead of bound de Bruijn indices). Must be
    larger than any bvar index that ever appears in user programs;
    `100_000_000` is conservative — Och programs nest at most ~20
    binders deep in practice.

    Exposed (not `private`) so the closedness predicate
    `Expr.closedAtLvl` (defined below) and downstream substrate proofs
    can refer to it. The encoding remains an internal detail; user code
    should not assume any particular value. -/
def levelOffset : Nat := 100_000_000

/-- Encode a de Bruijn level as a free level-var. -/
private def levelBvar (level : Nat) : Expr := .bvar (levelOffset + level)

/-- True iff `k` encodes a free level-var. Exposed for use in
    substrate hygiene proofs. -/
@[inline] def isLevelIdx (k : Nat) : Bool := k >= levelOffset

/-- Custom shift that does not touch level-vars. Standard `Expr.shift`
    would shift them, breaking absolute-position semantics. Otherwise
    mirrors `Expr.shift`. Structurally recursive.

    Exposed (not `private`) so substrate hygiene proofs in
    `Soundness/EvalSubstLemmas.lean` can refer to it. -/
def shiftL (d c : Nat) : Expr → Expr
  | .bvar k =>
      if isLevelIdx k then .bvar k
      else if k < c then .bvar k
      else .bvar (k + d)
  | .lam dom body => .lam (shiftL d c dom) (shiftL d (c + 1) body)
  | .iota ann body => .iota (shiftL d c ann) (shiftL d (c + 1) body)
  | .fix ann body => .fix (shiftL d c ann) (shiftL d (c + 1) body)
  | .letE val body => .letE (shiftL d c val) (shiftL d (c + 1) body)
  | .app f a => .app (shiftL d c f) (shiftL d c a)
  | .asc t ty => .asc (shiftL d c t) (shiftL d c ty)
  | .type => .type
  | .bot => .bot

/-- Custom substitution that does not touch level-vars.
    Standard `Expr.subst` would decrement level-vars > j, which is
    semantically wrong (levels are absolute, not relative). Mirrors
    `Expr.subst` otherwise. Structurally recursive on `e`.

    Exposed (not `private`) so substrate hygiene proofs in
    `Soundness/EvalSubstLemmas.lean` can refer to it. -/
def substL (e : Expr) (j : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar k =>
      if isLevelIdx k then .bvar k
      else if k == j then s
      else if k > j then .bvar (k - 1)
      else .bvar k
  | .lam dom body => .lam (substL dom j s) (substL body (j + 1) (shiftL 1 0 s))
  | .app f a => .app (substL f j s) (substL a j s)
  | .asc t ty => .asc (substL t j s) (substL ty j s)
  | .type => .type
  | .bot => .bot
  | .iota ann body => .iota (substL ann j s) (substL body (j + 1) (shiftL 1 0 s))
  | .fix ann body => .fix (substL ann j s) (substL body (j + 1) (shiftL 1 0 s))
  | .letE val body => .letE (substL val j s) (substL body (j + 1) (shiftL 1 0 s))

/-- Open a body under a fresh free level-var at the given depth.
    Mirrors `Closure.openFresh fuel depth` in NbE. -/
private def openFresh (body : Expr) (depth : Nat) : Expr :=
  substL body 0 (levelBvar depth)

/-- Inverse of `openFresh`: replace `levelBvar level` with `bvar 0`,
    shifting other bound bvars up by 1 to make room for the new
    binder. Other level-vars (different `level`) are unchanged.
    Used by `TyCheck` to abstract a synthesised body type back
    into a Π-type. -/
def closeLevelVar (level : Nat) (e : Expr) : Expr :=
  go 0 e
where
  go (c : Nat) : Expr → Expr
  | .bvar k =>
      if k == levelOffset + level then .bvar c
      else if k >= levelOffset then .bvar k
      else if k < c then .bvar k
      else .bvar (k + 1)
  | .lam dom body => .lam (go c dom) (go (c + 1) body)
  | .iota ann body => .iota (go c ann) (go (c + 1) body)
  | .fix ann body => .fix (go c ann) (go (c + 1) body)
  | .letE val body => .letE (go c val) (go (c + 1) body)
  | .app f a => .app (go c f) (go c a)
  | .asc t ty => .asc (go c t) (go c ty)
  | .type => .type
  | .bot => .bot

/-- True iff `e` is a "neutral" — its head is a free level-var or a
    stuck application thereof. Mirrors `Val.isNeutral`. Lambdas, iotas,
    fixes, type, bot are NOT neutral.

    Exposed (not `private`) so soundness proofs in
    `Soundness/SubCheckSubstNeutral.lean` can refer to it. -/
def isNeutral : Expr → Bool
  | .bvar k => isLevelIdx k
  | .app f _ => isNeutral f
  | _ => false

/-! ## Closedness modulo level-vars

The standard `Expr.closedAt n e` predicate (in `Syntax.lean`) requires
*every* `bvar k` to satisfy `k < n`.  Programs in the substitution
substrate violate that as soon as `openFresh` runs: a free level-var
is encoded as `bvar (levelOffset + lvl)`, an index far above any
realistic `n`.

For the substrate's hygiene proofs we therefore use a level-aware
predicate `Expr.closedAtLvl n e` that treats `bvar k` with `k ≥
levelOffset` as **closed** (they're values, not bound variables).  On
programs with no level-vars, `closedAtLvl 0 e ↔ closedAt 0 e`; on
opened programs with level-vars, only `closedAtLvl` is invariant under
the substitution substrate's operations.  This is the predicate
`evalSubst`-style proofs should be written against.

See `docs/ideas/soundness-strategy.md §4 wall-4` for context.

The predicate lives in `namespace Expr` (not `SubstEval`) so that dot
notation `e.closedAtLvl n` works the same way as `e.closedAt n`.
`levelOffset` is referenced from `SubstEval`, requiring the helper to
be re-exported below. -/

end SubstEval

namespace Expr

/-- Like `Expr.closedAt`, but treats `bvar`s with index ≥
    `SubstEval.levelOffset` (free level-vars) as closed. All other
    constructors recurse exactly as in `closedAt`. This is the right
    closedness invariant for substitution-substrate operations
    (`shiftL`, `substL`, `evalSubst`), which never disturb level-vars. -/
def closedAtLvl (n : Nat) : Expr → Bool
  | .bvar k => k < n || k >= SubstEval.levelOffset
  | .lam dom body => closedAtLvl n dom && closedAtLvl (n + 1) body
  | .app f a => closedAtLvl n f && closedAtLvl n a
  | .asc term ty => closedAtLvl n term && closedAtLvl n ty
  | .type => true
  | .bot => true
  | .iota ann body => closedAtLvl n ann && closedAtLvl (n + 1) body
  | .fix ann body => closedAtLvl n ann && closedAtLvl (n + 1) body
  | .letE val body => closedAtLvl n val && closedAtLvl (n + 1) body

end Expr

namespace SubstEval

open Expr (closedAtLvl)

/-- `closedAtLvl` is monotone in the cutoff. -/
theorem closedAtLvl_mono {e : Expr} {n m : Nat}
    (h : e.closedAtLvl n = true) (hnm : n ≤ m) : e.closedAtLvl m = true := by
  induction e generalizing n m with
  | bvar k =>
    simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr h2
  | lam dom body ih_dom ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_dom h.1 hnm, ih_body h.2 (by omega)⟩
  | app f a ih_f ih_a =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f h.1 hnm, ih_a h.2 hnm⟩
  | asc t y ih_t ih_y =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t h.1 hnm, ih_y h.2 hnm⟩
  | type => simp [closedAtLvl]
  | bot => simp [closedAtLvl]
  | iota ann body ih_ann ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hnm, ih_body h.2 (by omega)⟩
  | fix ann body ih_ann ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hnm, ih_body h.2 (by omega)⟩
  | letE val body ih_val ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_val h.1 hnm, ih_body h.2 (by omega)⟩

/-- A free level-var is `closedAtLvl n` for any `n`. -/
theorem closedAtLvl_levelBvar (lvl n : Nat) :
    (levelBvar lvl).closedAtLvl n = true := by
  simp only [levelBvar, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (Nat.le_add_right levelOffset lvl)

/-- `shiftL` preserves `closedAtLvl` (generalized). Mirrors
    `shift_closedAt`. The level-var arm of `shiftL` is the identity,
    and level-vars are unconditionally `closedAtLvl`. -/
theorem shiftL_closedAtLvl_gen (e : Expr) (n d c : Nat) (hc : c ≤ n)
    (h : e.closedAtLvl n = true) : (shiftL d c e).closedAtLvl (n + d) = true := by
  induction e generalizing n c with
  | bvar k =>
    simp only [shiftL, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    by_cases hLvl : isLevelIdx k
    · simp only [hLvl, ↓reduceIte, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
      simp only [isLevelIdx, decide_eq_true_eq] at hLvl
      exact Or.inr hLvl
    · simp only [hLvl, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
        rename_i hlt; exact Or.inl (by omega)
      · simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
        rename_i hge
        rcases h with h1 | h2
        · exact Or.inl (by omega)
        · simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
            decide_eq_false_iff_not, Nat.not_le] at hLvl
          exact Or.inr (by omega)
  | lam dom body ih_dom ih_body =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    refine ⟨ih_dom n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this
  | app f a ih_f ih_a =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f n c hc h.1, ih_a n c hc h.2⟩
  | asc t y ih_t ih_y =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t n c hc h.1, ih_y n c hc h.2⟩
  | type => simp [shiftL, closedAtLvl]
  | bot => simp [shiftL, closedAtLvl]
  | iota ann body ih_ann ih_body =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    refine ⟨ih_ann n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this
  | fix ann body ih_ann ih_body =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    refine ⟨ih_ann n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this
  | letE val body ih_val ih_body =>
    simp only [shiftL, closedAtLvl, Bool.and_eq_true] at h ⊢
    refine ⟨ih_val n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this

/-- `substL` preserves `closedAtLvl` (generalized). Mirrors
    `subst_closedAt_gen`. -/
theorem substL_closedAtLvl_gen (e : Expr) (j n : Nat) (s : Expr)
    (he : e.closedAtLvl (j + n + 1) = true) (hs : s.closedAtLvl (j + n) = true)
    : (substL e j s).closedAtLvl (j + n) = true := by
  induction e generalizing j s with
  | bvar k =>
    simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at he
    simp only [substL]
    by_cases hLvl : isLevelIdx k
    · simp only [hLvl, ↓reduceIte, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
      simp only [isLevelIdx, decide_eq_true_eq] at hLvl
      exact Or.inr hLvl
    · simp only [hLvl, Bool.false_eq_true, ↓reduceIte]
      by_cases heq : k == j
      · simp only [heq, ↓reduceIte]; exact hs
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        have hne : k ≠ j := by intro hh; simp [hh] at heq
        by_cases hgt : k > j
        · simp [hgt, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
          simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
            decide_eq_false_iff_not, Nat.not_le] at hLvl
          rcases he with h1 | h2
          · exact Or.inl (by omega)
          · omega
        · simp [hgt, closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
          rcases he with h1 | h2
          · exact Or.inl (by omega)
          · simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
              decide_eq_false_iff_not, Nat.not_le] at hLvl
            omega
  | type => simp [substL, closedAtLvl]
  | bot => simp [substL, closedAtLvl]
  | lam dom body ih_dom ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_dom, he_body⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_dom j s he_dom hs, ?_⟩
    have hshift : (shiftL 1 0 s).closedAtLvl (j + 1 + n) = true := by
      have h1 := shiftL_closedAtLvl_gen s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : body.closedAtLvl (j + 1 + n + 1) = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (shiftL 1 0 s) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this
  | app f a ih_f ih_a =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_f, he_a⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    exact ⟨ih_f j s he_f hs, ih_a j s he_a hs⟩
  | asc t y ih_t ih_y =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_t, he_y⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    exact ⟨ih_t j s he_t hs, ih_y j s he_y hs⟩
  | iota ann body ih_ann ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_ann, he_body⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_ann j s he_ann hs, ?_⟩
    have hshift : (shiftL 1 0 s).closedAtLvl (j + 1 + n) = true := by
      have h1 := shiftL_closedAtLvl_gen s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : body.closedAtLvl (j + 1 + n + 1) = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (shiftL 1 0 s) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this
  | fix ann body ih_ann ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_ann, he_body⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_ann j s he_ann hs, ?_⟩
    have hshift : (shiftL 1 0 s).closedAtLvl (j + 1 + n) = true := by
      have h1 := shiftL_closedAtLvl_gen s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : body.closedAtLvl (j + 1 + n + 1) = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (shiftL 1 0 s) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this
  | letE val body ih_val ih_body =>
    simp only [closedAtLvl, Bool.and_eq_true] at he
    obtain ⟨he_val, he_body⟩ := he
    simp only [substL, closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_val j s he_val hs, ?_⟩
    have hshift : (shiftL 1 0 s).closedAtLvl (j + 1 + n) = true := by
      have h1 := shiftL_closedAtLvl_gen s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : body.closedAtLvl (j + 1 + n + 1) = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (shiftL 1 0 s) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this

/-- `substL` at position 0 preserves `closedAtLvl`. -/
theorem substL_closedAtLvl {e s : Expr} {n : Nat}
    (he : e.closedAtLvl (n + 1) = true) (hs : s.closedAtLvl n = true)
    : (substL e 0 s).closedAtLvl n = true := by
  have := substL_closedAtLvl_gen e 0 n s (by simpa using he) (by simpa using hs)
  simpa using this

/-! ## Substitution-based open-term evaluator

Like `concEval` but treats free level-vars as values. Carries an
`unf` budget for fix/ι unfolds, mirroring NbE's schedule.

Result is an `Expr` in head-normal form: lambda, iota, fix, type, bot,
or a neutral spine. -/

/-- Default unfold bound. Match NbE for apples-to-apples behaviour. -/
def unfBound : Nat := 32

/-- Substitution-based head-normal-form evaluator. Decreasing on
    `(fuel, unf)` lex: every recursive call either decrements `fuel`
    (the outer `match fuel with | _+1 ⇒ …` consumes it) or holds
    `fuel` and decrements `unf` (the iota/fix unfold cases). -/
def evalSubst (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar k =>
      -- Free level-vars are neutral (return as-is). Bound bvars must
      -- not appear in well-formed input — they signal a stuck term.
      if isLevelIdx k then .ok (.bvar k)
      else .error s!"evalSubst: stuck on bound bvar {k}"
    | .type => .ok .type
    | .bot => .ok .bot
    | .lam _ _ => .ok e
    | .iota _ _ => .ok e
    | .fix _ _ => .ok e
    | .asc t _ => evalSubst fuel unf t
    | .letE val body => do
        let v ← evalSubst fuel unf val
        evalSubst fuel unf (substL body 0 v)
    | .app f a => do
        let f' ← evalSubst fuel unf f
        let a' ← evalSubst fuel unf a
        match f' with
        | .lam _dom body =>
            -- β: substitute argument into body.
            evalSubst fuel unf (substL body 0 a')
        | .iota _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              -- ι unfold: substitute self with the ι-value, then re-apply.
              let unfolded := substL body 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .fix _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              let unfolded := substL body 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | _ => .ok (.app f' a')

/-! ## Subtype check on Expr

Mirrors `subCheckVal` arm-by-arm. Uses `Expr` structural equality
(`DecidableEq`-derived `==`). `tyCtx[k]` is the type of the
level-bvar at level `k` — used by `neutralAscent` to ascend an
LHS neutral to its type when the spine doesn't match. Mirrors
NbE's `TyCtx`.

The recursion mixes WHNF re-evaluation with structural descent through
binders. Termination is captured by a lex `(fuel, phase)` measure
(see the module docstring): `subCheckSubst → subCheckSubstMatch`
decrements `fuel`, the reverse direction decrements `phase`, and all
other recursive calls decrement `fuel` directly. Equation lemmas
auto-generate.
-/

/-- Engine-internal type-context: `tyCtx[lvl]` is the type of the
    free level-var `freshLevelVar lvl`. Indexed by level (not by de
    Bruijn depth).

    Exposed (not `private`) so soundness proofs in
    `Soundness/SubCheckSubstNeutral.lean` can refer to it. -/
abbrev TyCtx := Array Expr

/-- Get the head level-var of a neutral spine. Returns `none` if `e`
    is not a neutral. -/
private def neutralHeadLevel : Expr → Option Nat
  | .bvar k => if isLevelIdx k then some (k - levelOffset) else none
  | .app f _ => neutralHeadLevel f
  | _ => none

/-- Internal: unfold a `.fix` / `.iota` wrapper in `ty` until a
    `.lam` is exposed. Used by `synthNeutralType` to walk a spine
    through types whose Π is wrapped in fix/iota (e.g. `Nat_`'s
    self-eliminator `fix N. ι self:N. λP:..`). The `inhab`
    argument is what to substitute for the ι-self when unfolding
    (typically the spine-head being applied). -/
private def exposePi (fuel : Nat) (inhab : Expr) (ty : Expr) :
    Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  /-- Structurally recursive on the unfold budget `n : Nat`. -/
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (substL body 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (substL body 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

mutual
  /-- Top-level subtype check arm. Forces WHNF on both sides, then
      delegates to `subCheckSubstMatch` for case-on-shape.

      Exposed (not `private`) so soundness proofs in
      `Soundness/SubCheckSubstNeutral.lean` can refer to it. -/
  def subCheckSubst (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      -- Force WHNF on both sides. Without this, types stored in
      -- tyCtx and inner doms can be un-evaluated Exprs whose
      -- structural equality doesn't match their reduced form.
      match evalSubst (fuel + 1) unfBound a, evalSubst (fuel + 1) unfBound b with
      | .ok a', .ok b' =>
          if a' == b' then .ok true
          else if seen.any (fun (av, bv) => a' == av && b' == bv) then .ok true
          else if b' == .type then .ok true
          else subCheckSubstMatch fuel tyCtx seen a' b'
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s => .error s
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- The per-shape case-split for `subCheckSubst`. Inputs are assumed
      to be in WHNF (the caller forces it). Exposed for soundness
      proofs. -/
  def subCheckSubstMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    let depth := tyCtx.size
    match a, b with
    -- Bot ⊑ anything ([S-BotL]).
    | .bot, _ => .ok true
    -- λ ⊑ λ: contravariant on domain, covariant on body (under fresh).
    -- Push `domB` (narrower / target) — matches declarative spec.
    -- See SubCheckVal.lean A6 comment for history.
    | .lam domA bodyA, .lam domB bodyB => do
        let contra ← subCheckSubst fuel tyCtx seen domB domA
        if !contra then return false
        let bodyA' := openFresh bodyA depth
        let bodyB' := openFresh bodyB depth
        subCheckSubst fuel (tyCtx.push domB) seen bodyA' bodyB'
    -- ι ⊑ ι: structural attempt then iotaIntro fallback.
    | .iota annA bodyA, .iota annB bodyB =>
        let seen' := (a, b) :: seen
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen' annA annB
          if !annOk then return false
          let bodyA' := openFresh bodyA depth
          let bodyB' := openFresh bodyB depth
          subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
        match structural with
        | .ok true => .ok true
        | _ => do
          let okAnn ← subCheckSubst fuel tyCtx seen' a annB
          if !okAnn then .ok false
          else do
            let bodyB' := substL bodyB 0 a
            match evalSubst (fuel + 1) unfBound bodyB' with
            | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
            | _ => .ok false
    -- fix ⊑ fix: structural attempt then unfold-RHS fallback.
    | .fix annA bodyA, .fix annB bodyB =>
        let seen' := (a, b) :: seen
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen' annA annB
          if !annOk then return false
          let bodyA' := openFresh bodyA depth
          let bodyB' := openFresh bodyB depth
          subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
        match structural with
        | .ok true => .ok true
        | _ => do
          let unfolded := substL bodyB 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    -- _ ⊑ ι: iotaIntro.
    | _, .iota ann bodyB => do
        let seen' := (a, b) :: seen
        let okAnn ← subCheckSubst fuel tyCtx seen' a ann
        if !okAnn then .ok false
        else do
          let bodyB' := substL bodyB 0 a
          match evalSubst (fuel + 1) unfBound bodyB' with
          | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
          | _ => .ok false
    -- _ ⊑ fix: unfoldFixR.
    | _, .fix _ann bodyB => do
        -- Neutral-LHS short-circuit: if `a` is a neutral whose ascended
        -- type via tyCtx is structurally `b`, accept immediately. This
        -- avoids a divergence pattern where unfolding the fix on the
        -- RHS produces a value that the post-unfold dispatch then
        -- compares back against the original neutral on the LHS,
        -- where the seen-set's stored entries don't match the post-
        -- substitution shapes (substL renames bound vars). The pure
        -- ascent path closes via Refl with no substitution drift.
        if isNeutral a then
          match synthNeutralType fuel tyCtx a with
          | .ok (some ty) =>
              if ty == b then .ok true
              else
                let seen' := (a, b) :: seen
                let unfolded := substL bodyB 0 b
                match evalSubst (fuel + 1) unfBound unfolded with
                | .ok b' => subCheckSubst fuel tyCtx seen' a b'
                | _ => .ok false
          | _ =>
              let seen' := (a, b) :: seen
              let unfolded := substL bodyB 0 b
              match evalSubst (fuel + 1) unfBound unfolded with
              | .ok b' => subCheckSubst fuel tyCtx seen' a b'
              | _ => .ok false
        else
          let seen' := (a, b) :: seen
          let unfolded := substL bodyB 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    -- fix ⊑ _: unfoldFixL.
    | .fix _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := substL bodyA 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    -- ι ⊑ _: iotaElim.
    | .iota _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := substL bodyA 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    -- Neutrals: try spine-compare; if that fails (or for one-sided
    -- neutrals), ascend to the LHS neutral's type and recurse.
    | _, _ =>
        if isNeutral a && isNeutral b then
          match subCheckSpine fuel tyCtx seen a b with
          | .ok true => .ok true
          | _ => neutralAscent fuel tyCtx seen a b
        else if isNeutral a then
          neutralAscent fuel tyCtx seen a b
        else
          .ok false
  termination_by (fuel, 1)
  decreasing_by all_goals (simp_wf; omega)

  /-- Compare two neutral spines structurally. Heads must be equal
      level-vars; arguments must be pairwise *equivalent* (any-
      variance). Exposed for soundness proofs. -/
  def subCheckSpine (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a, b with
      | .bvar k1, .bvar k2 =>
          if k1 == k2 && isLevelIdx k1 then .ok true else .ok false
      | .app f1 v1, .app f2 v2 => do
          let hd ← subCheckSpine fuel tyCtx seen f1 f2
          if !hd then return false
          let fwd ← subCheckSubst fuel tyCtx seen v1 v2
          if !fwd then return false
          subCheckSubst fuel tyCtx seen v2 v1
      | _, _ => .ok false
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral spine and check against `b`.
      Mirrors NbE's `neutralAscent`. Exposed for soundness proofs. -/
  def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match synthNeutralType fuel tyCtx a with
      | .ok (some ty) => subCheckSubst fuel tyCtx seen ty b
      | _ => .ok false
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral. Walks the spine, looking up
      head levels in `tyCtx` and applying argument types to function
      types via `substL`. When the synthesised type at a spine step
      is a `.fix` or `.iota` (e.g. `Nat_`'s self-eliminator), unfold
      it via `exposePi` to expose the underlying `.lam` and continue.
      A `.fix` at the spine head (e.g. `add_`) ascends to its
      annotation. Exposed for soundness proofs. -/
  def synthNeutralType (fuel : Nat) (tyCtx : TyCtx)
      (a : Expr) : Outcome (Option Expr) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a with
      | .bvar k =>
          if isLevelIdx k then
            let lvl := k - levelOffset
            .ok (tyCtx[lvl]?)
          else .ok none
      | .fix ann _ =>
          -- A fix's type-via-Refl is itself, but for spine walking
          -- we want the *function-type* under which arguments
          -- consume — that's the annotation.
          match evalSubst (fuel + 1) unfBound ann with
          | .ok ann' => .ok (some ann')
          | _ => .ok none
      | .app f arg => do
          match (← synthNeutralType fuel tyCtx f) with
          | some ty =>
              -- Expose a Π via fix/iota unfolding if needed. The
              -- inhabitant for ι-unfolding is `f` (the spine head
              -- that's being applied), since that's what
              -- structurally inhabits the ι annotation here.
              match exposePi fuel f ty with
              | some (.lam _dom retTy) =>
                  let retTy' := substL retTy 0 arg
                  match evalSubst (fuel + 1) unfBound retTy' with
                  | .ok r => .ok (some r)
                  | _ => .ok none
              | _ => .ok none
          | _ => .ok none
      | _ => .ok none
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)
end

/-- Structural subtype check on closed `Expr`s: WHNF both sides,
    then descend through `subCheckSubst`. Public so `TyCheck.typeCheck`
    can call it on conversion goals; the `subCheckSubst` mutual
    block stays private. -/
def subCheck (fuel : Nat) (a b : Expr) : Outcome Bool := do
  let a' ← evalSubst fuel unfBound a
  let b' ← evalSubst fuel unfBound b
  subCheckSubst fuel #[] [] a' b'

/-! ## Open-context API for `TyCheck`

The bidirectional type-checker (`Och/TyCheck.lean`) walks an open
`Expr` whose free variables are encoded as level-vars (the same
`bvar (levelOffset + k)` trick the engine uses internally). It
needs three things from this module:

  - a way to reference a fresh level-var (`freshLevelVar`),
  - a way to open a binder under that fresh (`openFreshTop`),
  - a way to substitute a value for the outermost binder
    (`substTop`),
  - a way to compare two types in a non-empty type context
    (`subCheckOpen`).

These are thin wrappers around the otherwise-private level-var
primitives; we expose only the ones `TyCheck` actually needs.
The `subCheckSubst` mutual block, `shiftL`, `isNeutral`, the
private flag on `substL`/`openFresh` all stay internal — `TyCheck`
does not need them directly.
-/

/-- The level-var encoding of de Bruijn level `level`. -/
def freshLevelVar (level : Nat) : Expr := levelBvar level

/-- If `e` is a free level-var, return its level; otherwise `none`. -/
def asLevelVar : Expr → Option Nat
  | .bvar k => if isLevelIdx k then some (k - levelOffset) else none
  | _ => none

/-- Open a body's outermost binder under a fresh level-var at
    the given depth. Public mirror of the internal `openFresh`. -/
def openFreshTop (body : Expr) (depth : Nat) : Expr :=
  openFresh body depth

/-- Substitute a value for the outermost binder of `body`, leaving
    level-vars untouched. Used by `TyCheck` to instantiate Π
    codomains with the actual argument and to discharge `let`
    binders. Public mirror of the internal `substL`. -/
def substTop (body : Expr) (value : Expr) : Expr :=
  substL body 0 value

/-- Subtype check in a non-empty type context. `tyCtx[k]` is the
    type of `freshLevelVar k`. Forces WHNF on both sides, then
    delegates to the private structural engine. -/
def subCheckOpen (fuel : Nat) (tyCtx : Array Expr) (a b : Expr) :
    Outcome Bool := do
  let a' ← evalSubst fuel unfBound a
  let b' ← evalSubst fuel unfBound b
  subCheckSubst fuel tyCtx [] a' b'

/-- Walk a neutral spine to compute its declarative type, looking
up free level-vars in `tyCtx` and applying argument types through
`Π` bodies via `substL`. Public mirror of the internal
`synthNeutralType` (used by `subCheckSubst`'s `[S-Ascent]` arm).

`Och.synth` calls this from its `.app` arm to recover the Π type
of a neutral function head: the bvar-arm of synth returns the
variable itself (per paper-B's Refl-typing convention), so we need
the spine ascent to expose a Π.

- `.ok (some ty)` — neutral head ascended to type `ty` (in WHNF).
- `.ok none` — `a` is not a neutral, or its head is unbound.
- `.outOfFuel` — fuel exhausted.

Returns `.ok none` for non-neutral inputs (the synth caller will
notice and report `applied non-Π head`). -/
def neutralType (fuel : Nat) (tyCtx : Array Expr) (a : Expr) :
    Outcome (Option Expr) :=
  synthNeutralType fuel tyCtx a

/-! ## Π-exposure helper

`Och.synth` (`Och/API.lean`) needs to destructure the synthesised
type/value of an applied head as a `.lam dom body` (a Π). When the
head is a `.fix`/`.iota`, we unfold the wrapper one or more times
to expose the underlying Π. This function does that — it's a
public mirror of the same logic that lived as a private helper in
`Och/TyCheck.lean`. -/

/-- Unfold a `.fix` / `.iota` wrapper in `ty` until a `.lam`
(Π) is exposed, returning the Π. The `inhab` argument is what
to substitute for the `ι`-self when unfolding `.iota` (= the
*inhabitant* whose type we're computing — `n : ι self. B` means
`n : B[self:=n]`). For `.fix`, the self is substituted with the
fix itself (μ-unfold).

- `some (.lam dom body)` — Π exposed.
- `some other` — non-Π head (e.g. `.type`, neutral) after WHNF.
- `none` — `.bot` (non-applicable; see `docs/ideas/bottom.md`)
  or evaluation failure. -/
def whnfPi (fuel : Nat) (inhab : Expr) (ty : Expr) : Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (substL body 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (substL body 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

end SubstEval
