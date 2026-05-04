import Pss.Mpss.AvoidsPro

/-! # `Pss.Mpss.MEqRedSize` — derivation-size measure on `MEqRed`

Iter 3 viability spike for the body-diamond unblock identified in
commit `62b9c3f` (Diamond.lean iter-2 docstring at lines ~436-560).

## Why this exists

`Lemma_2_DiamondMEqRed_core` (Diamond.lean:2014+) is currently proved
by `induction h₁ generalizing t₂` over the structure of the
**source-side** derivation. In the `MEqRed.fOp × MEqRed.fOp` cell the
inversion of `h₂ : MEqRed Γ (α::s) (.abs t body) v₂` gives back a
**body** sub-derivation `hbody_dst y _ : MEqRed (⟨y,α,.equ⟩::Γ) s
(body^[y]) (body₂^[y])` for which **no induction hypothesis is
available** — the structural recursion only sees subterms of `h₁`,
not subterms of `h₂`.

Iter-2's analysis recommended switching `_core`'s recursion to a
derivation-size measure so that body sub-derivations of either side
of the diamond get IHs. This file ships the load-bearing measure;
iter 4 will refactor `_core` to use it.

## What this file ships

* `MEqRed.derSize : MEqRed Γ s u v → Nat` — counts constructors,
  recursing under cofinite binders via the canonical `pickFresh L`
  sample (mirror of how `avoidsPro` and `AvoidsProUniv` recurse).
* Per-constructor `derSize_*` simp lemmas (definitional unfolds).
* Strict-decrease lemmas `derSize_*_lt` for every sub-derivation
  position. The load-bearing one is `derSize_fOp_body` (giving the
  body-diamond IH access in iter 4's `_core` refactor).

## Design notes

* Defined via `MEqRed.rec` (Type-valued post `16eed34`), matching the
  definitional style of `avoidsPro` (AvoidsPro.lean:495+) and
  `AvoidsProUniv` (AvoidsProUniv.lean:57+). This sidesteps the
  equation compiler's structural-decreasing synthesis across
  `∀ y, y ∉ L → ...` arguments.
* `noncomputable` because `pickFresh` uses `Classical.choice`.
* The cofinite-arm body sample is canonicalized to `pickFresh L` —
  this matches the convention used by `avoidsPro`'s simp lemmas, so
  downstream consumers that need to unfold `derSize` at the body
  position get a single canonical sample point.

## Iter-4 follow-up (NOT in this file)

Refactor `Lemma_2_DiamondMEqRed_core` from
`induction h₁ generalizing t₂` to a `noncomputable def` with explicit
pattern-matching, terminated by `decreasing_by exact derSize_*_lt _`.
The body-diamond cell can then make a recursive call to `_core` on
the body sub-derivations of either fOp/fOp leg, since
`derSize_fOp_body` proves the recursive measure strictly decreases. -/

namespace Pss

/-! ## §1. The derivation-size measure -/

/-- Derivation size: number of `MEqRed` constructors in the
derivation, recursing under cofinite binders at the canonical
`pickFresh L` sample.

Per-constructor counts:

* Leaf constructors (`var`, `top`, `tAp`) contribute `1`.
* Single-sub-derivation `pro` contributes `1 + derSize hα`.
* Binary `app` contributes `1 + derSize hu + derSize hv`.
* Cofinite `bet` contributes `1 + derSize (hbody (pickFresh L) _)
  + derSize hv`.
* Cofinite `fun_` / `fOp` contribute `1 + derSize hT
  + derSize (hbody (pickFresh L) _)`.

Defined via `MEqRed.rec` for the same reason as `avoidsPro` /
`AvoidsProUniv`: the equation compiler can't synthesise a structural
decrease across `∀ y, y ∉ L → MEqRed ...` cofinite arguments. -/
noncomputable def MEqRed.derSize {Γ s u v} (h : MEqRed Γ s u v) : Nat :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => Nat)
    -- Me-Pro: 1 + recurse into the inner promotion derivation.
    (fun _ _ _ ihα => 1 + ihα)
    -- Me-Bet: 1 + body sample + operand.
    (fun L _ _hbody _ _ ihbody ihv =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      1 + ihbody y hyL + ihv)
    -- Me-Top: leaf.
    (fun _ => 1)
    -- Me-App: 1 + operator + operand.
    (fun _ _ ihu ihv => 1 + ihu + ihv)
    -- Me-Var: leaf.
    (fun _ => 1)
    -- Me-Fun: 1 + bound-annotation + body sample.
    (fun L _ _hbody _ iht ihbody =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      1 + iht + ihbody y hyL)
    -- Me-TAp: leaf.
    (fun _ _ _ => 1)
    -- Me-FOp: 1 + bound-annotation + body sample.
    (fun L _ _hbody _ iht ihbody =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      1 + iht + ihbody y hyL)
    h

/-! ## §2. Per-constructor `simp` unfoldings

These mirror the `avoidsPro_*` family (AvoidsPro.lean:531+) so
downstream consumers can unfold `derSize` at the constructor level
without touching the recursor. -/

@[simp] theorem derSize_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') :
    MEqRed.derSize (MEqRed.pro hpv heq hα) = 1 + MEqRed.derSize hα := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    MEqRed.derSize (MEqRed.bet L hLCt hbody hUni hv) =
      1 + MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L))
        + MEqRed.derSize hv := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_top {Γ s} (hpv : PrevalidExt Γ s) :
    MEqRed.derSize (MEqRed.top hpv) = 1 := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    MEqRed.derSize (MEqRed.app hu hv) =
      1 + MEqRed.derSize hu + MEqRed.derSize hv := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_var {Γ s y} (hpv : PrevalidExt Γ s) :
    MEqRed.derSize (@MEqRed.var Γ s y hpv) = 1 := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize (MEqRed.fun_ L ht hbody hUni) =
      1 + MEqRed.derSize ht
        + MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L)) := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) :
    MEqRed.derSize (MEqRed.tAp hpv hLCu hfvu) = 1 := by
  unfold MEqRed.derSize; rfl

@[simp] theorem derSize_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize (@MEqRed.fOp Γ s t t' α body body' L ht hbody hUni) =
      1 + MEqRed.derSize ht
        + MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L)) := by
  unfold MEqRed.derSize; rfl

/-! ## §3. Sub-derivation strict-decrease lemmas

For every constructor with a sub-derivation, prove that the
sub-derivation's `derSize` is **strictly less** than the parent's.
These will populate `decreasing_by` clauses in the iter-4 `_core`
refactor.

Each proof unfolds the relevant `derSize_*` simp lemma and closes
with `omega`. -/

theorem derSize_pro_inner {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') :
    MEqRed.derSize hα < MEqRed.derSize (MEqRed.pro hpv heq hα) := by
  simp only [derSize_pro]; omega

theorem derSize_app_left {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    MEqRed.derSize hu < MEqRed.derSize (MEqRed.app hu hv) := by
  simp only [derSize_app]; omega

theorem derSize_app_right {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    MEqRed.derSize hv < MEqRed.derSize (MEqRed.app hu hv) := by
  simp only [derSize_app]; omega

theorem derSize_bet_operand {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    MEqRed.derSize hv < MEqRed.derSize (MEqRed.bet L hLCt hbody hUni hv) := by
  simp only [derSize_bet]; omega

theorem derSize_fun_annot {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize ht < MEqRed.derSize (MEqRed.fun_ L ht hbody hUni) := by
  simp only [derSize_fun_]; omega

theorem derSize_fOp_annot {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize ht <
      MEqRed.derSize (@MEqRed.fOp Γ s t t' α body body' L ht hbody hUni) := by
  simp only [derSize_fOp]; omega

/-! ### §3.1. Body-sample strict-decrease lemmas (load-bearing)

These are the lemmas iter 4 will use to license recursive calls of
`_core` on body sub-derivations of `MEqRed.bet` / `MEqRed.fun_` /
`MEqRed.fOp`. The sample point is `pickFresh L` to match the
convention in `derSize_*` simp lemmas. -/

/-- Body-sample strict-decrease for `Me-Bet`.

The body sub-derivation taken at the canonical `pickFresh L` sample
has strictly smaller `derSize` than the whole `Me-Bet` derivation.
This is the lemma that licenses the body-diamond recursive call in
iter 4's `_core` refactor for the `Me-Bet × Me-Bet` cell. -/
theorem derSize_bet_body {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L)) <
      MEqRed.derSize (MEqRed.bet L hLCt hbody hUni hv) := by
  simp only [derSize_bet]; omega

/-- Body-sample strict-decrease for `Me-Fun`.

Same shape as `derSize_bet_body`, for the un-applied abstraction. -/
theorem derSize_fun_body {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L)) <
      MEqRed.derSize (MEqRed.fun_ L ht hbody hUni) := by
  simp only [derSize_fun_]; omega

/-- Body-sample strict-decrease for `Me-FOp`.

**This is the load-bearing lemma** for the body-diamond unblock. The
iter-2 blocker was: in the `Me-FOp × Me-FOp` cell of `_core`,
`induction h₁` does NOT expose body sub-derivations of `h₂`'s
`MEqRed.fOp` — there's no IH for them. With `_core` refactored to WF
recursion on `derSize`, the cell can recurse on either body
sub-derivation since both have strictly smaller `derSize` than their
parent (this lemma). -/
theorem derSize_fOp_body {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    MEqRed.derSize (hbody (pickFresh L) (pickFresh_notMem L)) <
      MEqRed.derSize (@MEqRed.fOp Γ s t t' α body body' L ht hbody hUni) := by
  simp only [derSize_fOp]; omega

end Pss
