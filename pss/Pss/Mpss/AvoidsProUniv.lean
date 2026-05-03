import Pss.Mpss.Reductions

/-! # `Pss.Mpss.AvoidsProUniv` — universal cofinite avoidance predicate

Phase 5g.3a: extracted from `Pss.Mpss.AvoidsPro` to break the import
cycle that would otherwise arise once `MEqRed`'s cofinite constructors
mention `AvoidsProUniv` directly (Phase 5g.3b).

Today's chain is `Reductions ← ContextRed ← Substitution ← AvoidsPro`,
so if `Reductions` imported `AvoidsPro` it would circle back. The
fragments hosted here (`def AvoidsProUniv`, its eight per-constructor
simp lemmas, `def CofinAvoidsProSelfUniv`, and its eight per-constructor
simp lemmas) depend only on `MEqRed.rec` plus `Finset` / `String` /
`PrevalidExt` / `Ne` / `And`, so they hoist cleanly into a module that
imports only `Pss.Mpss.Reductions`.

The cast-invariance lemmas, the `AvoidsProUniv → avoidsPro = true`
bridge, and `AvoidsProUniv_refl` remain in `Pss.Mpss.AvoidsPro` because
they depend on the substitution / `MEqRed.refl` machinery downstream of
`Reductions`.

## §2.5. Universal cofinite avoidance: `AvoidsProUniv`

Phase 5a of the Type-aware MEqRed architectural refactor. Mirrors
`avoidsPro` but at every cofinite arm (`bet`/`fun_`/`fOp`), universally
quantifies over the cofinite witness rather than sampling at
`pickFresh L`. This lifts above the Bool `avoidsPro`'s sample-point
fragility:

* The Bool `avoidsPro` evaluates `hbody (pickFresh L) _`'s avoidance —
  fragile because future `rename_stray`-style helpers widen `L` to
  `L ∪ {y, z}`, shifting `pickFresh L` to `pickFresh (L ∪ {y, z})` and
  breaking equality across the rename.
* `AvoidsProUniv` evaluates `∀ y ∉ L, ...`, which is preserved across
  any `L ↦ L'` widening (a universal over a smaller cofinite set is
  trivially restrictable to a subset's complement: if `y ∉ L'` and
  `L ⊆ L'` then `y ∉ L`, so the universal over `L`'s complement
  applies).

Designed as the rename-stable foundation for the cofin* family in
Phase 5b/5c. The bridge `AvoidsProUniv → avoidsPro = true` (in
`Pss.Mpss.AvoidsPro`) lets existing Bool consumers continue to work
unchanged.

Defined via `MEqRed.rec` (matching the style of `avoidsPro`) so that
the cofinite arms' functional bodies are handled cleanly without the
equation compiler needing to synthesise a structural decreasing
measure across a `∀ y, y ∉ L → ...` argument. -/

namespace Pss

/-- Universal Prop-valued cofinite avoidance.

Mirror of the Bool `avoidsPro`: `AvoidsProUniv h x` holds iff no
`Me-Pro` step in `h` promotes `x`, but with each cofinite arm
quantified universally over the witness rather than sampled. -/
def AvoidsProUniv {Γ s u v} (h : MEqRed Γ s u v) (x : String) : Prop :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => String → Prop)
    -- Me-Pro: y ≠ x ∧ recurse on inner derivation.
    (fun {_ _ y _ _} _ _ _ ihα x => y ≠ x ∧ ihα x)
    -- Me-Bet: universal over the cofinite witness; recurse on operand.
    (fun {_ _ _ _ _ _ _} L _ _hbody _ _ ihbody ihv x =>
      (∀ y (hy : y ∉ L), ihbody y hy x) ∧ ihv x)
    -- Me-Top: vacuous.
    (fun _ _ => True)
    -- Me-App: both subterms.
    (fun _ _ ihu ihv x => ihu x ∧ ihv x)
    -- Me-Var: vacuous.
    (fun _ _ => True)
    -- Me-Fun: bound annotation + universal over cofinite witness.
    (fun {_ _ _ _ _} L _ _hbody _ iht ihbody x =>
      iht x ∧ ∀ y (hy : y ∉ L), ihbody y hy x)
    -- Me-TAp: vacuous.
    (fun _ _ _ _ => True)
    -- Me-FOp: bound annotation + universal over cofinite witness.
    (fun {_ _ _ _ _ _ _} L _ _hbody _ iht ihbody x =>
      iht x ∧ ∀ y (hy : y ∉ L), ihbody y hy x)
    h x

/-! ### §2.5.1. Per-constructor simp lemmas for `AvoidsProUniv` -/

@[simp] theorem AvoidsProUniv_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') (x : String) :
    AvoidsProUniv (MEqRed.pro hpv heq hα) x ↔ y ≠ x ∧ AvoidsProUniv hα x := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') (x : String) :
    AvoidsProUniv (MEqRed.bet L hLCt hbody hUni hv) x ↔
      (∀ y (hy : y ∉ L), AvoidsProUniv (hbody y hy) x) ∧
      AvoidsProUniv hv x := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_top {Γ s} (hpv : PrevalidExt Γ s) (x : String) :
    AvoidsProUniv (MEqRed.top hpv) x ↔ True := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') (x : String) :
    AvoidsProUniv (MEqRed.app hu hv) x ↔
      AvoidsProUniv hu x ∧ AvoidsProUniv hv x := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_var {Γ s y} (hpv : PrevalidExt Γ s) (x : String) :
    AvoidsProUniv (@MEqRed.var Γ s y hpv) x ↔ True := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    AvoidsProUniv (MEqRed.fun_ L ht hbody hUni) x ↔
      AvoidsProUniv ht x ∧
      ∀ y (hy : y ∉ L), AvoidsProUniv (hbody y hy) x := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    AvoidsProUniv (MEqRed.tAp hpv hLCu hfvu) x ↔ True := by
  unfold AvoidsProUniv; rfl

@[simp] theorem AvoidsProUniv_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    AvoidsProUniv (MEqRed.fOp L ht hbody hUni) x ↔
      AvoidsProUniv ht x ∧
      ∀ y (hy : y ∉ L), AvoidsProUniv (hbody y hy) x := by
  unfold AvoidsProUniv; rfl

/-! ### §2.5.4. `CofinAvoidsProSelfUniv` — universal version of `cofinAvoidsProSelf`

Phase 5d analog of `cofinAvoidsProSelf` (§3.3 of `Pss.Mpss.AvoidsPro`)
for the AvoidsProUniv architecture. At every `fOp` arm, asserts that
for ALL cofinite witnesses `y_i ∉ L`, the body derivation `hbody y_i _`
universally avoids `y_i` itself (i.e.
`AvoidsProUniv (hbody y_i _) y_i`).

Used by `MEqRed.stack_head_replace_univ_exists`: when stack_replace
delegates to `equ_head_replace_univ` at the fOp Case A, it needs the
body to avoid the binder name `y_i`. The universal form makes this
rename-stable (matches `AvoidsProUniv`'s `∀ y ∉ L, ...` shape).

Why this isn't alpha-equivariance: like `AvoidsProUniv`, this is a
Prop-valued universal — preserved across rename composition because
restricting `∀ y ∉ L_small, ...` to the smaller cofinite set
`L_widened ⊆ L_small`-complement is trivial. -/

def CofinAvoidsProSelfUniv {Γ s u v} (h : MEqRed Γ s u v) : Prop :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => Prop)
    -- Me-Pro: recurse on the inner derivation.
    (fun _ _ _ ihα => ihα)
    -- Me-Bet: propagate through body recursion + operand.
    (fun {_ _ _ _ _ _ _} L _ _ _ _ ihbody ihv =>
      (∀ y (hy : y ∉ L), ihbody y hy) ∧ ihv)
    -- Me-Top: leaf.
    (fun _ => True)
    -- Me-App: recurse on both subterms.
    (fun _ _ ihu ihv => ihu ∧ ihv)
    -- Me-Var: leaf.
    (fun _ => True)
    -- Me-Fun: propagate (no .equ swap; just bound recursion).
    (fun {_ _ _ _ _} L _ _ _ iht ihbody =>
      iht ∧ ∀ y (hy : y ∉ L), ihbody y hy)
    -- Me-TAp: leaf.
    (fun _ _ _ => True)
    -- Me-FOp: HERE is the body-self-avoidance condition. For every
    -- cofinite witness y, the body universally avoids y itself.
    (fun {_ _ _ _ _ _ _} L _ hbody _ iht ihbody =>
      iht ∧ ∀ y (hy : y ∉ L), AvoidsProUniv (hbody y hy) y ∧ ihbody y hy)
    h

@[simp] theorem CofinAvoidsProSelfUniv_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') :
    CofinAvoidsProSelfUniv (MEqRed.pro hpv heq hα) ↔
      CofinAvoidsProSelfUniv hα := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_bet {Γ s t v v' body body'}
    (L : Finset String) (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    CofinAvoidsProSelfUniv (MEqRed.bet L hLCt hbody hUni hv) ↔
      (∀ y (hy : y ∉ L), CofinAvoidsProSelfUniv (hbody y hy)) ∧
      CofinAvoidsProSelfUniv hv := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_top {Γ s} (hpv : PrevalidExt Γ s) :
    CofinAvoidsProSelfUniv (MEqRed.top hpv) ↔ True := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    CofinAvoidsProSelfUniv (MEqRed.app hu hv) ↔
      CofinAvoidsProSelfUniv hu ∧ CofinAvoidsProSelfUniv hv := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_var {Γ s y} (hpv : PrevalidExt Γ s) :
    CofinAvoidsProSelfUniv (@MEqRed.var Γ s y hpv) ↔ True := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_fun_ {Γ t t' body body'}
    (L : Finset String) (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    CofinAvoidsProSelfUniv (MEqRed.fun_ L ht hbody hUni) ↔
      CofinAvoidsProSelfUniv ht ∧
      ∀ y (hy : y ∉ L), CofinAvoidsProSelfUniv (hbody y hy) := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) :
    CofinAvoidsProSelfUniv (MEqRed.tAp hpv hLCu hfvu) ↔ True := by
  unfold CofinAvoidsProSelfUniv; rfl

@[simp] theorem CofinAvoidsProSelfUniv_fOp {Γ s t t' α body body'}
    (L : Finset String) (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    CofinAvoidsProSelfUniv (MEqRed.fOp L ht hbody hUni) ↔
      CofinAvoidsProSelfUniv ht ∧
      ∀ y (hy : y ∉ L),
        AvoidsProUniv (hbody y hy) y ∧ CofinAvoidsProSelfUniv (hbody y hy) := by
  unfold CofinAvoidsProSelfUniv; rfl

end Pss
