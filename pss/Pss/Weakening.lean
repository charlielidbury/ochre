import Pss.Declarative
import Pss.Induction
import Pss.Basic

/-!
# Weakening for the declarative system (Figure 1)

Renaming transport for the declarative block `CtxWf / Wf / WellSub / Sub`,
the load-bearing infrastructure for the §5 substitution lemma (Lemma 5.4).

Design note: the transport is *insertion-based* — we insert one well-formed
entry `a` at position `|Ξ|` of a context `Ξ ++ Γ₀` (`Ctx.insertAt`) and
rename with `upAt |Ξ|`. A general renaming-morphism formulation
(`ρ` with `Bound`-transport + a `CtxWf Δ` clause) is *not* provable by rule
induction here: W-FUN and DS-FUN extend the context with a bound `t` for
which no well-formedness induction hypothesis exists, so the morphism
extension obligation `Wf Δ (t.rename ρ)` cannot be discharged. The
split-based formulation avoids this entirely: entries of `Ξ` (well-formed
or junk) transport syntactically, and only the single inserted entry `a`
carries a `Wf Γ₀ a` obligation, used exactly at the `CtxWf` leaves.
-/

namespace Pss

/-! ## Presuppositions

Every term-level judgment of Figure 1 presupposes a well-formed context:
the leaves (W-VAR, W-TOP) carry `Γ wf`, and every derivation bottoms out
in such a leaf for its own context. -/

private theorem wf_presup :
    (∀ Γ, CtxWf Γ → True)
    ∧ (∀ Γ t, Wf Γ t → CtxWf Γ)
    ∧ (∀ Γ t r u, WellSub Γ t r u → CtxWf Γ)
    ∧ (∀ Γ t r u, Sub Γ t r u → True) :=
  decl_induction
    (motC := fun _ => True)
    (motW := fun Γ _ => CtxWf Γ)
    (motWS := fun Γ _ _ _ => CtxWf Γ)
    (motS := fun _ _ _ _ => True)
    (ctx_nil := trivial)
    (ctx_cons := fun _ _ _ _ => trivial)
    (wf_var := fun hC _ _ => hC)
    (wf_top := fun hC _ => hC)
    (wf_fn := fun _ ih => by cases ih with | cons h _ => exact h)
    (wf_app := fun _ _ ih _ => ih)
    (wsub_sub := fun _ _ _ ih _ _ => ih)
    (sub_trans := fun _ _ _ _ _ _ => trivial)
    (sub_symm := fun _ _ => trivial)
    (sub_eq := fun _ _ => trivial)
    (sub_var := trivial)
    (sub_top := trivial)
    (sub_fn := fun _ _ _ _ => trivial)
    (sub_app := fun _ _ _ _ => trivial)
    (sub_eapp := trivial)
    (sub_etop := trivial)
    (sub_evar := fun _ => trivial)

/-- `Γ ⊢ t wf` presupposes `Γ wf`. -/
theorem Wf.ctxWf {Γ : Ctx} {t : Term} (h : Wf Γ t) : CtxWf Γ :=
  wf_presup.2.1 Γ t h

/-- `Γ ⊢ t ⊲wf u` presupposes `Γ wf`. -/
theorem WellSub.ctxWf {Γ : Ctx} {t u : Term} {r : Rel} (h : WellSub Γ t r u) :
    CtxWf Γ := wf_presup.2.2.1 Γ t r u h

/-- Inversion of W-GAM2: the head entry is well-formed in the tail. -/
theorem CtxWf.head_wf {Γ : Ctx} {t : Term} (h : CtxWf (t :: Γ)) : Wf Γ t := by
  cases h with | cons _ h => exact h

/-- Inversion of W-GAM2: the tail of a well-formed context is well-formed. -/
theorem CtxWf.tail {Γ : Ctx} {t : Term} (h : CtxWf (t :: Γ)) : CtxWf Γ := by
  cases h with | cons h _ => exact h

/-! ## The insertion renaming `upAt` -/

/-- The renaming that inserts one fresh variable at de Bruijn level `n`:
indices `< n` are untouched, indices `≥ n` are shifted up by one. -/
def upAt (n : Nat) (x : Nat) : Nat := if x < n then x else x + 1

@[simp] theorem upAt_zero : upAt 0 = (· + 1) := by
  funext x; simp [upAt]

/-- Lifting `upAt n` under a binder is `upAt (n+1)`. -/
@[simp] theorem liftRen_upAt (n : Nat) :
    Term.liftRen (upAt n) = upAt (n + 1) := by
  funext x
  cases x with
  | zero => simp [Term.liftRen, upAt]
  | succ x =>
    show upAt n x + 1 = upAt (n + 1) (x + 1)
    unfold upAt
    by_cases h : x < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- Shifting commutes with a lifted renaming:
`(↑t).rename (⇑ρ) = ↑(t.rename ρ)`. -/
theorem Term.shift_rename_lift (ρ : Nat → Nat) (t : Term) :
    (t.shift 1).rename (Term.liftRen ρ) = (t.rename ρ).shift 1 := by
  show (t.rename _).rename _ = (t.rename _).rename _
  rw [Term.rename_rename, Term.rename_rename]
  congr 1

/-! ## Insertion into a context -/

/-- Insert entry `a` at position `|Ξ|` of the context `Ξ ++ Γ₀` (counting
from the inside): the entries of `Ξ` lie *inside* the new binding and must
be renamed to skip it (each entry of `Ξ` is scoped in its own tail, so the
insertion point sits at decreasing levels). -/
def Ctx.insertAt (a : Term) : Ctx → Ctx → Ctx
  | [], Γ₀ => a :: Γ₀
  | t :: Ξ, Γ₀ => t.rename (upAt Ξ.length) :: Ctx.insertAt a Ξ Γ₀

@[simp] theorem Ctx.insertAt_length (a : Term) (Ξ Γ₀ : Ctx) :
    (Ctx.insertAt a Ξ Γ₀).length = (Ξ ++ Γ₀).length + 1 := by
  induction Ξ with
  | nil => rfl
  | cons t Ξ ih => simp [Ctx.insertAt, ih]

/-- `upAt n` is bounded: it sends `dom(Ξ ++ Γ₀)` into `dom(insertAt a Ξ Γ₀)`. -/
theorem upAt_lt {n x len : Nat} (h : x < len) : upAt n x < len + 1 := by
  unfold upAt; split <;> omega

/-- Bounds transport along insertion: `x ≤ t ∈ Ξ ++ Γ₀` implies
`upAt |Ξ| x ≤ t.rename (upAt |Ξ|) ∈ insertAt a Ξ Γ₀`. -/
theorem Ctx.Bound.insertAt {Ξ Γ₀ : Ctx} {x : Nat} {t a : Term}
    (h : Ctx.Bound (Ξ ++ Γ₀) x t) :
    Ctx.Bound (Ctx.insertAt a Ξ Γ₀) (upAt Ξ.length x) (t.rename (upAt Ξ.length)) := by
  induction Ξ generalizing x t with
  | nil =>
    show Ctx.Bound (a :: Γ₀) (upAt 0 x) (t.rename (upAt 0))
    rw [upAt_zero]
    exact .there h
  | cons s Ξ ih =>
    cases h with
    | here =>
      simp only [List.length_cons]
      have h0 : upAt (Ξ.length + 1) 0 = 0 := by
        unfold upAt; rw [if_pos (Nat.zero_lt_succ _)]
      rw [h0, ← liftRen_upAt, Term.shift_rename_lift]
      exact .here
    | there h' =>
      rename_i t' x'
      simp only [List.length_cons]
      have hx : upAt (Ξ.length + 1) (x' + 1) = upAt Ξ.length x' + 1 := by
        unfold upAt
        by_cases hc : x' < Ξ.length
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
      rw [hx, ← liftRen_upAt, Term.shift_rename_lift]
      exact .there (ih h')

/-! ## The weakening theorem -/

/-- **Weakening** (insertion form): all four declarative judgments transport
along insertion of a well-formed entry `a` at position `|Ξ|`. The corollaries
below specialize to the usual shift-by-one weakening (`Ξ = []`). -/
theorem weakening_insertAt :
    (∀ Γ', CtxWf Γ' → ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      CtxWf (Ctx.insertAt a Ξ Γ₀))
    ∧ (∀ Γ' u, Wf Γ' u → ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      Wf (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)))
    ∧ (∀ Γ' u r v, WellSub Γ' u r v → ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      WellSub (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)) r
        (v.rename (upAt Ξ.length)))
    ∧ (∀ Γ' u r v, Sub Γ' u r v → ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      Sub (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)) r
        (v.rename (upAt Ξ.length))) :=
  decl_induction
    (motC := fun Γ' => ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      CtxWf (Ctx.insertAt a Ξ Γ₀))
    (motW := fun Γ' u => ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      Wf (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)))
    (motWS := fun Γ' u r v => ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      WellSub (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)) r
        (v.rename (upAt Ξ.length)))
    (motS := fun Γ' u r v => ∀ Ξ Γ₀ a, Γ' = Ξ ++ Γ₀ → Wf Γ₀ a →
      Sub (Ctx.insertAt a Ξ Γ₀) (u.rename (upAt Ξ.length)) r
        (v.rename (upAt Ξ.length)))
    (ctx_nil := fun Ξ Γ₀ a hEq ha => by
      cases Ξ with
      | nil => cases hEq; exact .cons .nil ha
      | cons s Ξ => cases hEq)
    (ctx_cons := fun hC hW ihC ihW Ξ Γ₀ a hEq ha => by
      cases Ξ with
      | nil => cases hEq; exact .cons (.cons hC hW) ha
      | cons s Ξ =>
        cases hEq
        exact .cons (ihC Ξ Γ₀ a rfl ha) (ihW Ξ Γ₀ a rfl ha))
    (wf_var := fun hC hx ihC Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .var (ihC Ξ Γ₀ a rfl ha)
        (by rw [Ctx.insertAt_length]; exact upAt_lt hx))
    (wf_top := fun hC ihC Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .top (ihC Ξ Γ₀ a rfl ha))
    (wf_fn := fun {Γ t u} _ ihW Ξ Γ₀ a hEq ha => by
      subst hEq
      refine Wf.fn ?_
      rw [liftRen_upAt]
      exact ihW (t :: Ξ) Γ₀ a rfl ha)
    (wf_app := fun _ _ ihWS1 ihWS2 Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .app (ihWS1 Ξ Γ₀ a rfl ha) (ihWS2 Ξ Γ₀ a rfl ha))
    (wsub_sub := fun _ _ _ ihW1 ihW2 ihS Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .sub (ihW1 Ξ Γ₀ a rfl ha) (ihW2 Ξ Γ₀ a rfl ha)
        (ihS Ξ Γ₀ a rfl ha))
    (sub_trans := fun _ _ _ ih1 ih2 ihW Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .trans (ih1 Ξ Γ₀ a rfl ha) (ih2 Ξ Γ₀ a rfl ha)
        (ihW Ξ Γ₀ a rfl ha))
    (sub_symm := fun _ ih Ξ Γ₀ a hEq ha => .symm (ih Ξ Γ₀ a hEq ha))
    (sub_eq := fun _ ih Ξ Γ₀ a hEq ha => .eq (ih Ξ Γ₀ a hEq ha))
    (sub_var := fun _ _ _ _ _ => .var)
    (sub_top := fun _ _ _ _ _ => .top)
    (sub_fn := fun {Γ t t' u u' r} _ _ ih1 ih2 Ξ Γ₀ a hEq ha => by
      subst hEq
      refine Sub.fn (ih1 Ξ Γ₀ a rfl ha) ?_
      rw [liftRen_upAt]
      exact ih2 (t :: Ξ) Γ₀ a rfl ha)
    (sub_app := fun _ _ ih1 ih2 Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .app (ih1 Ξ Γ₀ a rfl ha) (ih2 Ξ Γ₀ a rfl ha))
    (sub_eapp := fun {Γ t u s} Ξ Γ₀ a hEq ha => by
      subst hEq
      rw [Term.rename_subst1]
      exact .eapp)
    (sub_etop := fun _ _ _ _ _ => .etop)
    (sub_evar := fun hb Ξ Γ₀ a hEq ha => by
      subst hEq
      exact .evar hb.insertAt)

/-! ## Shift-by-one weakening (the `Ξ = []` corollaries) -/

theorem Term.shift_zero (t : Term) : t.shift 0 = t := by
  show t.rename _ = t
  have h : (fun x => x + 0) = id := by funext x; rfl
  rw [h, Term.rename_id]

theorem Term.shift_shift (t : Term) (n : Nat) :
    (t.shift n).shift 1 = t.shift (n + 1) := by
  show (t.rename _).rename _ = t.rename _
  rw [Term.rename_rename]
  congr 1

/-- Weakening for `Γ ⊢ t wf`: a well-formed entry may be pushed onto the
context. -/
theorem Wf.weaken {Γ : Ctx} {u a : Term} (h : Wf Γ u) (ha : Wf Γ a) :
    Wf (a :: Γ) (u.shift 1) := by
  simpa [Ctx.insertAt, Term.shift]
    using weakening_insertAt.2.1 Γ u h [] Γ a rfl ha

/-- Weakening for `Γ ⊢ t ⊲wf u`. -/
theorem WellSub.weaken {Γ : Ctx} {u v a : Term} {r : Rel}
    (h : WellSub Γ u r v) (ha : Wf Γ a) :
    WellSub (a :: Γ) (u.shift 1) r (v.shift 1) := by
  simpa [Ctx.insertAt, Term.shift]
    using weakening_insertAt.2.2.1 Γ u r v h [] Γ a rfl ha

/-- Weakening for `Γ ⊢ t ⊲ u`. -/
theorem Sub.weaken {Γ : Ctx} {u v a : Term} {r : Rel}
    (h : Sub Γ u r v) (ha : Wf Γ a) :
    Sub (a :: Γ) (u.shift 1) r (v.shift 1) := by
  simpa [Ctx.insertAt, Term.shift]
    using weakening_insertAt.2.2.2 Γ u r v h [] Γ a rfl ha

/-- Iterated weakening: a term well-formed in `Γ` is well-formed (suitably
shifted) in any *well-formed* extension `Ξ ++ Γ`. -/
theorem Wf.weaken_append {Γ : Ctx} {a : Term} :
    ∀ (Ξ : Ctx), CtxWf (Ξ ++ Γ) → Wf Γ a → Wf (Ξ ++ Γ) (a.shift Ξ.length)
  | [], _, ha => by simpa [Term.shift_zero] using ha
  | s :: Ξ, hC, ha => by
    have ih := Wf.weaken_append Ξ hC.tail ha
    simpa [Term.shift_shift] using ih.weaken hC.head_wf

/-- Iterated weakening for `Γ ⊢ t ⊲ u` into a *well-formed* extension.
This is exactly the provable fragment of the open `SubShiftWeakening`
(`Pss.Substitution`): for ill-formed extensions the transport of
DS-TRANS's well-formedness premise fails. -/
theorem Sub.weaken_append {Γ : Ctx} {u v : Term} {r : Rel} :
    ∀ (Ξ : Ctx), CtxWf (Ξ ++ Γ) → Sub Γ u r v →
      Sub (Ξ ++ Γ) (u.shift Ξ.length) r (v.shift Ξ.length)
  | [], _, h => by simpa [Term.shift_zero] using h
  | s :: Ξ, hC, h => by
    have ih := Sub.weaken_append Ξ hC.tail h
    simpa [Term.shift_shift] using ih.weaken hC.head_wf

end Pss
