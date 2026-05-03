import Pss.Mpss.ContextRed
import Pss.Util.Tactic

/-! # `Pss.Mpss.Weakening` — context weakening for MPSS reductions

Pasquale & García-Pérez 2024 (CSL 2026), appendix Lemmas 19, 20, 21, 22.

## Overview

This file mechanizes the **weakening** lemmas for MPSS reductions:
informally, "if a reduction holds in `Γ; s`, it still holds in any
prevalid extension `Γ'; s` of `Γ; s`."

The paper writes "Γ, Γ'" for "extend Γ on the right with Γ'"; with our
list-head-is-innermost convention, this is `Γ' ++ Γ` (Γ' carries the new
innermost entries). The inductive proof needs the more general form of
inserting a block in the **middle** of `Γ` (this is what binder cases
naturally produce in the IH). We take as primitive
`CtxExtends Γ Γ' := ∃ Γ₁ Δ Γ₂, Γ = Γ₁ ++ Γ₂ ∧ Γ' = Γ₁ ++ Δ ++ Γ₂`. The
"append-on-top" form (paper's `Γ, Γ'`) is the special case `Γ₁ = []`.

## Status

* **Lemma 19 (Prevalid side):** PROVED. Foundational; used as a side
  condition by every other lemma here.
* **Lemma 20 (Wf-side, schema):** PROVED as a schema over an abstract
  unary relation `R : Ctx → Term → Prop`. The `Wf` / `WSub` / `WSubStar`
  judgments are not yet defined in this codebase (Wave 5 Agent 5A);
  the schema awaits instantiation there.
* **Lemma 21 (MSubRed):** PROVED. Operates on a "scoped" wrapper
  `MSubRedScoped` (see below); the unscoped form follows via the
  (now-proven) bridge `MSubRed.toScoped`.
* **Lemma 22 (MEqRed):** PROVED. Operates on the wrapper `MEqRedScoped`.
* **Bridges `MEqRed.toScoped` / `MSubRed.toScoped`:** PROVED (Wave 5
  follow-up). After the wrapper refactor the bridges are trivial
  structural mirrors; see comment block on `MEqRedScoped` /
  `MSubRedScoped` for design notes.

## On the scoped wrappers

The MPSS reduction rules in `Pss.Mpss.Reductions` deliberately do NOT
carry `fv t ⊆ Γ.dom` premises on binder annotations (Pasquale 2024
Figure 2 describes an untyped reduction; well-scopedness is layered on
via `Wf` in §4 of the paper).

The original wrapper design (Wave 4) added `fv t ⊆ Γ.dom` premises on
binder annotations to enable extending `Γ` with a fresh
`⟨y, t, .sub⟩` / `⟨y, α, .equ⟩` binding for the body IH inside the
weakening proofs. That made the unscoped → scoped bridge unprovable.

The Wave 5 follow-up REMOVES those premises and instead recovers
`fv t`, `fv α`, `LC α` *on demand* inside Lemma 22/21's `fun_` /
`fOp` arms, by instantiating the body sub-derivation at a single
fresh `x_0` and inverting the resulting `Prevalid (⟨x_0, _, _⟩ :: Γ)`.
The wrappers are now structurally identical to `MEqRed` / `MSubRed`,
which makes the unscoped → scoped bridges trivial. -/

namespace Pss

/-! ## Context extension -/

/-- A `CtxExtends Γ Γ'` witness: Γ' is Γ with a block Δ inserted at some
depth. With our list-head-is-innermost convention, Γ = Γ₁ ++ Γ₂ partitions
Γ into a "newer" prefix Γ₁ and an "older" suffix Γ₂; Γ' = Γ₁ ++ Δ ++ Γ₂
inserts Δ between them. -/
def CtxExtends (Γ Γ' : Ctx) : Prop :=
  ∃ Γ₁ Δ Γ₂, Γ = Γ₁ ++ Γ₂ ∧ Γ' = Γ₁ ++ Δ ++ Γ₂

/-- The "append-on-top" form (paper's `Γ, Γ'`). -/
theorem CtxExtends.ofAppend (Γ Δ : Ctx) : CtxExtends Γ (Δ ++ Γ) :=
  ⟨[], Δ, Γ, by simp, by simp⟩

theorem CtxExtends.refl (Γ : Ctx) : CtxExtends Γ Γ :=
  ⟨[], [], Γ, by simp, by simp⟩

/-! ## Domain of an appended context -/

@[simp] lemma Ctx.dom_append (Γ₁ Γ₂ : Ctx) :
    (Γ₁ ++ Γ₂).dom = Γ₁.dom ∪ Γ₂.dom := by
  induction Γ₁ with
  | nil => simp
  | cons e rest ih =>
    simp [Ctx.dom_cons, ih, Finset.insert_union]

/-! ## Lookup through append -/

theorem Ctx.lookupSub_append_left (Γ₁ Γ₂ : Ctx) (x : String) (t : Term)
    (h : Γ₁.lookupSub x = some t) : (Γ₁ ++ Γ₂).lookupSub x = some t := by
  induction Γ₁ with
  | nil => simp [Ctx.lookupSub] at h
  | cons e rest ih =>
    rw [List.cons_append]
    rw [Ctx.lookupSub_cons] at h ⊢
    by_cases hex : e.name = x
    · simp [hex] at h ⊢
      exact h
    · simp [hex] at h ⊢
      exact ih h

theorem Ctx.lookupSub_append_right (Γ₁ Γ₂ : Ctx) (x : String) (t : Term)
    (hx : x ∉ Γ₁.dom) (h : Γ₂.lookupSub x = some t) :
    (Γ₁ ++ Γ₂).lookupSub x = some t := by
  induction Γ₁ with
  | nil => simpa using h
  | cons e rest ih =>
    simp [Ctx.dom_cons] at hx
    obtain ⟨hex, hxRest⟩ := hx
    have hex' : e.name ≠ x := fun heq => hex heq.symm
    simp [List.cons_append, Ctx.lookupSub_cons, hex']
    exact ih hxRest

theorem Ctx.lookupEqu_append_left (Γ₁ Γ₂ : Ctx) (x : String) (α : Term)
    (h : Γ₁.lookupEqu x = some α) : (Γ₁ ++ Γ₂).lookupEqu x = some α := by
  induction Γ₁ with
  | nil => simp [Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [List.cons_append]
    rw [Ctx.lookupEqu_cons] at h ⊢
    by_cases hex : e.name = x
    · simp [hex] at h ⊢
      exact h
    · simp [hex] at h ⊢
      exact ih h

theorem Ctx.lookupEqu_append_right (Γ₁ Γ₂ : Ctx) (x : String) (α : Term)
    (hx : x ∉ Γ₁.dom) (h : Γ₂.lookupEqu x = some α) :
    (Γ₁ ++ Γ₂).lookupEqu x = some α := by
  induction Γ₁ with
  | nil => simpa using h
  | cons e rest ih =>
    simp [Ctx.dom_cons] at hx
    obtain ⟨hex, hxRest⟩ := hx
    have hex' : e.name ≠ x := fun heq => hex heq.symm
    simp [List.cons_append, Ctx.lookupEqu_cons, hex']
    exact ih hxRest

/-! ## Lifting `subBinds` / `equBinds` through middle insertion -/

/-- Helper: if `Γ.lookupSub x = some _`, then `x ∈ Γ.dom`. -/
private lemma Ctx.lookupSub_some_mem_dom {Γ : Ctx} {x : String} {t : Term}
    (h : Γ.lookupSub x = some t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.lookupSub] at h
  | cons e rest ih =>
    rw [Ctx.lookupSub_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

private lemma Ctx.lookupEqu_some_mem_dom {Γ : Ctx} {x : String} {α : Term}
    (h : Γ.lookupEqu x = some α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- Helper: if `Prevalid (Δ ++ Γ₂)` and `x ∈ Γ₂.dom`, then `x ∉ Δ.dom`. -/
lemma Ctx.notin_delta_of_in_tail
    {Δ Γ₂ : Ctx} {x : String}
    (hpv : Prevalid (Δ ++ Γ₂)) (hxΓ₂ : x ∈ Γ₂.dom) :
    x ∉ Δ.dom := by
  induction Δ with
  | nil => simp
  | cons e rest ih =>
    have hpv' : Prevalid (e :: (rest ++ Γ₂)) := by simpa using hpv
    have hpv_rest : Prevalid (rest ++ Γ₂) := hpv'.tail
    have hname : e.name ∉ Ctx.dom (rest ++ Γ₂) := by
      cases hpv' with
      | sub _ hx _ _ => exact hx
      | equ _ hx _ _ => exact hx
    show x ∉ Ctx.dom (e :: rest)
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hin
    · -- heq : x = e.name. So e.name = x ∈ Γ₂.dom, but hname says e.name ∉ (rest ++ Γ₂).dom.
      apply hname
      rw [Ctx.dom_append]
      apply Finset.mem_union.mpr; right
      rw [← heq]; exact hxΓ₂
    · exact ih hpv_rest hin

theorem Ctx.subBinds_insert_middle {Γ₁ Δ Γ₂ : Ctx} {x : String} {t : Term}
    (hpv : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (h : (Γ₁ ++ Γ₂).subBinds x t) :
    (Γ₁ ++ Δ ++ Γ₂).subBinds x t := by
  classical
  induction Γ₁ with
  | nil =>
    rw [List.nil_append] at h
    rw [List.nil_append] at hpv
    have hxΓ₂ : x ∈ Γ₂.dom := Ctx.lookupSub_some_mem_dom h
    have hxΔ : x ∉ Δ.dom := Ctx.notin_delta_of_in_tail hpv hxΓ₂
    show ((Δ ++ Γ₂) : Ctx).lookupSub x = some t
    exact Ctx.lookupSub_append_right Δ Γ₂ x t hxΔ h
  | cons e rest ih =>
    have h1 : Ctx.lookupSub (e :: (rest ++ Γ₂)) x = some t := h
    have hp_norm : Prevalid (e :: (rest ++ Δ ++ Γ₂)) := hpv
    have hpv_rest : Prevalid (rest ++ Δ ++ Γ₂) := hp_norm.tail
    rw [Ctx.lookupSub_cons] at h1
    show Ctx.lookupSub (e :: (rest ++ Δ ++ Γ₂)) x = some t
    rw [Ctx.lookupSub_cons]
    by_cases hex : e.name = x
    · rw [if_pos hex] at h1 ⊢
      exact h1
    · rw [if_neg hex] at h1 ⊢
      exact ih hpv_rest h1

theorem Ctx.equBinds_insert_middle {Γ₁ Δ Γ₂ : Ctx} {x : String} {α : Term}
    (hpv : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (h : (Γ₁ ++ Γ₂).equBinds x α) :
    (Γ₁ ++ Δ ++ Γ₂).equBinds x α := by
  classical
  induction Γ₁ with
  | nil =>
    rw [List.nil_append] at h
    rw [List.nil_append] at hpv
    have hxΓ₂ : x ∈ Γ₂.dom := Ctx.lookupEqu_some_mem_dom h
    have hxΔ : x ∉ Δ.dom := Ctx.notin_delta_of_in_tail hpv hxΓ₂
    show ((Δ ++ Γ₂) : Ctx).lookupEqu x = some α
    exact Ctx.lookupEqu_append_right Δ Γ₂ x α hxΔ h
  | cons e rest ih =>
    have h1 : Ctx.lookupEqu (e :: (rest ++ Γ₂)) x = some α := h
    have hpv1 : Prevalid (e :: (rest ++ Δ ++ Γ₂)) := hpv
    have hpv_rest : Prevalid (rest ++ Δ ++ Γ₂) := hpv1.tail
    rw [Ctx.lookupEqu_cons] at h1
    show Ctx.lookupEqu (e :: (rest ++ Δ ++ Γ₂)) x = some α
    rw [Ctx.lookupEqu_cons]
    by_cases hex : e.name = x
    · rw [if_pos hex] at h1 ⊢
      exact h1
    · rw [if_neg hex] at h1 ⊢
      exact ih hpv_rest h1

/-! ## Lemma 19 (Weakening for Prevalid / PrevalidExt)

The paper's Lemma 19 is a multi-conclusion statement. The "Wf-side" is
dispatched to Lemma 20; the MSubRed/MEqRed sides are Lemmas 21/22 below.

The foundational piece (always available, used as a side condition by
the other cases): extending a prevalid extended context with a fresh
block in the middle preserves prevalidity. -/

noncomputable def Lemma_19_WeakeningPrevalid {Γ₁ Δ Γ₂ : Ctx} {s : Stack}
    (hpv' : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (hpvExt : PrevalidExt (Γ₁ ++ Γ₂) s) :
    PrevalidExt (Γ₁ ++ Δ ++ Γ₂) s := by
  induction hpvExt with
  | nil _ => exact PrevalidExt.nil hpv'
  | cons _ hLC hfv ih =>
    refine PrevalidExt.cons ih hLC ?_
    intro y hy
    have hyMem := hfv hy
    simp only [Ctx.dom_append, Finset.mem_union] at hyMem ⊢
    tauto

/-- "Append-on-top" form (paper's `Γ, Γ'`). -/
noncomputable def Lemma_19_WeakeningPrevalid_append {Γ Δ : Ctx} {s : Stack}
    (hpv' : Prevalid (Δ ++ Γ))
    (hpvExt : PrevalidExt Γ s) :
    PrevalidExt (Δ ++ Γ) s := by
  have := Lemma_19_WeakeningPrevalid (Γ₁ := []) (Δ := Δ) (Γ₂ := Γ) (s := s)
    (by simpa using hpv')
    (by simpa using hpvExt)
  simpa using this

/-! ## Lemma 20 (Weakening — Wf-side, schema)

The paper's Lemma 20 is the WF-side of weakening:
`Γ ⊢ u wf` lifts to `Γ, Γ' ⊢ u wf` (and similarly for `≤wf`, `≤*wf`).

The WF judgments for MPSS are not yet defined in this codebase (Wave 5
Agent 5A), so we mechanize Lemma 20 as a **schema over an abstract unary
relation** `R : Ctx → Term → Prop`. Wave 5 instantiates the schema by
proving `Wf`, `WSub`, `WSubStar` are each `AppendMonotone`. -/

/-- A unary relation `R : Ctx → Term → Prop` is **append-monotone** if a
prevalid block insertion preserves it. -/
def AppendMonotone (R : Ctx → Term → Prop) : Prop :=
  ∀ {Γ₁ Δ Γ₂ : Ctx} {u : Term},
    Prevalid (Γ₁ ++ Δ ++ Γ₂) → R (Γ₁ ++ Γ₂) u → R (Γ₁ ++ Δ ++ Γ₂) u

/-- **Lemma 20** (schema). For any append-monotone unary relation `R`,
the weakening property holds. The content of the paper's Lemma 20 is
that `Wf`, `≤wf`, `≤∗wf` are append-monotone — to be discharged in
Wave 5 against this schema. -/
theorem Lemma_20_WeakeningWf_schema {R : Ctx → Term → Prop}
    (hMon : AppendMonotone R)
    {Γ₁ Δ Γ₂ : Ctx} {u : Term}
    (hpv : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (hR : R (Γ₁ ++ Γ₂) u) : R (Γ₁ ++ Δ ++ Γ₂) u :=
  hMon hpv hR

/-! ## Scoped wrappers `MEqRedScoped` / `MSubRedScoped`

These mirror the rules of `MEqRed` / `MSubRed` from `Pss.Mpss.Reductions`
but add `fv ⊆ Γ.dom` (and `LC`) premises on **binder annotations** and on
**stack heads consumed by `fOp`**. These extra premises are what make
the weakening proof go through (we need them to construct
`Prevalid (⟨y, _, _⟩ :: ...)` for the IH).

The original rules don't carry these (they describe an untyped reduction);
the bridge `MEqRed.toScoped` provably reconstructs them under
`Prevalid Γ` + `fv u ⊆ Γ.dom`. We axiomatize the bridge here and discharge
it in Wave 5 against the actual `Wf` judgment.
-/

inductive MEqRedScoped : Ctx → Stack → Term → Term → Type where
  | pro {Γ : Ctx} {s : Stack} {x : String} {α α' : Term} :
      PrevalidExt Γ s → Γ.equBinds x α →
      MEqRedScoped Γ s α α' →
      MEqRedScoped Γ s (.fvar x) α'
  | bet {Γ : Ctx} {s : Stack} {t v v' body body' : Term}
        (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L → MEqRedScoped Γ s (body^[x]) (body'^[x])) →
      MEqRedScoped Γ [] v v' →
      MEqRedScoped Γ s (.app (.abs t body) v) (Term.opening v' body')
  | top {Γ : Ctx} {s : Stack} :
      PrevalidExt Γ s →
      MEqRedScoped Γ s .top .top
  | app {Γ : Ctx} {s : Stack} {u u' v v' : Term} :
      MEqRedScoped Γ (v :: s) u u' →
      MEqRedScoped Γ [] v v' →
      MEqRedScoped Γ s (.app u v) (.app u' v')
  | var {Γ : Ctx} {s : Stack} {x : String} :
      PrevalidExt Γ s →
      MEqRedScoped Γ s (.fvar x) (.fvar x)
  | fun_ {Γ : Ctx} {t t' body body' : Term} (L : Finset String) :
      MEqRedScoped Γ [] t t' →
      (∀ x, x ∉ L →
        MEqRedScoped (⟨x, t, .sub⟩ :: Γ) [] (body^[x]) (body'^[x])) →
      MEqRedScoped Γ [] (.abs t body) (.abs t' body')
  | tAp {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s → Term.LC u → Term.fv u ⊆ Γ.dom →
      MEqRedScoped Γ s (.app .top u) .top
  | fOp {Γ : Ctx} {s : Stack} {t t' α body body' : Term}
        (L : Finset String) :
      MEqRedScoped Γ [] t t' →
      (∀ x, x ∉ L →
        MEqRedScoped (⟨x, α, .equ⟩ :: Γ) s (body^[x]) (body'^[x])) →
      MEqRedScoped Γ (α :: s) (.abs t body) (.abs t' body')

inductive MSubRedScoped : Ctx → Stack → Term → Term → Type where
  | pro {Γ : Ctx} {s : Stack} {x : String} {t : Term} :
      PrevalidExt Γ s → Γ.subBinds x t →
      MSubRedScoped Γ s (.fvar x) t
  | top {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s → Term.LC u → Term.fv u ⊆ Γ.dom →
      MSubRedScoped Γ s u .top
  | equ {Γ : Ctx} {s : Stack} {u v : Term} :
      PrevalidExt Γ s →
      MEqRedScoped Γ s u v →
      MSubRedScoped Γ s u v
  | app {Γ : Ctx} {s : Stack} {u u' v : Term} :
      MSubRedScoped Γ (v :: s) u u' →
      Term.LC v → Term.fv v ⊆ Γ.dom →
      MSubRedScoped Γ s (.app u v) (.app u' v)
  | fun_ {Γ : Ctx} {t body body' : Term} (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L →
        MSubRedScoped (⟨x, t, .sub⟩ :: Γ) [] (body^[x]) (body'^[x])) →
      MSubRedScoped Γ [] (.abs t body) (.abs t body')
  | fOp {Γ : Ctx} {s : Stack} {t α body body' : Term}
        (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L →
        MSubRedScoped (⟨x, α, .equ⟩ :: Γ) s (body^[x]) (body'^[x])) →
      MSubRedScoped Γ (α :: s) (.abs t body) (.abs t body')

/-! ## Bridge: scoped → unscoped (the trivial direction) -/

noncomputable def MEqRedScoped.toMEqRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedScoped Γ s u v) : MEqRed Γ s u v := by
  induction h with
  | pro hpv heq _ ih => exact MEqRed.pro hpv heq ih
  | @bet Γ s t v v' body body' L hLCt _ _ ihbody ihv =>
    exact MEqRed.bet (L := L) hLCt ihbody trivial ihv
  | top hpv => exact MEqRed.top hpv
  | app _ _ ihu ihv => exact MEqRed.app ihu ihv
  | var hpv => exact MEqRed.var hpv
  | @fun_ Γ t t' body body' L _ _ iht ihbody =>
    exact MEqRed.fun_ (L := L) iht ihbody trivial
  | tAp hpv hLC hfv => exact MEqRed.tAp hpv hLC hfv
  | @fOp Γ s t t' α body body' L _ _ iht ihbody =>
    exact MEqRed.fOp (L := L) iht ihbody trivial

noncomputable def MSubRedScoped.toMSubRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedScoped Γ s u v) : MSubRed Γ s u v := by
  induction h with
  | pro hpv hb => exact MSubRed.pro hpv hb
  | top hpv hLC hfv => exact MSubRed.top hpv hLC hfv
  | @equ Γ s u v hpv heq => exact MSubRed.equ hpv heq.toMEqRed
  | app _ hLCv hfvv ihu => exact MSubRed.app ihu hLCv hfvv
  | @fun_ Γ t body body' L hLCt _ ihbody =>
    exact MSubRed.fun_ (L := L) hLCt ihbody trivial
  | @fOp Γ s t α body body' L hLCt _ ihbody =>
    exact MSubRed.fOp (L := L) hLCt ihbody trivial

/-! ## Helper: extract `Prevalid Γ` from any `MEqRed Γ s u v`

This mirrors the private `MEqRed.prevalid` from `Pss.Mpss.Substitution`.
We re-prove it here to keep `Pss.Mpss.Weakening`'s import surface
minimal. Used inside Lemma 22's `fun_` / `fOp` arms (and the analogous
Lemma 21 arms) to recover `fv t ⊆ Γ.dom` etc. from the body sub-
derivation after the wrapper refactor.
-/

private noncomputable def _extractPrevalidOfMEqRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ _ iht _ => exact iht

private noncomputable def _extractPrevalidOfMSubRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x t hpv _ => exact extractPrevalid hpv
  | @top Γ st u hpv _ _ => exact extractPrevalid hpv
  | @equ Γ st u v hpv heq => exact extractPrevalid hpv
  | @app Γ st u u' v _ _ _ ihu => exact ihu
  | @fun_ Γ t body body' L _ _ _ ihbody =>
    classical
    let x : String := Classical.choose (Term.exists_fresh L)
    have hx : x ∉ L := Classical.choose_spec (Term.exists_fresh L)
    exact (ihbody x hx).tail
  | @fOp Γ st t α body body' L _ _ _ ihbody =>
    classical
    let x : String := Classical.choose (Term.exists_fresh L)
    have hx : x ∉ L := Classical.choose_spec (Term.exists_fresh L)
    exact (ihbody x hx).tail

/-! ## Bridge: unscoped → scoped

After the Wave 5 follow-up refactor (see the comment block on the scoped
wrapper definitions above), `MEqRedScoped` / `MSubRedScoped` are
structurally identical to `MEqRed` / `MSubRed`. The bridge is therefore
a trivial structural reflection. The `Prevalid Γ` and `fv u ⊆ Γ.dom`
arguments are retained for backwards compatibility with downstream
callers in `Renaming.lean`, but are not consumed.
-/

/-- Internal premise-free bridge. After the wrapper refactor the scoped
wrapper is structurally identical to `MEqRed`, so this is a pure
constructor reflection. -/
noncomputable def _MEqRed.toScopedAux : ∀ {Γ : Ctx} {s : Stack} {u v : Term},
    MEqRed Γ s u v → MEqRedScoped Γ s u v := by
  intro Γ s u v h
  induction h with
  | pro hpv heq _ ih => exact MEqRedScoped.pro hpv heq ih
  | @bet Γ s t v v' body body' L hLCt _ _ _ ihbody ihv =>
    exact MEqRedScoped.bet (L := L) hLCt ihbody ihv
  | top hpv => exact MEqRedScoped.top hpv
  | app _ _ ihu ihv => exact MEqRedScoped.app ihu ihv
  | var hpv => exact MEqRedScoped.var hpv
  | @fun_ Γ t t' body body' L _ _ _ iht ihbody =>
    exact MEqRedScoped.fun_ (L := L) iht ihbody
  | tAp hpv hLC hfv => exact MEqRedScoped.tAp hpv hLC hfv
  | @fOp Γ s t t' α body body' L _ _ _ iht ihbody =>
    exact MEqRedScoped.fOp (L := L) iht ihbody

noncomputable def _MSubRed.toScopedAux : ∀ {Γ : Ctx} {s : Stack} {u v : Term},
    MSubRed Γ s u v → MSubRedScoped Γ s u v := by
  intro Γ s u v h
  induction h with
  | pro hpv hb => exact MSubRedScoped.pro hpv hb
  | top hpv hLC hfv => exact MSubRedScoped.top hpv hLC hfv
  | @equ Γ s u v hpv heq =>
    exact MSubRedScoped.equ hpv (_MEqRed.toScopedAux heq)
  | app _ hLCv hfvv ihu => exact MSubRedScoped.app ihu hLCv hfvv
  | @fun_ Γ t body body' L hLCt _ _ ihbody =>
    exact MSubRedScoped.fun_ (L := L) hLCt ihbody
  | @fOp Γ s t α body body' L hLCt _ _ ihbody =>
    exact MSubRedScoped.fOp (L := L) hLCt ihbody

/-- Bridge unscoped → scoped MEqRed. After the wrapper refactor the
scoped wrapper is structurally identical to `MEqRed`, so the bridge is
a trivial structural mirror. The `Prevalid` / `fv` premises are
retained for backwards compatibility with downstream callers in
`Renaming.lean`, but are not consumed. -/
noncomputable def MEqRed.toScoped {Γ : Ctx} {s : Stack} {u v : Term}
    (_hpv : Prevalid Γ) (_hfv : Term.fv u ⊆ Γ.dom) (h : MEqRed Γ s u v) :
    MEqRedScoped Γ s u v :=
  _MEqRed.toScopedAux h

/-- Bridge unscoped → scoped MSubRed. -/
noncomputable def MSubRed.toScoped {Γ : Ctx} {s : Stack} {u v : Term}
    (_hpv : Prevalid Γ) (_hfv : Term.fv u ⊆ Γ.dom) (h : MSubRed Γ s u v) :
    MSubRedScoped Γ s u v :=
  _MSubRed.toScopedAux h

/-! ## Lemma 22 (Weakening for MEqRed)

We prove this BEFORE Lemma 21, because Lemma 21's `Ms-Equ` arm calls
Lemma 22 as a sub-lemma (only `MSubRed` references `MEqRed`). -/

/-- Internal partitioned form: weakening for scoped MEqRed under a
middle insertion. -/
noncomputable def Lemma_22_WeakeningMEqRedScoped_partitioned :
    ∀ {Γ : Ctx} {s : Stack} {u v : Term},
      MEqRedScoped Γ s u v →
      ∀ (Γ₁ Δ Γ₂ : Ctx), Γ = Γ₁ ++ Γ₂ →
      Prevalid (Γ₁ ++ Δ ++ Γ₂) →
      MEqRedScoped (Γ₁ ++ Δ ++ Γ₂) s u v := by
  intro Γ s u v h
  induction h with
  | @pro Γ s x α α' hpv heq _ ih =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    have hpvE' : PrevalidExt (Γ₁ ++ Δ ++ Γ₂) s :=
      Lemma_19_WeakeningPrevalid hpv' hpv
    have heq' : (Γ₁ ++ Δ ++ Γ₂).equBinds x α :=
      Ctx.equBinds_insert_middle hpv' heq
    exact MEqRedScoped.pro hpvE' heq' (ih Γ₁ Δ Γ₂ rfl hpv')
  | @bet Γ s t v v' body body' L hLCt _ _ ihbody ihv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MEqRedScoped.bet (L := L) hLCt ?_ (ihv Γ₁ Δ Γ₂ rfl hpv')
    intro y hy
    exact ihbody y hy Γ₁ Δ Γ₂ rfl hpv'
  | @top Γ s hpv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    exact MEqRedScoped.top (Lemma_19_WeakeningPrevalid hpv' hpv)
  | @app Γ s u u' v v' _ _ ihu ihv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    exact MEqRedScoped.app (ihu Γ₁ Δ Γ₂ rfl hpv') (ihv Γ₁ Δ Γ₂ rfl hpv')
  | @var Γ s x hpv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    exact MEqRedScoped.var (Lemma_19_WeakeningPrevalid hpv' hpv)
  | @fun_ Γ t t' body body' L ht hbody iht ihbody =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    classical
    -- Recover `fv t ⊆ Γ.dom` and `LC t` from a single body sub-derivation
    -- at a fresh `x_0`. We pick `x_0 ∉ L ∪ (Γ₁ ++ Γ₂).dom` so the body
    -- sub-derivation lives at `⟨x_0, t, .sub⟩ :: (Γ₁ ++ Γ₂)`, whose
    -- prevalidity carries both pieces in its `Prevalid.sub` arm.
    -- We use `Classical.choose` (not `obtain`) since this is a `Type`-
    -- valued definition and `Exists` only eliminates into `Prop`.
    let x_0 : String :=
      Classical.choose (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0 : x_0 ∉ L ∪ (Γ₁ ++ Γ₂).dom :=
      Classical.choose_spec (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0_L : x_0 ∉ L := fun h => hx_0 (by
      apply Finset.mem_union.mpr; left; exact h)
    have hbody_x_0 : MEqRed (⟨x_0, t, .sub⟩ :: (Γ₁ ++ Γ₂)) []
        (body^[x_0]) (body'^[x_0]) := (hbody x_0 hx_0_L).toMEqRed
    have hpvBody : Prevalid (⟨x_0, t, .sub⟩ :: (Γ₁ ++ Γ₂)) :=
      _extractPrevalidOfMEqRed hbody_x_0
    have hLCt : Term.LC t := by
      cases hpvBody with
      | sub _ _ _ hLC => exact hLC
    have hFvT : Term.fv t ⊆ (Γ₁ ++ Γ₂).dom := by
      cases hpvBody with
      | sub _ _ hfv _ => exact hfv
    have hFvT' : Term.fv t ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := by
      intro z hz
      have := hFvT hz
      simp [Ctx.dom_append] at *
      tauto
    refine MEqRedScoped.fun_ (L := L ∪ (Γ₁ ++ Δ ++ Γ₂).dom)
      (iht Γ₁ Δ Γ₂ rfl hpv') ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (by
      apply Finset.mem_union.mpr; left; exact h)
    have hyΓ' : y ∉ (Γ₁ ++ Δ ++ Γ₂).dom := fun h => hy (by
      apply Finset.mem_union.mpr; right; exact h)
    have hpvY : Prevalid (⟨y, t, .sub⟩ :: (Γ₁ ++ Δ ++ Γ₂)) :=
      Prevalid.sub hpv' hyΓ' hFvT' hLCt
    have hres := ihbody y hyL (⟨y, t, .sub⟩ :: Γ₁) Δ Γ₂ rfl
      (by simpa [List.cons_append] using hpvY)
    have heq : (⟨y, t, .sub⟩ :: Γ₁) ++ Δ ++ Γ₂ =
        ⟨y, t, .sub⟩ :: (Γ₁ ++ Δ ++ Γ₂) := by
      simp [List.cons_append]
    rw [← heq]
    exact hres
  | @tAp Γ s u hpv hLC hfv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MEqRedScoped.tAp (Lemma_19_WeakeningPrevalid hpv' hpv) hLC ?_
    intro z hz
    have := hfv hz
    simp [Ctx.dom_append] at *
    tauto
  | @fOp Γ s t t' α body body' L ht hbody iht ihbody =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    classical
    -- Recover `fv α ⊆ Γ.dom` and `LC α` from a single body sub-derivation
    -- at a fresh `x_0`. (We do NOT need `fv t` after the wrapper refactor.)
    let x_0 : String :=
      Classical.choose (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0 : x_0 ∉ L ∪ (Γ₁ ++ Γ₂).dom :=
      Classical.choose_spec (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0_L : x_0 ∉ L := fun h => hx_0 (by
      apply Finset.mem_union.mpr; left; exact h)
    have hbody_x_0 : MEqRed (⟨x_0, α, .equ⟩ :: (Γ₁ ++ Γ₂)) s
        (body^[x_0]) (body'^[x_0]) := (hbody x_0 hx_0_L).toMEqRed
    have hpvBody : Prevalid (⟨x_0, α, .equ⟩ :: (Γ₁ ++ Γ₂)) :=
      _extractPrevalidOfMEqRed hbody_x_0
    have hLCα : Term.LC α := by
      cases hpvBody with
      | equ _ _ _ hLC => exact hLC
    have hFvα : Term.fv α ⊆ (Γ₁ ++ Γ₂).dom := by
      cases hpvBody with
      | equ _ _ hfv _ => exact hfv
    have hFvα' : Term.fv α ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := by
      intro z hz; have := hFvα hz
      simp [Ctx.dom_append] at *; tauto
    refine MEqRedScoped.fOp (L := L ∪ (Γ₁ ++ Δ ++ Γ₂).dom)
      (iht Γ₁ Δ Γ₂ rfl hpv') ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (by
      apply Finset.mem_union.mpr; left; exact h)
    have hyΓ' : y ∉ (Γ₁ ++ Δ ++ Γ₂).dom := fun h => hy (by
      apply Finset.mem_union.mpr; right; exact h)
    have hpvY : Prevalid (⟨y, α, .equ⟩ :: (Γ₁ ++ Δ ++ Γ₂)) :=
      Prevalid.equ hpv' hyΓ' hFvα' hLCα
    have hres := ihbody y hyL (⟨y, α, .equ⟩ :: Γ₁) Δ Γ₂ rfl
      (by simpa [List.cons_append] using hpvY)
    have heq : (⟨y, α, .equ⟩ :: Γ₁) ++ Δ ++ Γ₂ =
        ⟨y, α, .equ⟩ :: (Γ₁ ++ Δ ++ Γ₂) := by
      simp [List.cons_append]
    rw [← heq]
    exact hres

/-- **Lemma 22** (Weakening for `MEqRed`, partitioned form). The
paper's statement, translated to our partitioned `CtxExtends`. Operates
on the unscoped `MEqRed`; uses the `MEqRed.toScoped` bridge internally. -/
noncomputable def Lemma_22_WeakeningMEqRed {Γ₁ Δ Γ₂ : Ctx} {s : Stack} {u v : Term}
    (hΓPv : Prevalid (Γ₁ ++ Γ₂))
    (hFvU : Term.fv u ⊆ (Γ₁ ++ Γ₂).dom)
    (hpv' : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (h : MEqRed (Γ₁ ++ Γ₂) s u v) :
    MEqRed (Γ₁ ++ Δ ++ Γ₂) s u v :=
  (Lemma_22_WeakeningMEqRedScoped_partitioned
    (MEqRed.toScoped hΓPv hFvU h) Γ₁ Δ Γ₂ rfl hpv').toMEqRed

/-- "Append-on-top" form of Lemma 22 (paper's `Γ, Γ'`). -/
noncomputable def Lemma_22_WeakeningMEqRed_append {Γ Δ : Ctx} {s : Stack} {u v : Term}
    (hΓPv : Prevalid Γ)
    (hFvU : Term.fv u ⊆ Γ.dom)
    (hpv' : Prevalid (Δ ++ Γ))
    (h : MEqRed Γ s u v) :
    MEqRed (Δ ++ Γ) s u v := by
  have := Lemma_22_WeakeningMEqRed (Γ₁ := []) (Δ := Δ) (Γ₂ := Γ)
    (s := s) (u := u) (v := v)
    (by simpa using hΓPv)
    (by simpa using hFvU)
    (by simpa using hpv')
    (by simpa using h)
  simpa using this

/-! ## Lemma 21 (Weakening for MSubRed)

Same shape as Lemma 22, by induction on the `MSubRed` derivation. The
`Ms-Equ` arm calls into Lemma 22. -/

/-- Internal partitioned form: weakening for scoped MSubRed. -/
noncomputable def Lemma_21_WeakeningMSubRedScoped_partitioned :
    ∀ {Γ : Ctx} {s : Stack} {u v : Term},
      MSubRedScoped Γ s u v →
      ∀ (Γ₁ Δ Γ₂ : Ctx), Γ = Γ₁ ++ Γ₂ →
      Prevalid (Γ₁ ++ Δ ++ Γ₂) →
      MSubRedScoped (Γ₁ ++ Δ ++ Γ₂) s u v := by
  intro Γ s u v h
  induction h with
  | @pro Γ s x t hpv hb =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MSubRedScoped.pro (Lemma_19_WeakeningPrevalid hpv' hpv) ?_
    exact Ctx.subBinds_insert_middle hpv' hb
  | @top Γ s u hpv hLC hfv =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MSubRedScoped.top (Lemma_19_WeakeningPrevalid hpv' hpv) hLC ?_
    intro z hz; have := hfv hz
    simp [Ctx.dom_append] at *; tauto
  | @equ Γ s u v hpv heq =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MSubRedScoped.equ (Lemma_19_WeakeningPrevalid hpv' hpv) ?_
    exact Lemma_22_WeakeningMEqRedScoped_partitioned heq Γ₁ Δ Γ₂ rfl hpv'
  | @app Γ s u u' v hu hLCv hfvv ihu =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    refine MSubRedScoped.app (ihu Γ₁ Δ Γ₂ rfl hpv') hLCv ?_
    intro z hz; have := hfvv hz
    simp [Ctx.dom_append] at *; tauto
  | @fun_ Γ t body body' L hLCt hbody ihbody =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    classical
    -- Recover `fv t ⊆ Γ.dom` from a single body sub-derivation.
    let x_0 : String :=
      Classical.choose (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0 : x_0 ∉ L ∪ (Γ₁ ++ Γ₂).dom :=
      Classical.choose_spec (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0_L : x_0 ∉ L := fun h => hx_0 (by
      apply Finset.mem_union.mpr; left; exact h)
    have hbody_x_0 : MSubRed (⟨x_0, t, .sub⟩ :: (Γ₁ ++ Γ₂)) []
        (body^[x_0]) (body'^[x_0]) := (hbody x_0 hx_0_L).toMSubRed
    have hpvBody : Prevalid (⟨x_0, t, .sub⟩ :: (Γ₁ ++ Γ₂)) :=
      _extractPrevalidOfMSubRed hbody_x_0
    have hFvT : Term.fv t ⊆ (Γ₁ ++ Γ₂).dom := by
      cases hpvBody with
      | sub _ _ hfv _ => exact hfv
    have hFvT' : Term.fv t ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := by
      intro z hz; have := hFvT hz
      simp [Ctx.dom_append] at *; tauto
    refine MSubRedScoped.fun_ (L := L ∪ (Γ₁ ++ Δ ++ Γ₂).dom) hLCt ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (by
      apply Finset.mem_union.mpr; left; exact h)
    have hyΓ' : y ∉ (Γ₁ ++ Δ ++ Γ₂).dom := fun h => hy (by
      apply Finset.mem_union.mpr; right; exact h)
    have hpvY : Prevalid (⟨y, t, .sub⟩ :: (Γ₁ ++ Δ ++ Γ₂)) :=
      Prevalid.sub hpv' hyΓ' hFvT' hLCt
    have hres := ihbody y hyL (⟨y, t, .sub⟩ :: Γ₁) Δ Γ₂ rfl
      (by simpa [List.cons_append] using hpvY)
    have heq : (⟨y, t, .sub⟩ :: Γ₁) ++ Δ ++ Γ₂ =
        ⟨y, t, .sub⟩ :: (Γ₁ ++ Δ ++ Γ₂) := by
      simp [List.cons_append]
    rw [← heq]
    exact hres
  | @fOp Γ s t α body body' L hLCt hbody ihbody =>
    intro Γ₁ Δ Γ₂ hsplit hpv'
    subst hsplit
    classical
    -- Recover `fv α ⊆ Γ.dom` and `LC α` from a single body sub-derivation.
    let x_0 : String :=
      Classical.choose (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0 : x_0 ∉ L ∪ (Γ₁ ++ Γ₂).dom :=
      Classical.choose_spec (Term.exists_fresh (L ∪ (Γ₁ ++ Γ₂).dom))
    have hx_0_L : x_0 ∉ L := fun h => hx_0 (by
      apply Finset.mem_union.mpr; left; exact h)
    have hbody_x_0 : MSubRed (⟨x_0, α, .equ⟩ :: (Γ₁ ++ Γ₂)) s
        (body^[x_0]) (body'^[x_0]) := (hbody x_0 hx_0_L).toMSubRed
    have hpvBody : Prevalid (⟨x_0, α, .equ⟩ :: (Γ₁ ++ Γ₂)) :=
      _extractPrevalidOfMSubRed hbody_x_0
    have hLCα : Term.LC α := by
      cases hpvBody with
      | equ _ _ _ hLC => exact hLC
    have hFvα : Term.fv α ⊆ (Γ₁ ++ Γ₂).dom := by
      cases hpvBody with
      | equ _ _ hfv _ => exact hfv
    have hFvα' : Term.fv α ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := by
      intro z hz; have := hFvα hz
      simp [Ctx.dom_append] at *; tauto
    refine MSubRedScoped.fOp (L := L ∪ (Γ₁ ++ Δ ++ Γ₂).dom) hLCt ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (by
      apply Finset.mem_union.mpr; left; exact h)
    have hyΓ' : y ∉ (Γ₁ ++ Δ ++ Γ₂).dom := fun h => hy (by
      apply Finset.mem_union.mpr; right; exact h)
    have hpvY : Prevalid (⟨y, α, .equ⟩ :: (Γ₁ ++ Δ ++ Γ₂)) :=
      Prevalid.equ hpv' hyΓ' hFvα' hLCα
    have hres := ihbody y hyL (⟨y, α, .equ⟩ :: Γ₁) Δ Γ₂ rfl
      (by simpa [List.cons_append] using hpvY)
    have heq : (⟨y, α, .equ⟩ :: Γ₁) ++ Δ ++ Γ₂ =
        ⟨y, α, .equ⟩ :: (Γ₁ ++ Δ ++ Γ₂) := by
      simp [List.cons_append]
    rw [← heq]
    exact hres

/-- **Lemma 21** (Weakening for `MSubRed`, partitioned form). -/
noncomputable def Lemma_21_WeakeningMSubRed {Γ₁ Δ Γ₂ : Ctx} {s : Stack} {u v : Term}
    (hΓPv : Prevalid (Γ₁ ++ Γ₂))
    (hFvU : Term.fv u ⊆ (Γ₁ ++ Γ₂).dom)
    (hpv' : Prevalid (Γ₁ ++ Δ ++ Γ₂))
    (h : MSubRed (Γ₁ ++ Γ₂) s u v) :
    MSubRed (Γ₁ ++ Δ ++ Γ₂) s u v :=
  (Lemma_21_WeakeningMSubRedScoped_partitioned
    (MSubRed.toScoped hΓPv hFvU h) Γ₁ Δ Γ₂ rfl hpv').toMSubRed

/-- "Append-on-top" form of Lemma 21 (paper's `Γ, Γ'`). -/
noncomputable def Lemma_21_WeakeningMSubRed_append {Γ Δ : Ctx} {s : Stack} {u v : Term}
    (hΓPv : Prevalid Γ)
    (hFvU : Term.fv u ⊆ Γ.dom)
    (hpv' : Prevalid (Δ ++ Γ))
    (h : MSubRed Γ s u v) :
    MSubRed (Δ ++ Γ) s u v := by
  have := Lemma_21_WeakeningMSubRed (Γ₁ := []) (Δ := Δ) (Γ₂ := Γ)
    (s := s) (u := u) (v := v)
    (by simpa using hΓPv)
    (by simpa using hFvU)
    (by simpa using hpv')
    (by simpa using h)
  simpa using this

end Pss
