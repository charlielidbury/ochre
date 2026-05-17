import Pss.Syntax.LocallyNameless
import Mathlib.Data.List.Nodup

/-! # `Pss.Context.Logical` — logical contexts for PSS / MPSS

Unified context representation that covers both Hutchins 2010 PSS (only `≤`
bindings) and Pasquale & García-Pérez 2024 MPSS (both `≤` and `≡` bindings).

## Convention: list-head is innermost

The papers write contexts left-to-right with new bindings on the right:

```
Γ, x ≤ t
```

We encode this with **list head = newest (innermost) entry**: the textual
context `Γ, x ≤ t` becomes `⟨x, t, .sub⟩ :: Γ`. Lookups walk from head to tail,
which gives innermost-shadowing semantics for free.

This convention is load-bearing — every downstream module (notably
`Pss.Decl.Subtyping`, `Pss.Mpss.EqRed`) follows it.
-/

namespace Pss

/-! ## Entry kind and entry record -/

/-- Which paper-level binding form an entry represents. -/
inductive CtxEntryKind where
  | sub  -- subtype binding `x ≤ t`  (Hutchins + MPSS)
  | equ  -- equivalence binding `x ≡ α`  (MPSS only, MPSS Fig. 1, Pv-EqA)
deriving DecidableEq, Repr

/-- A single context entry. `bound` is `t` for `x ≤ t` or `α` for `x ≡ α`. -/
structure CtxEntry where
  name : String
  bound : Term
  kind : CtxEntryKind
deriving DecidableEq, Repr

/-- A logical context. **List head = innermost (newest) entry.** So the paper
context `Γ, x ≤ t` is encoded as `⟨x, t, .sub⟩ :: Γ`. -/
abbrev Ctx := List CtxEntry

/-! ## Domain -/

/-- The set of names bound in a context. -/
def Ctx.dom : Ctx → Finset String
  | []        => ∅
  | e :: rest => insert e.name (Ctx.dom rest)

@[simp] lemma Ctx.dom_nil : Ctx.dom [] = ∅ := rfl

@[simp] lemma Ctx.dom_cons (e : CtxEntry) (Γ : Ctx) :
    Ctx.dom (e :: Γ) = insert e.name (Ctx.dom Γ) := rfl

/-! ## Lookup with innermost shadowing

`lookupSub` and `lookupEqu` walk from list head (innermost) to tail (outermost),
returning the first entry whose `name` matches AND whose `kind` matches the
queried kind. A `.equ` entry shadows an outer `.sub` entry of the same name
(and vice versa); the tail is *not* searched for the other kind. This matches
the paper's "innermost wins" semantics. -/

/-- Look up the bound `t` for the innermost `.sub` binding `x ≤ t`. Returns
`none` if `x` is unbound, or the innermost binding for `x` is `.equ`. -/
def Ctx.lookupSub : Ctx → String → Option Term
  | [], _ => none
  | e :: rest, x =>
      if e.name = x then
        match e.kind with
        | .sub => some e.bound
        | .equ => none
      else Ctx.lookupSub rest x

/-- Look up `α` for the innermost `.equ` binding `x ≡ α`. -/
def Ctx.lookupEqu : Ctx → String → Option Term
  | [], _ => none
  | e :: rest, x =>
      if e.name = x then
        match e.kind with
        | .equ => some e.bound
        | .sub => none
      else Ctx.lookupEqu rest x

@[simp] lemma Ctx.lookupSub_nil (x : String) :
    Ctx.lookupSub [] x = none := rfl

@[simp] lemma Ctx.lookupEqu_nil (x : String) :
    Ctx.lookupEqu [] x = none := rfl

@[simp] lemma Ctx.lookupSub_cons (e : CtxEntry) (Γ : Ctx) (x : String) :
    Ctx.lookupSub (e :: Γ) x =
      (if e.name = x then
        match e.kind with
        | .sub => some e.bound
        | .equ => none
      else Ctx.lookupSub Γ x) := rfl

@[simp] lemma Ctx.lookupEqu_cons (e : CtxEntry) (Γ : Ctx) (x : String) :
    Ctx.lookupEqu (e :: Γ) x =
      (if e.name = x then
        match e.kind with
        | .equ => some e.bound
        | .sub => none
      else Ctx.lookupEqu Γ x) := rfl

/-! ## Propositional binding judgments -/

/-- `x ≤ t ∈ Γ` (innermost shadowing). -/
def Ctx.subBinds (Γ : Ctx) (x : String) (t : Term) : Prop :=
  Γ.lookupSub x = some t

/-- `x ≡ α ∈ Γ` (innermost shadowing). -/
def Ctx.equBinds (Γ : Ctx) (x : String) (α : Term) : Prop :=
  Γ.lookupEqu x = some α

/-- Self-binding: an innermost `.sub` entry binds itself. -/
lemma Ctx.subBinds_cons_self {Γ : Ctx} {x : String} {t : Term} :
    Ctx.subBinds (⟨x, t, .sub⟩ :: Γ) x t := by
  simp [Ctx.subBinds]

/-- Lookup-through: a different name at the head doesn't affect lookup. -/
lemma Ctx.subBinds_cons_other {Γ : Ctx} {e : CtxEntry} {x : String} {t : Term}
    (hne : e.name ≠ x) :
    Ctx.subBinds (e :: Γ) x t ↔ Ctx.subBinds Γ x t := by
  simp [Ctx.subBinds, hne]

/-- Self-binding for `.equ`. -/
lemma Ctx.equBinds_cons_self {Γ : Ctx} {x : String} {α : Term} :
    Ctx.equBinds (⟨x, α, .equ⟩ :: Γ) x α := by
  simp [Ctx.equBinds]

/-- Lookup-through for `.equ`. -/
lemma Ctx.equBinds_cons_other {Γ : Ctx} {e : CtxEntry} {x : String} {α : Term}
    (hne : e.name ≠ x) :
    Ctx.equBinds (e :: Γ) x α ↔ Ctx.equBinds Γ x α := by
  simp [Ctx.equBinds, hne]

/-! ## NoDup predicate -/

/-- Names of entries are pairwise distinct. -/
def Ctx.NoDup (Γ : Ctx) : Prop := (Γ.map CtxEntry.name).Nodup

@[simp] lemma Ctx.NoDup_nil : Ctx.NoDup [] := by
  simp [Ctx.NoDup]

lemma Ctx.NoDup_cons {e : CtxEntry} {Γ : Ctx} :
    Ctx.NoDup (e :: Γ) ↔ e.name ∉ (Γ.map CtxEntry.name) ∧ Ctx.NoDup Γ := by
  simp [Ctx.NoDup, List.nodup_cons]

/-- Helper: `name ∈ map name Γ ↔ name ∈ dom Γ`. -/
lemma Ctx.mem_map_name_iff_mem_dom (Γ : Ctx) (x : String) :
    x ∈ (Γ.map CtxEntry.name) ↔ x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.dom]
  | cons e rest ih =>
    simp [Ctx.dom, ih]

end Pss
