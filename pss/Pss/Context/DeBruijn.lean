import Pss.Syntax.DeBruijn

/-! # `Pss.Context.DeBruijn` — de Bruijn logical contexts and stacks

This module is the context-side seed of the de Bruijn refactor. It is
standalone and does not import the locally-nameless context modules.

List head is still the innermost binding. A de Bruijn variable `bvar 0`
therefore refers to the head entry, `bvar 1` to the next entry, and so on.
-/

namespace Pss
namespace DeBruijn

/-! ## Logical contexts -/

/-- Which paper-level binding form a de Bruijn context entry represents. -/
inductive CtxEntryKind where
  | sub
  | equ
  deriving DecidableEq, Repr

/-- A de Bruijn context entry. There is no name field; the entry's position in
the list is the variable index. -/
structure CtxEntry where
  bound : Term
  kind : CtxEntryKind
  deriving DecidableEq, Repr

/-- A logical context. List head is innermost/newest. -/
abbrev Ctx := List CtxEntry

namespace Ctx

/-- Context length, i.e. the number of de Bruijn variables in scope. -/
def depth : Ctx → Nat := List.length

@[simp] theorem depth_nil : depth [] = 0 := rfl

@[simp] theorem depth_cons (e : CtxEntry) (Γ : Ctx) :
    depth (e :: Γ) = depth Γ + 1 := by
  simp [depth, Nat.add_comm]

/-- Raw lookup by de Bruijn index, ignoring the entry kind. -/
def lookup : Ctx → Nat → Option CtxEntry
  | [], _ => none
  | e :: _, 0 => some e
  | _ :: Γ, n + 1 => lookup Γ n

/-- Look up the bound of a `.sub` entry at index `i`. -/
def lookupSub : Ctx → Nat → Option Term
  | [], _ => none
  | e :: _, 0 =>
      match e.kind with
      | .sub => some e.bound
      | .equ => none
  | _ :: Γ, n + 1 => lookupSub Γ n

/-- Look up the bound of an `.equ` entry at index `i`. -/
def lookupEqu : Ctx → Nat → Option Term
  | [], _ => none
  | e :: _, 0 =>
      match e.kind with
      | .equ => some e.bound
      | .sub => none
  | _ :: Γ, n + 1 => lookupEqu Γ n

@[simp] theorem lookup_nil (i : Nat) : lookup [] i = none := rfl
@[simp] theorem lookupSub_nil (i : Nat) : lookupSub [] i = none := rfl
@[simp] theorem lookupEqu_nil (i : Nat) : lookupEqu [] i = none := rfl

@[simp] theorem lookup_zero (e : CtxEntry) (Γ : Ctx) :
    lookup (e :: Γ) 0 = some e := rfl

@[simp] theorem lookup_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookup (e :: Γ) (i + 1) = lookup Γ i := rfl

@[simp] theorem lookupSub_zero_sub (t : Term) (Γ : Ctx) :
    lookupSub ({ bound := t, kind := .sub } :: Γ) 0 = some t := rfl

@[simp] theorem lookupSub_zero_equ (t : Term) (Γ : Ctx) :
    lookupSub ({ bound := t, kind := .equ } :: Γ) 0 = none := rfl

@[simp] theorem lookupEqu_zero_equ (t : Term) (Γ : Ctx) :
    lookupEqu ({ bound := t, kind := .equ } :: Γ) 0 = some t := rfl

@[simp] theorem lookupEqu_zero_sub (t : Term) (Γ : Ctx) :
    lookupEqu ({ bound := t, kind := .sub } :: Γ) 0 = none := rfl

@[simp] theorem lookupSub_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookupSub (e :: Γ) (i + 1) = lookupSub Γ i := rfl

@[simp] theorem lookupEqu_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookupEqu (e :: Γ) (i + 1) = lookupEqu Γ i := rfl

/-- A subtype binding at index `i`. -/
def subBinds (Γ : Ctx) (i : Nat) (t : Term) : Prop :=
  Γ.lookupSub i = some t

/-- An equivalence binding at index `i`. -/
def equBinds (Γ : Ctx) (i : Nat) (t : Term) : Prop :=
  Γ.lookupEqu i = some t

@[simp] theorem subBinds_zero_self (Γ : Ctx) (t : Term) :
    subBinds ({ bound := t, kind := .sub } :: Γ) 0 t := rfl

@[simp] theorem equBinds_zero_self (Γ : Ctx) (t : Term) :
    equBinds ({ bound := t, kind := .equ } :: Γ) 0 t := rfl

/-- A successful raw lookup is necessarily within the context depth. -/
theorem lookup_some_lt {Γ : Ctx} {i : Nat} {e : CtxEntry} :
    Γ.lookup i = some e → i < Γ.depth := by
  induction Γ generalizing i with
  | nil =>
    simp [lookup]
  | cons head tail ih =>
    cases i with
    | zero =>
      intro _
      simp [depth]
    | succ i =>
      intro h
      have hi := ih h
      simpa [depth, Nat.add_comm] using Nat.succ_lt_succ hi

/-- A successful `.sub` lookup is necessarily within the context depth. -/
theorem lookupSub_some_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.lookupSub i = some t → i < Γ.depth := by
  induction Γ generalizing i with
  | nil =>
    simp [lookupSub]
  | cons head tail ih =>
    cases i with
    | zero =>
      intro _
      simp [depth]
    | succ i =>
      intro h
      have hi := ih h
      simpa [depth, Nat.add_comm] using Nat.succ_lt_succ hi

/-- A successful `.equ` lookup is necessarily within the context depth. -/
theorem lookupEqu_some_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.lookupEqu i = some t → i < Γ.depth := by
  induction Γ generalizing i with
  | nil =>
    simp [lookupEqu]
  | cons head tail ih =>
    cases i with
    | zero =>
      intro _
      simp [depth]
    | succ i =>
      intro h
      have hi := ih h
      simpa [depth, Nat.add_comm] using Nat.succ_lt_succ hi

/-- A `.sub` binding index is necessarily within the context depth. -/
theorem subBinds_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.subBinds i t → i < Γ.depth :=
  lookupSub_some_lt

/-- An `.equ` binding index is necessarily within the context depth. -/
theorem equBinds_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.equBinds i t → i < Γ.depth :=
  lookupEqu_some_lt

end Ctx

/-! ## Stacks and extended contexts -/

/-- A continuation stack. List head is top of stack. -/
abbrev Stack := List Term

/-- Extended context `Γ ; s`. -/
abbrev ExtCtx := Ctx × Stack

namespace ExtCtx

def ctx (E : ExtCtx) : Ctx := E.fst

def stack (E : ExtCtx) : Stack := E.snd

@[simp] theorem ctx_mk (Γ : Ctx) (s : Stack) :
    ctx (Γ, s) = Γ := rfl

@[simp] theorem stack_mk (Γ : Ctx) (s : Stack) :
    stack (Γ, s) = s := rfl

/-- Push an operand onto the stack of an extended context. -/
def extend (E : ExtCtx) (α : Term) : ExtCtx := (E.ctx, α :: E.stack)

@[simp] theorem extend_mk (Γ : Ctx) (s : Stack) (α : Term) :
    extend (Γ, s) α = (Γ, α :: s) := rfl

end ExtCtx

/-! ## Prevalidity -/

/-- Pre-valid de Bruijn logical contexts.

When extending `Γ` with a new head entry, the entry's bound is scoped in the
tail `Γ`, not in the extended context. This matches the paper convention that
`Γ, x ≤ t` requires `t` to be well-scoped in `Γ`; the newly bound variable is
available only in bodies checked under the extended context. -/
inductive Prevalid : Ctx → Type
  | empty : Prevalid []
  | sub {Γ : Ctx} {t : Term} :
      Prevalid Γ →
      Term.Scoped Γ.depth t →
      Prevalid ({ bound := t, kind := .sub } :: Γ)
  | equ {Γ : Ctx} {α : Term} :
      Prevalid Γ →
      Term.Scoped Γ.depth α →
      Prevalid ({ bound := α, kind := .equ } :: Γ)

/-- Pre-validity for an extended de Bruijn context `Γ ; s`. -/
inductive PrevalidExt : Ctx → Stack → Type
  | nil {Γ : Ctx} : Prevalid Γ → PrevalidExt Γ []
  | cons {Γ : Ctx} {s : Stack} {α : Term} :
      PrevalidExt Γ s →
      Term.Scoped Γ.depth α →
      PrevalidExt Γ (α :: s)

namespace Prevalid

/-- The tail of a non-empty prevalid de Bruijn context is prevalid. -/
def tail {e : CtxEntry} {Γ : Ctx} :
    Prevalid (e :: Γ) → Prevalid Γ := by
  intro h
  cases h with
  | sub hΓ _ => exact hΓ
  | equ hΓ _ => exact hΓ

/-- Lookup of a `.sub` binding in a prevalid context returns a term scoped in
the whole context. -/
noncomputable def scoped_lookupSub {Γ : Ctx} {i : Nat} {t : Term}
    (hΓ : Prevalid Γ) (hb : Γ.subBinds i t) : Term.Scoped Γ.depth t := by
  induction hΓ generalizing i with
  | empty =>
    simp [Ctx.subBinds] at hb
  | @sub Γ' u hΓ' hu ih =>
    cases i with
    | zero =>
      simp [Ctx.subBinds] at hb
      subst hb
      exact Term.scoped_mono (by simp [Ctx.depth]) hu
    | succ i =>
      simp [Ctx.subBinds] at hb
      exact Term.scoped_mono (by simp [Ctx.depth]) (ih hb)
  | @equ Γ' α hΓ' hα ih =>
    cases i with
    | zero =>
      simp [Ctx.subBinds] at hb
    | succ i =>
      simp [Ctx.subBinds] at hb
      exact Term.scoped_mono (by simp [Ctx.depth]) (ih hb)

/-- Lookup of an `.equ` binding in a prevalid context returns a term scoped in
the whole context. -/
noncomputable def scoped_lookupEqu {Γ : Ctx} {i : Nat} {α : Term}
    (hΓ : Prevalid Γ) (hb : Γ.equBinds i α) : Term.Scoped Γ.depth α := by
  induction hΓ generalizing i with
  | empty =>
    simp [Ctx.equBinds] at hb
  | @sub Γ' u hΓ' hu ih =>
    cases i with
    | zero =>
      simp [Ctx.equBinds] at hb
    | succ i =>
      simp [Ctx.equBinds] at hb
      exact Term.scoped_mono (by simp [Ctx.depth]) (ih hb)
  | @equ Γ' β hΓ' hβ ih =>
    cases i with
    | zero =>
      simp [Ctx.equBinds] at hb
      subst hb
      exact Term.scoped_mono (by simp [Ctx.depth]) hβ
    | succ i =>
      simp [Ctx.equBinds] at hb
      exact Term.scoped_mono (by simp [Ctx.depth]) (ih hb)

end Prevalid

namespace PrevalidExt

/-- Extract the logical-context prevalidity witness from an extended-context
prevalidity witness. -/
noncomputable def ctx {Γ : Ctx} {s : Stack} :
    PrevalidExt Γ s → Prevalid Γ := by
  intro h
  induction h with
  | nil hΓ => exact hΓ
  | cons _ _ ih => exact ih

/-- The tail stack of a prevalid non-empty stack remains prevalid. -/
def tail {Γ : Ctx} {s : Stack} {α : Term} :
    PrevalidExt Γ (α :: s) → PrevalidExt Γ s := by
  intro h
  cases h with
  | cons hst _ => exact hst

/-- The top operand of a prevalid non-empty stack is scoped in the context. -/
def head_scoped {Γ : Ctx} {s : Stack} {α : Term} :
    PrevalidExt Γ (α :: s) → Term.Scoped Γ.depth α := by
  intro h
  cases h with
  | cons _ hα => exact hα

/-- Push a scoped operand onto a prevalid extended context. -/
def push {Γ : Ctx} {s : Stack} {α : Term} :
    PrevalidExt Γ s → Term.Scoped Γ.depth α → PrevalidExt Γ (α :: s) :=
  PrevalidExt.cons

/-- Extend the logical context at the head while preserving stack
prevalidity. Stack operands scoped in `Γ` remain scoped in `e :: Γ` by
monotonicity of de Bruijn scoping. -/
noncomputable def weaken_head {Γ : Ctx} {s : Stack} {e : CtxEntry} :
    PrevalidExt Γ s → Prevalid (e :: Γ) → PrevalidExt (e :: Γ) s := by
  intro h hpvHead
  induction h with
  | nil _ =>
    exact PrevalidExt.nil hpvHead
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (Term.scoped_mono (by simp [Ctx.depth]) hα)

end PrevalidExt

end DeBruijn
end Pss
