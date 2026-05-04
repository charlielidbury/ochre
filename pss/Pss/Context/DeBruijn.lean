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

end DeBruijn
end Pss
