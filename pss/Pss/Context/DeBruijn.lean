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

/-- Look up the bound of a `.sub` entry at index `i`, lifted into the current
context. The stored bound for an entry is scoped in that entry's tail; every
recursive step shifts it through one newer binding. -/
def lookupSub : Ctx → Nat → Option Term
  | [], _ => none
  | e :: _, 0 =>
      match e.kind with
      | .sub => some (Term.shift 0 e.bound)
      | .equ => none
  | _ :: Γ, n + 1 => (lookupSub Γ n).map (Term.shift 0)

/-- Look up the bound of an `.equ` entry at index `i`, lifted into the current
context. -/
def lookupEqu : Ctx → Nat → Option Term
  | [], _ => none
  | e :: _, 0 =>
      match e.kind with
      | .equ => some (Term.shift 0 e.bound)
      | .sub => none
  | _ :: Γ, n + 1 => (lookupEqu Γ n).map (Term.shift 0)

@[simp] theorem lookup_nil (i : Nat) : lookup [] i = none := rfl
@[simp] theorem lookupSub_nil (i : Nat) : lookupSub [] i = none := rfl
@[simp] theorem lookupEqu_nil (i : Nat) : lookupEqu [] i = none := rfl

@[simp] theorem lookup_zero (e : CtxEntry) (Γ : Ctx) :
    lookup (e :: Γ) 0 = some e := rfl

@[simp] theorem lookup_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookup (e :: Γ) (i + 1) = lookup Γ i := rfl

@[simp] theorem lookupSub_zero_sub (t : Term) (Γ : Ctx) :
    lookupSub ({ bound := t, kind := .sub } :: Γ) 0 = some (Term.shift 0 t) := rfl

@[simp] theorem lookupSub_zero_equ (t : Term) (Γ : Ctx) :
    lookupSub ({ bound := t, kind := .equ } :: Γ) 0 = none := rfl

@[simp] theorem lookupEqu_zero_equ (t : Term) (Γ : Ctx) :
    lookupEqu ({ bound := t, kind := .equ } :: Γ) 0 = some (Term.shift 0 t) := rfl

@[simp] theorem lookupEqu_zero_sub (t : Term) (Γ : Ctx) :
    lookupEqu ({ bound := t, kind := .sub } :: Γ) 0 = none := rfl

@[simp] theorem lookupSub_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookupSub (e :: Γ) (i + 1) = (lookupSub Γ i).map (Term.shift 0) := rfl

@[simp] theorem lookupEqu_succ (e : CtxEntry) (Γ : Ctx) (i : Nat) :
    lookupEqu (e :: Γ) (i + 1) = (lookupEqu Γ i).map (Term.shift 0) := rfl

/-- A subtype binding at index `i`. -/
def subBinds (Γ : Ctx) (i : Nat) (t : Term) : Prop :=
  Γ.lookupSub i = some t

/-- An equivalence binding at index `i`. -/
def equBinds (Γ : Ctx) (i : Nat) (t : Term) : Prop :=
  Γ.lookupEqu i = some t

@[simp] theorem subBinds_zero_self (Γ : Ctx) (t : Term) :
    subBinds ({ bound := t, kind := .sub } :: Γ) 0 (Term.shift 0 t) := rfl

@[simp] theorem equBinds_zero_self (Γ : Ctx) (t : Term) :
    equBinds ({ bound := t, kind := .equ } :: Γ) 0 (Term.shift 0 t) := rfl

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
  induction Γ generalizing i t with
  | nil =>
    simp [lookupSub]
  | cons head tail ih =>
    cases i with
    | zero =>
      intro _
      simp [depth]
    | succ i =>
      intro h
      simp [lookupSub] at h
      rcases h with ⟨a, ha, _⟩
      have hi := ih ha
      simpa [depth, Nat.add_comm] using Nat.succ_lt_succ hi

/-- A successful `.equ` lookup is necessarily within the context depth. -/
theorem lookupEqu_some_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.lookupEqu i = some t → i < Γ.depth := by
  induction Γ generalizing i t with
  | nil =>
    simp [lookupEqu]
  | cons head tail ih =>
    cases i with
    | zero =>
      intro _
      simp [depth]
    | succ i =>
      intro h
      simp [lookupEqu] at h
      rcases h with ⟨a, ha, _⟩
      have hi := ih ha
      simpa [depth, Nat.add_comm] using Nat.succ_lt_succ hi

/-- A `.sub` binding index is necessarily within the context depth. -/
theorem subBinds_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.subBinds i t → i < Γ.depth :=
  lookupSub_some_lt

/-- An `.equ` binding index is necessarily within the context depth. -/
theorem equBinds_lt {Γ : Ctx} {i : Nat} {t : Term} :
    Γ.equBinds i t → i < Γ.depth :=
  lookupEqu_some_lt

/-- Raw lookup weakens under a new head by incrementing the index. -/
theorem lookup_weaken_head {Γ : Ctx} {i : Nat} {entry found : CtxEntry} :
    lookup Γ i = some found → lookup (entry :: Γ) (i + 1) = some found := by
  intro h
  simpa using h

/-- Subtype lookup weakens under a new head by incrementing the index and
lifting the looked-up bound through the new binding. -/
theorem subBinds_weaken_head {Γ : Ctx} {i : Nat} {t : Term} (entry : CtxEntry) :
    subBinds Γ i t → subBinds (entry :: Γ) (i + 1) (Term.shift 0 t) := by
  intro h
  simp [subBinds]
  exact ⟨t, h, rfl⟩

/-- Equivalence lookup weakens under a new head by incrementing the index and
lifting the looked-up bound through the new binding. -/
theorem equBinds_weaken_head {Γ : Ctx} {i : Nat} {t : Term} (entry : CtxEntry) :
    equBinds Γ i t → equBinds (entry :: Γ) (i + 1) (Term.shift 0 t) := by
  intro h
  simp [equBinds]
  exact ⟨t, h, rfl⟩

end Ctx

/-! ## Stacks and extended contexts -/

/-- A continuation stack. List head is top of stack. -/
abbrev Stack := List Term

namespace Stack

/-- Shift every term in a stack. -/
def shiftBy (cutoff amount : Nat) : Stack → Stack :=
  List.map (Term.shiftBy cutoff amount)

/-- One-step shift every term in a stack. -/
def shift (cutoff : Nat) : Stack → Stack :=
  shiftBy cutoff 1

@[simp] theorem shiftBy_nil (cutoff amount : Nat) :
    shiftBy cutoff amount [] = [] := rfl

@[simp] theorem shiftBy_cons (cutoff amount : Nat) (α : Term) (s : Stack) :
    shiftBy cutoff amount (α :: s) =
      Term.shiftBy cutoff amount α :: shiftBy cutoff amount s := rfl

@[simp] theorem shift_nil (cutoff : Nat) :
    shift cutoff [] = [] := rfl

@[simp] theorem shift_cons (cutoff : Nat) (α : Term) (s : Stack) :
    shift cutoff (α :: s) = Term.shift cutoff α :: shift cutoff s := rfl

/-- Every term in a stack is scoped in a context of depth `depth`. Type-valued
so it can carry proof-relevant `Term.Scoped` witnesses. -/
inductive Scoped (depth : Nat) : Stack → Type
  | nil : Scoped depth []
  | cons {α : Term} {s : Stack} :
      Term.Scoped depth α → Scoped depth s → Scoped depth (α :: s)

/-- One-step shifting preserves stack scoping under one additional ambient
binding. -/
noncomputable def Scoped.shift {depth : Nat} {s : Stack} :
    Scoped depth s → Scoped (depth + 1) (Stack.shift 0 s) := by
  intro h
  induction h with
  | nil =>
    exact Scoped.nil
  | cons hα hs ih =>
    exact Scoped.cons (Term.shift_scoped 0 depth _ (Nat.zero_le _) hα) ih

end Stack

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
  induction hΓ generalizing i t with
  | empty =>
    simp [Ctx.subBinds] at hb
  | @sub Γ' u hΓ' hu ih =>
    cases i with
    | zero =>
      simp [Ctx.subBinds] at hb
      subst hb
      simpa [Ctx.depth] using Term.shift_scoped 0 Γ'.depth u (Nat.zero_le _) hu
    | succ i =>
      simp [Ctx.subBinds] at hb
      cases hlook : Γ'.lookupSub i with
      | none =>
        simp [hlook] at hb
      | some a =>
        simp [hlook] at hb
        have hsc : Term.Scoped Γ'.depth a := ih hlook
        have hsc' : Term.Scoped (Γ'.depth + 1) (Term.shift 0 a) :=
          Term.shift_scoped 0 Γ'.depth a (Nat.zero_le _) hsc
        subst hb
        simpa [Ctx.depth] using hsc'
  | @equ Γ' α hΓ' hα ih =>
    cases i with
    | zero =>
      simp [Ctx.subBinds] at hb
    | succ i =>
      simp [Ctx.subBinds] at hb
      cases hlook : Γ'.lookupSub i with
      | none =>
        simp [hlook] at hb
      | some a =>
        simp [hlook] at hb
        have hsc : Term.Scoped Γ'.depth a := ih hlook
        have hsc' : Term.Scoped (Γ'.depth + 1) (Term.shift 0 a) :=
          Term.shift_scoped 0 Γ'.depth a (Nat.zero_le _) hsc
        subst hb
        simpa [Ctx.depth] using hsc'

/-- Lookup of an `.equ` binding in a prevalid context returns a term scoped in
the whole context. -/
noncomputable def scoped_lookupEqu {Γ : Ctx} {i : Nat} {α : Term}
    (hΓ : Prevalid Γ) (hb : Γ.equBinds i α) : Term.Scoped Γ.depth α := by
  induction hΓ generalizing i α with
  | empty =>
    simp [Ctx.equBinds] at hb
  | @sub Γ' u hΓ' hu ih =>
    cases i with
    | zero =>
      simp [Ctx.equBinds] at hb
    | succ i =>
      simp [Ctx.equBinds] at hb
      cases hlook : Γ'.lookupEqu i with
      | none =>
        simp [hlook] at hb
      | some a =>
        simp [hlook] at hb
        have hsc : Term.Scoped Γ'.depth a := ih hlook
        have hsc' : Term.Scoped (Γ'.depth + 1) (Term.shift 0 a) :=
          Term.shift_scoped 0 Γ'.depth a (Nat.zero_le _) hsc
        subst hb
        simpa [Ctx.depth] using hsc'
  | @equ Γ' β hΓ' hβ ih =>
    cases i with
    | zero =>
      simp [Ctx.equBinds] at hb
      subst hb
      simpa [Ctx.depth] using Term.shift_scoped 0 Γ'.depth β (Nat.zero_le _) hβ
    | succ i =>
      simp [Ctx.equBinds] at hb
      cases hlook : Γ'.lookupEqu i with
      | none =>
        simp [hlook] at hb
      | some a =>
        simp [hlook] at hb
        have hsc : Term.Scoped Γ'.depth a := ih hlook
        have hsc' : Term.Scoped (Γ'.depth + 1) (Term.shift 0 a) :=
          Term.shift_scoped 0 Γ'.depth a (Nat.zero_le _) hsc
        subst hb
        simpa [Ctx.depth] using hsc'

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

/-- Every operand in a prevalid stack is scoped in the logical context. -/
noncomputable def stack_scoped {Γ : Ctx} {s : Stack} :
    PrevalidExt Γ s → Stack.Scoped Γ.depth s := by
  intro h
  induction h with
  | nil _ =>
    exact Stack.Scoped.nil
  | cons hst hα ih =>
    exact Stack.Scoped.cons hα ih

/-- Extend the logical context at the head while shifting stack operands to
preserve references to the old context. -/
noncomputable def weaken_head {Γ : Ctx} {s : Stack} {e : CtxEntry} :
    PrevalidExt Γ s → Prevalid (e :: Γ) → PrevalidExt (e :: Γ) (Stack.shift 0 s) := by
  intro h hpvHead
  induction h with
  | nil _ =>
    exact PrevalidExt.nil hpvHead
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (Term.shift_scoped 0 Γ.depth _ (Nat.zero_le _) hα)

/-- One-step shifting preserves prevalidity of stacks when the context is
extended at the head. -/
noncomputable def shift_stack_prevalid_head {Γ : Ctx} {s : Stack} {e : CtxEntry}
    (hpv : Prevalid (e :: Γ)) :
    PrevalidExt Γ s → PrevalidExt (e :: Γ) (Stack.shift 0 s) :=
  fun h => weaken_head h hpv

end PrevalidExt

end DeBruijn
end Pss
