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

namespace CtxEntry

/-- Shift the stored bound of a context entry. -/
def shift (cutoff : Nat) (entry : CtxEntry) : CtxEntry :=
  { bound := Term.shift cutoff entry.bound, kind := entry.kind }

@[simp] theorem shift_bound (cutoff : Nat) (entry : CtxEntry) :
    (entry.shift cutoff).bound = Term.shift cutoff entry.bound := rfl

@[simp] theorem shift_kind (cutoff : Nat) (entry : CtxEntry) :
    (entry.shift cutoff).kind = entry.kind := rfl

end CtxEntry

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

/-- Insert a context entry after `cutoff` preserved heads. Preserved entries
have their stored bounds shifted at the number of still-preserved heads below
them, because the inserted entry is outside those heads but inside the
remaining tail. If `cutoff` is larger than the context depth this leaves the
context unchanged; well-scoped uses carry a `cutoff ≤ Γ.depth` premise. -/
def insertAt (cutoff : Nat) (newEntry : CtxEntry) : Ctx → Ctx
  | Γ =>
      match cutoff, Γ with
      | 0, Γ => newEntry :: Γ
      | _ + 1, [] => []
      | cutoff + 1, head :: Γ => head.shift cutoff :: insertAt cutoff newEntry Γ

@[simp] theorem lookup_nil (i : Nat) : lookup [] i = none := rfl
@[simp] theorem lookupSub_nil (i : Nat) : lookupSub [] i = none := rfl
@[simp] theorem lookupEqu_nil (i : Nat) : lookupEqu [] i = none := rfl

@[simp] theorem insertAt_zero (newEntry : CtxEntry) (Γ : Ctx) :
    insertAt 0 newEntry Γ = newEntry :: Γ := rfl

@[simp] theorem insertAt_succ_nil (cutoff : Nat) (newEntry : CtxEntry) :
    insertAt (cutoff + 1) newEntry [] = [] := rfl

@[simp] theorem insertAt_succ_cons (cutoff : Nat) (newEntry head : CtxEntry) (Γ : Ctx) :
    insertAt (cutoff + 1) newEntry (head :: Γ) =
      head.shift cutoff :: insertAt cutoff newEntry Γ := rfl

@[simp] theorem insertAt_one_cons (newEntry head : CtxEntry) (Γ : Ctx) :
    insertAt 1 newEntry (head :: Γ) = head.shift 0 :: newEntry :: Γ := rfl

@[simp] theorem insertAt_two_cons_cons
    (newEntry head₁ head₂ : CtxEntry) (Γ : Ctx) :
    insertAt 2 newEntry (head₁ :: head₂ :: Γ) =
      head₁.shift 1 :: head₂.shift 0 :: newEntry :: Γ := rfl

@[simp] theorem depth_insertAt_of_le {cutoff : Nat} {newEntry : CtxEntry} {Γ : Ctx}
    (hcut : cutoff ≤ Γ.depth) :
    depth (insertAt cutoff newEntry Γ) = Γ.depth + 1 := by
  induction Γ generalizing cutoff with
  | nil =>
    cases cutoff with
    | zero =>
      simp [depth]
    | succ cutoff =>
      simp [depth] at hcut
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      simp [depth]
    | succ cutoff =>
      have htail : cutoff ≤ Ctx.depth tail := by
        simpa [depth, Nat.add_comm] using Nat.succ_le_succ_iff.mp hcut
      have hdepth := ih htail
      simp [depth] at hdepth ⊢
      omega

/-- The newly inserted entry is found exactly at the insertion cutoff. -/
theorem lookup_insertAt_self {cutoff : Nat} {newEntry : CtxEntry} {Γ : Ctx}
    (hcut : cutoff ≤ Γ.depth) :
    lookup (insertAt cutoff newEntry Γ) cutoff = some newEntry := by
  induction Γ generalizing cutoff with
  | nil =>
    cases cutoff with
    | zero =>
      rfl
    | succ cutoff =>
      simp [depth] at hcut
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      rfl
    | succ cutoff =>
      have htail : cutoff ≤ Ctx.depth tail := by
        simpa [depth, Nat.add_comm] using Nat.succ_le_succ_iff.mp hcut
      simpa using ih htail

/-- Raw lookup transport for entries at or outside the insertion cutoff: their
indices move up by one. -/
theorem lookup_insertAt_after {Γ : Ctx} {cutoff i : Nat} {newEntry found : CtxEntry}
    (hidx : cutoff ≤ i) :
    lookup Γ i = some found →
    lookup (insertAt cutoff newEntry Γ) (i + 1) = some found := by
  induction Γ generalizing cutoff i with
  | nil =>
    simp [lookup]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      intro h
      simpa using h
    | succ cutoff =>
      cases i with
      | zero =>
        omega
      | succ i =>
        intro h
        have htail : cutoff ≤ i := Nat.succ_le_succ_iff.mp hidx
        simpa using ih (cutoff := cutoff) (i := i) htail h

/-- Raw lookup transport for entries before the insertion cutoff: their
indices are preserved, while their stored bounds are shifted by the number of
preserved heads below them. -/
theorem lookup_insertAt_before {Γ : Ctx} {cutoff i : Nat} {newEntry found : CtxEntry}
    (hidx : i < cutoff) :
    lookup Γ i = some found →
    lookup (insertAt cutoff newEntry Γ) i = some (found.shift (cutoff - (i + 1))) := by
  induction Γ generalizing cutoff i with
  | nil =>
    simp [lookup]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      omega
    | succ cutoff =>
      cases i with
      | zero =>
        intro h
        cases h
        rfl
      | succ i =>
        intro h
        have htail : i < cutoff := Nat.succ_lt_succ_iff.mp hidx
        have hrec := ih (cutoff := cutoff) (i := i) htail h
        simpa [Nat.succ_sub_succ_eq_sub] using hrec

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

theorem lookupSub_unique {Γ : Ctx} {i : Nat} {t u : Term} :
    Γ.lookupSub i = some t → Γ.lookupSub i = some u → t = u := by
  intro ht hu
  rw [ht] at hu
  cases hu
  rfl

theorem lookupEqu_unique {Γ : Ctx} {i : Nat} {α β : Term} :
    Γ.lookupEqu i = some α → Γ.lookupEqu i = some β → α = β := by
  intro hα hβ
  rw [hα] at hβ
  cases hβ
  rfl

theorem subBinds_unique {Γ : Ctx} {i : Nat} {t u : Term} :
    Γ.subBinds i t → Γ.subBinds i u → t = u :=
  lookupSub_unique

theorem equBinds_unique {Γ : Ctx} {i : Nat} {α β : Term} :
    Γ.equBinds i α → Γ.equBinds i β → α = β :=
  lookupEqu_unique

theorem subBinds_equBinds_false {Γ : Ctx} {i : Nat} {t α : Term} :
    Γ.subBinds i t → Γ.equBinds i α → False := by
  unfold subBinds equBinds
  induction Γ generalizing i t α with
  | nil =>
    simp
  | cons entry Γ ih =>
    cases i with
    | zero =>
      cases entry with
      | mk bound kind =>
        cases kind <;> simp [lookupSub, lookupEqu]
    | succ i =>
      intro hsub heq
      cases hSubLookup : lookupSub Γ i with
      | none =>
        simp [lookupSub, hSubLookup] at hsub
      | some t0 =>
        cases hEquLookup : lookupEqu Γ i with
        | none =>
          simp [lookupEqu, hEquLookup] at heq
        | some α0 =>
          exact ih hSubLookup hEquLookup

theorem equBinds_subBinds_false {Γ : Ctx} {i : Nat} {α t : Term} :
    Γ.equBinds i α → Γ.subBinds i t → False := by
  intro heq hsub
  exact subBinds_equBinds_false hsub heq

@[simp] theorem subBinds_zero_self (Γ : Ctx) (t : Term) :
    subBinds ({ bound := t, kind := .sub } :: Γ) 0 (Term.shift 0 t) := rfl

@[simp] theorem equBinds_zero_self (Γ : Ctx) (t : Term) :
    equBinds ({ bound := t, kind := .equ } :: Γ) 0 (Term.shift 0 t) := rfl

/-- An equivalence lookup at an `.equ` head can only return that head's
stored bound, lifted into the extended context. -/
theorem equBinds_zero_equ_inv {Γ : Ctx} {t α : Term} :
    equBinds ({ bound := t, kind := .equ } :: Γ) 0 α →
    α = Term.shift 0 t := by
  intro h
  simpa [equBinds] using h.symm

/-- A subtype lookup at an `.equ` head is impossible. -/
theorem subBinds_zero_equ_false {Γ : Ctx} {t u : Term} :
    subBinds ({ bound := t, kind := .equ } :: Γ) 0 u → False := by
  simp [subBinds]

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

/-- Changing the bound stored in an `.equ` head does not affect subtype
lookups, because subtype lookup skips `.equ` heads. -/
theorem subBinds_equ_head_replace {Γ : Ctx} {old new : Term} {i : Nat} {t : Term} :
    subBinds ({ bound := old, kind := .equ } :: Γ) i t →
    subBinds ({ bound := new, kind := .equ } :: Γ) i t := by
  cases i with
  | zero =>
    simp [subBinds]
  | succ i =>
    intro h
    simpa [subBinds] using h

/-- Changing the bound stored in an `.equ` head preserves all equivalence
lookups outside that head. -/
theorem equBinds_equ_head_replace_succ {Γ : Ctx} {old new : Term}
    {i : Nat} {α : Term} :
    equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
    equBinds ({ bound := new, kind := .equ } :: Γ) (i + 1) α := by
  intro h
  simpa [equBinds] using h

/-- If an equivalence lookup under an `.equ` head does not target index `0`,
changing the head bound preserves it. -/
theorem equBinds_equ_head_replace_of_ne_zero {Γ : Ctx} {old new : Term}
    {i : Nat} {α : Term} (hi : i ≠ 0) :
    equBinds ({ bound := old, kind := .equ } :: Γ) i α →
    equBinds ({ bound := new, kind := .equ } :: Γ) i α := by
  cases i with
  | zero =>
    exact (hi rfl).elim
  | succ i =>
    exact equBinds_equ_head_replace_succ

/-- Subtype lookup transport for entries at or outside an insertion cutoff.
The returned bound is lifted through the inserted entry. -/
theorem subBinds_insertAt_after {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {t : Term} (hidx : cutoff ≤ i) :
    subBinds Γ i t →
    subBinds (insertAt cutoff newEntry Γ) (i + 1) (Term.shift 0 t) := by
  induction Γ generalizing cutoff i t with
  | nil =>
    simp [subBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      intro h
      simp [subBinds]
      exact ⟨t, h, rfl⟩
    | succ cutoff =>
      cases i with
      | zero =>
        omega
      | succ i =>
        intro h
        have htail : cutoff ≤ i := Nat.succ_le_succ_iff.mp hidx
        simp [subBinds] at h ⊢
        cases hlook : lookupSub tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              subBinds (insertAt cutoff newEntry tail) (i + 1) (Term.shift 0 a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [subBinds] at htail_bind
          subst h
          simp [htail_bind]

/-- Reduction-facing subtype lookup transport for entries at or outside an
insertion cutoff. This is the same index movement as
`subBinds_insertAt_after`, but presents the lifted bound as a shift at the
insertion cutoff, matching shifted reduction terms. -/
theorem subBinds_insertAt_after_shift {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {t : Term} (hidx : cutoff ≤ i) :
    subBinds Γ i t →
    subBinds (insertAt cutoff newEntry Γ) (i + 1) (Term.shift cutoff t) := by
  induction Γ generalizing cutoff i t with
  | nil =>
    simp [subBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      intro h
      simpa using subBinds_insertAt_after (Γ := head :: tail)
        (cutoff := 0) (i := i) (newEntry := newEntry) hidx h
    | succ cutoff =>
      cases i with
      | zero =>
        omega
      | succ i =>
        intro h
        have htail : cutoff ≤ i := Nat.succ_le_succ_iff.mp hidx
        simp [subBinds] at h ⊢
        cases hlook : lookupSub tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              subBinds (insertAt cutoff newEntry tail) (i + 1) (Term.shift cutoff a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [subBinds] at htail_bind
          subst h
          exact ⟨Term.shift cutoff a, htail_bind,
            (Term.shiftBy_shift_zero cutoff 1 a).symm⟩

/-- Subtype lookup transport for entries before an insertion cutoff. Their
indices are preserved, and their returned bounds are shifted at the cutoff
remaining below that entry. -/
theorem subBinds_insertAt_before {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {t : Term} (hidx : i < cutoff) :
    subBinds Γ i t →
    subBinds (insertAt cutoff newEntry Γ) i (Term.shift cutoff t) := by
  induction Γ generalizing cutoff i t with
  | nil =>
    simp [subBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      omega
    | succ cutoff =>
      cases i with
      | zero =>
        intro h
        cases head with
        | mk bound kind =>
          cases kind <;> simp [subBinds, CtxEntry.shift] at h ⊢
          subst h
          exact (Term.shiftBy_lift_comm 0 cutoff 1 bound (Nat.zero_le cutoff)).symm
      | succ i =>
        intro h
        have htail : i < cutoff := Nat.succ_lt_succ_iff.mp hidx
        simp [subBinds] at h ⊢
        cases hlook : lookupSub tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              subBinds (insertAt cutoff newEntry tail) i (Term.shift cutoff a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [subBinds] at htail_bind
          subst h
          exact ⟨Term.shift cutoff a, htail_bind,
            (Term.shiftBy_lift_comm 0 cutoff 1 a (Nat.zero_le cutoff)).symm⟩

/-- Equivalence lookup transport for entries at or outside an insertion cutoff.
The returned bound is lifted through the inserted entry. -/
theorem equBinds_insertAt_after {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {α : Term} (hidx : cutoff ≤ i) :
    equBinds Γ i α →
    equBinds (insertAt cutoff newEntry Γ) (i + 1) (Term.shift 0 α) := by
  induction Γ generalizing cutoff i α with
  | nil =>
    simp [equBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      intro h
      simp [equBinds]
      exact ⟨α, h, rfl⟩
    | succ cutoff =>
      cases i with
      | zero =>
        omega
      | succ i =>
        intro h
        have htail : cutoff ≤ i := Nat.succ_le_succ_iff.mp hidx
        simp [equBinds] at h ⊢
        cases hlook : lookupEqu tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              equBinds (insertAt cutoff newEntry tail) (i + 1) (Term.shift 0 a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [equBinds] at htail_bind
          subst h
          simp [htail_bind]

/-- Reduction-facing equivalence lookup transport for entries at or outside an
insertion cutoff. -/
theorem equBinds_insertAt_after_shift {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {α : Term} (hidx : cutoff ≤ i) :
    equBinds Γ i α →
    equBinds (insertAt cutoff newEntry Γ) (i + 1) (Term.shift cutoff α) := by
  induction Γ generalizing cutoff i α with
  | nil =>
    simp [equBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      intro h
      simpa using equBinds_insertAt_after (Γ := head :: tail)
        (cutoff := 0) (i := i) (newEntry := newEntry) hidx h
    | succ cutoff =>
      cases i with
      | zero =>
        omega
      | succ i =>
        intro h
        have htail : cutoff ≤ i := Nat.succ_le_succ_iff.mp hidx
        simp [equBinds] at h ⊢
        cases hlook : lookupEqu tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              equBinds (insertAt cutoff newEntry tail) (i + 1) (Term.shift cutoff a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [equBinds] at htail_bind
          subst h
          exact ⟨Term.shift cutoff a, htail_bind,
            (Term.shiftBy_shift_zero cutoff 1 a).symm⟩

/-- Equivalence lookup transport for entries before an insertion cutoff. Their
indices are preserved, and their returned bounds are shifted at the insertion
cutoff. -/
theorem equBinds_insertAt_before {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {α : Term} (hidx : i < cutoff) :
    equBinds Γ i α →
    equBinds (insertAt cutoff newEntry Γ) i (Term.shift cutoff α) := by
  induction Γ generalizing cutoff i α with
  | nil =>
    simp [equBinds]
  | cons head tail ih =>
    cases cutoff with
    | zero =>
      omega
    | succ cutoff =>
      cases i with
      | zero =>
        intro h
        cases head with
        | mk bound kind =>
          cases kind <;> simp [equBinds, CtxEntry.shift] at h ⊢
          subst h
          exact (Term.shiftBy_lift_comm 0 cutoff 1 bound (Nat.zero_le cutoff)).symm
      | succ i =>
        intro h
        have htail : i < cutoff := Nat.succ_lt_succ_iff.mp hidx
        simp [equBinds] at h ⊢
        cases hlook : lookupEqu tail i with
        | none =>
          simp [hlook] at h
        | some a =>
          simp [hlook] at h
          have htail_bind :
              equBinds (insertAt cutoff newEntry tail) i (Term.shift cutoff a) :=
            ih (cutoff := cutoff) (i := i) htail hlook
          simp [equBinds] at htail_bind
          subst h
          exact ⟨Term.shift cutoff a, htail_bind,
            (Term.shiftBy_lift_comm 0 cutoff 1 a (Nat.zero_le cutoff)).symm⟩

/-- De Bruijn index translation for inserting a new context entry after
`cutoff` preserved heads. -/
def insertAtIndex (cutoff i : Nat) : Nat :=
  if cutoff ≤ i then i + 1 else i

/-- Shifting a variable at `cutoff` implements the corresponding insertion
translation on its index. -/
theorem shift_bvar_insertAtIndex (cutoff i : Nat) :
    Term.shift cutoff (.bvar i) = .bvar (insertAtIndex cutoff i) := by
  by_cases h : cutoff ≤ i
  · simp [Term.shift, Term.shiftBy, insertAtIndex, h]
  · simp [Term.shift, Term.shiftBy, insertAtIndex, h]

@[simp] theorem insertAtIndex_zero (i : Nat) :
    insertAtIndex 0 i = i + 1 := by
  simp [insertAtIndex]

@[simp] theorem insertAtIndex_succ_self (cutoff : Nat) :
    insertAtIndex (cutoff + 1) cutoff = cutoff := by
  simp [insertAtIndex]

theorem insertAtIndex_eq_self_of_lt {cutoff i : Nat} :
    i < cutoff → insertAtIndex cutoff i = i := by
  intro h
  simp [insertAtIndex, Nat.not_le_of_gt h]

theorem insertAtIndex_eq_succ_of_le {cutoff i : Nat} :
    cutoff ≤ i → insertAtIndex cutoff i = i + 1 := by
  intro h
  simp [insertAtIndex, h]

/-- Inserting into a context preserves in-bounds indices after translating
them with `insertAtIndex`. -/
theorem insertAtIndex_lt_depth {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth) (hi : i < Γ.depth) :
    insertAtIndex cutoff i < (insertAt cutoff newEntry Γ).depth := by
  have hdepth : (insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    depth_insertAt_of_le hcut
  by_cases hidx : cutoff ≤ i
  · rw [insertAtIndex_eq_succ_of_le hidx, hdepth]
    omega
  · have hlt : i < cutoff := Nat.lt_of_not_ge hidx
    rw [insertAtIndex_eq_self_of_lt hlt, hdepth]
    omega

/-- Subtype binding transport across `insertAt`, stated using the common
translated index. -/
theorem subBinds_insertAt {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {t : Term} :
    subBinds Γ i t →
    subBinds (insertAt cutoff newEntry Γ) (insertAtIndex cutoff i) (Term.shift cutoff t) := by
  intro h
  by_cases hidx : cutoff ≤ i
  · rw [insertAtIndex_eq_succ_of_le hidx]
    exact subBinds_insertAt_after_shift hidx h
  · have hlt : i < cutoff := Nat.lt_of_not_ge hidx
    rw [insertAtIndex_eq_self_of_lt hlt]
    exact subBinds_insertAt_before hlt h

/-- Equivalence binding transport across `insertAt`, stated using the common
translated index. -/
theorem equBinds_insertAt {Γ : Ctx} {cutoff i : Nat} {newEntry : CtxEntry}
    {α : Term} :
    equBinds Γ i α →
    equBinds (insertAt cutoff newEntry Γ) (insertAtIndex cutoff i) (Term.shift cutoff α) := by
  intro h
  by_cases hidx : cutoff ≤ i
  · rw [insertAtIndex_eq_succ_of_le hidx]
    exact equBinds_insertAt_after_shift hidx h
  · have hlt : i < cutoff := Nat.lt_of_not_ge hidx
    rw [insertAtIndex_eq_self_of_lt hlt]
    exact equBinds_insertAt_before hlt h

/-- De Bruijn index translation for inserting a new context entry immediately
under an existing head binder. The binder keeps index `0`; every outer
reference moves up by one. -/
def insertUnderHeadIndex : Nat → Nat
  | 0 => 0
  | i + 1 => i + 2

@[simp] theorem insertUnderHeadIndex_zero :
    insertUnderHeadIndex 0 = 0 := rfl

@[simp] theorem insertUnderHeadIndex_succ (i : Nat) :
    insertUnderHeadIndex (i + 1) = i + 2 := rfl

/-- Shifting at cutoff `1` implements the index translation for inserting a
new context entry immediately under the current head binder. -/
theorem shift_one_bvar_insertUnderHeadIndex (i : Nat) :
    Term.shift 1 (.bvar i) = .bvar (insertUnderHeadIndex i) := by
  rw [shift_bvar_insertAtIndex]
  cases i with
  | zero =>
    rfl
  | succ i =>
    simp [insertAtIndex]

/-- De Bruijn index translation for inserting a new context entry immediately
under two existing heads. The two innermost binders keep indices `0` and `1`;
every outer reference moves up by one. -/
def insertUnderTwoHeadsIndex : Nat → Nat
  | 0 => 0
  | 1 => 1
  | i + 2 => i + 3

@[simp] theorem insertUnderTwoHeadsIndex_zero :
    insertUnderTwoHeadsIndex 0 = 0 := rfl

@[simp] theorem insertUnderTwoHeadsIndex_one :
    insertUnderTwoHeadsIndex 1 = 1 := rfl

@[simp] theorem insertUnderTwoHeadsIndex_add_two (i : Nat) :
    insertUnderTwoHeadsIndex (i + 2) = i + 3 := rfl

/-- Shifting at cutoff `2` implements the index translation for inserting a
new context entry immediately under two current heads. -/
theorem shift_two_bvar_insertUnderTwoHeadsIndex (i : Nat) :
    Term.shift 2 (.bvar i) = .bvar (insertUnderTwoHeadsIndex i) := by
  rw [shift_bvar_insertAtIndex]
  cases i with
  | zero =>
    rfl
  | succ i =>
    cases i with
    | zero =>
      rfl
    | succ i =>
      simp [insertAtIndex]

/-- Subtype lookup weakens when a new context entry is inserted immediately
under an existing head binder. The looked-up bound is lifted through the
inserted entry, while the head binder remains at index `0`. -/
theorem subBinds_weaken_tail_head {Γ : Ctx} {head newHead : CtxEntry} {i : Nat} {t : Term} :
    subBinds (head :: Γ) i t →
    subBinds (head.shift 0 :: newHead :: Γ) (insertUnderHeadIndex i) (Term.shift 0 t) := by
  intro h
  cases i with
  | zero =>
    cases head with
    | mk bound kind =>
      cases kind <;> simp [subBinds, CtxEntry.shift] at h ⊢
      subst h
      rfl
  | succ i =>
    simp [subBinds] at h ⊢
    cases hlook : lookupSub Γ i with
    | none =>
      simp [hlook] at h
    | some a =>
      simp [hlook] at h
      subst h
      simp [hlook]

/-- Equivalence lookup weakens when a new context entry is inserted immediately
under an existing head binder. -/
theorem equBinds_weaken_tail_head {Γ : Ctx} {head newHead : CtxEntry} {i : Nat} {α : Term} :
    equBinds (head :: Γ) i α →
    equBinds (head.shift 0 :: newHead :: Γ) (insertUnderHeadIndex i) (Term.shift 0 α) := by
  intro h
  cases i with
  | zero =>
    cases head with
    | mk bound kind =>
      cases kind <;> simp [equBinds, CtxEntry.shift] at h ⊢
      subst h
      rfl
  | succ i =>
    simp [equBinds] at h ⊢
    cases hlook : lookupEqu Γ i with
    | none =>
      simp [hlook] at h
    | some a =>
      simp [hlook] at h
      subst h
      simp [hlook]

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

/-- Stack-level lift commutation inherited pointwise from terms. -/
theorem shiftBy_lift_comm (base cutoff amount : Nat) (s : Stack)
    (hbase : base ≤ cutoff) :
    shiftBy (cutoff + 1) amount (shiftBy base 1 s) =
      shiftBy base 1 (shiftBy cutoff amount s) := by
  induction s with
  | nil =>
    rfl
  | cons α s ih =>
    simp only [shiftBy_cons, Term.shiftBy_lift_comm base cutoff amount α hbase, ih]

/-- Shifting a stack below one newly introduced binder commutes with the raw
top-level one-step lift. -/
theorem shiftBy_shift_zero (cutoff amount : Nat) (s : Stack) :
    shiftBy (cutoff + 1) amount (shift 0 s) =
      shift 0 (shiftBy cutoff amount s) := by
  simpa [shift] using shiftBy_lift_comm 0 cutoff amount s (Nat.zero_le cutoff)

/-- One-step version of `Stack.shiftBy_shift_zero`. -/
theorem shift_shift_zero (cutoff : Nat) (s : Stack) :
    shift (cutoff + 1) (shift 0 s) =
      shift 0 (shift cutoff s) := by
  simpa [shift] using shiftBy_shift_zero cutoff 1 s

/-- The stack shape used when weakening a body derivation under an existing
binder matches the shape obtained by first weakening the outer stack. -/
theorem shift_one_shift_zero (s : Stack) :
    shift 1 (shift 0 s) = shift 0 (shift 0 s) := by
  simpa [shift] using shiftBy_shift_zero 0 1 s

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

/-- One-step shifting at an arbitrary cutoff preserves stack scoping under one
additional ambient binding. -/
noncomputable def Scoped.shiftAt {depth cutoff : Nat} {s : Stack}
    (hcut : cutoff ≤ depth) :
    Scoped depth s → Scoped (depth + 1) (Stack.shift cutoff s) := by
  intro h
  induction h with
  | nil =>
    exact Scoped.nil
  | cons hα hs ih =>
    exact Scoped.cons (Term.shift_scoped cutoff depth _ hcut hα) ih

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

/-- Insert a prevalid entry into a prevalid context after `cutoff` preserved
heads. The inserted-entry witness is stated over the actual tail at the
insertion point. -/
noncomputable def insertAt {Γ : Ctx} {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth) :
    Prevalid Γ →
    Prevalid (newEntry :: List.drop cutoff Γ) →
    Prevalid (Ctx.insertAt cutoff newEntry Γ) := by
  intro hΓ hNew
  induction hΓ generalizing cutoff with
  | empty =>
    cases cutoff with
    | zero =>
      exact hNew
    | succ cutoff =>
      simp [Ctx.depth] at hcut
  | @sub Γ' t hTail hbound ih =>
    cases cutoff with
    | zero =>
      exact hNew
    | succ cutoff =>
      have htail : cutoff ≤ Ctx.depth Γ' := by
        simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ_iff.mp hcut
      have hbound' : Term.Scoped (Γ'.depth + 1) (Term.shift cutoff t) :=
        Term.shift_scoped cutoff _ _ htail hbound
      have hdepth :
          Ctx.depth (Ctx.insertAt cutoff newEntry Γ') = Γ'.depth + 1 :=
        Ctx.depth_insertAt_of_le htail
      exact Prevalid.sub
        (ih htail hNew)
        (by simpa [hdepth] using hbound')
  | @equ Γ' α hTail hbound ih =>
    cases cutoff with
    | zero =>
      exact hNew
    | succ cutoff =>
      have htail : cutoff ≤ Ctx.depth Γ' := by
        simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ_iff.mp hcut
      have hbound' : Term.Scoped (Γ'.depth + 1) (Term.shift cutoff α) :=
        Term.shift_scoped cutoff _ _ htail hbound
      have hdepth :
          Ctx.depth (Ctx.insertAt cutoff newEntry Γ') = Γ'.depth + 1 :=
        Ctx.depth_insertAt_of_le htail
      exact Prevalid.equ
        (ih htail hNew)
        (by simpa [hdepth] using hbound')

/-- Rebuild a prevalid head over a newly extended tail. The stored head bound
is shifted through the new tail head. This is the context-side operation needed
when weakening reductions under one binder: the binder remains innermost, while
the old outer context receives a new head. -/
noncomputable def weaken_tail_head {Γ : Ctx} {head newHead : CtxEntry} :
    Prevalid (head :: Γ) →
    Prevalid (newHead :: Γ) →
    Prevalid (head.shift 0 :: newHead :: Γ) := by
  intro hHead hNew
  cases hHead with
  | sub _ hbound =>
    exact Prevalid.sub hNew (Term.shift_scoped 0 Γ.depth _ (Nat.zero_le _) hbound)
  | equ _ hbound =>
    exact Prevalid.equ hNew (Term.shift_scoped 0 Γ.depth _ (Nat.zero_le _) hbound)

/-- Rebuild two prevalid heads over a newly extended tail. This is the next
context shape encountered when reduction weakening descends through an
abstraction inside an already-open binder body. -/
noncomputable def weaken_second_tail_head {Γ : Ctx} {head₁ head₂ newHead : CtxEntry} :
    Prevalid (head₁ :: head₂ :: Γ) →
    Prevalid (newHead :: Γ) →
    Prevalid (head₁.shift 1 :: head₂.shift 0 :: newHead :: Γ) := by
  intro hHeads hNew
  cases hHeads with
  | sub hTail hbound =>
    exact Prevalid.sub
      (Prevalid.weaken_tail_head hTail hNew)
      (Term.shift_scoped 1 (Γ.depth + 1) _ (by omega) hbound)
  | equ hTail hbound =>
    exact Prevalid.equ
      (Prevalid.weaken_tail_head hTail hNew)
      (Term.shift_scoped 1 (Γ.depth + 1) _ (by omega) hbound)

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

/-- Replace the bound stored in an innermost `.equ` context entry. The tail
context and context depth are unchanged, so all existing entries remain
well-scoped once the new bound is scoped in the same tail. -/
noncomputable def equ_head_replace {Γ : Ctx} {old new : Term} :
    Prevalid ({ bound := old, kind := .equ } :: Γ) →
    Term.Scoped Γ.depth new →
    Prevalid ({ bound := new, kind := .equ } :: Γ) := by
  intro h hnew
  cases h with
  | equ hΓ _ =>
    exact Prevalid.equ hΓ hnew

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

/-- Replace the bound stored in an innermost `.equ` context entry while
preserving extended-context prevalidity. -/
noncomputable def equ_head_replace {Γ : Ctx} {s : Stack} {old new : Term} :
    PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
    Term.Scoped Γ.depth new →
    PrevalidExt ({ bound := new, kind := .equ } :: Γ) s := by
  intro h hnew
  induction h with
  | nil hΓ =>
    exact PrevalidExt.nil (Prevalid.equ_head_replace hΓ hnew)
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (by
      simpa [Ctx.depth] using hα)

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

/-- Insert a logical context entry at an arbitrary cutoff while shifting stack
operands at the same cutoff. -/
noncomputable def insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth) :
    PrevalidExt Γ s →
    Prevalid (Ctx.insertAt cutoff newEntry Γ) →
    PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s) := by
  intro h hpv
  induction h with
  | nil _ =>
    exact PrevalidExt.nil hpv
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (by
      have hα' := Term.shift_scoped cutoff Γ.depth _ hcut hα
      have hdepth :
          Ctx.depth (Ctx.insertAt cutoff newEntry Γ) = Γ.depth + 1 :=
        Ctx.depth_insertAt_of_le hcut
      simpa [hdepth] using hα')

/-- Insert a new logical context entry immediately under an existing binder
head. Stack operands are shifted at cutoff `1`, preserving references to the
innermost binder at index `0` while lifting all outer-context references. -/
noncomputable def weaken_tail_head {Γ : Ctx} {s : Stack} {head newHead : CtxEntry} :
    PrevalidExt (head :: Γ) s →
    Prevalid (head.shift 0 :: newHead :: Γ) →
    PrevalidExt (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s) := by
  intro h hpv
  induction h with
  | nil _ =>
    exact PrevalidExt.nil hpv
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (Term.shift_scoped 1 (Γ.depth + 1) _ (by omega) hα)

/-- Insert a new logical context entry immediately under two existing binder
heads, shifting stack operands at cutoff `2`. -/
noncomputable def weaken_second_tail_head {Γ : Ctx} {s : Stack}
    {head₁ head₂ newHead : CtxEntry} :
    PrevalidExt (head₁ :: head₂ :: Γ) s →
    Prevalid (head₁.shift 1 :: head₂.shift 0 :: newHead :: Γ) →
    PrevalidExt (head₁.shift 1 :: head₂.shift 0 :: newHead :: Γ) (Stack.shift 2 s) := by
  intro h hpv
  induction h with
  | nil _ =>
    exact PrevalidExt.nil hpv
  | cons hst hα ih =>
    exact PrevalidExt.cons ih (Term.shift_scoped 2 (Γ.depth + 2) _ (by omega) hα)

end PrevalidExt

end DeBruijn
end Pss
