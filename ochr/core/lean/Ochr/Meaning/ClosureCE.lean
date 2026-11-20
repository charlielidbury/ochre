import Ochr.Meaning.Steps.Statements

/-!
# The closure lemma as stated in `Steps/FixKnot.lean`: where it is false (kernel-checked)

`closure_mem_of_total` and `closure_apply` (the knot's two closure statements, owed by the data
layer) each fail at a small closure, here, for every data reading:

1. `closure_apply` asks only that the function be defined at the arguments applied. A closure is
   built strictly (`closureAt` is `mkTelL`'s element, `err` unless the function is defined and of its
   type at EVERY member argument), so a function defined at one argument only makes the closure
   `err`, and the call fails (`closure_apply_false`).
2. `closure_mem_of_total` at sort `0`: the closure is `⋆` and its type the proposition that the
   codomain is TRUE at every argument; a good function into `Nat` makes it `prop False`
   (`closure_mem_prop_false`).
3. `closure_mem_of_total` at a returned borrow: the carrier holds the functions with an injective
   backward function and a returned label (`mkLeafRefL`), which `OutGood` does not ask
   (`closure_mem_ref_false`).
4. `closure_mem_of_total` at a codomain above the closure's level: a function of sort `Type₀`
   returning `Type₀`'s elements (types) has no code at level 0 to decode its result at
   (`closure_mem_level_false`).

The true forms are in `Closure.lean`.
-/

namespace Ochr.Meaning.ClosureCE

universe u

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `Π(n : Nat). Nat`'s description. -/
def dsN : List PiDom := [⟨false, fun _ => TyM.nat⟩]
def outN : PiCod := ⟨false, fun _ => TyM.nat⟩

/-- Defined at `0` only. -/
noncomputable def gAt0 (args : List Sem) : Option BodyOut :=
  open Classical in if args = [.el0 Nat 0] then some ⟨.el0 Nat 0, [], none⟩ else none

/-- A built function is built at every element of its first parameter. -/
theorem mkTelL_param_some {L : Lvl.{u}} {φ : Future} {Fin : Type u} {isRef : Bool} {A : Type u} {c : L.Code A}
    {C : A → Type u} {k : (a : A) → Tel L.Code (extFin isRef Fin A) (C a)} {acc : List Sem}
    {mkFin : List Sem → Option (Fin × List Sem)} {g : List Sem → Option BodyOut} {F : (a : A) → C a}
    (h : mkTelL L φ (.param Fin isRef A c C k) acc mkFin g = some F) :
    ∀ x, (mkTelL L φ (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) g).isSome := by
  simp only [mkTelL] at h
  split at h
  · assumption
  · cases h

theorem closureAt_gAt0_err (R : DataRead) (φ : Future) : closureAt R 1 φ dsN outN gAt0 = .err := by
  simp only [closureAt, closureL]
  split
  · rename_i F hF
    exfalso
    have h1 := mkTelL_param_some hF (by exact (1 : Nat))
    revert h1
    simp [mkTelL, gAt0, dsN, outN, telL, lvl0, TyM.code0, TyM.nat, Code0.enc]
  · rfl

/-- `err` is no function's meaning. -/
theorem err_not_mem_pi (R : DataRead) (C : Type) (t : Tel Code0 PUnit C) : ¬ (Sem.err ∈ₛ[R] TyM.t0 C (.pi C t)) := by
  rintro ⟨f, hf⟩
  cases hf

/-- **`closure_apply`, as stated, is false.** -/
theorem closure_apply_false (R : DataRead) :
    ¬ (∀ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (g : List Sem → Option BodyOut),
        1 ≤ l ∧ l ≤ 3 → ∀ (args : List Res) (s : SState) (o : BodyOut),
        DomMembers R ds (args.map (·.1)) → g (args.map (·.1)) = some o → out.isRef = false →
        ∃ s', callOf R (closureAt R l φ ds out g, .plain (piTyAt R l ds out)) args s =
          some ((o.result, .plain (out.cod (args.map (·.1)))), s')) := by
  intro h
  obtain ⟨s', hs'⟩ := h 1 noFuture dsN outN gAt0 ⟨Nat.le_refl 1, by omega⟩ [(.el0 Nat 0, .plain TyM.nat)]
    (emptyState 0) ⟨.el0 Nat 0, [], none⟩
    ⟨rfl, fun i a d ha hd => by
      cases i with
      | zero =>
        simp [dsN] at ha hd; subst ha; subst hd; exact ⟨0, rfl⟩
      | succ i => simp at ha⟩
    (by simp [gAt0]) rfl
  rw [closureAt_gAt0_err] at hs'
  have hnone : callOfL (lvl0 R) (telL (lvl0 R) dsN [] PUnit outN).2 Sem.err [(.el0 Nat 0, .plain TyM.nat)]
      (emptyState 0) = none := by
    simp only [callOfL]; rfl
  have hc : callOf R (Sem.err, .plain (piTyAt R 1 dsN outN)) [(.el0 Nat 0, .plain TyM.nat)] (emptyState 0) =
      callOfL (lvl0 R) (telL (lvl0 R) dsN [] PUnit outN).2 Sem.err [(.el0 Nat 0, .plain TyM.nat)] (emptyState 0) := rfl
  rw [hc, hnone] at hs'
  cases hs'

/-- **`closure_mem_of_total` at sort `0` is false**: a good function into `Nat`. -/
theorem closure_mem_prop_false (R : DataRead) :
    ¬ (∀ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (g : List Sem → Option BodyOut), l ≤ 3 →
        (∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood R ds out args o) →
        closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out) := by
  intro h
  have hm := h 0 noFuture [] outN (fun _ => some ⟨.el0 Nat 0, [], none⟩) (by omega)
    (fun args _ => ⟨_, rfl, ⟨⟨0, rfl⟩, fun i d hd _ => by simp at hd⟩⟩)
  obtain ⟨⟨p⟩, -⟩ := hm
  exact p

/-- **`closure_mem_of_total` at a returned borrow is false**: a good function returning no label. -/
theorem closure_mem_ref_false (R : DataRead) :
    ¬ (∀ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (g : List Sem → Option BodyOut), l ≤ 3 →
        (∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood R ds out args o) →
        closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out) := by
  intro h
  have hm := h 1 noFuture [] ⟨true, fun _ => TyM.nat⟩ (fun _ => some ⟨.el0 Nat 0, [], none⟩) (by omega)
    (fun args _ => ⟨_, rfl, ⟨⟨0, rfl⟩, fun i d hd _ => by simp at hd⟩⟩)
  have he : closureAt R 1 noFuture [] ⟨true, fun _ => TyM.nat⟩ (fun _ => some ⟨.el0 Nat 0, [], none⟩) = .err := by
    simp [closureAt, closureL, telL, mkTelL, mkLeafRefL]
  rw [he] at hm
  exact err_not_mem_pi R _ _ hm

/-- **`closure_mem_of_total` at a codomain above the closure's level is false**: a function of sort
`Type₀` returning a type. -/
theorem closure_mem_level_false (R : DataRead) :
    ¬ (∀ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (g : List Sem → Option BodyOut), l ≤ 3 →
        (∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood R ds out args o) →
        closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out) := by
  intro h
  have hm := h 1 noFuture [] ⟨false, fun _ => TyM.univ 1⟩ (fun _ => some ⟨.ty TyM.nat, [], none⟩) (by omega)
    (fun args _ => ⟨_, rfl, ⟨⟨⟨Nat, Code0.nat, rfl⟩, rfl⟩, fun i d hd _ => by simp at hd⟩⟩)
  have he : closureAt R 1 noFuture [] ⟨false, fun _ => TyM.univ 1⟩ (fun _ => some ⟨.ty TyM.nat, [], none⟩) = .err := by
    simp only [closureAt, closureL]
    split
    · rename_i F hF
      simp only [telL, mkTelL, Option.bind_some, mkLeafDataL] at hF
      exact absurd hF (by
        simp only [lvl0, TyM.univ, TyM.code0]
        intro h'
        split at h'
        · rename_i r _ hr _
          exact r.elim
        · cases h')
    · rfl
  rw [he] at hm
  exact err_not_mem_pi R _ _ hm

end Ochr.Meaning.ClosureCE
