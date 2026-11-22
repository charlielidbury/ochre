import Ochr.Meaning.DataModel.Exists.FrameLocal.Run
import Ochr.Meaning.DataModel.Exists.RunLemmas

/-!
# The knot, part 1: swapping the bindings a term does not read (exists5)

The canonical frame of a record key and the actual frame a field type runs in (`teleFrame`) are
both one-frame, shape-free states (`stateOf`). They differ at bindings the term does not read: the
fields and parameters whose values vary between the knot's comparisons, and the earlier fields that
are no index. `runT_stateOf_swap` is frame locality (`FrameLocal.runT_qset`) in that form: two binding
lists equal off a set of indices `X`, each holding a constant whole value its type admits (`Good`)
at `X`, with the same declared readings there, give the same run of every term whose free variables
avoid `X`; the final states are related by the transform.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning SState Ochr.Meaning.DataModel.Exists.FrameLocal
open Classical

/-- The positions of frame `0` at the indices `X` below `len`. -/
def QX (X : Nat → Prop) (len : Nat) (p : Pos) : Prop := ∃ i, p = .bind 0 i ∧ i < len ∧ X i

/-- A binding list read as a function of positions (frame `0`), anything elsewhere. -/
noncomputable def βOf (bs : List SBinding) : Pos → SBinding
  | .bind 0 i => bs.getD i { ty := .plain TyM.err, val := fun _ => .err, decl := .other }
  | _ => { ty := .plain TyM.err, val := fun _ => .err, decl := .other }

section
variable {X : Nat → Prop} {bs bs' : List SBinding}

theorem βOf_get {i : Nat} (hi : i < bs.length) : βOf bs (.bind 0 i) = bs[i] := by
  simp [βOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The transform at `X` by the second list turns the first list's state into the second's. -/
theorem qset_stateOf (n : Nat) (hl : bs'.length = bs.length) (hsame : ∀ i, ¬ X i → bs'[i]? = bs[i]?) :
    qset (QX X bs.length) (βOf bs') (stateOf n bs) = stateOf n bs' := by
  simp only [qset, stateOf]
  congr 1
  · simp only [List.zipIdx_singleton, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    simp only [qframe]
    congr 1
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_zipIdx]
    rcases h : bs[i]? with _ | b
    · have : bs'[i]? = none := by
        rw [List.getElem?_eq_none_iff] at h ⊢; omega
      simp [this]
    · have hi : i < bs.length := (List.getElem?_eq_some_iff.1 h).1
      simp only [Option.map_some, Nat.zero_add]
      by_cases hx : X i
      · have hq : QX X bs.length (.bind 0 i) := ⟨i, rfl, hi, hx⟩
        rw [if_pos hq, βOf_get (by omega), List.getElem?_eq_getElem (by omega)]
      · have hq : ¬ QX X bs.length (.bind 0 i) := by
          rintro ⟨j, hj, -, hxj⟩
          cases hj; exact hx hxj
        rw [if_neg hq, hsame i hx, h]
  · funext p; split <;> rfl

theorem qset_stateOf_self (n : Nat) : qset (QX X bs.length) (βOf bs) (stateOf n bs) = stateOf n bs :=
  qset_stateOf n rfl (fun _ _ => rfl)

theorem pre_stateOf (n : Nat) (hc : ∀ i b, X i → bs[i]? = some b → ∃ c, b.val = fun _ => c)
    (hl : bs'.length = bs.length) (hc' : ∀ i b, X i → bs'[i]? = some b → ∃ c, b.val = fun _ => c) :
    Pre (QX X bs.length) (βOf bs') (stateOf n bs) := by
  refine ⟨fun f i h => ?_, fun p h => ?_, fun p _ => rfl, fun p h => ?_⟩
  · obtain ⟨j, hj, _⟩ := h; cases hj
  · obtain ⟨i, rfl, hi, _⟩ := h
    simp [SState.positions, stateOf, hi]
  · obtain ⟨i, rfl, hi, hx⟩ := h
    rw [βOf_get (by omega)]
    exact hc' i _ hx (List.getElem?_eq_getElem (by omega))
end

/-- **Frame locality between two one-frame states**: binding lists equal off `X`, each binding at `X`
`Good` in both, with the same declared reading, give the same run of a term whose free variables
avoid `X`; the second's final state is the first's transformed. -/
theorem runT_stateOf_swap (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (t : Term)
    (n : Nat) (bs bs' : List SBinding) (X : Nat → Prop)
    (hK : ∀ g, (K.C.global g).2.label = none) (hD : DecLocal K.D)
    (hl : bs'.length = bs.length) (hsame : ∀ i, ¬ X i → bs'[i]? = bs[i]?)
    (hgood : ∀ i b, X i → bs[i]? = some b → FrameLocal.Good K b) (hgood' : ∀ i b, X i → bs'[i]? = some b → FrameLocal.Good K b)
    (hdecl : ∀ i b b', X i → bs[i]? = some b → bs'[i]? = some b' → b'.decl = b.decl)
    (hconst : ∀ b ∈ bs, ∃ c, b.val = fun _ => c)
    (hvars : ∀ v ∈ t.freeVars, v < bs.length → ¬ X (bs.length - 1 - v)) :
    runT K ρ φ tl hint t (stateOf n bs') =
      (runT K ρ φ tl hint t (stateOf n bs)).map fun x => (x.1, qset (QX X bs.length) (βOf bs') x.2) := by
  have hc : ∀ i b, X i → bs[i]? = some b → ∃ c, b.val = fun _ => c := fun i b hx hb =>
    let ⟨c, e, _⟩ := hgood i b hx hb; ⟨c, e⟩
  have hc' : ∀ i b, X i → bs'[i]? = some b → ∃ c, b.val = fun _ => c := fun i b hx hb =>
    let ⟨c, e, _⟩ := hgood' i b hx hb; ⟨c, e⟩
  have hA : Adm K (QX X bs.length) (βOf bs) (βOf bs') (stateOf n bs) := by
    refine ⟨⟨pre_stateOf n hc rfl hc, pre_stateOf n hc hl hc', qset_stateOf_self n, EnvLe.refl _⟩, ?_, ?_, ?_⟩
    · rintro p ⟨i, rfl, hi, hx⟩
      rw [βOf_get hi, βOf_get (by omega)]
      exact hdecl i _ _ hx (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))
    · rintro p ⟨i, rfl, hi, hx⟩
      rw [βOf_get hi]
      exact hgood i _ hx (List.getElem?_eq_getElem hi)
    · rintro p ⟨i, rfl, hi, hx⟩
      rw [βOf_get (by omega)]
      exact hgood' i _ hx (List.getElem?_eq_getElem (by omega))
  have hV : VarsAvoid (QX X bs.length) (stateOf n bs) t := by
    intro v hv pos hpos
    by_cases hlt : v < bs.length
    · rw [RunLemmas.varPos_stateOf n bs v hlt] at hpos
      cases hpos
      rintro ⟨i, hi, -, hx⟩
      cases hi
      exact hvars v hv hlt hx
    · simp [SState.varPos, stateOf, hlt] at hpos
  have hR : RInv (fun _ => True) (stateOf n bs) := by
    apply rinv_of_const _ (fun _ => rfl)
    intro p
    cases p with
    | temp f i => exact ⟨.err, by simp [SState.valAt, stateOf]; cases f <;> simp⟩
    | bind f i =>
      simp only [SState.valAt, stateOf]
      split
      · rename_i b hb
        cases f with
        | succ f => simp at hb
        | zero =>
          simp only [List.getElem?_cons_zero, Option.bind_some] at hb
          exact hconst b (List.mem_of_getElem? hb)
      · exact ⟨.err, rfl⟩
  have h := runT_qset K ρ φ hK hD tl t hint (stateOf n bs) _ _ _ hA hV hR
  unfold Comm at h
  rw [qset_stateOf n hl hsame] at h
  rw [h]
  rfl

end Ochr.Meaning.DataModel.Exists.Knot
