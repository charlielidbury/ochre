import Ochr.Meaning.ClosureRef

/-!
# The weakened stage closure (the recursion knot's stage-`b` meaning; docs/34, Handoff)

While a recursive function is checked, its meaning is known to be good only at arguments whose
decreasing component has rank below a bound `b`. The function that is good only there is not an
element of the function's type (a closure is built strictly; `ClosureCE`), unless every result type
is already known to be inhabited, which is what the induction is proving. So the stage-`b` meaning
is given a **weakened** function type: the true result type below the bound, `Unit` above it (the
true proposition `True` at sort `0`). The stage function (`stageFn`) is the stage below the bound
and a trivial output above it (`()`, the borrow arguments handed back unchanged, any label), so it
is good everywhere at the weakened type, and the stage closure is an honest element built by the
ordinary strict construction (`closureAt`), with no fill.

* `stage_mem`: at a data sort, the stage closure is a member of the weakened function type.
* `stage_apply`: applied at arguments below the bound, it gives the stage's result at the TRUE
  result type (the weakened codomain agrees with the true one there).
* `stage_mem_prop`: the sort-`0` form (a function into propositions).
* `stage_mem_ref`, `stage_apply_ref`: at a returned borrow (`ClosureRef.lean`); above the bound the
  borrow's content type is `Unit`, so the backward function is injective trivially.
-/

namespace Ochr.Meaning

open Ochr Ochr.Meaning.Steps

/-- The rank of the decreasing argument (the `fix`'s index `dec`; `0` for a function that does not
recurse): `semRank`, as the run's `.fix` clause (`rankOf`) and `Steps.decRank` read it. -/
noncomputable def decArgRank (dec : Option Nat) (args : List Sem) : Nat :=
  match dec with
  | some j => ((args[j]?).map semRank).getD 0
  | none => 0

theorem fillVal_mem (R : DataRead) (l : Nat) : fillVal l ∈ₛ[R] fillTy l := by
  unfold fillVal fillTy
  split
  · exact ⟨⟨trivial⟩, rfl⟩
  · exact ⟨(), rfl⟩

theorem refFinals_length : ∀ (ds : List PiDom) (args : List Sem), args.length = ds.length →
    (refFinals ds args).length = (ds.filter (·.isRef)).length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | d :: ds, a :: as, h => by
    have ih := refFinals_length ds as (by simpa using h)
    cases hd : d.isRef <;> simp [refFinals, hd, ih]

theorem refFinals_get : ∀ (ds : List PiDom) (args : List Sem) (i : Nat) (d : PiDom) (a : Sem),
    ds[i]? = some d → args[i]? = some a → d.isRef = true →
    (refFinals ds args)[((ds.take i).filter (·.isRef)).length]? = some (fun _ => a)
  | [], _, _, _, _, hd, _, _ => by simp at hd
  | _ :: _, [], _, _, _, _, ha, _ => by simp at ha
  | d0 :: ds, a0 :: as, 0, d, a, hd, ha, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hd ha
    subst hd; subst ha
    simp [refFinals, hr]
  | d0 :: ds, a0 :: as, i + 1, d, a, hd, ha, hr => by
    simp only [List.getElem?_cons_succ] at hd ha
    have ih := refFinals_get ds as i d a hd ha hr
    cases h0 : d0.isRef <;> simp [refFinals, h0, ih]

/-- Above the bound, the trivial output is good at the weakened codomain. -/
theorem fill_outGood (R : DataRead) (l : Nat) (ds : List PiDom) (rk : List Sem → Nat) (b : Nat)
    (out : PiCod) (args : List Sem) (hm : DomMembers R ds args) (hge : ¬ rk args < b) :
    OutGood R ds (weakCod l rk b out) args ⟨fillVal l, refFinals ds args, some 0⟩ := by
  refine ⟨?_, fun i d hd hr => ?_⟩
  · show fillVal l ∈ₛ[R] (if rk args < b then out.cod args else fillTy l)
    rw [if_neg hge]; exact fillVal_mem R l
  · have hi : i < args.length := by
      rw [hm.1]; exact (List.getElem?_eq_some_iff.mp hd).1
    obtain ⟨a, ha⟩ : ∃ a, args[i]? = some a := ⟨args[i], List.getElem?_eq_getElem hi⟩
    exact ⟨fun _ => a, refFinals_get ds args i d a hd ha hr, fun _ _ => hm.2 i a d ha hd⟩

/-- Below the bound the weakened codomain's result holds what the true codomain's does. -/
theorem held_weakCod (l : Nat) (rk : List Sem → Nat) (b : Nat) (out : PiCod) (args : List Sem) (o : BodyOut)
    (hlt : rk args < b) : o.held (weakCod l rk b out) args = o.held out args := by
  simp [BodyOut.held, weakCod, hlt]

/-- The stage function is good everywhere at the weakened codomain, given the stage good below the
bound. -/
theorem stageFn_good (R : DataRead) (l : Nat) (ds : List PiDom) (rk : List Sem → Nat) (b : Nat)
    (out : PiCod) (stage : List Sem → Option BodyOut)
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length) :
    ∀ args, DomMembers R ds args →
      ∃ o, stageFn l ds rk b stage args = some o ∧ OutGood R ds (weakCod l rk b out) args o ∧
        o.finals.length = (ds.filter (·.isRef)).length := by
  intro args hm
  by_cases hlt : rk args < b
  · obtain ⟨o, hg, ⟨hres, hfin⟩, hlen⟩ := hgood args hm hlt
    refine ⟨o, by simp [stageFn, hlt, hg], ⟨?_, by rw [held_weakCod l rk b out args o hlt]; exact hfin⟩, hlen⟩
    show o.result ∈ₛ[R] (if rk args < b then out.cod args else fillTy l)
    rw [if_pos hlt]; exact hres
  · exact ⟨_, by simp [stageFn, hlt], fill_outGood R l ds rk b out args hm hlt,
      refFinals_length ds args hm.1⟩

/-- **The stage closure is a member of the weakened function type** (data sort `1 ≤ l ≤ 3`, a data
codomain whose code fits the level below the bound): an honest element, built strictly. -/
theorem stage_mem (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (rk : List Sem → Nat) (b : Nat) (stage : List Sem → Option BodyOut)
    (hl : 1 ≤ l ∧ l ≤ 3) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers R ds args → rk args < b → LevelFit l (out.cod args))
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length) :
    closureAt R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage) ∈ₛ[R]
      piTyAt R l ds (weakCod l rk b out) := by
  refine closure_mem_of_total' R l φ ds _ _ hl hdata (fun args hm => ?_)
    (stageFn_good R l ds rk b out stage hgood)
  show LevelFit l (if rk args < b then out.cod args else fillTy l)
  split
  · exact hcod args hm ‹_›
  · have : l ≠ 0 := by omega
    simp only [fillTy, this, if_false, TyM.unit, LevelFit]; exact hl.1

/-- **The stage closure applied below the bound is the stage's result, at the TRUE codomain** (the
weakened codomain agrees with it there), as a call reads it: at member arguments whose domains fit
the level, the codomain canonical there. -/
theorem stage_apply (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (rk : List Sem → Nat) (b : Nat) (stage : List Sem → Option BodyOut)
    (hl : 1 ≤ l ∧ l ≤ 3) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers R ds args → rk args < b → LevelFit l (out.cod args))
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers R ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom ((args.map (·.1)).take i)))
    (hlt : rk (args.map (·.1)) < b) (hcanon : (out.cod (args.map (·.1))).Canon)
    (hg : stage (args.map (·.1)) = some o) :
    ∃ s', callOf R (closureAt R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage),
        .plain (piTyAt R l ds (weakCod l rk b out))) args s =
      some ((o.result, .plain (out.cod (args.map (·.1)))), s') := by
  have hw : (weakCod l rk b out).cod (args.map (·.1)) = out.cod (args.map (·.1)) := by
    simp [weakCod, hlt]
  have := closure_apply' R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage) hl hdata
    (fun args hm => by
      show LevelFit l (if rk args < b then out.cod args else fillTy l)
      split
      · exact hcod args hm ‹_›
      · have : l ≠ 0 := by omega
        simp only [fillTy, this, if_false, TyM.unit, LevelFit]; exact hl.1)
    (stageFn_good R l ds rk b out stage hgood) args s o hmem hdom (by rw [hw]; exact hcanon)
    (by simp [stageFn, hlt, hg])
  rwa [hw] at this

/-- **The sort-`0` form**: a stage closure into propositions is a member of the weakened function
type (the proposition that the codomain holds below the bound) when the stage is defined below the
bound with a result in the codomain, a proposition there. -/
theorem stage_mem_prop (R : DataRead) (φ : Future) (ds : List PiDom) (out : PiCod)
    (rk : List Sem → Nat) (b : Nat) (stage : List Sem → Option BodyOut) (hdata : out.isRef = false)
    (hprop : ∀ args, DomMembers R ds args → rk args < b → ∃ P, out.cod args = TyM.prop P)
    (htot : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ o.result ∈ₛ[R] out.cod args) :
    closureAt R 0 φ ds (weakCod 0 rk b out) (stageFn 0 ds rk b stage) ∈ₛ[R]
      piTyAt R 0 ds (weakCod 0 rk b out) := by
  refine closure_mem_prop' R φ ds _ _ hdata (fun args hm => ?_) (fun args hm => ?_)
  · show ∃ P, (if rk args < b then out.cod args else fillTy 0) = TyM.prop P
    split
    · exact hprop args hm ‹_›
    · exact ⟨True, rfl⟩
  · by_cases hlt : rk args < b
    · obtain ⟨o, hg, hres⟩ := htot args hm hlt
      refine ⟨o, by simp [stageFn, hlt, hg], ?_⟩
      show o.result ∈ₛ[R] (if rk args < b then out.cod args else fillTy 0)
      rw [if_pos hlt]; exact hres
    · refine ⟨⟨fillVal 0, refFinals ds args, some 0⟩, by simp [stageFn, hlt], ?_⟩
      show fillVal 0 ∈ₛ[R] (if rk args < b then out.cod args else fillTy 0)
      rw [if_neg hlt]; exact fillVal_mem R 0

/-! ## At a returned borrow -/

/-- Above the bound at a data sort, the trivial output's returned borrow is good: its content type
is `Unit`, which has one member. -/
theorem fill_retGood (R : DataRead) (l : Nat) (hl : l ≠ 0) (ds : List PiDom) (rk : List Sem → Nat) (b : Nat)
    (out : PiCod) (args : List Sem) (hge : ¬ rk args < b) :
    RetGood R (weakCod l rk b out) args ⟨fillVal l, refFinals ds args, some 0⟩ := by
  refine ⟨0, rfl, fun ψ v w hv hw _ => ?_⟩
  simp only [weakCod, hge, if_false, fillTy, hl, TyM.unit] at hv hw
  obtain ⟨⟨⟩, rfl⟩ := hv
  obtain ⟨⟨⟩, rfl⟩ := hw
  rfl

/-- The stage function is good everywhere at the weakened codomain, returned borrow included. -/
theorem stageFn_good_ref (R : DataRead) (l : Nat) (hl : l ≠ 0) (ds : List PiDom) (rk : List Sem → Nat)
    (b : Nat) (out : PiCod) (stage : List Sem → Option BodyOut)
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ RetGood R out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length) :
    ∀ args, DomMembers R ds args →
      ∃ o, stageFn l ds rk b stage args = some o ∧ OutGood R ds (weakCod l rk b out) args o ∧
        RetGood R (weakCod l rk b out) args o ∧ o.finals.length = (ds.filter (·.isRef)).length := by
  intro args hm
  by_cases hlt : rk args < b
  · obtain ⟨o, hg, ⟨hres, hfin⟩, ⟨k, hk, hinj⟩, hlen⟩ := hgood args hm hlt
    have hw : (weakCod l rk b out).cod args = out.cod args := by simp [weakCod, hlt]
    refine ⟨o, by simp [stageFn, hlt, hg], ⟨by rw [hw]; exact hres, by rw [held_weakCod l rk b out args o hlt]; exact hfin⟩,
      ⟨k, hk, fun ψ v w hv hw' => hinj ψ v w (by rwa [hw] at hv) (by rwa [hw] at hw')⟩, hlen⟩
  · exact ⟨_, by simp [stageFn, hlt], fill_outGood R l ds rk b out args hm hlt,
      fill_retGood R l hl ds rk b out args hlt, refFinals_length ds args hm.1⟩

theorem weakCod_fit (l : Nat) (hl : 1 ≤ l ∧ l ≤ 3) (R : DataRead) (ds : List PiDom) (rk : List Sem → Nat)
    (b : Nat) (out : PiCod) (hcod : ∀ args, DomMembers R ds args → rk args < b → LevelFit l (out.cod args)) :
    ∀ args, DomMembers R ds args → LevelFit l ((weakCod l rk b out).cod args) := by
  intro args hm
  show LevelFit l (if rk args < b then out.cod args else fillTy l)
  split
  · exact hcod args hm ‹_›
  · have : l ≠ 0 := by omega
    simp only [fillTy, this, if_false, TyM.unit, LevelFit]; exact hl.1

/-- **The stage closure at a returned borrow is a member of the weakened function type.** -/
theorem stage_mem_ref (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (rk : List Sem → Nat) (b : Nat) (stage : List Sem → Option BodyOut)
    (hl : 1 ≤ l ∧ l ≤ 3) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers R ds args → rk args < b → LevelFit l (out.cod args))
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ RetGood R out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length) :
    closureAt R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage) ∈ₛ[R]
      piTyAt R l ds (weakCod l rk b out) :=
  closure_mem_of_total_ref' R l φ ds _ _ hl href (weakCod_fit l hl R ds rk b out hcod)
    (stageFn_good_ref R l (by omega) ds rk b out stage hgood)

/-- **The stage closure at a returned borrow, applied below the bound**, is the stage's result at
the TRUE codomain, under a fresh label, as a call reads it. -/
theorem stage_apply_ref (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (rk : List Sem → Nat) (b : Nat) (stage : List Sem → Option BodyOut)
    (hl : 1 ≤ l ∧ l ≤ 3) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers R ds args → rk args < b → LevelFit l (out.cod args))
    (hgood : ∀ args, DomMembers R ds args → rk args < b →
      ∃ o, stage args = some o ∧ OutGood R ds out args o ∧ RetGood R out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers R ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom ((args.map (·.1)).take i)))
    (hlt : rk (args.map (·.1)) < b) (hcanon : (out.cod (args.map (·.1))).Canon)
    (hg : stage (args.map (·.1)) = some o) :
    ∃ k s', callOf R (closureAt R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage),
        .plain (piTyAt R l ds (weakCod l rk b out))) args s =
      some ((o.result, ⟨out.cod (args.map (·.1)), some k⟩), s') := by
  have hw : (weakCod l rk b out).cod (args.map (·.1)) = out.cod (args.map (·.1)) := by
    simp [weakCod, hlt]
  have := closure_apply_ref' R l φ ds (weakCod l rk b out) (stageFn l ds rk b stage) hl href
    (weakCod_fit l hl R ds rk b out hcod) (stageFn_good_ref R l (by omega) ds rk b out stage hgood)
    args s o hmem hdom (by rw [hw]; exact hcanon) (by simp [stageFn, hlt, hg])
  rwa [hw] at this

end Ochr.Meaning
