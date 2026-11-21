import Ochr.Meaning.DataModel.Faithful
import Ochr.Meaning.Attack.RunEqs

/-!
# Piece 3's run lemmas: what the reference run gives a field-type or parameter-type term

Faithfulness (`DataModel/Faithful.lean`) is conditional: WHERE the run of a declared type term is
defined, its result is the model's. So each lemma here says what the result is when the run is
defined, for one term form, in the frames faithfulness runs in (`teleFrame`, `paramFrame`: one
frame, no live borrow), under EVERY run context (decisions included): a lemma about the run of a
term form, not about a program.

* `runT_var_frame`: a variable reads its binding's value (whatever the decisions say about erasure
  and copying: an erased read that is not `•` fails, `SM.erasedIf`);
* `runT_sort`: `Sort l` is `Type_l`'s code.
-/

namespace Ochr.Meaning.DataModel.Exists.RunLemmas

open Ochr Ochr.Meaning

/-- A one-frame, shape-free state: what `stateOf` builds. -/
theorem stateOf_shape (n : Nat) (bs : List SBinding) : (stateOf n bs).shape = fun _ => none := rfl

/-- In such a state, variable `j` is binding `bs.length - 1 - j` (the last binding is `var 0`). -/
theorem varPos_stateOf (n : Nat) (bs : List SBinding) (j : Nat) (hj : j < bs.length) :
    (stateOf n bs).varPos j = some (.bind 0 (bs.length - 1 - j)) := by
  simp [SState.varPos, stateOf, SState.topIdx, hj]

/-- Its value there, at any future, when the binding's value is constant. -/
theorem valAt_stateOf (n : Nat) (bs : List SBinding) (k : Nat) (hk : k < bs.length) (ψ : Future) :
    (stateOf n bs).valAt (.bind 0 k) ψ = bs[k].val ψ := by
  simp [SState.valAt, stateOf, hk]

/-- **A variable's run reads its binding's value**: in a shape-free state, if the run of `var j` is
defined, its result is the value at `var j`'s position, at the typed future (which a shape-free state
does not move). Whatever the decisions: copy or move, statement or not, and a proof read only when the
value is `•`. -/
theorem runT_var (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (j : Nat) (s : SState)
    (hs : s.shape = fun _ => none) (pos : Pos) (hpos : s.varPos j = some pos)
    {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.place (.var j)) s = some (r, s')) :
    r.1 = s.valAt pos φ := by
  have hacc : ∀ hit, s.access pos hit = s := fun hit => Attack.access_noShape s hs pos hit
  have htf : s.typedFuture φ = φ := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simpa [List.filterMap_cons] using ih
    funext l; simp [SState.typedFuture, SState.liveLabels, hs, h0]
  have hc : contentOf K φ (.var j) s = some ((s.valAt pos φ, s.tyAt pos, pos, []), s) := by
    simp only [contentOf, resolve, Place.steps, hpos, Option.map_some, hacc, htf, Sem.follow]
    rfl
  -- the read: whatever it does to the state, its value is the content's
  have hrd : ∀ copy r' s'', readPlace K φ (.var j) copy s = some (r', s'') → r'.1 = s.valAt pos φ := by
    intro copy r' s'' h'
    simp only [readPlace, hc, bind, Option.bind] at h'
    split at h'
    · cases h'
    · split at h'
      · cases h'
      · split at h'
        · cases h'; rfl
        · revert h'
          generalize setContent K φ pos [] Sem.moved s = sc
          intro h'
          cases sc with
          | none => cases h'
          | some p =>
            obtain ⟨⟨⟩, s₁⟩ := p
            simp only at h'
            split at h' <;> (cases h'; rfl)
  -- the read is guarded (the STRICT END test, ruling (A)); the guard changes no value
  have hg : ∀ copy r' s'', SM.guarded (ContentOk K φ (.var j)) (readPlace K φ (.var j) copy) s = some (r', s'') →
      r'.1 = s.valAt pos φ := fun copy r' s'' h' => hrd copy r' s'' (SM.guarded_some h').2
  simp only [runT] at hr
  unfold SM.erasedIf at hr
  split at hr
  · split at hr
    · rename_i r₀ T₀ s₀ hx
      cases hr
      exact (hg _ _ _ hx).symm ▸ rfl
    · cases hr
    · cases hr
  · unfold SM.stmtIf at hr
    split at hr
    · revert hr
      cases hx : SM.guarded (ContentOk K φ (.var j)) (readPlace K φ (.var j) _) s with
      | none => intro hr; cases hr
      | some x =>
        intro hr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact hg _ x.1 x.2 hx
    · exact hg _ _ _ hr

/-- **`Sort l` runs to `Type_l`'s code.** -/
theorem runT_sort (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (l : Nat) (s : SState) :
    runT K ρ φ tl h (.sort l) s = some ((.ty (TyM.univ l), .plain (TyM.univ (sortSucc l))), s) := by
  simp [runT, pure]

/-! ## The frame a field type runs in -/

/-- `teleFrame`'s bindings: the constructor's fields (the earlier ones, then `moved`), then the
parameters. -/
theorem teleFrame_eq (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) :
    ∃ fbs : List SBinding, fbs.length = (e ++ List.replicate (DataLib.arity d c - e.length) Sem.moved).length ∧
      teleFrame dm D d ps c e = stateOf 0 (fbs ++ ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1
        ((paramDecls D d (DataLib.arity d c)).getD vj.2 .other))) :=
  ⟨_, by simp [DataLib.arity], rfl⟩

/-- **A parameter read in a field type is the parameter**: in `teleFrame`, at a field below the
constructor's arity, variable `ps.length - 1 - j` reads parameter `j` (the checker numbers the
parameters first, the last one `var 0`), so where its run is defined it gives `ps[j]`. -/
theorem runT_teleFrame_param (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS)
    (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ DataLib.arity d c) (j : Nat) (hj : j < ps.length) {r : Res} {s' : SState}
    (hr : runT K ρ φ tl h (.place (.var (ps.length - 1 - j))) (teleFrame dm D d ps c e) = some (r, s')) :
    r.1 = ps[j] := by
  obtain ⟨fbs, hl, heq⟩ := teleFrame_eq dm D d ps c e
  rw [heq] at hr
  have hlen : fbs.length = DataLib.arity d c := by
    simp only [List.length_append, List.length_replicate] at hl; omega
  generalize hL : ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1
        ((paramDecls D d (DataLib.arity d c)).getD vj.2 .other)) = L at hr
  have hLl : L.length = ps.length := by rw [← hL]; simp
  have hv : ps.length - 1 - j < (fbs ++ L).length := by simp [hLl]; omega
  have h1 := runT_var K ρ φ tl h _ _ (stateOf_shape 0 _) _ (varPos_stateOf 0 _ _ hv) hr
  rw [h1]
  have hk : (fbs ++ L).length - 1 - (ps.length - 1 - j) = fbs.length + j := by simp [hLl]; omega
  have hget : (fbs ++ L)[fbs.length + j]? = some (faithBind (dm.paramTy d j (ps.take j)) ps[j]
      ((paramDecls D d (DataLib.arity d c)).getD j .other)) := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ← hL]
    simp [List.getElem?_map, hj]
  rw [hk]
  have hlt : fbs.length + j < (fbs ++ L).length := by simp [hLl]; omega
  rw [valAt_stateOf 0 _ _ hlt]
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
  rw [hget]
  rfl

end Ochr.Meaning.DataModel.Exists.RunLemmas
