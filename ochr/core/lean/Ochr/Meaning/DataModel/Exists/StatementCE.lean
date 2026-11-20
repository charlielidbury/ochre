import Ochr.Meaning.DataModel.Faithful
import Ochr.Meaning.DecisionsInst
import Ochr.Meaning.Consistency

/-!
# The existence statement as it stands is false: two counterexamples to `FieldsFaithful`

Both at the simplest declaration with a parameter, `Box (A : Type) := MkBox(x : A)` (the field's
type is the parameter, `var 0`), under the checker's decisions, for EVERY data model.

1. **A type parameter that is a junk code** (`fieldsFaithful_false_junk`). The universe `Type₀`'s
   carrier holds every level-1 code, among them data codes `.data d r X` whose carrier `X` is not
   the model's `car d r`. `ParamsTyped` admits such a parameter (as `.ty T`; universe membership
   would admit it too: its level is `1`). The run of the field type `A` reads the parameter and
   returns `T`, but no shape's type is `T` (`shapeTy_ne_junk`): `shapeTy` makes every data-coded
   leaf `err`, and a `sub`'s type has the model's carrier. Here `X := car d r → Prop`, which is not
   `car d r` by Cantor.
2. **A parameter list of the wrong length** (`fieldsFaithful_false_short`). `ParamsTyped` does not
   ask `ps.length = d.params.length`; at `ps = []` the field type's `var 0` is the field itself,
   bound `⊥` in `teleFrame`, so the run is undefined, and `FieldsFaithful` asks it defined.

Both lift to `Assembly.exists_dataModel` at the one-item program `[Box]` once the checker accepts
`Box` from empty Σ (`DataFaithful` at the whole program asks `CtxFaithful` at a state whose
declarations are `[Box]`).
-/

namespace Ochr.Meaning.DataModel.Exists.StatementCE

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-- `Box (A : Type) := MkBox(x : A)`, as the checker records it. -/
def boxD : IndDecl :=
  { name := "Box", params := [(⟨"A"⟩, .sort 1)], ctors := [("MkBox", [("x", .place (.var 0))])] }

/-! ## Cantor: a type is not its own powerset -/

theorem not_eq_set (X : Type) (h : X = (X → Prop)) : False := by
  let f : X → X → Prop := fun x => cast h x
  let S : X → Prop := fun x => ¬ f x x
  let x₀ : X := cast h.symm S
  have hx : f x₀ = S := by simp [f, x₀]
  have : S x₀ ↔ ¬ S x₀ := by
    constructor
    · intro hs; have := hs; simp only [S] at this; rw [hx] at this; exact this
    · intro hs; show ¬ f x₀ x₀; rw [hx]; exact hs
  exact (iff_not_self this).elim

theorem set_ne_pempty (X : Type) : (PEmpty : Type) ≠ (X → Prop) := by
  intro h
  have : Nonempty (X → Prop) := ⟨fun _ => True⟩
  rw [← h] at this
  exact this.elim (fun e => e.elim)

/-! ## No shape's type is a junk data code -/

/-- A data code whose carrier is `Set` of the model's carrier: a level-1 code (an element of
`Type₀`'s carrier) that no shape means. -/
def junk (dm : DataModel) (d : IndDecl) (r : Rec) : TyM :=
  .t0 ((dm.car d r → Prop)) (.data d r ((dm.car d r → Prop)))

theorem data_heq_inj {A A' : Type} {d d' : IndDecl} {r r' : Rec} (hA : A = A')
    (h : HEq (Code0.data d r A) (Code0.data d' r' A')) : d = d' ∧ r = r' := by
  subst hA
  cases h
  exact ⟨rfl, rfl⟩

theorem shapeTy_ne_junk (dm : DataModel) (s : Shape) (d : IndDecl) (r : Rec) :
    dm.shapeTy s ≠ junk dm d r := by
  intro h
  cases s with
  | leaf B c =>
    simp only [DataModel.shapeTy] at h
    by_cases hc : c.isData = true
    · rw [if_pos hc] at h
      obtain ⟨e, -⟩ := TyM.t0_inj h
      exact set_ne_pempty _ e
    · rw [if_neg hc] at h
      obtain ⟨e, hh⟩ := TyM.t0_inj h
      have := Code0.congr_heq (fun c => c.isData) c _ e hh
      simp [Code0.isData] at this
      exact hc this
  | sub d' r' =>
    simp only [DataModel.shapeTy] at h
    by_cases hs : (d'.sort == 0) = true
    · rw [if_pos hs] at h
      obtain ⟨e, -⟩ := TyM.t0_inj h
      exact set_ne_pempty _ e
    · rw [if_neg hs] at h
      unfold DataModel.tyR at h
      rw [if_neg hs] at h
      obtain ⟨e, hh⟩ := TyM.t0_inj h
      obtain ⟨rfl, rfl⟩ := data_heq_inj e hh
      exact not_eq_set _ e
  | prf d' r' =>
    simp only [DataModel.shapeTy] at h
    by_cases hs : (d'.sort == 0) = true
    · rw [if_pos hs] at h
      unfold DataModel.tyR at h
      rw [if_pos hs] at h
      obtain ⟨e, hh⟩ := TyM.t0_inj h
      have := Code0.congr_heq (fun c => c.isData) _ _ e hh
      simp [Code0.isData] at this
    · rw [if_neg hs] at h
      obtain ⟨e, -⟩ := TyM.t0_inj h
      exact set_ne_pempty _ e

/-! ## The run of a parameter read in `teleFrame` -/

theorem filterMap_none' {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all

theorem liveLabels_stateOf (bs : List SBinding) : (stateOf 0 bs).liveLabels = [] := by
  simp only [SState.liveLabels, stateOf, filterMap_none', List.mergeSort_nil]

theorem access_stateOf (bs : List SBinding) (p : Pos) (hit : List Step → Bool) :
    (stateOf 0 bs).access p hit = stateOf 0 bs := by
  simp [SState.access, liveLabels_stateOf]

/-- A variable of a one-frame state read by COPY (`Regress/CodeRuns.readPlace_frame`'s form). -/
theorem readPlace_frame_copy (K : RunCtx) (φ : Future) (bs : List SBinding) (i : Nat) (b : SBinding)
    (hi : i < bs.length) (hb : bs[bs.length - 1 - i]? = some b) (hw : (b.val φ).whole) :
    readPlace K φ (.var i) true (stateOf 0 bs) = some ((b.val φ, { b.ty with label := none }), stateOf 0 bs) := by
  have hr : resolve (stateOf 0 bs) (.var i) = some (.bind 0 (bs.length - 1 - i), []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, stateOf, hi]
  have hcf : (stateOf 0 bs).typedFuture φ = φ := by funext l; simp [SState.typedFuture, liveLabels_stateOf]
  simp only [readPlace, contentOf, hr, access_stateOf, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, stateOf, hb, hw]

theorem updAt_nil (dm : DataModel) (Γ : List IndDecl) (T : TyS) (f : Sem → Sem) (v : Sem) :
    Sem.updAt dm Γ T f [] v = some (f v) := rfl

/-- A variable of a one-frame state read by MOVE (`copy = false`): its meaning, at its type. -/
theorem readPlace_move (K : RunCtx) (φ : Future) (bs : List SBinding) (i : Nat) (b : SBinding)
    (hi : i < bs.length) (hb : bs[bs.length - 1 - i]? = some b) (hw : (b.val φ).whole) :
    ∃ s', readPlace K φ (.var i) false (stateOf 0 bs) = some ((b.val φ, { b.ty with label := none }), s') := by
  have hr : resolve (stateOf 0 bs) (.var i) = some (.bind 0 (bs.length - 1 - i), []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, stateOf, hi]
  have hcf : (stateOf 0 bs).typedFuture φ = φ := by funext l; simp [SState.typedFuture, liveLabels_stateOf]
  simp only [readPlace, contentOf, hr, access_stateOf, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, stateOf, hb, hw, setContent, updAt_nil]

/-- A variable of a one-frame state that is not whole (`⊥`) cannot be read. -/
theorem readPlace_notWhole (K : RunCtx) (φ : Future) (bs : List SBinding) (i : Nat) (b : SBinding) (cp : Bool)
    (hi : i < bs.length) (hb : bs[bs.length - 1 - i]? = some b) (hw : ¬ (b.val φ).whole) :
    readPlace K φ (.var i) cp (stateOf 0 bs) = none := by
  have hr : resolve (stateOf 0 bs) (.var i) = some (.bind 0 (bs.length - 1 - i), []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, stateOf, hi]
  have hcf : (stateOf 0 bs).typedFuture φ = φ := by funext l; simp [SState.typedFuture, liveLabels_stateOf]
  simp only [readPlace, contentOf, hr, access_stateOf, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, stateOf, hb, hw]

theorem whole_ty (T : TyM) : (Sem.ty T).whole := by
  unfold Sem.whole; exact trivial

theorem erasedAt_none {T : SState → TyS} {x : SM (Sem × TyS)} {s : SState} :
    SM.erasedAt (false, false) T x s = x s := rfl

theorem teleFrame_box (dm : DataModel) (T : TyM) :
    teleFrame dm boxD [.ty T] 0 [] = stateOf 0 [faithBind (dm.fieldTy boxD [.ty T] 0 0 []) .moved,
      faithBind (dm.paramTy boxD 0 []) (.ty T)] := rfl

theorem teleFrame_box_short (dm : DataModel) :
    teleFrame dm boxD [] 0 [] = stateOf 0 [faithBind (dm.fieldTy boxD [] 0 0 []) .moved] := rfl

/-- **Counterexample 1: a junk type parameter.** For every data model, at decisions that read a
variable of `teleFrame` as data (as the checker's do, `checker_flags`), `FieldsFaithful` fails at
`Box`: the run of `A` at `A := junk` is `junk`, which no shape means. -/
theorem fieldsFaithful_false_junk (K : RunCtx) (ρ : Assignment) (hΓ : boxD ∈ K.Γ)
    (hfl : K.D.flags [.other, .other] (.place (.var 0)) = (false, false)) : ¬ FieldsFaithful K ρ := by
  intro h
  let T := junk K.dm boxD (fun _ => .none)
  obtain ⟨r, s', hrun, heq⟩ := h boxD hΓ [.ty T] 0 0 [] (.place (.var 0))
    (fun j hj => .inr ⟨T, by simp at hj; subst hj; rfl⟩) (fun i hi => absurd hi (Nat.not_lt_zero _)) rfl rfl
  rw [teleFrame_box] at hrun
  obtain ⟨s'', hrd⟩ := readPlace_move K noFuture
    [faithBind (K.dm.fieldTy boxD [.ty T] 0 0 []) .moved, faithBind (K.dm.paramTy boxD 0 []) (.ty T)] 0
    (faithBind (K.dm.paramTy boxD 0 []) (.ty T)) (by simp) rfl (whole_ty T)
  have hcp : ∀ b : Bool, ∃ s₀, readPlace K noFuture (.var 0) b
      (stateOf 0 [faithBind (K.dm.fieldTy boxD [.ty T] 0 0 []) .moved, faithBind (K.dm.paramTy boxD 0 []) (.ty T)]) =
      some ((.ty T, { (faithBind (K.dm.paramTy boxD 0 []) (.ty T)).ty with label := none }), s₀) := by
    intro b
    cases b
    · exact ⟨s'', hrd⟩
    · exact ⟨_, readPlace_frame_copy K noFuture _ 0 (faithBind (K.dm.paramTy boxD 0 []) (.ty T))
        (by simp) rfl (whole_ty T)⟩
  change SM.erasedAt (K.D.flags [.other, .other] (.place (.var 0))) _ _ _ = _ at hrun
  rw [hfl, erasedAt_none] at hrun
  revert hrun
  generalize K.D.copy _ = b
  intro hrun
  obtain ⟨s₀, h₀⟩ := hcp b
  rw [h₀] at hrun
  cases hrun
  exact shapeTy_ne_junk K.dm _ boxD (fun _ => .none) heq.symm

/-- **Counterexample 2: a parameter list of the wrong length.** At `ps = []` the field type `A`
(`var 0`) is the field `x` itself, bound `⊥`, so the run is undefined, and `FieldsFaithful` asks it
defined. -/
theorem fieldsFaithful_false_short (K : RunCtx) (ρ : Assignment) (hΓ : boxD ∈ K.Γ)
    (hfl : K.D.flags [.other] (.place (.var 0)) = (false, false)) : ¬ FieldsFaithful K ρ := by
  intro h
  obtain ⟨r, s', hrun, -⟩ := h boxD hΓ [] 0 0 [] (.place (.var 0))
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _)) rfl rfl
  rw [teleFrame_box_short] at hrun
  change SM.erasedAt (K.D.flags [.other] (.place (.var 0))) _ _ _ = _ at hrun
  rw [hfl, erasedAt_none, readPlace_notWhole K noFuture _ 0 _ _ (by simp) rfl (by simp [faithBind, Sem.whole])] at hrun
  cases hrun

/-- The checker's decisions read a variable of `teleFrame` as data, not a proof or a statement. -/
theorem checker_flags (st : MState) :
    (checkerDecisions st 2000000).flags [.other, .other] (.place (.var 0)) = (false, false) := rfl

theorem checker_flags_short (st : MState) :
    (checkerDecisions st 2000000).flags [.other] (.place (.var 0)) = (false, false) := rfl

/-! ## Counterexample 3: `teleFrame` binds the parameters at `other`, the checker at their readings

`DL (A : Type) := MkDL(e : Eq(Nat, (let x = A; let y = A; 0), 0))` is accepted (and `MkDL[Nat](refl)`
with it, `DataModel/Exists/Probes.lean`): the checker's `fieldTele` binds `A` at its declared
reading (`Type`, a copy reading), so the two reads copy it. `teleFrame` binds every parameter at
`other`, which reads by MOVE, so the second read finds `⊥` and the run is undefined, at every
parameter. So the run `FieldsFaithful` speaks of is not the run of the checker's frame. -/

/-- `DL`, as the checker records it (the fields `var 1 …` after the parameter `var 0`). -/
def dlD : IndDecl :=
  { name := "DL", params := [(⟨"A"⟩, .sort 1)],
    ctors := [("MkDL", [("e", .eq .nat (.letIn ⟨"x"⟩ (.place (.var 0)) (.letIn ⟨"y"⟩ (.place (.var 1)) .zero)) .zero)])] }

/-- A variable of a one-frame state read by MOVE, with the state it leaves (the variable `⊥`). -/
theorem readPlace_move_eq (K : RunCtx) (φ : Future) (bs : List SBinding) (i : Nat) (b : SBinding)
    (hi : i < bs.length) (hb : bs[bs.length - 1 - i]? = some b) (hw : (b.val φ).whole) :
    readPlace K φ (.var i) false (stateOf 0 bs) = some ((b.val φ, { b.ty with label := none }),
      stateOf 0 (bs.modify (bs.length - 1 - i) fun b => { b with val := fun _ => .moved })) := by
  have hr : resolve (stateOf 0 bs) (.var i) = some (.bind 0 (bs.length - 1 - i), []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, stateOf, hi]
  have hcf : (stateOf 0 bs).typedFuture φ = φ := by funext l; simp [SState.typedFuture, liveLabels_stateOf]
  simp only [readPlace, contentOf, hr, access_stateOf, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, stateOf, hb, hw, setContent, updAt_nil, SState.setAt]

theorem teleFrame_dl (dm : DataModel) (T : TyM) :
    teleFrame dm dlD [.ty T] 0 [] = stateOf 0 [faithBind (dm.fieldTy dlD [.ty T] 0 0 []) .moved,
      faithBind (dm.paramTy dlD 0 []) (.ty T)] := rfl

/-- **Counterexample 3**: at decisions that read the frame's variables as data and by move (the
checker's at `other`, `checker_flags_dl`), the run of `DL`'s field type in `teleFrame` is undefined
at every type parameter, though the checker computes it. -/
theorem run_dl_undefined (K : RunCtx) (ρ : Assignment) (T : TyM)
    (h1 : K.D.flags [.other, .other] (.letIn ⟨"x"⟩ (.place (.var 0)) (.letIn ⟨"y"⟩ (.place (.var 1)) .zero)) = (false, false))
    (h2 : K.D.flags [.other, .other] (.place (.var 0)) = (false, false))
    (h3 : K.D.copy (K.D.placeDecl [.other, .other] (.var 0)) = false)
    (h4 : K.D.flags [K.D.declOf [.other, .other] (.place (.var 0)), .other, .other]
      (.letIn ⟨"y"⟩ (.place (.var 1)) .zero) = (false, false))
    (h5 : K.D.flags [K.D.declOf [.other, .other] (.place (.var 0)), .other, .other] (.place (.var 1)) = (false, false)) :
    run K ρ noFuture (.plain (TyM.univ 1)) (.eq .nat (.letIn ⟨"x"⟩ (.place (.var 0)) (.letIn ⟨"y"⟩ (.place (.var 1)) .zero)) .zero)
      (teleFrame K.dm dlD [.ty T] 0 []) = none := by
  rw [teleFrame_dl]
  generalize hb₁ : faithBind (K.dm.fieldTy dlD [.ty T] 0 0 []) .moved = b₁
  generalize hb₂ : faithBind (K.dm.paramTy dlD 0 []) (.ty T) = b₂
  have hd₁ : b₁.decl = .other := by rw [← hb₁]; rfl
  have hd₂ : b₂.decl = .other := by rw [← hb₂]; rfl
  have hv₂ : b₂.val noFuture = .ty T := by rw [← hb₂]; rfl
  have hl₂ : b₂.ty.label = none := by rw [← hb₂]; rfl
  have hsc : scopeOf (stateOf 0 [b₁, b₂]) = [.other, .other] := by simp [scopeOf, stateOf, hd₁, hd₂]
  have hrd := readPlace_move_eq K noFuture [b₁, b₂] 0 b₂ (by simp) rfl (by rw [hv₂]; exact whole_ty T)
  simp only [List.length_cons, List.length_nil] at hrd
  have hread : runT K ρ noFuture false (.plain TyM.err) (.place (.var 0)) (stateOf 0 [b₁, b₂]) =
      some ((.ty T, { m := b₂.ty.m }), stateOf 0 [b₁, { b₂ with val := fun _ => .moved }]) := by
    show SM.erasedAt (K.D.flags (scopeOf _) _) _ (readPlace K noFuture _ (K.D.copy (K.D.placeDecl (scopeOf _) _))) _ = _
    rw [hsc, h2, erasedAt_none, h3, hrd, hv₂]
    rfl
  have hlet : ∀ h, runT K ρ noFuture false h
      (.letIn ⟨"x"⟩ (.place (.var 0)) (.letIn ⟨"y"⟩ (.place (.var 1)) .zero)) (stateOf 0 [b₁, b₂]) = none := by
    intro h
    show SM.erasedIf (K.D.flags (scopeOf _) _) _ _ = none
    rw [hsc, h1]
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, bind, hread, Option.bind]
    let b₂' : SBinding := { b₂ with val := fun _ => .moved }
    let bx : SBinding := ⟨{ m := b₂.ty.m }, fun _ => .ty T, K.D.declOf (scopeOf (stateOf 0 [b₁, b₂'])) (.place (.var 0)), none⟩
    have hpush : pushBindShaped (stateOf 0 [b₁, b₂']) bx = stateOf 0 [b₁, b₂', bx] := by
      simp [pushBindShaped, bx, SState.pushBind, stateOf, SState.topIdx]
    have hsc' : scopeOf (stateOf 0 [b₁, b₂']) = [.other, .other] := by simp [scopeOf, stateOf, b₂', hd₁, hd₂]
    have hsc₃ : scopeOf (stateOf 0 [b₁, b₂', bx]) =
        [K.D.declOf [.other, .other] (.place (.var 0)), .other, .other] := by
      simp [scopeOf, stateOf, b₂', bx, hd₁, hd₂]
    have hinner : runT K ρ noFuture false h (.letIn ⟨"y"⟩ (.place (.var 1)) .zero) (stateOf 0 [b₁, b₂', bx]) = none := by
      show SM.erasedIf (K.D.flags (scopeOf _) _) _ _ = none
      rw [hsc₃, h4]
      simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, bind]
      have hr1 : runT K ρ noFuture false (.plain TyM.err) (.place (.var 1)) (stateOf 0 [b₁, b₂', bx]) = none := by
        show SM.erasedAt (K.D.flags (scopeOf _) _) _ (readPlace K noFuture _ (K.D.copy (K.D.placeDecl (scopeOf _) _))) _ = _
        rw [hsc₃, h5, erasedAt_none]
        exact readPlace_notWhole K noFuture _ 1 b₂' _ (by simp) rfl (by simp [b₂', Sem.whole])
      rw [hr1]; rfl
    show (runT K ρ noFuture false h (.letIn ⟨"y"⟩ (.place (.var 1)) .zero) (pushBindShaped (stateOf 0 [b₁, b₂']) bx)).bind _ = none
    rw [hpush, hinner]; rfl
  show SM.onCopy _ _ = none
  simp only [SM.onCopy, bind]
  have hnat : runT K ρ noFuture false (.plain TyM.err) .nat (stateOf 0 [b₁, b₂]) =
      some ((.ty TyM.nat, .plain (TyM.univ 1)), stateOf 0 [b₁, b₂]) := rfl
  rw [hnat]
  simp only [hlet, Option.map_none]

/-- The checker's decisions meet `run_dl_undefined`'s hypotheses (the frame's variables read as data,
by move, at `other`). -/
theorem checker_dl (st : MState) :
    let D := checkerDecisions st 2000000
    D.flags [.other, .other] (.letIn ⟨"x"⟩ (.place (.var 0)) (.letIn ⟨"y"⟩ (.place (.var 1)) .zero)) = (false, false) ∧
    D.flags [.other, .other] (.place (.var 0)) = (false, false) ∧
    D.copy (D.placeDecl [.other, .other] (.var 0)) = false ∧
    D.flags [D.declOf [.other, .other] (.place (.var 0)), .other, .other] (.letIn ⟨"y"⟩ (.place (.var 1)) .zero) = (false, false) ∧
    D.flags [D.declOf [.other, .other] (.place (.var 0)), .other, .other] (.place (.var 1)) = (false, false) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- So `FieldsFaithful` (which asks the run defined) fails at `DL` for every data model, under the
checker's decisions. -/
theorem fieldsFaithful_false_frame (K : RunCtx) (ρ : Assignment) (hΓ : dlD ∈ K.Γ) (st : MState)
    (hD : K.D = checkerDecisions st 2000000) : ¬ FieldsFaithful K ρ := by
  intro h
  obtain ⟨r, s', hrun, -⟩ := h dlD hΓ [.ty TyM.nat] 0 0 [] _
    (fun j hj => .inr ⟨TyM.nat, by simp at hj; subst hj; rfl⟩) (fun i hi => absurd hi (Nat.not_lt_zero _)) rfl rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := checker_dl st
  rw [← hD] at h1 h2 h3 h4 h5
  rw [run_dl_undefined K ρ TyM.nat h1 h2 h3 h4 h5] at hrun
  cases hrun

/-! ## The existence statement itself, at the program `[Box]` -/

/-- Whether the checker accepts `Box` from empty Σ and records exactly it (asserted natively
below: the kernel cannot evaluate `checkInd`). -/
def boxAccepted : Bool :=
  match (runMachine (checkItem (.ind boxD)) { globals := [], inds := [], cfg := {} } 2000000).1 with
  | .ok () st' => (st'.inds.map (·.name)) == ["Box"]
  | _ => false

#guard boxAccepted

/-- **`Assembly.exists_dataModel` is false** at the one-item program `[Box]` and fuel `2000000`,
given that the checker accepts `Box` from empty Σ and records it (`boxAccepted`, checked natively):
at the whole program, `DataFaithful` asks `CtxFaithful` at a state whose declarations are `[Box]`,
and both counterexamples refute its field part. -/
theorem exists_dataModel_false (st' : MState)
    (hacc : (runMachine (checkItem (.ind boxD)) { globals := [], inds := [], cfg := {} } 2000000).1 = .ok () st')
    (hinds : st'.inds = [boxD]) :
    ¬ ∃ dm : DataModel,
      (progMeaning dm (fun st => checkerDecisions st 2000000) (fun _ => .err) {} 2000000 [.ind boxD]).Covered dm ∧
      ∀ k, k ≤ [Item.ind boxD].length → Assembly.DataFaithful dm (fun st => checkerDecisions st 2000000)
        (progMeaning dm (fun st => checkerDecisions st 2000000) (fun _ => .err) {} 2000000 ([Item.ind boxD].take k)) := by
  rintro ⟨dm, -, hf⟩
  have h1 := hf 1 (Nat.le_refl _)
  rw [show [Item.ind boxD].take 1 = [Item.ind boxD] from rfl] at h1
  generalize hPdef : progMeaning dm (fun st => checkerDecisions st 2000000) (fun _ => .err) {} 2000000 [.ind boxD] = P at h1
  have hP : P.inds = [boxD] ∧ P.globals = st'.globals := by
    rw [← hPdef]
    simp only [progMeaning, progMeaningFrom, List.foldl_cons, List.foldl_nil, ProgState.step]
    rw [show ({ globals := ({} : ProgState).globals, inds := ({} : ProgState).inds, cfg := {} } : MState)
      = { globals := [], inds := [], cfg := {} } from rfl, hacc]
    exact ⟨hinds, rfl⟩
  have hc := h1 { globals := P.globals, inds := P.inds } (by rfl) (List.prefix_refl _)
  obtain ⟨hfields, -, -⟩ := hc (fun _ => .plain TyM.err) (fun _ => .err)
  refine fieldsFaithful_false_junk _ _ ?_ (checker_flags _) hfields
  show boxD ∈ P.inds
  rw [hP.1]; exact List.mem_singleton_self _

end Ochr.Meaning.DataModel.Exists.StatementCE
