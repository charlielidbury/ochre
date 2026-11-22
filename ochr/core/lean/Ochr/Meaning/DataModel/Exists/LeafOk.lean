import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.RunLemmas

/-!
# `leafOk` of the knot's and the truth spec's records (exists10)

`RecordsFaithful.leafOk` asks a record at well-typed parameters never to hold, at a genuine field key,
a leaf whose code is a data code over the model's own carrier (`DataModel.LeafOk`). At a knot's
record the shape at a field key is the shape of the knot's own field type (`uShape_recK`), and that
shape is such a leaf only when the field type is the type value `rawTy P r` of a `Prop`-sorted
declaration `P` (a data-sorted declaration's code is read as a `.data` entry, `dataView`): the raw
code, which is the meaning of no type the checker has (`Code0.level`: it has no level).

The knot's field types are read off the field-type term, which the grammar (`Spine`, `PSpine`; a
fact about the checker, enforced, `grammar_of_checks`) restricts to `Nat`, `Unit`, a parameter, an
applied declaration, a call of a global, and an equation. An applied declaration gives a `.data`
field type (or, for the truth spec's own occurrence, a proposition). The others give the run's value,
and none of them can be the raw code:
* a parameter is a member of its type (well-typed parameters), and no member of any type is the raw
  code (`mem_notRaw`: a type value is a member only of a universe, whose elements have a level);
* a call's value is an encoding of an element of its codomain's carrier (`callOf_notRaw`);
* an equation's value is a proposition, `Nat`'s and `Unit`'s are their codes.

So `leafOk` holds at the knot's records and the truth spec's, at every key and at every list of
parameters that are not raw codes (`recLeafOk_knot`, `recLeafOk_truth`), with no assumption beyond
the grammar. This closes the hypothesis `hleaf` of `Records.recordsFaithful_canon` (docs/34 §18.14).
-/

namespace Ochr.Meaning.DataModel.Exists.LeafOk

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Ochr.Meaning.DataModel.Exists.RunLemmas

universe u

/-- **A type is not the raw data code of a `Prop`-sorted declaration** over the model's carrier. -/
def NotRawP (T : TyM) : Prop :=
  ∀ (P : IndDecl) (r : Rec), P.sort = 0 → T ≠ .t0 (ucar P r) (.data P r (ucar P r))

/-- A value is not the raw code as a type value. -/
def NotRawV (v : Sem) : Prop := ∀ X, v = .ty X → NotRawP X

theorem notRawP_of_dataCode {A : Type} (c : Code0 A) (h : c.dataCode? = none) : NotRawP (.t0 A c) := by
  intro P r _ e
  obtain ⟨hA, hh⟩ := TyM.t0_inj e
  have := Code0.congr_heq (fun c => c.dataCode?) _ _ hA hh
  rw [h] at this
  cases this

theorem notRawP_of_level {A : Type} (c : Code0 A) {l : Nat} (h : c.level = some l) : NotRawP (.t0 A c) := by
  intro P r hP e
  obtain ⟨hA, hh⟩ := TyM.t0_inj e
  have := Code0.congr_heq (fun c => c.level) _ _ hA hh
  rw [h] at this
  simp [Code0.level, hP] at this

theorem notRawP_t1 {A : Type 1} (c : Code1 A) : NotRawP (.t1 A c) := fun _ _ _ e => by cases e

theorem notRawP_err : NotRawP TyM.err := notRawP_of_dataCode _ rfl

theorem notRawP_prop (P : Prop) : NotRawP (TyM.prop P) := notRawP_of_dataCode _ rfl

theorem notRawP_asTy {v : Sem} (h : NotRawV v) : NotRawP v.asTy := by
  cases v with
  | ty X => exact h X rfl
  | _ => exact notRawP_err

/-! ## No member of a type is the raw code -/

theorem read_ne_ty (dm : DataModel) (d : IndDecl) (r : Rec) (A : Type) (a : A) (X : TyM) :
    dm.read.read d r A a ≠ .ty X := by
  show dm.readFn d r A a ≠ .ty X
  unfold DataModel.readFn
  split
  · intro h
    have hm : dm.Mem d r (.ty X) := (DataModel.mem_iff_meanC dm d r _).2 ⟨_, h⟩
    obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
    cases he
  · intro h; cases h

/-- A level-0 element never encodes as a type value. -/
theorem enc0_ne_ty (dm : DataModel) : ∀ {A : Type} (c : Code0 A) (a : A) (X : TyM), c.enc dm.read a ≠ .ty X
  | _, .prop _, _, _ => fun h => by cases h
  | _, .nat, _, _ => fun h => by cases h
  | _, .unit, _, _ => fun h => by cases h
  | _, .data d r A, a, X => read_ne_ty dm d r A a X
  | _, .pi .., _, _ => fun h => by cases h
  | _, .err, a, _ => nomatch a

theorem enc1_notRaw (dm : DataModel) : ∀ {A : Type 1} (c : Code1 A) (a : A), NotRawV (c.enc dm.read a)
  | _, .lift _ c, a, X, h => absurd h (enc0_ne_ty dm c a.down X)
  | _, .univ0, P, X, h => by cases h; exact notRawP_prop _
  | _, .univ1, p, X, h => by cases h; exact notRawP_of_level _ p.2.2
  | _, .pi .., _, _, h => by cases h

theorem enc2_notRaw (dm : DataModel) : ∀ {A : Type 2} (c : Code2 A) (a : A), NotRawV (c.enc dm.read a)
  | _, .lift _ c, a, X, h => enc1_notRaw dm c a.down X h
  | _, .univ2, _, X, h => by cases h; exact notRawP_t1 _
  | _, .pi .., _, _, h => by cases h

/-- **No member of a type is the raw code.** -/
theorem mem_notRaw (dm : DataModel) {v : Sem} {T : TyM} (h : v ∈ₛ[dm.read] T) : NotRawV v := by
  intro X hv
  subst hv
  cases T with
  | t0 A c => obtain ⟨a, ha⟩ := h; exact absurd ha (enc0_ne_ty dm c a X)
  | t1 A c => obtain ⟨a, ha⟩ := h; exact enc1_notRaw dm c a X ha
  | t2 A c => obtain ⟨a, ha⟩ := h; exact enc2_notRaw dm c a X ha

/-! ## A call's value is an encoding -/

theorem applyTelL_enc (L : Lvl.{u}) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (readFin : Fin → List Sem) (F : C) (args : List Sem)
      {r : Sem} {T : TyM} {fins : List Sem}, applyTelL L t readFin F args = some (.data r T fins) →
      ∃ (B : Type u) (c : L.Code B) (x : B), r = L.enc c x
  | _, _, .dat _ _ c, _, F, [], _, _, _, h => by
    simp only [applyTelL, Option.some.injEq, AppResultL.data.injEq] at h
    exact ⟨_, c, F.1, h.1.symm⟩
  | _, _, .ref .., _, _, [], _, _, _, h => by simp [applyTelL] at h
  | _, _, .param _ _ _ c _ k, _, F, a :: as, _, _, _, h => by
    simp only [applyTelL] at h
    cases hx : L.dec c a with
    | none => rw [hx] at h; cases h
    | some x => rw [hx] at h; exact applyTelL_enc L (k x) _ (F x) as h
  | _, _, .dat .., _, _, _ :: _, _, _, _, h => by simp [applyTelL] at h
  | _, _, .ref .., _, _, _ :: _, _, _, _, h => by simp [applyTelL] at h
  | _, _, .param .., _, _, [], _, _, _, h => by simp [applyTelL] at h

theorem callOfL_enc (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args : List Res) (s : SState)
    {r : Res} {s' : SState} (h : callOfL L t fv args s = some (r, s')) :
    ∃ (B : Type u) (c : L.Code B) (x : B), r.1 = L.enc c x := by
  unfold callOfL at h
  dsimp only at h
  split at h
  · rename_i r0 T finals happ
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    unfold applyFnL at happ
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.1 happ
    exact applyTelL_enc L t _ F _ hF
  · rename_i U c fwd back happ
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact ⟨U, c, fwd, rfl⟩
  · cases h

/-- **A call's value is not the raw code.** -/
theorem callOf_notRaw (dm : DataModel) (fv : Res) (args : List Res) (s : SState) {r : Res} {s' : SState}
    (h : callOf dm.read fv args s = some (r, s')) : NotRawV r.1 := by
  intro X hX
  unfold callOf at h
  split at h
  · obtain ⟨B, c, x, e⟩ := callOfL_enc _ _ _ _ _ h
    rw [e] at hX; exact absurd hX (enc0_ne_ty dm c x X)
  · obtain ⟨B, c, x, e⟩ := callOfL_enc _ _ _ _ _ h
    rw [e] at hX; exact enc1_notRaw dm c x X hX
  · obtain ⟨B, c, x, e⟩ := callOfL_enc _ _ _ _ _ h
    rw [e] at hX; exact enc2_notRaw dm c x X hX
  · cases h

/-! ## The run's value at a steady node of the grammar -/

section
variable (K : RunCtx) (ρ : Assignment) (s : SState) (h : TyS)

theorem valOf_of {t : Term} (H : ∀ r s', runT K ρ noFuture false h t s = some (r, s') → NotRawV r.1) :
    NotRawP (valOf K ρ s h t).asTy := by
  unfold valOf
  cases e : runT K ρ noFuture false h t s with
  | none => exact notRawP_err
  | some p => exact notRawP_asTy (H p.1 p.2 e)

theorem valOf_nat : NotRawP (valOf K ρ s h .nat).asTy :=
  valOf_of K ρ s h fun r s' e => by
    rw [runT_nat] at e; cases e; intro X hX; cases hX; exact notRawP_of_dataCode _ rfl

theorem valOf_unit : NotRawP (valOf K ρ s h .unit).asTy :=
  valOf_of K ρ s h fun r s' e => by
    simp only [runT, pure, Option.some.injEq] at e; cases e; intro X hX; cases hX; exact notRawP_of_dataCode _ rfl

theorem valOf_eq (A a b : Term) : NotRawP (valOf K ρ s h (.eq A a b)).asTy :=
  valOf_of K ρ s h fun r s' e => by
    obtain ⟨_, va, vb, _, _, _, _, _, hr, _⟩ := runT_eq K ρ noFuture false h A a b s e
    intro X hX; rw [hr] at hX; cases hX; exact notRawP_prop _

theorem valOf_call (g : String) (as : List Term) (hd : Bool) :
    NotRawP (valOf K ρ s h (.call (.const g) as hd)).asTy :=
  valOf_of K ρ s h fun r s' e => by
    obtain ⟨_, _, r', _, _, hc, hv⟩ := runT_call_const K ρ noFuture false h g as hd s e
    rw [hv]; exact callOf_notRaw K.dm _ _ _ hc

end

/-! ## The knot's and the truth spec's field types -/

/-- A shape read off a field type that is not the raw code satisfies `LeafOk`. -/
theorem leafOk_shapeOf (dm : DataModel) (F : FTy) (h : ∀ T, F = .ty T → NotRawP T) : dm.LeafOk (shapeOf F) := by
  have herr : dm.LeafOk (.leaf PEmpty .err) := fun _ _ hc => by cases hc
  have hdat : ∀ M, F.kind = .data M → dm.LeafOk (shapeOf F) := by
    intro M hk
    simp only [shapeOf, hk]
    split
    · exact True.intro
    · exact True.intro
  cases F with
  | data M r => exact hdat M rfl
  | ty T =>
    rcases hv : dataView T with _ | ⟨M, r⟩
    · cases T with
      | t0 B c =>
        have hk : FTy.kind (.ty (.t0 B c)) = .leaf B c := by simp [FTy.kind, hv]
        simp only [shapeOf, hk]
        intro P r hc hB
        cases c with
        | data P' r' A =>
          simp only [Code0.dataCode?, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          rw [car_eq_ucar] at hB
          subst hB
          by_cases hs : P'.sort = 0
          · exact h _ rfl P' r' hs rfl
          · have e : TyM.t0 (ucar P' r') (Code0.data P' r' (ucar P' r')) = uTyR P' r' := by
              have hs' : (P'.sort == 0) = false := by simpa using hs
              simp [uTyR, hs']
            rw [e, dataView_uTyR P' r' hs] at hv; cases hv
        | _ => simp [Code0.dataCode?] at hc
      | t1 A c =>
        have hk : FTy.kind (.ty (.t1 A c)) = .none := by simp [FTy.kind, hv]
        simp only [shapeOf, hk]; exact herr
      | t2 A c =>
        have hk : FTy.kind (.ty (.t2 A c)) = .none := by simp [FTy.kind, hv]
        simp only [shapeOf, hk]; exact herr
    · exact hdat M (by simp [FTy.kind, hv])

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

/-- **The knot's field types are never the raw code**, at parameters that are not, whatever the key. -/
theorem ftyK_notRaw (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT) (R : List Sem → Rec)
    (ps : List Sem) (hps : ∀ v ∈ ps, NotRawV v) (c i : Nat) (es : List Small) :
    ∀ T, ftyK K ρ d R ps c i es = .ty T → NotRawP T := by
  intro T hT
  rw [ftyK_eq] at hT
  revert hT
  cases hFT : fieldTerm d c i with
  | none => intro hT; cases hT; exact notRawP_err
  | some FT =>
    simp only
    generalize canFrame K d ps c i es _ = s
    intro hT
    cases hspine c i FT hFT with
    | nat => rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semT_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hT; cases hT; exact valOf_nat K ρ s _
    | unit => rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semT_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hT; cases hT; exact valOf_unit K ρ s _
    | param v hv =>
      rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semT_var _ _ _ _ _ _ _ _ hv] at hT
      cases hT
      apply notRawP_asTy
      rw [List.getD_eq_getElem?_getD]
      cases e : ps[d.params.length - 1 - v]? with
      | none => intro X hX; cases hX
      | some w => exact hps w (List.mem_of_getElem? e)
    | tind n as M hM _ => rw [itpT_tind, hM] at hT; cases hT
    | call f as hd _ => rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semT_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hT; cases hT; exact valOf_call K ρ s _ f as hd
    | eq A a b _ => rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semT_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hT; cases hT; exact valOf_eq K ρ s _ A a b

/-- **The truth spec's field types are never the raw code**, at parameters that are not. -/
theorem ftyP_notRaw (hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT) (T : List Sem → Prop)
    (ps : List Sem) (hps : ∀ v ∈ ps, NotRawV v) (c i : Nat) (es : List Small) :
    ∀ X, ftyP K ρ d T ps c i es = .ty X → NotRawP X := by
  intro X hX
  rw [ftyP_eq] at hX
  revert hX
  cases hFT : fieldTerm d c i with
  | none => intro hX; cases hX; exact notRawP_err
  | some FT =>
    simp only
    generalize canFrame K d ps c i es _ = s
    intro hX
    cases hspine c i FT hFT with
    | nat => rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semP_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hX; cases hX; exact valOf_nat K ρ s _
    | unit => rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semP_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hX; cases hX; exact valOf_unit K ρ s _
    | param v hv =>
      rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semP_var _ _ _ _ _ _ _ _ hv] at hX
      cases hX
      apply notRawP_asTy
      rw [List.getD_eq_getElem?_getD]
      cases e : ps[d.params.length - 1 - v]? with
      | none => intro Y hY; cases hY
      | some w => exact hps w (List.mem_of_getElem? e)
    | tind n as M hM _ =>
      rw [itpP_tind, hM] at hX
      simp only at hX
      split at hX
      · cases hX; exact notRawP_prop _
      · cases hX
    | call f as hd _ => rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semP_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hX; cases hX; exact valOf_call K ρ s _ f as hd
    | eq A a b _ => rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), semP_other _ _ _ _ _ _ _ _
        (fun _ _ e => by cases e) (fun _ e => by cases e)] at hX; cases hX; exact valOf_eq K ρ s _ A a b

end

/-- **`leafOk` at a knot spec's record**, from its field types never being the raw code. -/
theorem recLeafOk_of (dm : DataModel) (S : KnotSpec) (d : IndDecl) (ps : List Sem)
    (h : ∀ c i es T, S.fty (recK S) ps c i es = .ty T → NotRawP T) : dm.RecLeafOk d (recK S ps) := by
  intro c i e _ _ he
  show dm.LeafOk (uShape d (recK S ps) c i e)
  rw [uShape_recK S d ps c i e he]
  exact leafOk_shapeOf dm _ (h c i _)

/-- Well-typed parameters are not raw codes. -/
theorem params_notRaw {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : ParamsTyped dm d ps) :
    ∀ v ∈ ps, NotRawV v := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  exact mem_notRaw dm (h j hj)

end Ochr.Meaning.DataModel.Exists.LeafOk
