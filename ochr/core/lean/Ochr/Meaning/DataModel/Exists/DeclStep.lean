import Ochr.Meaning.DataModel.Exists.Params
import Ochr.Meaning.DataModel.Exists.Knot.Exists
import Ochr.Meaning.DataModel.Exists.Knot.CongrN

/-!
# A new declaration is faithful: the step's core (exists10)

The assembly's step at an accepted data-sorted declaration `d` builds, at a build context `K1` (the
stage's model with `d`'s parameter types set to `Params.pty`), the knot's records (`knotK`) and makes
the model's records `Records.recCanon`. Here: `d` is then faithful (`DeclFaithful`) at EVERY context
`K` whose runs of `d`'s field types and parameter types are those of the build context (`htr`, the
transfer; the assembly proves it by the run's congruences), at the model's records and parameter
types at `d`.

* fields (`fieldsFaithful_knot`): `knotK_agree` at the knot's context gives the run's reading as the
  knot's field type's meaning; the model's field type is the shape type of the knot's field type's
  shape (`uShape_recK`); the two agree when the field type is of carrier level 0 (`shapeTyP_uShape`).
  That last condition is a fact about the checker, `hlev`: it rejects a field whose type is not in
  `Prop` or `Type` ("its type must be in Prop or Type", `sortOf` at generic values, Check.lean), and at
  a `Type₁`-valued field the model's field type (always a level-0 code) could not be the run's reading;
* parameter types (`paramsFaithful_pty`): `Params.pty_faithful`;
* records (`Records.recordsFaithful_canon`).
-/

namespace Ochr.Meaning.DataModel.Exists.DeclStep

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Ochr.Meaning.DataModel.Exists.Records Ochr.Meaning.DataModel.Exists.Params

theorem read_eq (dm dm' : DataModel) : dm.read = dm'.read := rfl

/-- A field type reads the model only through the declaration's record at the parameters. -/
theorem fieldTy_congr {dm dm' : DataModel} {d : IndDecl} {ps : List Sem} (h : dm.recOf d ps = dm'.recOf d ps)
    (c i : Nat) (e : List Sem) : dm.fieldTy d ps c i e = dm'.fieldTy d ps c i e := by
  unfold DataModel.fieldTy DataModel.fieldTyR
  rw [h, shapeTy_eq_shapeTyP, shapeTy_eq_shapeTyP]

theorem fieldsTyped_congr {dm dm' : DataModel} {d : IndDecl} {ps : List Sem} (h : dm.recOf d ps = dm'.recOf d ps)
    {c : Nat} {e : List Sem} (he : FieldsTyped dm d ps c e) : FieldsTyped dm' d ps c e := fun i hi => by
  have := he i hi
  rwa [fieldTy_congr h] at this

theorem paramsTyped_congr {dm dm' : DataModel} {d : IndDecl} (h : dm.paramTy d = dm'.paramTy d)
    {ps : List Sem} (hp : ParamsTyped dm d ps) : ParamsTyped dm' d ps := fun j hj => by
  have := hp j hj
  rwa [h] at this

/-- What `knot_exists` and `truth_exists` conclude of a spec `S` at the build context `K1`: at the
knot's context, the run's reading of a field type at members is the spec's field type's meaning. -/
def SpecAgree (K1 : RunCtx) (ρ0 : Assignment) (d : IndDecl) (S : KnotSpec) : Prop :=
  ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
    ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K1.dm.read] K1.dm.paramTy d j (ps.take j)) →
    (∀ j (hj : j < e.length), e[j] ∈ₛ[K1.dm.read] (setRec K1.dm d (recK S)).fieldTy d ps c j (e.take j)) →
    e.length = i → fieldTerm d c i = some FT →
    run { K1 with dm := setRec K1.dm d (recK S) } ρ0 noFuture (.plain (TyM.univ 1)) FT
      (teleFrame (setRec K1.dm d (recK S)) K1.D d ps c e) = some (r, s') →
      r.1.asTy = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean

/-- **`d`'s fields are faithful** at any context running `d`'s field types as the spec's context does
(`htr`), whose records at `d` are the spec's at well-typed parameters and whose parameter types at `d`
are the build context's. Assumes, besides the spec's agreement: `hlev` (the run of a field type at
members is a code of carrier level 0: the checker's field-level check). -/
theorem fieldsFaithful_spec (K1 : RunCtx) (ρ0 : Assignment) (d : IndDecl) (S : KnotSpec)
    (hagree : SpecAgree K1 ρ0 d S) (K : RunCtx) (ρ : Assignment)
    (hrec : ∀ ps, ParamsTyped K.dm d ps → K.dm.recOf d ps = recK S ps)
    (hpt : K.dm.paramTy d = K1.dm.paramTy d)
    (htr : ∀ ps c i e FT, ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e →
      e.length = i → fieldTerm d c i = some FT →
      run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) =
        run { K1 with dm := setRec K1.dm d (recK S) } ρ0 noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K1.dm d (recK S)) K1.D d ps c e))
    (hlev : ∀ ps c i e FT r s', ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e →
      e.length = i → fieldTerm d c i = some FT →
      run { K1 with dm := setRec K1.dm d (recK S) } ρ0 noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K1.dm d (recK S)) K1.D d ps c e) = some (r, s') →
        ∃ (B : Type) (cd : Code0 B), r.1.asTy = .t0 B cd) :
    FieldsFaithfulAt K ρ d := by
  intro ps c i e FT hl hps he hei hFT r s' hr
  rw [htr ps c i e FT hl hps he hei hFT] at hr
  obtain ⟨B, cd, hB⟩ := hlev ps c i e FT r s' hl hps he hei hFT hr
  have hR := hrec ps hps
  have hag := hagree ps c i e FT r s' hl (fun j hj => by have := hps j hj; rwa [hpt] at this)
    (fun j hj => by
      have := he j hj
      rwa [fieldTy_congr (dm' := setRec K1.dm d (recK S)) (by rw [setRec_self]; exact hR)] at this)
    hei hFT hr
  rw [hag]
  have hk := recK_kind S ps c i (projIdx d c (e.map Sem.small)) (by rw [projIdx_len]; simp [hei])
  have hc := recK_contRec S ps c i (projIdx d c (e.map Sem.small)) (by rw [projIdx_len]; simp [hei])
  have hLvl : (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).Lvl0 := by
    rw [hag] at hB
    revert hB
    cases S.fty (recK S) ps c i (projIdx d c (e.map Sem.small)) with
    | data M r => intro _; trivial
    | ty T => intro hB; exact ⟨B, cd, hB⟩
  show _ = K.dm.fieldTyR d (K.dm.recOf d ps) c i e
  unfold DataModel.fieldTyR
  rw [hR, shapeTy_eq_shapeTyP]
  exact (shapeTyP_uShape d (recK S ps) c i (e.map Sem.small) _ hLvl hk hc).symm

/-- **`d`'s parameter types are faithful** at any context running `d`'s parameter types as the build
context `K0` does, whose parameter types at `d` are `Params.pty`. Assumes `DecLocal` and label-free
globals at `K0` (`pty_faithful`'s). -/
theorem paramsFaithful_pty (K0 : RunCtx) (ρ0 : Assignment) (d : IndDecl)
    (hK0 : ∀ g, (K0.C.global g).2.label = none) (hD0 : FrameLocal.DecLocal K0.D)
    (K : RunCtx) (ρ : Assignment) (hpt : K.dm.paramTy d = pty K0 ρ0 d)
    (htr : ∀ ps j hn PT, ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
      run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm K.D d ps) =
        run K0 ρ0 noFuture (.plain (TyM.univ 2)) PT (frameP d (pty K0 ρ0 d) K0.D false ps)) :
    ParamsFaithfulAt K ρ d := by
  intro ps j hn PT hps hl hj r s' hr
  rw [htr ps j hn PT hps hl hj] at hr
  rw [hpt]
  exact pty_faithful K0 ρ0 d hK0 hD0 ps j hn PT (fun u hu => by have := hps u hu; rwa [hpt] at this) hl hj r s' hr

end Ochr.Meaning.DataModel.Exists.DeclStep

/-! ## The transfer: a context extending the stage runs `d`'s declared types as the build context does -/

namespace Ochr.Meaning.DataModel.Exists.DeclStep

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Ochr.Meaning.DataModel.Exists.Params

theorem ctx_ext {K K' : RunCtx} (h1 : K.dm = K'.dm) (h2 : K.Γ = K'.Γ) (h3 : K.C = K'.C) (h4 : K.D = K'.D)
    (h5 : K.Δ = K'.Δ) (h6 : K.Λ = K'.Λ) (h7 : K.cur = K'.cur) : K = K' := by
  cases K; cases K'; simp_all

theorem teleFrame_congr {dm dm' : DataModel} {d : IndDecl} {ps : List Sem} (h1 : dm.recOf d ps = dm'.recOf d ps)
    (h2 : dm.paramTy d = dm'.paramTy d) (D : Decisions) (c : Nat) (e : List Sem) :
    teleFrame dm D d ps c e = teleFrame dm' D d ps c e := by
  unfold teleFrame
  simp only [fieldTy_congr h1, h2]

theorem noAbs {t : Term} (h : t.anyAtom (fun _ => true) = false) (K : RunCtx) (Δ' : Nat → TyS) (ρ ρ' : Assignment) :
    ∀ σ, t.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ := fun σ hσ => by
  have := Term.anyAtom_mono (P := (· == .abs σ)) (Q := fun _ => true) (fun _ _ => rfl) t hσ
  rw [h] at this; cases this

/-- **The transfer of a field type's run**: from a context `K` at the decisions of a state `st`, to a
context `Kb` at the decisions of `st'`, the same declaration list, Λ and definition, whose model and
globals agree with `K`'s at the names the field type mentions (`AgreeN`), and whose records and
parameter types at `d` agree with `K`'s at `ps`. The decisions move by `hDS` (piece 8, `DecStable`);
Δ and the assignment are not read (no embedded value). -/
theorem field_transfer {D : MState → Decisions} {st st' : MState} {d : IndDecl} {c i : Nat} {FT : Term}
    (hDS : ∀ (K : RunCtx) (ρ : Assignment) (ps e : List Sem),
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st) d ps c e) =
        run { K with D := D st' } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st') d ps c e))
    (K Kb : RunCtx) (hKD : K.D = D st) (hKbD : Kb.D = D st') (hΓ : K.Γ = Kb.Γ) (hΛ : K.Λ = Kb.Λ) (hcur : K.cur = Kb.cur)
    (N : NameOk) (hA : AgreeN { K with Δ := Kb.Δ, D := D st' } Kb.dm Kb.C N)
    (hnv : FT.anyAtom (fun _ => true) = false) (hnok : Term.nok N FT = true)
    (ρ ρb : Assignment) (ps e : List Sem) (hrec : K.dm.recOf d ps = Kb.dm.recOf d ps)
    (hpt : K.dm.paramTy d = Kb.dm.paramTy d) :
    run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) =
      run Kb ρb noFuture (.plain (TyM.univ 1)) FT (teleFrame Kb.dm Kb.D d ps c e) := by
  rw [run_congrA K Kb.Δ ρ ρb noFuture FT _ _ (noAbs hnv K Kb.Δ ρ ρb)]
  have e1 : KA K Kb.Δ = { KA K Kb.Δ with D := D st } := by
    apply ctx_ext <;> simp [hKD]
  rw [e1, hKD, hDS (KA K Kb.Δ) ρb ps e]
  rw [run_congrN _ Kb.dm Kb.C N ρb noFuture hA FT _ _ hnok]
  rw [teleFrame_congr hrec hpt, hKbD]
  congr 1
  apply ctx_ext <;> simp [hΓ, hKbD, hΛ, hcur]

/-- **The transfer of a parameter type's run**, the same way (`DecStable`'s second part). -/
theorem param_transfer {D : MState → Decisions} {st st' : MState} {d : IndDecl} {j : Nat} {PT : Term}
    (hPT : paramTerm d j = PT)
    (hDS : ∀ (K : RunCtx) (ρ : Assignment) (ps : List Sem) (mask : Bool),
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 2)) (paramTerm d j) (frameP d (K.dm.paramTy d) (D st) mask ps) =
        run { K with D := D st' } ρ noFuture (.plain (TyM.univ 2)) (paramTerm d j) (frameP d (K.dm.paramTy d) (D st') mask ps))
    (K Kb : RunCtx) (hKD : K.D = D st) (hKbD : Kb.D = D st') (hΓ : K.Γ = Kb.Γ) (hΛ : K.Λ = Kb.Λ) (hcur : K.cur = Kb.cur)
    (N : NameOk) (hA : AgreeN { K with Δ := Kb.Δ, D := D st' } Kb.dm Kb.C N)
    (hnv : PT.anyAtom (fun _ => true) = false) (hnok : Term.nok N PT = true)
    (ρ ρb : Assignment) (ps : List Sem) (P : Nat → List Sem → TyM) (hpt : K.dm.paramTy d = P) :
    run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm K.D d ps) =
      run Kb ρb noFuture (.plain (TyM.univ 2)) PT (frameP d P Kb.D false ps) := by
  rw [paramFrame_eq, run_congrA K Kb.Δ ρ ρb noFuture PT _ _ (noAbs hnv K Kb.Δ ρ ρb)]
  have e1 : KA K Kb.Δ = { KA K Kb.Δ with D := D st } := by
    apply ctx_ext <;> simp [hKD]
  rw [e1, hKD, ← hPT, hDS (KA K Kb.Δ) ρb ps false, hPT]
  rw [run_congrN _ Kb.dm Kb.C N ρb noFuture hA PT _ _ hnok]
  rw [hKbD]
  have e2 : (KA K Kb.Δ).dm.paramTy d = P := hpt
  rw [e2]
  congr 1
  apply ctx_ext <;> simp [hΓ, hKbD, hΛ, hcur]

end Ochr.Meaning.DataModel.Exists.DeclStep
