import Ochr.Meaning.DataModel.Exists.KnotCE

/-!
# `truth_exists` as written is false: an earlier record that is not monotone (exists6)

`General.truth_exists` (piece 5: a `Prop`-sorted declaration's truth predicate and records whose field
types are the run's) assumes nothing of the earlier declarations' records. But a `Prop`-sorted `Q`
nested at a `Prop` parameter of an earlier `N` reads `N`'s membership at `Q`'s own proposition, and if
`N`'s records are anti-monotone there, no record of `Q` can be faithful: `Q` would be inhabited exactly
when it is not.

The declarations (accepted by the checker, asserted below; Lean accepts the same):
`N (P : Prop) : Prop := MkN(h : P)` and `Q : Prop := MkQ(h : N(Q))`. The model (`dmT`): `N`'s record at
`[P]` holds, at `h`'s key, the proposition leaf `¬P`. Then the run of `Q`'s field type `N(Q)` gives the
proposition "`N` at `Q`'s proposition is inhabited", that is `¬`(`Q` is inhabited); faithfulness makes
`Q`'s one field that proposition, so `Q` is inhabited exactly when it is not (`truthOld_false`).

What this shows: `truth_exists` needs the earlier records MONOTONE in their nestable `Prop` parameters
(what `mono_prop` gives one declaration from its records' shapes); with them the one-step operator is
monotone and its least fixed point is the truth predicate. The counterexample uses no truth predicate:
the contradiction comes from the faithfulness clause alone.
-/

namespace Ochr.Meaning.DataModel.Exists.TruthCE

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Ochr.Meaning.DataModel.Exists.RunLemmas
open Ochr.Meaning.DataModel.Exists.PreludeModel (hn sameDecl)

/-- `General.truth_exists` as written (kept here so its refutation is checked in the default build). -/
def TruthOld : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (d : IndDecl), d ∈ K.Γ → d.sort = 0 →
    (∀ P : ProgState, P.baseC = K.C → GlobalsTyped K.dm P) →
    ∃ (T : List Sem → Prop) (R : List Sem → Rec),
      (∀ ps, uTyR d (R ps) = TyM.prop (T ps)) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), FitsOneM uSig (uShape d (R ps) c j ((e.take j).map Sem.small)) e[j]) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d R } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d R) K.D d ps c e) = some (r, s') →
          r.1.asTy = shapeTyP (uShape d (R ps) c i (e.map Sem.small))

/-! ## The declarations, as the checker stores them -/

def nD : IndDecl :=
  { name := "N", params := [(hn "P", .sort 0)], sort := 0, ctors := [("MkN", [("h", .place (.var 0))])],
    nestable := [true] }
def qD : IndDecl := { name := "Q", sort := 0, ctors := [("MkQ", [("h", .tind "N" [.tind "Q" []])])] }

def tDecls : List IndDecl := [nD, qD]

open Ochr.Test in
ochr TruthCEA {
  inductive N (P : Prop) : Prop := MkN(h : P)
  inductive Q : Prop := MkQ(h : N(Q))
}

open Ochr.Test in
-- both declarations are accepted
#guard (Ochr.Test.run "TruthCEA" TruthCEA).rejectedWith []

def tItems : List Item :=
  (Prelude.decls ++ TruthCEA.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ TruthCEA.decls) d with
    | .ok it => some it
    | .error _ => none

-- after the library and the block, the checker's last two inductive declarations are `tDecls`
#guard let inds := (globalsAfter {} tItems).2
  inds.length == 6 && ((inds.drop 4).zip tDecls).all fun ab => sameDecl ab.1 ab.2

/-! ## The model -/

open Classical in
/-- `N`'s record at `[P]`: at `h`'s key, the leaf `¬P` (anti-monotone in `P`). -/
noncomputable def negRec (ps : List Sem) : Rec := fun q =>
  match ps with
  | [.ty (.t0 _ (.prop P))] => if q = kindKey 0 0 [] then .leaf (PLift (¬ P)) (.prop (¬ P)) else .none
  | _ => .none

open Classical in
noncomputable def dmT : DataModel where
  covers _ := True
  recOf d ps := if d = nD then negRec ps else fun _ => .none
  paramTy _ _ _ := TyM.univ 0

noncomputable def KT : RunCtx where
  dm := dmT
  Γ := tDecls
  C := KnotCE.cC
  D := Strict.Witness.Dw []

theorem nD_ne : nD ≠ qD := by
  intro h; have := congrArg IndDecl.name h; simp [nD, qD] at this

theorem hglob_T : ∀ P : ProgState, P.baseC = KT.C → GlobalsTyped KT.dm P := by
  intro P hP n g _ _ args s r s' hc
  rw [hP] at hc
  simp [KT, KnotCE.cC, callOf, TyS.plain, TyM.err] at hc

/-! ## The run of `Q`'s field type, at any record of `Q` -/

section
variable (R : List Sem → Rec)

noncomputable abbrev KQ : RunCtx := { KT with dm := setRec dmT qD R }

theorem uTyR_q (r : Rec) : uTyR qD r = TyM.prop (Nonempty (ucar qD r)) := by simp [uTyR, qD]
theorem uTyR_n (r : Rec) : uTyR nD r = TyM.prop (Nonempty (ucar nD r)) := by simp [uTyR, nD]

theorem run_Q (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) :
    runT (KQ R) ρ φ tl h (.tind "Q" []) s = some ((.ty (uTyR qD (R [])), .plain (TyM.univ 0)), s) := by
  have hf : (KQ R).Γ.find? (·.name == "Q") = some qD := rfl
  simp only [runT, hf, runParams, pure, bind]
  rw [if_pos (paramsOk_nil _ _)]
  simp only [DataModel.tyM, setRec_self, tyR_eq_uTyR]
  rfl

theorem run_NQ (ρ : Assignment) (s : SState) :
    run (KQ R) ρ noFuture (.plain (TyM.univ 1)) (.tind "N" [.tind "Q" []]) s =
      some ((.ty (uTyR nD (negRec [.ty (uTyR qD (R []))])), .plain (TyM.univ 0)), s) := by
  have hpo : paramsOk (setRec dmT qD R) nD [.ty (uTyR qD (R []))] := by
    intro i v hv
    match i, hv with
    | 0, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      rw [uTyR_q]
      exact ⟨ULift.up _, rfl⟩
  show runT (KQ R) ρ noFuture false _ _ s = _
  rw [runT]
  have hf : (KQ R).Γ.find? (·.name == "N") = some nD := rfl
  simp only [hf, runParams, pure, bind, SM.onCopy, run_Q, Option.map_some]
  rw [if_pos hpo]
  simp only [DataModel.tyM, setRec_other _ _ nD_ne, tyR_eq_uTyR]
  simp [dmT]
  rfl

end

/-! ## The refutation -/

/-- A type's proposition, when it is one. -/
def propOf : TyM → Option Prop
  | .t0 _ (.prop P) => some P
  | _ => none

/-- A one-constructor, one-field declaration is inhabited exactly when its field's shape is fitted. -/
theorem nonempty_iff_fits (d : IndDecl) (r : Rec) (hc : d.ctors.length = 1) (har : arity d 0 = 1) :
    Nonempty (ucar d r) ↔ ∃ f, FitsOneM uSig (uShape d r 0 0 []) f := by
  constructor
  · rintro ⟨x⟩
    have hm : DataLib.Mem uSig d r (DataLib.meanC uSig x) := (DataLib.mem_iff_meanC uSig d r _).2 ⟨x, rfl⟩
    obtain ⟨c, fs, -, hf⟩ := (DataLib.mem_iff uSig d r _).1 hm
    obtain ⟨c, hcl⟩ := c
    obtain rfl : c = 0 := by omega
    simp only [har] at hf
    obtain ⟨f, fs', -, h1, -⟩ := hf
    exact ⟨f, h1⟩
  · rintro ⟨f, hf⟩
    have hm : DataLib.Mem uSig d r (.dat d.name r 0 [f]) :=
      (DataLib.mem_iff uSig d r _).2 ⟨⟨0, by omega⟩, [f], rfl, by simp only [har]; exact ⟨f, [], rfl, hf, rfl⟩⟩
    obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig d r _).1 hm
    exact ⟨x⟩

/-- **A shape whose type is a proposition is fitted exactly when the proposition holds.** -/
theorem fits_iff_of_prop {sh : Shape} {X : Prop} (h : shapeTyP sh = TyM.prop X) :
    (∃ f, FitsOneM uSig sh f) ↔ X := by
  have hp : propOf (shapeTyP sh) = some X := by rw [h]; rfl
  cases sh with
  | leaf B c =>
    cases c with
    | prop P =>
      simp only [shapeTyP, propOf, Option.some.injEq] at hp
      subst hp
      exact ⟨fun ⟨_, b, _⟩ => b.down, fun x => ⟨_, ⟨x⟩, rfl⟩⟩
    | _ => simp [shapeTyP, propOf] at hp
  | sub d r =>
    simp only [shapeTyP] at hp
    split at hp
    · simp [TyM.err, propOf] at hp
    · rename_i hs
      simp [uTyR, hs, propOf] at hp
  | prf d r =>
    simp only [shapeTyP] at hp
    split at hp
    · rename_i hs
      simp only [uTyR, hs, if_true, TyM.prop, propOf, Option.some.injEq] at hp
      subst hp
      constructor
      · rintro ⟨_, -, v, hv⟩
        obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig d r v).1 hv
        exact ⟨x⟩
      · rintro ⟨x⟩
        exact ⟨.proof, rfl, _, (DataLib.mem_iff_meanC uSig d r _).2 ⟨x, rfl⟩⟩
    · simp [TyM.err, propOf] at hp

/-- **`truth_exists` as written is false.** -/
theorem truthOld_false : ¬ TruthOld := by
  intro H
  obtain ⟨T, R, -, hag⟩ := H KT (fun _ => .err) qD (by simp [KT, tDecls]) rfl hglob_T
  have h := hag [] 0 0 [] (.tind "N" [.tind "Q" []]) _ _ rfl (by simp) (by simp) rfl rfl
    (run_NQ R (fun _ => .err) (teleFrame (setRec KT.dm qD R) KT.D qD [] 0 []))
  simp only [Sem.asTy, List.map_nil] at h
  have hX : Nonempty (ucar nD (negRec [.ty (uTyR qD (R []))])) ↔ ¬ Nonempty (ucar qD (R [])) := by
    rw [nonempty_iff_fits nD _ rfl rfl]
    have hsh : uShape nD (negRec [.ty (uTyR qD (R []))]) 0 0 [] =
        .leaf (PLift (¬ Nonempty (ucar qD (R [])))) (.prop (¬ Nonempty (ucar qD (R [])))) := by
      simp [uShape, negRec, uTyR_q, TyM.prop, projIdx_nil]
    rw [hsh]
    exact ⟨fun ⟨_, b, _⟩ => b.down, fun x => ⟨_, ⟨x⟩, rfl⟩⟩
  have hY : Nonempty (ucar qD (R [])) ↔ Nonempty (ucar nD (negRec [.ty (uTyR qD (R []))])) := by
    rw [nonempty_iff_fits qD _ rfl rfl]
    exact fits_iff_of_prop (by rw [← h, uTyR_n])
  exact iff_not_self (hY.trans hX)

end Ochr.Meaning.DataModel.Exists.TruthCE
