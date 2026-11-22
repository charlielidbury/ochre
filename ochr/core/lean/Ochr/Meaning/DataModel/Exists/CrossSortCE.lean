import Ochr.Meaning.DataModel.Exists.PreludeModel
import Ochr.Meaning.DataModel.Exists.Knot.Agree
import Ochr.Test

/-!
# Nesting across sorts: accepted by the checker, rejected by Lean (exists6, 2026-11-22; rejected by the checker too since D121)

Rule (A) (docs/34 §18.6) checks, at an occurrence `M(…d…)` of a data-sorted `d`, that `M` is
data-sorted. It does not follow the parameter on: `M` may pass it to a declaration of the other sort.
The checker accepts all of the following (asserted below), and Lean's kernel rejects `D`, `QW` and `Q`
("mutually inductive types must live in the same universe", checked with the local toolchain):
* `PP (A : Type) : Prop := MkPP(x : A)`, `E (A : Type) := MkE(p : PP(A))`, `D := MkD(e : E(D))`: a
  data-sorted `D` nested in data-sorted `E`, which passes it to the `Prop`-sorted `PP`;
* `Wrap (P : Prop) := MkWrap(h : P)`, `QW : Prop := MkQW(w : Wrap(QW))`: a `Prop`-sorted declaration
  nested directly in a data-sorted one;
* `E2 (P : Prop) : Prop := MkE2(w : Wrap(P))`, `Q : Prop := MkQ(e : E2(Q))`: a `Prop`-sorted one nested
  in a `Prop`-sorted one, which passes it to a data-sorted one.

The checker stores `E`'s parameter as nestable (asserted). What follows:
* `General.mono_prop`'s hypothesis (the shapes at `ps` and `ps'` are equal or weaker proposition
  leaves) cannot hold of `E2`'s records: the shape at `w` is `Wrap`'s record at `P`, a sub-record.
* `knot_exists`'s hypothesis `hpar` is NOT false for `E`. exists6 first claimed it was, in every
  program declaring `E` (argued from a faithful record holding "`PP(A)` is inhabited" as a proposition
  leaf); that claim was wrong (corrected 2026-11-22). A faithful record may keep `PP(A)` as `PP`'s
  sub-record instead of a leaf, and the canonical one does: `hpar_E` below checks, in the program
  `[PP, E]` with `E`'s parameter nestable as the checker stores it today, that the canonical records
  (`recK`) are parametric and faithful at `E`'s field (`fields_E`). Under (A*)(ii) the parameter is not
  nestable, which asks less (`RAgree.anti`).

Rule (A*) (Lean's: a nested occurrence passes only through declarations of the occurring
declaration's sort) was ADOPTED by the lead, subject to measurement. Its decidable predicates are in
`Knot/Grammar.lean` (`occSortB`, `NestSortB`); the guards below show the checker's verdicts today.
-/

namespace Ochr.Meaning.DataModel.Exists.CrossSortCE

open Ochr Ochr.Test

ochr CrossSort {
  inductive PP (A : Type) : Prop := MkPP(x : A)
  inductive E (A : Type) := MkE(p : PP(A))
  reject inductive D := MkD(e : E(D))
  inductive Wrap (P : Prop) := MkWrap(h : P)
  reject inductive QW : Prop := MkQW(w : Wrap(QW))
  inductive E2 (P : Prop) : Prop := MkE2(w : Wrap(P))
  reject inductive Q : Prop := MkQ(e : E2(Q))
}

-- all seven were accepted when this file was written; since D121 (rule (A*) in the checker) `D`, `QW`
-- and `Q` are rejected
#guard (Ochr.Test.run "CrossSort" CrossSort).rejectedWith [
  ("D", "field e of MkD : E(D): D occurs at the parameter A of E, which is not nestable in E: E passes it to a declaration of the other sort"),
  ("QW", "field w of MkQW : Wrap(QW): QW, a proposition, occurs inside an argument of Wrap, a type of data"),
  ("Q", "field e of MkQ : E2(Q): Q occurs at the parameter P of E2, which is not nestable in E2: E2 passes it to a declaration of the other sort")]

def items : List Item :=
  (Prelude.decls ++ CrossSort.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ CrossSort.decls) d with
    | .ok it => some it
    | .error _ => none

-- `PP`'s and `Wrap`'s parameters are stored nestable; `E`'s and `E2`'s were when this file was
-- written, and are not since D121 (each passes its parameter to a declaration of the other sort)
#guard ((globalsAfter {} items).2.filter (fun d => ["PP", "E", "Wrap", "E2"].contains d.name)).map
  (fun d => (d.name, d.nestable)) == [("PP", [true]), ("E", [false]), ("Wrap", [true]), ("E2", [false])]

/-! ## Rule (A*) on these declarations, as the checker stores them today

Before D121 (A*) failed at `E` and `E2` by (ii) (their stored nestable parameter was passed to a
declaration of the other sort) and at `QW` by (i) (it occurs in the data-sorted `Wrap`); `D` and `Q`
passed (A*) at themselves and were excluded only because `E`'s and `E2`'s parameters stop being
nestable under (ii). With D121 in the checker, (A*) holds at every declaration it stores, and `D`,
`QW`, `Q` are not stored. -/

open Ochr.Meaning.DataModel.Exists.Knot in
#guard let inds := (globalsAfter {} items).2
  let ok (n : String) : Option Bool := (inds.find? (·.name == n)).map (AStarOk inds)
  [ok "PP", ok "E", ok "D", ok "Wrap", ok "QW", ok "E2", ok "Q"] ==
    [some true, some true, none, some true, none, some true, none]

/-! ## The canonical record of `E` is parametric and faithful (the corrected claim) -/

open Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Ochr.Meaning.DataModel.Exists.PreludeModel (hn sameDecl)

def ppD : IndDecl :=
  { name := "PP", params := [(hn "A", .sort 1)], sort := 0, ctors := [("MkPP", [("x", .place (.var 0))])],
    nestable := [true] }
def eD : IndDecl :=
  { name := "E", params := [(hn "A", .sort 1)], sort := 1, ctors := [("MkE", [("p", .tind "PP" [.place (.var 0)])])],
    nestable := [true] }

-- the checker stores `PP` so, and `E` so but for its parameter's nestability (after the library's
-- four); `eD` is `E` as stored before D121, whose canonical record is shown parametric below
#guard let inds := (globalsAfter {} items).2
  sameDecl (inds.getD 4 default) ppD && sameDecl (inds.getD 5 default) { eD with nestable := [false] }

theorem semAgree_head {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hN : N 0 = true) (hp : ParAgree N n ps ps') :
    SemAgree n (ps.getD 0 .err) (ps'.getD 0 .err) := by
  rcases h1 : ps[0]? with _ | v
  · have h2 : ps'[0]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    simp only [List.getD_eq_getElem?_getD, h1, h2, Option.getD_none]
    exact .inl rfl
  · rcases h2 : ps'[0]? with _ | v'
    · exfalso
      rw [List.getElem?_eq_none_iff] at h2
      have := (List.getElem?_eq_some_iff.1 h1).1
      rw [hp.1] at this; omega
    · have := hp.2 0 v v' h1 h2
      rw [hN, if_pos rfl] at this
      simp only [List.getD_eq_getElem?_getD, h1, h2, Option.getD_some]
      exact this

/-- `PP`'s knot: its field is its parameter. -/
noncomputable def ppK : KnotSpec where
  d := ppD
  N := fun j => ppD.nestable.getD j false
  fty := fun _ ps _ _ _ => .ty (ps.getD 0 .err).asTy
  pEntry := pEntryTy
  guarded := fun n _ _ _ ps ps' hp _ _ _ => semAgree_fty (semAgree_head (N := fun j => ppD.nestable.getD j false) rfl hp)
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

theorem parAgree_single {n : Nat} {a a' : Sem} (h : SemAgree n a a') :
    ParAgree (fun j => ppD.nestable.getD j false) n [a] [a'] := by
  refine ⟨rfl, fun j v v' h1 h2 => ?_⟩
  match j, h1, h2 with
  | 0, h1, h2 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    exact h

/-- `E`'s knot: its field is `PP` at its parameter, kept as `PP`'s record (a sub-record). -/
noncomputable def eK : KnotSpec where
  d := eD
  N := fun j => eD.nestable.getD j false
  fty := fun _ ps _ _ _ => .data ppD (recK ppK [ps.getD 0 .err])
  pEntry := pEntryTy
  guarded := fun n _ _ _ ps ps' hp _ _ _ =>
    ⟨rfl, recK_agree ppK n [_] [_] (parAgree_single (semAgree_head (N := fun j => eD.nestable.getD j false) rfl hp))⟩
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

theorem eD_ne_ppD : eD ≠ ppD := by
  intro h; have := congrArg IndDecl.name h; simp [eD, ppD] at this

open Classical in
noncomputable def dmX : DataModel where
  covers _ := True
  recOf M := if M = ppD then recK ppK else if M = eD then recK eK else fun _ _ => .none
  paramTy _ _ _ := TyM.univ 1

theorem recOf_E : dmX.recOf eD = recK eK := by simp [dmX, eD_ne_ppD]
theorem recOf_PP : dmX.recOf ppD = recK ppK := by simp [dmX]

/-- **`hpar` holds of `E`'s canonical record**, with `E`'s parameter nestable (as the checker stores it
today), and of `PP`'s. -/
theorem hpar_E (n : Nat) : RAgree (fun j => eD.nestable.getD j false) n (dmX.recOf eD) (dmX.recOf eD) := by
  rw [recOf_E]; exact recK_agree eK n

theorem hpar_PP (n : Nat) : RAgree (fun j => ppD.nestable.getD j false) n (dmX.recOf ppD) (dmX.recOf ppD) := by
  rw [recOf_PP]; exact recK_agree ppK n

/-- Parametricity at fewer nestable parameters is implied (under (A*)(ii) `E`'s parameter is not nestable). -/
theorem RAgree.anti {N N' : Nat → Bool} {n : Nat} {R R' : List Sem → Rec} (hle : ∀ j, N j = true → N' j = true)
    (h : RAgree N' n R R') : RAgree N n R R' := by
  intro ps ps' hp
  refine h ps ps' ⟨hp.1, fun j v v' h1 h2 => ?_⟩
  have := hp.2 j v v' h1 h2
  by_cases hN : N j = true
  · rw [if_pos hN] at this; rw [if_pos (hle j hN)]; exact this
  · rw [if_neg hN] at this; subst this
    by_cases hN' : N' j = true
    · rw [if_pos hN']; exact .inl rfl
    · rw [if_neg hN']

theorem hpar_E_ii (n : Nat) : RAgree (fun _ => false) n (dmX.recOf eD) (dmX.recOf eD) :=
  RAgree.anti (fun _ h => by cases h) (hpar_E n)

/-- **`E`'s field type is the run's** at its canonical record: `PP(A)` runs to `PP`'s code at `PP`'s
record at `A`, which is `E`'s shape at `p` (a `prf` of `PP` at that record). -/
theorem fields_E (K : RunCtx) (hdm : K.dm = dmX) (hΓ : K.Γ = [ppD, eD]) (ρ : Assignment) (ps : List Sem)
    (hlen : ps.length = 1) {r : Res} {s' : SState}
    (hr : run K ρ noFuture (.plain (TyM.univ 1)) (.tind "PP" [.place (.var 0)]) (teleFrame K.dm K.D eD ps 0 []) =
      some (r, s')) :
    r.1.asTy = dmX.fieldTy eD ps 0 0 [] := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  obtain ⟨M, v, T, s₁, hM, hv, hr1⟩ := RunLemmas.runT_tind1 _ ρ noFuture false _ "PP" _ _ hr
  have hMM : M = ppD := (Option.some.inj (show some ppD = some M from hM)).symm
  subst hMM
  have h1 := RunLemmas.runT_teleFrame_param _ ρ noFuture false _ dmX D eD ps 0 [] (by simp) 0 (by omega)
    (by omega) hv
  rw [hr1]
  simp only at h1
  rw [h1]
  obtain ⟨a, rfl⟩ : ∃ a, ps = [a] := by
    rcases ps with _ | ⟨a, _ | _⟩ <;> simp at hlen
    exact ⟨a, rfl⟩
  simp only [Sem.asTy, DataModel.tyM, recOf_PP, tyR_eq_uTyR, DataModel.fieldTy, DataModel.fieldTyR, recOf_E,
    shapeTy_eq_shapeTyP, List.map_nil]
  show uTyR ppD (recK ppK [[a][0]]) = shapeTyP (uShape eD (recK eK [a]) 0 0 [])
  rw [uShape_recK eK eD [a] 0 0 [] rfl]
  simp [eK, shapeOf, FTy.kind, ppD, shapeTyP]
  rfl

end Ochr.Meaning.DataModel.Exists.CrossSortCE
