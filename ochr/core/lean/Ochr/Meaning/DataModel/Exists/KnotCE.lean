import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Exists.PreludeModel
import Ochr.Meaning.Strict.Witness
import Ochr.Meaning.Steps.FrameFrag
import Ochr.Test

/-!
# `knot_exists` as first written is false: a value parameter carries the knot's own records (exists5)

`General.knot_exists` (exists2, 2026-11-21) asked of the earlier declarations' records only `hpar`:
each is parametric in its nestable parameters (`RAgree`), which compares a VALUE parameter by
equality. But a value parameter can hold a member of the declaration being built, and such a member
carries the knot's record (`Sem.dat d.name r c fs`). So an earlier record may read the knot's record
through a value parameter, at any depth, and put what it reads at a short path; `hpar` does not
forbid it, and then the knot's record must equal its own flip at some path.

The declarations (both accepted by the checker, asserted natively below):
`Pt (A : Type) (a : A) := MkPt` and `D2 := D2Leaf | D2Node(x : D2, p : Pt(D2, x))`. Field `p`'s
type is `Pt` at the code of `D2` and at the earlier field `x`, a member of `D2` at the knot's record.

The model (`dmCE`): `Pt`'s record at `[A, v]` holds at the empty path the FLIP of `v`'s own record at
the path `[contStep 1 1 [v.small]]` (the step past `p`'s key, at `x`'s small reading). It reads only
the value parameter, so `hpar` holds. If a knot `S` existed: field `x`'s run gives `D2` at `recK S []`
(`run_x`), so `x := D2Leaf` at that record is a member; field `p`'s run then gives `Pt` at
`[D2's code, D2Leaf]` (`run_p`), and the knot's record past `p`'s key is that record
(`recK_cont`): at the empty path, `recK S [] π = flip (recK S [] π)`.

Lean rejects the same declarations ("nested inductive datatypes parameters cannot contain local
variables"). What this shows: `hpar` must compare value parameters by their small readings (what the
canonical records read of them), or the checker must reject a value argument that reads an earlier
field whose type mentions the declaration (Lean's rule); docs/34 §18.6.
-/

namespace Ochr.Meaning.DataModel.Exists.KnotCE

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Ochr.Meaning.DataModel.Exists.RunLemmas
open Ochr.Meaning.DataModel.Exists.PreludeModel (hn sameDecl)

/-! ## The statement as exists2 wrote it -/

/-- `General.knot_exists` as first written (kept here so its refutation is checked in the default
build). -/
def KnotOld : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (d : IndDecl), d ∈ K.Γ → d.sort ≠ 0 →
    (∀ P : ProgState, P.baseC = K.C → GlobalsTyped K.dm P) →
    (∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M)) →
    ∃ S : KnotSpec, S.d = d ∧ (∀ j, S.N j = d.nestable.getD j false) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), FitsOneM uSig (uShape d (recK S ps) c j ((e.take j).map Sem.small)) e[j]) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d (recK S) } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d (recK S)) K.D d ps c e) = some (r, s') →
          r.1.asTy = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean

/-! ## The declarations, as the checker stores them -/

def ptD : IndDecl :=
  { name := "Pt", params := [(hn "A", .sort 1), (hn "a", .place (.var 0))], sort := 1,
    ctors := [("MkPt", [])], nestable := [true, false] }
def d2D : IndDecl :=
  { name := "D2", sort := 1,
    ctors := [("D2Leaf", []), ("D2Node", [("x", .tind "D2" []), ("p", .tind "Pt" [.tind "D2" [], .place (.var 1)])])] }

def ceDecls : List IndDecl := [ptD, d2D]

open Ochr.Test in
ochr KnotCEA {
  inductive Pt (A : Type) (a : A) := MkPt
  inductive D2 := D2Leaf | D2Node(x : D2, p : Pt(D2, x))
}

open Ochr.Test in
-- both declarations are accepted
#guard (Ochr.Test.run "KnotCEA" KnotCEA).rejectedWith []

/-- The block's items, after the library's. -/
def ceItems : List Item :=
  (Prelude.decls ++ KnotCEA.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ KnotCEA.decls) d with
    | .ok it => some it
    | .error _ => none

-- after the library and the block, the checker's last two inductive declarations are `ceDecls`
#guard let inds := (globalsAfter {} ceItems).2
  inds.length == 6 && ((inds.drop 4).zip ceDecls).all fun ab => sameDecl ab.1 ab.2

/-! ## The model -/

/-- An entry's flip: never itself. -/
def flipE : Entry → Entry
  | .none => .leaf Unit .unit
  | _ => .none

theorem flipE_ne (x : Entry) : flipE x ≠ x := by
  cases x <;> simp [flipE]

/-- `Pt`'s record at `[A, v]`: at the empty path, the flip of `v`'s record at the step past `D2Node`'s
field `p`'s key (at `v`'s small reading); nothing elsewhere. -/
def advPt (ps : List Sem) : Rec := fun q =>
  match q, ps[1]? with
  | [], some (Sem.dat n r c fs) => flipE (r [contStep 1 1 [(Sem.dat n r c fs).small]])
  | _, _ => .none

open Classical in
noncomputable def dmCE : DataModel where
  covers _ := True
  recOf d ps := if d = ptD then advPt ps else fun _ => .none
  paramTy _ j ps := if j = 0 then TyM.univ 1 else (ps.getD 0 .err).asTy

def cC : CodeMeaning where
  global _ := (.err, .plain TyM.err)
  sealed _ _ _ _ := .err
  clo _ _ _ _ _ := .err
  pi _ _ _ _ _ := TyM.err
  paramTy _ _ _ _ := .plain TyM.err

noncomputable def KCE : RunCtx where
  dm := dmCE
  Γ := ceDecls
  C := cC
  D := Strict.Witness.Dw []

/-! ## The hypotheses hold -/

theorem ptD_ne : ptD ≠ d2D := by
  intro h; have := congrArg IndDecl.name h; simp [ptD, d2D] at this

theorem hglob_CE : ∀ P : ProgState, P.baseC = KCE.C → GlobalsTyped KCE.dm P := by
  intro P hP n g _ _ args s r s' hc
  rw [hP] at hc
  simp [KCE, cC, callOf, TyS.plain, TyM.err] at hc

/-- At a non-nestable parameter `ParAgree` is equality. -/
theorem parAgree_get {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (h : ParAgree N n ps ps') (j : Nat)
    (hj : N j = false) : ps[j]? = ps'[j]? := by
  rcases h1 : ps[j]? with _ | v
  · rw [List.getElem?_eq_none_iff] at h1
    exact (List.getElem?_eq_none_iff.2 (by rw [← h.1]; exact h1)).symm
  · rcases h2 : ps'[j]? with _ | v'
    · rw [List.getElem?_eq_none_iff] at h2
      have : ps[j]? = none := List.getElem?_eq_none_iff.2 (by rw [h.1]; exact h2)
      rw [this] at h1; cases h1
    · have := h.2 j v v' h1 h2
      rw [hj] at this
      simp only [Bool.false_eq_true, if_false] at this
      rw [this]

theorem hpar_CE : ∀ M ∈ KCE.Γ, M ≠ d2D → ∀ n,
    RAgree (fun j => M.nestable.getD j false) n (KCE.dm.recOf M) (KCE.dm.recOf M) := by
  intro M hM hne n ps ps' hp q _
  simp only [KCE, ceDecls, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl
  · have h1 := parAgree_get hp 1 (by simp [ptD])
    simp only [KCE, dmCE]
    unfold advPt
    rw [h1]
  · exact absurd rfl hne


/-- **A variable's run, forward**: in a shape-free state, under decisions that erase nothing, the read
of a whole value its stored type admits succeeds with that value. -/
theorem runT_var_fwd (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (j : Nat) (s : SState)
    (hD : ∀ sc t, K.D.flags sc t = (false, false)) (hs : s.shape = fun _ => none) (pos : Pos)
    (hpos : s.varPos j = some pos) (hw : (s.valAt pos φ).whole) (hg : ReadGood K.dm.read (s.tyAt pos).m (s.valAt pos φ)) :
    ∃ T s', ∀ h, runT K ρ φ tl h (.place (.var j)) s = some ((s.valAt pos φ, T), s') := by
  have hacc : ∀ hit, s.access pos hit = s := fun hit => Attack.access_noShape s hs pos hit
  have hll : s.liveLabels = [] := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    simp [SState.liveLabels, hs, h0]
  have htf : s.typedFuture φ = φ := by funext l; simp [SState.typedFuture, hll]
  have hc : contentOf K φ (.var j) s = some ((s.valAt pos φ, s.tyAt pos, pos, []), s) := by
    simp only [contentOf, resolve, Place.steps, hpos, Option.map_some, hacc, htf, Sem.follow]
    rfl
  have hrd : ∀ cp, ∃ T s', readPlace K φ (.var j) cp s = some ((s.valAt pos φ, T), s') := by
    intro cp
    simp only [readPlace, hc, bind, Option.bind]
    rw [if_neg (fun hn => hn hw), if_neg (fun hn => hn hg)]
    cases cp
    · simp only [Bool.false_eq_true, if_false, List.isEmpty_nil, if_true, hs,
        Steps.Form.FrameFrag.setContent_nil]
      exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  obtain ⟨T, s', e⟩ := hrd (K.D.copy (K.D.placeDecl (scopeOf s) (.var j)))
  refine ⟨T, s', fun h => ?_⟩
  simp only [runT]
  rw [hD]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false,
    SM.guarded_of (Strict.Witness.contentOk_noLive hll (.var j))]
  exact e

/-! ## The runs, at any knot -/

section
variable (S : KnotSpec)

/-- The model with `D2`'s records the knot's. -/
noncomputable abbrev dmR : DataModel := setRec dmCE d2D (recK S)
noncomputable abbrev KR : RunCtx := { KCE with dm := dmR S }

theorem find_D2 : ceDecls.find? (·.name == "D2") = some d2D := rfl
theorem find_Pt : ceDecls.find? (·.name == "Pt") = some ptD := rfl

theorem tyM_D2 (ps : List Sem) : (dmR S).tyM d2D ps = uTyR d2D (recK S ps) := by
  simp only [DataModel.tyM, dmR, setRec_self, tyR_eq_uTyR]

theorem tyM_Pt (ps : List Sem) : (dmR S).tyM ptD ps = uTyR ptD (advPt ps) := by
  simp only [DataModel.tyM, dmR, setRec_other _ _ ptD_ne, tyR_eq_uTyR]
  simp [dmCE]

/-- `D2` runs to its code at the knot's record, in any state. -/
theorem run_D2 (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) :
    runT (KR S) ρ φ tl h (.tind "D2" []) s = some ((.ty (uTyR d2D (recK S [])), .plain (TyM.univ 1)), s) := by
  simp only [runT, KCE, find_D2, runParams, pure, bind]
  rw [if_pos (paramsOk_nil _ _), tyM_D2]
  rfl


/-- `x`'s frame: `D2Node`'s fields, the first `x`, the second not yet there. -/
theorem varPos_x (x : Sem) : (teleFrame (dmR S) KCE.D d2D [] 1 [x]).varPos 1 = some (.bind 0 0) := by
  simp [teleFrame, SState.varPos, stateOf, SState.topIdx, d2D]

theorem valAt_x (x : Sem) (φ : Future) : (teleFrame (dmR S) KCE.D d2D [] 1 [x]).valAt (.bind 0 0) φ = x := by
  simp [teleFrame, SState.valAt, stateOf, d2D, faithBind]

theorem tyAt_x (x : Sem) : ((teleFrame (dmR S) KCE.D d2D [] 1 [x]).tyAt (.bind 0 0)).m =
    (dmR S).fieldTy d2D [] 1 0 [] := by
  simp [teleFrame, SState.tyAt, stateOf, d2D, faithBind]
  rfl

/-- `Pt(D2, x)` runs to `Pt` at `[D2's code, x]`, when `x` is a whole member of its stored type. -/
theorem run_p (ρ : Assignment) (x : Sem) (hw : x.whole)
    (hx : x ∈ₛ[(dmR S).read] (dmR S).fieldTy d2D [] 1 0 [])
    (hx' : x ∈ₛ[(dmR S).read] uTyR d2D (recK S [])) :
    ∃ r s', run (KR S) ρ noFuture (.plain (TyM.univ 1)) (.tind "Pt" [.tind "D2" [], .place (.var 1)])
      (teleFrame (dmR S) KCE.D d2D [] 1 [x]) = some (r, s') ∧
      r.1 = .ty (uTyR ptD (advPt [.ty (uTyR d2D (recK S [])), x])) := by
  have hsh : (teleFrame (dmR S) KCE.D d2D [] 1 [x]).shape = fun _ => none := rfl
  obtain ⟨T, s₁, hrx⟩ := runT_var_fwd (KR S) ρ noFuture false 1 _ (fun _ _ => rfl) hsh (.bind 0 0)
    (varPos_x S x) (by rw [valAt_x]; exact hw) (by rw [valAt_x, tyAt_x]; exact .inl hx)
  rw [valAt_x] at hrx
  have hpo : paramsOk (dmR S) ptD [.ty (uTyR d2D (recK S [])), x] := by
    intro i v hv
    match i, hv with
    | 0, hv =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      simp only [dmR, setRec_paramTy, dmCE, if_true, List.take_zero]
      refine ⟨⟨ucar d2D (recK S []), ⟨.data d2D (recK S []) (ucar d2D (recK S [])), by simp [Code0.level, d2D]⟩⟩, ?_⟩
      simp [Code1.enc, uTyR, d2D, ucar]
    | 1, hv =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      exact hx'
  have hrun : run (KR S) ρ noFuture (.plain (TyM.univ 1)) (.tind "Pt" [.tind "D2" [], .place (.var 1)])
      (teleFrame (dmR S) KCE.D d2D [] 1 [x]) =
      some ((.ty (uTyR ptD (advPt [.ty (uTyR d2D (recK S [])), x])), .plain (TyM.univ 1)),
        teleFrame (dmR S) KCE.D d2D [] 1 [x]) := by
    show runT (KR S) ρ noFuture false _ _ (teleFrame (dmR S) KCE.D d2D [] 1 [x]) = _
    rw [runT]
    have hf : (KR S).Γ.find? (·.name == "Pt") = some ptD := rfl
    simp only [hf, runParams, pure, bind, SM.onCopy, run_D2, Option.map_some, hrx]
    rw [if_pos hpo, tyM_Pt]
    rfl
  exact ⟨_, _, hrun, rfl⟩

end


/-! ## The refutation -/

/-- A field type meaning a data-sorted declaration's code at a record: its kind is the declaration
and its continuation the record. -/
theorem kind_cont_of_mean {F : FTy} {d : IndDecl} {r : Rec} (hs : d.sort ≠ 0) (h : uTyR d r = F.mean) :
    F.kind = .data d ∧ F.cont = r := by
  cases F with
  | data d' r' =>
    simp only [FTy.mean] at h
    by_cases hs' : d'.sort = 0
    · exfalso
      have e1 : (d.sort == 0) = false := by simpa using hs
      have e2 : (d'.sort == 0) = true := by simpa using hs'
      have hl := congrArg (fun T : TyM => match T with | .t0 _ c => c.level | _ => none) h
      simp [uTyR, e1, e2, TyM.prop, Code0.level] at hl
    · obtain ⟨rfl, rfl⟩ := uTyR_inj hs hs' h
      exact ⟨rfl, rfl⟩
  | ty T =>
    simp only [FTy.mean] at h
    subst h
    simp [FTy.kind, FTy.cont, dataView_uTyR d r hs]

theorem d2_sort : d2D.sort ≠ 0 := by simp [d2D]

theorem idx_d2 : d2D.indexFields 1 = [0] := by decide

theorem projIdx_d2 (sm : Small) : projIdx d2D 1 [sm] = [sm] := by simp [projIdx, idx_d2]

/-- **`knot_exists` as first written is false.** -/
theorem knotOld_false : ¬ KnotOld := by
  intro H
  obtain ⟨S, -, -, hag⟩ := H KCE (fun _ => .err) d2D (by simp [KCE, ceDecls]) d2_sort hglob_CE hpar_CE
  -- field `x`: its type runs to `D2` at the knot's record
  have h0 := hag [] 1 0 [] (.tind "D2" []) _ _ rfl (by simp) (by simp) rfl rfl
    (run_D2 S (fun _ => .err) noFuture false _ _)
  obtain ⟨hk0, hc0⟩ := kind_cont_of_mean d2_sort h0
  have hkey0 : recK S [] (kindKey 1 0 []) = .data d2D := (recK_kind S [] 1 0 [] rfl).trans hk0
  have hcr0 : contRec (recK S []) (contStep 1 0 []) = recK S [] := (recK_contRec S [] 1 0 [] rfl).trans hc0
  have hsh0 : uShape d2D (recK S []) 1 0 [] = .sub d2D (recK S []) := by
    rw [uShape_data d2D _ 1 0 [] d2D hkey0]
    simp [d2D, hcr0, projIdx_nil]
  -- `D2Leaf` at that record is a member
  let x : Sem := .dat "D2" (recK S []) 0 []
  have hmem : DataLib.Mem uSig d2D (recK S []) x :=
    (DataLib.mem_iff uSig d2D (recK S []) x).2 ⟨⟨0, by simp [d2D]⟩, [], rfl, by simp [FitsM, arity, d2D]⟩
  have hft : (dmR S).fieldTy d2D [] 1 0 [] = uTyR d2D (recK S []) := by
    simp only [DataModel.fieldTy, DataModel.fieldTyR, dmR, setRec_self, DataModel.sig, uSig, List.map_nil]
    show (dmR S).shapeTy (uShape d2D (recK S []) 1 0 []) = _
    rw [hsh0, shapeTy_eq_shapeTyP]
    simp [shapeTyP, d2D]
  have hx' : x ∈ₛ[(dmR S).read] uTyR d2D (recK S []) := by
    rw [← tyR_eq_uTyR (dmR S), DataModel.mem_tyR _ _ _ (by simp [d2D])]
    exact hmem
  -- field `p`: its type runs to `Pt` at `[D2's code, x]`
  obtain ⟨r, s', hrun, hr⟩ := run_p S (fun _ => .err) x (by simp [x, Sem.whole]) (by rw [hft]; exact hx') hx'
  have h1 := hag [] 1 1 [x] _ r s' rfl (by simp)
    (by
      intro j hj
      simp only [List.length_singleton] at hj
      obtain rfl : j = 0 := by omega
      simp only [List.take_zero, List.map_nil, List.getElem_singleton]
      rw [hsh0]; exact hmem)
    rfl rfl hrun
  rw [hr] at h1
  simp only [Sem.asTy, List.map_cons, List.map_nil, projIdx_d2] at h1
  obtain ⟨-, hc1⟩ := kind_cont_of_mean (by simp [ptD]) h1
  -- the knot's record past `p`'s key is `Pt`'s record there: at the empty path, its own flip
  have e := recK_cont S [] 1 1 [x.small] rfl []
  rw [hc1] at e
  simp only [advPt, List.getElem?_cons_succ, List.getElem?_cons_zero] at e
  exact flipE_ne _ e.symm

end Ochr.Meaning.DataModel.Exists.KnotCE
