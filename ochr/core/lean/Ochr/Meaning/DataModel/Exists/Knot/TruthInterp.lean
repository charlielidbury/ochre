import Ochr.Meaning.DataModel.Exists.Knot.Interp
import Ochr.Meaning.DataModel.Exists.Truth

/-!
# Truth first, part 2: the interpreter for a `Prop`-sorted declaration (exists7)

A `Prop`-sorted declaration's code is a proposition, `uTyR d r = TyM.prop (Nonempty (ucar d r))`,
which reads its record at every depth; so a nested occurrence `And(Q, True)` cannot be guarded
(`PropNestCE`). Truth first: fix a truth predicate `T` for `d` and read every occurrence `d(ā)` of `d`
as the proposition `T ā` (`semP`, `itpP`). The field types (`ftyP`) then do not read `d`'s records at
all, so the record they make (`truthSpec T`, `recK`) needs no knot. Everything else is read as the
knot reads it (`Interp.lean`): an earlier declaration through the model's record, a parameter as
itself, a steady node as its run at the canonical frame.

The truth predicate is the least fixed point (`Truth.lfpM`) of `Φ T ps := Nonempty (ucar d (R_T ps))`;
at it, `uTyR d (R_T ā) = TyM.prop (T ā)`, so the actual run's code of `d(ā)` is the interpreter's.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

mutual
/-- A term's value at the canonical frame `s` and the hint `h`, `d`'s own occurrences read as `T`. -/
noncomputable def semP (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) : Term → Sem
  | .tind n as => match K.Γ.find? (·.name == n) with
    | some M => if M = d then .ty (TyM.prop (T (itpArgsP T ps s M 0 [] as)))
      else .ty (uTyR M (K.dm.recOf M (itpArgsP T ps s M 0 [] as)))
    | none => .ty TyM.err
  | .place (.var v) =>
    if v < d.params.length then ps.getD (d.params.length - 1 - v) .err else valOf K ρ s h (.place (.var v))
  | t => valOf K ρ s h t

/-- The arguments of `M(…)` from parameter `j`, after the values `pre`. -/
noncomputable def itpArgsP (T : List Sem → Prop) (ps : List Sem) (s : SState) (M : IndDecl) :
    Nat → List Sem → List Term → List Sem
  | _, _, [] => []
  | j, pre, a :: as =>
    argSemP T ps s M j pre a :: itpArgsP T ps s M (j + 1) (pre ++ [argSemP T ps s M j pre a]) as

/-- One argument's value: a type argument read by `semP`, a value argument as its run. -/
noncomputable def argSemP (T : List Sem → Prop) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat)
    (pre : List Sem) : Term → Sem
  | a => if M.paramIsType j then semP T ps s (.plain TyM.err) a
    else valOf K ρ s (.plain TyM.err) a
end

/-- A term's field type at the canonical frame `s`: `d`'s own occurrence is the proposition leaf. -/
noncomputable def itpP (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) : Term → FTy
  | .tind n as => match K.Γ.find? (·.name == n) with
    | some M => if M = d then .ty (TyM.prop (T (itpArgsP K ρ d T ps s M 0 [] as)))
      else .data M (K.dm.recOf M (itpArgsP K ρ d T ps s M 0 [] as))
    | none => .ty TyM.err
  | t => .ty (semP K ρ d T ps s h t).asTy

/-- **The field types read with `d` as `T`**: as `ftyK`, at the same canonical frames. -/
noncomputable def ftyP (T : List Sem → Prop) (ps : List Sem) (c : Nat) : Nat → List Small → FTy
  | i, es => match fieldTerm d c i with
    | some FT => itpP K ρ d T ps
        (canFrame K d ps c i es fun j => if _h : j < i then shapeTyP (shapeOf (ftyP T ps c j (es.take j))) else TyM.err)
        (.plain (TyM.univ 1)) FT
    | none => .ty TyM.err
termination_by i => i

/-! ## Unfolding the interpreter -/

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

theorem semP_tind (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) (n : String) (as : List Term) :
    semP K ρ d T ps s h (.tind n as) = match K.Γ.find? (·.name == n) with
      | some M => if M = d then .ty (TyM.prop (T (itpArgsP K ρ d T ps s M 0 [] as)))
        else .ty (uTyR M (K.dm.recOf M (itpArgsP K ρ d T ps s M 0 [] as)))
      | none => .ty TyM.err := by
  simp only [semP]

theorem semP_var (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) (v : Nat) (hv : v < d.params.length) :
    semP K ρ d T ps s h (.place (.var v)) = ps.getD (d.params.length - 1 - v) .err := by
  rw [semP, if_pos hv]

theorem semP_other (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) (t : Term)
    (h1 : ∀ n as, t ≠ .tind n as) (h2 : ∀ v, t ≠ .place (.var v)) :
    semP K ρ d T ps s h t = valOf K ρ s h t := by
  rw [semP]
  · exact fun n as e => h1 n as e
  · exact fun v e => h2 v e

theorem itpArgsP_nil (T : List Sem → Prop) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem) :
    itpArgsP K ρ d T ps s M j pre [] = [] := by
  rw [itpArgsP]

theorem itpArgsP_cons (T : List Sem → Prop) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem)
    (a : Term) (as : List Term) :
    itpArgsP K ρ d T ps s M j pre (a :: as) =
      argSemP K ρ d T ps s M j pre a :: itpArgsP K ρ d T ps s M (j + 1) (pre ++ [argSemP K ρ d T ps s M j pre a]) as := by
  rw [itpArgsP]

theorem argSemP_eq (T : List Sem → Prop) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem) (a : Term) :
    argSemP K ρ d T ps s M j pre a = if M.paramIsType j then semP K ρ d T ps s (.plain TyM.err) a
      else valOf K ρ s (.plain TyM.err) a := by
  rw [argSemP]

theorem itpP_tind (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) (n : String) (as : List Term) :
    itpP K ρ d T ps s h (.tind n as) = match K.Γ.find? (·.name == n) with
      | some M => if M = d then .ty (TyM.prop (T (itpArgsP K ρ d T ps s M 0 [] as)))
        else .data M (K.dm.recOf M (itpArgsP K ρ d T ps s M 0 [] as))
      | none => .ty TyM.err := by
  simp only [itpP]

theorem itpP_other (T : List Sem → Prop) (ps : List Sem) (s : SState) (h : TyS) (t : Term)
    (h1 : ∀ n as, t ≠ .tind n as) : itpP K ρ d T ps s h t = .ty (semP K ρ d T ps s h t).asTy := by
  rw [itpP]
  exact fun n as e => h1 n as e

theorem ftyP_eq (T : List Sem → Prop) (ps : List Sem) (c i : Nat) (es : List Small) :
    ftyP K ρ d T ps c i es = match fieldTerm d c i with
      | some FT => itpP K ρ d T ps
          (canFrame K d ps c i es fun j => if _h : j < i then shapeTyP (shapeOf (ftyP K ρ d T ps c j (es.take j))) else TyM.err)
          (.plain (TyM.univ 1)) FT
      | none => .ty TyM.err := by
  rw [ftyP]

end

/-! ## A proposition's code is not a data code -/

theorem dataView_prop (P : Prop) : dataView (TyM.prop P) = none := by
  unfold dataView
  rw [dif_neg]
  rintro ⟨⟨d, r⟩, hs, he⟩
  have hs' : (d.sort == 0) = false := by simpa using hs
  simp only [uTyR, hs', Bool.false_eq_true, if_false, TyM.prop] at he
  obtain ⟨e, hh⟩ := TyM.t0_inj he
  have := Code0.congr_heq (fun c => c.isData) _ _ e hh
  simp [Code0.isData] at this

theorem shapeOf_prop (P : Prop) : shapeOf (.ty (TyM.prop P)) = .leaf (PLift P) (.prop P) := by
  simp only [shapeOf, FTy.kind, dataView_prop]
  rfl

theorem uTyR_prop {d : IndDecl} (hs : d.sort = 0) (r : Rec) : uTyR d r = TyM.prop (Nonempty (ucar d r)) := by
  simp [uTyR, hs]

theorem nonempty_iff_mem (d : IndDecl) (r : Rec) : Nonempty (ucar d r) ↔ ∃ v, DataLib.Mem uSig d r v := by
  constructor
  · rintro ⟨x⟩; exact ⟨_, (DataLib.mem_iff_meanC uSig d r _).2 ⟨x, rfl⟩⟩
  · rintro ⟨v, hv⟩; obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig d r _).1 hv; exact ⟨x⟩

/-! ## The truth record: a `KnotSpec` whose field types do not read its records -/

theorem parAgree_none_eq {n : Nat} {ps ps' : List Sem} (h : ParAgree (fun _ => false) n ps ps') : ps = ps' := by
  apply List.ext_getElem?
  intro j
  rcases h1 : ps[j]? with _ | v
  · rw [List.getElem?_eq_none_iff, h.1] at h1
    rw [List.getElem?_eq_none h1]
  · rcases h2 : ps'[j]? with _ | v'
    · rw [List.getElem?_eq_none_iff, ← h.1] at h2
      rw [List.getElem?_eq_none h2] at h1; cases h1
    · have := h.2 j v v' h1 h2; simp only [Bool.false_eq_true, if_false] at this; rw [this]

/-- **The truth spec**: the field types `ftyP T`, which ignore the record function, so guardedness is
reflexivity (the parameters compared by equality). -/
noncomputable def truthSpec (T : List Sem → Prop) : KnotSpec where
  d := d
  N := fun _ => false
  fty := fun _ ps c i es => ftyP K ρ d T ps c i es
  pEntry := pEntryV d
  guarded := fun _ _ _ _ _ _ hp _ _ _ => by
    rw [parAgree_none_eq hp]; exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryV_agree hp j

/-- The record a truth predicate gives. -/
noncomputable def truthRec (T : List Sem → Prop) : List Sem → Rec := recK (truthSpec K ρ d T)

/-- **The one-step operator**: `d` inhabited at the record `T` gives. -/
def truthOp (T : List Sem → Prop) (ps : List Sem) : Prop := Nonempty (ucar d (truthRec K ρ d T ps))


end Ochr.Meaning.DataModel.Exists.Knot
