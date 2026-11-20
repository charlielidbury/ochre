import Ochr.Meaning.DataModel.Old

/-!
# Three records against the data layer before the port (docs/34 §2; kernel-checked)

Each is a statement about the definitions on `spine` at 34ecffdd, before docs/34's port, kept as a
record against their frozen copy (`DataModel/Old.lean`). The port answers each: faithfulness in
the existence statement excludes the degenerate model (`Faithful.degenerate_not_faithful`), the
rank is the height of the meaning (`Regress/DataCodes.lean`, `CountF` computes `3`), and a code
keeps a record, not parameters (`DataModel/Examples.lean`, `te` is a member of its type).

1. **`exists_dataModel` held of a model that ignores the program** (`degenerate_meets`): every
   field type is `err`, the carriers hold the constructors with no fields, nothing is recursive.
   The statement asked of the data model only that it cover the program's declarations
   (`ProgState.Covered`: `∀ d ∈ P.inds, dm.covers d`) and read whole fields, so it said nothing
   about the program; the checker's field types do not mean this model's (`degenerate_fieldTy`).
2. **The rank law does not give guarded recursion through nesting** (`Counterexamples/Rank.lean`).
3. **A parameter above level 0 is not read back from its code** (`ctorM_large_not_mem`): for
   every data model, a constructor value whose first parameter is a level-1 type value (`te`'s
   `Type`, `Examples/Fording.lean` and `DataModel/Probes.lean`, accepted) is a member of no code
   of its type, so `Assembly.defn_member` is false for that program.
-/

namespace Ochr.Meaning.DataModel.Counterexamples

open Ochr.Meaning.Old Ochr.Meaning.Old.DataModel

/-! ## 1. The degenerate model -/

/-- Constructor `c` of `d` exists and has no fields. -/
def Fieldless (d : IndDecl) (c : Nat) : Prop := ∃ ctor, d.ctors[c]? = some ctor ∧ ctor.2.length = 0

theorem mem_err (R : DataRead) (s : Sem) : ¬ (s ∈ₛ[R] TyM.err) := fun ⟨a, _⟩ => a.elim

/-- A data model that covers every declaration and ignores its fields: every field type is `err`,
an element is a constructor with no fields. -/
noncomputable def degenerate : DataModel where
  covers _ := True
  car d _ := {c : Nat // Fieldless d c}
  fieldTy _ _ _ _ _ := TyM.err
  paramTy _ _ _ := TyM.err
  pack d _ c fs := open Classical in if h : Fieldless d c ∧ fs = [] then some ⟨c, h.1⟩ else none
  tag x := x.1
  fields _ := []
  rank _ := 0
  tag_pack {d ps c fs} x _ h := by
    split at h
    · cases h; rfl
    · cases h
  fields_pack {d ps c fs} x _ h := by
    split at h
    · rename_i hh; exact hh.2.symm
    · cases h
  pack_fields {d ps} x _ := by
    show (open Classical in if h : Fieldless d x.1 ∧ ([] : List Sem) = [] then some (⟨x.1, h.1⟩ : {c // Fieldless d c}) else none) = some x
    rw [dif_pos ⟨x.2, rfl⟩]
  pack_isSome {d ps c fs} _ := by
    simp only
    constructor
    · intro h
      split at h
      · rename_i hh
        obtain ⟨⟨ctor, hc, hl⟩, rfl⟩ := hh
        exact ⟨ctor, hc, by simp [hl], fun i hi => absurd hi (by simp)⟩
      · cases h
    · rintro ⟨ctor, hc, hl, hm⟩
      cases fs with
      | nil => rw [dif_pos ⟨⟨ctor, hc, by simpa using hl.symm⟩, rfl⟩]; rfl
      | cons f fs => exact absurd (hm 0 (by simp)) (mem_err _ _)
  rank_lt _ _ _ _ h := by cases h

/-- **`exists_dataModel`'s statement held of the degenerate model**, for every program: its data
model clauses were `Covered` (every declaration of the program covered) and whole fields. -/
theorem degenerate_meets (inds : List IndDecl) :
    (∀ d ∈ inds, degenerate.covers d) ∧ degenerate.read.WholeFields := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro d ps A a f hf
  simp only [degenerate, readOf] at hf
  split at hf <;> simp at hf

/-- Its field types are `err`, which no checker field type means (`Nat`'s is `TyM.nat`). -/
theorem degenerate_fieldTy (d : IndDecl) (ps : List Sem) (c i : Nat) (e : List Sem) :
    degenerate.fieldTy d ps c i e = TyM.err ∧ TyM.nat ≠ TyM.err :=
  ⟨rfl, fun h => by have := congrArg TyM.level h; simp [TyM.level, TyM.nat, TyM.err, Code0.level] at this⟩

/-! ## 3. Parameters above level 0 -/

/-- No level-0 encoding is a type value. -/
theorem Code0.enc_ne_ty (R : DataRead) {A : Type} (c : Code0 A) (a : A) (T : TyM) : c.enc R a ≠ .ty T := by
  cases c with
  | err => exact a.elim
  | _ => simp [Code0.enc]

/-- A parameter that is a type value of level 1 or 2 is coded as an element, so it reads back as
an encoding or `err`, never as itself. -/
theorem parOf_large_sem (R : DataRead) (T : TyM) (U : TyM) (hU : ∀ A c, U ≠ .t0 A c) :
    (parOf R T (.ty U)).sem R ≠ .ty U := by
  cases U with
  | t0 A c => exact absurd rfl (hU A c)
  | t1 A c =>
    simp only [parOf, Par0.sem, eltOf]
    split
    · exact Code0.enc_ne_ty R _ _ _
    · simp [Elt0.sem]
  | t2 A c =>
    simp only [parOf, Par0.sem, eltOf]
    split
    · exact Code0.enc_ne_ty R _ _ _
    · simp [Elt0.sem]

/-- **A data value whose first parameter is a type of level 1 or 2 is a member of no code of its
type**, at every data model: the code reads that parameter back as something else. -/
theorem dat_large_not_mem (dm : DataModel) (d : IndDecl) (hs : (d.sort == 0) = false) (U : TyM)
    (hU : ∀ A c, U ≠ .t0 A c) (rest : List Sem) (n : String) (k : Nat) (fs : List Sem)
    (el : Option ((A : Type) × A)) :
    ¬ (Sem.dat n (.ty U :: rest) k fs el ∈ₛ[dm.read] dm.tyM d (.ty U :: rest)) := by
  intro h
  simp only [DataModel.tyM, hs, Bool.false_eq_true, if_false, Sem.mem] at h
  obtain ⟨a, ha⟩ := h
  simp only [Code0.enc, DataModel.parsOf, Par0.sems, Sem.dat.injEq] at ha
  exact parOf_large_sem dm.read _ U hU (List.cons.inj ha.2.1).1

/-- `Type₀` as a value is a level-1 type: what the run gives the parameter `Type` (`Run.lean`, the
`.sort` clause: `.ty (TyM.univ 1)`). -/
theorem univ1_large : ∀ A c, TyM.univ 1 ≠ .t0 A c := by
  intro A c h; cases h

/-- **`te : TEq(Type, Word, Word)`'s constructor value is not a member of its type**, at every data
model: the run's constructor clause gives `ctorM d ps c fs` (`Run.lean`), here at parameters whose
first is `Type`. -/
theorem ctorM_large_not_mem (dm : DataModel) (d : IndDecl) (hs : (d.sort == 0) = false)
    (rest : List Sem) (c : Nat) (fs : List Sem) :
    ¬ (dm.ctorM d (.ty (TyM.univ 1) :: rest) c fs ∈ₛ[dm.read] dm.tyM d (.ty (TyM.univ 1) :: rest)) := by
  unfold DataModel.ctorM
  split
  · split
    · exact dat_large_not_mem dm d hs _ univ1_large rest _ _ _ _
    · exact dat_large_not_mem dm d hs _ univ1_large rest _ _ _ _
  · exact dat_large_not_mem dm d hs _ univ1_large rest _ _ _ _

end Ochr.Meaning.DataModel.Counterexamples
