import Ochr.Meaning.Consistency
import Ochr.Meaning.DecisionsInst

/-!
# Draft, for the spine lead: what `exists_dataModel` and the run context should say (docs/34 §6)

Definitions only (they type-check; nothing is claimed). The spine lead owns the statements and
restates them from this draft.

1. **Faithfulness.** The data model reads a declaration's field and parameter types as the
   reference run does: at well-typed parameters and earlier fields, the run of the declared type
   term, in the frame the checker's `fieldTele` evaluates it in, is defined and means
   `dm.fieldTy` (`dm.paramTy`). Under the model itself: a field `List(A)` runs to
   `dm.tyM List [A]`. Type functions in field types read the program's earlier globals, so the
   run context is the program meaning's.
2. **The rank.** `rank`, `recArgs` and `rank_lt` go; `semRank` reads the height of the meaning
   (`semHeight`: a constructor value one more than its fields, a number its value), whose law is
   structural (`semHeight_field_lt`) and covers every field step through every declaration.
-/

namespace Ochr.Meaning.DataModel.Faithful

open Ochr Ochr.Meaning Ochr.Meaning.Assembly

/-- A binding holding `v` at type `T`. -/
def bindAt (T : TyM) (v : Sem) : SBinding := { ty := .plain T, val := fun _ => v }

/-- The frame `Machine.fieldTele` evaluates constructor `c`'s field types in, as meanings: the
fields (the earlier ones `e`, the rest `moved`, as the checker binds `⊥`), then the parameters,
each at its type. -/
noncomputable def teleFrame (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : SState :=
  let k := ((d.ctors[c]?).map (·.2.length)).getD 0
  let fs := e ++ List.replicate (k - e.length) Sem.moved
  stateOf 0 (fs.zipIdx.map (fun vi => bindAt (dm.fieldTy d ps c vi.2 (e.take vi.2)) vi.1) ++
    ps.zipIdx.map (fun vj => bindAt (dm.paramTy d vj.2 (ps.take vj.2)) vj.1))

/-- The frame parameter `j`'s declared type is evaluated in: the earlier parameters. -/
noncomputable def paramFrame (dm : DataModel) (d : IndDecl) (ps : List Sem) : SState :=
  stateOf 0 (ps.zipIdx.map (fun vj => bindAt (dm.paramTy d vj.2 (ps.take vj.2)) vj.1))

/-- Parameters each of their declared type at the earlier ones. -/
def ParamsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) : Prop :=
  ∀ j (h : j < ps.length), ps[j] ∈ₛ[dm.read] dm.paramTy d j (ps.take j) ∨ ∃ T, ps[j] = .ty T

/-- Earlier fields each of their field type at the ones before. -/
def FieldsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : Prop :=
  ∀ i (h : i < e.length), e[i] ∈ₛ[dm.read] dm.fieldTy d ps c i (e.take i)

/-- **Field types are the run's readings of the declared field-type terms.** -/
def FieldsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term),
    ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i → fieldTerm d c i = some FT →
    ∃ r s', run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm d ps c e) = some (r, s') ∧
      r.1.asTy = K.dm.fieldTy d ps c i e

/-- **Parameter types are the run's readings of the declared parameter types.** -/
def ParamsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term),
    ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
    ∃ r s', run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm d ps) = some (r, s') ∧
      r.1.asTy = K.dm.paramTy d j ps

/-- **`exists_dataModel`, restated.** The decisions are the checker's (an existential `D` could
make the runs above undefined). Faithfulness is at every checker state over the program's Σ and
every assignment, the run context being the program meaning's (`ProgState.ctx`). -/
def ExistsDataModel (items : List Item) (fuel : Nat) : Prop :=
  ∃ dm : DataModel,
    let D := fun st => checkerDecisions st fuel
    let P := progMeaning dm D (fun _ => .err) {} fuel items
    P.Covered dm ∧ dm.read.WholeFields ∧
      ∀ (st : MState) (ρ : Assignment), st.inds = P.inds →
        FieldsFaithful (P.ctx dm D st) ρ ∧ ParamsFaithful (P.ctx dm D st) ρ

/-- What `CtxOk` should carry beside `covers`. -/
def CtxFaithful (K : RunCtx) (ρ : Assignment) : Prop := FieldsFaithful K ρ ∧ ParamsFaithful K ρ

/-! ## The rank: the height of the meaning -/

mutual
/-- The height of a meaning: a constructor value one more than its fields, a number its value. -/
noncomputable def semHeight : Sem → Nat
  | .dat _ _ _ fs _ => semHeightList fs + 1
  | s => s.asNat.getD 0
noncomputable def semHeightList : List Sem → Nat
  | [] => 0
  | f :: fs => max (semHeight f) (semHeightList fs)
end

theorem semHeight_le_list : ∀ (fs : List Sem) (f : Sem), f ∈ fs → semHeight f ≤ semHeightList fs
  | [], _, h => by cases h
  | g :: gs, f, h => by
    simp only [semHeightList]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (semHeight_le_list gs f h) (Nat.le_max_right _ _)

/-- **Every field of a constructor value has smaller height**, whatever the declarations. -/
theorem semHeight_field_lt (n : String) (ps : List Sem) (c : Nat) (fs : List Sem)
    (el : Option ((A : Type) × A)) (f : Sem) (h : f ∈ fs) : semHeight f < semHeight (.dat n ps c fs el) := by
  simp only [semHeight]
  exact Nat.lt_succ_of_le (semHeight_le_list fs f h)

end Ochr.Meaning.DataModel.Faithful
