import Ochr.Meaning.Strict.MemReadsCE
import Ochr.Meaning.DataModel.ReadMember
import Ochr.Meaning.Regress.DataCodes

/-!
# The typed read (route (c)): witnesses, and the partly moved read refuted

The read is ported (`DataModel.readTy`, `Places.Sem.stepField`, `ReadMember.follow_good`). Here: the
read lemma applied to the `MemReadsCE` value (`fresh_member`), the read on a hand model
(`list_tail_read`), and what no read typing gives: a partly moved value with its index moved out
(`not_memReads_dep`), which open membership (`DataModel.OMem`) handles.
-/

namespace Ochr.Meaning.ReadProto

open Ochr.Meaning Ochr.Meaning.DataModel Ochr.Meaning.DataLib

open Classical

section Witness
open Ochr.Meaning.Strict.MemReadsCE

/-- The read lemma applied to the counterexample's member: its field is a member of the type the
read gives it (the non-vacuity witness of `follow_good`). -/
theorem fresh_member (dm : DataModel) : Sem.el0 Nat 5 ∈ₛ[dm.read] TyM.nat := by
  rcases follow_good (Γ := []) [.field g] (.inl (mem dm)) (fresh_read dm []) with h | ⟨h, -⟩
  · exact h
  · exact absurd (congrArg TyM.level h) (by decide)

end Witness

section HandModel
open Ochr.Meaning.DataModel.Program (dmP listD)
open Ochr.Meaning.Regress.DataCodes (semL rN psN)

/-- The tail of `[3, 4] : List(Nat)` at the probes' model: `[4]` at `List(Nat)`. -/
theorem list_tail_read (Γ : List IndDecl) :
    Sem.follow dmP Γ (.plain (dmP.tyM listD psN)) (semL [3, 4]) [.field ⟨"List", 1, 1, "t"⟩]
        = some (semL [4], .plain (dmP.tyM listD psN)) := by
  have hdc : (TyS.plain (dmP.tyM listD psN)).m.dataCode? = some (listD, rN) := rfl
  have hsh : dmP.sig.shape listD rN 1 1 [Sem.small (.el0 Nat 3)] =
      .sub listD (DataLib.contRec rN (DataLib.contStep 1 1 [.other])) := rfl
  have hrt : dmP.readTy listD rN 1 1 [.el0 Nat 3] (semL [4]) = some (dmP.tyM listD psN) := by
    simp only [DataModel.readTy, List.map_cons, List.map_nil, hsh]; rfl
  simp only [semL] at hrt
  simp only [Sem.follow, Sem.step, Sem.stepField, hdc, semL, Option.bind]
  simp [show listD.name = "List" from rfl, hrt]

end HandModel

/-! ## What neither read gives: a partly moved value with its index moved out

`MemReads` also asks the read lemma of every value BELOW a member (`MovedOf`). A field whose type
reads an earlier INDEX field is read at the key of that field's current content; once the index is
moved out the key is another's, so the whole field reads at the wrong type. Below: `C(n : Nat, v :
X(n))` at a record where `v` is a `Nat` leaf at every number `n` and nothing at `⊥`. `C(3, 7)` is a
member; `C(⊥, 7)` is below it; its `v` reads `7` at `err`, by name (with `C` declared, the record
coherent) and typed alike. This is the dependent-values area: the checker (D112) invalidates such
a field when its index is written; the model mirrors that and replaces "below a member" by the
dependent-values lane's open membership (`Dep/`), whose definition this read lemma then is. -/

section DepMoved
open Ochr.Meaning.Strict

/-- `C(n : Nat, v : X(n))`: field `v`'s type mentions field `n` (an index field, D64). -/
def dE : IndDecl := { name := "E", ctors := [("C", [("n", .nat), ("v", .tind "X" [.place (.var 1)])])] }

/-- `n` a `Nat` leaf; `v` a `Nat` leaf at every number, nothing at any other reading of `n`. -/
def rE : Rec
  | [(0, 0, [])] => .leaf Nat .nat
  | [(0, 1, [.el _ _])] => .leaf Nat .nat
  | _ => .none

def gV : FieldRef := { ty := "E", ctor := 0, idx := 1, name := "v" }

theorem dE_index : dE.indexFields 0 = [0] := by decide

theorem cE_mem (dm : DataModel) : Sem.dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7] ∈ₛ[dm.read] dm.tyR dE rE := by
  refine (dm.mem_tyR dE rE rfl _).2 ((DataLib.mem_iff dm.sig dE rE _).2 ⟨⟨0, by decide⟩, _, rfl, ?_⟩)
  show ∃ f fs', [Sem.el0 Nat 3, Sem.el0 Nat 7] = f :: fs' ∧ _ ∧ _
  refine ⟨.el0 Nat 3, [.el0 Nat 7], rfl, ⟨3, rfl⟩, .el0 Nat 7, [], rfl, ?_, rfl⟩
  have hsh : dm.sig.shape dE rE 0 1 [Small.el Nat 3] = .leaf Nat .nat := rfl
  show FitsOneM dm.sig (dm.sig.shape dE rE 0 1 [Small.el Nat 3]) _
  rw [hsh]
  exact ⟨7, rfl⟩

/-- `C(⊥, 7)` is below the member `C(3, 7)`. -/
theorem cE_below : DataModel.MovedOf [dE] (.dat "E" rE 0 [.moved, .el0 Nat 7]) (.dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7]) :=
  .dat (.cons (.moved _) (.cons (.refl _) .nil))

theorem shape_moved (dm : DataModel) : dm.sig.shape dE rE 0 1 [Small.other] = .leaf PEmpty .err := rfl

/-- The read of `C(⊥, 7).v` (`Γ` anything, `C` declared or not): `7` at `err`. -/
theorem moved_index_read (dm : DataModel) (Γ : List IndDecl) :
    Sem.follow dm Γ (.plain (dm.tyR dE rE)) (.dat "E" rE 0 [.moved, .el0 Nat 7]) [.field gV]
      = some (.el0 Nat 7, .plain TyM.err) := by
  have hown : ¬ dm.OwnCarrier Code0.err := by
    rintro ⟨d, r, h, -⟩; cases h
  have hdc : (TyS.plain (dm.tyR dE rE)).m.dataCode? = some (dE, rE) := rfl
  have hrt : dm.readTy dE rE 0 1 [.moved] (.el0 Nat 7) = some TyM.err := by
    simp only [DataModel.readTy, List.map_cons, List.map_nil, Sem.small, shape_moved, DataModel.shapeReadTy,
      if_neg hown]; rfl
  simp only [Sem.follow, Sem.step, Sem.stepField, gV, hdc, Option.bind]
  simp [show dE.name = "E" from rfl, hrt]

/-- **`MemReads` (its partly moved form) is false even for a declared declaration at a coherent
record**, in every data model, under the typed read. -/
theorem not_memReads_dep (dm : DataModel) : ¬ MemReads dm [dE] := by
  intro h
  rcases h (.plain (dm.tyR dE rE)) _ _ (cE_mem dm) cE_below [.field gV] _ _ (moved_index_read dm [dE])
      (by simp [Sem.whole]) with ⟨a, _⟩ | ⟨-, ⟨T, hT⟩ | hT⟩
  · exact a.elim
  · cases hT
  · cases hT

end DepMoved

end Ochr.Meaning.ReadProto
