import Ochr.Meaning.Strict.MemReadsCE
import Ochr.Meaning.DataModel.ReadMember
import Ochr.Meaning.Regress.DataCodes

/-!
# PROTOTYPE (route (c), 2026-11-21): a read typed by the value's type and record, not by name

Today a read types a field through the declaration it finds BY NAME in `Γ` (`Places.contentTyS`:
`fieldHint` at `Γ.find? n`, and `dataTyS` for a field that is a constructor value), so a data code
of an undeclared declaration has members whose fields read at `err` (`MemReadsCE`).

What a field's type needs (`DataModel.fieldTyR d r c i e = shapeTy (uShape d r c i e)`):
* the RECORD `r` (the tree's own): the entry at the field's key, which for a data field names the
  field's declaration (`Entry.data d'`) and gives its record as the continuation;
* the DECLARATION `d` of the value, only for its index fields (`projIdx d c`: which earlier fields
  the key keeps). The tree carries only its declaration's NAME. The record does not say which
  fields are index fields.
So the record alone is not enough; the declaration is. Here it is taken from the TYPE the read
starts at (a data code carries its declaration, `TyM.dataCode?`), and down the path from the
shapes (a `sub` shape carries the field's declaration). No lookup by name remains; the named step's
check becomes "the type's declaration is the value's" (the names agree).

The field's type (`readTy`) is the type whose members are exactly the values that fit the field's
shape (`fits_readTy`), at every shape but one: a leaf whose code is a data code over the model's
own carrier (no type has the tagged leaf elements as its members; the canonical signature has no
such leaf, `DataModel.LeafOk`). There the read FAILS (`none`), so the read lemma has no hypothesis.
-/

namespace Ochr.Meaning.ReadProto

open Ochr.Meaning Ochr.Meaning.DataModel Ochr.Meaning.DataLib

open Classical

variable (dm : DataModel)

/-- A data code of `d` at `r` over the model's carrier, whatever `d`'s sort (a `sub` shape's members). -/
noncomputable def rawTy (d : IndDecl) (r : Rec) : TyM := .t0 (dm.car d r) (.data d r (dm.car d r))

/-- A leaf code that is a data code over the model's own carrier (the junk leaf `LeafOk` excludes). -/
def OwnCarrier {B : Type} (c : Code0 B) : Prop := ∃ d r, c.dataCode? = some (d, r) ∧ B = dm.car d r

/-- **The type a field of a shape is read at**: the type whose members are the values that fit it;
none at a junk leaf. -/
noncomputable def shapeReadTy : Shape → Option TyM
  | .leaf B c => if OwnCarrier dm c then none else some (.t0 B c)
  | .sub d r => some (rawTy dm d r)
  | .prf d r => some (TyM.prop (Nonempty (dm.car d r)))

/-- **The type field `i` of constructor `c` is read at**, in a value of declaration `d` at its own
record `r`, given the earlier fields and the field itself: the shape's, a constructor value in a
data field at ITS OWN record (D112: a tree field keeps the type its own record gives). -/
noncomputable def readTy (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) (f : Sem) : Option TyM :=
  match dm.sig.shape d r c i (earlier.map Sem.small), f with
  | .sub d' _, .dat _ r' _ _ => some (rawTy dm d' r')
  | sh, _ => shapeReadTy dm sh

/-- A fitting value is a member of the type its shape is read at. -/
theorem fits_readTy {sh : Shape} {f : Sem} {U : TyM} (hf : FitsOneM dm.sig sh f) (hU : shapeReadTy dm sh = some U) :
    f ∈ₛ[dm.read] U := by
  cases sh with
  | leaf B c =>
    simp only [shapeReadTy] at hU
    split at hU
    · cases hU
    · rename_i hown
      cases hU
      obtain ⟨b, rfl⟩ := hf
      refine ⟨b, ?_⟩
      cases c with
      | data d r A =>
        have hA : B ≠ dm.car d r := fun h => hown ⟨d, r, rfl, h⟩
        show dm.readFn d r B b = _
        simp only [DataModel.readFn, dif_neg hA, encLeaf]
      | err => exact b.elim
      | prop P => rfl
      | nat => rfl
      | unit => rfl
      | pi C t => rfl
  | sub d r =>
    simp only [shapeReadTy, Option.some.injEq] at hU
    subst hU
    obtain ⟨x, rfl⟩ := (dm.mem_iff_meanC d r f).1 hf
    exact ⟨x, show dm.read.read d r (dm.car d r) x = _ from dm.read_car x⟩
  | prf d r =>
    simp only [shapeReadTy, Option.some.injEq] at hU
    subst hU
    obtain ⟨rfl, v, hv⟩ := hf
    obtain ⟨x, -⟩ := (dm.mem_iff_meanC d r v).1 hv
    exact ⟨⟨⟨x⟩⟩, rfl⟩

/-- The field's type, for a value that fits the field's shape, is the shape's. -/
theorem readTy_fit {d : IndDecl} {r : Rec} {c i : Nat} {earlier : List Sem} {f : Sem}
    (hf : FitsOneM dm.sig (dm.sig.shape d r c i (earlier.map Sem.small)) f) :
    readTy dm d r c i earlier f = shapeReadTy dm (dm.sig.shape d r c i (earlier.map Sem.small)) := by
  unfold readTy
  generalize dm.sig.shape d r c i (earlier.map Sem.small) = sh at hf ⊢
  cases sh with
  | sub d' r₀ =>
    cases f with
    | dat n r' c' fs =>
      obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d' r₀ _).1 hf
      simp only [Sem.dat.injEq] at he
      obtain ⟨-, rfl, -⟩ := he
      rfl
    | _ => rfl
  | _ => rfl

/-! ## The read, typed by the type the path starts at -/

/-- Field `i` of constructor `c` of a constructor value read at the type `T`: the type's declaration
must be the value's (the names agree), and the field is read at `readTy`, at the value's own
record. A field of `⋆` is `⋆` at `err`. -/
noncomputable def stepFieldT (T : TyS) (c i : Nat) (s : Sem) : Option (Sem × TyS) :=
  match s with
  | .proof => some (.proof, .plain TyM.err)
  | .dat n r c' fs =>
    match T.m.dataCode? with
    | some (d, _) =>
      if d.name = n ∧ c' = c then
        match fs[i]? with
        | some f => (readTy dm d r c i (fs.take i) f).map fun U => (f, .plain U)
        | none => none
      else none
    | none => none
  | _ => none

/-- One step (`Sem.step` with the field typed by `stepFieldT`): a partly moved number's predecessor
is read only at a type that is not a data code. -/
noncomputable def stepT (T : TyS) : Step → Sem → Option (Sem × TyS)
  | .deref, s => some (s, T)
  | .proj 0, s =>
    match s.asNat with
    | some (n + 1) => some (.el0 Nat n, .plain TyM.nat)
    | some 0 => none
    | none => match T.m.dataCode?, s with
      | none, .dat "Nat" _ 1 [w] => some (w, .plain TyM.nat)
      | _, _ => stepFieldT dm T 0 0 s
  | .proj i, s => stepFieldT dm T 0 i s
  | .field g, s => match s with
    | .dat n _ _ _ => if n = g.ty ∧ n ≠ "Nat" then stepFieldT dm T g.ctor g.idx s else none
    | s => stepFieldT dm T g.ctor g.idx s

/-- Follow a path, typed by the type it starts at. -/
noncomputable def followT (T : TyS) (s : Sem) : List Step → Option (Sem × TyS)
  | [] => some (s, T)
  | st :: sts => (stepT dm T st s).bind fun (s', T') => followT T' s' sts

/-- What a read returns: a member of its type, or no data at `err` (`GoodRes`'s escape). -/
def GoodAt (T : TyS) (w : Sem) : Prop := w ∈ₛ[dm.read] T.m ∨ (T.m = TyM.err ∧ Strict.NoData w)

variable {dm}

theorem stepFieldT_good {T U : TyS} {c i : Nat} {w x : Sem} (hw : GoodAt dm T w)
    (h : stepFieldT dm T c i w = some (x, U)) : GoodAt dm U x := by
  unfold stepFieldT at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, .inr rfl⟩
  · rename_i n r c' fs
    split at h
    · rename_i d r₀ hdc
      split at h
      · rename_i hcond
        obtain ⟨hn, rfl⟩ := hcond
        split at h
        · rename_i f hf
          cases hU : readTy dm d r c' i (fs.take i) f with
          | none => rw [hU] at h; cases h
          | some U' =>
            rw [hU] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases hw with hm | ⟨-, ⟨X, hX⟩ | hX⟩
            · obtain ⟨d₁, hdc₁, hmem, -⟩ := mem_dat_inv dm hm
              rw [hdc] at hdc₁
              simp only [Option.some.injEq, Prod.mk.injEq] at hdc₁
              obtain ⟨rfl, -⟩ := hdc₁
              subst hn
              obtain ⟨⟨c₂, hc₂⟩, fs₂, he, hfits⟩ := (DataLib.mem_iff dm.sig d r _).1 hmem
              simp only [Sem.dat.injEq, true_and] at he
              obtain ⟨hc, rfl⟩ := he
              subst hc
              have hfit := fitsM_get dm.sig d r c' _ 0 [] fs hfits i f hf
              simp only [Nat.zero_add, List.nil_append] at hfit
              rw [readTy_fit dm hfit] at hU
              exact .inl (fits_readTy dm hfit hU)
            · cases hX
            · cases hX
        · cases h
      · cases h
    · cases h
  · cases h

theorem stepT_good {T U : TyS} {st : Step} {w x : Sem} (hw : GoodAt dm T w)
    (h : stepT dm T st w = some (x, U)) : GoodAt dm U x := by
  cases st with
  | deref =>
    simp only [stepT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hw
  | proj i =>
    cases i with
    | zero =>
      simp only [stepT] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨_, rfl⟩
      · cases h
      · split at h
        · rename_i hT _
          rcases hw with hm | ⟨-, ⟨X, hX⟩ | hX⟩
          · obtain ⟨d₁, hdc, -, -⟩ := mem_dat_inv dm hm
            rw [hT] at hdc; cases hdc
          · cases hX
          · cases hX
        · exact stepFieldT_good hw h
    | succ i => exact stepFieldT_good hw h
  | field g =>
    simp only [stepT] at h
    split at h
    · split at h
      · exact stepFieldT_good hw h
      · cases h
    · exact stepFieldT_good hw h

/-- **The read lemma, with no hypothesis**: every read path of a value that is good at a type (a
member, or no data at `err`) gives a good value at the type the read gives it. In particular every
read of a MEMBER of ANY data code (declared by the program or not, at any record) gives a member
of its type or `⋆`/a type value at `err`. -/
theorem followT_good : ∀ (steps : List Step) {T U : TyS} {w x : Sem}, GoodAt dm T w →
    followT dm T w steps = some (x, U) → GoodAt dm U x
  | [], T, U, w, x, hw, h => by
    simp only [followT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hw
  | st :: sts, T, U, w, x, hw, h => by
    simp only [followT] at h
    cases hs : stepT dm T st w with
    | none => rw [hs] at h; cases h
    | some p =>
      obtain ⟨w', T'⟩ := p
      rw [hs] at h
      exact followT_good sts (stepT_good hw hs) h

/-- `MemReads`' whole form, for the typed read: a member's whole read paths give members (or no data
at `err`), for every data model, every type, every path. -/
theorem memReads_whole {T U : TyS} {w x : Sem} (hw : w ∈ₛ[dm.read] T.m) (steps : List Step)
    (h : followT dm T w steps = some (x, U)) : x ∈ₛ[dm.read] U.m ∨ (U.m = TyM.err ∧ Strict.NoData x) :=
  followT_good steps (.inl hw) h

/-! ## Witnesses -/

section Witness
open Ochr.Meaning.Strict.MemReadsCE

/-- **The typed read on the counterexample**: `Fresh.C(5)`'s field reads `5` at `Nat` (the by-name
read gave `err`, `MemReadsCE.not_memReads`), in every data model and whatever `Γ` declares. -/
theorem fresh_read (dm : DataModel) :
    followT dm (.plain (dm.tyR dF rF)) (.dat "Fresh" rF 0 [.el0 Nat 5]) [.field g]
      = some (.el0 Nat 5, .plain TyM.nat) := by
  have hown : ¬ OwnCarrier dm Code0.nat := by
    rintro ⟨d, r, h, -⟩; cases h
  have hdc : (TyS.plain (dm.tyR dF rF)).m.dataCode? = some (dF, rF) := rfl
  have hsh : dm.sig.shape dF rF 0 0 [] = .leaf Nat .nat := rfl
  have hrt : readTy dm dF rF 0 0 [] (.el0 Nat 5) = some TyM.nat := by
    simp only [readTy, List.map_nil, hsh, shapeReadTy, if_neg hown]; rfl
  simp only [followT, stepT, stepFieldT, g, hdc, Option.bind]
  simp [show dF.name = "Fresh" from rfl, hrt]

/-- The read lemma applied to the counterexample's member: its field is a member of the type the
read gives it (the non-vacuity witness of `memReads_whole`). -/
theorem fresh_member (dm : DataModel) : Sem.el0 Nat 5 ∈ₛ[dm.read] TyM.nat := by
  rcases memReads_whole (mem dm) [.field g] (fresh_read dm) with h | ⟨h, -⟩
  · exact h
  · exact absurd (congrArg TyM.level h) (by decide)

end Witness

/-! ## On a hand model the typed read agrees with the by-name read -/

section HandModel
open Ochr.Meaning.DataModel.Program (dmP listD)
open Ochr.Meaning.Regress.DataCodes (semL rN psN)

/-- The tail of `[3, 4] : List(Nat)` at the probes' model: both reads give `[4]` at `List(Nat)`. -/
theorem list_tail_agree :
    followT dmP (.plain (dmP.tyM listD psN)) (semL [3, 4]) [.field ⟨"List", 1, 1, "t"⟩]
        = some (semL [4], .plain (dmP.tyM listD psN)) ∧
      Sem.follow dmP [listD] (.plain (dmP.tyM listD psN)) (semL [3, 4]) [.field ⟨"List", 1, 1, "t"⟩]
        = some (semL [4], .plain (dmP.tyM listD psN)) := by
  have hdc : (TyS.plain (dmP.tyM listD psN)).m.dataCode? = some (listD, rN) := rfl
  have hsh : dmP.sig.shape listD rN 1 1 [Sem.small (.el0 Nat 3)] =
      .sub listD (DataLib.contRec rN (DataLib.contStep 1 1 [.other])) := rfl
  have hrt : readTy dmP listD rN 1 1 [.el0 Nat 3] (semL [4]) = some (dmP.tyM listD psN) := by
    simp only [readTy, List.map_cons, List.map_nil, hsh]; rfl
  simp only [semL] at hrt
  constructor
  · simp only [followT, stepT, stepFieldT, hdc, semL, Option.bind]
    simp [show listD.name = "List" from rfl, hrt]
  · simp [Sem.follow, Sem.step, Sem.stepField, contentTyS, dataTyS, semL,
      show listD.name = "List" from rfl, DataModel.tyM, Regress.DataCodes.recOf_listNat]

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

/-- The by-name read of `C(⊥, 7).v`, with `C` declared: `7` at `err`. -/
theorem byName_read (dm : DataModel) :
    Sem.follow dm [dE] (.plain (dm.tyR dE rE)) (.dat "E" rE 0 [.moved, .el0 Nat 7]) [.field gV]
      = some (.el0 Nat 7, .plain TyM.err) := by
  have hfd : List.find? (fun x => x.name == "E") [dE] = some dE := rfl
  have hct : contentTyS dm [dE] "E" rE 0 1 [.moved] (.el0 Nat 7) = .plain TyM.err := by
    simp only [contentTyS, hfd, fieldHint, DataModel.fieldTyR, List.map_cons, List.map_nil, Sem.small,
      shape_moved]
    rfl
  simp [Sem.follow, Sem.step, Sem.stepField, gV, hct]

/-- The typed read of `C(⊥, 7).v`: also `7` at `err`. -/
theorem typed_read (dm : DataModel) :
    followT dm (.plain (dm.tyR dE rE)) (.dat "E" rE 0 [.moved, .el0 Nat 7]) [.field gV]
      = some (.el0 Nat 7, .plain TyM.err) := by
  have hown : ¬ OwnCarrier dm Code0.err := by
    rintro ⟨d, r, h, -⟩; cases h
  have hdc : (TyS.plain (dm.tyR dE rE)).m.dataCode? = some (dE, rE) := rfl
  have hrt : readTy dm dE rE 0 1 [.moved] (.el0 Nat 7) = some TyM.err := by
    simp only [readTy, List.map_cons, List.map_nil, Sem.small, shape_moved, shapeReadTy, if_neg hown]; rfl
  simp only [followT, stepT, stepFieldT, gV, hdc, Option.bind]
  simp [show dE.name = "E" from rfl, hrt]

/-- **`MemReads` is false even for a declared declaration at a coherent record**, in every data model:
the partly moved form, independently of how a read finds the declaration. -/
theorem not_memReads_dep (dm : DataModel) : ¬ MemReads dm [dE] := by
  intro h
  rcases h (.plain (dm.tyR dE rE)) _ _ (cE_mem dm) cE_below [.field gV] _ _ (byName_read dm)
      (by simp [Sem.whole]) with ⟨a, _⟩ | ⟨-, ⟨T, hT⟩ | hT⟩
  · exact a.elim
  · cases hT
  · cases hT

/-- The typed read's partly moved form is false too. -/
theorem not_typed_below (dm : DataModel) :
    ¬ ∀ (T U : TyS) (w v x : Sem) (steps : List Step), w ∈ₛ[dm.read] T.m → DataModel.MovedOf [dE] v w →
      followT dm T v steps = some (x, U) → x.whole → GoodAt dm U x := by
  intro h
  rcases h _ _ _ _ _ _ (cE_mem dm) cE_below (typed_read dm) (by simp [Sem.whole]) with ⟨a, _⟩ | ⟨-, ⟨T, hT⟩ | hT⟩
  · exact a.elim
  · cases hT
  · cases hT

end DepMoved

end Ochr.Meaning.ReadProto
