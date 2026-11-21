import Ochr.Meaning.DataLib.Universal

/-!
# The model of inductive types (docs/34 §8, §14)

A data value's meaning is a tree (`Sem.dat name r c fs`: its declaration's name, its type's
record, its constructor, its fields). A data type's meaning is a code naming its declaration, its
RECORD and its carrier (`Code0.data d r A`); the record keeps what the declaration's field types
read of the parameters, never a parameter above level 0, which no `Type₀` code can hold. The
members of `D` at `r` are the least set of trees closed under `D`'s constructors (`Mem`,
`DataLib.mem_iff`), defined from the signature before any carrier; the carrier is a small copy of
the members with a bijection onto them (`meanC`), which is the reading (`read`). There is no
packing, no fixed point of a model and its reading, and no rank: guarded recursion reads the
height of a meaning (`semHeight`, `Places.lean`).

What the program decides is the interface: which declarations are covered, the signature (each
field's shape at a record and the earlier fields read small: a leaf's code, a data field's
declaration and record, a proof of a `Prop`-sorted declaration), the record of a declaration at
parameters, and the parameters' types. That they are the reference run's readings of the
declared types is faithfulness (`DataModel/Faithful.lean`), the existence statement's obligation.
Everything else is defined here, and its laws are the library's theorems (`DataLib`).

`Nat` and `Unit` are not declarations (`Value.tNat`, `Value.tUnit`, `zero`, `succ`, `unit`) and
are modelled directly in `Value.lean` as `Nat` and `Unit`.
-/

namespace Ochr.Meaning

open DataLib


/-- **The model of the program's inductive declarations** (docs/34 §14). -/
structure DataModel where
  covers : IndDecl → Prop
  /-- The record of `D(ps)`: what `D`'s field types read of the parameters (along the whole
  unfolding), and at `paramKey` each type parameter's entry and each level-0 value parameter read
  small. -/
  recOf : IndDecl → List Sem → Rec
  /-- The meaning of the declared type of parameter `i` at the earlier parameters (a type
  parameter's is its sort; a value parameter's, D71, a data type). -/
  paramTy : IndDecl → Nat → List Sem → TyM

namespace DataModel

variable (dm : DataModel)

/-- The signature: the universal one (docs/34 §18), the same for every model; what a model decides
is its records. -/
@[reducible] def sig (_ : DataModel) : Sig := uSig

/-- The carrier of `D` at record `r`: a small copy of its members. -/
def car (d : IndDecl) (r : Rec) : Type := DataLib.car dm.sig d r

/-- An element's meaning. -/
def meanC {d : IndDecl} {r : Rec} (x : dm.car d r) : Sem := DataLib.meanC dm.sig x

/-- **The members of `D` at `r`**: the least set of trees closed under `D`'s constructors. -/
def Mem (d : IndDecl) (r : Rec) (v : Sem) : Prop := DataLib.Mem dm.sig d r v

/-- **The carrier is a copy of the members**: a member is the meaning of an element. -/
theorem mem_iff_meanC (d : IndDecl) (r : Rec) (v : Sem) : dm.Mem d r v ↔ ∃ x : dm.car d r, dm.meanC x = v :=
  DataLib.mem_iff_meanC dm.sig d r v

/-- Reading an element of a carrier: its meaning, when the carrier is the model's at the code's
declaration and record; tagged by its carrier otherwise (no code of the model has that carrier). -/
noncomputable def readFn (d : IndDecl) (r : Rec) (A : Type) (a : A) : Sem :=
  open Classical in if h : A = dm.car d r then dm.meanC (cast h a) else .el0 A a

theorem readFn_inj (d : IndDecl) (r : Rec) (A : Type) : Function.Injective (dm.readFn d r A) := by
  intro a b h
  unfold readFn at h
  split at h
  · rename_i hA
    have hc := DataLib.meanC_inj dm.sig _ _ h
    have := congrArg (cast hA.symm) hc
    simpa using this
  · simp only [Sem.el0.injEq, heq_eq_eq, true_and] at h
    exact h

/-- **The reading**: the bijection between a carrier and its members. -/
noncomputable def read : DataRead := ⟨dm.readFn, dm.readFn_inj⟩

theorem read_car {d : IndDecl} {r : Rec} (x : dm.car d r) : dm.read.read d r (dm.car d r) x = dm.meanC x := by
  simp [read, readFn]

/-- The meaning of `D` at a record: its code (a `Prop`-sorted declaration: the proposition that
its carrier is inhabited). -/
def tyR (d : IndDecl) (r : Rec) : TyM :=
  if d.sort == 0 then TyM.prop (Nonempty (dm.car d r)) else .t0 (dm.car d r) (.data d r (dm.car d r))

/-- **The meaning of the type `D(ps)`.** -/
def tyM (d : IndDecl) (ps : List Sem) : TyM := dm.tyR d (dm.recOf d ps)

/-- A data code (a leaf's code is never one in a canonical signature). -/
def _root_.Ochr.Meaning.Code0.isData : {A : Type} → Code0 A → Bool
  | _, .data .. => true
  | _, _ => false

/-- A shape's type. A leaf's is its code, whatever the code (docs/34 §18, task 2a): a data code over
a foreign carrier (a junk code of `Type₀`'s carrier, `Exists/StatementCE`) is an ordinary leaf, its
members the tagged elements the reading gives a foreign carrier. A `sub` of a `Prop`-sorted
declaration or a `prf` of a data one has the error type. -/
def shapeTy : Shape → TyM
  | .leaf B c => .t0 B c
  | .sub d r => if d.sort == 0 then TyM.err else dm.tyR d r
  | .prf d r => if d.sort == 0 then dm.tyR d r else TyM.err

/-- The type field `i` of constructor `c` of `D` at record `r` is read at, given the earlier fields. -/
def fieldTyR (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) : TyM :=
  dm.shapeTy (dm.sig.shape d r c i (earlier.map Sem.small))

/-- The same at parameters: the meaning of the declared type of field `i` of constructor `c` at
the parameters and the earlier fields (the telescope, D64). -/
def fieldTy (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : TyM :=
  dm.fieldTyR d (dm.recOf d ps) c i earlier

/-- Parameter `j`'s type as a record keeps it (`unifyTyS` reads a type parameter back off a record):
its leaf's code, or its declaration at the record's continuation past the parameter. -/
def paramTyOf (r : Rec) (j : Nat) : TyM :=
  match r (paramKey j) with
  | .leaf B c => .t0 B c
  | .data d => dm.tyR d (contRec r (paramContStep j))
  | _ => TyM.err

/-- **A constructor value at a record**: the tree, whatever its fields hold. -/
def ctorR (d : IndDecl) (r : Rec) (c : Nat) (fs : List Sem) : Sem := .dat d.name r c fs

/-- A constructor value at parameters. -/
def ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem := ctorR d (dm.recOf d ps) c fs

/-- The constructor and fields of a constructor value, read off the value (docs/31 D32). -/
def _root_.Ochr.Meaning.Sem.parts : Sem → Option (Nat × List Sem)
  | .dat _ _ c fs => some (c, fs)
  | _ => none

theorem parts_ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) :
    (dm.ctorM d ps c fs).parts = some (c, fs) := rfl

/-! ## Membership of data, through the reading -/

/-- **The members of a data type's code are the members of its declaration at its record.** -/
theorem mem_tyR (d : IndDecl) (r : Rec) (hs : (d.sort == 0) = false) (v : Sem) :
    v ∈ₛ[dm.read] dm.tyR d r ↔ dm.Mem d r v := by
  unfold tyR
  rw [hs]
  show (∃ a, dm.read.read d r (dm.car d r) a = v) ↔ _
  simp only [read_car]
  exact (DataLib.mem_iff_meanC dm.sig d r v).symm

/-- A `Prop`-sorted declaration's type is the proposition that it has a member. -/
theorem tyR_prop (d : IndDecl) (r : Rec) (hs : (d.sort == 0) = true) :
    dm.tyR d r = TyM.prop (∃ v, dm.Mem d r v) := by
  unfold tyR
  rw [hs]
  simp only [if_true]
  congr 1
  apply propext
  constructor
  · rintro ⟨x⟩; exact ⟨_, (DataLib.mem_iff_meanC dm.sig d r _).2 ⟨x, rfl⟩⟩
  · rintro ⟨v, hv⟩; obtain ⟨x, _⟩ := (DataLib.mem_iff_meanC dm.sig d r v).1 hv; exact ⟨x⟩

theorem err_mem_false (R : DataRead) (s : Sem) : ¬ (s ∈ₛ[R] TyM.err) := fun ⟨a, _⟩ => nomatch a

/-- The declaration and record of a data code. -/
def _root_.Ochr.Meaning.Code0.dataCode? : {A : Type} → Code0 A → Option (IndDecl × Rec)
  | _, .data d r _ => some (d, r)
  | _, _ => none

/-- A shape is not a leaf holding a data code over the model's own carrier (such a code's members
are trees, a leaf's tagged elements). A canonical record never makes one: a data code at the
model's carrier is a `.data` entry, so a `sub`. -/
def LeafOk : Shape → Prop
  | .leaf B c => ∀ d r, c.dataCode? = some (d, r) → B ≠ dm.car d r
  | _ => True

/-- Every field shape of `D` at the record satisfies `LeafOk` (a canonical record's do: it keeps a
data code at the model's carrier as a `.data` entry, `RecordsFaithful.leafOk`). -/
def RecLeafOk (d : IndDecl) (r : Rec) : Prop := ∀ c i e, dm.LeafOk (dm.sig.shape d r c i e)

/-- **On a canonical shape, fitting is membership**: a field that fits its shape among the members
is a member of the shape's type, unless that type is `err` (a non-canonical shape) or the shape is a
leaf holding a data code over the model's own carrier. -/
theorem fitsOneM_mem (s : Shape) (f : Sem) (h : DataLib.FitsOneM dm.sig s f) (hne : dm.shapeTy s ≠ TyM.err)
    (hok : dm.LeafOk s) : f ∈ₛ[dm.read] dm.shapeTy s := by
  cases s with
  | leaf B c =>
    obtain ⟨b, rfl⟩ := h
    cases c with
    | data d r A =>
      have hA : B ≠ dm.car d r := hok d r rfl
      refine ⟨b, ?_⟩
      show dm.readFn d r B b = _
      simp only [readFn, dif_neg hA, encLeaf]
    | err => exact b.elim
    | prop P => exact ⟨b, rfl⟩
    | nat => exact ⟨b, rfl⟩
    | unit => exact ⟨b, rfl⟩
    | pi C t => exact ⟨b, rfl⟩
  | sub d r =>
    by_cases hs : (d.sort == 0) = true
    · exact absurd (by simp [shapeTy, hs]) hne
    · have hs' : (d.sort == 0) = false := by simpa using hs
      simp only [shapeTy, hs', Bool.false_eq_true, if_false]
      exact (dm.mem_tyR d r hs' f).2 h
  | prf d r =>
    by_cases hs : (d.sort == 0) = true
    · obtain ⟨rfl, hv⟩ := h
      simp only [shapeTy, hs, if_true]
      rw [dm.tyR_prop d r hs]
      exact ⟨⟨hv⟩, rfl⟩
    · exact absurd (by simp [shapeTy, hs]) hne

/-- **The reading gives whole meanings** (docs/31 D68): a member is whole. -/
theorem read_wholeFields : dm.read.WholeFields := by
  intro d r A a
  show (dm.readFn d r A a).whole
  unfold readFn
  split
  · exact DataLib.mem_whole dm.sig d r _ ((DataLib.mem_iff_meanC dm.sig d r _).2 ⟨_, rfl⟩)
  · simp [Sem.whole]

/-- A whole constructor value that is OPEN in the data type `T` (D64): it names `T`'s declaration
and record and its fields are whole (a field may lie outside the type its earlier fields give; the
checker types such a field by its content until [Repack]). Membership's `pmem` admits it, as the
checker's state does (`Regress/OpenWriteDep`). -/
def OpenIn (_R : DataRead) : TyM → Sem → Prop
  | .t0 _ (.data d r _), .dat n' r' _ fs => d.name = n' ∧ r = r' ∧ ∀ f ∈ fs, f.whole
  | _, _ => False

mutual
/-- `s` is `t` with some of its parts moved out: `moved` is anything with all of it moved, a
partly moved constructor value is one with some fields moved out, and a partly moved number is a
successor whose predecessor is (docs/31 D24). -/
inductive MovedOf (Γ : List IndDecl) : Sem → Sem → Prop
  | moved (t : Sem) : MovedOf Γ .moved t
  | refl (t : Sem) : MovedOf Γ t t
  | dat {n : String} {r : Rec} {c : Nat} {fs gs : List Sem} :
      MovedOfList Γ fs gs → MovedOf Γ (.dat n r c fs) (.dat n r c gs)
  | succ {s : Sem} {n : Nat} : MovedOf Γ s (.el0 Nat n) → MovedOf Γ (.dat "Nat" natRec 1 [s]) (.el0 Nat (n + 1))

/-- The same, field by field. -/
inductive MovedOfList (Γ : List IndDecl) : List Sem → List Sem → Prop
  | nil : MovedOfList Γ [] []
  | cons {f g : Sem} {fs gs : List Sem} : MovedOf Γ f g → MovedOfList Γ fs gs → MovedOfList Γ (f :: fs) (g :: gs)
end

/-- Membership for a possibly partly moved value (docs/18 part (b) at a binding holding a value
some field of which was moved out): the value is `⊥` outright, or it is some whole member of the
type with parts moved out (`MovedOf`). For a whole value this is membership (`pmem_of_mem`). -/
def pmem (R : DataRead) (Γ : List IndDecl) (s : Sem) (T : TyM) : Prop :=
  s = .moved ∨ ∃ t : Sem, t.whole ∧ MovedOf Γ s t ∧ (t ∈ₛ[R] T ∨ OpenIn R T t)

theorem pmem_of_mem (R : DataRead) (Γ : List IndDecl) {s : Sem} {T : TyM} (hw : s.whole) (h : s ∈ₛ[R] T) :
    pmem R Γ s T :=
  .inr ⟨s, hw, .refl s, .inl h⟩

end DataModel

end Ochr.Meaning
