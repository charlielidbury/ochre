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

/-! ## The type a read gives a field (route (c), 2026-11-21; `Strict/ReadProto.lean` the prototype)

A field is typed from the TYPE the read starts at (a data code carries its declaration) and the
value's own record, through the universal signature. The declaration is needed for one thing only,
which earlier fields are index fields (the record's key projects to them, `projIdx`). One case looks
a declaration up by name: a tree field holding a tree of ANOTHER declaration than the one its shape
names at the current earlier fields (what a strong update stored before an index write changed the
field's declared type; the checker's `depFieldType` types it by its content, `valType?`, its own
declaration and parameters), typed by its own declaration found in the program's declarations, at
its own record (`ownTy`). A member never reaches that case (`readTy_fit`). `readTy` is THE function
for "the type a read gives a field": the run's read (`Places.Sem.stepField`), open membership (`OMem`)
and the read lemma use it. -/

/-- The declaration and record of a data code, at any carrier level (lifts included). -/
def _root_.Ochr.Meaning.Code1.dataCode? : {A : Type 1} → Code1 A → Option (IndDecl × Rec)
  | _, .lift _ c => c.dataCode?
  | _, _ => none

def _root_.Ochr.Meaning.Code2.dataCode? : {A : Type 2} → Code2 A → Option (IndDecl × Rec)
  | _, .lift _ c => c.dataCode?
  | _, _ => none

def _root_.Ochr.Meaning.TyM.dataCode? : TyM → Option (IndDecl × Rec)
  | .t0 _ c => c.dataCode?
  | .t1 _ c => c.dataCode?
  | .t2 _ c => c.dataCode?

/-- The data code of `d` at `r` over the model's carrier, whatever `d`'s sort (a `sub` shape's members). -/
noncomputable def rawTy (d : IndDecl) (r : Rec) : TyM := .t0 (dm.car d r) (.data d r (dm.car d r))

/-- A leaf code that is a data code over the model's own carrier (the junk leaf `LeafOk` excludes). -/
def OwnCarrier {B : Type} (c : Code0 B) : Prop := ∃ d r, c.dataCode? = some (d, r) ∧ B = dm.car d r

open Classical in
/-- The type a field of a shape is read at: the type whose members are the values that fit it;
none at a junk leaf (no type has its tagged elements as members). -/
noncomputable def shapeReadTy : Shape → Option TyM
  | .leaf B c => if dm.OwnCarrier c then none else some (.t0 B c)
  | .sub d r => some (dm.rawTy d r)
  | .prf d r => some (TyM.prop (Nonempty (dm.car d r)))

/-- A tree's own type: its declaration, found by name among the program's declarations, at its own
record (the checker's `valType?` of a tree). -/
noncomputable def ownTy (Γ : List IndDecl) (n : String) (r : Rec) : Option TyM :=
  (Γ.find? (·.name == n)).map (dm.rawTy · r)

/-- **The type field `i` of constructor `c` is read at**, in a value of declaration `d` at its own
record `r`, given the program's declarations, the earlier fields and the field itself: the shape's;
a constructor value in a data field at ITS OWN record (D112: a tree field keeps the type its own
record gives), of its OWN declaration where that is not the shape's (`ownTy`: a strong update's
tree, typed by its content as the checker's `depFieldType` types it). -/
noncomputable def readTy (Γ : List IndDecl) (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) (f : Sem) :
    Option TyM :=
  match dm.sig.shape d r c i (earlier.map Sem.small), f with
  | .sub d' _, .dat n r' _ _ => if n = d'.name then some (dm.rawTy d' r') else dm.ownTy Γ n r'
  | sh, _ => dm.shapeReadTy sh

/-- **A fitting value is a member of the type its shape is read at.** -/
theorem fits_readTy {sh : Shape} {f : Sem} {U : TyM} (hf : FitsOneM dm.sig sh f) (hU : dm.shapeReadTy sh = some U) :
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
        simp only [readFn, dif_neg hA, encLeaf]
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

/-- For a value that fits the field's shape, the field's type is the shape's. -/
theorem readTy_fit {Γ : List IndDecl} {d : IndDecl} {r : Rec} {c i : Nat} {earlier : List Sem} {f : Sem}
    (hf : FitsOneM dm.sig (dm.sig.shape d r c i (earlier.map Sem.small)) f) :
    dm.readTy Γ d r c i earlier f = dm.shapeReadTy (dm.sig.shape d r c i (earlier.map Sem.small)) := by
  unfold readTy
  generalize dm.sig.shape d r c i (earlier.map Sem.small) = sh at hf ⊢
  cases sh with
  | sub d' r₀ =>
    cases f with
    | dat n r' c' fs =>
      obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d' r₀ _).1 hf
      simp only [Sem.dat.injEq] at he
      obtain ⟨hn, rfl, -⟩ := he
      simp only [hn, if_true]
      rfl
    | _ => rfl
  | _ => rfl

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

mutual
/-- **Open membership** (D64, D112; route (c); the dependent-values unit, 2026-11-21): what a position
holds. `moved`; a member; a partly moved number; or a constructor value of the type's declaration at
the type's record each of whose fields is `moved` or an open member of the type the READ gives it
(`readTy`), at some completion of the earlier fields' moved parts (the current earlier fields are
one: `MovedOfList.refl`). A tree field is read at its own record (D112), so a value whose index was
rewritten under a tree field is open, not a member; a whole value is a member exactly when closed
(`closed_iff_mem`). -/
inductive OMem (Γ : List IndDecl) : TyM → Sem → Prop
  | moved (T : TyM) : OMem Γ T .moved
  | mem {T : TyM} {s : Sem} : s ∈ₛ[dm.read] T → OMem Γ T s
  | succ {T : TyM} {s : Sem} (n : Nat) : Sem.el0 Nat (n + 1) ∈ₛ[dm.read] T → OMem Γ TyM.nat s →
      OMem Γ T (.dat "Nat" natRec 1 [s])
  | dat {T : TyM} {d : IndDecl} {r : Rec} {c : Nat} {fs : List Sem} :
      T.dataCode? = some (d, r) → c < d.ctors.length → fs.length = arity d c →
      OFields Γ d r c 0 [] fs → OMem Γ T (.dat d.name r c fs)

/-- The fields of an open value, one by one, after the earlier ones. -/
inductive OFields (Γ : List IndDecl) : IndDecl → Rec → Nat → Nat → List Sem → List Sem → Prop
  | nil {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} : OFields Γ d r c i e []
  | cons {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem} {fs : List Sem} :
      OField Γ d r c i e f → OFields Γ d r c (i + 1) (e ++ [f]) fs → OFields Γ d r c i e (f :: fs)

/-- One field of an open value, at a completion `e'` of the earlier fields: `moved`; a partly moved
member of the field's shape (its declared type, fitting); or an open member of the type the read
gives it (a tree at its own record, D112). -/
inductive OField (Γ : List IndDecl) : IndDecl → Rec → Nat → Nat → List Sem → Sem → Prop
  | moved {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} : OField Γ d r c i e .moved
  | fits {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem} (e' : List Sem) (t : Sem) :
      MovedOfList Γ e e' → t.whole → MovedOf Γ f t → FitsOneM dm.sig (dm.sig.shape d r c i (e'.map Sem.small)) t →
      OField Γ d r c i e f
  | at {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem} (e' : List Sem) (U : TyM) :
      MovedOfList Γ e e' → dm.readTy Γ d r c i e' f = some U → OMem Γ U f → OField Γ d r c i e f
end

/-- Partial membership IS open membership (the dependent-values unit: the old "below a whole member,
or open" definition admitted junk, `Dep/Records`, and its partly moved form read wrong types). -/
def pmem (Γ : List IndDecl) (s : Sem) (T : TyM) : Prop := dm.OMem Γ T s

theorem pmem_of_mem (Γ : List IndDecl) {s : Sem} {T : TyM} (_hw : s.whole) (h : s ∈ₛ[dm.read] T) :
    dm.pmem Γ s T :=
  .mem h

theorem pmem_moved (Γ : List IndDecl) (T : TyM) : dm.pmem Γ .moved T := .moved T

/-- `MovedOfList` is reflexive. -/
theorem movedOfList_refl' (Γ : List IndDecl) : ∀ (fs : List Sem), MovedOfList Γ fs fs
  | [] => .nil
  | f :: fs => .cons (.refl f) (movedOfList_refl' Γ fs)

theorem movedOfList_append {Γ : List IndDecl} : ∀ {a b c d : List Sem}, MovedOfList Γ a b → MovedOfList Γ c d →
    MovedOfList Γ (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h hs, h' => .cons h (movedOfList_append hs h')

theorem movedOfList_length {Γ : List IndDecl} : ∀ {a b : List Sem}, MovedOfList Γ a b → a.length = b.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hs => by simp [movedOfList_length hs]

end DataModel

end Ochr.Meaning
