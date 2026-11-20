import Ochr.Env

/-!
# Prototype (b2): a data value is its tree; a type carves trees out (docs/34 §4, §7)

Local copies of the definitions that differ from the spine's (`Sem.lean`, `Data.lean`), to be
validated before they are ported:

* **`Val`**, a meaning without the packed carrier element: a constructor value is `dat n r c fs`,
  its declaration's name, its type's RECORD, its constructor and its fields. Nothing in a meaning
  points into a carrier, so meanings can be formed before any carrier exists.
* **Codes with records** (`Code`, `Entry`, `Rec`): a data type's code is its declaration, a small
  record and its carrier. The record keeps what the declaration's field types read of the
  parameters, never a parameter above level 0 (a `Type₀` code cannot hold `Type₀`; §7).
* **Stages** (`lvl`): the carrier of `D` at a record by stages, each stage with the meaning of its
  elements, a field's meaning read by LATER field types through `small` (stage-independent). No
  reading is given from outside: the meaning function is built with the stages.
* **The carrier** (`car`): the elements of the stage equal to their depth, so each member once; its
  meaning (`meanC`) is a bijection onto the members (`Mem`), which are the least set closed under the
  constructors (`mem_iff`). The reading of an element is `meanC`; there is no fixed point to build.
* **Rank**: the depth of a meaning; every field is a subtree (`depth_field_lt`).
-/

namespace Ochr.Meaning.DataModel.Proto

/-- What a later field's type reads of an earlier field: its constructor tree and its non-data
leaves, without types or records (small, so codes can be keyed by it). -/
inductive Small : Type 1
  | el (A : Type) (a : A)
  | proof
  | node (c : Nat) (fs : List Small)
  | other

/-- One step into a declaration's fields: constructor, field, the earlier fields read small. -/
abbrev Step : Type 1 := Nat × Nat × List Small

mutual
/-- **Level-0 codes.** A data type's code is its declaration, its record and its carrier. A
function type's code is `fn C` here (its telescope is not this prototype's subject). -/
inductive Code : Type → Type 1
  | prop (P : Prop) : Code (PLift P)
  | nat : Code Nat
  | unit : Code Unit
  | fn (C : Type) : Code C
  | data (d : IndDecl) (r : List Step → Entry) (A : Type) : Code A
  | err : Code PEmpty
/-- What a record says at a position: a leaf's code, a data type's declaration and record, or
nothing. -/
inductive Entry : Type 1
  | none
  | leaf (B : Type) (c : Code B)
  | data (d : IndDecl) (r : List Step → Entry)
end

/-- A data type's record: small, read by its declaration's signature (`Sig`). -/
abbrev Rec : Type 1 := List Step → Entry

/-- Level-1 codes, enough for a parameter above level 0 (`Type₀` itself, a type-valued function). -/
inductive Code1 : Type 1 → Type 2
  | lift (A : Type) (c : Code A) : Code1 (ULift A)
  | univ0 : Code1 (ULift Prop)
  | univ1 : Code1 ((A : Type) × Code A)
  | fn (C : Type 1) : Code1 C

/-- The meaning of a type: a code at carrier level 0 or 1. -/
inductive Ty : Type 2
  | t0 (A : Type) (c : Code A)
  | t1 (A : Type 1) (c : Code1 A)

/-- **The meaning of a value**, without a packed carrier element. -/
inductive Val : Type 2
  | el0 (A : Type) (a : A)
  | el1 (A : Type 1) (a : A)
  | ty (T : Ty)
  | proof
  | moved
  | dat (n : String) (r : Rec) (c : Nat) (fs : List Val)
  | err

mutual
/-- A meaning read small. -/
def Val.small : Val → Small
  | .el0 A a => .el A a
  | .proof => .proof
  | .dat _ _ c fs => .node c (Val.smallList fs)
  | _ => .other
def Val.smallList : List Val → List Small
  | [] => []
  | v :: vs => v.small :: Val.smallList vs
end

theorem Val.smallList_eq (vs : List Val) : Val.smallList vs = vs.map Val.small := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Val.smallList, ih]

mutual
/-- The depth of a meaning: constructor values nested. -/
def Val.depth : Val → Nat
  | .dat _ _ _ fs => Val.depthList fs + 1
  | _ => 0
/-- The largest depth in a list. -/
def Val.depthList : List Val → Nat
  | [] => 0
  | v :: vs => max v.depth (Val.depthList vs)
end

theorem Val.depth_le_depthList : ∀ (vs : List Val) (v : Val), v ∈ vs → v.depth ≤ Val.depthList vs
  | [], _, h => by cases h
  | w :: ws, v, h => by
    simp only [Val.depthList]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (Val.depth_le_depthList ws v h) (Nat.le_max_right _ _)

/-- **Every field of a constructor value has smaller depth**: the rank of a meaning decreases
along every field step, through any declaration (docs/34 §2.2). -/
theorem Val.depth_field_lt (n : String) (r : Rec) (c : Nat) (fs : List Val) (v : Val) (h : v ∈ fs) :
    v.depth < (Val.dat n r c fs).depth := by
  simp only [Val.depth]
  exact Nat.lt_succ_of_le (Val.depth_le_depthList fs v h)

/-- A meaning holds no `moved` part and is not the error value. -/
def Val.whole : Val → Prop
  | .moved => False
  | .err => False
  | .dat _ _ _ fs => ∀ f ∈ fs, f.whole
  | _ => True

end Ochr.Meaning.DataModel.Proto
