import Ochr.Env

/-!
# The semantic domain: meanings of types (`TyM`, codes) and of values (`Sem`)

The set model of `ochr/docs/18` §3, built from Lean's own types (docs/24). A type means a CODE
closed under the type formers, as Lean's tagged types do (Carneiro §6.4; docs/31 D59): a function
type's code gives the code of the rest of its telescope as a function of each argument, a data
type's code names its declaration and parameters, and a universe decodes to the codes of the level
below. Every type the reference run holds (a call's result, a computed function type, a field's
type, a type passed through a universe parameter) therefore keeps its structure by construction.

Lean cannot define codes together with their decoding (induction-recursion), so each code is
INDEXED by the Lean type it decodes to: `Code0 A` is a code whose carrier is `A`. The codes hold
no meaning (`Sem`), so they are small, and `Type₀` can decode to `(A : Type) × Code0 A`.

What a *value* means must be nameable without its type (a state is a function from positions to
meanings, and `Eq` compares two meanings), so meanings live in one untyped universe `Sem`, whose
elements are tagged by the Lean type they belong to; a constructor value describes itself (`dat`,
docs/31 D32). A value is a member of a type when it is the encoding of an element of the type's
carrier (Lean: elements are taken from the decoding).

A data type's code names its declaration, its parameters and its carrier, and nothing more
(docs/31 D61): an element's constructor and fields are read through the data model (`DataRead`),
which every run has, so encoding, decoding and membership take it as an argument. As Lean's model
codes a W-type by its index set and family and never by its own decoding, no code holds a code of
the type it is the code of, so a recursive or nested declaration (`List`, `Rose(A)` with a field
`List(Rose(A))`) has a code like any other.

## Levels (Q1, docs/18)

Ochr's `sort 0 = Prop`, `sort 1 = Type₀`, `sort 2 = Type₁`, with `Prop : Type₁` beside
`Type₀ : Type₁` (`sortSucc`). The model fixes the levels a program may write: `Prop`, `Type₀`,
`Type₁` (`LevelsBelow 2`, `Bounded.lean`). There is one code family per carrier level: `Code0`
(carriers in `Type`: propositions and `Type₀` types), `Code1` (`Type 1`: `Type₁` types, the
universes `Prop` and `Type₀`, lower codes lifted), `Code2` (`Type 2`: `Type₂` types and `Type₁`).
-/

namespace Ochr.Meaning

universe u

/-- What a call returning `&U` from borrowed places with final contents `Fin` gives back: the
returned borrow's content at return, and an injective backward function from the value the
caller leaves in it to the final contents (`Slice.lean`'s `Back`). -/
def Back (Fin U : Type u) : Type u := {p : U × (U → Fin) // ∀ v w, p.2 v = p.2 w → v = w}

/-- The final contents accumulated after a parameter: a borrow parameter adds its content. -/
abbrev extFin (b : Bool) (Fin T : Type u) : Type u := match b with | true => Fin × T | false => Fin

/-- **A telescope code** over a level's code family, indexed by the final contents of the borrow
parameters seen so far and by the carrier it decodes to. A function with borrow parameters means a
function from the parameters' starting contents to the result and the borrowed places' final
contents: `dat B c` decodes to `B × Fin`; a returned borrow `&U` decodes to `Back Fin U`, the
forward value with an injective backward function (docs/18's relation R folded in); `param` decodes
to `(a : A) → C a`, and `k a` is the rest of the telescope at the parameter's element `a`, as
Lean's `(Π, A, B)` with `B` a function from `A`'s elements to codes. -/
inductive Tel (Code : Type u → Type (u + 1)) : Type u → Type u → Type (u + 1)
  | dat (Fin B : Type u) (c : Code B) : Tel Code Fin (B × Fin)
  | ref (Fin U : Type u) (c : Code U) : Tel Code Fin (Back Fin U)
  | param (Fin : Type u) (isRef : Bool) (A : Type u) (c : Code A) (C : A → Type u)
      (k : (a : A) → Tel Code (extFin isRef Fin A) (C a)) : Tel Code Fin ((a : A) → C a)

/-- What a later field's type reads of an earlier field: its constructor tree and its leaves,
without types or records (docs/34 §8). Small, so a record can be keyed by it. -/
inductive Small : Type 1
  | el (A : Type) (a : A)
  | proof
  | node (c : Nat) (fs : List Small)
  | other

/-- One step into a declaration's fields: constructor, field, the earlier fields read small. -/
abbrev RStep : Type 1 := Nat × Nat × List Small

mutual
/-- **Codes of carrier level 0** (`Type₀` types and propositions), indexed by their carrier: a
proposition (decoding to `PLift P`), `Nat`, `Unit`, a data type (its declaration, its RECORD and
its carrier; docs/34 §8: a record keeps what the declaration's field types read of the
parameters, never a parameter above level 0, which no `Type₀` code can hold), a function type (a
telescope code), and the error code (no elements). -/
inductive Code0 : Type → Type 1
  | prop (P : Prop) : Code0 (PLift P)
  | nat : Code0 Nat
  | unit : Code0 Unit
  | data (d : IndDecl) (r : List RStep → Entry) (A : Type) : Code0 A
  | pi (C : Type) (t : Tel Code0 PUnit C) : Code0 C
  | err : Code0 PEmpty
/-- What a record says at a key: a leaf's code, a data type's declaration (its record is the
record's CONTINUATION past the key, never held here: docs/34 §18), a level-0 value parameter read
small (at `paramKey`, docs/34 Handoff 3b), or nothing. -/
inductive Entry : Type 1
  | none
  | leaf (B : Type) (c : Code0 B)
  | data (d : IndDecl)
  | small (s : Small)
end

/-- **A data type's record** (docs/34 §8, §14, §18): what its declaration's field types read of the
parameters, keyed by paths of steps; small, so codes stay small. A function of paths: the record of
the data type at a key is the continuation past the key (`DataLib.contRec`), so no entry holds a
record, and a record may mention itself (a recursive or nested field) without an infinite descent. -/
abbrev Rec : Type 1 := List RStep → Entry

/-- The sort a level-0 code is a type of: `0` for a proposition, `1` for a `Type₀` type. -/
def Code0.level : {A : Type} → Code0 A → Option Nat
  | _, .prop _ => some 0
  | _, .err => none
  | _, _ => some 1

/-- **Codes of carrier level 1**: a level-0 code lifted; the universe `Prop`, decoding to the
propositions (untagged, as Lean's `T₀ = U₀`); the universe `Type₀`, decoding to the codes of
`Type₀` types (Lean's `⦇(U, 0)⦈ = T₀`); a function type at `Type₁`. -/
inductive Code1 : Type 1 → Type 2
  | lift (A : Type) (c : Code0 A) : Code1 (ULift.{1} A)
  | univ0 : Code1 (ULift.{1} Prop)
  | univ1 : Code1 ((A : Type) × {c : Code0 A // c.level = some 1})
  | pi (C : Type 1) (t : Tel Code1 PUnit C) : Code1 C

def Code1.level : {A : Type 1} → Code1 A → Option Nat
  | _, .lift _ c => c.level
  | _, .univ0 => some 2
  | _, .univ1 => some 2
  | _, .pi .. => some 2

/-- **Codes of carrier level 2**: a level-1 code lifted; the universe `Type₁`, decoding to the
codes of `Type₁` types (`Prop` and `Type₀` among them); a function type at `Type₂`. -/
inductive Code2 : Type 2 → Type 3
  | lift (A : Type 1) (c : Code1 A) : Code2 (ULift.{2} A)
  | univ2 : Code2 ((A : Type 1) × {c : Code1 A // c.level = some 2})
  | pi (C : Type 2) (t : Tel Code2 PUnit C) : Code2 C

def Code2.level : {A : Type 2} → Code2 A → Option Nat
  | _, .lift _ c => c.level
  | _, .univ2 => some 3
  | _, .pi .. => some 3

/-- **The meaning of a type**: a code at one of the three carrier levels. -/
inductive TyM : Type 3 where
  | t0 (A : Type) (c : Code0 A)
  | t1 (A : Type 1) (c : Code1 A)
  | t2 (A : Type 2) (c : Code2 A)

/-- The meaning of a value, tagged by its carrier. `proof` is `•`, the one element of every true
proposition; `ty T` a type used as a value; `moved` is `⊥`, a place definitely moved out of
(D84: a definite value, equal only to itself); `err` is the error value.

A constructor value describes itself (docs/31 D32, docs/34 §14): `dat name r c fs` is a TREE, its
declaration's name, its type's record, its constructor and its fields' meanings, whole, partly
moved or open alike. It holds no element of a carrier: whether it is a member of its type is the
data model's predicate on trees (`DataModel.Mem`), so meanings exist before any carrier. A partly
moved number `S(⊥)` is `dat "Nat" natRec 1 [⊥]`; a whole number is `el0 Nat n`. -/
inductive Sem : Type 3 where
  | el0 (A : Type) (a : A)
  | el1 (A : Type 1) (a : A)
  | el2 (A : Type 2) (a : A)
  | ty (T : TyM)
  | proof
  | moved
  | dat (name : String) (r : Rec) (c : Nat) (fs : List Sem)
  | err

/-- **How a data element is read** (docs/31 D61, docs/34 §14): an element of a carrier, at its
declaration and record, read as its whole meaning (the data model's bijection between a carrier
and its members). Injective, so encoding is. -/
structure DataRead : Type 3 where
  read : IndDecl → Rec → (A : Type) → A → Sem
  inj : ∀ d r A, Function.Injective (read d r A)

/-! ## Types as codes: the common ones and their views -/

namespace TyM

/-- The error type (ill-formed: no derivation reaches one; it has no members). -/
def err : TyM := .t0 PEmpty .err
/-- A proposition. -/
def prop (P : Prop) : TyM := .t0 (PLift P) (.prop P)
/-- `Nat` and `Unit`. -/
def nat : TyM := .t0 Nat .nat
def unit : TyM := .t0 Unit .unit
/-- The universe `sort l`: `Prop` and `Type₀` at carrier level 1, `Type₁` at level 2; above the
bounded levels, the error type. -/
def univ : Nat → TyM
  | 0 => .t1 _ .univ0
  | 1 => .t1 _ .univ1
  | 2 => .t2 _ .univ2
  | _ => err

/-- A level-1 code as a type, a lifted level-0 code read at its own level. -/
def of1 : {A : Type 1} → Code1 A → TyM
  | _, .lift A c => .t0 A c
  | _, c => .t1 _ c

/-- A level-2 code as a type, lifted codes read at their own level. -/
def of2 : {A : Type 2} → Code2 A → TyM
  | _, .lift _ c => of1 c
  | _, c => .t2 _ c

/-- Ochr's level of a type: the `l` of the `sort l` it is an element of. -/
def level : TyM → Option Nat
  | .t0 _ c => c.level
  | .t1 _ c => c.level
  | .t2 _ c => c.level

/-- The error type, recognised. -/
def isErr : TyM → Bool
  | .t0 _ .err => true
  | _ => false

/-- A function type (its code is a telescope). -/
def isPi : TyM → Bool
  | .t0 _ (.pi ..) | .t1 _ (.pi ..) | .t2 _ (.pi ..) => true
  | _ => false

/-- A proposition's meaning is true. -/
def true : TyM → Prop
  | .t0 _ (.prop P) => P
  | _ => False

/-- The code of a type read at carrier level 0 (the error code at a higher level). -/
def code0 : TyM → (A : Type) × Code0 A
  | .t0 A c => ⟨A, c⟩
  | _ => ⟨PEmpty, .err⟩

/-- The code of a type read at carrier level 1 (a level-0 code lifted). -/
def code1 : TyM → (A : Type 1) × Code1 A
  | .t0 A c => ⟨ULift A, .lift A c⟩
  | .t1 A c => ⟨A, c⟩
  | .t2 _ _ => ⟨ULift PEmpty, .lift _ .err⟩

/-- The code of a type read at carrier level 2 (lower codes lifted). -/
def code2 : TyM → (A : Type 2) × Code2 A
  | .t0 A c => ⟨ULift (ULift A), .lift _ (.lift A c)⟩
  | .t1 A c => ⟨ULift A, .lift A c⟩
  | .t2 A c => ⟨A, c⟩

/-- The carriers at each level (`PEmpty` above the level; lower levels lifted). -/
abbrev el0 (T : TyM) : Type := T.code0.1
abbrev el1 (T : TyM) : Type 1 := T.code1.1
abbrev el2 (T : TyM) : Type 2 := T.code2.1

end TyM

theorem false_not_true : ¬ (TyM.prop False).true := id

/-! ## Encoding an element of a carrier as a meaning -/

section
variable (R : DataRead)

/-- A level-0 element as a meaning: a proof is `•`, a data element its meaning as the data model
reads it (a constructor value recording its type's record), anything else is tagged by its
carrier. -/
def Code0.enc : {A : Type} → Code0 A → A → Sem
  | _, .prop _, _ => .proof
  | _, .nat, n => .el0 Nat n
  | _, .unit, x => .el0 Unit x
  | _, .data d r A, a => R.read d r A a
  | _, .pi C _, f => .el0 C f
  | _, .err, x => nomatch x

/-- A level-1 element as a meaning: a lifted element as itself, a proposition or a `Type₀` code as
the type value it is, a function by its tag. -/
def Code1.enc : {A : Type 1} → Code1 A → A → Sem
  | _, .lift _ c, a => c.enc R a.down
  | _, .univ0, P => .ty (.prop P.down)
  | _, .univ1, p => .ty (.t0 p.1 p.2.1)
  | _, .pi C _, f => .el1 C f

/-- A level-2 element as a meaning. -/
def Code2.enc : {A : Type 2} → Code2 A → A → Sem
  | _, .lift _ c, a => c.enc R a.down
  | _, .univ2, p => .ty (.t1 p.1 p.2.1)
  | _, .pi C _, f => .el2 C f

open Classical in
/-- Decoding a meaning at a code: its preimage under the encoding, if it has one (the encoding is
injective, `Code0.enc_inj`). -/
noncomputable def Code0.dec {A : Type} (c : Code0 A) (s : Sem) : Option A :=
  if h : ∃ a, c.enc R a = s then some h.choose else none

open Classical in
noncomputable def Code1.dec {A : Type 1} (c : Code1 A) (s : Sem) : Option A :=
  if h : ∃ a, c.enc R a = s then some h.choose else none

open Classical in
noncomputable def Code2.dec {A : Type 2} (c : Code2 A) (s : Sem) : Option A :=
  if h : ∃ a, c.enc R a = s then some h.choose else none

/-- The declaration's name and record a data type's code carries. -/
def TyM.dataRec? : TyM → Option (String × Rec)
  | .t0 _ (.data d r _) => some (d.name, r)
  | _ => none

/-- **Membership**: a meaning lies in a type when it is the encoding of an element of the type's
carrier (Lean: a type's elements are taken from its code's decoding). An element is a member of
the carrier it is tagged with; `•` of every true proposition; a type value of the universe of its
level; a constructor value of the data type it names, when it describes an element. -/
def Sem.mem (s : Sem) : TyM → Prop
  | .t0 _ c => ∃ a, c.enc R a = s
  | .t1 _ c => ∃ a, c.enc R a = s
  | .t2 _ c => ∃ a, c.enc R a = s

end

/-- Membership, the data model's reading `R` explicit. -/
scoped notation:50 s:51 " ∈ₛ[" R "] " T:51 => Sem.mem R s T

/-- Read a meaning as a type. -/
def Sem.asTy : Sem → TyM
  | .ty T => T
  | _ => .err

/-- A meaning holds no `moved` part and is not the error value. -/
def Sem.whole : Sem → Prop
  | .moved => False
  | .err => False
  | .dat _ _ _ fs => ∀ f ∈ fs, f.whole
  | _ => True

/-- The reading gives whole fields: what makes an encoding whole (`Steps/Records.lean`,
`enc_whole_lvl0`), so that the record a borrow-returning call makes is whole (docs/31 D68). A fact
about the data model, owed where the reading is fixed (`Assembly.exists_dataModel`). -/
def DataRead.WholeFields (R : DataRead) : Prop :=
  ∀ d r A a, (R.read d r A a).whole

/-- The record of the numbers' partly moved form (`Nat` is not a declaration). -/
def natRec : Rec := fun _ => .none

mutual
/-- A meaning read small (docs/34 §8): its constructor tree and its leaves, no records. -/
def Sem.small : Sem → Small
  | .el0 A a => .el A a
  | .proof => .proof
  | .dat _ _ c fs => .node c (Sem.smallList fs)
  | _ => .other
def Sem.smallList : List Sem → List Small
  | [] => []
  | v :: vs => v.small :: Sem.smallList vs
end

theorem Sem.smallList_eq (vs : List Sem) : Sem.smallList vs = vs.map Sem.small := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Sem.smallList, ih]

mutual
/-- **A meaning rebuilt from its small reading** (what the run's constructor clause solves a value
parameter to from the `.small` entry a record keeps): a leaf as itself, a constructor tree under
no declaration and no record. Its small reading is the one it was built from (`small_ofSmall`),
which is all a record reads of a value parameter (`RecordsFaithful`). -/
def ofSmall : Small → Sem
  | .el A a => .el0 A a
  | .proof => .proof
  | .node c fs => .dat "" natRec c (ofSmallList fs)
  | .other => .err
def ofSmallList : List Small → List Sem
  | [] => []
  | s :: ss => ofSmall s :: ofSmallList ss
end

mutual
theorem small_ofSmall : ∀ s : Small, (ofSmall s).small = s
  | .el _ _ => rfl
  | .proof => rfl
  | .node c fs => by
    show Small.node c (Sem.smallList (ofSmallList fs)) = Small.node c fs
    rw [smallList_ofSmallList fs]
  | .other => rfl
theorem smallList_ofSmallList : ∀ ss : List Small, Sem.smallList (ofSmallList ss) = ss
  | [] => rfl
  | s :: ss => by
    show (ofSmall s).small :: Sem.smallList (ofSmallList ss) = s :: ss
    rw [small_ofSmall s, smallList_ofSmallList ss]
end

mutual
/-- The information order used by the step lemmas (docs/18 Def. "less informative"): `moved` is
below everything, `ctor` is compared componentwise, everything else only with itself. Under D84
`⊥` is a definite value, so this is not an information order on observations: it is the device
that lets the main theorem conclude equality at a whole leaf (`le_eq_of_whole`) while a borrow
holder forgotten by an early end (`Pick`) stays below the reference. -/
inductive Sem.le : Sem → Sem → Prop
  | moved (s : Sem) : Sem.le .moved s
  | refl (s : Sem) : Sem.le s s
  | dat {n r c} {fs gs : List Sem} : Sem.leList fs gs → Sem.le (.dat n r c fs) (.dat n r c gs)

/-- The order pointwise on lists of the same length. -/
inductive Sem.leList : List Sem → List Sem → Prop
  | nil : Sem.leList [] []
  | cons {f g fs gs} : Sem.le f g → Sem.leList fs gs → Sem.leList (f :: fs) (g :: gs)
end

scoped infix:50 " ⊑ " => Sem.le

theorem Sem.le_refl (s : Sem) : s ⊑ s := .refl s

mutual
/-- A whole meaning below another equals it: on whole values the order is equality. -/
theorem Sem.le_eq_of_whole : ∀ {s t : Sem}, s ⊑ t → s.whole → s = t
  | _, _, .moved _, hw => by simp [Sem.whole] at hw
  | _, _, .refl _, _ => rfl
  | _, _, .dat h, hw => by
    simp only [Sem.whole] at hw
    rw [Sem.leList_eq_of_whole h hw]

theorem Sem.leList_eq_of_whole : ∀ {fs gs : List Sem}, Sem.leList fs gs → (∀ f ∈ fs, f.whole) → fs = gs
  | _, _, .nil, _ => rfl
  | _, _, .cons h hs, hw => by
    rw [Sem.le_eq_of_whole h (hw _ (List.mem_cons_self ..)),
      Sem.leList_eq_of_whole hs fun f hf => hw f (List.mem_cons_of_mem _ hf)]
end

mutual
theorem Sem.le_trans : ∀ {a b c : Sem}, a ⊑ b → b ⊑ c → a ⊑ c
  | _, _, _, .moved _, _ => .moved _
  | _, _, _, .refl _, h => h
  | _, _, _, .dat h₁, .refl _ => .dat h₁
  | _, _, _, .dat h₁, .dat h₂ => .dat (Sem.leList_trans h₁ h₂)

theorem Sem.leList_trans : ∀ {a b c : List Sem}, Sem.leList a b → Sem.leList b c → Sem.leList a c
  | _, _, _, .nil, h => h
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ => .cons (Sem.le_trans h₁ h₂) (Sem.leList_trans hs₁ hs₂)
end

/-! ## The encodings are injective, so decoding inverts them -/

section
variable (R : DataRead)

/-- A function of a code respects heterogeneous equality of codes over equal carriers. -/
theorem Code0.congr_heq {X : Sort _} (f : {A : Type} → Code0 A → X) :
    ∀ {A A' : Type} (c : Code0 A) (c' : Code0 A'), A = A' → HEq c c' → f c = f c' := by
  intro A A' c c' h hh; subst h; cases hh; rfl

/-- The proposition a level-0 code is (`False` for any other code). -/
def Code0.propOf : {A : Type} → Code0 A → Prop
  | _, .prop P => P
  | _, _ => False

theorem Code0.enc_inj : ∀ {A : Type} (c : Code0 A) {a b : A}, c.enc R a = c.enc R b → a = b
  | _, .prop _, a, b, _ => by cases a; cases b; rfl
  | _, .nat, _, _, h => by simp only [Code0.enc, Sem.el0.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .unit, _, _, _ => Subsingleton.elim _ _
  | _, .data d r A, _, _, h => R.inj d r A h
  | _, .pi .., _, _, h => by simp only [Code0.enc, Sem.el0.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .err, a, _, _ => nomatch a

theorem TyM.t0_inj {A A' : Type} {c : Code0 A} {c' : Code0 A'} (h : TyM.t0 A c = TyM.t0 A' c') :
    A = A' ∧ HEq c c' := by
  cases h; exact ⟨rfl, HEq.rfl⟩

theorem Code1.enc_inj : ∀ {A : Type 1} (c : Code1 A) {a b : A}, c.enc R a = c.enc R b → a = b
  | _, .lift _ c, a, b, h => by
    have := Code0.enc_inj R c h
    cases a; cases b; cases this; rfl
  | _, .univ0, a, b, h => by
    simp only [Code1.enc, Sem.ty.injEq, TyM.prop] at h
    obtain ⟨e, hh⟩ := TyM.t0_inj h
    have := Code0.congr_heq Code0.propOf _ _ e hh
    cases a; cases b; simp only [Code0.propOf] at this; cases this; rfl
  | _, .univ1, ⟨A, c, hc⟩, ⟨A', c', hc'⟩, h => by
    simp only [Code1.enc, Sem.ty.injEq] at h
    obtain ⟨e, hh⟩ := TyM.t0_inj h
    subst e; cases hh; rfl
  | _, .pi .., _, _, h => by simp only [Code1.enc, Sem.el1.injEq, heq_eq_eq, true_and] at h; exact h

theorem TyM.t1_inj {A A' : Type 1} {c : Code1 A} {c' : Code1 A'} (h : TyM.t1 A c = TyM.t1 A' c') :
    A = A' ∧ HEq c c' := by
  cases h; exact ⟨rfl, HEq.rfl⟩

theorem Code2.enc_inj : ∀ {A : Type 2} (c : Code2 A) {a b : A}, c.enc R a = c.enc R b → a = b
  | _, .lift _ c, a, b, h => by
    have := Code1.enc_inj R c h
    cases a; cases b; cases this; rfl
  | _, .univ2, ⟨A, c, hc⟩, ⟨A', c', hc'⟩, h => by
    simp only [Code2.enc, Sem.ty.injEq] at h
    obtain ⟨e, hh⟩ := TyM.t1_inj h
    subst e; cases hh; rfl
  | _, .pi .., _, _, h => by simp only [Code2.enc, Sem.el2.injEq, heq_eq_eq, true_and] at h; exact h

theorem Code0.dec_enc {A : Type} (c : Code0 A) (a : A) : c.dec R (c.enc R a) = some a := by
  have h : ∃ a', c.enc R a' = c.enc R a := ⟨a, rfl⟩
  simp only [Code0.dec, dif_pos h, Option.some.injEq]
  exact Code0.enc_inj R c h.choose_spec

theorem Code1.dec_enc {A : Type 1} (c : Code1 A) (a : A) : c.dec R (c.enc R a) = some a := by
  have h : ∃ a', c.enc R a' = c.enc R a := ⟨a, rfl⟩
  simp only [Code1.dec, dif_pos h, Option.some.injEq]
  exact Code1.enc_inj R c h.choose_spec

theorem Code2.dec_enc {A : Type 2} (c : Code2 A) (a : A) : c.dec R (c.enc R a) = some a := by
  have h : ∃ a', c.enc R a' = c.enc R a := ⟨a, rfl⟩
  simp only [Code2.dec, dif_pos h, Option.some.injEq]
  exact Code2.enc_inj R c h.choose_spec

theorem Code0.enc_of_dec {A : Type} (c : Code0 A) {s : Sem} {a : A} (h : c.dec R s = some a) : c.enc R a = s := by
  unfold Code0.dec at h
  split at h
  · rename_i hx; cases h; exact hx.choose_spec
  · cases h

theorem Code1.enc_of_dec {A : Type 1} (c : Code1 A) {s : Sem} {a : A} (h : c.dec R s = some a) : c.enc R a = s := by
  unfold Code1.dec at h
  split at h
  · rename_i hx; cases h; exact hx.choose_spec
  · cases h

theorem Code2.enc_of_dec {A : Type 2} (c : Code2 A) {s : Sem} {a : A} (h : c.dec R s = some a) : c.enc R a = s := by
  unfold Code2.dec at h
  split at h
  · rename_i hx; cases h; exact hx.choose_spec
  · cases h

/-- Decoding succeeds exactly on the encodings. -/
theorem Code0.dec_isSome {A : Type} (c : Code0 A) (s : Sem) : (c.dec R s).isSome ↔ ∃ a, c.enc R a = s := by
  unfold Code0.dec; split <;> simp_all

theorem Code1.dec_isSome {A : Type 1} (c : Code1 A) (s : Sem) : (c.dec R s).isSome ↔ ∃ a, c.enc R a = s := by
  unfold Code1.dec; split <;> simp_all

theorem Code2.dec_isSome {A : Type 2} (c : Code2 A) (s : Sem) : (c.dec R s).isSome ↔ ∃ a, c.enc R a = s := by
  unfold Code2.dec; split <;> simp_all

end

end Ochr.Meaning
