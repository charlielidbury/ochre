import Ochr.Env

/-!
# The data layer before docs/34's port: a frozen copy, for the records against it

A copy of `Sem.lean` and `Data.lean` as they stood on `spine` at 34ecffdd, under
`Ochr.Meaning.Old`: a constructor value's meaning held its parameters and packed carrier element
(`Sem.dat n ps c fs el`), a data type's code held its parameters (`Code0.data d ps A`), and a data
model gave carriers, packing, tags, fields and a rank, with laws. The records of what was wrong
with that layer (`Counterexamples.lean`, `RankCounterexample.lean`, docs/34 §2) are kernel-checked
against this copy. Nothing else uses it.
-/

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

namespace Ochr.Meaning.Old

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

mutual
/-- **Codes of carrier level 0** (`Type₀` types and propositions), indexed by their carrier: a
proposition (decoding to `PLift P`), `Nat`, `Unit`, a data type (its declaration, its parameters
as codes and coded values, and its carrier; its elements are read through the data model, D61), a
function type (a telescope code), and the error code (no elements). -/
inductive Code0 : Type → Type 1
  | prop (P : Prop) : Code0 (PLift P)
  | nat : Code0 Nat
  | unit : Code0 Unit
  | data (d : IndDecl) (ps : List Par0) (A : Type) : Code0 A
  | pi (C : Type) (t : Tel Code0 PUnit C) : Code0 C
  | err : Code0 PEmpty
/-- A coded element (a value parameter of a data type): a carrier, its code, an element; or
nothing (a parameter not of its declared type, which no well-typed value has). -/
inductive Elt0 : Type 1
  | mk (B : Type) (c : Code0 B) (b : B)
  | bad
/-- A data type's parameter: a type (as its code), or a coded value. -/
inductive Par0 : Type 1
  | ty (A : Type) (c : Code0 A)
  | val (e : Elt0)
end

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

A constructor value describes itself (docs/31 D32): `dat name ps c fs el` is its declaration's
name, its parameters' meanings, its constructor and its fields' meanings, and `el` its element of
the carrier when it is whole and of its type (`DataModel.ctorM` packs it), `none` when a field is
moved out or the value is open. A partly moved number `S(⊥)` is `dat "Nat" [] 1 [⊥] none`; a whole
number is `el0 Nat n`. -/
inductive Sem : Type 3 where
  | el0 (A : Type) (a : A)
  | el1 (A : Type 1) (a : A)
  | el2 (A : Type 2) (a : A)
  | ty (T : TyM)
  | proof
  | moved
  | dat (name : String) (ps : List Sem) (c : Nat) (fs : List Sem) (el : Option ((A : Type) × A))
  | err

/-- **How a data value is read** (docs/31 D61): an element of a declaration's carrier at its
parameters' meanings, read as its constructor and its fields' meanings. The data model gives it
(`DataModel.read`); a code does not hold it. -/
abbrev DataRead : Type 3 := IndDecl → List Sem → (A : Type) → A → Nat × List Sem

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

mutual
/-- A level-0 element as a meaning: a proof is `•`, a data element is the constructor value that
describes it (its constructor and fields read through the data model, `R`), anything else is
tagged by its carrier. -/
def Code0.enc : {A : Type} → Code0 A → A → Sem
  | _, .prop _, _ => .proof
  | _, .nat, n => .el0 Nat n
  | _, .unit, x => .el0 Unit x
  | _, .data d ps A, a => .dat d.name (Par0.sems ps) (R d (Par0.sems ps) A a).1 (R d (Par0.sems ps) A a).2 (some ⟨A, a⟩)
  | _, .pi C _, f => .el0 C f
  | _, .err, x => nomatch x
def Elt0.sem : Elt0 → Sem
  | .mk _ c b => Code0.enc c b
  | .bad => .err
def Par0.sem : Par0 → Sem
  | .ty A c => .ty (.t0 A c)
  | .val e => e.sem
def Par0.sems : List Par0 → List Sem
  | [] => []
  | p :: ps => p.sem :: Par0.sems ps
end

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

/-- The declaration's name and parameters' meanings a data type's code carries. -/
def TyM.dataName? : TyM → Option (String × List Sem)
  | .t0 _ (.data d ps _) => some (d.name, Par0.sems R ps)
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

/-- The element of a carrier a constructor value packs, if it is whole and of its type (what
guarded recursion ranks, `semRank`). -/
def Sem.elt : Sem → Option ((A : Type) × A)
  | .dat _ _ _ _ el => el
  | _ => none

/-- Read a meaning as a type. -/
def Sem.asTy : Sem → TyM
  | .ty T => T
  | _ => .err

/-- A meaning holds no `moved` part and is not the error value. -/
def Sem.whole : Sem → Prop
  | .moved => False
  | .err => False
  | .dat _ _ _ fs _ => ∀ f ∈ fs, f.whole   -- whole fields and no element: an OPEN (ill-typed) value
  | _ => True

/-- The reading gives whole fields: what makes an encoding whole (`Steps/Records.lean`,
`enc_whole_lvl0`), so that the record a borrow-returning call makes is whole (docs/31 D68). A fact
about the data model, owed where the reading is fixed (`Assembly.exists_dataModel`). -/
def DataRead.WholeFields (R : DataRead) : Prop :=
  ∀ d ps A a, ∀ f ∈ (R d ps A a).2, Sem.whole f

mutual
/-- The information order used by the step lemmas (docs/18 Def. "less informative"): `moved` is
below everything, `ctor` is compared componentwise, everything else only with itself. Under D84
`⊥` is a definite value, so this is not an information order on observations: it is the device
that lets the main theorem conclude equality at a whole leaf (`le_eq_of_whole`) while a borrow
holder forgotten by an early end (`Pick`) stays below the reference. -/
inductive Sem.le : Sem → Sem → Prop
  | moved (s : Sem) : Sem.le .moved s
  | refl (s : Sem) : Sem.le s s
  | dat {n ps c} {fs gs : List Sem} : Sem.leList fs gs → Sem.le (.dat n ps c fs none) (.dat n ps c gs none)

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
  | _, .data .., _, _, h => by
    simp only [Code0.enc, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2
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

end Ochr.Meaning.Old

/-!
# The model of inductive types

An inductive declaration means, at each tuple of parameter meanings, the least family of sets
closed under its constructors (docs/18 Def. "meaning of types"). In Lean that family is a small
type built by the stage construction of `Ochr/Model/Slice.lean` §4 generalised to telescopes
(stage `k + 1` is a `Σ` over constructors of the telescope of field carriers, recursive fields at
stage `k`; the carrier is the colimit). The spine does not fix the construction: it fixes the
*interface* a data type must provide to the step lemmas, `DataModel`, and states its laws. The
library's declarations are modelled by hand (`libModel`, as `Slice.lean` models `Nat` and `Pair`);
the generic construction for every accepted program is milestone 2's `genericDataModel` (Q2).

`Nat` and `Unit` are not declarations (`Value.tNat`, `Value.tUnit`, `zero`, `succ`, `unit`) and
are modelled directly in `Value.lean` as `Nat` and `Unit`.
-/

namespace Ochr.Meaning.Old

/-- The reading of a data model's elements (docs/31 D61) from its carriers, tags and fields: an
element of `D(ps)`'s carrier is its tag and fields; an element of any other type is read as
nothing (no code of `D(ps)` has that carrier). -/
noncomputable def readOf (car : IndDecl → List Sem → Type) (tag : {d : IndDecl} → {ps : List Sem} → car d ps → Nat)
    (fields : {d : IndDecl} → {ps : List Sem} → car d ps → List Sem) : DataRead :=
  fun d ps A a => open Classical in if h : A = car d ps then (tag (cast h a), fields (cast h a)) else (0, [])

theorem readOf_car (car : IndDecl → List Sem → Type) (tag : {d : IndDecl} → {ps : List Sem} → car d ps → Nat)
    (fields : {d : IndDecl} → {ps : List Sem} → car d ps → List Sem) {d : IndDecl} {ps : List Sem} (x : car d ps) :
    readOf car tag fields d ps (car d ps) x = (tag x, fields x) := by
  simp [readOf]

/-- The model of the program's inductive declarations. Parameters are passed as meanings: a
type parameter as `Sem.ty T`, a value parameter (D71) as the value's meaning. `fieldTy d ps c i
earlier` is the meaning of the declared type of field `i` of constructor `c` at the parameters
and the meanings of the earlier fields (the telescope, D64), as the reference run computes it;
it is part of the model because the laws are stated with it. `covers d` says which declarations
the model speaks for; the laws hold for those. -/
structure DataModel where
  covers : IndDecl → Prop
  /-- The carrier of `D(ps)`: a small Lean type. -/
  car : IndDecl → List Sem → Type
  fieldTy : IndDecl → List Sem → Nat → Nat → List Sem → TyM
  /-- The meaning of the declared type of parameter `i` at the earlier parameters (a type
  parameter's is its sort; a value parameter's, D71, a data type). -/
  paramTy : IndDecl → Nat → List Sem → TyM
  /-- The parameters of field `i`'s declared type when it is an occurrence of the declaration
  itself (a recursive field), at the parameters and the earlier fields: what guarded recursion
  reads (`rank_lt`). -/
  recArgs : IndDecl → List Sem → Nat → Nat → List Sem → Option (List Sem) :=
    fun _ _ _ _ _ => none
  /-- Pack a constructor's fields, given as meanings, into an element; `none` if some field is
  not a member of its field type (the fields are read in telescope order). -/
  pack : (d : IndDecl) → (ps : List Sem) → Nat → List Sem → Option (car d ps)
  tag : {d : IndDecl} → {ps : List Sem} → car d ps → Nat
  fields : {d : IndDecl} → {ps : List Sem} → car d ps → List Sem
  /-- The rank, for guarded recursion (docs/24): a recursive field has a smaller rank. -/
  rank : {d : IndDecl} → {ps : List Sem} → car d ps → Nat
  /-- How an element is read as a constructor value (docs/31 D61): what the codes' encoding,
  decoding and membership read a data element through. A data type's code names its declaration,
  parameters and carrier only, so a recursive or nested declaration's element is read here, by
  the model, and never by a code holding the code it is the code of. -/
  read : DataRead := readOf car tag fields
  /-- The reading is the model's: a covered declaration's element is read as its tag and fields
  (by `readOf_car` for the default reading; a model that reads at a reading given from outside,
  as the generic one, owes it as a coherence: docs/31 D61). -/
  read_eq : ∀ {d ps} (x : car d ps), covers d → read d ps (car d ps) x = (tag x, fields x) := by
    intro d ps x _; simp [readOf]
  tag_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → tag x = c
  fields_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → fields x = fs
  /-- Every element is a constructor applied to its fields (the carrier is a least fixed point). -/
  pack_fields : ∀ {d ps} (x : car d ps), covers d → pack d ps (tag x) (fields x) = some x
  /-- Packing succeeds exactly when each field is a member of its field type at the earlier
  fields, and there are as many as the constructor declares. -/
  pack_isSome : ∀ {d ps c fs}, covers d →
    ((pack d ps c fs).isSome ↔
      ∃ ctor, d.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[read] fieldTy d ps c i (fs.take i))
  /-- A recursive field, read at the parameters of its declared occurrence (`recArgs`), has
  smaller rank: the element it packs (`Sem.elt`, what `semRank` ranks) is ranked below. The law
  is stated through the declared type, not through carriers: carriers do not determine
  parameters, and the form "every field whose carrier is the declaration's" is false (in
  `Pair(Pair(Unit, Unit), Unit)` the inner pair packs an element of `car Pair [Unit, Unit]`, a
  field of the outer one at the same rank; with `Nat = Nat × Unit`, consistent with Lean, no rank
  function satisfies it; docs/31, data-generic). As first stated the field was the tagged element
  `el0 (car d ps') y`, which no field has been since D32 (a constructor value describes itself). -/
  rank_lt : ∀ {d ps ps'} (x : car d ps) (y : car d ps'), covers d → ∀ i,
    recArgs d ps (tag x) i ((fields x).take i) = some ps' →
    ((fields x)[i]?).bind Sem.elt = some ⟨car d ps', y⟩ → rank y < rank x

namespace DataModel

variable (dm : DataModel)

/-- A value read as a coded element of the type `T` (its code read at carrier level 0); `bad`
when it is not a member. -/
noncomputable def _root_.Ochr.Meaning.Old.eltOf (R : DataRead) (T : TyM) (s : Sem) : Elt0 :=
  match T.code0.2.dec R s with
  | some b => .mk _ T.code0.2 b
  | none => .bad

/-- A parameter's meaning as a coded parameter of a data type: a type value as its code, a value
as a coded element of the parameter's declared type `T`. -/
noncomputable def _root_.Ochr.Meaning.Old.parOf (R : DataRead) (T : TyM) : Sem → Par0
  | .ty (.t0 A c) => .ty A c
  | s => .val (eltOf R T s)

/-- The parameters of `d` as coded parameters, each at its declared type at the earlier ones. -/
noncomputable def parsOf (d : IndDecl) (i : Nat) (earlier : List Sem) : List Sem → List Par0
  | [] => []
  | p :: ps => parOf dm.read (dm.paramTy d i earlier) p :: parsOf d (i + 1) (earlier ++ [p]) ps

/-- The meaning of the type `D(ps)`: a data type is its code, naming its declaration, its
parameters and its carrier and nothing more (docs/31 D61: its elements are read through the model,
`read`); a `Prop`-sorted declaration the truncation of the same fixed point, true when it is
inhabited. -/
noncomputable def tyM (d : IndDecl) (ps : List Sem) : TyM :=
  if d.sort == 0 then TyM.prop (Nonempty (dm.car d ps))
  else .t0 (dm.car d ps) (.data d (dm.parsOf d 0 [] ps) (dm.car d ps))

/-- The constructor and fields of a constructor value, read off the value (docs/31 D32). -/
def _root_.Ochr.Meaning.Old.Sem.parts : Sem → Option (Nat × List Sem)
  | .dat _ _ c fs _ => some (c, fs)
  | _ => none

/-- A whole constructor value OPEN in the data type `T` (D64): it names `T`'s declaration and
parameters, its fields are whole, and it has no element of the carrier because a field lies
outside the type its earlier fields give (the checker types such a field by its content until
[Repack]). Membership's `pmem` admits it, as the checker's state does (`Regress/OpenWriteDep`). -/
def OpenIn (R : DataRead) : TyM → Sem → Prop
  | .t0 _ (.data d ps _), .dat n' ps' _ fs none => d.name = n' ∧ Par0.sems R ps = ps' ∧ ∀ f ∈ fs, f.whole
  | _, _ => False

/-- The meaning of a constructor value `C(ps; fs)` of a data type whose fields already mean
`fs`: it describes itself (`Sem.dat`, docs/31 D32), with its element of the carrier when every field
is whole and of its type, and none otherwise: when some field holds `moved` (D84: a definite value
lying in no type), and when a whole field is not of its type (an open value). A `Prop`-sorted declaration's constructor values are `⋆` already
(`Machine.evalCtor`, D42), so `ctorM` is only applied to data.

An ill-typed constructor value used to mean `err`, not a tuple. Then a value with a LENT field
meant `err` at every future that gives the field's label a whole value outside its type, and a
read of ANOTHER field failed there, so what [Access] observes of the other field depended on the
lent field's label and the access ended it: the audit's A1 was not fixed for packed data
(docs/31 D25, third lead; `Regress/SiblingAccess.lean`). As a tuple, a constructor value's fields
are read whatever the others hold (`fieldsOf_ctorM`). -/
noncomputable def ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem :=
  open Classical in
  if ∀ f ∈ fs, f.whole then
    match dm.pack d ps c fs with
    | some x => .dat d.name ps c fs (some ⟨dm.car d ps, x⟩)
    | none => .dat d.name ps c fs none
  else .dat d.name ps c fs none

mutual
/-- `s` is `t` with some of its parts moved out: `moved` is anything with all of it moved, a
partly moved tuple is a packed element of its carrier with some fields moved out, and a partly
moved number is a successor whose predecessor is.

This is the order membership of a partly moved value needs, and `Sem.le` is not it (docs/31 D24,
third lead): `Sem.le` compares a tuple only with a tuple, and a whole constructor value is never
a tuple (it is `el0` of its carrier, `ctorM`), so no whole member of any type lay above a partly
moved tuple, and `pmem` as first stated (`∃ t whole, s ⊑ t ∧ t ∈ T`) was FALSE of every partly
moved constructor value (`Regress/PartlyMoved.lean`). A partly moved binding is what every match
that moves a field out leaves, so `Good` failed at the state after it. -/
inductive MovedOf (Γ : List IndDecl) : Sem → Sem → Prop
  | moved (t : Sem) : MovedOf Γ .moved t
  | refl (t : Sem) : MovedOf Γ t t
  | dat {n : String} {ps : List Sem} {c : Nat} {fs gs : List Sem} {el : Option ((A : Type) × A)} :
      MovedOfList Γ fs gs → MovedOf Γ (.dat n ps c fs none) (.dat n ps c gs el)
  | succ {s : Sem} {n : Nat} : MovedOf Γ s (.el0 Nat n) → MovedOf Γ (.dat "Nat" [] 1 [s] none) (.el0 Nat (n + 1))

/-- The same, field by field. -/
inductive MovedOfList (Γ : List IndDecl) : List Sem → List Sem → Prop
  | nil : MovedOfList Γ [] []
  | cons {f g : Sem} {fs gs : List Sem} : MovedOf Γ f g → MovedOfList Γ fs gs → MovedOfList Γ (f :: fs) (g :: gs)
end

/-- Membership for a possibly partly moved value (docs/18 part (b) at a binding holding a value
some field of which was moved out): the value is `⊥` outright, or it is some whole member of the
type with parts moved out (`MovedOf`). For a whole value this is membership (`pmem_of_mem`). A
move keeps it: the value before the move is such a member. -/
def pmem (R : DataRead) (Γ : List IndDecl) (s : Sem) (T : TyM) : Prop :=
  s = .moved ∨ ∃ t : Sem, t.whole ∧ MovedOf Γ s t ∧ (t ∈ₛ[R] T ∨ OpenIn R T t)

theorem pmem_of_mem (R : DataRead) (Γ : List IndDecl) {s : Sem} {T : TyM} (hw : s.whole) (h : s ∈ₛ[R] T) :
    pmem R Γ s T :=
  .inr ⟨s, hw, .refl s, .inl h⟩

/-- No code encodes an element as a constructor value with no element: a constructor value is a
member of a type only when it packs an element of the carrier. -/
theorem _root_.Ochr.Meaning.Old.Code0.enc_ne_dat_none (R : DataRead) {A : Type} (c : Code0 A) (a : A) (n : String)
    (ps : List Sem) (k : Nat) (fs : List Sem) : c.enc R a ≠ .dat n ps k fs none := by
  cases c with
  | err => exact a.elim
  | _ => simp [Code0.enc]

theorem _root_.Ochr.Meaning.Old.Sem.not_mem_dat_none (R : DataRead) (n : String) (ps : List Sem) (k : Nat)
    (fs : List Sem) (T : TyM) : ¬ (Sem.dat n ps k fs none ∈ₛ[R] T) := by
  rintro h
  cases T with
  | t0 A c => obtain ⟨a, ha⟩ := h; exact Code0.enc_ne_dat_none R c a n ps k fs ha
  | t1 A c =>
    obtain ⟨a, ha⟩ := h
    cases c with
    | lift _ c₀ => exact Code0.enc_ne_dat_none R c₀ a.down n ps k fs ha
    | _ => simp [Code1.enc] at ha
  | t2 A c =>
    obtain ⟨a, ha⟩ := h
    cases c with
    | lift _ c₁ =>
      cases c₁ with
      | lift _ c₀ => exact Code0.enc_ne_dat_none R c₀ a.down.down n ps k fs ha
      | _ => simp [Code1.enc, Code2.enc] at ha
    | _ => simp [Code2.enc] at ha

/-- **The parameters of `D(ps)` are read back from its code** (docs/31 D61): each a level-0 type
value or a member of its declared type (`parsOf_sems`). With the model's reading of a covered
declaration (`read_eq`), it is all a packed element needs to be a member of its type
(`ctor_mem_tyM`), for every declaration, recursive and nested ones included: the code reads no
field. (D59's `CodeFaithful` also asked the code to read every element's fields back, which a
recursive declaration's code could do only by stages and a nested one's not at all.) -/
def ParamsCoded (d : IndDecl) (ps : List Sem) : Prop := Par0.sems dm.read (dm.parsOf d 0 [] ps) = ps

/-- A packed element of a covered declaration, read as the constructor value that describes it,
is a member of its type where its parameters are read back from its code. -/
theorem ctor_mem_tyM (d : IndDecl) (ps : List Sem) (hd : dm.covers d) (hs : (d.sort == 0) = false)
    (hp : dm.ParamsCoded d ps) (x : dm.car d ps) :
    Sem.dat d.name ps (dm.tag x) (dm.fields x) (some ⟨dm.car d ps, x⟩) ∈ₛ[dm.read] dm.tyM d ps := by
  unfold tyM
  rw [hs]
  refine ⟨x, ?_⟩
  unfold ParamsCoded at hp
  simp only [Code0.enc, hp, dm.read_eq x hd]

/-- **A constructor value's tag and fields are read off its meaning whatever its fields hold**:
packed, partly moved, or open (docs/31 D32: the value describes itself; no declaration, carrier or
type is consulted). -/
theorem parts_ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) :
    (dm.ctorM d ps c fs).parts = some (c, fs) := by
  unfold ctorM
  split
  · split <;> rfl
  · rfl

/-! ## Small field types

A field of a `Type₀` or `Prop` inductive lives in `Type₀` or `Prop` (docs/18 (I6)), so its
meaning is a level-0 code (a `Type₀` type or a proposition): a *small* type, whose elements a carrier
in `Type` can store (`El`). `small` cuts any other type meaning down to `err`, which has no
members, so that a model whose field types are `small` packs exactly the members of its field
types. -/

/-- The small part of a type meaning: itself if its carrier is at level 0 (a `Type₀` type or a
proposition), `err` otherwise. -/
def small : TyM → TyM
  | .t0 A c => .t0 A c
  | _ => TyM.err

/-- What a carrier in `Type` stores for an element of a small type: its level-0 carrier. -/
abbrev El (T : TyM) : Type := T.el0

section
variable (R : DataRead)

/-- The meaning of a stored element. -/
def enc (T : TyM) (a : El T) : Sem := T.code0.2.enc R a

/-- Read a meaning as a stored element of a small type, if it is a member (classically). -/
noncomputable def dec (T : TyM) (s : Sem) : Option (El T) := T.code0.2.dec R s

theorem small_small (T : TyM) : small (small T) = small T := by
  cases T <;> rfl

theorem small_code0 (T : TyM) : (small T).code0 = T.code0 := by
  cases T <;> rfl

theorem enc_mem_small (T : TyM) (a : El T) : enc R T a ∈ₛ[R] small T := by
  cases T with
  | t0 A c => exact ⟨a, rfl⟩
  | t1 _ _ | t2 _ _ => exact a.elim

theorem enc_mem (T : TyM) (a : El T) : enc R T a ∈ₛ[R] T := by
  cases T with
  | t0 A c => exact ⟨a, rfl⟩
  | t1 _ _ | t2 _ _ => exact a.elim

theorem enc_inj {T : TyM} {a b : El T} (h : enc R T a = enc R T b) : a = b := Code0.enc_inj R _ h

theorem dec_enc (T : TyM) (a : El T) : dec R T (enc R T a) = some a := Code0.dec_enc R _ a

theorem enc_of_dec {T : TyM} {s : Sem} {a : El T} (h : dec R T s = some a) : enc R T a = s :=
  Code0.enc_of_dec R _ h

/-- Decoding succeeds exactly on the members of the small part of the type. -/
theorem dec_isSome_iff (T : TyM) (s : Sem) : (dec R T s).isSome ↔ s ∈ₛ[R] small T := by
  rw [dec, Code0.dec_isSome]
  cases T with
  | t0 A c => rfl
  | t1 _ _ | t2 _ _ =>
    simp only [small, TyM.err, Sem.mem]
    exact ⟨fun ⟨a, _⟩ => a.elim, fun ⟨a, _⟩ => a.elim⟩

/-- On a small type, membership is membership of the small part. -/
theorem mem_small_of_mem {T : TyM} {s : Sem} (h : s ∈ₛ[R] T) (hT : small T = T) : s ∈ₛ[R] small T := by
  rw [hT]; exact h

end

/-! ## Constructor shapes

The laws state a constructor's arity through the declaration (`d.ctors`); both models compare
it with an arity list, through this lemma. -/

/-- The arities of a declaration's constructors. -/
def arities (d : IndDecl) : List Nat := d.ctors.map (·.2.length)

theorem ctor_iff_arity (d : IndDecl) (c : Nat) (P : Nat → Prop) :
    (∃ ctor, d.ctors[c]? = some ctor ∧ P ctor.2.length) ↔ ∃ n, (arities d)[c]? = some n ∧ P n := by
  simp only [arities, List.getElem?_map]
  constructor
  · rintro ⟨ctor, h, hp⟩
    exact ⟨_, by rw [h]; rfl, hp⟩
  · rintro ⟨n, h, hp⟩
    cases hc : d.ctors[c]? with
    | none => rw [hc] at h; cases h
    | some ctor =>
      rw [hc] at h
      cases h
      exact ⟨ctor, rfl, hp⟩

/-! ## The library's declarations, modelled by hand -/

/-- Which library declaration a declaration is: by its name, sort and constructor arities, so
that a covered declaration has the shape the hand-written model assumes (a declaration named
`Pair` with three fields is not covered: its fields could not be packed into a product of two). -/
inductive LibKind
  | pair | ff | tt | and | other
deriving DecidableEq

/-- The library declaration `d` is (`Prelude.decls`), or `none`. -/
def libKind (d : IndDecl) : LibKind :=
  if d.name = "Pair" ∧ d.sort = 1 ∧ arities d = [2] then .pair
  else if d.name = "False" ∧ d.sort = 0 ∧ arities d = [] then .ff
  else if d.name = "True" ∧ d.sort = 0 ∧ arities d = [0] then .tt
  else if d.name = "And" ∧ d.sort = 0 ∧ arities d = [2] then .and
  else .other

/-- The arities of the library declarations. -/
def LibKind.arities : LibKind → List Nat
  | .pair | .and => [2]
  | .ff | .other => []
  | .tt => [0]

theorem arities_libKind (d : IndDecl) (h : libKind d ≠ .other) :
    arities d = (libKind d).arities := by
  unfold libKind at h ⊢
  repeat' split
  all_goals first | (rename_i hh; exact hh.2.2) | (rename_i hh _ _ _; exact hh.2.2) | skip
  all_goals simp_all

/-- Parameter `i` as a field type: the type it holds, cut to its small part. -/
def libPar (ps : List Sem) (i : Nat) : TyM :=
  small (match ps.getD i .err with
    | .ty T => T
    | _ => TyM.err)

/-- `Pair(A, B)` means `A × B`, `And(P, Q)` the product of the proofs, `True` the unit type and
`False` the empty type (so the truncations of the last three are `P ∧ Q`, `True` and `False`). -/
def LibKind.car : LibKind → List Sem → Type
  | .pair, ps | .and, ps => El (libPar ps 0) × El (libPar ps 1)
  | .tt, _ => PUnit
  | .ff, _ | .other, _ => PEmpty

/-- The carrier of a library declaration. -/
def libCar (d : IndDecl) (ps : List Sem) : Type := (libKind d).car ps

/-- The two fields of `Pair` and `And` have the parameters' types. -/
def LibKind.fieldTy : LibKind → List Sem → Nat → TyM
  | .pair, ps, i | .and, ps, i => if i = 0 then libPar ps 0 else libPar ps 1
  | _, _, _ => TyM.err

noncomputable def LibKind.pack (R : DataRead) : (k : LibKind) → (ps : List Sem) → Nat → List Sem → Option (k.car ps)
  | .pair, _, c, fs | .and, _, c, fs =>
    if c = 0 then
      match fs with
      | [f, g] => (dec R _ f).bind fun a => (dec R _ g).map fun b => (a, b)
      | _ => none
    else none
  | .tt, _, c, fs => if c = 0 ∧ fs = [] then some PUnit.unit else none
  | .ff, _, _, _ | .other, _, _, _ => none

def LibKind.fields (R : DataRead) : (k : LibKind) → (ps : List Sem) → k.car ps → List Sem
  | .pair, ps, (a, b) | .and, ps, (a, b) => [enc R (libPar ps 0) a, enc R (libPar ps 1) b]
  | .tt, _, _ => []
  | .ff, _, x | .other, _, x => x.elim

theorem LibKind.tag_pack (R : DataRead) (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) (x : k.car ps)
    (h : k.pack R ps c fs = some x) : c = 0 := by
  cases k <;> simp only [LibKind.pack] at h
  all_goals first | cases h | (split at h <;> simp_all)

theorem LibKind.fields_pack (R : DataRead) (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) (x : k.car ps)
    (h : k.pack R ps c fs = some x) : k.fields R ps x = fs := by
  cases k <;> simp only [LibKind.pack] at h
  case pair | and =>
    split at h
    · split at h
      · rename_i f g
        cases ha : dec R (libPar ps 0) f <;> cases hb : dec R (libPar ps 1) g <;>
          rw [ha, hb] at h <;> cases h
        simp [LibKind.fields, enc_of_dec R ha, enc_of_dec R hb]
      · cases h
    · cases h
  case tt =>
    split at h
    · rename_i hc; obtain ⟨_, rfl⟩ := hc; rfl
    · cases h
  all_goals cases h

theorem LibKind.pack_fields (R : DataRead) (k : LibKind) (ps : List Sem) (x : k.car ps) :
    k.pack R ps 0 (k.fields R ps x) = some x := by
  cases k
  case pair | and =>
    obtain ⟨a, b⟩ := x
    simp only [LibKind.pack, LibKind.fields, dec_enc R]
    rfl
  case tt => rfl
  all_goals exact x.elim

theorem dec_libPar_isSome (R : DataRead) (ps : List Sem) (i : Nat) (s : Sem) :
    (dec R (libPar ps i) s).isSome ↔ s ∈ₛ[R] libPar ps i := by
  rw [dec_isSome_iff, libPar, small_small]

theorem LibKind.pack_isSome (R : DataRead) (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) :
    (k.pack R ps c fs).isSome ↔
      ∃ n, k.arities[c]? = some n ∧ fs.length = n ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[R] k.fieldTy ps i := by
  cases k
  case pair | and =>
    simp only [LibKind.pack, LibKind.arities, LibKind.fieldTy]
    by_cases hc : c = 0
    · subst hc
      simp only [if_true, List.getElem?_cons_zero, Option.some.injEq, exists_eq_left']
      match fs with
      | [f, g] =>
        simp only [List.length_cons, List.length_nil, true_and]
        constructor
        · intro h i hi
          cases ha : dec R (libPar ps 0) f <;> cases hb : dec R (libPar ps 1) g <;>
            rw [ha, hb] at h <;> simp [Option.bind, Option.map] at h
          have hf := (dec_libPar_isSome R ps 0 f).1 (by simp [ha])
          have hg := (dec_libPar_isSome R ps 1 g).1 (by simp [hb])
          match i, hi with
          | 0, _ => exact hf
          | 1, _ => exact hg
        · intro h
          have ha := (dec_libPar_isSome R ps 0 f).2 (h 0 (by decide))
          have hb := (dec_libPar_isSome R ps 1 g).2 (h 1 (by decide))
          cases ha' : dec R (libPar ps 0) f <;> cases hb' : dec R (libPar ps 1) g <;>
            simp_all [Option.bind, Option.map]
          rfl
      | [] | [_] | _ :: _ :: _ :: _ => simp
    · simp [hc]
  case tt =>
    simp only [LibKind.pack, LibKind.arities]
    by_cases hc : c = 0
    · subst hc
      cases fs <;> simp
      rfl
    · cases c with
      | zero => exact absurd rfl hc
      | succ c => simp
  all_goals simp [LibKind.pack, LibKind.arities]

/-- The library model (`Prelude.decls`: `Pair`, `False`, `True`, `And`). Every constructor is
constructor `0`; no library declaration is recursive (`recArgs` is `none`), so the rank is `0`;
no field's declared type is an inductive (`Pair`'s and `And`'s fields have the parameters' types).
A field of a parameter's type is read at a reading `R` given from outside (the whole program's
model, which reads the parameters' own data), and the model is lawful where `R` reads the library's
elements as this model does (`hR`, docs/31 D61). -/
noncomputable def libModel (R : DataRead)
    (hR : ∀ {d ps} (x : libCar d ps), libKind d ≠ .other → R d ps (libCar d ps) x = (0, (libKind d).fields R ps x)) :
    DataModel where
  covers d := libKind d ≠ .other
  car := libCar
  fieldTy d ps _ i _ := (libKind d).fieldTy ps i
  paramTy d _ _ := if d.name = "Pair" then TyM.univ 1 else if d.name = "And" then TyM.univ 0 else TyM.err
  pack d ps c fs := (libKind d).pack R ps c fs
  tag _ := 0
  fields {d ps} x := (libKind d).fields R ps x
  rank _ := 0
  read := R
  read_eq x hd := hR x hd
  tag_pack {d ps c fs} x _ h := ((libKind d).tag_pack R ps c fs x h).symm
  fields_pack {d ps c fs} x _ h := (libKind d).fields_pack R ps c fs x h
  pack_fields {d ps} x _ := (libKind d).pack_fields R ps x
  pack_isSome {d ps c fs} hd := by
    rw [ctor_iff_arity d c (fun n => fs.length = n ∧ _), arities_libKind d hd]
    exact (libKind d).pack_isSome R ps c fs
  rank_lt _ _ _ _ h := by cases h

end DataModel

end Ochr.Meaning.Old
