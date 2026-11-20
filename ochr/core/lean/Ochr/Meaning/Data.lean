import Ochr.Meaning.Sem

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

namespace Ochr.Meaning

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
noncomputable def _root_.Ochr.Meaning.eltOf (R : DataRead) (T : TyM) (s : Sem) : Elt0 :=
  match T.code0.2.dec R s with
  | some b => .mk _ T.code0.2 b
  | none => .bad

/-- A parameter's meaning as a coded parameter of a data type: a type value as its code, a value
as a coded element of the parameter's declared type `T`. -/
noncomputable def _root_.Ochr.Meaning.parOf (R : DataRead) (T : TyM) : Sem → Par0
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
def _root_.Ochr.Meaning.Sem.parts : Sem → Option (Nat × List Sem)
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
theorem _root_.Ochr.Meaning.Code0.enc_ne_dat_none (R : DataRead) {A : Type} (c : Code0 A) (a : A) (n : String)
    (ps : List Sem) (k : Nat) (fs : List Sem) : c.enc R a ≠ .dat n ps k fs none := by
  cases c with
  | err => exact a.elim
  | _ => simp [Code0.enc]

theorem _root_.Ochr.Meaning.Sem.not_mem_dat_none (R : DataRead) (n : String) (ps : List Sem) (k : Nat)
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

end Ochr.Meaning
