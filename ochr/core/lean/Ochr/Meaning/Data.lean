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
  /-- The declaration's name and parameter meanings of field `i`'s declared type, at the
  parameters and the earlier fields, when that type is an inductive: the `data` of the field's
  structured hint (docs/31 D8), so that a field holding a constructor value that records no
  parameters is read at its declared parameters. Read by the same reading as `fieldTy`. -/
  fieldData : IndDecl → List Sem → Nat → Nat → List Sem → Option (String × List Sem) :=
    fun _ _ _ _ _ => none
  /-- The same for parameter `i`'s declared type at the earlier parameters (a value parameter
  of inductive type, D71). -/
  paramData : IndDecl → Nat → List Sem → Option (String × List Sem) := fun _ _ _ => none
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
  tag_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → tag x = c
  fields_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → fields x = fs
  /-- Every element is a constructor applied to its fields (the carrier is a least fixed point). -/
  pack_fields : ∀ {d ps} (x : car d ps), covers d → pack d ps (tag x) (fields x) = some x
  /-- Packing succeeds exactly when each field is a member of its field type at the earlier
  fields, and there are as many as the constructor declares. -/
  pack_isSome : ∀ {d ps c fs}, covers d →
    ((pack d ps c fs).isSome ↔
      ∃ ctor, d.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ fieldTy d ps c i (fs.take i))
  /-- A recursive field, read at the parameters of its declared occurrence (`recArgs`), has
  smaller rank. The law is stated through the declared type, not through carriers: carriers do
  not determine parameters, and the form "every field whose carrier is the declaration's" is
  false (in `Pair(Pair(Unit, Unit), Unit)` the inner pair's meaning is definitionally
  `el0 (car Pair [Unit, Unit]) _`, a field of the outer one at the same rank; with `Nat = Nat × Unit`,
  consistent with Lean, no rank function satisfies it; docs/31, data-generic). -/
  rank_lt : ∀ {d ps ps'} (x : car d ps) (y : car d ps'), covers d → ∀ i,
    recArgs d ps (tag x) i ((fields x).take i) = some ps' →
    (fields x)[i]? = some (Sem.el0 (car d ps') y) → rank y < rank x

namespace DataModel

variable (dm : DataModel)

/-- The meaning of the type `D(ps)`: a data type is its carrier; a `Prop`-sorted declaration
the truncation of the same fixed point, true when it is inhabited. -/
def tyM (d : IndDecl) (ps : List Sem) : TyM :=
  if d.sort == 0 then .prop (Nonempty (dm.car d ps)) else .ty0 (dm.car d ps)

/-- Parameters whose carrier is the type `T`, chosen classically (`paramsOf_car`). A fallback
only: since carriers do not determine parameters, no definition relies on this choice; a
constructor value that records no parameters reads them off its structured hint (docs/31 D8),
`fieldData` and `paramData` supplying the hints of fields and parameters. -/
noncomputable def paramsOf (d : IndDecl) : TyM → Option (List Sem)
  | .ty0 A => open Classical in
    if h : ∃ ps, dm.car d ps = A then some (Classical.choose h) else none
  | _ => none

theorem paramsOf_car (d : IndDecl) (A : Type) (ps : List Sem) (h : dm.paramsOf d (.ty0 A) = some ps) :
    dm.car d ps = A := by
  by_cases hex : ∃ ps, dm.car d ps = A
  · have : dm.paramsOf d (.ty0 A) = some (Classical.choose hex) := by
      simp [paramsOf, hex]
    rw [this] at h
    cases h
    exact Classical.choose_spec hex
  · simp [paramsOf, hex] at h

/-- The meaning of a constructor value `C(ps; fs)` of a data type whose fields already mean
`fs`: packed into the carrier when every field is whole, kept as an untyped tuple when some
field holds `moved` (D84: a definite value lying in no type), the error value when a whole
field is not of its type. A `Prop`-sorted declaration's constructor values are `⋆` already
(`Machine.evalCtor`, D42), so `ctorM` is only applied to data. -/
noncomputable def ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem :=
  open Classical in
  if ∀ f ∈ fs, f.whole then
    match dm.pack d ps c fs with
    | some x => .el0 (dm.car d ps) x
    | none => .err
  else .ctor d.name c fs

/-- The fields of a meaning of a constructor value, if it is one. -/
noncomputable def fieldsOf (d : IndDecl) (ps : List Sem) : Sem → Option (Nat × List Sem)
  | .el0 A x => open Classical in
    if h : A = dm.car d ps then some (dm.tag (h ▸ x), dm.fields (h ▸ x)) else none
  | .ctor n c fs => if n = d.name then some (c, fs) else none
  | _ => none

/-! ## Small field types

A field of a `Type₀` or `Prop` inductive lives in `Type₀` or `Prop` (docs/18 (I6)), so its
meaning is a carrier `ty0 A` or a proposition `prop P`: a *small* type, whose elements a carrier
in `Type` can store (`El`). `small` cuts any other type meaning down to `err`, which has no
members, so that a model whose field types are `small` packs exactly the members of its field
types. -/

/-- The small part of a type meaning: itself if it is a `Type₀` carrier or a proposition, `err`
otherwise. -/
def small : TyM → TyM
  | .ty0 A => .ty0 A
  | .prop P => .prop P
  | _ => .err

/-- What a carrier in `Type` stores for an element of a small type: the element itself, a proof
of the proposition; nothing for any other type meaning. -/
def El : TyM → Type
  | .ty0 A => A
  | .prop P => PLift P
  | _ => PEmpty

/-- The meaning of a stored element. -/
def enc : (T : TyM) → El T → Sem
  | .ty0 A, a => .el0 A a
  | .prop _, _ => .proof
  | .ty1 _, x | .ty2 _, x | .univ _, x | .err, x => x.elim

/-- Read a meaning as a stored element of a small type, if it is a member (classically). -/
noncomputable def dec : (T : TyM) → Sem → Option (El T)
  | .ty0 A, .el0 B b => open Classical in if h : B = A then some (h ▸ b) else none
  | .prop P, .proof => open Classical in if h : P then some ⟨h⟩ else none
  | _, _ => none

theorem small_small (T : TyM) : small (small T) = small T := by
  cases T <;> rfl

theorem enc_mem (T : TyM) (a : El T) : enc T a ∈ₛ T := by
  cases T with
  | ty0 A => exact rfl
  | prop P => exact a.down
  | _ => exact a.elim

theorem enc_mem_small (T : TyM) (a : El T) : enc T a ∈ₛ small T := by
  cases T with
  | ty0 A => exact rfl
  | prop P => exact a.down
  | _ => exact a.elim

theorem enc_inj {T : TyM} {a b : El T} (h : enc T a = enc T b) : a = b := by
  cases T with
  | ty0 A => cases h; rfl
  | prop P => cases a; cases b; rfl
  | _ => exact a.elim

theorem dec_enc (T : TyM) (a : El T) : dec T (enc T a) = some a := by
  cases T with
  | ty0 A => simp [enc, dec]
  | prop P => cases a; simp [enc, dec, *]
  | _ => exact a.elim

theorem enc_of_dec {T : TyM} {s : Sem} {a : El T} (h : dec T s = some a) : enc T a = s := by
  cases T <;> cases s <;> simp [dec] at h
  case ty0.el0 A B b =>
    obtain ⟨rfl, rfl⟩ := h
    rfl
  case prop.proof P =>
    obtain ⟨_, h⟩ := h
    cases h
    rfl

/-- Decoding succeeds exactly on the members of the small part of the type. -/
theorem dec_isSome_iff (T : TyM) (s : Sem) : (dec T s).isSome ↔ s ∈ₛ small T := by
  cases T <;> cases s <;> simp [dec, small, Sem.mem]
  case prop.proof P =>
    by_cases h : P <;> simp [h, Option.isSome]

/-- On a small type, membership is membership of the small part. -/
theorem mem_small_of_mem {T : TyM} {s : Sem} (h : s ∈ₛ T) (hT : small T = T) : s ∈ₛ small T := by
  rw [hT]; exact h

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
    | _ => .err)

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
  | _, _, _ => .err

noncomputable def LibKind.pack : (k : LibKind) → (ps : List Sem) → Nat → List Sem → Option (k.car ps)
  | .pair, ps, c, fs | .and, ps, c, fs =>
    if c = 0 then
      match fs with
      | [f, g] => (dec _ f).bind fun a => (dec _ g).map fun b => (a, b)
      | _ => none
    else none
  | .tt, _, c, fs => if c = 0 ∧ fs = [] then some PUnit.unit else none
  | .ff, _, _, _ | .other, _, _, _ => none

def LibKind.fields : (k : LibKind) → (ps : List Sem) → k.car ps → List Sem
  | .pair, ps, (a, b) | .and, ps, (a, b) => [enc (libPar ps 0) a, enc (libPar ps 1) b]
  | .tt, _, _ => []
  | .ff, _, x | .other, _, x => x.elim

theorem LibKind.tag_pack (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) (x : k.car ps)
    (h : k.pack ps c fs = some x) : c = 0 := by
  cases k <;> simp only [LibKind.pack] at h
  all_goals first | cases h | (split at h <;> simp_all)

theorem LibKind.fields_pack (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) (x : k.car ps)
    (h : k.pack ps c fs = some x) : k.fields ps x = fs := by
  cases k <;> simp only [LibKind.pack] at h
  case pair | and =>
    split at h
    · split at h
      · rename_i f g
        cases ha : dec (libPar ps 0) f <;> cases hb : dec (libPar ps 1) g <;>
          rw [ha, hb] at h <;> cases h
        simp [LibKind.fields, enc_of_dec ha, enc_of_dec hb]
      · cases h
    · cases h
  case tt =>
    split at h
    · rename_i hc; obtain ⟨_, rfl⟩ := hc; rfl
    · cases h
  all_goals cases h

theorem LibKind.pack_fields (k : LibKind) (ps : List Sem) (x : k.car ps) :
    k.pack ps 0 (k.fields ps x) = some x := by
  cases k
  case pair | and =>
    obtain ⟨a, b⟩ := x
    simp only [LibKind.pack, LibKind.fields, dec_enc]
    rfl
  case tt => rfl
  all_goals exact x.elim

theorem dec_libPar_isSome (ps : List Sem) (i : Nat) (s : Sem) :
    (dec (libPar ps i) s).isSome ↔ s ∈ₛ libPar ps i := by
  rw [dec_isSome_iff, libPar, small_small]

theorem LibKind.pack_isSome (k : LibKind) (ps : List Sem) (c : Nat) (fs : List Sem) :
    (k.pack ps c fs).isSome ↔
      ∃ n, k.arities[c]? = some n ∧ fs.length = n ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ k.fieldTy ps i := by
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
          cases ha : dec (libPar ps 0) f <;> cases hb : dec (libPar ps 1) g <;>
            rw [ha, hb] at h <;> simp [Option.bind, Option.map] at h
          have hf := (dec_libPar_isSome ps 0 f).1 (by simp [ha])
          have hg := (dec_libPar_isSome ps 1 g).1 (by simp [hb])
          match i, hi with
          | 0, _ => exact hf
          | 1, _ => exact hg
        · intro h
          have ha := (dec_libPar_isSome ps 0 f).2 (h 0 (by decide))
          have hb := (dec_libPar_isSome ps 1 g).2 (h 1 (by decide))
          cases ha' : dec (libPar ps 0) f <;> cases hb' : dec (libPar ps 1) g <;>
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
no field's declared type is an inductive (`fieldData` is `none`: `Pair`'s and `And`'s fields
have the parameters' types). -/
noncomputable def libModel : DataModel where
  covers d := libKind d ≠ .other
  car := libCar
  fieldTy d ps _ i _ := (libKind d).fieldTy ps i
  paramTy d _ _ := if d.name = "Pair" then .univ 1 else if d.name = "And" then .univ 0 else .err
  pack d ps c fs := (libKind d).pack ps c fs
  tag _ := 0
  fields {d ps} x := (libKind d).fields ps x
  rank _ := 0
  tag_pack {d ps c fs} x _ h := ((libKind d).tag_pack ps c fs x h).symm
  fields_pack {d ps c fs} x _ h := (libKind d).fields_pack ps c fs x h
  pack_fields {d ps} x _ := (libKind d).pack_fields ps x
  pack_isSome {d ps c fs} hd := by
    rw [ctor_iff_arity d c (fun n => fs.length = n ∧ _), arities_libKind d hd]
    exact (libKind d).pack_isSome ps c fs
  rank_lt _ _ _ _ h := by cases h

end DataModel

end Ochr.Meaning
