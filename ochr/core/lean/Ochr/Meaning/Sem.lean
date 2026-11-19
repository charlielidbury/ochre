import Ochr.Env

/-!
# The semantic domain: meanings of types (`TyM`) and of values (`Sem`)

The set model of `ochr/docs/18` §3, built from Lean's own types as `Ochr/Model/Slice.lean` does
(docs/24): a type means a Lean type holding only its good elements, so there is no universe of
codes and no induction-recursion. What a *value* means must also be nameable without its type
(a state is a function from positions to meanings, and `Eq` compares two meanings), so meanings
live in one untyped universe `Sem`, whose elements are tagged by the Lean type they belong to.
Membership `s ∈ ⟦T⟧` is then the tag's equality with the type's carrier.

## Why tagged elements, not tuples

In ZFC a constructor value means a tagged tuple and a function a set of pairs, all in one
`V_κ`. Lean has no small type closed under its own function space, so an untyped universe holding
functions on itself cannot be an inductive type, and a universe of first-order trees with leaves
of arbitrary small types is one level too big to be a leaf type itself. The only encoding that
keeps `Π` small is the typed one: a function value means a Lean function on the carriers of its
domain and codomain, `el0 ((a : A) → B a) f`. A constructor value (docs/31 D32) describes itself:
`dat` carries its declaration's name, its parameters' meanings, its constructor and its fields, and
when it is whole and of its type also its element of the carrier, which is what a Lean function on
carriers is applied to (`dec`/`enc` at a data type's code, `TyM.data`). So a value is taken apart
by reading it, as a ZFC tree is in Lean's own model, and never through a type or a carrier.

## Levels (Q1, docs/18)

Ochr's `sort 0 = Prop`, `sort 1 = Type₀`, `sort 2 = Type₁`, …, with `Prop : Type₁` beside
`Type₀ : Type₁` (`sortSucc`). Lean's universes cannot be indexed by a number, so the model fixes
the levels a program may write: `Prop`, `Type₀` and `Type₁` (`LevelsBelow 2`, `Bounded.lean`).
Carriers then live in `Type`, `Type 1` or `Type 2`, and `Sem : Type 3`. Supporting one more
level is one more constructor in each of `TyM`, `Sem`, `El`.
-/

namespace Ochr.Meaning

mutual
/-- The meaning of a type value: a proposition (whose only possible element is the proof `•`),
a carrier at one of the three supported Lean levels, a data type, a universe `⟦sort l⟧`, or the
error value (an ill-formed type; no derivation reaches one). A universe is kept symbolic rather
than as the Lean type `Type` etc. so that its *elements*, type values `Sem.ty T`, are recognised
by their level (`mem`). A data type (docs/31 D32) is a code: its declaration's name and its
parameters' meanings, decoding to its carrier `A`, with `unpk` reading an element's constructor
and fields (Lean's tagged types, Carneiro §6.4, for data). -/
inductive TyM : Type 3 where
  | prop (P : Prop)
  | ty0 (A : Type)
  | ty1 (A : Type 1)
  | ty2 (A : Type 2)
  | univ (l : Nat)
  | err
  | data (name : String) (ps : List Sem) (A : Type) (unpk : A → Nat × List Sem)

/-- The meaning of a value, tagged by its carrier. `proof` is `•`, the one element of every true
proposition; `ty T` a type used as a value; `moved` is `⊥`, a place definitely moved out of
(D84: a definite value, equal only to itself); `err` is the error value.

A constructor value describes itself (docs/31 D32): `dat name ps c fs el` is its declaration's
name, its parameters' meanings, its constructor and its fields' meanings, and `el` its element of
the carrier when it is whole and of its type (`DataModel.ctorM` packs it), `none` when a field is
moved out or the value is open (a field outside the type its earlier fields give). So a value is
taken apart by reading it, never through a type: an element of an inductive type is a tree that
describes itself, as in Lean's set-theoretic model. A partly moved number `S(⊥)` is
`dat "Nat" [] 1 [⊥] none`; a whole number is `el0 Nat n`. -/
inductive Sem : Type 3 where
  | el0 (A : Type) (a : A)
  | el1 (A : Type 1) (a : A)
  | el2 (A : Type 2) (a : A)
  | ty (T : TyM)
  | proof
  | moved
  | dat (name : String) (ps : List Sem) (c : Nat) (fs : List Sem) (el : Option ((A : Type) × A))
  | err
end

/-- Ochr's level of a type meaning: the `l` of the `sort l` it is an element of. -/
def TyM.level : TyM → Option Nat
  | .prop _ => some 0
  | .ty0 _ => some 1
  | .ty1 _ => some 2
  | .ty2 _ => some 3
  | .univ l => some (sortSucc l)
  | .err => none
  | .data .. => some 1

/-- A meaning holds no `moved` part and is not the error value. -/
def Sem.whole : Sem → Prop
  | .moved => False
  | .err => False
  | .dat _ _ _ fs _ => ∀ f ∈ fs, f.whole   -- whole fields and no element: an OPEN (ill-typed) value
  | _ => True

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

/-- Membership: a meaning lies in a type's meaning. An element is a member of the carrier it is
tagged with; the proof `•` of every true proposition; a type value of the universe of its level.
The tag is compared as a Lean type, which is what convertible type values must be shown to
share (`conv_sound_ty`). A constructor value is a member of a data type when it names the type's
declaration and parameters and its element reads back as its constructor and fields (D32). -/
def Sem.mem : Sem → TyM → Prop
  | .el0 A _, .ty0 B => A = B
  | .el1 A _, .ty1 B => A = B
  | .el2 A _, .ty2 B => A = B
  | .proof, .prop P => P
  | .ty T, .univ l => T.level = some l
  | .dat n ps c fs (some ⟨A, x⟩), .data n' ps' A' unpk => n = n' ∧ ps = ps' ∧ ∃ h : A = A', unpk (h ▸ x) = (c, fs)
  | _, _ => False

scoped infix:50 " ∈ₛ " => Sem.mem

/-- Read a meaning as a type. -/
def Sem.asTy : Sem → TyM
  | .ty T => T
  | _ => .err

/-- A proposition's meaning is true. -/
def TyM.true : TyM → Prop
  | .prop P => P
  | _ => False

theorem false_not_true : ¬ (TyM.prop False).true := id

end Ochr.Meaning
