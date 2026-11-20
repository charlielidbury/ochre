import Ochr.Meaning.Rules.Sound
import Ochr.Meaning.Rules.Counter

/-!
# The rules trial: "hereditarily well typed" values (the lead's decision 1)

Membership of a value in a type says nothing about the values inside it that do not determine its
meaning's membership: `Eq(A, a, b)` is a member of `Prop` whatever `a` and `b` are, and an
inductive type applied to anything is a type. Conversion compares values component by component,
so its soundness needs every component typed at the type its former expects.

`HWT K ρ φ T v`: `v` is a (partly moved) member of `T`, and each component a type former reads is
itself hereditarily well typed at the type the former expects: an `Eq`'s sides at its type, an
inductive type's arguments and a constructor value's recorded parameters at the declaration's
parameter types (so `And`'s arguments are propositions), a constructor value's fields at its field
types, a closure's or Π-closure's captures at their recorded types. For terms (the code of
closures and Π-closures, the programs in sealed programs) the predicate can say only that each
embedded value is hereditarily well typed at SOME type (`HWTerm`): which type a position of a
term expects is a typing judgement for terms, which neither the paper nor the model has. That is
the gap the lead suspected; `Rules/Typed.lean`'s docstring below and the report list where it
bites.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

mutual
/-- The values written directly in a term (`.val v` nodes, not looking inside the values). -/
def _root_.Ochr.Term.vals : Term → List Value
  | .val v => [v]
  | .assign _ t | .succ t | .ref t => t.vals
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.vals ++ u.vals
  | .matchNat _ z s => z.vals ++ s.vals
  | .pi _ ds c => Term.valsList ds ++ c.vals
  | .fix _ _ ds c _ b => Term.valsList ds ++ c.vals ++ b.vals
  | .call f as _ => f.vals ++ Term.valsList as
  | .eq a b c | .id a b c => a.vals ++ b.vals ++ c.vals
  | .ctor _ _ _ ps as => Term.valsList ps ++ Term.valsList as
  | .prim _ as | .tind _ as => Term.valsList as
  | .matchInd _ _ as => Term.valsArms as
  | _ => []
termination_by structural t => t

def _root_.Ochr.Term.valsList : List Term → List Value
  | [] => []
  | t :: ts => t.vals ++ Term.valsList ts
termination_by structural ts => ts

def _root_.Ochr.Term.valsArms : List (Hint × Term) → List Value
  | [] => []
  | (_, t) :: ts => t.vals ++ Term.valsArms ts
termination_by structural ts => ts
end

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A value means a type, at some level. -/
def IsType (A : Value) : Prop := ((meanV K ρ φ (.plain .err) A).asTy).level.isSome

mutual
/-- **Hereditarily well typed at `T`.** -/
inductive HWT : TyM → Value → Prop
  /-- a value with no components a former reads -/
  | atom {T : TyM} {v : Value} : (match v with
      | .succ _ | .tEq .. | .tInd .. | .ind .. | .tRef _ | .borrow .. | .gloan .. | .sealed _
      | .clo .. | .tPi .. => False | _ => True) →
      DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) v) T → HWT T v
  | succ {T : TyM} {a : Value} : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.succ a)) T →
      HWT TyM.nat a → HWT T (.succ a)
  /-- an `Eq`'s sides at its type -/
  | tEq {T : TyM} {A a b : Value} {l : Nat} : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.tEq A a b)) T →
      HWT (TyM.univ l) A → HWT (tyOf K ρ φ A) a → HWT (tyOf K ρ φ A) b → HWT T (.tEq A a b)
  /-- an inductive type's arguments at its parameter types -/
  | tInd {T : TyM} {n : String} {args : List Value} {d : IndDecl} :
      DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.tInd n args)) T →
      K.Γ.find? (·.name == n) = some d → HWTParams d 0 [] args → HWT T (.tInd n args)
  /-- a constructor value of a data declaration at that declaration's type in the model
  (`DataModel.tyR`, whose carrier is the model's: as first written only `T.dataRec?` was asked,
  which a data code over another carrier also has): its recorded parameters at the parameter
  types, its fields at the field types of its record -/
  | ind {T : TyM} {t : String} {c : Nat} {h : Hint} {ps fs : List Value} {d : IndDecl} {r : Rec} :
      DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.ind t c h ps fs)) T →
      K.Γ.find? (·.name == t) = some d → (d.sort == 0) = false → T = K.dm.tyR d r →
      HWTParams d 0 [] ps → HWTFields d r c 0 [] fs → HWT T (.ind t c h ps fs)
  /-- a borrow type's content type at a universe, as `tEq` types its type (`⟦&A⟧` reads `A` at
  hint `err`; as first written this was `HWT T A → HWT T (.tRef A)`, typing `A` at the hint `T`,
  which is not where `⟦&A⟧` reads it, and with no membership of `&A` itself) -/
  | tRef {T : TyM} {A : Value} {l : Nat} : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.tRef A)) T →
      HWT (TyM.univ l) A → HWT T (.tRef A)
  | borrow {T : TyM} {l : Nat} {a : Value} : HWT T a → HWT T (.borrow l a)
  | gloan {T : TyM} {l : Nat} {a : Value} : HWT T a → HWT T (.gloan l a)
  /-- code: each value written in it well typed at some type (all a term-free predicate can say) -/
  | sealed {T : TyM} {t : Term} : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.sealed t)) T →
      HWTerm t → HWT T (.sealed t)
  | clo {T : TyM} {cs : List Value} {t : Term} {rd : List (DeclInfo × Value)} :
      DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.clo cs t rd)) T →
      HWTCaps cs rd → HWTerm t → HWT T (.clo cs t rd)
  | tPi {T : TyM} {cs : List Value} {t : Term} {rd : List (DeclInfo × Value)} :
      DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.tPi cs t rd)) T →
      HWTCaps cs rd → HWTerm t → HWT T (.tPi cs t rd)

/-- Parameters, each at its parameter type given the earlier ones. -/
inductive HWTParams : IndDecl → Nat → List Sem → List Value → Prop
  | nil {d : IndDecl} {i : Nat} {e : List Sem} : HWTParams d i e []
  | cons {d : IndDecl} {i : Nat} {e : List Sem} {v : Value} {vs : List Value} :
      HWT (K.dm.paramTy d i e) v →
      HWTParams d (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.paramTy d i e)) v]) vs → HWTParams d i e (v :: vs)

/-- Fields, each at its field type at the record and the earlier fields. -/
inductive HWTFields : IndDecl → Rec → Nat → Nat → List Sem → List Value → Prop
  | nil {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} : HWTFields d r c i e []
  | cons {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {v : Value} {vs : List Value} :
      HWT (K.dm.fieldTyR d r c i e) v →
      HWTFields d r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) v]) vs →
      HWTFields d r c i e (v :: vs)

/-- Captures, each at its recorded type. -/
inductive HWTCaps : List Value → List (DeclInfo × Value) → Prop
  | nil : HWTCaps [] []
  | cons {v : Value} {vs : List Value} {d : DeclInfo} {T : Value} {rd : List (DeclInfo × Value)} :
      HWT (tyOf K ρ φ T) v → HWTCaps vs rd → HWTCaps (v :: vs) ((d, T) :: rd)

/-- Values, each well typed at some type. -/
inductive HWTVals : List Value → Prop
  | nil : HWTVals []
  | cons {T : TyM} {v : Value} {vs : List Value} : HWT T v → HWTVals vs → HWTVals (v :: vs)

/-- A term: each value written in it is well typed at some type. -/
inductive HWTerm : Term → Prop
  | mk {t : Term} : HWTVals t.vals → HWTerm t
end

/-- A type value is no member of `Nat`, even partly moved. -/
theorem ty_not_pmem_nat (X : TyM) : ¬ DataModel.pmem K.dm.read K.Γ (.ty X) TyM.nat := by
  rintro (h | ⟨t, -, hm, hmem | hopen⟩)
  · cases h
  · cases hm with
    | refl => obtain ⟨n, hn⟩ := hmem; cases hn
  · cases hm with
    | refl => exact hopen

/-- The predicate excludes the counterexample to `conv_sound_stmt` (`Rules/Counter.lean`):
`Eq(Nat, And(True, Nat), Nat)` is no hereditarily well-typed proposition, since its left side, a type,
is no number. -/
theorem vBad_not_hwt (T : TyM) : ¬ HWT K ρ φ T Counter.vBad := by
  intro h
  cases h with
  | atom hm _ => exact hm
  | tEq _ _ ha _ =>
    have e : tyOf K ρ φ .tNat = TyM.nat := rfl
    rw [e] at ha
    cases ha with
    | atom hm _ => exact hm
    | tInd hp _ _ =>
      revert hp; simp only [meanV]
      split <;> exact ty_not_pmem_nat K _

/-! The first statement of A under the predicate (`convV_sound_hwt`, a `sorry`'d guess: convertible
values, both `HWT` at one type, mean the same there, from `PremSound` and `LibOk`) is replaced by
`Rules/SoundT.lean`'s `convV_alike`: proved, with the claim strengthened to two parts (type values at
possibly different universes), and with the code cases as a named hypothesis (`CodeOk`) on a closed
class of values. As written it is believed false for code: `HWTerm` types each value written in
code at SOME type, so a sealed program `⌈Eq(D(Nat), Nil(Unit;), Nil(Nat;))⌉` and its `==`-copy
`⌈Eq(D(Nat), Nil(Nat;), Nil(Nat;))⌉` (`==` ignores recorded parameters) are both well typed
propositions and mean `False` and `True` when the data model's record keeps the type parameter
(a guess: not kernel-checked, since a run context meeting `LibOk` has to be built). -/

end

end Ochr.Meaning.Rules
