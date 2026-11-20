import Ochr.Meaning.Run
import Ochr.Examples.Nat

/-!
# The reference read a constructor value through another declaration of the same carrier (built; fixed by D32)

docs/31 D31 (fifth lead, 2026-11-19; found attacking L2, the drop's write of `⊥` at a path). The
reference navigates data by its TYPE MEANING: a match's tag (`indTag`), a field read
(`Sem.follow`, `Sem.stepField`), a write or drop at a path (`Sem.updAt`) and [Rec]'s rank all
decode a constructor value's meaning through `TyM.dataOf`, the FIRST declaration of `Γ` (with
parameters chosen classically, `DataModel.paramsOf`) whose carrier is the type's. Carriers do not
determine declarations: two declarations may have equal carriers, which Lean can neither prove nor
refute for two types of the same size, and a data model may make true. Then the reference decodes
the value with the other declaration's constructors and fields.

The model below satisfies every law of `DataModel` and covers both declarations (as `CtxOk`
requires of `Γ`): `B1 := T1 | F1` and `B2 := F2 | T2`, both with carrier `Bool`, `B1` storing `T1`
as `true` and `B2` storing `T2` as `true`. The checker's `T2` (constructor 1 of `B2`) means
`el0 Bool true`, at the type `B2`, whose meaning is `ty0 Bool`; the reference's match reads its
tag through `B1` and gets constructor `0` (`tag_wrong`), so it takes the arm `F2`. On the program
`match T2 { F2 => Z, T2 => S(Z) }` the reference computes `Z` where the checker computes `S(Z)`,
and so `Id(Nat, …, S(Z))`, which the checker proves by `refl`, is false in the model. The same
decoding is in the field read, the write and the drop at a path (`Sem.stepField`, `Sem.updAt`):
there the other declaration's field list is read and its name written into the result.

So every step lemma that navigates data is false at this model, and at the generic model it is
unprovable (a proof would have to refute that an earlier declaration's carrier equals the value's,
which for two carriers of the same size Lean cannot do). The fix (D31): decode by the type's
structured data (`TyS.data`: the declaration's NAME and the parameters' meanings, which every
binding's type and every field's hint already carry, D8), never by its carrier.

Fixed, first by decoding through the type's declaration name (D31), then for good by D32: a
constructor value describes itself (`Sem.dat`: name, parameters, constructor, fields, element), so
the match reads `T2`'s constructor off the value at any type (`tag_right`), and the value is a member
of `B2`'s code (`T2_mem`). The counterexample against the old definitions is kept, unbuilt, in
`DataOfChoice_189132fd.lean`.
-/

open Ochr.Test

ochr DataOfChoice uses Nats {
  inductive B1 := T1 | F1
  inductive B2 := F2 | T2
  -- the match on `T2` takes the arm `T2`: the checker proves its result is `S(Z)`
  def PickT2 : Nat := (let x = T2; match x { F2 => Z, T2 => S(Z) })
  def PickT2Is : Id(Nat, PickT2, S(Z)) := refl
  -- the control: the result is not `Z`
  reject def PickT2Z : Id(Nat, PickT2, Z) := refl
}

namespace Ochr.Meaning.Regress.DataOfChoice
open Ochr Ochr.Meaning

def B1 : IndDecl := { name := "B1", ctors := [("T1", []), ("F1", [])] }
def B2 : IndDecl := { name := "B2", ctors := [("F2", []), ("T2", [])] }

/-- The element of constructor `c`: `B1`'s `T1` and `B2`'s `T2` are `true`. -/
def enc (d : IndDecl) (c : Nat) : Bool := if d.name = "B1" then c == 0 else c == 1
/-- The constructor of an element. -/
def dec (d : IndDecl) (x : Bool) : Nat := if d.name = "B1" then (if x then 0 else 1) else (if x then 1 else 0)

theorem covers_cases {d : IndDecl} (hd : d = B1 ∨ d = B2) :
    (d.name = "B1" ∧ d.ctors = B1.ctors) ∨ (d.name = "B2" ∧ d.ctors = B2.ctors) := by
  rcases hd with rfl | rfl
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- A lawful data model of `B1` and `B2` with the carrier `Bool` for both. -/
noncomputable def dm : DataModel where
  covers d := d = B1 ∨ d = B2
  car _ _ := Bool
  fieldTy _ _ _ _ _ := .err
  paramTy _ _ _ := .err
  pack d _ c fs := if c < 2 ∧ fs = [] then some (enc d c) else none
  tag := fun {d} {_} x => dec d x
  fields _ := []
  rank _ := 0
  tag_pack {d ps c fs} x hd h := by
    by_cases hc : c < 2 ∧ fs = []
    · simp only [hc, and_self, ↓reduceIte, Option.some.injEq] at h
      subst h
      obtain ⟨hc, -⟩ := hc
      have : c = 0 ∨ c = 1 := by omega
      rcases covers_cases hd with ⟨hn, -⟩ | ⟨hn, -⟩ <;> rcases this with rfl | rfl <;> simp [enc, dec, hn]
    · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  fields_pack {d ps c fs} x hd h := by
    by_cases hc : c < 2 ∧ fs = []
    · exact hc.2.symm
    · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  pack_fields {d ps} x hd := by
    rcases covers_cases hd with ⟨hn, -⟩ | ⟨hn, -⟩ <;> cases x <;> simp [enc, dec, hn]
  pack_isSome {d ps c fs} hd := by
    rcases covers_cases hd with ⟨-, hc⟩ | ⟨-, hc⟩ <;>
    · rw [hc]
      constructor
      · intro h
        have h' : c < 2 ∧ fs = [] := by
          by_cases h2 : c < 2 ∧ fs = []
          · exact h2
          · simp [h2] at h
        obtain ⟨h1, rfl⟩ := h'
        have : c = 0 ∨ c = 1 := by omega
        rcases this with rfl | rfl <;> simp [B1, B2]
      · rintro ⟨ctor, hct, hlen, -⟩
        have hc2 : c < 2 := by
          rcases c with _ | _ | c <;> simp_all [B1, B2]
        have hfs : fs = [] := by
          have h0 : ctor.2 = [] := by
            rcases c with _ | _ | c <;> simp [B1, B2] at hct <;> first | omega | (subst hct; rfl)
          exact List.eq_nil_of_length_eq_zero (by rw [hlen, h0]; rfl)
        simp [hc2, hfs]
  rank_lt _ _ _ _ h _ := by cases h

/-- The decisions play no part. -/
def D : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  «copy» _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := []
  rePointed _ _ := []
  typeDecl _ _ := .other

/-- The run context: the model above, `Γ = [B1, B2]` (the order the program declares them in);
the code meaning and the decisions play no part. -/
noncomputable def K : RunCtx where
  dm := dm
  Γ := [B1, B2]
  C := { global := fun _ => (.err, .plain .err), sealed := fun _ _ _ _ => .err,
         clo := fun _ _ _ _ _ => .err, pi := fun _ _ _ _ _ => .err, paramTy := fun _ _ _ _ => .plain .err }
  D := D



variable (ρ : Assignment) (φ : Future) (H : TyS)

/-- The checker's `T2` means constructor `1` of `B2`, describing itself (docs/31 D32): its
declaration's name, no parameters, constructor `1`, no fields, and its element `true` of `Bool`. -/
theorem mean_T2 : Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] []) =
    .dat "B2" [] 1 [] (some ⟨Bool, true⟩) := by
  simp [Value.mean, K, B1, B2, Value.meanParams, Value.meanFields, DataModel.ctorM, dm, enc]

/-- The type `B2` is a code naming `B2`, decoding to `Bool`, the carrier of `B1` too. -/
theorem mean_B2 : Value.mean K.dm K.C K.Γ ρ φ H (.tInd "B2" []) = .ty (.t0 Bool (.data B2 [] Bool)) := by
  simp [Value.mean, K, B1, B2, Value.meanParams, DataModel.tyM, DataModel.parsOf, dm]

/-- **The reference's match reads constructor `1`** at any type the value is held at: the value is
read, not decoded through a declaration found by its carrier (`DataOfChoice_189132fd`: the match
took the arm `F2`) or through its type at all. -/
theorem tag_right (T : TyS) : indTag (Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] [])) T = .el0 Nat 1 := by
  rw [mean_T2]; rfl

/-- The value is a member of its type: its name and parameters are the code's and its element reads
back as its constructor and fields. -/
theorem T2_mem : Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] []) ∈ₛ[dm.read] dm.tyM B2 [] := by
  rw [mean_T2]
  refine ⟨true, ?_⟩
  simp [DataModel.tyM, DataModel.parsOf, dm, B2, dec, Code0.enc, readOf, Par0.sems]

/-- A value held at a type that names no declaration (as a call's result was typed, `.plain`) is
still read: since D32 nothing is decoded through a type. -/
theorem indTag_plain (T : TyM) : indTag (.dat "B2" [] 1 [] (some ⟨Bool, true⟩)) (.plain T) = .el0 Nat 1 := rfl

end Ochr.Meaning.Regress.DataOfChoice
