import Ochr.Meaning.DataModel.Exists.Assembly

/-!
# `GlobalCallLevels` attacked at its hard case (exists12; docs/34 §18.17)

The hard case of `Assembly.GlobalCallLevels`: a global with a domain in `Type₁` and codomain `Type`
heading an accepted field's type, so its Π-type is a level-2 code and `LeafOk.callOfL_enc` alone does
not bound its calls (the sixth referee's Y3: level 2 has `Code2.univ2`, whose encodings are level-1
type values, `univ2_not_lvl0` below). Three instances, the ones the brief named, each as resolution
builds it (`resolveProgram` on the surface text, printed and copied; the surface text is in the
docstrings):
* a constant, `def FT (A : Type₁) : Type := Nat` heading `inductive WT (A : Type₁) := MkWT(x : FT(A))`;
* the identity on a small type, `def FI (A : Type₁) (B : Type) : Type := B` heading
  `inductive WI (A : Type₁) (B : Type) := MkWI(x : FI(A, B))`;
* a match on a value, `def FM (A : Type₁) (n : Nat) : Type := match n { Z => Nat, S p => Unit }`
  heading `inductive WM (A : Type₁) := MkWM(n : Nat, x : FM(A, n))`.
Checked here: the definition is accepted and stored at `Π(A : Type₁) …. Type` (in the kernel for `FT`,
`decide +kernel`; natively for `FI` and `FM`, `#guard`, as the kernel's reduction of `checkDef`'s run
of a body that reads a parameter gets stuck); the declaration is accepted with its field headed by the
global (natively: the kernel's reduction of `checkInd`'s run of these declarations gets stuck, as
`FactsCE.tlAccepted`'s did); and the statement's conclusion at the stage after both (`hard_FT`, no
hypothesis; `hard_FI`, `hard_FM`, given the stored type checked natively). The statement is not false there: it is proved in general (`Assembly.globalCallLevels`).
-/

namespace Ochr.Meaning.DataModel.Exists.GlobalCallsHard

open Ochr Ochr.Meaning

/-- At level 2 an encoding need not be a level-0 type value: the universe `Type₁`'s code encodes
level-1 type values (the reason the referee's Y3 asks for the leaf code, not merely some code). -/
theorem univ2_not_lvl0 (R : DataRead) :
    ¬ FieldLevel.Lvl0V (Code2.enc R Code2.univ2 ⟨_, ⟨Code1.univ1, rfl⟩⟩) := by
  rintro ⟨B, cd, h⟩
  cases h

/-- `def FT (A : Type₁) : Type := Nat`. -/
def dFT : Def := { name := "FT", hs := [⟨"A"⟩], doms := [.sort 2], cod := .sort 1, body := .nat }
/-- `inductive WT (A : Type₁) := MkWT(x : FT(A))`. -/
def dWT : IndDecl :=
  { name := "WT", params := [(⟨"A"⟩, .sort 2)],
    ctors := [("MkWT", [("x", .call (.const "FT") [.place (.var 0)] false)])] }
/-- `def FI (A : Type₁) (B : Type) : Type := B`. -/
def dFI : Def := { name := "FI", hs := [⟨"A"⟩, ⟨"B"⟩], doms := [.sort 2, .sort 1], cod := .sort 1, body := .place (.var 0) }
/-- `inductive WI (A : Type₁) (B : Type) := MkWI(x : FI(A, B))`. -/
def dWI : IndDecl :=
  { name := "WI", params := [(⟨"A"⟩, .sort 2), (⟨"B"⟩, .sort 1)],
    ctors := [("MkWI", [("x", .call (.const "FI") [.place (.var 1), .place (.var 0)] false)])] }
/-- `def FM (A : Type₁) (n : Nat) : Type := match n { Z => Nat, S p => Unit }`. -/
def dFM : Def :=
  { name := "FM", hs := [⟨"A"⟩, ⟨"n"⟩], doms := [.sort 2, .nat], cod := .sort 1,
    body := .matchNat (.var 0) .nat .unit }
/-- `inductive WM (A : Type₁) := MkWM(n : Nat, x : FM(A, n))` (the field frame binds the fields, then
the parameters: `A` is `var 0`, `n` is `var 2`). -/
def dWM : IndDecl :=
  { name := "WM", params := [(⟨"A"⟩, .sort 2)],
    ctors := [("MkWM", [("n", .nat), ("x", .call (.const "FM") [.place (.var 0), .place (.var 2)] false)])] }

def pT : List Item := [.defn dFT, .ind dWT]
def pI : List Item := [.defn dFI, .ind dWI]
def pM : List Item := [.defn dFM, .ind dWM]

/-- The `k`-th item is accepted at the state the program has reached. -/
def okAt (items : List Item) (k : Nat) : Bool :=
  match items[k]? with
  | some it => match (runMachine (checkItem it) (Assembly.stSt 3000 items k) 3000).1 with
    | .ok () _ => true
    | _ => false
  | none => false

/-- After the first item, the global `f` is stored at `Π(A : Type₁) …. Type`. -/
def storedHard (items : List Item) (f : String) : Bool :=
  match ((Assembly.sig 3000 items 1).1.find? (·.name == f)).map (·.ty) with
  | some (Value.tPi [] (Term.pi _ (Term.sort 2 :: _) (Term.sort 1)) []) => true
  | _ => false

/-- After the second item, the last field of the stored declaration is headed by the global `f`. -/
def headedBy (items : List Item) (f : String) : Bool :=
  match (Assembly.sig 3000 items 2).2.getLast? with
  | some d' => match fieldTerm d' 0 ((d'.ctors.head?.map (·.2.length)).getD 1 - 1) with
    | some (.call (.const g) _ false) => g == f
    | _ => false
  | none => false

/-- The constant `FT` is accepted, at `Π(A : Type₁). Type` (kernel). -/
theorem def_FT_hard : (okAt pT 0 && storedHard pT "FT") = true := by decide +kernel

-- `FI` and `FM` likewise, natively (the kernel's reduction of `checkDef`'s run of a body that reads
-- a parameter or matches on one gets stuck; `FT`'s body, `Nat`, reads none).
#guard okAt pI 0 && storedHard pI "FI"
#guard okAt pM 0 && storedHard pM "FM"

-- The declarations are accepted with their field headed by the global (natively: the kernel's
-- reduction of `checkInd`'s run of them gets stuck).
#guard okAt pT 1 && headedBy pT "FT"
#guard okAt pI 1 && headedBy pI "FI"
#guard okAt pM 1 && headedBy pM "FM"

/-- An inductive item leaves the globals (accepted: `Steps.Machine.checkItem_tables`; rejected: Σ kept). -/
theorem sig_ind_globals (items : List Item) (d : IndDecl) (h1 : items.length = 2) (h2 : items[1]? = some (.ind d)) :
    (Assembly.sig 3000 items 2).1 = (Assembly.sig 3000 items 1).1 := by
  have ht : items.take 2 = items.take 1 ++ [.ind d] := by
    match items, h1, h2 with
    | [a, b], _, h2 => simp at h2; subst h2; rfl
  unfold Assembly.sig sigAfterFrom
  rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split
  · rename_i st' hst
    exact ((Steps.Machine.checkItem_tables _ _ st' 3000 hst).1 d rfl).2
  · rfl

theorem stored_of (items : List Item) (f : String) (h : storedHard items f = true) :
    ∃ hs ds, ((Assembly.sig 3000 items 1).1.find? (·.name == f)).map (·.ty) =
      some (.tPi [] (.pi hs (.sort 2 :: ds) (.sort 1)) []) := by
  unfold storedHard at h
  split at h
  · rename_i hs ds e; exact ⟨hs, ds, e⟩
  · cases h

/-- **The conclusion at a hard instance**, from the stored type (kernel) and `globalCallLevels`. -/
theorem hard_of (items : List Item) (d : IndDecl) (f : String) (h1 : items.length = 2) (h2 : items[1]? = some (.ind d))
    (hs : storedHard items f = true) (D : MState → Decisions) (dm dmR : DataModel) :
    FieldLevel.CallsLevel0 dmR ((Assembly.stage D 3000 items dm 2).baseC.global f) := by
  obtain ⟨hs', ds, e⟩ := stored_of items f hs
  refine Assembly.globalCallLevels D 3000 items dm 2 (by omega) f [] hs' (.sort 2 :: ds) 1 [] (Nat.le_refl 1) ?_ dmR
  rw [(Assembly.stage_sig D 3000 items dm 2).1, sig_ind_globals items d h1 h2]
  exact e

theorem hard_FT (D : MState → Decisions) (dm dmR : DataModel) :
    FieldLevel.CallsLevel0 dmR ((Assembly.stage D 3000 pT dm 2).baseC.global "FT") :=
  hard_of pT dWT "FT" rfl rfl (by have := def_FT_hard; simp only [Bool.and_eq_true] at this; exact this.2) D dm dmR

/-- At `FI`, given its stored type (checked natively above). -/
theorem hard_FI (hs : storedHard pI "FI" = true) (D : MState → Decisions) (dm dmR : DataModel) :
    FieldLevel.CallsLevel0 dmR ((Assembly.stage D 3000 pI dm 2).baseC.global "FI") :=
  hard_of pI dWI "FI" rfl rfl hs D dm dmR

/-- At `FM`, given its stored type (checked natively above). -/
theorem hard_FM (hs : storedHard pM "FM" = true) (D : MState → Decisions) (dm dmR : DataModel) :
    FieldLevel.CallsLevel0 dmR ((Assembly.stage D 3000 pM dm 2).baseC.global "FM") :=
  hard_of pM dWM "FM" rfl rfl hs D dm dmR

end Ochr.Meaning.DataModel.Exists.GlobalCallsHard
