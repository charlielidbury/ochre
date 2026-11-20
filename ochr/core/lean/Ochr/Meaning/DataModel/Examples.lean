import Ochr.Meaning.DataModel.Program

/-!
# The probe programs' values are members (docs/34 §10, §14; kernel-checked)

Each value below is the meaning the reference run gives the probe's constructor value
(`DataModel/Probes.lean`, verdicts asserted by the build), a tree: its declaration's name, its
type's record, its constructor, its fields. Membership is proved from `mem_iff` alone, at the
probe programs' data model (`Program.dmP`). `List`, `Rose` and `CountF` are in
`Regress/DataCodes.lean`.

**`te : TEq(Type, Word, Word)` is a member of its type** (`te_ctorM_memTy`): the run's constructor
value at parameters whose first is `Type` (a level-1 type, which no level-0 code holds). Before the
port a code held its parameters, so this value was a member of no code of its type, at every data
model (`Counterexamples.ctorM_large_not_mem`, against the frozen copy); now the code keeps a record,
and `TEq`'s keeps only the truth of `a = b`.
-/

namespace Ochr.Meaning.DataModel.Program

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-! ## `Word`, `Bool` -/

def wordR : Rec := constRec .none
def zeroV : Sem := .dat "Word" wordR 0 []
def succV (m : Sem) : Sem := .dat "Word" wordR 1 [m]

theorem zero_mem : dmP.Mem wordD wordR zeroV := mem_intro wordD wordR ⟨0, by decide⟩ [] rfl

theorem succ_mem (m : Sem) (hm : dmP.Mem wordD wordR m) : dmP.Mem wordD wordR (succV m) := by
  refine mem_intro wordD wordR ⟨1, by decide⟩ [m] ?_
  exact ⟨m, [], rfl, hm, rfl⟩

theorem small_zeroV : zeroV.small = zeroS := rfl
theorem small_succV (m : Sem) : (succV m).small = succS m.small := rfl

def boolR : Rec := constRec .none
def falseV : Sem := .dat "Bool" boolR 0 []
def trueV : Sem := .dat "Bool" boolR 1 []

theorem false_mem : dmP.Mem boolD boolR falseV := mem_intro boolD boolR ⟨0, by decide⟩ [] rfl
theorem true_mem : dmP.Mem boolD boolR trueV := mem_intro boolD boolR ⟨1, by decide⟩ [] rfl

def natE : Entry := .leaf Nat .nat

/-! ## `Single(Single(Nat, 0), S1)`: a parameter instantiated at the declaration itself -/

def s1R : Rec := singleRec natE (.el Nat 0)
def s1V : Sem := .dat "Single" s1R 0 [.el0 Nat 0, .proof]

theorem s1_mem : dmP.Mem singleD s1R s1V := by
  refine mem_intro singleD s1R ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, ⟨0, rfl⟩, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-- `Single(Nat, 0)`'s record is the record at its parameters. -/
theorem s1R_recOf : dmP.recOf singleD [.ty TyM.nat, .el0 Nat 0] = s1R := rfl

def s2R : Rec := singleRec (.data singleD s1R) s1V.small
def s2V : Sem := .dat "Single" s2R 0 [s1V, .proof]

/-- **`S2 : Single(Single(Nat, 0), S1)` is a member** of its type; nothing about `Single` at
`(Nat, 0)` had to be built first: its member `S1` is a tree, compared small. -/
theorem s2_mem : dmP.Mem singleD s2R s2V := by
  refine mem_intro singleD s2R ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, s1_mem, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem s2R_recOf : dmP.recOf singleD [.ty (dmP.tyR singleD s1R), s1V] = s2R := rfl

theorem s2_memTy : s2V ∈ₛ[dmP.read] dmP.tyR singleD s2R := (DataModel.mem_tyR dmP _ _ rfl _).2 s2_mem

/-! ## `TEq(Type, Word, Word)`: a parameter of level 2, not kept -/

/-- `Word` as a type value, and `Type₀` as a value (what the run's `.sort` clause gives). -/
def wordTy : TyM := dmP.tyR wordD wordR
def type0V : Sem := .ty (TyM.univ 1)

/-- `te`'s parameters, and its type's record: the truth of `Word = Word`. -/
def psTE : List Sem := [type0V, .ty wordTy, .ty wordTy]
def teR : Rec := dmP.recOf teqD psTE
def teV : Sem := .dat "TEq" teR 0 [.proof]

theorem teR_eq : teR = teqRec (Sem.ty wordTy = Sem.ty wordTy) := rfl

/-- The record of `TEq(U, a, b)` does not depend on `U`. -/
theorem teqRec_U (U U' a b : Sem) : dmP.recOf teqD [U, a, b] = dmP.recOf teqD [U', a, b] := rfl

theorem te_mem : dmP.Mem teqD teR teV := by
  refine mem_intro teqD teR ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-- **`te : TEq(Type, Word, Word)` is a member of its type**: the run's constructor value
(`ctorM`, at the written parameters) is a member of the code the run gives `TEq(Type, Word, Word)`
(`tyM`). Its code is small (`Code0`, holding the declaration, the record and the carrier) although
`Type` is not. -/
theorem te_ctorM_memTy : dmP.ctorM teqD psTE 0 [.proof] ∈ₛ[dmP.read] dmP.tyM teqD psTE :=
  (DataModel.mem_tyR dmP _ _ rfl _).2 te_mem

/-- `te2`'s shape: an equation between one (level-1) value and itself is true. -/
theorem te2_mem (a : Sem) :
    dmP.Mem teqD (dmP.recOf teqD [type0V, a, a]) (.dat "TEq" (dmP.recOf teqD [type0V, a, a]) 0 [.proof]) := by
  refine mem_intro teqD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-- `te3`'s: between two different values, the type is empty (the checker rejects `te3`). -/
theorem te3_empty (U a b : Sem) (hab : a ≠ b) (v : Sem) : ¬ dmP.Mem teqD (dmP.recOf teqD [U, a, b]) v := by
  intro hv
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (mem_iff S teqD _ v).1 hv
  match c, hc with
  | 0, _ =>
    obtain ⟨f, fs', rfl, h1, -⟩ := hf
    have h1' : ∃ p : PLift (a = b), encLeaf (.prop (a = b)) p = f := h1
    obtain ⟨⟨hp⟩, -⟩ := h1'
    exact hab hp
  | _ + 1, hc => exact absurd hc (by simp [teqD])

/-- `te4 := IdT(TEq(Type, Word, Word), te)`: the type is an element of `Type₀`'s carrier (its
code, nothing dropped), and `te` is the reading of an element of its carrier, which the identity
returns. -/
theorem te4 : ∃ x : dmP.car teqD teR, dmP.read.read teqD teR (dmP.car teqD teR) x = teV := by
  obtain ⟨x, hx⟩ := (DataModel.mem_iff_meanC dmP _ _ _).1 te_mem
  exact ⟨x, (DataModel.read_car dmP x).trans hx⟩

/-! ## `VecF(Nat, Succ(Zero))` over `Word` -/

def vecR (eA : Entry) (n : Sem) : Rec := vecRec eA n.small
def v0 : Sem := .dat "VecF" (vecR natE zeroV) 0 [.proof]
def v1 : Sem := .dat "VecF" (vecR natE (succV zeroV)) 1 [zeroV, .el0 Nat 5, v0, .proof]

theorem vecR_recOf (n : Sem) : dmP.recOf vecD [.ty TyM.nat, n] = vecR natE n := rfl

theorem v0_mem : dmP.Mem vecD (vecR natE zeroV) v0 := by
  refine mem_intro vecD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem v1_mem : dmP.Mem vecD (vecR natE (succV zeroV)) v1 := by
  refine mem_intro vecD _ ⟨1, by decide⟩ _ ?_
  exact ⟨_, _, rfl, zero_mem, _, _, rfl, ⟨5, rfl⟩, _, _, rfl, v0_mem, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-! ## `BW`, `BH`: type-function fields reading a `Bool` field -/

def bwR : Rec := constRec .none
theorem bw1_mem : dmP.Mem bwD bwR (.dat "BW" bwR 0 [trueV, .el0 Unit ()]) := by
  refine mem_intro bwD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, true_mem, _, [], rfl, ⟨(), rfl⟩, rfl⟩
theorem bw0_mem : dmP.Mem bwD bwR (.dat "BW" bwR 0 [falseV, .el0 Nat 5]) := by
  refine mem_intro bwD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, false_mem, _, [], rfl, ⟨5, rfl⟩, rfl⟩
theorem bh1_mem (g : NatFn) : dmP.Mem bhD bwR (.dat "BH" bwR 0 [trueV, .el0 NatFn g]) := by
  refine mem_intro bhD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, true_mem, _, [], rfl, ⟨g, rfl⟩, rfl⟩

/-! ## `IsZ(n) : Prop`: the proposition is that a witness tree exists -/

theorem isZ_zero : dmP.Mem isZD (isZRec zeroS) (.dat "IsZ" (isZRec zeroS) 0 [.proof]) := by
  refine mem_intro isZD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem isZ_one_empty (v : Sem) : ¬ dmP.Mem isZD (isZRec (succS zeroS)) v := by
  intro hv
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (mem_iff S isZD _ v).1 hv
  match c, hc with
  | 0, _ =>
    obtain ⟨f, fs', rfl, h1, -⟩ := hf
    have h1' : ∃ p : PLift (succS zeroS = zeroS), encLeaf (.prop (succS zeroS = zeroS)) p = f := h1
    obtain ⟨⟨hp⟩, -⟩ := h1'
    cases hp
  | _ + 1, hc => exact absurd hc (by simp [isZD])

/-- The proposition `IsZ(Zero)` is true: its type is the proposition that it has a member. -/
theorem isZ_zero_true : dmP.tyM isZD [zeroV] = TyM.prop (∃ v, dmP.Mem isZD (isZRec zeroS) v) ∧
    ∃ v, dmP.Mem isZD (isZRec zeroS) v :=
  ⟨DataModel.tyR_prop dmP _ _ rfl, ⟨_, isZ_zero⟩⟩

/-! ## `V := MkV(n : Nat, x : Fin1(n))`: a field typed by an earlier `Nat` field -/

theorem v_mem : dmP.Mem vD bwR (.dat "V" bwR 0 [.el0 Nat 1, .dat "Fin1" (fin1Rec (.el Nat 1)) 0 [.proof]]) := by
  refine mem_intro vD bwR ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ⟨1, rfl⟩, _, [], rfl, ?_, rfl⟩
  refine mem_intro fin1D _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-! ## The laws, at one instance: whole, a bijection -/

theorem te_whole : teV.whole := mem_whole S _ _ _ te_mem
theorem te_unique (x y : dmP.car teqD teR) (hx : dmP.meanC x = teV) (hy : dmP.meanC y = teV) : x = y :=
  meanC_inj S x y (hx.trans hy.symm)

end Ochr.Meaning.DataModel.Program
