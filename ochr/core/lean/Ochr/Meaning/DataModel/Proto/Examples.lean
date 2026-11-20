import Ochr.Meaning.DataModel.Proto.Program

/-!
# Prototype (b2), concrete: the probe programs' values are members, with no fixed point

Each value below is the meaning the reference run gives the probe's constructor value
(`DataModel/Probes.lean`, verdicts asserted by the build), written as a tree: its declaration's
name, its type's record, its constructor, its fields. Membership is proved from `mem_iff` alone:
no reading, no carrier, nothing built before. Kernel-checked; `#print axioms` at the end.
-/

namespace Ochr.Meaning.DataModel.Proto

/-! ## `Word`, `Bool` -/

def wordR : Rec := constRec .none
def zeroV : Val := .dat "Word" wordR 0 []
def succV (m : Val) : Val := .dat "Word" wordR 1 [m]

theorem zero_mem : Mem S wordD wordR zeroV := mem_intro wordD wordR ⟨0, by decide⟩ [] rfl

theorem succ_mem (m : Val) (hm : Mem S wordD wordR m) : Mem S wordD wordR (succV m) := by
  refine mem_intro wordD wordR ⟨1, by decide⟩ [m] ?_
  exact ⟨m, [], rfl, hm, rfl⟩

theorem small_zeroV : zeroV.small = zeroS := rfl
theorem small_succV (m : Val) : (succV m).small = succS m.small := rfl

def boolR : Rec := constRec .none
def falseV : Val := .dat "Bool" boolR 0 []
def trueV : Val := .dat "Bool" boolR 1 []

theorem false_mem : Mem S boolD boolR falseV := mem_intro boolD boolR ⟨0, by decide⟩ [] rfl
theorem true_mem : Mem S boolD boolR trueV := mem_intro boolD boolR ⟨1, by decide⟩ [] rfl


/-! ## `List(Nat)`, `Rose(Nat)` (nested), and `CountF`'s recursive call -/

def natE : Entry := .leaf Nat .nat
def nilV (r : Rec) : Val := .dat "List" r 0 []
def consV (r : Rec) (x xs : Val) : Val := .dat "List" r 1 [x, xs]

theorem nil_mem (r : Rec) : Mem S listD r (nilV r) := mem_intro listD r ⟨0, by decide⟩ [] rfl

theorem cons_mem (r : Rec) (x xs : Val) (hx : FitsOneM S (shapeOf (r [])) x) (hxs : Mem S listD r xs) :
    Mem S listD r (consV r x xs) := by
  refine mem_intro listD r ⟨1, by decide⟩ [x, xs] ?_
  exact ⟨x, [xs], rfl, hx, xs, [], rfl, hxs, rfl⟩

/-- `Rose(Nat)`'s record, and `List(Rose(Nat))`'s: `List`'s record whose entry is `Rose(Nat)`. -/
def roseNatR : Rec := constRec natE
def forestR : Rec := constRec (.data roseD roseNatR)
def nodeV (a : Nat) (kids : Val) : Val := .dat "Rose" roseNatR 0 [.el0 Nat a, kids]

theorem node_mem (a : Nat) (kids : Val) (hk : Mem S listD forestR kids) : Mem S roseD roseNatR (nodeV a kids) := by
  refine mem_intro roseD roseNatR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, ⟨a, rfl⟩, kids, [], rfl, hk, rfl⟩

/-- `CountF`'s argument in `F3` and the forest its recursive call is at, `f.0.1`. -/
def kV : Val := consV forestR (nodeV 2 (consV forestR (nodeV 3 (nilV forestR)) (nilV forestR))) (nilV forestR)
def fV : Val := consV forestR (nodeV 1 kV) (nilV forestR)

theorem kV_mem : Mem S listD forestR kV :=
  cons_mem _ _ _ (node_mem 2 _ (cons_mem _ _ _ (node_mem 3 _ (nil_mem _)) (nil_mem _))) (nil_mem _)

theorem fV_mem : Mem S listD forestR fV := cons_mem _ _ _ (node_mem 1 _ kV_mem) (nil_mem _)

/-- **`CountF`'s recursive argument has smaller rank**: the depth of the meaning decreases along
the two field steps from `f` to `k` (contrast `RankCounterexample.semRank_eq`). -/
theorem countF_decreases : kV.depth < fV.depth :=
  Nat.lt_trans (Val.depth_field_lt "Rose" roseNatR 0 [.el0 Nat 1, kV] kV (by simp))
    (Val.depth_field_lt "List" forestR 1 [nodeV 1 kV, nilV forestR] (nodeV 1 kV) (by simp))

/-! ## `Single(Single(Nat, 0), S1)`: a parameter instantiated at the declaration itself -/

def s1R : Rec := singleRec natE (.el Nat 0)
def s1V : Val := .dat "Single" s1R 0 [.el0 Nat 0, .proof]

theorem s1_mem : Mem S singleD s1R s1V := by
  refine mem_intro singleD s1R ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, ⟨0, rfl⟩, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

def s2R : Rec := singleRec (.data singleD s1R) s1V.small
def s2V : Val := .dat "Single" s2R 0 [s1V, .proof]

/-- **`S2 : Single(Single(Nat, 0), S1)` is a member** of its type; nothing about `Single` at
`(Nat, 0)` had to be built first: its member `S1` is a tree, compared small. -/
theorem s2_mem : Mem S singleD s2R s2V := by
  refine mem_intro singleD s2R ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, s1_mem, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem s2_memTy : memTy S s2V (tyOf S singleD s2R) := (memTy_tyOf S _ _ _).2 s2_mem


/-! ## `TEq(Type, Word, Word)`: a parameter of level 2, not kept -/

/-- The record of `TEq(U, a, b)`: the truth of `a = b`, whatever `U` is (`U` is dropped). -/
def teqRecOf (_U a b : Val) : Rec := teqRec (a = b)

theorem teqRecOf_U (U U' a b : Val) : teqRecOf U a b = teqRecOf U' a b := rfl

/-- `Word` as a type value, and `Type₀` as a value (a level-1 type, the code `univ1`). -/
def wordTy : Ty := tyOf S wordD wordR
def type0V : Val := .ty (.t1 _ .univ1)

def teR : Rec := teqRecOf type0V (.ty wordTy) (.ty wordTy)
def teV : Val := .dat "TEq" teR 0 [.proof]

/-- **`te : TEq(Type, Word, Word)` is a member of its type**, whose code is small (`Code`, in
`Type 1`, holding the declaration, the record and the carrier) although `Type` is not. -/
theorem te_mem : Mem S teqD teR teV := by
  refine mem_intro teqD teR ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem te_memTy : memTy S teV (tyOf S teqD teR) := (memTy_tyOf S _ _ _).2 te_mem

/-- `te2`'s shape: an equation between one (level-1) value and itself is true. -/
theorem te2_mem (a : Val) : Mem S teqD (teqRecOf type0V a a) (.dat "TEq" (teqRecOf type0V a a) 0 [.proof]) := by
  refine mem_intro teqD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-- `te3`'s: between two different values, the type is empty (the checker rejects `te3`). -/
theorem te3_empty (U a b : Val) (hab : a ≠ b) (v : Val) : ¬ Mem S teqD (teqRecOf U a b) v := by
  rw [mem_iff]
  rintro ⟨⟨c, hc⟩, fs, rfl, hf⟩
  match c, hc with
  | 0, _ =>
    obtain ⟨f, fs', rfl, h1, -⟩ := hf
    have h1' : ∃ p : PLift (a = b), encLeaf (.prop (a = b)) p = f := h1
    obtain ⟨⟨hp⟩, -⟩ := h1'
    exact hab hp
  | _ + 1, hc => exact absurd hc (by simp [teqD])

/-- `te4 := IdT(TEq(Type, Word, Word), te)`: the type is an element of `Type₀`'s carrier (its
code, nothing dropped), and `te` is the encoding of an element of its carrier, which the
identity returns. -/
theorem te4 : ∃ x : car S teqD teR, encC S (.data teqD teR (car S teqD teR)) x = teV := te_memTy

/-! ## `VecF(Nat, Succ(Zero))` over `Word` -/

def vecR (eA : Entry) (n : Val) : Rec := vecRec eA n.small
def v0 : Val := .dat "VecF" (vecR natE zeroV) 0 [.proof]
def v1 : Val := .dat "VecF" (vecR natE (succV zeroV)) 1 [zeroV, .el0 Nat 5, v0, .proof]

theorem v0_mem : Mem S vecD (vecR natE zeroV) v0 := by
  refine mem_intro vecD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem v1_mem : Mem S vecD (vecR natE (succV zeroV)) v1 := by
  refine mem_intro vecD _ ⟨1, by decide⟩ _ ?_
  exact ⟨_, _, rfl, zero_mem, _, _, rfl, ⟨5, rfl⟩, _, _, rfl, v0_mem, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

/-! ## `BW`, `BH`: type-function fields reading a `Bool` field -/

def bwR : Rec := constRec .none
theorem bw1_mem : Mem S bwD bwR (.dat "BW" bwR 0 [trueV, .el0 Unit ()]) := by
  refine mem_intro bwD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, true_mem, _, [], rfl, ⟨(), rfl⟩, rfl⟩
theorem bw0_mem : Mem S bwD bwR (.dat "BW" bwR 0 [falseV, .el0 Nat 5]) := by
  refine mem_intro bwD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, false_mem, _, [], rfl, ⟨5, rfl⟩, rfl⟩
theorem bh1_mem : Mem S bhD bwR (.dat "BH" bwR 0 [trueV, .el0 (Nat → Nat) Nat.succ]) := by
  refine mem_intro bhD bwR ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, true_mem, _, [], rfl, ⟨Nat.succ, rfl⟩, rfl⟩

/-! ## `IsZ(n) : Prop`: the proposition is that a witness tree exists -/

theorem isZ_zero : Mem S isZD (isZRec zeroS) (.dat "IsZ" (isZRec zeroS) 0 [.proof]) := by
  refine mem_intro isZD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem isZ_one_empty (v : Val) : ¬ Mem S isZD (isZRec (succS zeroS)) v := by
  rw [mem_iff]
  rintro ⟨⟨c, hc⟩, fs, rfl, hf⟩
  match c, hc with
  | 0, _ =>
    obtain ⟨f, fs', rfl, h1, -⟩ := hf
    have h1' : ∃ p : PLift (succS zeroS = zeroS), encLeaf (.prop (succS zeroS = zeroS)) p = f := h1
    obtain ⟨⟨hp⟩, -⟩ := h1'
    cases hp
  | _ + 1, hc => exact absurd hc (by simp [isZD])

/-- The proposition `IsZ(Zero)` means: the carrier is inhabited. -/
theorem isZ_zero_true : Nonempty (car S isZD (isZRec zeroS)) :=
  let ⟨x, _⟩ := (mem_iff_meanC S _ _ _).1 isZ_zero; ⟨x⟩

/-! ## `V := MkV(n : Nat, x : Fin1(n))`: a field typed by an earlier `Nat` field -/

theorem v_mem : Mem S vD bwR (.dat "V" bwR 0 [.el0 Nat 1, .dat "Fin1" (fin1Rec (.el Nat 1)) 0 [.proof]]) := by
  refine mem_intro vD bwR ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ⟨1, rfl⟩, _, [], rfl, ?_, rfl⟩
  exact mem_intro fin1D _ ⟨0, by decide⟩ _ (by exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩)

/-! ## The laws, at one instance: whole, a bijection, the rank -/

theorem te_whole : teV.whole := mem_whole S _ _ _ te_mem
theorem te_unique (x y : car S teqD teR) (hx : meanC S x = teV) (hy : meanC S y = teV) : x = y :=
  meanC_inj S x y (hx.trans hy.symm)

end Ochr.Meaning.DataModel.Proto
