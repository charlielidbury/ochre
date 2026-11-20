import Ochr.Meaning.DataModel.Proto.Residual

/-!
# Where K3 could be wrong: the accepted adversarial declarations, in the prototype (docs/34 §13)

The checker's verdicts are asserted in `DataModel/Probes.lean` (`DMProbeAdv`). Each accepted
declaration whose field types depend on a parameter above level 0 is modelled here with a record
that keeps only small things, and its probe's value is a member.

* `H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λx. f(Succ(x))))`: non-uniform
  recursion at a large parameter that a field type applies. The record must keep the codes
  `f(0), f(1), …` along the whole unfolding (`hRec`), not only at the root; a child's record is the
  parent's shifted (`shiftRec`), which is the record of the child's own parameter (`shift_hRec`).
* `MM (G : Π(X : Type). Word) := MkMM(y : MG(G))`, `MG(G) := match G(Word) {…}`: a large function
  applied in a field type and its result matched. The record keeps the code the match gives.
* `FP (f : Π(x : Word). Word) := MkFP(y : Word, e : Eq(Word, f(y), y))`: a function-valued
  (level-0) parameter applied in an equation field. The record keeps the equation as a function
  of `y` read small.
-/

namespace Ochr.Meaning.DataModel.Proto

/-! ## `H`: the record keeps the codes along the unfolding -/

theorem shift_hRec (g : Nat → Entry) : shiftRec (hRec g) = hRec (fun k => g (k + 1)) := by
  funext st
  unfold shiftRec
  split
  · rfl
  · rename_i hne
    unfold hRec
    split
    · rename_i k; exact absurd rfl (hne k)
    · rfl

/-- `H(λx. Word)`: `App0` gives `Word` at every depth. -/
def gWord : Nat → Entry := fun _ => .data wordD wordR
def hR : Rec := hRec gWord

/-- `hh := HS(Zero, HB)` (accepted). -/
def hhV : Val := .dat "H" hR 1 [zeroV, .dat "H" (shiftRec hR) 0 []]

theorem hh_mem : Mem S hD hR hhV := by
  refine mem_intro hD hR ⟨1, by decide⟩ _ ?_
  refine ⟨_, _, rfl, zero_mem, _, [], rfl, ?_, rfl⟩
  exact mem_intro hD _ ⟨0, by decide⟩ [] rfl

/-! ## `MM`: a large function applied and matched -/

def mmR0 : Rec := mmRec (.data wordD wordR)
def mmR1 : Rec := mmRec (.leaf Unit .unit)

/-- `mm0 : MM(λX. Zero)` (`MG` gives `Word`) and `mm1 : MM(λX. Succ(Zero))` (`Unit`). -/
theorem mm0_mem : Mem S mmD mmR0 (.dat "MM" mmR0 0 [zeroV]) := by
  refine mem_intro mmD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, zero_mem, rfl⟩

theorem mm1_mem : Mem S mmD mmR1 (.dat "MM" mmR1 0 [.el0 Unit ()]) := by
  refine mem_intro mmD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨(), rfl⟩, rfl⟩

/-- `mm0Bad` (rejected): `()` is not a member of `MM(λX. Zero)`'s field type. -/
theorem mm0Bad_not (fs : List Val) : ¬ Mem S mmD mmR0 (.dat "MM" mmR0 0 (.el0 Unit () :: fs)) := by
  rw [mem_iff]
  rintro ⟨⟨c, hc⟩, gs, he, hf⟩
  simp only [Val.dat.injEq, true_and] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨f, fs', hfs, h1, -⟩ := hf
  simp only [List.cons.injEq] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have h1' : Mem S wordD wordR (.el0 Unit ()) := h1
  rw [mem_iff] at h1'
  obtain ⟨_, _, he', _⟩ := h1'
  cases he'

/-! ## `FP`: a function-valued parameter applied in an equation -/

/-- `FP(λx. x)`: the equation `f(y) = y` holds at every `y`. -/
def fpR : Rec := fpRec (fun _ => True)

theorem fp_mem : Mem S fpD fpR (.dat "FP" fpR 0 [zeroV, .proof]) := by
  refine mem_intro fpD _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, zero_mem, _, [], rfl, ⟨⟨trivial⟩, rfl⟩, rfl⟩

end Ochr.Meaning.DataModel.Proto
