import Ochr.Meaning.Regress.CallInPlace
import Ochr.Examples.Nat

/-!
# A place a returned reborrow is lent at reads its final content raw; `callOf` reads it decoded (built)

The checker's side of the finding recorded in docs/31 D66. After `let r = Id1(&a)` (`Id1 (x : &Nat)
: &Nat := &*x`, run directly), the checker holds `a ↦ lent_k loan_k`, `r ↦ borrow_k …`
(`a_after_call`, the real run of `ReturnedReadAt` evaluated): `a` means the future at `k`, whatever
it is (`meanV` of a mark is its content's, of a loan the future at its label). The reference's call
by `callOf` leaves `a` reading the future at `k` DECODED at the result's code and passed through the
backward function (`CallInPlace.callOf_id1`): at a future whose value at `k` is not a number (here
`moved`), `a` reads `err` (`callOf_reads_decoded`). The two agree at every future whose value at
`k` is a member of `Nat` (`callOf_reads_typed`).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr ReturnedReadAt uses Nats {
  def Id1 (x : &Nat) : &Nat := &*x
  def Id1At (a : Nat) : Unit := (let r = Id1(&a); ?)
}

namespace Ochr.Meaning.Regress.ReturnedRead
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CallInPlace

/-- The values of the bindings the checker holds at the hole (the function's own binding left out). -/
def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "ReturnedReadAt" ReturnedReadAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

/-- `a ↦ lent_k loan_k` and `r ↦ borrow_k _` for one label `k`. -/
def markLoan : List Value → Bool
  | [.gloan k (.loan k'), .borrow k'' _] => k == k' && k == k''
  | _ => false

-- the checker's state after the direct call: `a` holds the mark over the returned borrow's loan
#guard markLoan (atHole "Id1At")

/-- The checker's `a` means the future at `k`, raw. -/
theorem mark_loan_raw (K : RunCtx) (ρ : Assignment) (ψ : Future) (hint : TyS) (k : Nat) :
    meanV K ρ ψ hint (.gloan k (.loan k)) = ψ k := rfl

/-- **`callOf`'s `a` reads the returned label decoded**: at a future whose value at the reborrow's
label is `moved`, `y` (`a`) reads `err`, where the checker's mark reads `moved`. -/
theorem callOf_reads_decoded (dm : DataModel) (ψ : Future) (h : ψ 1 = .moved) :
    yR1 dm ψ = .err ∧ ψ 1 ≠ .err := by
  have hd : Code0.dec dm.read TyM.nat.code0.snd Sem.moved = none :=
    (Attack.dec_nat_as dm.read .moved).trans (by simp [Sem.as]; rfl)
  refine ⟨?_, by rw [h]; exact fun h' => by cases h'⟩
  simp only [yR1, h]
  rw [hd]

/-- At a future whose value at the label is a number, the two agree. -/
theorem callOf_reads_typed (dm : DataModel) (ψ : Future) (n : Nat) (h : ψ 1 = .el0 Nat n) : yR1 dm ψ = ψ 1 := by
  have hd : Code0.dec dm.read TyM.nat.code0.snd (.el0 Nat n) = some (show TyM.nat.code0.fst from n) :=
    Attack.dec_nat_el0 dm.read n
  simp only [yR1, h]
  rw [hd]
  simp [Future.upd]
  rfl

end Ochr.Meaning.Regress.ReturnedRead
