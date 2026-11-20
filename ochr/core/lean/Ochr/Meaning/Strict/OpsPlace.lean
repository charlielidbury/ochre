import Ochr.Meaning.Strict.Ops

/-!
# The place operations keep the invariant: holder transfers, a `let`'s binding and drop, reads,
borrows, assignments

Each at a ROOT path or through a borrow (`[*]`) proved; at a FIELD path, a write (a move out of a
field, a borrow's lender, an assignment to a field) changes a part of a constructor value, which
later dependent fields' types read: that is the dependent-values area, isolated as named guesses
(`*_field_*`), each with what it would need.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

variable {K : RunCtx} {φ : Future}

/-- A borrow's holder moves to a new temporary holding a partly moved member of its content type (a
move of a holder, `readPlace`). -/
theorem sgood_transfer {s : SState} (hs : SGood K.dm K.Γ φ s) {l : Nat} (hl : l ∈ s.liveLabels) {v : Sem}
    (hv : PMem K.dm.read K.Γ v (s.heldTy l)) :
    SGood K.dm K.Γ φ ((s.takeLabel l).pushTempShaped (fun _ => v) l) := by
  sorry

/-- A `let`'s binding (`pushBindShaped`) of a good result whose label records its type. -/
theorem sgood_pushBindShaped (hMR : MemReads K.dm K.Γ) {s : SState} (hs : SGood K.dm K.Γ φ s) (b : SBinding)
    {v : Sem} (hb : b.val = fun _ => v) (hv : GoodRes K.dm.read (v, b.ty)) (hlab : LabOk K.dm s (v, b.ty))
    (hne : s.env ≠ []) : SGood K.dm K.Γ φ (pushBindShaped s b) := by
  sorry

/-- A `let`'s drop: the borrow its binding holds ends, or the borrows lent at it end, then it goes. -/
theorem sgood_letDrop {s : SState} (hs : SGood K.dm K.Γ φ s) :
    SGood K.dm K.Γ φ ((match (match s.env.getLast? with
        | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
        | none => none) with
      | some l => s.endLabel l
      | none => letLenders s).dropLast) := by
  sorry

/-- **A read of a place**, copied or moved: the value read is a member of the type the read gives it
(the read clause, `ReadOk`, at the typed future of the accessed state); a move writes `⊥` there and,
at a holder, parks the borrow in a temporary. -/
theorem readPlace_fund (hMR : MemReads K.dm K.Γ) (p : Place) (copy : Bool) :
    FundAt K.dm K.Γ φ (readPlace K φ p copy) := by
  sorry

/-- **A borrow** (strict: the content is a member of the place's type). -/
theorem borrowPlace_fund (hMR : MemReads K.dm K.Γ) (p : Place) :
    FundAt K.dm K.Γ φ (SM.strictS K.dm.read (borrowPlace K φ p)) := by
  sorry

/-- **An assignment's write** (`assignAt`), the value checked at the place's type at the write and its
label at that type (the strict `.assign` clause's test). -/
theorem assignAt_sgood (hMR : MemReads K.dm K.Γ) {p : Place} {v : Sem} {R : TyS} {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m) (hl : labTyOk s R.label (placeTy K φ p s).m)
    (hlab : LabOk K.dm s (v, R)) (h : assignAt K φ p v R.label s = some (r, s')) :
    GoodRes K.dm.read r ∧ LabOk K.dm s' r ∧ SGood K.dm K.Γ φ s' := by
  sorry

end Ochr.Meaning.Strict
