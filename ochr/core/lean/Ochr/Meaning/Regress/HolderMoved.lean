import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# A live borrow whose content was moved out through it (built)

docs/31 D42 (fifth lead, 2026-11-21). Moving out through a borrow is allowed if the content is
whole again when the borrow ends (D53 (h)): in `MoveThrough`, between `let x = *r` and `*r := b`,
the checker's state holds `r ↦ borrow_ℓ ⊥`. The reference's meaning of a holder is its content's
final meaning, which there reads `moved`. The reference's drop at the join (`Run.dropAt`) tested
the meaning first and the holder second, so at such a holder it did nothing, where the checker's
`dropAtJoin` tests its stored value, a borrow, and ends it (`endBorrow`, which rejects a holed
content outside an observation and ends it inside one, D68). The obligation `holder_follow` (the
holder's meaning is not `moved`) was false at this state. Fixed in the reference: the holder is
tested first, by its shape, as the checker tests its stored value; `holder_follow` is deleted.
-/

open Ochr.Test

ochr HolderMoved uses Nats, Lists {
  def MoveThrough (a : List(Nat)) (b : List(Nat)) : List(Nat) := (let r = &a; let x = *r; *r := b; x)
}

namespace Ochr.Meaning.Regress.HolderMoved
open Ochr Ochr.Meaning

/-- Some binding of the top frame holds a borrow whose content is `⊥`. -/
def holdsMovedBorrow (st : MState) : Bool :=
  match st.env.back? with
  | some fr => fr.binds.toList.any fun b => match b.val with | .borrow _ .bot => true | _ => false
  | none => false

/-- The checker's recorded states while checking `MoveThrough`. -/
def states : List MState :=
  let r := Ochr.Test.runWith (some Prelude) "HolderMoved" HolderMoved { recordStates := true } (located := true)
  match r.rows.find? (·.name == "MoveThrough") with
  | some row => row.trace.toList.filterMap fun | .state _ _ _ st => some st | _ => none
  | none => []

#guard states.any holdsMovedBorrow

end Ochr.Meaning.Regress.HolderMoved
