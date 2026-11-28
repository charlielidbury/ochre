import Ochr.Meaning.Steps.CallGAttack
import Ochr.Meaning.Steps.CallStep

/-!
# The checker facts of the in-place call step, attacked on the checker (lead39, 2026-11-28; docs/31 D241)

At the hole of `CallGAttack`'s `At` (`a ↦ σa`, `c ↦ σc`, `b ↦ Z`), the calls run in place and closed off, typed and
untyped, checked against what `Steps/CallStep` assumes of the checker:
- `OccursLiveG` ((WF2)): after each call every label occurring in the state is live (a loan or a borrow of a label
  whose borrow is held). Pinned at `Ip(Z)`, `Ip(c)`, `Pr(c)` (closed off), `Inc(&b)` (a borrow argument, data result),
  `Kr(&b)` (a borrow result, lender marked): every label below the counter that occurs is live.
- `CallRanSimG` (i) and (v), the reserved label: at a borrow codomain the result's label is the one reserved at the call
  point, the counter after the arguments (`Kr`: `stH.nextLoan + 1`, the argument's borrow taking `stH.nextLoan`), on the
  in-place path as on the closed-off one; at a data codomain no label survives the call (`Inc`: none occurs).
-/

namespace Ochr.Meaning.Steps.Form.CallStepGuards

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Steps.Form.CallGAttack
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The label `l` occurs in the state (`MState.Occurs`, decided). -/
def occurs (st : MState) (l : Nat) : Bool :=
  (Env.values st.env).any fun v =>
    v.anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false))

/-- `OccursLiveG` at a state: every label below the counter that occurs is live. -/
def occursLive (st : MState) : Bool :=
  (List.range st.nextLoan).all fun l => !occurs st l || liveLoan st.env l

/-- The labels that occur. -/
def occLabels (st : MState) : List Nat := (List.range st.nextLoan).filter (occurs st)

/-- The state after a call with its result held as a temporary (what `Rel` relates after the step,
`st₁.withTempT v T?`). -/
def after (typed : Bool) (t : Term) : MState :=
  let r := outVal (CallGAttack.run typed t) stH 1000000
  (outSt (CallGAttack.run typed t) stH 1000000).withTempT r.1 r.2

#guard occursLive stH
#guard occursLive (after true (callG "Ip" [.zero]))
#guard occursLive (after false (callG "Ip" [.zero]))
#guard occursLive (after true (callG "Ip" [.place (.var 1)]))
#guard occursLive (after true (callG "Pr" [.place (.var 1)]))
#guard occursLive (after false (callG "Pr" [.place (.var 1)]))
#guard occursLive (after true (callG "Inc" [.borrow (.var 0)]))
#guard occursLive (after false (callG "Inc" [.borrow (.var 0)]))
#guard occursLive (after true (callG "Kr" [.borrow (.var 0)]))
#guard occursLive (after false (callG "Kr" [.borrow (.var 0)]))
-- without its result the state after `Kr(&b)` is not (WF2): the lender's mark outlives nothing only because the
-- result holds the borrow; `OccursLiveG` is asked of the state WITH the result (`withTempT`), as the step's `Rel` is
#guard !occursLive (outSt (CallGAttack.run true (callG "Kr" [.borrow (.var 0)])) stH 1000000)

-- at a data codomain no label survives the call; at a borrow codomain exactly the reserved one does
#guard occLabels (after true (callG "Inc" [.borrow (.var 0)])) == []
#guard occLabels (after true (callG "Kr" [.borrow (.var 0)])) == [stH.nextLoan + 1]
#guard occLabels (after false (callG "Kr" [.borrow (.var 0)])) == [stH.nextLoan + 1]
-- untyped as typed: the reserved label is the counter after the argument's borrow
#guard match (outVal (CallGAttack.run false (callG "Kr" [.borrow (.var 0)])) stH 1000000) with
  | (.borrow g _, _) => g == stH.nextLoan + 1 | _ => false

end Ochr.Meaning.Steps.Form.CallStepGuards
