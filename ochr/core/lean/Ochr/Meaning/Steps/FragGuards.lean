import Ochr.Meaning.Steps.ColumnB

/-!
# Sanity runs of the fragment's assumed facts about the checker (lead10; compiled, not kernel-checked)

Each `Prop` of `Steps/FragMachine.lean` run at the entry conditions it must survive (several live
borrows, the holder bound before or after the lender, the holder a value in flight, the term in tail
position, a handed-down reading, an untyped run, a mode other than the fragment's).
-/

namespace Ochr.Meaning.Steps.Form

namespace FragGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open ColumnB (vals modeOf)

def bN (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some .tNat, val := v, decl := .other }
def bR (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some (.tRef .tNat), val := v, decl := .ref .other }

/-- One frame: `x ↦ loan_0`, `z ↦ loan_1`, `y ↦ borrow_0 S(Z)`, `w ↦ borrow_1 Z` (two live borrows). -/
def st2 : MState :=
  { env := #[{ binds := #[bN "x" (.loan 0), bN "z" (.loan 1), bR "y" (.borrow 0 (.succ .zero)),
      bR "w" (.borrow 1 .zero)] }], nextLoan := 2 }

-- `VarLentInv`: the read of `x` (variable 3) ends `0` only: `S(Z)` at `Nat`; `y ↦ ⊥`, `z`, `w` kept;
-- the standalone decision moves (`x ↦ ⊥`)
#guard outVal (Ochr.evalCore 100 true (.place (.var 3)) none) st2 1000 == (.succ .zero, some .tNat)
#guard vals (outSt (Ochr.evalCore 100 true (.place (.var 3)) none) st2 1000) ==
  [.bot, .loan 1, .bot, .borrow 1 .zero]
-- the read of `z` (variable 2) ends `1` only
#guard vals (outSt (Ochr.evalCore 100 true (.place (.var 2)) none) st2 1000) ==
  [.loan 0, .bot, .borrow 0 (.succ .zero), .bot]
-- in tail position, under a handed-down reading, untyped: the same value (untyped: no type)
#guard outVal (Ochr.evalCore 100 true (.place (.var 3)) none) { st2 with curTail := true } 1000 ==
  (.succ .zero, some .tNat)
#guard outVal (Ochr.eval 100 true (.place (.var 3)) none) { st2 with tailDecl := some .other } 1000 ==
  (.succ .zero, some .tNat)
#guard (outVal (Ochr.evalCore 100 false (.place (.var 3)) none) st2 1000).1 == .succ .zero
#guard (outVal (Ochr.evalCore 100 false (.place (.var 3)) none) st2 1000).2.all (· == .tNat)
-- the mode after is the mode before
#guard modeOf (outSt (Ochr.evalCore 100 true (.place (.var 3)) none) st2 1000) == (false, false, false, 0)
-- the holder bound BEFORE the lender: the same end
def st2r : MState :=
  { env := #[{ binds := #[bR "y" (.borrow 0 (.succ .zero)), bN "x" (.loan 0)] }], nextLoan := 1 }
#guard outVal (Ochr.evalCore 100 true (.place (.var 0)) none) st2r 1000 == (.succ .zero, some .tNat)
#guard vals (outSt (Ochr.evalCore 100 true (.place (.var 0)) none) st2r 1000) == [.bot, .bot]
-- the holder a value in flight (a temporary): the access is rejected (D106), so `VarLentInv` asks a binding
def stT : MState :=
  { env := #[{ binds := #[bN "x" (.loan 0)], temps := #[.borrow 0 (.succ .zero)], tempTys := #[some (.tRef .tNat)] }],
    nextLoan := 1 }
#guard !isOk (Ochr.evalCore 100 true (.place (.var 0)) none) stT 1000

-- `VarBotInv`: reading a moved variable fails, typed or not, in any mode
def stB0 : MState := { env := #[{ binds := #[bN "x" .bot] }] }
#guard !isOk (Ochr.evalCore 100 true (.place (.var 0)) none) stB0 1000
#guard !isOk (Ochr.evalCore 100 false (.place (.var 0)) none) stB0 1000
#guard !isOk (Ochr.evalCore 100 true (.place (.var 0)) none) { stB0 with copying := true } 1000

-- `EvalLow`: below fuel `3` every fragment form fails (and at `3` the leaves run)
def stX1 : MState := { env := #[{ binds := #[bN "x" (.succ .zero)] }] }
#guard [Term.zero, .succ .zero, .place (.var 0), .borrow (.var 0), .assign (.var 0) .zero,
    .letIn ⟨"y"⟩ .zero .zero, .seq .zero .zero].all fun t =>
  [0, 1, 2].all fun m => !isOk (Ochr.eval m true t none) stX1 1000
#guard isOk (Ochr.eval 3 true .zero none) stX1 1000

-- `DropBorrowInv`: the drop of `y ↦ borrow_0 S(Z)` gives `x` its content back and pops `y`; another
-- live borrow (`z`, `w`) is kept; the tail's value parked meanwhile (a number, another label's borrow)
def bindsD : Array Binding :=
  #[bN "x" (.loan 0), bN "z" (.loan 1), bR "w" (.borrow 1 .zero), bR "y" (.borrow 0 (.succ .zero))]
def frD (tmp : Value) (T : Value) : Frame := { binds := bindsD, temps := #[tmp], tempTys := #[some T] }
def stD (tmp : Value) (T : Value) : MState := { env := #[frD tmp T], nextLoan := 2 }
#guard vals (outSt (Ochr.dropTopBind 100) (stD (.borrow 1 .zero) (.tRef .tNat)) 1000) == [.succ .zero, .loan 1, .borrow 1 .zero]
#guard vals (outSt (Ochr.dropTopBind 100) (stD .zero .tNat) 1000) == [.succ .zero, .loan 1, .borrow 1 .zero]
#guard vals (outSt (Ochr.dropTopBind 100) { stD .zero .tNat with typing := true } 1000) ==
  [.succ .zero, .loan 1, .borrow 1 .zero]
-- `SeqBorInv`: `&x; x` from `x ↦ S(Z)`: the discard ends the borrow, `x` is read back
#guard outVal (Ochr.evalCore 100 true (.seq (.borrow (.var 0)) (.place (.var 0))) none) stX1 1000 == (.succ .zero, some .tNat)
#guard isOk (Ochr.evalCore 100 true (.seq (.borrow (.var 0)) (.place (.var 0))) none) { stX1 with curTail := true } 1000

/-! ## lead11: the `let` of the fragment -/

-- `DropLentFail`: the drop of a binding lent to the value in flight fails, alone or with another
-- borrow live (`z ↦ loan_1`, `w ↦ borrow_1 Z`), typed or under a private copy
def stL : MState :=
  { env := #[{ binds := #[bN "x" (.loan 0)], temps := #[.borrow 0 .zero], tempTys := #[some (.tRef .tNat)] }],
    nextLoan := 1 }
#guard !isOk (Ochr.dropTopBind 100) stL 1000
def frL2 : Frame :=
  { binds := #[bN "z" (.loan 1), bR "w" (.borrow 1 .zero), bN "x" (.loan 0)], temps := #[.borrow 0 .zero],
    tempTys := #[some (.tRef .tNat)] }
def stL2 : MState := { env := #[frL2], nextLoan := 2 }
#guard !isOk (Ochr.dropTopBind 100) stL2 1000
#guard !isOk (Ochr.dropTopBind 100) { stL2 with copying := true } 1000
-- so `let x = Z; &x` is rejected
def stA : MState := { env := #[{ binds := #[bN "a" (.succ .zero)] }] }
#guard !isOk (Ochr.eval 100 true (.letIn ⟨"x"⟩ .zero (.borrow (.var 0))) none) stA 1000
-- `FragRun`: `let y = &a; &a` (the second borrow ends the first; the drop of `y`, now `⊥`, ends
-- nothing): a borrow at `&Nat` in flight, `a ↦ loan_1`; at a hint, in tail position, the same
#guard outVal (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.borrow (.var 1))) none) stA 1000 ==
  (.borrow 1 (.succ .zero), some (.tRef .tNat))
#guard vals (outSt (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.borrow (.var 1))) none) stA 1000) == [.loan 1]
#guard outVal (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.borrow (.var 1))) (some (.tRef .tNat))) stA 1000 ==
  (.borrow 1 (.succ .zero), some (.tRef .tNat))
#guard outVal (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.borrow (.var 1))) none) { stA with tailNext := true } 1000 ==
  (.borrow 1 (.succ .zero), some (.tRef .tNat))
-- `FragRun` at a hint the term does not have: the checker's value and type are the term's
#guard outVal (Ochr.eval 100 true .zero (some .tUnit)) stA 1000 == (.zero, some .tNat)
-- `DropBorrowInv` through a whole `let`: `let y = &a; Z` gives `a` its content back
#guard vals (outSt (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) .zero) none) stA 1000) == [.succ .zero]
-- the mode after is the mode before
#guard modeOf (outSt (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) .zero) none) stA 1000) == (false, false, false, 0)

-- `BorrowLentInv`: `&x` of a lent `x` (variable 3 of `st2`, another borrow live): ends `0`, lends at `2`
#guard outVal (Ochr.evalCore 100 true (.borrow (.var 3)) none) st2 1000 == (.borrow 2 (.succ .zero), some (.tRef .tNat))
#guard vals (outSt (Ochr.evalCore 100 true (.borrow (.var 3)) none) st2 1000) == [.loan 2, .loan 1, .bot, .borrow 1 .zero]
#guard modeOf (outSt (Ochr.evalCore 100 true (.borrow (.var 3)) none) st2 1000) == (false, false, false, 0)
-- `BorrowBotInv`
#guard !isOk (Ochr.evalCore 100 true (.borrow (.var 0)) none) stB0 1000
-- `AssignVarInv`: lent (ends `0`, then overwrites), moved, a number read by `u`
#guard outVal (Ochr.evalCore 100 true (.assign (.var 3) .zero) none) st2 1000 == (.unit, some .tUnit)
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.var 3) .zero) none) st2 1000) == [.zero, .loan 1, .bot, .borrow 1 .zero]
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.var 0) .zero) none) stB0 1000) == [.zero]
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.var 0) (.succ (.place (.var 0)))) none) stX1 1000) == [.succ (.succ .zero)]
-- `AssignDerefInvF`: another borrow live: kept; `y ↦ ⊥`: the write fails
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.deref (.var 1)) .zero) none) st2 1000) ==
  [.loan 0, .loan 1, .borrow 0 .zero, .borrow 1 .zero]
def stYB : MState := { env := #[{ binds := #[bN "x" (.succ .zero), bR "y" .bot] }] }
#guard !isOk (Ochr.evalCore 100 true (.assign (.deref (.var 0)) .zero) none) stYB 1000
-- `*y := x` with `y = &x`: `u`'s read of `x` ends `y`'s borrow, then the write fails
#guard !isOk (Ochr.eval 100 true (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.assign (.deref (.var 0)) (.place (.var 1)))) none) stA 1000

end FragGuards

end Ochr.Meaning.Steps.Form
