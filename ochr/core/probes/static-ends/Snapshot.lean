import Ochr.Examples.Nat
open Ochr.Test

-- A stuck block reads a capture through a borrow before a later capture ends that borrow,
-- so its arm reads a snapshot; the direct run's arm reads the place after the match's entry
ochr Snap uses Nats {
  reject def EK (k : Nat) (a : Nat) : Unit := (
    let b = &a;
    let c = 5;
    b := &c;
    match k { Z => (c := 1; ()), S _ => (let z = clone(*b); ()) };
    ()
  )
}
ochr SnapRuns uses Nats, Snap {
  reject def EKRun : Unit := EK(1, 0)
  reject def EKRun0 : Unit := EK(0, 0)
}
