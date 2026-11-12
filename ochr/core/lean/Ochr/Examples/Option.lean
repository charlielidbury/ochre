import Ochr.Test
import Ochr.Runtime

/-! # Option: an optional value

`Opt(A) := None | Some(v : A)` (Rust's `Option`), with the propositions `IsSome(A, o)` and
`IsNone(A, o)`. Where nothing fixes `A`, a constructor takes it explicitly: `None[Nat]`. -/

open Ochr.Test

ochr Options {
  -- An optional value (Rust's `Option`), and whether one holds a value, as propositions.
  inductive Opt (A : Type) := None | Some(v : A)

  def IsSome (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  def IsNone (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => ⊤,
      Some(_) => False,
    }
  )
}

/-! ## Constructor values record their parameters (D88)

An untyped run (a called body, a sealed program's re-run, the runtime) infers a constructor's
parameters from its fields' types when they are not written, and the value records them:
`Some(n)` at `n : Nat` is `Some[Nat](n)`. Where the fields do not determine them (here `None`,
with no fields) the value records only what was written. -/

ochr OptionRuns uses Options {
  def WrapSome (n : Nat) : Opt(Nat) := Some(n)
  def BareNone (u : Unit) : Opt(Nat) := None
  def WrittenNone (u : Unit) : Opt(Nat) := None[Nat]
}

namespace Ochr.OptionRunsTest
open Ochr Ochr.Surface Ochr.Test

def sig : List GDef × List IndDecl :=
  let p := libOf {} 2000000 OptionRuns ++ OptionRuns.decls
  globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)

def params? : Outcome Value → Option (List Value)
  | .ok (.ind "Opt" _ _ ps _) _ => some ps
  | _ => none

-- the checker's untyped run and the runtime both build `Some[Nat](0)` ...
#guard params? (closedCall sig.1 sig.2 "WrapSome" [.zero] false) == some [.tNat]
#guard params? (closedCall sig.1 sig.2 "WrapSome" [.zero] true) == some [.tNat]
-- ... and a written parameter is recorded as before
#guard params? (closedCall sig.1 sig.2 "WrittenNone" [.unit] false) == some [.tNat]
-- twin: a bare `None` has no field to infer from, and records nothing (D88's residual)
#guard params? (closedCall sig.1 sig.2 "BareNone" [.unit] false) == some []

end Ochr.OptionRunsTest

