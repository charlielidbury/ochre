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

/-! ## Constructor values record their parameters (D88, D89)

An untyped run (a called body, a sealed program's re-run, the runtime) builds a constructor
value with its parameters, as typing does: inferred from its fields' types when they are not
written (D88, `Some(n)` at `n : Nat` is `Some[Nat](n)`), and where the fields do not determine
them (no fields, a phantom parameter, only proof fields, or fields whose types a type function
computes) from the type its context declares (D89): a body's declared codomain at its tail, a
`let` annotation, a call's parameter type, the field's type in an enclosing constructor. -/

ochr OptionRuns uses Options {
  def WrapSome (n : Nat) : Opt(Nat) := Some(n)
  def BareNone (u : Unit) : Opt(Nat) := None
  def WrittenNone (u : Unit) : Opt(Nat) := None[Nat]
  def KeepO (o : Opt(Nat)) : Opt(Nat) := o
  def PassNone (u : Unit) : Opt(Nat) := KeepO(None)
  def SomeNone (u : Unit) : Opt(Opt(Nat)) := Some(None)
  def LetNone (u : Unit) : Opt(Nat) := (let x : Opt(Nat) = None; x)
  def CloNone (u : Unit) : Opt(Nat) := (let f = (λ(v : Unit) : Opt(Nat) => None); f(()))
  def ArmNone (k : Nat) : Opt(Nat) := match k { Z => None, S _ => None }
  -- a phantom parameter, a parameter only a proof field has, and one only a type function reads
  inductive TagO (A : Type) := MkTagO(n : Nat)
  def MkTO (n : Nat) : TagO(Nat) := MkTagO(n)
  inductive SigO (P : Prop) := MkSigO(n : Nat, h : P)
  def MkSO (n : Nat) (h : Eq(Nat, n, n)) : SigO(Eq(Nat, n, n)) := MkSigO(clone(n), h)
  def GO (n : Nat) : Type := match n { Z => Nat, S _ => Nat }
  inductive DPO (n : Nat) := MkDPO(y : GO(n), z : Nat)
  def MkDO (n : Nat) (y : GO(n)) : DPO(n) := MkDPO(y, 0)
}

namespace Ochr.OptionRunsTest
open Ochr Ochr.Surface Ochr.Test

def sig : List GDef × List IndDecl :=
  let p := libOf {} 2000000 OptionRuns ++ OptionRuns.decls
  globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)

def params? : Outcome Value → Option (List Value)
  | .ok (.ind _ _ _ ps _) _ => some ps
  | _ => none

def untyped (g : String) (args : List Value) : Outcome Value := closedCall sig.1 sig.2 g args false

-- D88: the checker's untyped run and the runtime both build `Some[Nat](0)` ...
#guard params? (untyped "WrapSome" [.zero]) == some [.tNat]
#guard params? (closedCall sig.1 sig.2 "WrapSome" [.zero] true) == some [.tNat]
-- ... and a written parameter is recorded as before
#guard params? (untyped "WrittenNone" [.unit]) == some [.tNat]
-- D89: a bare `None` (no field to infer from) takes the context's type: a body's codomain
-- (D88 alone recorded nothing here), a call's parameter, a `let` annotation, a closure's
-- codomain, an arm of a match in tail position, and an enclosing constructor's field
#guard params? (untyped "BareNone" [.unit]) == some [.tNat]
#guard params? (closedCall sig.1 sig.2 "BareNone" [.unit] true) == some [.tNat]
#guard params? (untyped "PassNone" [.unit]) == some [.tNat]
#guard params? (untyped "LetNone" [.unit]) == some [.tNat]
#guard params? (untyped "CloNone" [.unit]) == some [.tNat]
#guard params? (untyped "ArmNone" [.succ .zero]) == some [.tNat]
#guard match untyped "SomeNone" [.unit] with
  | .ok (.ind _ _ _ [.tInd "Opt" [.tNat]] [.ind _ _ _ [.tNat] []]) _ => true
  | _ => false
-- a phantom parameter, a proof field's (`Eq(Nat, 0, 0)` computes to `⊤`), a type function's
#guard params? (untyped "MkTO" [.zero]) == some [.tNat]
#guard (params? (untyped "MkSO" [.zero, .proof])).map (·.length) == some 1
#guard params? (untyped "MkDO" [.zero, .zero]) == some [.zero]

end Ochr.OptionRunsTest

