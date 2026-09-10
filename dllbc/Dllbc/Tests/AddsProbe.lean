import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.FnMacro

/-! Probe (uncommitted): what the checker says about the three `add`s in
    adds.txt. Not part of the suite; not imported by the root. -/

open Dllbc
open Dllbc.StdLemmas (LeReflRaw Le)

namespace Dllbc.Tests.AddsProbe

def showRun (r : Except String Env) : String :=
  match r with
  | .ok env => String.intercalate ", " (env.map (fun kv => kv.1 ++ " ↦ " ++ kv.2.pretty))
  | .error e => "RUN ERR: " ++ e

def verdict (t : Term) : String :=
  match checkProgram t (ty{ Unit }) with
  | .ok _ => "CHECKS"
  | .error e => "REJECTED: " ++ e

/-! ## Add1 — functional, consume and rebuild -/

def add1 : Term := prog_parse {
  fn Add1 [x] (x : Nat, y : Nat) -> Nat {
    match x { Z => y, S(px) => S(Add1(px, y)) }
  };
  let r = Add1(2, 3);
  () }

#eval verdict add1
#eval showRun (runProgram add1)

/-! ## Add2 — imperative walk, graft at the Z leaf; naive (no fuel) -/

def add2naive : Term := prog_parse {
  fn Add2M (x : &mut Nat, y : Nat) -> Unit {
    match x {
      Z => { *x := y; () },
      S(px) => { Add2M(px, y); () }
    }
  };
  fn Add2 (x : Nat, y : Nat) -> Nat { Add2M(&m x, y); x };
  let r = Add2(2, 3);
  () }

#eval verdict add2naive

/-! ## Add2 — fuel-threaded (the zero_all shape) -/

def add2fuel : Term := prog_parse {
  fn Add2M [fuel] (fuel : Nat, x : &mut Nat, y : Nat, Hf : Le *x fuel) -> Unit {
    match x {
      Z => { *x := y; () },
      S(px) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => { Add2M(f2, px, y, Hf); () }
      }
    }
  };
  fn Add2 (x : Nat, y : Nat) -> Nat {
    let Hp = %LeReflRaw x;
    Add2M(x, &m x, y, Hp);
    x
  };
  let r = Add2(2, 3);
  () }

#eval verdict add2fuel
#eval showRun (runProgram add2fuel)

/-! ## Add3 — take, recurse by value, refill; naive as sketched -/

def add3naive : Term := prog_parse {
  fn Add3 [x] (x : Nat, y : Nat) -> Nat {
    match &m x {
      Z => y,
      S(px) => { *px := Add3(*px, y); x }
    }
  };
  let r = Add3(2, 3);
  () }

#eval verdict add3naive

/-! ## Add3 — fuel-threaded -/

def add3fuel : Term := prog_parse {
  fn Add3 [fuel] (fuel : Nat, x : Nat, y : Nat, Hf : Le x fuel) -> Nat {
    match &m x {
      Z => y,
      S(px) => match fuel {
        Z => botElim Nat Hf,
        S(f2) => { *px := Add3(f2, *px, y, Hf); x }
      }
    }
  };
  fn Add3C (x : Nat, y : Nat) -> Nat { Add3(x, x, y, %LeReflRaw x) };
  let r = Add3C(2, 3);
  () }

#eval verdict add3fuel
#eval showRun (runProgram add3fuel)

end Dllbc.Tests.AddsProbe
