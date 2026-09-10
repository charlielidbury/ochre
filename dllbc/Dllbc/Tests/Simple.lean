import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.Tests.Diff
import Dllbc.Boundary
import Dllbc.Tests.Arrays
import Dllbc.Tests.Direct
import Dllbc.FnMacro

open Dllbc



def simple : Term := prog{
  fn Iden(x: Nat, y: Unit) -> Nat {
    x
  };
  Iden(5, 4);
  ()
}
