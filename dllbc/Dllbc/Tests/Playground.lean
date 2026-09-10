
import Dllbc.ElabCheck
import Dllbc.Program
import Dllbc.Std
import Dllbc.ProgMacro

open Dllbc

def entrypoint : Checked := prog () {
  fn Reverse [src] (src: List Nat, dst: List Nat) -> List Nat {
    match src {
      Nil => dst,
      Cons(hd, tl) => Reverse(tl, Cons(hd, dst))
    }
  };

  fn F(x : List Nat) {
    let X0 = x;
    x := Nil;
    let X1 = x;
    ()
  };

  ()
}

-- Bind the result to a slot: `runProgramFrom` hands back the final Ω, so a bare
-- tail expression's value is computed and then discarded.
def res := runProgramFrom entrypoint prog_parse {
  let out = Reverse(Cons(0, Cons(1, Nil)), Nil);
  ()
}

#eval res
