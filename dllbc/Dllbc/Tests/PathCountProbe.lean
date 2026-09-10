import Dllbc.ElabCheck
namespace Dllbc.Tests.PathCountProbe
open Dllbc

-- One symbolic two-branch match with a continuation: expect 2 paths.
def oneFork : Term := prog{
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    let c = b;
    () };
  () }

-- Two SEQUENTIAL symbolic matches: expect 4 paths (2 × 2).
def twoForks : Term := prog{
  fn P (n : Nat, m : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    let c = match m { Z => True, S(k) => False };
    let d = b;
    () };
  () }

-- Three: expect 8.
def threeForks : Term := prog{
  fn P (n : Nat, m : Nat, o : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    let c = match m { Z => True, S(k) => False };
    let d = match o { Z => True, S(k) => False };
    let e = b;
    () };
  () }

#eval match checkProgramHover oneFork none true with
  | .ok (_, pts) => s!"oneFork: {pts.length} path(s)"
  | .error e => s!"rejected: {e.msg}"

#eval match checkProgramHover twoForks none true with
  | .ok (_, pts) => s!"twoForks: {pts.length} path(s)"
  | .error e => s!"rejected: {e.msg}"

#eval match checkProgramHover threeForks none true with
  | .ok (_, pts) => s!"threeForks: {pts.length} path(s)"
  | .error e => s!"rejected: {e.msg}"

end Dllbc.Tests.PathCountProbe
