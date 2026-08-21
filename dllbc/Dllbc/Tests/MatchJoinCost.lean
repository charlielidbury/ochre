import Dllbc.ElabCheck
import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program

/-! # MatchJoinCost — the 2^N claim, measured (docs/19 v2 Stage R4)

    NOT in the build (`lake env lean Dllbc/Tests/MatchJoinCost.lean`). The SAME
    annotation-free programs the fork was measured on (v1 AS BUILT: 3/5/9/65
    paths, 27/64/138/1205 ms ×200 at N = 1/2/3/6) — under the unconditional
    join. Paths via `checkProgramHover`, wall-time via repeated `checkProgram`. -/

namespace Dllbc.Tests.MatchJoinCost
open Dllbc

def chain1 : Term := prog{
  fn P (a : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let d = b1; () };
  () }
def chain2 : Term := prog{
  fn P (a : Nat, b : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let d = b1; () };
  () }
def chain3 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let b3 = match c { Z => True, S(k3) => False };
    let d = b1; () };
  () }
def chain6 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat, d : Nat, e : Nat, f : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let b3 = match c { Z => True, S(k3) => False };
    let b4 = match d { Z => True, S(k4) => False };
    let b5 = match e { Z => True, S(k5) => False };
    let b6 = match f { Z => True, S(k6) => False };
    let g = b1; () };
  () }

def pathsOf (t : Term) : String :=
  match checkProgramHover t none true with
  | .ok (_, pts) => s!"{pts.length} path(s)"
  | .error _ => "rejected"

def timeN (n : Nat) (t : Term) : IO Nat := do
  let t0 ← IO.monoMsNow
  let mut ok := 0
  for _ in [0:n] do
    if progOk t then ok := ok + 1
  let t1 ← IO.monoMsNow
  if ok != n then IO.println s!"  (WARN: {n - ok} rejected)"
  pure (t1 - t0)

#eval show IO Unit from do
  IO.println "join (v2) — fork baseline from v1 AS BUILT in brackets"
  for (label, t, fp, fm) in [("N=1", chain1, 3, 27), ("N=2", chain2, 5, 64),
                             ("N=3", chain3, 9, 138), ("N=6", chain6, 65, 1205)] do
    let tm ← timeN 200 t
    IO.println s!"{label}  {pathsOf t} [fork {fp}]   x200 {tm}ms [fork {fm}ms]"

end Dllbc.Tests.MatchJoinCost
