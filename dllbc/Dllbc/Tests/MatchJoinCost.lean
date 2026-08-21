import Dllbc.ElabCheck
import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program

/-! # MatchJoinCost — the 2^N claim, measured (docs/19 Stage 4)

    NOT in the build (`lake env lean Dllbc/Tests/MatchJoinCost.lean`). Path
    counts via `checkProgramHover` (the harness `PointCost` uses) and repeated
    `checkProgram` wall-time, fork vs join, N = 1..3 sequential two-branch
    matches on independent symbolic Nats. -/

namespace Dllbc.Tests.MatchJoinCost
open Dllbc

def fork1 : Term := prog{
  fn P (a : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let d = b1; () };
  () }
def fork2 : Term := prog{
  fn P (a : Nat, b : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let d = b1; () };
  () }
def fork3 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let b3 = match c { Z => True, S(k3) => False };
    let d = b1; () };
  () }

def join1 : Term := prog{
  fn P (a : Nat) -> Unit {
    let b1 : Bool = match a { Z => True, S(k1) => False };
    let d = b1; () };
  () }
def join2 : Term := prog{
  fn P (a : Nat, b : Nat) -> Unit {
    let b1 : Bool = match a { Z => True, S(k1) => False };
    let b2 : Bool = match b { Z => True, S(k2) => False };
    let d = b1; () };
  () }
def join3 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat) -> Unit {
    let b1 : Bool = match a { Z => True, S(k1) => False };
    let b2 : Bool = match b { Z => True, S(k2) => False };
    let b3 : Bool = match c { Z => True, S(k3) => False };
    let d = b1; () };
  () }

def fork6 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat, d : Nat, e : Nat, f : Nat) -> Unit {
    let b1 = match a { Z => True, S(k1) => False };
    let b2 = match b { Z => True, S(k2) => False };
    let b3 = match c { Z => True, S(k3) => False };
    let b4 = match d { Z => True, S(k4) => False };
    let b5 = match e { Z => True, S(k5) => False };
    let b6 = match f { Z => True, S(k6) => False };
    let g = b1; () };
  () }
def join6 : Term := prog{
  fn P (a : Nat, b : Nat, c : Nat, d : Nat, e : Nat, f : Nat) -> Unit {
    let b1 : Bool = match a { Z => True, S(k1) => False };
    let b2 : Bool = match b { Z => True, S(k2) => False };
    let b3 : Bool = match c { Z => True, S(k3) => False };
    let b4 : Bool = match d { Z => True, S(k4) => False };
    let b5 : Bool = match e { Z => True, S(k5) => False };
    let b6 : Bool = match f { Z => True, S(k6) => False };
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
  for (label, f, j) in [("N=1", fork1, join1), ("N=2", fork2, join2), ("N=3", fork3, join3), ("N=6", fork6, join6)] do
    IO.println s!"{label}  fork: {pathsOf f}   join: {pathsOf j}"
  for (label, f, j) in [("N=1", fork1, join1), ("N=2", fork2, join2), ("N=3", fork3, join3), ("N=6", fork6, join6)] do
    let tf ← timeN 200 f
    let tj ← timeN 200 j
    IO.println s!"{label}  checkProgram x200  fork: {tf}ms   join: {tj}ms"

end Dllbc.Tests.MatchJoinCost
