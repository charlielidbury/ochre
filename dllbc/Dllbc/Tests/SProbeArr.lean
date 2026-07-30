import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.StdLemmas
import Dllbc.Tests.S9Diff

/-! Scratch probes for the array partition lane. Not a deliverable. -/

open Dllbc
open Dllbc.StdLemmas (le_refl le_add le_add_l le_add_succ le_trans le_up_r le_pred_l
  leb_true_le leb_false_gt SortedA UbA LbA countA znots id_sym id_congr)

namespace Dllbc.Tests.SProbeArr

def fnEnv (d : Decl) (tbl : List Decl := [d]) : Option Env :=
  match runFn tbl d with | [.ok e] => some e | _ => none

def checkFnMsg (d : Decl) (tbl : List Decl := [d]) : String :=
  match checkFn tbl d with | .ok _ => "OK" | .error e => e

/-! ### T1 — does a two-segment owned node fold, and does `countA` then compute? -/

def node2 : Val :=
  Val.segsNode [Val.segNode (Val.nat 1) (.ctor "Arr" [.sym 7]), Val.segNode (.sym 3) (.sym 6)]
#eval (Val.arrFoldDeep node2).pretty
#eval (Val.nfV 2000 (Val.arrFoldDeep node2)).pretty

def touchA : Decl := decl{ fn touchA (q : Nat, s : &mut (Array q Nat)) -> Unit { () } }

/-! ### T2 — head carve (supplied residue) + tail consumed by a call -/

def peelCall : Decl := decl{
  fn peelCall (n : Nat, a : &mut (Array n Nat))
      -> Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a)) {
    match n {
      Z => λ (q : Nat). Refl,
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        let tl = &mut (*a)[S Z ; ..];
        touchA(m, tl);
        λ (q : Nat). Refl } } } }
#eval checkFnOk peelCall [peelCall, touchA]
#eval (checkFnMsg peelCall [peelCall, touchA]).take 400

/-! ### T3 — carve the head, read it, then WRITE it back (ends nothing, but tests
    whether a write through the element place leaves the node foldable). -/

def peelWrite : Decl := decl{
  fn peelWrite (n : Nat, a : &mut (Array n Nat))
      -> Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a)) {
    match n {
      Z => λ (q : Nat). Refl,
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        (*hd)[0] := x;
        λ (q : Nat). Refl } } } }
#eval checkFnOk peelWrite
#eval (checkFnMsg peelWrite).take 400

/-! ### T4 — the Z branch alone: is `countA q Z σ ≡ countA q Z σ` (Refl) fine? -/

def zOnly : Decl := decl{
  fn zOnly (n : Nat, a : &mut (Array n Nat))
      -> Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a)) {
    λ (q : Nat). Refl } }
#eval checkFnOk zOnly
#eval (checkFnMsg zOnly).take 300

/-! ### T5 — the carve alone, no reads: does `*a` fold with two live segment borrows? -/

def carveOnly : Decl := decl{
  fn carveOnly (n : Nat, m : Nat, a : &mut (Array n Nat))
      -> Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a)) {
    let hd = &mut (*a)[Z ; 1 ; m];
    let tl = &mut (*a)[S Z ; ..];
    λ (q : Nat). Refl } }
#eval checkFnOk carveOnly
#eval (checkFnMsg carveOnly).take 400

end Dllbc.Tests.SProbeArr
