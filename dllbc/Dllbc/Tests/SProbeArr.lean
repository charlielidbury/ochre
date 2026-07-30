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

def checkFnMsg (d : Decl) (tbl : List Decl := [d]) : String :=
  match checkFn tbl d with | .ok _ => "OK" | .error e => e

def touchA : Decl := decl{ fn touchA (q : Nat, s : &mut (Array q Nat)) -> Unit { () } }

/-! ### U1 — peel + tail + a call taking a REBORROW of the tail -/

def u1 : Decl := decl{
  fn u1 (n : Nat, a : &mut (Array n Nat)) -> Unit {
    match n {
      Z => (),
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        let tl = &mut (*a)[S Z ; ..];
        touchA(m, &mut *tl);
        () } } } }
#eval (checkFnMsg u1 [u1, touchA]).take 300

/-! ### U2 — U1 + the three carves inside the tail -/

def u2 : Decl := decl{
  fn u2 (n : Nat, k3 : Nat, r2 : Nat, a : &mut (Array n Nat)) -> Unit {
    match n {
      Z => (),
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        let tl = &mut (*a)[S Z ; ..];
        touchA(m, &mut *tl);
        let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)];
        let mid = &mut (*tl)[k3 ; 1 ; r2];
        let hi = &mut (*tl)[S k3 ; ..];
        () } } } }
#eval (checkFnMsg u2 [u2, touchA]).take 300

/-! ### U3 — U2 without the call (are the nested carves the problem, or the call?) -/

def u3 : Decl := decl{
  fn u3 (n : Nat, k3 : Nat, r2 : Nat, a : &mut (Array n Nat)) -> Unit {
    match n {
      Z => (),
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        let tl = &mut (*a)[S Z ; ..];
        let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)];
        let mid = &mut (*tl)[k3 ; 1 ; r2];
        let hi = &mut (*tl)[S k3 ; ..];
        () } } } }
#eval (checkFnMsg u3).take 300

/-! ### U4 — U3 + the swap writes -/

def u4 : Decl := decl{
  fn u4 (n : Nat, k3 : Nat, r2 : Nat, a : &mut (Array n Nat)) -> Unit {
    match n {
      Z => (),
      S(m) => {
        let hd = &mut (*a)[Z ; 1 ; m];
        let x = (*hd)[0];
        let tl = &mut (*a)[S Z ; ..];
        let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)];
        let mid = &mut (*tl)[k3 ; 1 ; r2];
        let hi = &mut (*tl)[S k3 ; ..];
        let y = (*mid)[0];
        (*mid)[0] := x;
        (*hd)[0] := y;
        () } } } }
#eval (checkFnMsg u4).take 300

/-! ### U5 — the recursive shape, with a SELF call, no nested carve -/

def u5 : Decl := decl{
  fn u5 [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, a : &mut (Array m Nat)) -> Unit {
    match m {
      Z => (),
      S(m2) => match fuel {
        Z => botElim Unit hfuel,
        S(f2) => {
          let hd = &mut (*a)[Z ; 1 ; m2];
          let x = (*hd)[0];
          let tl = &mut (*a)[S Z ; ..];
          u5(f2, m2, hfuel, &mut *tl);
          () } } } } }
#eval (checkFnMsg u5).take 300

end Dllbc.Tests.SProbeArr
