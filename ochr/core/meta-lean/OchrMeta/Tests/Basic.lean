import OchrMeta.Examples

/-! # Regression and property tests of meta-model-v1 §3.4(A), on the interpreter

Each `#guard` is checked at build time.  Negative tests assert the *reason* where the
interpreter can expose it (an `err` from a specific step, a non-injective map). -/

namespace OchrMeta.Tests
open OchrMeta OchrMeta.Ex

def natOf (r : Res) (x : String) : Option Nat := (get r x).bind Val.toNat?
def fuel : Nat := 2000
def nrm (v : Val) : Val := norm P fuel v
def sl (f : String) (as : List Val) (k : SealK) (w : Val := .unit) : Val := .sealed f (Val.ofList as) k w

/-! ## `e1e2_runs`: concrete runs of E1/E2 on inputs 0..5 -/

#guard (List.range 6).all fun a => (List.range 6).all fun y =>
  natOf (go [("a", nat a)] (cl "AddM" [bw (V "a"), num y])) "a" == some (a + y)
#guard (List.range 6).all fun a => (List.range 6).all fun y =>
  ((value (go [] (cl "Add" [num a, num y]))).bind Val.toNat?) == some (a + y)
#guard (List.range 6).all fun a => (List.range 6).all fun w =>
  natOf (go [("a", nat a)] (.letIn "r" (cl "TailM" [bw (V "a")]) (.assign (dr (V "r")) (num w)))) "a"
    == some (a + w)
#guard (List.range 6).all fun a => (List.range 6).all fun y =>
  natOf (go [("a", nat a)] (cl "AddM'" [bw (V "a"), num y])) "a" == some (a + y)

/-! ## `close_eqs`: each [Close] fill normalises to the concrete run's final content -/

-- AddM: ⌈let c = a; AddM(&c, y); c⌉ ↦ a + y, the concrete final content of the borrowed place
#guard (List.range 5).all fun a => (List.range 5).all fun y =>
  nrm (sl "AddM" [nat a, nat y] (.fin 0)) == nat (a + y) &&
  natOf (go [("x", nat a)] (cl "AddM" [bw (V "x"), num y])) "x" == some (a + y)
-- TailM: current content of the returned borrow is 0; the hole fill with w is a + w
#guard (List.range 5).all fun a =>
  nrm (sl "TailM" [nat a] .cur) == nat 0 &&
  (List.range 5).all fun w => nrm (sl "TailM" [nat a] (.back 0) (nat w)) == nat (a + w)
-- Pick: the returned borrow is x or y; the fill of the other place ignores w
#guard (List.range 3).all fun n => (List.range 3).all fun a => (List.range 3).all fun b =>
  nrm (sl "Pick" [nat n, nat a, nat b] .cur) == nat (if n = 0 then a else b) &&
  (List.range 5).all fun w =>
    nrm (sl "Pick" [nat n, nat a, nat b] (.back 1) (nat w)) == nat (if n = 0 then w else a) &&
    nrm (sl "Pick" [nat n, nat a, nat b] (.back 2) (nat w)) == nat (if n = 0 then b else w)

/-! ## symbolic runs produce the expected sealed programs -/

-- `AddM(&a, 0)` with `a ↦ σ`: `a ↦ ⌈let c = σ; AddM(&c, 0); c⌉`, result `()`
#guard go [("a", .abs 0)] (cl "AddM" [bw (V "a"), num 0]) ==
  .ok ⟨[[("a", sl "AddM" [.abs 0, nat 0] (.fin 0))]], 1⟩ .unit
-- `let r = TailM(&a); *r := 5` with `a ↦ σ`: the hole is filled with 5 when `r` dies
#guard get (go [("a", .abs 0)] (.letIn "r" (cl "TailM" [bw (V "a")]) (.assign (dr (V "r")) (num 5)))) "a"
  == some (sl "TailM" [.abs 0] (.back 0) (nat 5))

/-! ## `owners_pick` (C2, D18): the hole of a returned borrow has two owners -/

def pickEnv : Res :=
  go [("n", .abs 0), ("a", .abs 1), ("b", .abs 2)]
    (.letIn "r" (cl "Pick" [rd (V "n"), bw (V "a"), bw (V "b")]) (.read (V "n")))

-- stop just after the call: keep `r` alive by running the call in the outer frame
def pickSt : Res :=
  go [("n", .abs 0), ("a", .abs 1), ("b", .abs 2), ("r", .unit)]
    (.assign (V "r") (cl "Pick" [rd (V "n"), bw (V "a"), bw (V "b")]))

#guard match pickSt with
  | .ok s _ => match s.lookup (.nm "r") with
    | some (.borrow k _) => owners s.env k == [.nm "a", .nm "b"]
    | _ => false
  | _ => false

/-! ## `access_inner` (C5, breaker-close A1): moving `b` ends the reborrow `r` inside it -/

def accessInner (withMove : Bool) : Res :=
  go [] (.letIn "a" (num 1) (.letIn "b" (bw (V "a")) (.letIn "r" (bw (.fst (dr (V "b"))))
    (.seq (if withMove then cl "G" [rd (V "b"), num 0] else .unit) (.assign (dr (V "r")) (num 0))))))

#guard accessInner true == .err
#guard accessInner false != .err

/-! ## `erase_natural` (R1): a Prop-typed block that writes leaves `a` unchanged -/

def eraseBlock : Term :=
  .erase (.mtch (V "b") (.assign (V "a") (num 1)) "m" (.assign (V "a") (num 1)))

#guard get (go [("a", nat 0), ("b", .abs 0)] eraseBlock) "a" == some (nat 0)
#guard get (go [("a", nat 0), ("b", nat 0)] eraseBlock) "a" == some (nat 0)
#guard get (go [("a", .abs 1), ("b", .abs 0)] eraseBlock) "a" == some (.abs 1)

end OchrMeta.Tests
