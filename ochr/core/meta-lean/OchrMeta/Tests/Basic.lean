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

/-! ## `t5_nose_counterexample`: meta-model-v1 Theorem 5 "on the nose" is false

`r := Pick(n, &a, &b); z := b` with `n ↦ σ`: symbolically, `b`'s content is a sealed program
containing the hole `loan_k` of the returned borrow `r`, so reading `b` ends `r` ([Access]).
Concretely at `n = 0`, `r` borrows `a`, `b` contains no loan, and `r` stays live.  The refined,
normalised symbolic state has `r ↦ ⊥, a ↦ 1`; the concrete state has `r ↦ borrow_q 1, a ↦ loan_q`.
They are not equal up to renaming of loans; they agree after resolution (ending `r`). -/
namespace T5
def prog : Term :=
  .seq (.assign (V "r") (cl "Pick" [rd (V "n"), bw (V "a"), bw (V "b")])) (.assign (V "z") (rd (V "b")))
def init (n : Val) : List (String × Val) := [("n", n), ("a", nat 1), ("b", nat 2), ("r", .unit), ("z", .unit)]
def symb := go (init (.abs 0)) prog
def conc := go (init (nat 0)) prog
def refined : Option Env := match symb with
  | .ok s _ => some ((s.env.substAbs 0 (nat 0)).norm P fuel)
  | _ => none
-- the symbolic run ended `r`; the concrete run did not
#guard get symb "r" == some .moved
#guard get conc "r" == some (.borrow 0 (nat 1)) && get conc "a" == some (.loan 0)
#guard refined == some [[(.nm "n", nat 0), (.nm "a", nat 1), (.nm "b", nat 2), (.nm "r", .moved), (.nm "z", nat 2)]]
-- so the refined symbolic state is not the concrete one up to loan renaming ...
#guard match conc, refined with
  | .ok s _, some Ω => Env.canon s.env != Env.canon Ω
  | _, _ => false
-- ... but they agree after resolution (ending every borrow)
#guard match conc, refined with
  | .ok s _, some Ω => ((endAll s).map (·.env)) == some Ω
  | _, _ => false
end T5

/-! ## `canon_sched` (T1): every order of [End] steps gives the same final environment -/
namespace Sched
open OchrMeta.Ex

/-- all permutations of a small list (fuel = its length) -/
def permsN : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, l => if l = [] then [[]] else l.flatMap fun x => (permsN n (l.erase x)).map (x :: ·)
def perms (l : List Nat) : List (List Nat) := permsN l.length l

def heldNames (s : St) : List Nat := s.env.flatten.filterMap fun b =>
  match b.2 with | .borrow l _ => some l | _ => none

def endIn (s : St) : List Nat → Option St
  | [] => some s
  | l :: ls => (endBorrow l s).bind (endIn · ls)

def allSame (s : St) : Bool :=
  match (perms (heldNames s)).map (fun o => (endIn s o).map (·.env)) with
  | [] => true
  | x :: xs => xs.all (· == x) && x.isSome

-- three borrows: b = &a, r = &(*b).1, q = &(*r).1 (a chain), then stop with all alive
def chain : Res :=
  go [("a", nat 3), ("b", .unit), ("r", .unit), ("q", .unit)]
    (.seq (.assign (V "b") (bw (V "a"))) (.seq (.assign (V "r") (bw (.fst (dr (V "b")))))
      (.assign (V "q") (bw (.fst (dr (V "r")))))))
#guard match chain with | .ok s _ => (heldNames s).length == 3 && allSame s | _ => false
-- Pick's result with a symbolic scrutinee, plus a second borrow alive
def pick2 : Res :=
  go [("n", .abs 0), ("a", nat 1), ("b", nat 2), ("c", nat 5), ("r", .unit), ("k", .unit)]
    (.seq (.assign (V "r") (cl "Pick" [rd (V "n"), bw (V "a"), bw (V "b")])) (.assign (V "k") (bw (V "c"))))
#guard match pick2 with | .ok s _ => (heldNames s).length == 2 && allSame s | _ => false
end Sched

/-! ## `back_inj_small` (Lemma 4) and `ctx_needs_all_owners` (C2), on the sealed programs -/
namespace Inj
def back (f : String) (as : List Val) (is : List Nat) (w : Nat) : List Val :=
  is.map fun i => nrm (sl f as (.back i) (nat w))
def injOn (g : Nat → List Val) (n : Nat) : Bool :=
  (List.range n).all fun a => (List.range n).all fun b => a == b || g a != g b
-- TailM's backward function (one borrowed place) is injective
#guard (List.range 4).all fun a => injOn (back "TailM" [nat a] [0]) 7
-- Pick's, jointly over both borrowed places, in both branches
#guard injOn (back "Pick" [nat 0, nat 3, nat 5] [1, 2]) 7
#guard injOn (back "Pick" [nat 1, nat 3, nat 5] [1, 2]) 7
-- observing only the owner `a` (place 1) is not injective in the `S` branch: C2
#guard !injOn (back "Pick" [nat 1, nat 3, nat 5] [1]) 7
end Inj

end OchrMeta.Tests
