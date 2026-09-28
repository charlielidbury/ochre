import OchrMeta.Guard
import OchrMeta.Examples

/-! # Regression tests of the [Rec] guard check (meta-model-v1 §3.4 `guard_rejects`, C3)

Accepted: `AddM`, `TailM`, an in-place `AddMZero` (at `Unit`, and at a proposition, where the
machine erases the call and the guard is the only barrier), a value recursion `Dbl`, and a
two-step descent `Half`.  Rejected, each with its reason asserted: `Grow` (meta-model §3.3), e346's
`Loop` (write before the match), `f(n) := f(n)`, `f(n) := match n {Z ⇒ Z | S m ⇒ f(S m)}`, and
further cases.  `Apply(f, n)` and `let g = f; g(n)` (R2) are not expressible in FO: functions are
not values, so every occurrence of `f` is the head of a call. -/

namespace OchrMeta.Tests.GuardT
open OchrMeta OchrMeta.Ex OchrMeta.Guard

/-- `AddMZero(x : &Nat) : Unit by x := match *x { Z ⇒ () | S p ⇒ AddMZero(&p) }` -/
def addMZero : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.mtch (dr (V "x")) .unit "p" (cl "AddMZero" [bw (V "p")]))

/-- The same at a proposition (RULES' `AddMZero : Id Unit (AddM(x, 0)) ()`): the machine erases
every call to it, so only the guard stands between it and a circular proof. -/
def addMZeroP : FunDef where
  params := [("x", .ref .nat)]
  ret := .prop
  recPos := some 0
  body := some (.mtch (dr (V "x")) .unit "p" (cl "AddMZeroP" [bw (V "p")]))

/-- `Dbl(n : Nat) : Nat by n := match n { Z ⇒ Z | S m ⇒ S (S (Dbl(m))) }` (a value parameter) -/
def dbl : FunDef where
  params := [("n", .nat)]
  ret := .nat
  recPos := some 0
  body := some (.mtch (V "n") .zero "m" (.succ (.succ (cl "Dbl" [rd (V "m")]))))

/-- `Half(x : &Nat) : Unit by x := match *x { Z ⇒ () | S p ⇒ match p { Z ⇒ () | S q ⇒ Half(&q) } }` -/
def half : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.mtch (dr (V "x")) .unit "p"
    (.mtch (V "p") .unit "q" (cl "Half" [bw (V "q")])))

/-- The accepted program: E1/E2 plus the definitions above. -/
def PG : Prog := Ex.P ++
  [("AddMZero", addMZero), ("AddMZeroP", addMZeroP), ("Dbl", dbl), ("Half", half)]

/-! ## Rejected definitions -/

/-- meta-model §3.3 `Grow`, in FO (`()` for `refl`):
`Grow(b : Nat, x : &Nat) : Unit by x :=`
`  (match b { Z ⇒ () | S _ ⇒ () }); match *x { Z ⇒ () | S p ⇒ (p := S p; Grow(b, &p)) }`.
The write to the pattern variable after the match puts `S σ'`, the whole entry value, back into
`p`: a check that only asks "is the argument a pattern variable of a match on `*x`" accepts it. -/
def grow : FunDef where
  params := [("b", .nat), ("x", .ref .nat)]
  ret := .unit
  recPos := some 1
  body := some (.seq (.mtch (V "b") .unit "c" .unit)
    (.mtch (dr (V "x")) .unit "p"
      (.seq (.assign (V "p") (.succ (rd (V "p")))) (cl "Grow" [rd (V "b"), bw (V "p")]))))

/-- e346 F6 `Loop(x : &Nat) : Unit by x := *x := S *x; match *x { Z ⇒ () | S p ⇒ Loop(&p) }`:
a write before the match.  `p` is a pattern variable, but its content is the entry value. -/
def loop : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.seq (.assign (dr (V "x")) (.succ (rd (dr (V "x")))))
    (.mtch (dr (V "x")) .unit "p" (cl "Loop" [bw (V "p")])))

/-- `Self(n : Nat) : Nat by n := Self(n)` -/
def self' : FunDef where
  params := [("n", .nat)]
  ret := .nat
  recPos := some 0
  body := some (cl "Self" [rd (V "n")])

/-- `Re(n : Nat) : Nat by n := match n { Z ⇒ Z | S m ⇒ Re(S m) }`: the argument is equal to the
entry value `S σ'`, not a strict subterm. -/
def re : FunDef where
  params := [("n", .nat)]
  ret := .nat
  recPos := some 0
  body := some (.mtch (V "n") .zero "m" (cl "Re" [.succ (rd (V "m"))]))

/-- `Boom(n : Nat) : Prop by n := Boom(n)`: the machine erases every call to it, so it never
diverges; only the guard rejects it (R1/R2: once proofs are not run, the guard must be exact). -/
def boom : FunDef where
  params := [("n", .nat)]
  ret := .prop
  recPos := some 0
  body := some (cl "Boom" [rd (V "n")])

/-- `BoomE(n : Nat) : Unit by n := erase (BoomE(n))`: a recursive call inside an erased block. -/
def boomE : FunDef where
  params := [("n", .nat)]
  ret := .unit
  recPos := some 0
  body := some (.erase (cl "BoomE" [rd (V "n")]))

/-- `HalfTwice(x : &Nat) : Unit by x := match *x { Z ⇒ () | S p ⇒ match p { Z ⇒ () | S q ⇒
(HalfTwice(&q); HalfTwice(&p)) } }`: after the first call wrote `q`, the content of `p` is
`S ⌈…⌉`, which says nothing about the entry value. -/
def halfTwice : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.mtch (dr (V "x")) .unit "p"
    (.mtch (V "p") .unit "q" (.seq (cl "HalfTwice" [bw (V "q")]) (cl "HalfTwice" [bw (V "p")]))))

/-- `Swap(x : &Nat, y : &Nat) : Unit by x := match *x { Z ⇒ () | S p ⇒ Swap(y, &p) }`: the
decreasing position receives `y`, whose content is unrelated to `x`'s entry value. -/
def swap : FunDef where
  params := [("x", .ref .nat), ("y", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.mtch (dr (V "x")) .unit "p" (cl "Swap" [rd (V "y"), bw (V "p")]))

/-- A match on a sealed program (the result of an opaque call): generalise-then-split is out of
scope, so the check rejects with `stuck`.
`StuckM(x : &Nat) : Unit by x := let r = Opq(x); match *r { Z ⇒ () | S p ⇒ StuckM(&p) }` -/
def stuckM : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.letIn "r" (cl "Opq" [rd (V "x")]) (.mtch (dr (V "r")) .unit "p" (cl "StuckM" [bw (V "p")])))

/-- A borrow-checker error: `x` is moved, then matched. -/
def moveM : FunDef where
  params := [("x", .ref .nat)]
  ret := .unit
  recPos := some 0
  body := some (.letIn "a" (rd (V "x")) (.mtch (dr (V "x")) .unit "p" (cl "MoveM" [bw (V "p")])))

def PB : Prog := Ex.P ++
  [("Grow", grow), ("Loop", loop), ("Self", self'), ("Re", re), ("Boom", boom), ("BoomE", boomE),
   ("HalfTwice", halfTwice), ("Swap", swap), ("StuckM", stuckM), ("MoveM", moveM)]

/-! ## `guard_accepts` -/

def fuel : Nat := 200
def verdict (P : Prog) (f : String) : Verdict := checkDef P f fuel

#guard ["AddM", "TailM", "AddMZero", "AddMZeroP", "Dbl", "Half"].all fun f => verdict PG f == .accept
#guard wellGuardedB PG fuel
-- a non-recursive definition is not a subject of the check (its termination is the call order)
#guard verdict PG "Add" == .reject .badDef

/-! ## `guard_rejects`, each for its reason

Abstract ids: parameter `i` is `σᵢ = abs i`; [Split] numbers the fresh predecessors from the
number of parameters on. -/

-- Grow: in the `S` arm (`σ₁ := S σ₂`), `p := S p` makes `p`'s content `S σ₂`, the entry value itself
#guard verdict PB "Grow" == .reject (.recArg (.succ (.abs 2)) (.succ (.abs 2)))
-- Loop: after `*x := S *x`, the match takes its `S` arm without a split: `p`'s content is `σ₀`
#guard verdict PB "Loop" == .reject (.recArg (.abs 0) (.abs 0))
#guard verdict PB "Self" == .reject (.recArg (.abs 0) (.abs 0))
#guard verdict PB "Re" == .reject (.recArg (.succ (.abs 1)) (.succ (.abs 1)))
-- erased recursion is checked all the same
#guard verdict PB "Boom" == .reject (.recArg (.abs 0) (.abs 0))
#guard verdict PB "BoomE" == .reject (.recArg (.abs 0) (.abs 0))
-- after `HalfTwice(&q)` wrote `q`, `p`'s content is `S ⌈HalfTwice(σ₂); c₀⌉`
#guard verdict PB "HalfTwice" == .reject (.recArg
  (.succ (.sealed "HalfTwice" (Val.ofList [.abs 2]) (.fin 0) .unit)) (.succ (.succ (.abs 2))))
#guard verdict PB "Swap" == .reject (.recArg (.abs 1) (.succ (.abs 2)))
-- not [Rec] failures: a match on a sealed program (no generalise-then-split), and a borrow error
#guard verdict PB "StuckM" == .reject .stuck
#guard verdict PB "MoveM" == .reject .err
#guard !wellGuardedB PB fuel
-- the accepted definitions are still accepted inside `PB`
#guard ["AddM", "TailM"].all fun f => verdict PB f == .accept

/-! ## The call order -/

def callsF : FunDef := { params := [("n", .nat)], ret := .nat, body := some (cl "G2" [rd (V "n")]) }
def callsG : FunDef := { params := [("n", .nat)], ret := .nat, body := some (cl "F2" [rd (V "n")]) }
-- mutual recursion: `F2` calls the later `G2`
#guard !orderedAux [] [("F2", callsF), ("G2", callsG)]
-- a self-call in a definition not declared recursive
#guard !orderedAux [] [("Self", { self' with recPos := none })]
-- a duplicated name
#guard !orderedAux [] [("Dbl", dbl), ("Dbl", dbl)]
#guard orderedAux [] PG && orderedAux [] PB

/-! ## Concrete runs: the unguarded definitions diverge, the guarded ones terminate -/

/-- Run a term in program `P` from one frame of source bindings. -/
def goIn (P : Prog) (n : Nat) (bs : List (String × Val)) (t : Term) : Res :=
  run P n ⟨[bs.map fun (x, v) => (Var.nm x, v)], 0⟩ t

def natIn (r : Res) (x : String) : Option Nat := (get r x).bind Val.toNat?

-- `Loop(&a)` runs out of fuel from every input and at every fuel tried
#guard [100, 1000, 3000].all fun n => (List.range 6).all fun a =>
  goIn PB n [("a", nat a)] (cl "Loop" [bw (V "a")]) == .oof
-- `Grow(b, &a)` diverges as soon as `a ≠ 0` (and returns at once for `a = 0`)
#guard [100, 1000].all fun n => (List.range 3).all fun b => (List.range 6).all fun a =>
  (goIn PB n [("a", nat a)] (cl "Grow" [num b, bw (V "a")]) == .oof) == (a != 0)
#guard [100, 1000].all fun n => (List.range 6).all fun a =>
  goIn PB n [] (cl "Self" [num a]) == .oof && (goIn PB n [] (cl "Re" [num a]) == .oof) == (a != 0)
-- `Boom` never diverges: the machine erases it (so the machine alone cannot reject it)
#guard (List.range 6).all fun a =>
  goIn PB 100 [] (cl "Boom" [num a]) == .ok ⟨[[]], 0⟩ .star

-- the guarded definitions terminate on inputs 0..5, with the expected results
#guard (List.range 6).all fun a => (List.range 6).all fun y =>
  let r := goIn PG 1000 [("a", nat a)] (cl "AddM" [bw (V "a"), num y])
  r != .oof && natIn r "a" == some (a + y)
#guard (List.range 6).all fun a => (List.range 6).all fun w =>
  let r := goIn PG 1000 [("a", nat a)] (.letIn "r" (cl "TailM" [bw (V "a")]) (.assign (dr (V "r")) (num w)))
  r != .oof && natIn r "a" == some (a + w)
#guard (List.range 6).all fun a =>
  let r := goIn PG 1000 [("a", nat a)] (cl "AddMZero" [bw (V "a")])
  r != .oof && natIn r "a" == some a
#guard (List.range 6).all fun a =>
  ((value (goIn PG 1000 [] (cl "Dbl" [num a]))).bind Val.toNat?) == some (2 * a)
#guard (List.range 6).all fun a => goIn PG 1000 [("a", nat a)] (cl "Half" [bw (V "a")]) != .oof

/-! ## White-box: what the checker does -/

def branches (P : Prog) (f : String) : List (GSt × Val) :=
  match checkRun P f fuel with
  | some (.ok bs) => bs
  | _ => []

-- AddM: two branches; in the `S` arm the recursive call is closed off (`x ↦ S ⌈AddM(σ₂, σ₁); c₀⌉`),
-- not unfolded, and the entry value is refined to `S σ₂`
#guard (branches PG "AddM").map (fun (g, _) => (g.entry, g.st.env.head?.bind (·.lookup (.nm "x")))) ==
  [(.zero, some (.borrow 0 (.abs 1))),
   (.succ (.abs 2), some (.borrow 0 (.succ (.sealed "AddM" (Val.ofList [.abs 2, .abs 1]) (.fin 0) .unit))))]
-- Half: three branches, the entry refined twice in the recursive one
#guard (branches PG "Half").map (·.1.entry) == [.zero, .succ .zero, .succ (.succ (.abs 2))]

/-- `PairT(n : Nat) : Nat × Nat by n := (n, match n { Z ⇒ Z | S m ⇒ PairT(m); Z })`: the first
component is in flight while the match splits, and must be refined with it. -/
def pairT : FunDef where
  params := [("n", .nat)]
  ret := .pair .nat .nat
  recPos := some 0
  body := some (.pair (rd (V "n")) (.mtch (V "n") .zero "m" (.seq (cl "PairT" [rd (V "m")]) .zero)))

#guard verdict [("PairT", pairT)] "PairT" == .accept
#guard (branches [("PairT", pairT)] "PairT").map (·.2) ==
  [.pair .zero .zero, .pair (.succ (.abs 1)) .zero]

end OchrMeta.Tests.GuardT
