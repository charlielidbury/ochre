import OchrMeta.Interp

/-! # The example programs of RULES §7, in the FO fragment -/

namespace OchrMeta.Ex

open OchrMeta

def V (x : String) : Place := .var (.nm x)
def rd (p : Place) : Term := .read p
def bw (p : Place) : Term := .borrow p
def dr (p : Place) : Place := .deref p
def cl (f : String) (args : List Term) : Term := .call f args
def num : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (num n)
def nat (n : Nat) : Val := Val.ofNat n

/-- `AddM(x : &Nat, y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }` -/
def addM : FunDef where
  params := [("x", .ref .nat), ("y", .nat)]
  ret := .unit
  recPos := some 0
  body := some (.mtch (dr (V "x")) (.assign (dr (V "x")) (rd (V "y"))) "p"
    (cl "AddM" [bw (V "p"), rd (V "y")]))

/-- `Add(x : Nat, y : Nat) : Nat := AddM(&x, y); x` -/
def add : FunDef where
  params := [("x", .nat), ("y", .nat)]
  ret := .nat
  body := some (.seq (cl "AddM" [bw (V "x"), rd (V "y")]) (rd (V "x")))

/-- `TailM(x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }` -/
def tailM : FunDef where
  params := [("x", .ref .nat)]
  ret := .ref .nat
  recPos := some 0
  body := some (.mtch (dr (V "x")) (rd (V "x")) "p" (cl "TailM" [bw (V "p")]))

/-- `AddM'(x : &Nat, y : Nat) : Unit := let t = TailM(x); *t := y` -/
def addM' : FunDef where
  params := [("x", .ref .nat), ("y", .nat)]
  ret := .unit
  body := some (.letIn "t" (cl "TailM" [rd (V "x")]) (.assign (dr (V "t")) (rd (V "y"))))

/-- `Pick(n : Nat, x : &Nat, y : &Nat) : &Nat := match n { Z => x | S _ => y }` -/
def pick : FunDef where
  params := [("n", .nat), ("x", .ref .nat), ("y", .ref .nat)]
  ret := .ref .nat
  body := some (.mtch (V "n") (rd (V "x")) "m" (rd (V "y")))

/-- A function that only consumes its arguments. -/
def gee : FunDef where
  params := [("x", .ref .nat), ("n", .nat)]
  ret := .unit
  body := some .unit

/-- An opaque function returning a borrow into its argument (an abstract `σ_f`). -/
def opq : FunDef where
  params := [("x", .ref .nat)]
  ret := .ref .nat
  body := none

def P : Prog :=
  [("AddM", addM), ("Add", add), ("TailM", tailM), ("AddM'", addM'), ("Pick", pick),
   ("G", gee), ("Opq", opq)]

/-- Run a term from a single frame of source bindings. -/
def go (bs : List (String × Val)) (t : Term) (next : Nat := 0) : Res :=
  run P 10000 ⟨[bs.map fun (x, v) => (Var.nm x, v)], next⟩ t

/-- The content of source variable `x` in a result. -/
def get (r : Res) (x : String) : Option Val :=
  match r with
  | .ok s _ => s.lookup (.nm x)
  | _ => none

def value (r : Res) : Option Val :=
  match r with
  | .ok _ v => some v
  | _ => none

end OchrMeta.Ex
