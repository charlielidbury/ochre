import Ochr.Notation
import Ochr.Fuzz.Rand

/-!
# Fuzzer: generator types and the template library

Each generated program draws a random subset of these templates (closed under their
dependencies), plus a few random functions. The templates are the shapes that exposed
the known "two paths" bugs: in-place recursion (`AddM`), returned borrows (`TailM`,
`Pick`, `LastM`), writes through pattern variables (`Clr`, F5), a `Type`-valued family
and functions whose codomain is that family (`U`, `V`, `W`, `MkF`: F1, X1, BoomL), a
`Prop`-valued recursive predicate (`Le`), a proof-valued lemma (`Lemma`) and a
type-valued function with an effect (`F5`, P2).
-/

namespace Ochr.Fuzz
open Ochr.Surface

/-- The generator's types. `fam a` is the type `U(a)` (values of it are propositions,
so it is a type family returning sorts); `prop` is a term whose value is a proposition;
`proof` a proof of `⊤`. -/
inductive GTy where
  | nat | unit
  | ind (n : String)
  | ref (t : GTy)
  | prop | proof
  | fam (a : STerm)
  | fn (ps : List GTy) (r : GTy)
deriving Inhabited

partial def GTy.beq : GTy → GTy → Bool
  | .nat, .nat | .unit, .unit | .prop, .prop | .proof, .proof => true
  | .ind a, .ind b => a == b
  | .ref a, .ref b => a.beq b
  | .fam _, .fam _ => true
  | .fn ps r, .fn qs s => ps.length == qs.length && (ps.zip qs).all (fun (a, b) => a.beq b) && r.beq s
  | _, _ => false

instance : BEq GTy := ⟨GTy.beq⟩

/-- The surface type of a generator type. -/
partial def GTy.surface : GTy → STerm
  | .nat => .ident "Nat"
  | .unit => .ident "Unit"
  | .ind n => .ident n
  | .ref t => .amp t.surface
  | .prop => .sort 0
  | .proof => .top
  | .fam a => .call (.ident "U") [a]
  | .fn ps r => .pi ((ps.zipIdx).map fun (p, i) => (s!"z{i}", p.surface)) r.surface

/-- Data types (borrow-free, first-order): what can be matched, borrowed and observed. -/
def GTy.isData : GTy → Bool
  | .nat | .ind _ => true
  | _ => false

/-- A library function: its signature for the generator. `famArg i` in the result
means `U(argument i)`. -/
structure LibFn where
  name : String
  ps : List GTy
  ret : GTy
  famArg : Option Nat := none
  deps : List String := []

ochr FuzzLib {
  inductive B2 := F | T
  inductive L := Nil | Cons(h : Nat, t : L)
  inductive Box := Mk(v : Nat)
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x | S _ => y }
  def Double (n : Nat) : Nat by n := match n { Z => Z | S p => S (S (Double(p))) }
  def IsZ (n : Nat) : B2 := match n { Z => T | S _ => F }
  def G1 (x : &Nat) (n : Nat) : Unit := match n { Z => () | S _ => *x := 0 }
  def Clr (x : &Nat) : Unit := match *x { Z => () | S p => p := Z }
  def Inc (x : &Nat) : Unit := *x := S *x
  def U (n : Nat) : Type := match n { Z => Prop | S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }
  def W (x : &Nat) (n : Nat) : U(n) := *x := S Z; V(n)
  def MkF (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤ | S a' => match b { Z => Eq Nat Z (S Z) | S b' => Le(a', b') } }
  def Lemma (u : Unit) : ⊤ := refl
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  def LastM (xs : &L) : &L by xs := match *xs { Nil => xs | Cons(h, t) => LastM(&t) }
  def AppendM (xs : &L) (ys : L) : Unit by xs := match *xs { Nil => *xs := ys | Cons(h, t) => AppendM(&t, ys) }
  def Len (xs : L) : Nat by xs := match xs { Nil => Z | Cons(h, t) => S (Len(t)) }
}

def libFns : List LibFn :=
  [ { name := "AddM", ps := [.ref .nat, .nat], ret := .unit },
    { name := "Add", ps := [.nat, .nat], ret := .nat, deps := ["AddM"] },
    { name := "TailM", ps := [.ref .nat], ret := .ref .nat },
    { name := "Pick", ps := [.nat, .ref .nat, .ref .nat], ret := .ref .nat },
    { name := "Double", ps := [.nat], ret := .nat },
    { name := "IsZ", ps := [.nat], ret := .ind "B2", deps := ["B2"] },
    { name := "G1", ps := [.ref .nat, .nat], ret := .unit },
    { name := "Clr", ps := [.ref .nat], ret := .unit },
    { name := "Inc", ps := [.ref .nat], ret := .unit },
    { name := "V", ps := [.nat], ret := .fam (.num 0), famArg := some 0, deps := ["U"] },
    { name := "W", ps := [.ref .nat, .nat], ret := .fam (.num 0), famArg := some 1, deps := ["U", "V"] },
    { name := "MkF", ps := [.nat], ret := .fn [.ref .nat] (.fam (.num 0)), famArg := some 0, deps := ["U", "V"] },
    { name := "Le", ps := [.nat, .nat], ret := .prop },
    { name := "Lemma", ps := [.unit], ret := .proof },
    { name := "F5", ps := [.ref .nat], ret := .prop },
    { name := "LastM", ps := [.ref (.ind "L")], ret := .ref (.ind "L"), deps := ["L"] },
    { name := "AppendM", ps := [.ref (.ind "L"), .ind "L"], ret := .unit, deps := ["L"] },
    { name := "Len", ps := [.ind "L"], ret := .nat, deps := ["L"] } ]

/-- The declaration of a template by name. -/
def libDecl (n : String) : Option SDecl := FuzzLib.find? (·.name == n)

/-- Close a set of template names under dependencies, in library order. -/
partial def closeDeps (ns : List String) : List String :=
  let step (ns : List String) : List String :=
    ns ++ (ns.flatMap fun n => ((libFns.find? (·.name == n)).map (·.deps)).getD []).filter (!ns.contains ·)
  let ns' := (step ns).eraseDups
  if ns'.length == ns.length then (FuzzLib.map (·.name)).filter ns.contains else closeDeps ns'

end Ochr.Fuzz
