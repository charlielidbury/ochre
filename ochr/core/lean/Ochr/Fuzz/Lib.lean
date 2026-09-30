import Ochr.Prelude
import Ochr.Fuzz.Rand

/-!
# Fuzzer: generator types and the template library

Each generated program draws a random subset of these templates (closed under their
dependencies), plus a few random functions. The templates are the shapes that exposed
the known "two paths" bugs: in-place recursion (`AddM`), returned borrows (`TailM`,
`Pick`, `LastM`), writes through pattern variables (`Clr`, F5), a `Type`-valued family
and functions whose codomain is that family (`U`, `V`, `W`, `MkF`: F1, X1, BoomL), a
`Prop`-valued recursive predicate (`Le`), a proof-valued lemma (`Lemma`) and a
type-valued function with an effect (`F5`, P2). v2.x adds the Prop inductives (the
library's `False`, `True`, `And`, and the user-declared `Or` and `ExN`), functions taking
proofs and matching on them (`AndSwap`, `Absurd`, `WriteIf`, `OrProof`, `ExProof`,
`EffL`), and closures capturing values (`Clo`, `CapP`).
-/

namespace Ochr.Fuzz
open Ochr.Surface

/-- The propositions whose shape the generator knows (v2.x): `⊤`, `False`, `P ∧ Q`, the
user Prop inductives `Or(⊤, ⊤)` (two constructors: matched only into proofs) and `ExN`
(one constructor with a data field: not a subsingleton either), and opaque statements
about data (`Eq Nat a b`, `Le(a, b)`), which are passed around but not taken apart.
`key` identifies an opaque statement (for equality). -/
inductive PT where
  | top | fls
  | and (a b : PT)
  | or | ex
  | opq (s : STerm) (key : String)
deriving Inhabited

partial def PT.beq : PT → PT → Bool
  | .top, .top | .fls, .fls | .or, .or | .ex, .ex => true
  | .and a b, .and c d => a.beq c && b.beq d
  | .opq _ k, .opq _ k' => k == k'
  | _, _ => false

instance : BEq PT := ⟨PT.beq⟩

partial def PT.surface : PT → STerm
  | .top => .top
  | .fls => .ident "False"
  | .and a b => .and a.surface b.surface
  | .or => .call (.ident "Or") [.top, .top]
  | .ex => .ident "ExN"
  | .opq s _ => s

/-- The generator's types. `fam a` is the type `U(a)` (values of it are propositions,
so it is a type family returning sorts); `prop` is a term whose value is a proposition;
`pf P` a proof of `P`. -/
inductive GTy where
  | nat | unit
  | ind (n : String)
  | ref (t : GTy)
  | prop
  | pf (P : PT)
  | fam (a : STerm)
  | fn (ps : List GTy) (r : GTy)
  | alias (s : STerm) (key : String) (as : GTy)  -- a type written `s` that evaluates to `as` (D54/D55:
                                                 -- `P0` for `Prop`, `UU(Z)` for `Unit`, `V(Z)` for `⊤`)
deriving Inhabited

/-- A proof of `⊤` (the v1 generator's only proof type). -/
abbrev GTy.proof : GTy := .pf .top

partial def GTy.beq : GTy → GTy → Bool
  | .nat, .nat | .unit, .unit | .prop, .prop => true
  | .pf P, .pf Q => P == Q
  | .ind a, .ind b => a == b
  | .ref a, .ref b => a.beq b
  | .fam _, .fam _ => true
  | .fn ps r, .fn qs s => ps.length == qs.length && (ps.zip qs).all (fun (a, b) => a.beq b) && r.beq s
  | .alias _ k _, .alias _ k' _ => k == k'
  | _, _ => false

instance : BEq GTy := ⟨GTy.beq⟩

/-- A type up to evaluation: an alias is the type it evaluates to (D54/D55: `P0` and `Prop`,
`UU(Z)` and `Unit`, `V(Z)` and `⊤` denote the same thing but may differ in class). -/
partial def GTy.evalKey : GTy → GTy
  | .alias _ _ a => a.evalKey
  | .fn ps r => .fn (ps.map GTy.evalKey) r.evalKey
  | .ref t => .ref t.evalKey
  | t => t

/-- The surface type of a generator type. -/
partial def GTy.surface : GTy → STerm
  | .nat => .ident "Nat"
  | .unit => .ident "Unit"
  | .ind "Pair" => .prod (.ident "Nat") (.ident "Nat")   -- D52: the generator's pairs are Nat × Nat
  | .ind n => .ident n
  | .ref t => .amp t.surface
  | .prop => .sort 0
  | .pf P => P.surface
  | .fam a => .call (.ident "U") [a]
  | .fn ps r => .pi ((ps.zipIdx).map fun (p, i) => (s!"z{i}", p.surface)) r.surface
  | .alias s _ _ => s

/-- Data types (borrow-free, first-order): what can be matched, borrowed and observed. -/
def GTy.isData : GTy → Bool
  | .nat | .ind _ => true
  | _ => false

def GTy.isProof : GTy → Bool
  | .pf _ => true
  | _ => false

/-- A library function: its signature for the generator. `famArg i` in the result
means `U(argument i)`. -/
structure LibFn where
  name : String
  ps : List GTy
  ret : GTy
  famArg : Option Nat := none
  deps : List String := []
  attack : Bool := false   -- offered to the generator even when the default rules reject it
                           -- (a reviewer's attack shape, live only with a rule switched off)
  wrapper : Bool := false  -- an identity on functions (`IdFP(f)(&c)`: D54's wrapper variant)
deriving Inhabited

ochr FuzzLib {
  inductive B2 := F | T
  inductive L := Nil | Cons(h : Nat, t : L)
  inductive Box := MkB(v : Nat)
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(l : P) | Inr(r : Q)
  inductive ExN : Prop := Wit(n : Nat, e : ⊤)
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S _ => y }
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  def Keep (x : &Nat) : Unit := ()
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  def IsZ (n : Nat) : B2 := match n { Z => T, S _ => F }
  def G1 (x : &Nat) (n : Nat) : Unit := match n { Z => (), S _ => *x := 0 }
  def Clr (x : &Nat) : Unit := match *x { Z => (), S p => p := Z }
  def Inc (x : &Nat) : Unit := *x := S *x
  def U (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }
  def W (x : &Nat) (n : Nat) : U(n) := *x := S Z; V(n)
  def MkF (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S a' => match b { Z => False, S b' => Le(a', b') } }
  def Lemma (u : Unit) : ⊤ := refl
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  def LastM (xs : &L) : &L by xs := match *xs { Nil => xs, Cons(h, t) => LastM(&t) }
  def AppendM (xs : &L) (ys : L) : Unit by xs := match *xs { Nil => *xs := ys, Cons(h, t) => AppendM(&t, ys) }
  def Len (xs : L) : Nat by xs := match xs { Nil => Z, Cons(h, t) => S (Len(t)) }
  def AndSwap (h : ⊤ ∧ ⊤) : ⊤ ∧ ⊤ := match h { Intro(a, b) => ⟨b, a⟩ }
  def Absurd (h : False) : Nat := match h {}
  def WriteIf (x : &Nat) (h : ⊤ ∧ ⊤) : Unit := match h { Intro(a, b) => *x := 1 }
  def OrProof (h : Or(⊤, ⊤)) : ⊤ := match h { Inl(p) => p, Inr(q) => q }
  def ExProof (h : ExN) : ⊤ := match h { Wit(n, e) => match n { Z => refl, S m => e } }
  def EffL (x : &Nat) (h : Or(⊤, ⊤)) : ⊤ := match h { Inl(p) => (*x := 1; refl), Inr(q) => (*x := 2; refl) }
  def Clo (n : Nat) (y : Nat) : Nat := let f = (λ(z : Nat) : Nat => Add(n, z)); f(y)
  def CapN (x : &Nat) : Nat := let n = *x; let f = (λ(z : Nat) : Nat => n); AddM(&*x, 1); f(0)
  def PropIf (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
  def P0 : Type := Prop
  def H (x : &Nat) : P0 := (*x := S Z; ⊤)
  def HP (x : &Nat) : Prop := (*x := S Z; ⊤)
  def UU (n : Nat) : Type := match n { Z => Unit, S _ => Unit }
  def HU (x : &Nat) : UU(Z) := *x := S Z
  def HW (x : &Nat) : Unit := *x := S Z
  def HTop (x : &Nat) : ⊤ := refl
  def HTopW (x : &Nat) : ⊤ := (*x := S Z; refl)
  def IdFP (f : Π(x : &Nat). Prop) : (Π(x : &Nat). Prop) := f
  def IdFT (f : Π(x : &Nat). ⊤) : (Π(x : &Nat). ⊤) := f
  def IdFU (f : Π(x : &Nat). Unit) : (Π(x : &Nat). Unit) := f
  def RunG (f : Π(x : &Nat). Prop) : Nat := (let c = Z; let g = f; g(&c); c)
  def RunK (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
  def WV (u : Unit) : V(Z) := refl
  def FV (x : &Nat) : V(Z) := (*x := S Z; WV(()))
  def GV (x : &Nat) : V(Z) := WV(())
  def TT : Prop := (Π(x : &Nat). V(Z))
  -- reviewer-6's A1/L1 family: a type family whose arms are different data types, and
  -- type-level observers of a place of the second (their `Id` compares at the place's type)
  inductive Bx (A : Type) := MkBx(v : A)
  def TF (n : Nat) : Type := match n { Z => Bx(Unit), S _ => Bx(B2) }
  def TG (n : Nat) : Type := match n { Z => Nat, S _ => B2 }
  def CmpBx (b : Bx(B2)) : Prop := (let c = b; Id Unit (c := MkBx[B2](T)) (c := MkBx[B2](F)))
  def CmpB2 (b : B2) : Prop := (let c = b; Id Unit (c := T) (c := F))
  -- instances of the families' dependent function parameters (`h : Π(n : Nat). TG(n)`)
  def HG (n : Nat) : TG(n) := match n { Z => 0, S _ => F }
  def HF (n : Nat) : TF(n) := match n { Z => MkBx[Unit](()), S _ => MkBx[B2](T) }
}

/-- The codomain types written differently from what they evaluate to (D54, D55). -/
def tyP0 : GTy := .alias (.ident "P0") "P0" .prop
def tyUUZ : GTy := .alias (.call (.ident "UU") [.num 0]) "UU(Z)" .unit
def tyVZ : GTy := .alias (.call (.ident "V") [.num 0]) "V(Z)" .proof

def libFns : List LibFn :=
  [ { name := "AddM", ps := [.ref .nat, .nat], ret := .unit },
    { name := "Add", ps := [.nat, .nat], ret := .nat, deps := ["AddM"] },
    { name := "TailM", ps := [.ref .nat], ret := .ref .nat },
    { name := "Pick", ps := [.nat, .ref .nat, .ref .nat], ret := .ref .nat },
    { name := "PickX", ps := [.ref .nat, .ref .nat], ret := .ref .nat },
    { name := "PickY", ps := [.ref .nat, .ref .nat], ret := .ref .nat },
    { name := "Keep", ps := [.ref .nat], ret := .unit },
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
    { name := "Len", ps := [.ind "L"], ret := .nat, deps := ["L"] },
    { name := "AndSwap", ps := [.pf (.and .top .top)], ret := .pf (.and .top .top) },
    { name := "Absurd", ps := [.pf .fls], ret := .nat },
    { name := "WriteIf", ps := [.ref .nat, .pf (.and .top .top)], ret := .unit },
    { name := "OrProof", ps := [.pf .or], ret := .proof, deps := ["Or"] },
    { name := "ExProof", ps := [.pf .ex], ret := .proof, deps := ["ExN"] },
    { name := "EffL", ps := [.ref .nat, .pf .or], ret := .fam (.num 0), deps := ["Or", "U", "V"] },
    { name := "Clo", ps := [.nat, .nat], ret := .nat, deps := ["Add"] },
    { name := "CapN", ps := [.ref .nat], ret := .nat, deps := ["AddM"] },
    { name := "PropIf", ps := [.nat], ret := .prop },
    -- D54 (reviewer-5): writing functions whose codomain terms differ from their values' class
    { name := "H", ps := [.ref .nat], ret := tyP0, deps := ["P0"] },
    { name := "HP", ps := [.ref .nat], ret := .prop },
    { name := "HU", ps := [.ref .nat], ret := tyUUZ, deps := ["UU"] },
    { name := "HW", ps := [.ref .nat], ret := .unit },
    { name := "HTop", ps := [.ref .nat], ret := .proof },
    { name := "HTopW", ps := [.ref .nat], ret := .proof },
    { name := "IdFP", ps := [.fn [.ref .nat] .prop], ret := .fn [.ref .nat] .prop, wrapper := true },
    { name := "IdFT", ps := [.fn [.ref .nat] .proof], ret := .fn [.ref .nat] .proof, wrapper := true },
    { name := "IdFU", ps := [.fn [.ref .nat] .unit], ret := .fn [.ref .nat] .unit, wrapper := true },
    { name := "RunG", ps := [.fn [.ref .nat] .prop], ret := .nat },
    { name := "RunK", ps := [.fn [.ref .nat] .proof, .ref .nat], ret := .unit },
    -- D55 (reviewer-4): a type-level family whose value is a proposition but whose declared
    -- sort is not Prop; rejected by the default rules (D55), live with `sortsSyntactic` off
    { name := "WV", ps := [.unit], ret := tyVZ, deps := ["U", "V"], attack := true },
    { name := "FV", ps := [.ref .nat], ret := tyVZ, deps := ["WV"], attack := true },
    { name := "GV", ps := [.ref .nat], ret := tyVZ, deps := ["WV"], attack := true },
    { name := "TT", ps := [], ret := .prop, deps := ["U", "V"], attack := true } ]

/-- The declaration of a template by name. -/
def libDecl (n : String) : Option SDecl := (Block.decls FuzzLib).find? (·.name == n)

/-- Close a set of template names under dependencies, in library order. -/
partial def closeDeps (ns : List String) : List String :=
  let step (ns : List String) : List String :=
    ns ++ (ns.flatMap fun n => ((libFns.find? (·.name == n)).map (·.deps)).getD []).filter (!ns.contains ·)
  let ns' := (step ns).eraseDups
  if ns'.length == ns.length then ((Block.decls FuzzLib).map (·.name)).filter ns.contains else closeDeps ns'

end Ochr.Fuzz
