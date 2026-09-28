import Ochr.Fuzz.Ctx

/-!
# Fuzzer: the type-directed term generator

`gen Γ T f` produces a surface term of generator type `T` in context `Γ` with size
budget `f`. Besides the evident forms it has weighted productions for the shapes behind
the known two-path bugs: effects before a `Type`-family call (F1), λs whose codomain is
that family (X1, BoomL), a `let x : Prop` bound to a match whose arms write (BoomB),
writes through pattern variables (F5), a returned borrow live across a match of its
source (F2), proofs whose arms write (N1), matches whose arms move different borrows
(C5), borrows of sub-places passed to calls (D19), `Id` formed after a returned borrow
has holes in several owners (D18), and matches on call results inside types (X3).
-/

namespace Ochr.Fuzz
open Ochr.Surface

structure Callee where
  head : STerm
  ps : List GTy
  ret : GTy
  famArg : Option Nat := none
deriving Inhabited

def calleesOf (Γ : Ctx) : Gen (List Callee) := do
  let lib := Γ.lib.map fun f => ({ head := .ident f.name, ps := f.ps, ret := f.ret, famArg := f.famArg } : Callee)
  let mut fns := []
  for v in Γ.vars do
    if v.kind == .fnv && !(← isDead v.name) then
      if let .fn ps r := v.ty then fns := fns ++ [({ head := .ident v.name, ps := ps, ret := r } : Callee)]
  pure (lib ++ fns)

/-- The data places that can be matched on. -/
def matchPlaces (Γ : Ctx) : Gen (List GVar) := do
  let mut out := []
  for T in [GTy.nat, .ind "B2", .ind "L", .ind "Box"] do
    out := out ++ (← placesOf Γ T)
  pure out

def hasPlace (Γ : Ctx) (T : GTy) : Gen Bool := do pure !(← placesOf Γ T).isEmpty

/-- Can a term of type `T` be generated here? -/
def canGen (Γ : Ctx) (T : GTy) : Gen Bool := do
  match T with
  | .ref t => hasPlace Γ t
  | .ind n => pure (Γ.inds.contains n)
  | .fam _ => pure (Γ.lib.any (·.name == "V"))
  | .fn ps _ => pure (ps.all fun p => match p with | .ref _ => true | _ => true)
  | _ => pure true

/-- A nat term that can index the family `U`, for a λ codomain or `V(…)`: an owned Nat
variable (a captured value inside a λ) or a literal. -/
def famArg (Γ : Ctx) : Gen STerm := do
  let ns := Γ.vars.filter fun v => v.kind == .owned && v.ty == .nat
  if ns.isEmpty || (← chance 15) then return natLit (← rand 2)
  pure (.ident (← pick ns).name)

/-- The variables a λ body may see: owned values (captured by copy), pattern variables
of owned places, and function values; never a borrow. -/
def lamCtx (Γ : Ctx) : Ctx :=
  let isOwnedRoot (r : String) : Bool := Γ.vars.any fun v => v.name == r && v.kind == .owned
  { Γ with inLam := true, vars := Γ.vars.filter fun v =>
      v.kind == .owned || v.kind == .fnv || (v.kind == .alias && isOwnedRoot v.root) }

/-- The root that a `let`-bound borrow depends on (accessing it ends the borrow). -/
partial def borrowRoot (Γ : Ctx) (x : String) : STerm → String
  | .amp (.ident c) => c
  | .amp (.deref (.ident y)) => y
  | .amp (.proj _ p) => borrowRoot Γ x (.amp p)
  | .ident y => ((Γ.vars.find? (·.name == y)).map (·.root)).getD x
  | .call _ (a :: as) => match a with
    | .amp _ => borrowRoot Γ x a
    | _ => borrowRoot Γ x (.call (.ident "_") as)
  | _ => x

def saveDead : Gen (List String) := do pure (← get).dead
def setDead (d : List String) : Gen Unit := modify fun s => { s with dead := d }

end Ochr.Fuzz
