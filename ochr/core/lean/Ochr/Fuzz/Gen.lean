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

/-- The places that can be matched on for a result of type `T`: data places, and (v2.x)
proofs, by their type (D45). A proof of `Or` or `ExN` is not a subsingleton, so it is
matched only into proofs; an opaque statement only rarely (`match h {}`, which checks only
where the statement computes to `False`: a fail-safe path, D49 (1)). -/
def matchPlaces (Γ : Ctx) (T : GTy) : Gen (List GVar) := do
  let mut out := []
  for D in [GTy.nat, .ind "B2", .ind "L", .ind "Box", .ind "Pair"] do
    out := out ++ (← placesOf Γ D)
  for (v, P) in ← proofVars Γ do
    if P.large || T.isProof then
      match P with
      | .opq .. => if ← chance 10 then out := out ++ [v]
      | _ => out := out ++ [v, v]
  pure out

def hasPlace (Γ : Ctx) (T : GTy) : Gen Bool := do pure !(← placesOf Γ T).isEmpty

/-- Can a term of type `T` be generated here? -/
def canGen (Γ : Ctx) (T : GTy) : Gen Bool := do
  match T with
  | .ref t => hasPlace Γ t
  | .ind n => pure (Γ.inds.contains n)
  | .fam _ => pure (Γ.lib.any (·.name == "V"))
  | .fn ps _ => pure (ps.all fun p => match p with | .ref _ => true | _ => true)
  | .pf P => canPf Γ P
  | _ => pure true
where
  /-- A proof of `P` can be built from constructors, or (`False`, opaque) read from a variable. -/
  canPf (Γ : Ctx) : PT → Gen Bool
    | .top => pure true
    | .or => pure (Γ.inds.contains "Or")
    | .ex => pure (Γ.inds.contains "ExN")
    | .and a b => do pure ((← canPf Γ a) && (← canPf Γ b))
    | P => do pure ((← proofVars Γ).any (·.2 == P))

/-- A nat term that can index the family `U`, for a λ codomain or `V(…)`: an owned Nat
variable (a captured value inside a λ) or a literal. -/
def famArg (Γ : Ctx) : Gen STerm := do
  let ns := Γ.vars.filter fun v => v.kind == .owned && v.ty == .nat
  if ns.isEmpty || (← chance 15) then return natLit (← rand 2)
  pure (.ident (← pick ns).name)

/-- The variables a λ body may see: owned values (captured by copy; proofs among them keep
their declared types, D51), pattern variables of owned places, and function values; never
a borrow. -/
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

/-- (D54/D55) The function values that take one `&Nat`, with their result types: function
parameters and library functions (not the identity wrappers). -/
def fnHeads (Γ : Ctx) : Gen (List (STerm × GTy)) := do
  let mut out := []
  for v in Γ.vars do
    if v.kind == .fnv && !(← isDead v.name) then
      if let .fn [.ref .nat] r := v.ty then out := out ++ [(STerm.ident v.name, r), (.ident v.name, r)]
  for f in Γ.lib do
    if f.ps == [.ref .nat] && !f.wrapper && f.famArg.isNone then out := out ++ [(.ident f.name, f.ret)]
  pure out

/-- The surface types that evaluate to a given result type: `Prop`/`P0`, `Unit`/`UU(Z)`,
`⊤`/`V(Z)` (the latter of each when the library declares it). -/
def variantsOf (Γ : Ctx) (r : GTy) : List STerm :=
  let has (n : String) := Γ.lib.any (·.name == n)
  match r.evalKey with
  | .prop => [.sort 0] ++ (if has "H" then [.ident "P0"] else [])
  | .unit => [.ident "Unit"] ++ (if has "HU" then [.call (.ident "UU") [.num 0]] else [])
  | .pf .top => [.top] ++ (if has "WV" then [.call (.ident "V") [.num 0]] else [])
  | t => [t.surface]

def saveDead : Gen (List String) := do pure (← get).dead
def setDead (d : List String) : Gen Unit := modify fun s => { s with dead := d }

end Ochr.Fuzz
