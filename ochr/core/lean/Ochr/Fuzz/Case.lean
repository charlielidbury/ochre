import Ochr.Fuzz.GenTerm
import Ochr.Fuzz.Print

/-!
# Fuzzer: a test case

A case is a small program (template library, random functions) and a statement
`Id A lhs rhs` over parameters. The oracles evaluate the statement's two sides and the
`Id` type at the generic call (every parameter abstract, as [Def] does) and at
refinements and instances, and compare.
-/

namespace Ochr.Fuzz
open Ochr.Surface

structure Case where
  lib : List String := []          -- template names, closed under dependencies
  extra : List SDecl := []         -- random functions
  params : List (String × STerm) := []
  ty : STerm := .ident "Nat"
  lhs : STerm := .num 0
  rhs : STerm := .num 0
deriving Inhabited

def Case.stmtDecl (c : Case) : SDecl :=
  { name := "Stmt", params := c.params, ret := .sort 0, body := .app "Id" [c.ty, c.lhs, c.rhs],
    expectAccept := true }

def Case.decls (c : Case) : List SDecl :=
  c.lib.filterMap libDecl ++ c.extra ++ [c.stmtDecl]

def Case.show (c : Case) (name : String := "Cex") : String := ppProgram name c.decls

def indsOf (lib : List String) : List String := ["B2", "L", "Box"].filter lib.contains

/-- Phase 1: the template subset. -/
def genTemplates : Gen (List String) := do
  let mut chosen := []
  for f in libFns do
    if ← chance 30 then chosen := chosen ++ [f.name]
  for (n, p) in [("L", 25), ("B2", 15), ("Box", 15)] do
    if ← chance p then chosen := chosen ++ [n]
  pure (closeDeps chosen)

/-- A random function over 1–2 parameters; with a borrowed Nat parameter, sometimes
recursive on it (`match *x { Z => … | S p => … R(&p, …) … }`). -/
def genFn (name : String) (lib : List LibFn) (inds : List String) : Gen (SDecl × LibFn) := do
  let np ← weighted [(3, pure 1), (2, pure 2)]
  let hasL := inds.contains "L"
  let mut ps : Array (String × GTy) := #[]
  for j in [0:np] do
    let T ← weighted [(4, pure (GTy.ref .nat)), (4, pure GTy.nat),
      (if hasL then 1 else 0, pure (GTy.ref (.ind "L"))), (if hasL then 1 else 0, pure (GTy.ind "L"))]
    ps := ps.push ((match T with | .ref _ => "x" | _ => "n") ++ toString j, T)
  let natP := ps.toList.zipIdx.find? fun ((_, T), _) => T == .nat
  let refNat := ps.toList.zipIdx.find? fun ((_, T), _) => T == .ref .nat
  let fam := lib.any (·.name == "V") && natP.isSome
  let ret ← weighted [(3, pure GTy.unit), (3, pure GTy.nat), (if refNat.isSome then 1 else 0, pure (GTy.ref .nat)),
    (1, pure GTy.prop), (if fam then 2 else 0, pure (GTy.fam (.ident ((natP.map (·.1.1)).getD "n0"))))]
  let Γ : Ctx := { lib := lib, inds := inds, vars := ps.toList.map fun (x, T) => match T with
    | .ref _ => { name := x, ty := T, kind := .bvar, root := x, param := true }
    | _ => { name := x, ty := T, kind := .owned, root := x, param := true } }
  let recur := refNat.isSome && !(ret matches .fam _) && (← chance 35)
  let body ← if recur then do
      let ((x, _), xi) := refNat.get!
      let z ← gen Γ ret (2 + (← rand 2))
      let p ← freshName "p"
      let Γs := Γ.push { name := p, ty := .nat, kind := .alias, root := x }
      let mut args : Array STerm := #[]
      for ((y, T), j) in ps.toList.zipIdx do
        if j == xi then args := args.push (.amp (.ident p))
        else match T with
          | .ref t => args := args.push (((← borrowOf? Γs t [x]).map (·.1)).getD (.amp (.deref (.ident y))))
          | T => args := args.push (← leaf Γs T)
      let rc := STerm.call (.ident name) args.toList
      let s ← match ret with
        | .unit => do pure (.seq (← gen Γs .unit 1) rc)
        | .nat => do pure (← pick [rc, .app "S" [rc]])
        | _ => pure rc
      pure (STerm.matchGen (.deref (.ident x)) [("Z", [], z), ("S", [p], s)])
    else gen Γ ret (3 + (← rand 3))
  let famArg := match ret, natP with
    | .fam _, some (_, i) => some i
    | _, _ => none
  let d : SDecl := { name := name, params := ps.toList.map fun (x, T) => (x, T.surface), ret := ret.surface,
                     body := body, dec := if recur then some (refNat.get!.1.1) else none, expectAccept := true }
  pure (d, { name := name, ps := ps.toList.map (·.2), ret := ret, famArg := famArg })

/-- Phase 2: the statement's parameters, observed type and two sides. -/
def genStmt (lib : List LibFn) (inds : List String) : Gen (List (String × STerm) × STerm × STerm × STerm) := do
  let np ← weighted [(3, pure 1), (4, pure 2), (2, pure 3)]
  let ind (n : String) : Nat := if inds.contains n then 1 else 0
  let mut vars : List GVar := []
  let mut ps : Array (String × STerm) := #[]
  for j in [0:np] do
    let T ← weighted [(4, pure GTy.nat), (4, pure (GTy.ref .nat)), (ind "B2", pure (GTy.ind "B2")),
      (ind "L", pure (GTy.ind "L")), (ind "L", pure (GTy.ref (.ind "L"))), (ind "Box", pure (GTy.ind "Box"))]
    let x := (match T with | .ref _ => "x" | .ind "L" => "l" | .ind "B2" => "b" | .ind _ => "m" | _ => "n") ++ toString j
    ps := ps.push (x, T.surface)
    vars := { name := x, ty := T, kind := (if T matches .ref _ then .bvar else .owned), root := x, param := true } :: vars
  let Γ : Ctx := { vars := vars, lib := lib, inds := inds }
  let A ← weighted [(3, pure GTy.nat), (3, pure GTy.unit), (ind "B2", pure (GTy.ind "B2")),
    (ind "L", pure (GTy.ind "L")), (2, pure GTy.prop)]
  let d0 ← saveDead
  let lhs ← gen Γ A (3 + (← rand 7))
  setDead d0
  let rhs ← gen Γ A (← rand 3)
  pure (ps.toList, A.surface, lhs, rhs)

end Ochr.Fuzz
