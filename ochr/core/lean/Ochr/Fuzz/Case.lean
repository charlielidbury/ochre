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
  conv : Option (STerm × STerm × STerm) := none   -- a function type and two functions: conversion oracle
deriving Inhabited

def Case.stmtDecl (c : Case) : SDecl :=
  { name := "Stmt", params := c.params, ret := .sort 0, body := .app "Id" [c.ty, c.lhs, c.rhs],
    expectAccept := true }

/-- `ConvF`, `ConvG` and the claim `ConvEq : Eq T ConvF ConvG := refl`, which the checker
accepts iff it finds the two functions convertible. -/
def convDecls : Option (STerm × STerm × STerm) → List SDecl
  | none => []
  | some (T, f, g) =>
    [{ name := "ConvF", ret := T, body := f, expectAccept := true },
     { name := "ConvG", ret := T, body := g, expectAccept := true },
     { name := "ConvEq", ret := .app "Eq" [T, .ident "ConvF", .ident "ConvG"], body := .ident "refl", expectAccept := true }]

/-- The case's own declarations (what a counterexample prints). -/
def Case.own (c : Case) : List SDecl :=
  c.lib.filterMap libDecl ++ c.extra ++ convDecls c.conv ++ [c.stmtDecl]

/-- The program checked: the library block `Prelude` (D52: `Pair`, `False`, `True`, `And`),
which every `ochr` block uses implicitly, then the case's own declarations. -/
def Case.decls (c : Case) : List SDecl := (Block.decls Prelude) ++ c.own

def Case.show (c : Case) (name : String := "Cex") : String := ppProgram name c.own

def indsOf (lib : List String) : List String := ["B2", "L", "Box", "Or", "ExN"].filter lib.contains ++ ["Pair"]

/-- Phase 1: the template subset. -/
def genTemplates : Gen (List String) := do
  let mut chosen := []
  for f in libFns do
    if ← chance 30 then chosen := chosen ++ [f.name]
  for (n, p) in [("L", 25), ("B2", 15), ("Box", 15), ("Or", 20), ("ExN", 20)] do
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
  -- v2.x: sometimes a proof parameter, which the body may take apart (D45)
  if ← chance 30 then
    let P ← weighted [(3, pure PT.top), (3, pure (PT.and .top .top)), (1, pure PT.fls),
      (if inds.contains "Or" then 2 else 0, pure PT.or), (if inds.contains "ExN" then 2 else 0, pure PT.ex)]
    ps := ps.push (s!"h{np}", .pf P)
  let natP := ps.toList.zipIdx.find? fun ((_, T), _) => T == .nat
  let refNat := ps.toList.zipIdx.find? fun ((_, T), _) => T == .ref .nat
  let fam := lib.any (·.name == "V") && natP.isSome
  let ret ← weighted [(3, pure GTy.unit), (3, pure GTy.nat), (if refNat.isSome then 1 else 0, pure (GTy.ref .nat)),
    (1, pure GTy.prop), (if fam then 2 else 0, pure (GTy.fam (.ident ((natP.map (·.1.1)).getD "n0"))))]
  let ret ← if ← chance 10 then pure GTy.proof else pure ret
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

/-- A hypothesis over the parameters so far: a proposition of known shape, or an opaque
statement about a data parameter (`Eq Nat n 0`, `Le(n, m)`, `PropIf(*x)`), which is `⊤` at
some instances and `False` at others. -/
def genHyp (lib : List LibFn) (inds : List String) (vars : List GVar) : Gen PT := do
  let nats := vars.filterMap fun v => match v.kind, v.ty with
    | .owned, .nat => some (STerm.ident v.name)
    | .bvar, .ref .nat => some (.deref (.ident v.name))
    | _, _ => none
  let has (n : String) : Bool := lib.any (·.name == n)
  let opq : Gen PT := do
    let a ← pick nats
    let k ← rand 2
    let b ← if nats.length > 1 && (← chance 40) then pick nats else pure (STerm.num k)
    let s ← weighted [(3, pure (STerm.app "Eq" [.ident "Nat", a, b])),
      (if has "Le" then 2 else 0, pure (.call (.ident "Le") [a, b])),
      (if has "PropIf" then 2 else 0, pure (.call (.ident "PropIf") [a]))]
    pure (PT.opq s (toString (repr s)))
  weighted [(2, pure PT.top), (2, pure (PT.and .top .top)), (1, pure PT.fls),
    (if inds.contains "Or" then 1 else 0, pure PT.or), (if inds.contains "ExN" then 1 else 0, pure PT.ex),
    (if nats.isEmpty then 0 else 4, opq), (if nats.isEmpty then 0 else 2, do pure (PT.and (← opq) .top))]

/-- Phase 2: the statement's parameters, observed type and two sides. -/
def genStmt (lib : List LibFn) (inds : List String) : Gen (List (String × STerm) × STerm × STerm × STerm) := do
  let np ← weighted [(3, pure 1), (4, pure 2), (2, pure 3)]
  let ind (n : String) : Nat := if inds.contains n then 1 else 0
  let mut vars : List GVar := []
  let mut ps : Array (String × STerm) := #[]
  -- abstract functions: the types of library functions, so that instances exist
  let simple (t : GTy) : Bool := match t with
    | .nat | .unit | .ind _ | .prop => true
    | .ref .nat | .ref (.ind _) => true
    | _ => false
  let fnTys := (lib.filter fun f => f.famArg.isNone && simple f.ret && f.ps.all simple).map fun f => GTy.fn f.ps f.ret
  for j in [0:np] do
    let T ← weighted [(4, pure GTy.nat), (4, pure (GTy.ref .nat)), (ind "B2", pure (GTy.ind "B2")),
      (ind "L", pure (GTy.ind "L")), (ind "L", pure (GTy.ref (.ind "L"))), (ind "Box", pure (GTy.ind "Box")),
      (2, pure (GTy.ind "Pair")), (2, pure (GTy.ref (.ind "Pair"))),
      (if fnTys.isEmpty then 0 else 2, pick fnTys)]
    let x := (match T with | .ref _ => "x" | .ind "L" => "l" | .ind "B2" => "b" | .ind "Pair" => "q" | .ind _ => "m" | .fn .. => "h" | _ => "n") ++ toString j
    ps := ps.push (x, T.surface)
    let kind := match T with
      | .ref _ => VKind.bvar
      | .fn .. => .fnv
      | _ => .owned
    vars := { name := x, ty := T, kind := kind, root := x, param := true } :: vars
  -- v2.x: proof parameters (bound to ⋆ at the generic call, never refined, D27), some of
  -- them statements about the earlier parameters, whose truth refinement decides
  let np' ← weighted [(5, pure 0), (3, pure 1), (1, pure 2)]
  for j in [0:np'] do
    let P ← genHyp lib inds vars
    let x := s!"h{np + j}"
    ps := ps.push (x, P.surface)
    vars := { name := x, ty := .pf P, kind := .owned, root := x, param := true } :: vars
  let Γ : Ctx := { vars := vars, lib := lib, inds := inds }
  let A ← weighted [(3, pure GTy.nat), (3, pure GTy.unit), (ind "B2", pure (GTy.ind "B2")),
    (ind "L", pure (GTy.ind "L")), (2, pure GTy.prop), (1, pure GTy.proof), (2, pure (GTy.ind "Pair"))]
  let d0 ← saveDead
  let lhs ← gen Γ A (3 + (← rand 7))
  setDead d0
  let rhs ← gen Γ A (← rand 3)
  pure (ps.toList, A.surface, lhs, rhs)

/-- A conversion pair: two functions of one type, the second often a small mutation of
the first (so that conversion has a chance to identify them). -/
def genConvPair (lib : List LibFn) (inds : List String) (mutate : STerm → List STerm) :
    Gen (Option (STerm × STerm × STerm)) := do
  let simple (t : GTy) : Bool := match t with
    | .nat | .unit | .ind _ | .ref .nat | .ref (.ind _) => true
    | _ => false
  let fixed : List (List GTy × GTy) := [([.ref .nat], .unit), ([.ref .nat], .nat),
    ([.ref .nat, .ref .nat], .ref .nat), ([.nat], .nat), ([.ref .nat, .nat], .unit)]
  let sigs := fixed ++ (lib.filter fun f => f.famArg.isNone && simple f.ret && f.ps.all simple).map fun f => (f.ps, f.ret)
  let (ps, r) ← pick sigs
  let named := (lib.filter fun f => f.famArg.isNone && GTy.fn f.ps f.ret == GTy.fn ps r).map fun f => STerm.ident f.name
  let Γ : Ctx := { lib := lib, inds := inds }
  let mkOne : Gen STerm := do
    weighted [(if named.isEmpty then 0 else 2, pick named), (3, genLambda Γ ps r (1 + (← rand 4)))]
  let f ← mkOne
  let g ← weighted [(3, mkOne), (3, do
      match f with
      | .fix x bs rt d b =>
        let ms := mutate b
        if ms.isEmpty then mkOne else pure (STerm.fix x bs rt d (← pick ms))
      | _ => mkOne)]
  pure (some ((GTy.fn ps r).surface, f, g))

end Ochr.Fuzz
