import Ochr.Fuzz.Shrink

/-!
# Fuzzer: making case `i` of a run

Phase 1 draws the templates and random functions; the library is then checked (always
under the default rules, so a seed gives the same case whatever rule switch is being
tested); phase 2 draws the statement over the accepted functions only.
-/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

/-- The names of the library declarations the checker accepts, in order. -/
def acceptedNames (cfg : Config) (fuel : Nat) (decls : List SDecl) : List String := Id.run do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  let mut ok : List String := []
  for d in decls do
    match resolveProgram decls d with
    | .error _ => pure ()
    | .ok it =>
      match runSt (checkItem it) { globals := globals, inds := inds, cfg := cfg, fuel := fuel } with
      | .ok ((), st') => globals := st'.globals; inds := st'.inds; ok := ok ++ [d.name]
      | .error _ => pure ()
  pure ok

def genExtras (lib : List String) : Gen (List (SDecl × LibFn)) := do
  let k ← weighted [(5, pure 0), (3, pure 1), (2, pure 2)]
  let mut fns := libFns.filter (lib.contains ·.name)
  let mut out := #[]
  for j in [0:k] do
    let (d, f) ← genFn s!"R{j}" fns (indsOf lib)
    out := out.push (d, f)
    fns := fns ++ [f]
  pure out.toList

/-- Reviewer-6's A1/L1 family (W10): a parameter `n0 : Nat` and an abstract function
`g1 : Π(u : Unit). Fam(n0)` (or over `&Nat`) whose codomain depends on `n0` through a
family whose arms are different data types (`TF`: `Bx(Unit)`/`Bx(B2)`, one constructor at two
parameters, as A1's `Box`; `TG`: `Nat`/`B2`, as L1). A match on
`n0` calls `g1` in several arms and uses the result at that arm's type: splits it, or (in
the `S` arm) observes it with a type-level function (`CmpBx`, `CmpB2`) whose `Id` compares
a place at its type. A split in one arm generalises the call; the other arm re-derives the
same program text. Returns the statement and the family's own proof candidates. -/
def genA1 : Gen (List (String × STerm) × STerm × STerm × STerm × List STerm) := do
  let tf ← chance 60
  let fam := if tf then "TF" else "TG"
  let byRef ← chance 25
  let dom : STerm := if byRef then .amp (.ident "Nat") else .ident "Unit"
  let ps : List (String × STerm) :=
    [("n0", .ident "Nat"), ("g1", .pi [("u", dom)] (.call (.ident fam) [.ident "n0"]))]
  let callG : STerm := if byRef then .call (.ident "g1") [.amp (.ident "c9")] else .call (.ident "g1") [.unitLit]
  let bind (x : String) (body : STerm) : STerm :=
    let b := STerm.letIn x none callG body
    if byRef then .letIn "c9" none (.num 0) b else b
  -- the Z arm's value (at the family's Z type) and the S arm's (at its S type), as a proposition
  -- or as a number
  let prop ← chance 70
  let splitZ (x : String) (e : STerm) : STerm :=
    if tf then .matchGen (.ident x) [("MkBx", ["v"], e)]
    else .matchGen (.ident x) [("Z", [], e), ("S", ["_"], e)]
  let splitS (y : String) (ef et : STerm) : STerm :=
    if tf then .matchGen (.ident y) [("MkBx", ["v"], .matchGen (.ident "v") [("F", [], ef), ("T", [], et)])]
    else .matchGen (.ident y) [("F", [], ef), ("T", [], et)]
  let observe (y : String) : STerm := .call (.ident (if tf then "CmpBx" else "CmpB2")) [.ident y]
  let armZ ← if prop then
      weighted [(3, pure (bind "x5" (splitZ "x5" .top))), (1, pure (bind "x5" .top)), (1, pure .top)]
    else
      weighted [(3, pure (bind "x5" (splitZ "x5" (.num 0)))), (1, pure (.num 0))]
  let armS ← if prop then
      weighted [(3, pure (bind "y6" (observe "y6"))), (1, pure (bind "y6" (splitS "y6" .top (.ident "False")))),
                (1, pure (bind "y6" .top))]
    else
      weighted [(3, pure (bind "y6" (splitS "y6" (.num 1) (.num 2)))), (1, pure (.num 1))]
  -- which arm comes first in the program text: the Z arm is checked first either way
  let body := STerm.matchGen (.ident "n0") [("Z", [], armZ), ("S", ["p7"], armS)]
  let lhs ← weighted [(3, pure body), (1, pure (.letIn "a8" none body (.ident "a8")))]
  let A : STerm := if prop then .sort 0 else .ident "Nat"
  let rhs ← if prop then
      weighted [(2, pure .top), (2, pure (.matchGen (.ident "n0") [("Z", [], .top), ("S", ["_"], .ident "False")]))]
    else weighted [(1, pure (.num 1)), (1, pure (.num 0)), (1, pure lhs)]
  -- the family's proofs: A1's own shape (a split of the call in the Z arm, `refl` in the S arm)
  let zProof : STerm := bind "x5" (splitZ "x5" (.ident "refl"))
  let proofs := [.matchGen (.ident "n0") [("Z", [], zProof), ("S", ["_"], .ident "refl")]]
  pure (ps, A, lhs, rhs, proofs)

/-- The E family with a dependent codomain (reviewer-6 W10: E against A1). A stuck block
returns a closure whose codomain mentions a value the arm refined (`λ(u : Unit) : Fam(p1) =>
h(clone(p1))` in `match q0 { Mk(p1, p2) => … }`), so the block's inferred Π-type captures an
arm-local σ (class E); or, over `n0 : Nat`, each arm's closure has codomain `Fam(n0)`, with
or without the block annotated. The continuation calls the closure in several arms of a
match on the same data and splits or observes the result at that arm's type. -/
def genEDep : Gen (List (String × STerm) × STerm × STerm × STerm × List STerm) := do
  let tf ← chance 60
  let fam := if tf then "TF" else "TG"
  let famOf (t : STerm) : STerm := .call (.ident fam) [t]
  let clo (t : STerm) : STerm :=
    .fix "_" [("u", .ident "Unit")] (famOf t) none (.call (.ident "h") [.call (.ident "clone") [t]])
  let splitZ (x : String) (e : STerm) : STerm :=
    if tf then .matchGen (.ident x) [("MkBx", ["v"], e)]
    else .matchGen (.ident x) [("Z", [], e), ("S", ["_"], e)]
  let observe (y : String) : STerm := .call (.ident (if tf then "CmpBx" else "CmpB2")) [.ident y]
  let useZ ← pick [STerm.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" .top), .top]
  let useS ← pick [STerm.letIn "y6" none (.call (.ident "f") [.unitLit]) (observe "y6"), .top]
  let hTy : STerm := .pi [("n", .ident "Nat")] (famOf (.ident "n"))
  -- data: a match on the result of `h`, whose type is the family at a parameter (stuck at the
  -- generic call), with the patterns of one of the family's types
  if ← chance 30 then
    let ps : List (String × STerm) := [("n0", .ident "Nat"), ("h", hTy)]
    let x : STerm := .call (.ident "h") [.ident "n0"]
    let m := if tf then STerm.matchGen (.ident "x5") [("MkBx", ["v"], .num 0)]
      else STerm.matchGen (.ident "x5") [("Z", [], .num 0), ("S", ["_"], .num 1)]
    let lhs := STerm.letIn "x5" none x m
    return (ps, .ident "Nat", lhs, ← pick [STerm.num 0, .num 1], [])
  let pairScrut ← chance 60
  if pairScrut then
    let ps : List (String × STerm) := [("q0", .prod (.ident "Nat") (.ident "Nat")), ("h", hTy)]
    let block := STerm.matchGen (.ident "q0") [("Mk", ["p1", "p2"], clo (.ident "p1"))]
    let cont := STerm.matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], useZ), ("S", ["_"], useS)])]
    let lhs := STerm.letIn "f" none block cont
    let rhs ← pick [STerm.top, .matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], .top), ("S", ["_"], .ident "False")])]]
    let zProof : STerm := .letIn "f" none block (.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" (.ident "refl")))
    let proofs := [.matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], .ident "refl"), ("S", ["_"], .ident "refl")])],
                   .matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], zProof), ("S", ["_"], .ident "refl")])]]
    pure (ps, .sort 0, lhs, rhs, proofs)
  else
    let ps : List (String × STerm) := [("n0", .ident "Nat"), ("h", hTy)]
    let annotated ← chance 50
    let block := STerm.matchGen (.ident "n0") [("Z", [], clo (.ident "n0")), ("S", ["p"], clo (.ident "n0"))]
    let fTy : STerm := .pi [("u", .ident "Unit")] (famOf (.ident "n0"))
    let cont := STerm.matchGen (.ident "n0") [("Z", [], useZ), ("S", ["_"], useS)]
    let lhs := STerm.letIn "f" (if annotated then some fTy else none) block cont
    let rhs ← pick [STerm.top, .matchGen (.ident "n0") [("Z", [], .top), ("S", ["_"], .ident "False")]]
    let zProof : STerm := .letIn "f" (if annotated then some fTy else none) block
      (.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" (.ident "refl")))
    let proofs := [.matchGen (.ident "n0") [("Z", [], zProof), ("S", ["_"], .ident "refl")]]
    pure (ps, .sort 0, lhs, rhs, proofs)

/-- The rules family (reviewer-6 W5): a declaration that a rule of the calculus forbids, which
the checker must reject. [T-Borrow]'s premise, that only places of a data type are
borrowed, at the term level: a borrow of a proof, of a value of a type variable, of a type
variable itself, of a function. And closures in data: an inductive parameter instantiated
at a Π-type or a sort (`Bx(Π(n : Nat). Nat)`, `Bx(Prop)`). Returns (rule, declaration). -/
def genRule : Gen (String × SDecl) := do
  let unitRet : STerm := .ident "Unit"
  let nat : STerm := .ident "Nat"
  let piNat : STerm := .pi [("n", nat)] nat
  let piRef : STerm := .pi [("y", .amp nat)] (.amp nat)
  let mk (ps : List (String × STerm)) (ret body : STerm) : SDecl :=
    { name := "RuleX", params := ps, ret := ret, body := body, expectAccept := false }
  let borrowThen (x : String) (after : STerm) : STerm := .letIn "r" none (.amp (.ident x)) after
  weighted [
    -- a borrow of a proof
    (3, do
      let P ← pick [STerm.top, .and .top .top, .app "Eq" [nat, .num 0, .num 0]]
      let after ← pick [STerm.unitLit, .seq (.deref (.ident "r")) .unitLit]
      pure ("borrow of a proof", mk [("h", P)] unitRet (borrowThen "h" after))),
    -- a borrow of a value of a type variable
    (2, do
      let after ← pick [STerm.unitLit, .assign (.deref (.ident "r")) (.ident "x")]
      pure ("borrow of a type variable's value", mk [("A", .sort 1), ("x", .ident "A")] unitRet (borrowThen "x" after))),
    -- a borrow of a type variable, written through
    (2, do
      let after ← pick [STerm.unitLit, .assign (.deref (.ident "r")) nat]
      pure ("borrow of a type", mk [("A", .sort 1)] unitRet (borrowThen "A" after))),
    -- a borrow of a function
    (2, do
      let after ← pick [STerm.unitLit, .assign (.deref (.ident "r")) (.ident "f")]
      pure ("borrow of a function", mk [("f", piNat)] unitRet (borrowThen "f" after))),
    -- a closure in data: an inductive parameter at a Π-type
    (3, do
      let (T, body, ret) ← pick [
        (piNat, STerm.ctorP "MkBx" [piNat] [.ident "f"], STerm.call (.ident "Bx") [piNat]),
        (piNat, STerm.unitLit, unitRet),
        (piRef, STerm.unitLit, unitRet)]
      let ps := if body matches .unitLit then [("b", STerm.call (.ident "Bx") [T])] else [("f", T)]
      pure ("Π-type as an inductive parameter", mk ps ret body)),
    -- an inductive parameter at a sort
    (1, do
      let so ← pick [STerm.sort 0, .sort 1]
      pure ("sort as an inductive parameter", mk [("b", .call (.ident "Bx") [so])] unitRet .unitLit)) ]

/-- The Drop family (meta-order's `Bad2`, DropProbe): a data function that assigns a borrow
returned by a stuck call, whose hole sits in several owners' fills, into a variable that
outlives one of the borrowed places, then accesses another owner. Symbolically the access
ends the borrow; at a ground instance it may not, and the place goes out of scope while
borrowed. The execution oracle runs it at ground inputs. -/
def genDropFn : Gen SDecl := do
  -- reviewer-9's Bad4 (Scratch/Reviewer9Probe.lean): a borrow into a single owner (`TailM`,
  -- whose result points at the owner or deep inside it), then a match on (or another access
  -- to) the owner; symbolically the match ends the borrow, on the ground the loan may sit
  -- deeper and survive it
  if ← chance 40 then
    let xParam ← chance 60
    let ownerParam ← chance 60
    let owner := if ownerParam then "a" else "b"
    let acc ← weighted [
      (3, pure (STerm.matchGen (.ident owner) [("Z", [], .unitLit), ("S", ["_"], .unitLit)])),
      (2, pure (STerm.matchGen (.ident owner) [("Z", [], .unitLit), ("S", ["p"], .matchGen (.ident "p") [("Z", [], .unitLit), ("S", ["_"], .unitLit)])])),
      (1, pure (STerm.letIn "z" none (.ident owner) .unitLit)),
      (1, pure (STerm.assign (.ident owner) (.num 3))) ]
    let body := STerm.seq (.assign (.ident "x") (.call (.ident "TailM") [.amp (.ident owner)])) acc
    let body := if ownerParam then body else .letIn "b" none (.ident "a") body
    let body := if xParam then body else .letIn "c" none (.num 1) (.letIn "x" none (.amp (.ident "c")) body)
    let ps : List (String × STerm) := (if xParam then [("x", .amp (.ident "Nat"))] else []) ++ [("a", .ident "Nat")]
    return { name := "RD", params := ps, ret := .ident "Unit", body := body, expectAccept := true }
  let xParam ← chance 60
  let call ← weighted [
    (3, pure (STerm.call (.ident "Pick") [.ident "n", .amp (.ident "a"), .amp (.ident "b")])),
    (2, pure (STerm.call (.ident "Pick") [.ident "n", .amp (.ident "b"), .amp (.ident "a")])),
    (2, pure (STerm.matchGen (.ident "n") [("Z", [], .amp (.ident "a")), ("S", ["_"], .amp (.ident "b"))])),
    (1, pure (STerm.call (.ident "PickX") [.amp (.ident "a"), .amp (.ident "b")])) ]
  let accesses : List STerm := [
    .letIn "z" none (.ident "b") .unitLit, .assign (.ident "b") (.num 2),
    .letIn "w" none (.amp (.ident "b")) .unitLit, .assign (.deref (.ident "x")) (.num 5),
    .letIn "v" none (.deref (.ident "x")) .unitLit ]
  let k ← weighted [(1, pure 0), (3, pure 1), (2, pure 2)]
  let mut after : List STerm := []
  for _ in [0:k] do after := after ++ [← pick accesses]
  let seqAll (ts : List STerm) (last : STerm) : STerm := ts.foldr (fun t acc => .seq t acc) last
  -- `a` in the function's scope, or in an inner block that ends before `x`'s scope
  let inner ← chance 40
  let core := STerm.letIn "a" none (.num 0) (seqAll (STerm.assign (.ident "x") call :: after) .unitLit)
  let body := if inner then .seq core .unitLit else core
  let body := if xParam then body
    else .letIn "c" none (.num 1) (.letIn "x" none (.amp (.ident "c")) body)
  let ps : List (String × STerm) := [("n", .ident "Nat"), ("b", .ident "Nat")] ++
    (if xParam then [("x", .amp (.ident "Nat"))] else [])
  pure { name := "RD", params := ps, ret := .ident "Unit", body := body, expectAccept := true }

/-- The audit family (rule-audit's witnesses, notes/rule-audit.md): declarations where the
checker and the printed rules disagree. Returns declarations the printed rules reject,
helper declarations, and pairs the printed rules decide alike.
- `NatT`: a `Nat` match on a value whose stored type is not `Nat` ([Split]'s stored-type
  premise), as data or as a proof by splitting;
- `EqConf`: an assignment to an outer place inside a side of `Eq` ([T-Erase], [Erase-err]);
- `JT`: `J` with non-convertible endpoints runs its body ([J-stuck]), through a helper `JF`;
- `MixPos`: a type annotation whose arms disagree on being proofs ([Type-pos]);
- `BlockRef`: a closure in a stuck block's arm capturing a written place ([Fix]);
- `EtaP`/`EtaCtl`: a read of a pair's field after a block that moved the other one, and the
  same read without the block (no η for pairs unless D62; either way both alike). -/
def genAudit : Gen (List (String × SDecl) × List SDecl × List (String × SDecl × SDecl)) := do
  let nat : STerm := .ident "Nat"
  let mk (n : String) (ps : List (String × STerm)) (ret body : STerm) (acc : Bool := false) : SDecl :=
    { name := n, params := ps, ret := ret, body := body, expectAccept := acc }
  let idS (A t u : STerm) : STerm := .app "Id" [A, t, u]
  let natMatch (x : STerm) (e0 e1 : STerm) : STerm := .matchGen x [("Z", [], e0), ("S", ["_"], e1)]
  let k ← pick [1, 2, 5]
  weighted [
    (2, do
      let asProof ← chance 40
      let ps := [("T", STerm.sort 1), ("x", .ident "T")]
      if asProof then
        let d := mk "AuditX" ps (idS nat (natMatch (.ident "x") (.num 0) (.num 0)) (.num 0))
          (.matchGen (.ident "x") [("Z", [], .ident "refl"), ("S", ["p"], .ident "refl")])
        pure ([("Nat match on a non-Nat stored type", d)], [], [])
      else
        pure ([("Nat match on a non-Nat stored type", mk "AuditX" ps nat (natMatch (.ident "x") (.num 0) (.num k)))], [], [])),
    (2, do
      let side := STerm.seq (.assign (.ident "x") (.num k)) (.num 0)
      let eqT := STerm.app "Eq" [nat, side, .num 0]
      let asProof ← chance 60
      -- since rule-audit's C22 (ad2bdd26) `Eq`'s sides run on a private copy, unconfined, so
      -- the assignment is discarded and the declaration is ACCEPTED (and `x` is unchanged)
      let d := if asProof then
          mk "AuditX" [("x", nat)] (idS nat (.letIn "T" none eqT (.ident "x")) (.ident "x")) (.ident "refl") true
        else mk "AuditX" [("x", nat)] nat (.letIn "T" none eqT (.ident "x")) true
      pure ([("an Eq side's assignment is discarded (accepted)", d)], [], [])),
    (2, do
      let jf := mk "JF" [("a", nat), ("b", nat), ("h", .app "Eq" [nat, .ident "a", .ident "b"]), ("x", .amp nat)] nat
        (.call (.ident "J") [nat, .ident "a", .ident "b", .fix "_" [("z", nat)] (.sort 1) none nat, .ident "h",
          .seq (.assign (.deref (.ident "x")) (.num k)) (.num 0)]) true
      let d := mk "AuditX" [("a", nat), ("b", nat), ("h", .app "Eq" [nat, .ident "a", .ident "b"])]
        (idS nat (.letIn "c" none (.num 0) (.seq (.call (.ident "JF") [.ident "a", .ident "b", .ident "h", .amp (.ident "c")]) (.ident "c"))) (.num k))
        (.ident "refl")
      pure ([("J with non-convertible endpoints runs its body", d)], [jf], [])),
    (1, do
      let ann := natMatch (.ident "n") nat (.ident "h")
      let d := mk "AuditX" [("h", .top)] nat (.letIn "n" none (.num 0) (.letIn "x" (some ann) (.num k) (.ident "x")))
      pure ([("a type position accepts arms that disagree on being proofs", d)], [], [])),
    (2, do
      let v ← pick ["T", "F"]
      let arm (withClo : Bool) : STerm :=
        let w := STerm.assign (.ident "x") (.ident v)
        if withClo then .seq w (.letIn "f" none (.fix "_" [("u", .ident "Unit")] (.ident "B2") none (.ident "x")) .unitLit)
        else .seq w .unitLit
      let blk (withClo : Bool) : STerm := .seq (natMatch (.ident "n") (arm withClo) .unitLit) (.ident "x")
      let d := mk "AuditX" [("n", nat), ("x", .ident "B2")] (idS (.ident "B2") (blk true) (blk false))
        (natMatch (.ident "n") (.ident "refl") (.ident "refl"))
      pure ([("a closure in a block captures through the block's borrow", d)], [], [])),
    (2, do
      -- the field read is never the one the block moves (reading a moved field differs for a
      -- reason of its own, D53)
      let (moved, read) ← pick [("a", 2), ("b", 1)]
      let armBody ← pick [STerm.letIn "v" none (.ident moved) .unitLit, .unitLit]
      let rd : STerm := .proj read (.ident "q")
      let a := mk "EtaP" [("q", .prod nat nat)] nat (.seq (.matchGen (.ident "q") [("Mk", ["a", "b"], armBody)]) rd) true
      let b := mk "EtaCtl" [("q", .prod nat nat)] nat rd true
      pure ([], [], [("a pair's field read with and without a block before it", a, b)])) ]

/-- The template names the A1 family needs. -/
def a1Lib : List String := ["B2", "Bx", "TF", "TG", "CmpBx", "CmpB2", "HG", "HF"]

def mkCase (seed i : Nat) (fuel : Nat := 200000) (a1 : Nat := 0) (edep : Nat := 0) (rules : Nat := 0) (drop : Nat := 0) (audit : Nat := 0) : Case × Rng := Id.run do
  let phase1 : Gen (List String × List (SDecl × LibFn)) := do
    let lib ← genTemplates
    pure (lib, ← genExtras lib)
  let ((lib, extras), g1) := phase1.run { rng := caseRng seed i }
  let ok := acceptedNames {} fuel ((Block.decls Prelude) ++ lib.filterMap libDecl ++ extras.map (·.1))
  let extras := extras.filter fun (d, _) => ok.contains d.name
  -- attack templates are offered even when the default rules reject them (live with a switch off)
  let fns := libFns.filter (fun f => ok.contains f.name || (f.attack && lib.contains f.name)) ++ extras.map (·.2)
  let ((ps, A, lhs, rhs), g2) := (genStmt fns (indsOf lib)).run g1
  -- a quarter of the cases also carry a conversion pair
  let mutate (b : STerm) : List STerm := [.seq .unitLit b, .letIn "z9" none (.num 0) b] ++ shrinkT b
  let ((conv, _), g3) := (do
      if ← chance 25 then pure (← genConvPair fns (indsOf lib) mutate, ()) else pure (none, ())).run g2
  let c0 : Case := { lib := lib, extra := extras.map (·.1), params := ps, ty := A, lhs := lhs, rhs := rhs, conv := conv }
  -- `a1` percent of the cases are the A1 family instead, drawn from their own streams so
  -- that every other case is the one it would be without the family
  let (x, _) := (caseRng seed (i + 1000003)).next
  if a1 > 0 && x.toNat % 100 < a1 then
    let ((ps, A, lhs, rhs, prf), g4) := genA1.run { rng := caseRng seed (i + 2000003) }
    return ({ c0 with lib := closeDeps (lib ++ a1Lib), params := ps, ty := A, lhs := lhs, rhs := rhs,
                      conv := none, extraProofs := prf }, g4.rng)
  let (u, _) := (caseRng seed (i + 9000011)).next
  if audit > 0 && u.toNat % 100 < audit then
    let ((rds, helpers, agrees), g8) := genAudit.run { rng := caseRng seed (i + 10000019) }
    return ({ c0 with lib := closeDeps (lib ++ ["B2"]), extra := c0.extra ++ helpers, ruleDecls := rds,
                      agreeDecls := agrees }, g8.rng)
  let (w, _) := (caseRng seed (i + 7000003)).next
  if drop > 0 && w.toNat % 100 < drop then
    let (rd, g7) := genDropFn.run { rng := caseRng seed (i + 8000009) }
    return ({ c0 with lib := closeDeps (lib ++ ["Pick", "PickX", "TailM"]), extra := c0.extra ++ [rd] }, g7.rng)
  let (z, _) := (caseRng seed (i + 5000011)).next
  if rules > 0 && z.toNat % 100 < rules then
    let (rd, g6) := genRule.run { rng := caseRng seed (i + 6000013) }
    return ({ c0 with lib := closeDeps (lib ++ ["Bx"]), ruleDecls := [rd] }, g6.rng)
  let (y, _) := (caseRng seed (i + 3000017)).next
  if edep > 0 && y.toNat % 100 < edep then
    let ((ps, A, lhs, rhs, prf), g5) := genEDep.run { rng := caseRng seed (i + 4000037) }
    return ({ c0 with lib := closeDeps (lib ++ a1Lib), params := ps, ty := A, lhs := lhs, rhs := rhs,
                      conv := none, extraProofs := prf }, g5.rng)
  (c0, g3.rng)

end Ochr.Fuzz
