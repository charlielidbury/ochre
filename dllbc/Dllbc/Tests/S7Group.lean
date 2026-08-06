import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Migrate

/-!
# §6.1 test suite — entangled calls and loan groups

Some functions break the wire correspondence: `choose` returns a borrow into
`x` OR `y` depending on a runtime bool, so no per-loan promise can say where a
written value lands. A call mints a **loan group** tying the loans it captured
to the borrows it issued, and the ending discipline is the group's whole
content — every issued borrow ends first, then the group ends atomically,
releasing each captured loan. The ordering *is* the soundness argument: a
captured owner cannot recover while an issued borrow lives.

The headline is the pair: the opaque group **forgets** (choose → distinct
fresh σ's; `z = 7` is not provable, and that is the cost, §6.2), while the
identity wire **remembers** (through → the owner recovers the written value).
M5/M6's wires are now the degenerate `issued = []` group.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S7Group

def natT : Term := .const "Nat"
def boolT : Term := .const "Bool"
def listNatT : Term := .app (.const "List") natT

/-! ## `choose`: the entangled call -/

-- choose (c : Bool, x : &mut Nat, y : &mut Nat) → &mut Nat = match c { … }.
-- The callee checks under the borrow-returning audit: each branch consumes one
-- argument borrow into the result (exempt) and audits the other.
def choose : FnDef :=
  { name := "choose", retType := .borrowT natT natT,
    telescope := [("c", boolT), ("x", .borrowT natT natT), ("y", .borrowT natT natT)],
    body := dllbc [c, x, y] { match c { True => x, False => y } } }

example : Migrate.progOkOf choose = true := by native_decide

-- The §6.1 trace verbatim. After `*r := 7`, demanding `a` (via `let z = a`)
-- forces the cascade: End ℓᵣ first (its 7 surrendered and DISCARDED — the
-- ordering as soundness, r ↦ ⊥ and 7 never reaches a or b), then the group
-- ends ATOMICALLY (b's fresh existential arrives too, though only a was
-- demanded). a and b hold DISTINCT fresh σ's; z holds a's. The imprecision is
-- the point: z = 7 is not provable (§6.2's cost).
def chooseCaller : FnDef :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbc{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      *r := 7;
      let z = a;
      () } }

-- `let z = a` ends the group (fresh existentials for a and b) and then COPIES
-- a's existential (§2.1), so a and z share it; canonicalization numbers a's σ
-- first (it now appears in a's own slot), b's second.
example : Migrate.progEnvOfT [choose, chooseCaller] chooseCaller
  [("a", .sym 0), ("b", .sym 1), ("pa", .bot), ("pb", .bot), ("r", .bot), ("z", .sym 0)]
  = true := by native_decide

/-! ## A single-borrow wire is opaque too (no signature-driven precision) -/

-- through (b : &mut List Nat) → &mut List Nat = b. It shares its SIGNATURE with
-- an `advance` that returns a field reborrow of the tail — signature-only
-- checking cannot tell them apart, so constraining the captured release to the
-- surrendered payload would be UNSOUND. Every opaque group therefore releases
-- a fresh existential: the caller below recovers a FRESH σ : List Nat, NOT the
-- written `Cons 9 Nil`. Precision is deliberately lost; §6.2's transparent/spec
-- group ends are the recovery route.
def through : FnDef :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbc [b] { b } }

example : Migrate.progOkOf through = true := by native_decide

def throughCaller : FnDef :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbc{
      let x = Cons(1, Nil); let b = &mut x;
      let r = through(b);
      *r := Cons(9, Nil);
      let y = x;
      () } }

-- y is a fresh σ (the write is forgotten — deliberate, per the soundness fix).
-- `x`'s recovered σ is typed `List Nat` (DATA), so reading it MOVES it (§2.1).
example : Migrate.progEnvOfT [through, throughCaller] throughCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

/-! ## Rejections -/

-- The group cannot end because an issued borrow cannot surrender: `*r` was
-- taken, leaving its payload a hole (⊥), and then a captured owner is demanded.
example : Migrate.progRejectsOf
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbc{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      let tk = *r;
      let z = a;
      () } }
  "nothing surrendered" [choose] = true := by native_decide

-- A borrow-returning body whose returned payload fails its owed type:
-- `bad (b : &mut Nat) → &mut Bool = b` returns a Nat borrow as a Bool borrow.
example : Migrate.progRejectsOf
  { name := "bad", retType := .borrowT boolT boolT,
    telescope := [("b", .borrowT natT natT)],
    body := dllbc [b] { b } }
  "owed type" = true := by native_decide

/-! ## The constrained branch, exercised directly (dead under opaque calls) -/

def listNatV : Val := .app (.const "List") (.const "Nat")

/-- A hand-built `constrained` group: owner `o ↦ loanₘ 100`, issued borrow
    `i ↦ borrowₘ 200 (Cons 9 Nil)`, tied by ρ0. -/
def constrainedGroup : Group :=
  { id := 0, captured := [(100, listNatV)], issued := [(200, listNatV)], constrained := true }

def constrainedSt : St :=
  { initSt with
    env := [(⟨0, "o"⟩, .loanM 100), (⟨1, "i"⟩, .borrowM 200 (cons (nat 9) nil))],
    groups := [constrainedGroup] }

/-- Ending the constrained group directly: the owner recovers the surrendered
    payload. -/
def constrainedResult : Bool :=
  match (endGroup 1000 constrainedGroup).run constrainedSt with
  | .ok _ st' => canonicalize st'.env == [("o", cons (nat 9) nil), ("i", .bot)]
  | .error _ _ => false

-- No call mints a `constrained` group (that inference is unsound, removed), so
-- `endGroup`'s constrained branch is unreachable through the checker. It stays
-- for §6.2's transparent/spec ends; this drives it directly so the branch is
-- not dead-untested: the captured owner recovers the issued borrow's
-- SURRENDERED payload (`Cons 9 Nil`), not a fresh σ.
example : constrainedResult = true := by native_decide

end Dllbc.Tests.S7Group
