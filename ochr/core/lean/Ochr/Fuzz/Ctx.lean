import Ochr.Fuzz.Lib

/-!
# Fuzzer: the generation context

The generator is type-directed and tracks, approximately, which variables are still
usable: a moved borrow variable, or a borrow whose owner was accessed since, is marked
dead (in `GenSt.dead`) and not generated again. The tracking is conservative and
incomplete; the checker is the judge, and a program it rejects on the symbolic path is
simply uninteresting.
-/

namespace Ochr.Fuzz
open Ochr.Surface

inductive VKind where
  | owned      -- an owned local or parameter: the place `x`
  | bvar       -- a borrow variable `x : &T`: the place `*x`; reading `x` moves it
  | alias      -- a pattern variable: a sub-place of a matched place
  | fnv        -- a function value
deriving BEq, Inhabited

structure GVar where
  name : String
  ty : GTy            -- for `bvar`, the borrow type `ref T`
  kind : VKind
  root : String       -- the variable whose accesses end this one (itself for owned)
  param : Bool := false
deriving Inhabited

structure Ctx where
  vars : List GVar := []
  lib : List LibFn := []
  inds : List String := []
  inLam : Bool := false      -- inside a λ body: no borrows in scope
deriving Inhabited

def Ctx.push (Γ : Ctx) (v : GVar) : Ctx := { Γ with vars := v :: Γ.vars }

def isDead (n : String) : Gen Bool := do pure ((← get).dead.contains n)

def kill (n : String) : Gen Unit := modify fun s => { s with dead := n :: s.dead }

/-- An access to the owned variable `r` ends the borrows taken from it; a write also
invalidates the pattern variables below it. -/
def touch (Γ : Ctx) (r : String) (write : Bool) : Gen Unit := do
  for v in Γ.vars do
    if v.root == r && v.name != r then
      if v.kind == .bvar || (write && v.kind == .alias) then kill v.name

/-- The content type of a variable seen as a place. -/
def GVar.placeTy (v : GVar) : Option GTy :=
  match v.kind, v.ty with
  | .bvar, .ref t => some t
  | .owned, t | .alias, t => if t.isData || (t matches .prop) || t.isProof then some t else none
  | _, _ => none

def GVar.place (v : GVar) : STerm :=
  if v.kind == .bvar then .deref (.ident v.name) else .ident v.name

/-- The variable at the root of the variable's place (a pattern variable's `root` is
its scrutinee's). Accessing the place is an access to this variable. -/
def GVar.proot (v : GVar) : String := if v.kind == .alias then v.root else v.name

/-- Live, or (rarely) dead anyway: a use after a move or after the borrow ended is how
C5- and D29-style bugs show, so the generator sometimes makes one on purpose. -/
def usable (v : GVar) : Gen Bool := do
  if !(← isDead v.name) && !(v.kind == .alias && (← isDead v.root)) then return true
  chance 6

/-- Usable places of content type `T`, parameters listed twice (they are abstract on
the symbolic path, which is where closing off happens). -/
def placesOf (Γ : Ctx) (T : GTy) : Gen (List GVar) := do
  let mut out := []
  for v in Γ.vars do
    if !(← usable v) then continue
    if let some t := v.placeTy then
      if t == T then
        out := out ++ (if v.param then [v, v] else [v])
  pure out

def natLit (k : Nat) : STerm := .num k

/-- Read a place of type `T` (applying the access to the borrow tracking). -/
def readPlace? (Γ : Ctx) (T : GTy) : Gen (Option STerm) := do
  let ps ← placesOf Γ T
  if ps.isEmpty then return none
  let v ← pick ps
  touch Γ v.proot false
  pure (some v.place)

/-- A borrow of content type `T` for a call argument or a `let`: `&p`, a reborrow
`&*x`, a move of a borrow variable `x`, or (rarely) a borrow of a sub-place `&(p).1`.
`avoid` are roots already borrowed by the same call. Returns the term and its root. -/
def borrowOf? (Γ : Ctx) (T : GTy) (avoid : List String) : Gen (Option (STerm × String)) := do
  -- (inside a λ the context has no captured borrows already: `lamCtx`)
  let ps := (← placesOf Γ T).filter fun v => !avoid.contains v.proot
  if ps.isEmpty then return none
  let v ← pick ps
  touch Γ v.proot false
  if v.kind == .bvar then
    if ← chance 30 then
      kill v.name
      return some (.ident v.name, v.root)
    return some (.amp (.deref (.ident v.name)), v.name)
  if T == .nat && (← chance 8) then
    return some (.amp (.proj 1 v.place), v.proot)
  pure (some (.amp v.place, v.proot))

/-- The constructors of a declared inductive, with field types, as the generator sees them. -/
def ctorsOf : String → List (String × List (String × GTy))
  | "B2" => [("F", []), ("T", [])]
  | "L" => [("Nil", []), ("Cons", [("h", .nat), ("t", .ind "L")])]
  | "Box" => [("Mk", [("v", .nat)])]
  | "Or" => [("Inl", [("l", .proof)]), ("Inr", [("r", .proof)])]
  | "ExN" => [("Wit", [("n", .nat), ("e", .proof)])]
  | _ => []

/-- The arms of a match on a proof of `P` (v2.x, D45: by the type). `False` and an opaque
statement have none (`match h {}`; on an opaque statement this type-checks only where the
statement computes to `False`, D49 (1)). -/
def pfShapes : PT → List (String × List (String × GTy))
  | .top => [("I", [])]
  | .and a b => [("Intro", [("l", .pf a), ("r", .pf b)])]
  | .or => ctorsOf "Or"
  | .ex => ctorsOf "ExN"
  | .fls | .opq .. => []

/-- Is a match on a proof of `P` a subsingleton elimination (D45: no constructors, or one
whose fields are all proofs), so that it may produce data or effects? -/
def PT.large : PT → Bool
  | .top | .and .. | .fls | .opq .. => true
  | .or | .ex => false

/-- The proof variables in scope (usable), with their propositions. -/
def proofVars (Γ : Ctx) : Gen (List (GVar × PT)) := do
  let mut out := []
  for v in Γ.vars do
    if !(← usable v) then continue
    if let some (.pf P) := v.placeTy then out := out ++ [(v, P)]
  pure out

end Ochr.Fuzz
