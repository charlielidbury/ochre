import Ochr.Machine

/-!
# Checking programs: a sequence of top-level definitions

A definition `def f (x̄ : Ā) : B := b` is the closed term `fix f (x̄:Ā):B := b`,
checked by [Def] (`checkFix`). A definition with no parameters is a constant: its
type is evaluated, its body is checked against it, and its value is stored.
Definitions are checked in order; a rejected one is not added to the globals.
-/

namespace Ochr

structure Def where
  name : String
  hs : List Hint
  doms : List Term
  cod : Term
  dec : Option Nat := none     -- `by xⱼ`: the decreasing parameter
  body : Term
deriving Inhabited

inductive Verdict where
  | accepted
  | rejected (msg : String)
deriving Inhabited

def Verdict.ok : Verdict → Bool
  | .accepted => true
  | .rejected _ => false

partial def Term.mentionsConst (n : String) : Term → Bool
  | .const m => m == n
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.mentionsConst n
  | .letIn _ t u | .seq t u | .prod t u | .pair t u | .and t u | .andI t u | .cong t u
  | .ascribe t u => t.mentionsConst n || u.mentionsConst n
  | .matchNat _ z s => z.mentionsConst n || s.mentionsConst n
  | .pi _ ds c => ds.any (·.mentionsConst n) || c.mentionsConst n
  | .fix _ _ ds c _ b => ds.any (·.mentionsConst n) || c.mentionsConst n || b.mentionsConst n
  | .call f as _ => f.mentionsConst n || as.any (·.mentionsConst n)
  | .eq a b c | .id a b c => a.mentionsConst n || b.mentionsConst n || c.mentionsConst n
  | .prim _ as | .ctor _ _ _ as => as.any (·.mentionsConst n)
  | .matchInd _ _ as => as.any (·.2.mentionsConst n)
  | _ => false

/-- Check one definition and add it to the globals. -/
def checkDef (d : Def) : M Unit := do
  if (d.cod :: d.doms).any (Term.mentionsConst d.name) then
    err s!"{d.name} occurs in its own type"
  if d.doms.isEmpty then
    -- a constant
    modify fun s => { s with env := #[{}], goal := none, recStack := [], recCands := [], refs := [] }
    let goal ← evalType d.cod
    let (v, T) ← eval true d.body
    unless (← match T with | some T => conv T goal | none => pure false) do
      err s!"the body of {d.name} has type {T.getD .bot}, but the goal is {goal}"
    let v ← if (← get).cfg.p5 && (← isPropV goal) then pure .proof else pure v
    modify fun s => { s with env := #[{}], globals := s.globals ++ [⟨d.name, goal, none, v⟩] }
  else
    let fixT := Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body
    let ty := Value.tPi [] (.pi d.hs d.doms d.cod)
    modify fun s => { s with globals := s.globals ++ [⟨d.name, ty, some fixT, .gfn d.name⟩] }
    checkFix (.gfn d.name) [] fixT

/-- A program item: a definition, or an inductive type declaration. -/
inductive Item where
  | defn (d : Def)
  | ind (name : String) (ctors : List (String × List (String × Term)))
deriving Inhabited

def Item.name : Item → String
  | .defn d => d.name
  | .ind n _ => n

/-- D36 (v1.7): a field type is first-order data: declared inductive types (the one
being declared among them), `Nat`, `Unit` and `×` of these; no `Π`, no `&`, no sort, no
proposition. This is strict positivity in its simplest form. -/
def firstOrder : Value → Bool
  | .tNat | .tUnit | .tInd _ => true
  | .tProd A B => firstOrder A && firstOrder B
  | _ => false

/-- Declare an inductive type: constructors with named fields of closed, borrow-free
types; fields may mention the type itself (recursive) or earlier types. -/
def checkInd (n : String) (ctors : List (String × List (String × Term))) : M Unit := do
  if (← get).inds.any (·.name == n) then err s!"{n} is already declared"
  modify fun s => { s with env := #[{}], inds := s.inds ++ [⟨n, []⟩] }
  let mut cs := #[]
  for (cn, fields) in ctors do
    let mut fs := #[]
    for (fname, FT) in fields do
      let T ← evalType FT
      if T.typeHasRef then err s!"field {fname} of {cn}: no borrows inside data"
      if (← sortOf T) != 1 then err s!"field {fname} of {cn}: its type must be a data type in Type"
      if (← get).cfg.positivity && !firstOrder T then
        err s!"field {fname} of {cn} : {T}: fields are first-order data (inductive types, Nat, Unit, ×), D36"
      fs := fs.push (fname, T)
    cs := cs.push (cn, fs.toList)
  modify fun s => { s with inds := s.inds.map fun d => if d.name == n then ⟨n, cs.toList⟩ else d }

def checkItem : Item → M Unit
  | .defn d => checkDef d
  | .ind n cs => checkInd n cs

/-- Check a list of items in order, with a fresh state per item apart from the
globals and inductive types accepted so far. -/
def checkDefs (cfg : Config) (ds : List Item) (fuel : Nat := 2000000) :
    List (String × Verdict × Array String) := Id.run do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  let mut out := #[]
  for d in ds do
    let st : MState := { globals := globals, inds := inds, cfg := cfg, fuel := fuel }
    let (r, tr) := ((checkItem d).run st).run.run #[]
    match r with
    | .ok ((), st') =>
      globals := st'.globals
      inds := st'.inds
      out := out.push (d.name, .accepted, tr)
    | .error (.error m) => out := out.push (d.name, .rejected m, tr)
    | .error (.stuck _) => out := out.push (d.name, .rejected "internal: stuck escaped to the top", tr)
  pure out.toList

/-- The globals and inductive types after checking a list of items. -/
def globalsAfter (cfg : Config) (ds : List Item) : List GDef × List IndDecl := Id.run do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  for d in ds do
    let st : MState := { globals := globals, inds := inds, cfg := cfg }
    match (((checkItem d).run st).run.run #[]).1 with
    | .ok ((), st') => globals := st'.globals; inds := st'.inds
    | .error _ => pure ()
  pure (globals, inds)

/-- Run a machine computation from a given state (for unit tests). -/
def runM {α : Type} (x : M α) (st : MState) : Except String α :=
  match ((x.run st).run.run #[]).1 with
  | .ok (a, _) => .ok a
  | .error (.error m) => .error m
  | .error (.stuck _) => .error "stuck"

end Ochr
