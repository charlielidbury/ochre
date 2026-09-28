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
  | .fix _ _ ds c b => ds.any (·.mentionsConst n) || c.mentionsConst n || b.mentionsConst n
  | .call f as _ => f.mentionsConst n || as.any (·.mentionsConst n)
  | .eq a b c | .id a b c => a.mentionsConst n || b.mentionsConst n || c.mentionsConst n
  | .prim _ as => as.any (·.mentionsConst n)
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
    unless T == some goal do
      err s!"the body of {d.name} has type {T.getD .bot}, but the goal is {goal}"
    let v ← if (← get).cfg.p5 && (← isPropV goal) then pure .proof else pure v
    modify fun s => { s with env := #[{}], globals := s.globals ++ [⟨d.name, goal, none, v⟩] }
  else
    let fixT := Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.body
    let ty := Value.tPi [] (.pi d.hs d.doms d.cod)
    modify fun s => { s with globals := s.globals ++ [⟨d.name, ty, some fixT, .gfn d.name⟩] }
    checkFix (.gfn d.name) [] fixT

/-- Check a list of definitions in order, with a fresh state per definition apart
from the globals accepted so far. -/
def checkDefs (cfg : Config) (ds : List Def) (fuel : Nat := 2000000) :
    List (String × Verdict × Array String) := Id.run do
  let mut globals : List GDef := []
  let mut out := #[]
  for d in ds do
    let st : MState := { globals := globals, cfg := cfg, fuel := fuel }
    let (r, tr) := ((checkDef d).run st).run.run #[]
    match r with
    | .ok ((), st') =>
      globals := st'.globals
      out := out.push (d.name, .accepted, tr)
    | .error (.error m) => out := out.push (d.name, .rejected m, tr)
    | .error (.stuck _) => out := out.push (d.name, .rejected "internal: stuck escaped to the top", tr)
  pure out.toList

/-- The globals after checking a list of definitions (rejected ones are left out). -/
def globalsAfter (cfg : Config) (ds : List Def) : List GDef := Id.run do
  let mut globals : List GDef := []
  for d in ds do
    let st : MState := { globals := globals, cfg := cfg }
    match (((checkDef d).run st).run.run #[]).1 with
    | .ok ((), st') => globals := st'.globals
    | .error _ => pure ()
  pure globals

/-- Run a machine computation from a given state (for unit tests). -/
def runM {α : Type} (x : M α) (st : MState) : Except String α :=
  match ((x.run st).run.run #[]).1 with
  | .ok (a, _) => .ok a
  | .error (.error m) => .error m
  | .error (.stuck _) => .error "stuck"

end Ochr
