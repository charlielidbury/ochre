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
  | .letIn _ t u | .seq t u | .cong t u
  | .ascribe t u => t.mentionsConst n || u.mentionsConst n
  | .matchNat _ z s => z.mentionsConst n || s.mentionsConst n
  | .pi _ ds c => ds.any (·.mentionsConst n) || c.mentionsConst n
  | .fix _ _ ds c _ b => ds.any (·.mentionsConst n) || c.mentionsConst n || b.mentionsConst n
  | .call f as _ => f.mentionsConst n || as.any (·.mentionsConst n)
  | .eq a b c | .id a b c => a.mentionsConst n || b.mentionsConst n || c.mentionsConst n
  | .ctor _ _ _ ps as => ps.any (·.mentionsConst n) || as.any (·.mentionsConst n)
  | .prim _ as | .tind _ as => as.any (·.mentionsConst n)
  | .matchInd _ _ as => as.any (·.2.mentionsConst n)
  | _ => false

/-! ### D55: sorts are syntactic

Every term written where a type is expected must have a *declared* type (read from the
declared types of its heads, without normalising: the D35 notion) that is syntactically a
sort. `DeclInfo` is what a declared type says, read off its term: a sort, a Π-type (with
what its codomain says), or anything else. -/

inductive DeclInfo where
  | sort (l : Nat)        -- the declared type is the sort `l` (`0` = `Prop`): the term is a type
  | pi (cod : DeclInfo)   -- the declared type is a Π-type whose codomain says `cod`
  | ref (A : DeclInfo)    -- the declared type is `&A`
  | other
deriving BEq, Inhabited

/-- What a type term says, read syntactically. -/
partial def Term.asDecl : Term → DeclInfo
  | .sort l | .val (.sort l) => .sort l
  | .pi _ _ c => .pi c.asDecl
  | .val (.tPi _ (.pi _ _ c)) => .pi c.asDecl
  | .ref A => .ref A.asDecl
  | _ => .other

/-- What a type value says (a global's stored declared type). -/
def Value.asDecl : Value → DeclInfo
  | .sort l => .sort l
  | .tPi _ (.pi _ _ c) => .pi c.asDecl
  | .tRef (.sort l) => .ref (.sort l)
  | _ => .other

/-- The declared type of a place: a variable's, or through a borrow the borrowed type's. -/
def placeDecl (sc : List DeclInfo) : Place → DeclInfo
  | .var i => sc.getD i .other
  | .deref q => match placeDecl sc q with
    | .ref d => d
    | _ => .other
  | _ => .other

mutual
/-- The declared type of `t` in a scope giving each variable's (`sc`, de Bruijn order; `ns`
its name, for messages), checking every type position inside `t` (D55). -/
partial def declOf (sc : List DeclInfo) (ns : List String) (t : Term) : M DeclInfo := do
  let sub (u : Term) : M Unit := discard (declOf sc ns u)
  match t with
  | .place p => pure (placeDecl sc p)
  | .borrow _ | .zero | .tt => pure .other
  | .assign _ u | .succ u | .fst u | .snd u => sub u; pure .other
  | .letIn h u w => do let d ← declOf sc ns u; declOf (d :: sc) (h.name :: ns) w
  | .seq u w => sub u; declOf sc ns w
  | .matchNat _ z s => do
    let a ← declOf sc ns z
    let b ← declOf sc ns s
    pure (if a == b then a else .other)
  | .matchInd _ _ arms => do
    let ds ← arms.mapM fun (_, a) => declOf sc ns a
    pure (match ds with
      | d :: rest => if rest.all (· == d) then d else .other
      | [] => .other)
  | .const n =>     -- an unknown name is the machine's error, reported where it is met
    tryCatch (do pure (← lookupGlobal n).ty.asDecl) fun _ => pure (.sort 1)
  | .val v => match v with
    | .sort l => pure (.sort (l + 1))
    | .tNat | .tUnit | .tRef _ | .tInd .. | .tEq .. | .tPi .. => pure (.sort (← sortOf v))
    | .gfn n => pure (← lookupGlobal n).ty.asDecl
    | .clo _ (.fix _ _ _ c _ _) => pure (.pi c.asDecl)
    | _ => pure .other
  | .sort l => pure (.sort (l + 1))
  | .nat | .unit => pure (.sort 1)
  | .ref A => discard (typePos sc ns A); pure (.sort 1)
  | .pi hs ds c => do
    let (sc', ns', l) ← telescope sc ns hs ds
    let lc ← typePos sc' ns' c
    pure (.sort (if lc == 0 then 0 else max l lc))
  | .fix self hs ds c _ body => do
    let (sc', ns', _) ← telescope sc ns hs ds
    discard (typePos sc' ns' c)
    -- the body sees the parameters, then `self`, then the enclosing scope
    let scB := (ds.map Term.asDecl).reverse ++ (DeclInfo.pi c.asDecl :: sc)
    let nsB := (hs.map (fun (h : Hint) => h.name)).reverse ++ (self.name :: ns)
    discard (declOf scB nsB body)
    pure (DeclInfo.pi c.asDecl)
  | .call f as _ => do
    let df ← declOf sc ns f
    for a in as do sub a
    pure (match df with | .pi r => r | _ => .other)
  | .eq A a b | .id A a b => do
    discard (typePos sc ns A); sub a; sub b; pure (.sort 0)
  | .cong f h => sub f; sub h; pure .other
  | .ascribe u A => do discard (typePos sc ns A); sub u; pure A.asDecl
  | .prim "J" [A, a, b, P, h, u] => do
    discard (typePos sc ns A)
    for x in [a, b, h, u] do sub x
    let dP ← declOf sc ns P
    pure (match dP with | .pi r => r | _ => .other)
  | .prim _ as => for a in as do sub a
                  pure .other
  | .tind n as => do
    for a in as do discard (typePos sc ns a)
    tryCatch (do pure (.sort (← lookupInd n).sort)) fun _ => pure (.sort 1)
  | .ctor _ _ _ ps as => do
    for p in ps do discard (typePos sc ns p)
    for a in as do sub a
    pure .other

/-- A term written where a type is expected: its declared type must be a sort (D55);
returns the sort. -/
partial def typePos (sc : List DeclInfo) (ns : List String) (T : Term) : M Nat := do
  match ← declOf sc ns T with
  | .sort l => pure l
  | _ =>
    if (← get).cfg.sortsSyntactic then
      err s!"[D55] {T.pp ns} is written where a type is expected, but its declared type is not a sort (it is a type only by computation)"
    else pure 1

/-- A telescope of binder types, each in the scope of the earlier ones: the extended
scope, and the largest of their sorts. -/
partial def telescope (sc : List DeclInfo) (ns : List String) (hs : List Hint) (ds : List Term) :
    M (List DeclInfo × List String × Nat) := do
  let mut sc := sc
  let mut ns := ns
  let mut l := 0
  for (h, d) in hs.zip ds do
    l := max l (← typePos sc ns d)
    sc := d.asDecl :: sc
    ns := h.name :: ns
  pure (sc, ns, l)
end

/-- Check one definition and add it to the globals. -/
def checkDef (d : Def) : M Unit := do
  if (d.cod :: d.doms).any (Term.mentionsConst d.name) then
    err s!"{d.name} occurs in its own type"
  -- D48 (2): & only at the top of a declared type, never produced by computation
  if (← get).cfg.refTop && !((d.cod :: d.doms).all Term.refTopOk && d.body.refsOk) then
    err s!"[D48] {d.name}: & appears only as the whole declared type of a parameter, result or annotated term, never inside a type or produced by computation"
  -- D55: every type position, in the types and in the body
  discard (declOf [] [] (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body))
  if d.doms.isEmpty then
    -- a constant
    modify fun s => { s with env := #[{}], goal := none, recStack := [], refs := [] }
    let goal ← evalType d.cod
    let (v, T) ← eval true d.body goal     -- the goal: a hint for a constructor's parameters
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
  | ind (d : IndDecl)
deriving Inhabited

def Item.name : Item → String
  | .defn d => d.name
  | .ind d => d.name

/-- D36 (v1.7), with parameters (v2.0, D46): a field type is first-order data, read off
its term: `Nat`, `Unit`, `×` of first-order types, a parameter, or a declared inductive
type (the one being declared among them) applied to first-order types. No `Π`, no `&`,
no sort, no `Eq`: strict positivity in its simplest form. A parameter is instantiated
only at first-order types in a field, so a negative occurrence cannot hide behind one
(`Box(Π(x : Bad). Void)` is rejected). -/
partial def firstOrderTerm (np : Nat) : Term → M Bool
  | .nat | .unit => pure true
  | .place (.var j) => pure (j < np)
  | .tind m as => do
    discard (lookupInd m)
    as.allM (firstOrderTerm np)
  | _ => pure false

/-- Declare an inductive type (v2.0, D45/D46): a sort (`Prop` or `Type₀`), uniform
parameters, and zero or more constructors whose fields are first-order data or
parameters; fields may mention the type itself (recursive) or earlier types. The field
types are checked at generic parameters, in a frame of their own. -/
def checkInd (d : IndDecl) : M Unit := do
  let n := d.name
  if (← get).inds.any (·.name == n) then err s!"{n} is already declared"
  for (cn, _) in d.ctors do
    if (← get).inds.any (·.ctors.any (·.1 == cn)) || (d.ctors.filter (·.1 == cn)).length > 1 then
      err s!"{n}: the constructor name {cn} is already used (constructors are resolved by name)"
  if d.sort > 1 then err s!"{n}: an inductive type is in Prop or Type"
  modify fun s => { s with env := #[{}], inds := s.inds ++ [{ d with ctors := [] }] }
  -- D55: parameter and field types are type positions
  let (sc, ns, _) ← telescope [] [] (d.params.map (·.1)) (d.params.map (·.2))
  for (_, fields) in d.ctors do
    for (_, FT) in fields do discard (typePos sc ns FT)
  for (h, PT) in d.params do
    let A ← evalType PT
    pushBind h (some A) (← genericValue A)
  for (cn, fields) in d.ctors do
    for (fname, FT) in fields do
      let T ← evalType FT
      if T.typeHasRef then err s!"field {fname} of {cn}: no borrows inside data"
      if (← sortOf T) > 1 then err s!"field {fname} of {cn}: its type must be in Prop or Type"
      if (← get).cfg.positivity && !(← firstOrderTerm d.params.length FT) then
        err s!"field {fname} of {cn} : {FT.pp ((d.params.map (·.1.name)).reverse)}: fields are first-order data (inductive types, Nat, Unit, ×) or parameters, D36"
  modify fun s => { s with env := #[{}], inds := s.inds.map fun e => if e.name == n then d else e }

def checkItem : Item → M Unit
  | .defn d => checkDef d
  | .ind d => checkInd d

/-- The globals and inductive types after checking a list of items, from a start. -/
def globalsAfterFrom (cfg : Config) (start : List GDef × List IndDecl) (ds : List Item) :
    List GDef × List IndDecl := Id.run do
  let (g0, i0) := start
  let mut globals := g0
  let mut inds := i0
  for d in ds do
    let st : MState := { globals := globals, inds := inds, cfg := cfg }
    match (((checkItem d).run st).run.run #[]).1 with
    | .ok ((), st') => globals := st'.globals; inds := st'.inds
    | .error _ => pure ()
  pure (globals, inds)

/-- Check a list of items in order, with a fresh state per item apart from the
globals and inductive types accepted so far. The library (`Pair`, `False`, `True`, `And`)
is not built in (v2.1): it is the `Prelude` block (`Ochr/Prelude.lean`), whose
declarations come first in every program (`Ochr.Test.libOf`). -/
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

/-- The globals and inductive types after checking a list of items (the library among
them, first: `Ochr.Test.libOf`). -/
def globalsAfter (cfg : Config) (ds : List Item) : List GDef × List IndDecl :=
  globalsAfterFrom cfg ([], []) ds

/-- Run a machine computation from a given state (for unit tests). -/
def runM {α : Type} (x : M α) (st : MState) : Except String α :=
  match ((x.run st).run.run #[]).1 with
  | .ok (a, _) => .ok a
  | .error (.error m) => .error m
  | .error (.stuck _) => .error "stuck"

end Ochr
