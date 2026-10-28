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
  implBy : Option String := none   -- `implemented by "sym"` (K3): the compiler calls `sym`
deriving Inhabited

/-- A declaration's verdict. `undecided`: the checker ran out of fuel or past a depth limit,
so it does not know (neither accepted nor rejected; `Ochr/Catch.lean`). With more fuel an
undecided verdict may become decided, and a decided one never changes: exhaustion cannot be
caught below the verdict boundary, so it never becomes a decision. -/
inductive Verdict where
  | accepted
  | rejected (msg : String) (at? : Option Loc := none)   -- `at?`: where (the editor), if known
  | undecided (msg : String)
deriving Inhabited

def Verdict.ok : Verdict → Bool
  | .accepted => true
  | .rejected .. | .undecided _ => false

mutual
def Term.mentionsConst (n : String) : Term → Bool
  | .const m => m == n
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.mentionsConst n
  | .letIn _ t u | .seq t u | .cong t u
  | .ascribe t u => t.mentionsConst n || u.mentionsConst n
  | .matchNat _ z s => z.mentionsConst n || s.mentionsConst n
  | .pi _ ds c => Term.mentionsConstList n ds || c.mentionsConst n
  | .fix _ _ ds c _ b => Term.mentionsConstList n ds || c.mentionsConst n || b.mentionsConst n
  | .call f as _ => f.mentionsConst n || Term.mentionsConstList n as
  | .eq a b c | .id a b c => a.mentionsConst n || b.mentionsConst n || c.mentionsConst n
  | .ctor _ _ _ ps as => Term.mentionsConstList n ps || Term.mentionsConstList n as
  | .prim _ as | .tind _ as => Term.mentionsConstList n as
  | .matchInd _ _ as => Term.mentionsConstArms n as
  | _ => false
termination_by structural t => t

def Term.mentionsConstList (n : String) : List Term → Bool
  | [] => false
  | t :: ts => t.mentionsConst n || Term.mentionsConstList n ts
termination_by structural ts => ts

def Term.mentionsConstArms (n : String) : List (Hint × Term) → Bool
  | [] => false
  | (_, t) :: ts => t.mentionsConst n || Term.mentionsConstArms n ts
termination_by structural ts => ts
end

/-- [Def], [Const], [Ind-decl]: is `n` already a name of Σ? The declared types, their
constructors and the definitions share one namespace: the one the surface resolves an
identifier in (a type, then a constructor, then a definition: `Surface.resolve`), and the one
`Block.clashes` enforces between the blocks of an `ochr` command. A definition named like a
type or a constructor could never be called, and a second `def X` would be appended to Σ
behind the first, which every lookup still finds. -/
def declared (n : String) : M Bool := do
  let s ← get
  pure (s.globals.any (·.name == n) || s.inds.any fun e => e.name == n || e.ctors.any (·.1 == n))

/-- Check one definition and add it to the globals. -/
def checkDef (d : Def) : M Unit := do
  -- [Def], [Const]: f ∉ Σ
  if ← declared d.name then err s!"{d.name} is already declared"
  if (d.cod :: d.doms).any (Term.mentionsConst d.name) then
    err s!"{d.name} occurs in its own type"
  -- D48 (2): & only at the top of a declared type, never produced by computation
  if !((d.cod :: d.doms).all Term.refTopOk && d.body.refsOk) then
    err s!"[D48] {d.name}: & appears only as the whole declared type of a parameter, result or annotated term, never inside a type or produced by computation"
  -- D55: every type position, in the types and in the body
  discard (declOf true [] [] (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body))
  if d.doms.isEmpty then
    -- a constant
    modify fun s => { s with env := #[{}], goal := none, recStack := [], refs := [] }
    let goal ← evalType d.cod
    let (v, T) ← eval true d.body goal     -- the goal: a hint for a constructor's parameters
    located d.body <| unless (← match T with | some T => conv T goal | none => pure false) do
      err s!"the body of {d.name} has type {T.getD .bot}, but the goal is {goal}"
    repackCheck s!"{d.name} is defined as it" v goal
    let v ← if (← isPropV goal) then pure .proof else pure v
    modify fun s => { s with env := #[{}], globals := s.globals ++ [{ name := d.name, ty := goal, fn? := none, val := v }] }
  else
    let fixT := Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body
    let ty := Value.tPi [] (.pi d.hs d.doms d.cod)
    -- K2/K3: model code (native, or taking or returning an unsized value) never runs at runtime
    let model ← if d.implBy.isSome then pure true else modelSignature d.hs d.doms d.cod
    modify fun s => { s with globals := s.globals ++ [{ name := d.name, ty := ty, fn? := some fixT, val := .gfn d.name, model }] }
    if model then modify fun s => { s with modelDepth := s.modelDepth + 1 }
    checkFix (.gfn d.name) [] fixT
    if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }

/-- A program item: a definition, or an inductive type declaration. -/
inductive Item where
  | defn (d : Def)
  | ind (d : IndDecl)
deriving Inhabited

def Item.name : Item → String
  | .defn d => d.name
  | .ind d => d.name

mutual
/-- Does a term mention the inductive type `n` anywhere? -/
def Term.mentionsType (n : String) : Term → Bool
  | .tind m as => m == n || Term.mentionsTypeList n as
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.mentionsType n
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.mentionsType n || u.mentionsType n
  | .matchNat _ z s => z.mentionsType n || s.mentionsType n
  | .pi _ ds c => Term.mentionsTypeList n ds || c.mentionsType n
  | .fix _ _ ds c _ b => Term.mentionsTypeList n ds || c.mentionsType n || b.mentionsType n
  | .call f as _ => f.mentionsType n || Term.mentionsTypeList n as
  | .eq a b c | .id a b c => a.mentionsType n || b.mentionsType n || c.mentionsType n
  | .ctor t _ _ ps as => t == n || Term.mentionsTypeList n ps || Term.mentionsTypeList n as
  | .prim _ as => Term.mentionsTypeList n as
  | .matchInd _ t as => t == n || Term.mentionsTypeArms n as
  | _ => false
termination_by structural t => t

def Term.mentionsTypeList (n : String) : List Term → Bool
  | [] => false
  | t :: ts => t.mentionsType n || Term.mentionsTypeList n ts
termination_by structural ts => ts

def Term.mentionsTypeArms (n : String) : List (Hint × Term) → Bool
  | [] => false
  | (_, t) :: ts => t.mentionsType n || Term.mentionsTypeArms n ts
termination_by structural ts => ts
end

mutual
/-- `paramNestable` with fuel: each step, into a field type, an argument or another
declaration, spends one unit, and running out is an error (not an answer). -/
def paramNestableF (fuel : Nat) (d : IndDecl) (i : Nat) : M Bool :=
  match fuel with
  | 0 => err "out of fuel"   -- FUEL-OUTCOME: the out-of-fuel outcome once no-fallbacks lands
  | fuel + 1 => do
    let np := d.params.length
    d.ctors.allM fun (_, fields) =>
      fields.allM fun (_, FT) => paramNestableGo fuel d (np - 1 - i) FT
termination_by structural fuel

/-- The walk of a field type of `d` for the parameter at index `v`. -/
def paramNestableGo (fuel : Nat) (d : IndDecl) (v : Nat) (t : Term) : M Bool :=
  match fuel with
  | 0 => err "out of fuel"   -- FUEL-OUTCOME
  | fuel + 1 =>
    match t with
    | .place (.var _) => pure true
    | .nat | .unit => pure true
    | .tind m as => paramNestableArgs fuel d v m 0 as
    | t => pure !(t.freeVars.contains v)
termination_by structural fuel

/-- The arguments of `m(…)` in a field type of `d`, the first at `m`'s parameter `idx`. -/
def paramNestableArgs (fuel : Nat) (d : IndDecl) (v : Nat) (m : String) (idx : Nat) (as : List Term) :
    M Bool :=
  match fuel with
  | 0 => err "out of fuel"   -- FUEL-OUTCOME
  | fuel + 1 =>
    match as with
    | [] => pure true
    | a :: as => do
      let ok ← (do
        if !(a.freeVars.contains v) then return true
        if m == d.name then return (← paramNestableGo fuel d v a)
        let dm ← lookupInd m
        let r1 ← paramNestableF fuel dm idx
        let r2 ← paramNestableGo fuel d v a
        pure (r1 && r2) : M Bool)
      if ok then paramNestableArgs fuel d v m (idx + 1) as else pure false
termination_by structural fuel
end

/-- K4's nesting condition: parameter `i` of `d` occurs in `d`'s field types only where the
type it stands for occurs positively in the simplest form: as a field type itself, or as an
argument of an inductive at one of that inductive's nestable parameters (the type itself
counts as nestable at a uniform recursive use). A parameter passed to a type function
(`Neg(A)`), or occurring anywhere else, is not nestable: a later declaration may not put
the type it declares there, since the function may use it negatively. The walk spends from
the checker's fuel budget (`paramNestableF`). -/
def paramNestable (d : IndDecl) (i : Nat) : M Bool := do
  paramNestableF (← get).fuel d i

mutual
/-- K4's nesting condition, for its message: an occurrence of the type being declared `n` at
a parameter of an inductive that is not nestable there (`paramNestable`), as the inner
inductive and the parameter's name. -/
def nestViolation (n : String) : Term → M (Option (String × String))
  | .tind m as => do
    let dm ← lookupInd m
    nestViolationArgs n m dm 0 as
  | _ => pure none
termination_by structural t => t

/-- The arguments of `m(…)`, the first at `m`'s parameter `i`: the first violation. -/
def nestViolationArgs (n m : String) (dm : IndDecl) (i : Nat) : List Term → M (Option (String × String))
  | [] => pure none
  | a :: as => do
    let nestable ← paramNestable dm i
    if m != n && a.mentionsType n && !nestable then
      return some (m, (dm.params[i]!).1.name)
    if let some r ← nestViolation n a then return some r
    nestViolationArgs n m dm (i + 1) as
termination_by structural as => as
end

mutual
/-- D36 (v1.7), with parameters (v2.0, D46), K4 and dependent fields (D64): a field type of
the inductive `n` (with `np` parameters and, in this constructor, `k` fields) is first-order
data, read off its term: `Nat`, `Unit`, a parameter, a declared inductive type (the one being
declared among them) applied to first-order types, or (K4) a call of an earlier type function
(its declared codomain is a sort) whose arguments are parameters, fields (data: D64's earlier
fields), numerals or first-order types, none mentioning `n`. No `Π`, no `&`, no sort, no
`Eq`: strict positivity in its simplest form. A parameter is instantiated only at first-order
types in a field, so a negative occurrence cannot hide behind one (`Box(Π(x : Bad). Void)` is
rejected); and a type being declared may be nested only at a parameter the inner inductive
does not pass to a type function (K4's nesting condition: `NBox(A) := MkNBox(f : Neg(A))`,
then `Bad := MkBad(b : NBox(Bad))`, is the D36 attack again). -/
def firstOrderTerm (n : String) (np k : Nat) : Term → M Bool
  | .nat | .unit => pure true
  | .place (.var j) => pure (j < np)
  | .tind m as => do
    let dm ← lookupInd m
    firstOrderArgs n np k m dm 0 as
  | .call (.const f) as _ => do
    let some g := (← get).globals.find? (·.name == f) | return false
    let .tPi _ (.pi _ _ cod) := g.ty | return false
    unless cod matches .sort _ do return false
    firstOrderCallArgs n np k as
  | _ => pure false
termination_by structural t => t

/-- The arguments of an inductive `m(…)` in a field type, the first at `m`'s parameter `i`. -/
def firstOrderArgs (n : String) (np k : Nat) (m : String) (dm : IndDecl) (i : Nat) :
    List Term → M Bool
  | [] => pure true
  | a :: as => do
    let ok ← (do
      unless ← firstOrderTerm n np k a do return false
      -- K4's nesting condition
      if m != n && a.mentionsType n then paramNestable dm i else pure true
      : M Bool)
    if ok then firstOrderArgs n np k m dm (i + 1) as else pure false
termination_by structural as => as

/-- The arguments of a call of a type function in a field type (K4). -/
def firstOrderCallArgs (n : String) (np k : Nat) : List Term → M Bool
  | [] => pure true
  | a :: as => do
    let ok ← (do
      if a.mentionsType n then return false
      match a with
      | .place (.var j) => pure (j < np + k)      -- a parameter, or a field (data)
      | .zero | .succ _ => pure true
      | _ => firstOrderTerm n np k a
      : M Bool)
    if ok then firstOrderCallArgs n np k as else pure false
termination_by structural as => as
end

/-- Declare an inductive type (v2.0, D45/D46): a sort (`Prop` or `Type₀`), uniform
parameters, and zero or more constructors whose fields are first-order data or
parameters; fields may mention the type itself (recursive) or earlier types. D64 ([Ind]):
each constructor's field types are a telescope, a field's type mentioning the parameters
and the earlier fields only, checked at generic parameters and generic earlier fields
(`fieldTele`). -/
def checkInd (d : IndDecl) : M Unit := do
  let n := d.name
  -- [Ind-decl]: D, C₁, …, Cₘ ∉ Σ, pairwise distinct
  if ← declared n then err s!"{n} is already declared"
  for (cn, _) in d.ctors do
    if (← declared cn) || cn == n || (d.ctors.filter (·.1 == cn)).length > 1 then
      err s!"{n}: the constructor name {cn} is already used (constructors are resolved by name)"
  if d.sort > 1 then err s!"{n}: an inductive type is in Prop or Type"
  modify fun s => { s with env := #[{}], inds := s.inds ++ [{ d with ctors := [] }] }
  let np := d.params.length
  let pnames := (d.params.map (·.1.name)).reverse
  -- D64 [Ind]: a field's type mentions only the parameters and the earlier fields
  fire .IndDecl fun _ => s!"{n}: {d.params.length} parameters, {d.ctors.length} constructors, fields a telescope"
  for ((cn, fields), c) in d.ctors.zipIdx do
    for ((fname, FT), i) in fields.zipIdx do
      let late := (d.fieldRefs c FT).filter (· ≥ i)
      unless late.isEmpty do
        let names := late.map fun j => (fields[j]!).1
        err s!"[Ind] field {fname} of {cn}: its type mentions {", ".intercalate names}, which is not an earlier field (a field's type may mention the parameters and the fields before it)"
  -- D55: parameter and field types are type positions (the fields are in scope, as data)
  let (sc, ns, _) ← telescope true [] [] (d.params.map (·.1)) (d.params.map (·.2))
  for (_, fields) in d.ctors do
    let sc' := sc ++ fields.reverse.map fun _ => DeclInfo.other
    let ns' := ns ++ fields.reverse.map (·.1)
    for (_, FT) in fields do discard (typePos true sc' ns' FT)
  let mut ps := #[]
  for (h, PT) in d.params do
    let A ← evalType PT
    let v ← genericValue A
    pushBind h (some A) v
    ps := ps.push v
  for ((cn, fields), c) in d.ctors.zipIdx do
    let names := pnames ++ fields.reverse.map (·.1)
    -- the field types at generic parameters, each at generic values of the earlier fields
    discard <| fieldTele d ps.toList c fun j T => do
      let (fname, FT) := fields[j]!
      if T.typeHasRef then err s!"field {fname} of {cn}: no borrows inside data"
      if (← sortOf T) > 1 then err s!"field {fname} of {cn}: its type must be in Prop or Type"
      -- K4's nesting condition
      if let some (m, a) ← nestViolation n FT then
        err s!"field {fname} of {cn} : {FT.pp names}: {n} occurs at the parameter {a} of {m}, which {m} passes to a type function (one may use its argument negatively): not strictly positive (K4, D36)"
      -- D36, K4
      if !(← firstOrderTerm n np fields.length FT) then
        err s!"field {fname} of {cn} : {FT.pp names}: fields are first-order data (inductive types, Nat, Unit, ×, earlier type functions) or parameters, D36"
      -- K4: a type function's result is first-order data too (at the generic telescope)
      if (FT matches .call ..) && (T matches .tPi .. | .sort _ | .tEq .. | .tRef _) then
        err s!"field {fname} of {cn} : {FT.pp names} computes to {T}, which is not first-order data, D36"
      -- D53: a type declared `copy` has copy fields (the type itself counts as one)
      let isSelf := match T with | .tInd m _ => m == n | _ => false
      if d.copy && !isSelf && !(← isCopyType T) then
        err s!"[D53] {n} is declared copy, but the field {fname} of {cn} has the type {T}, which is not a copy type"
      genericValue T
  modify fun s => { s with env := #[{}], inds := s.inds.map fun e => if e.name == n then d else e }

def checkItem : Item → M Unit
  | .defn d => checkDef d
  | .ind d => checkInd d

/-- Does the item mention the global or inductive type `n` (in a type, a field or a body)? -/
def Item.mentions (n : String) : Item → Bool
  | .defn d => (d.body :: d.cod :: d.doms).any fun t => t.mentionsConst n || t.mentionsType n
  | .ind d => (d.params.map (·.2) ++ d.ctors.flatMap (·.2.map (·.2))).any fun t =>
      t.mentionsConst n || t.mentionsType n

/-- The globals and inductive types after checking a list of items, from a start. -/
def globalsAfterFrom (cfg : Config) (start : List GDef × List IndDecl) (ds : List Item) :
    List GDef × List IndDecl := Id.run do
  let (g0, i0) := start
  let mut globals := g0
  let mut inds := i0
  for d in ds do
    let st : MState := { globals := globals, inds := inds, cfg := cfg }
    -- the verdict boundary: an item not accepted adds nothing to Σ
    if let .ok () st' := (runMachine (checkItem d) st 2000000).1 then
      globals := st'.globals; inds := st'.inds
  pure (globals, inds)

/-- Check a list of items in order, with a fresh state per item apart from the
globals and inductive types accepted so far. The library (`Pair`, `False`, `True`, `And`)
is not built in (v2.1): it is the `Prelude` block (`Ochr/Prelude.lean`), whose
declarations come first in every program (`Ochr.Test.libOf`). The result has one verdict
per item, in order; `locsOf i` is where item `i`'s terms are written (the editor). -/
def checkDefs (cfg : Config) (ds : List Item) (fuel : Nat := 2000000)
    (locsOf : Nat → Locs := fun _ => {}) : List (String × Verdict × Array LogEntry) := Id.run do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  let mut undecided : List String := []
  let mut out := #[]
  for (d, i) in ds.zipIdx do
    -- an item that mentions an undecided one is undecided too: without the earlier item the
    -- checker cannot know its verdict (left out of Σ, it would be rejected for a missing name,
    -- a decision made by exhaustion, which more fuel would change)
    if let some n := undecided.find? (d.mentions ·) then
      undecided := d.name :: undecided
      out := out.push (d.name, .undecided s!"it mentions {n}, which is undecided", #[])
      continue
    let st : MState := { globals := globals, inds := inds, cfg := cfg, locs := locsOf i }
    -- the verdict boundary: the one place a failure becomes something else (a verdict)
    let (r, _, tr) := runMachine (checkItem d) st fuel
    match r with
    | .ok () st' =>
      globals := st'.globals
      inds := st'.inds
      out := out.push (d.name, .accepted, tr)
    | .fail (.error m l) => out := out.push (d.name, .rejected m l, tr)
    | .fail (.stuck _) => out := out.push (d.name, .rejected "internal: stuck escaped to the top", tr)
    | .exhausted m =>
      undecided := d.name :: undecided
      out := out.push (d.name, .undecided m, tr)
  pure out.toList

/-- The globals and inductive types after checking a list of items (the library among
them, first: `Ochr.Test.libOf`). -/
def globalsAfter (cfg : Config) (ds : List Item) : List GDef × List IndDecl :=
  globalsAfterFrom cfg ([], []) ds

/-- Run a machine computation from a given state (for unit tests). -/
def runM {α : Type} (x : M α) (st : MState) (fuel : Nat := 2000000) : Except String α :=
  match (runMachine x st fuel).1 with
  | .ok a _ => .ok a
  | .fail (.error m _) => .error m
  | .fail (.stuck _) => .error "stuck"
  | .exhausted m => .error s!"undecided: {m}"

end Ochr
