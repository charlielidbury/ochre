import Ochr.Check

/-!
# Surface syntax: named terms and their resolution to de Bruijn terms

The `ochr` command (in `Ochr/Notation.lean`) parses paper-style programs into the
named `STerm` below; `resolve` turns them into core `Term`s. Resolution decides:
* `&t` is the borrow type in a *type position* (binder and result types, the type
  argument of `Id`/`Eq`, Π domains and codomain, `×`, `→`, ascriptions) and a borrow
  `&p` elsewhere;
* a pattern variable `y` in `match p { …, S y => u }` is the sub-place `p.1`
  (RULES §1), so it is substituted rather than bound;
* the name of the definition being checked, inside its own body, is its `self` binder;
* numerals are `S … Z`; `cong S h` takes `S` as the function `λ(n : Nat) : Nat => S n`.
-/

namespace Ochr.Surface

inductive STerm where
  | ident (x : String)
  | num (n : Nat)
  | app (f : String) (args : List STerm)        -- juxtaposition, builtins only: S t, Id A t u, Eq A t u, cong f h
  | call (f : STerm) (args : List STerm)        -- f(a₁, …, aₙ)
  | ctorP (c : String) (ps : List STerm) (args : List STerm)   -- C[ā](t̄): parameters written (core C(ā; t̄))
  | deref (t : STerm)
  | proj (i : Nat) (t : STerm)                   -- t.1, t.2
  | amp (t : STerm)
  | assign (p t : STerm)
  | letIn (x : String) (ty : Option STerm) (t u : STerm)
  | seq (t u : STerm)
  | matchGen (scrut : STerm) (arms : List (String × List String × STerm))   -- C(x̄) => t
  | pi (bs : List (String × STerm)) (cod : STerm)
  | arrow (A B : STerm)
  | fix (f : String) (bs : List (String × STerm)) (ret : STerm) (dec : Option String) (body : STerm)
  | unitLit
  | pair (a b : STerm)
  | andI (a b : STerm)                             -- ⟨h, k⟩: notation for And's Intro(h, k)
  | top                                          -- ⊤: notation for True
  | and (P Q : STerm)                            -- P ∧ Q: notation for And(P, Q)
  | prod (A B : STerm)
  | ascribe (t A : STerm)
  | sort (l : Nat)
deriving Inhabited, Repr

structure SDecl where
  name : String
  params : List (String × STerm) := []
  ret : STerm := .unitLit
  body : STerm := .unitLit
  dec : Option String := none
  ind? : Option (List (String × List (String × STerm))) := none   -- an inductive declaration
  indParams : List (String × STerm) := []                         -- its uniform parameters (v2.0)
  indSort : Option STerm := none                                  -- its sort (default Type₀)
  expectAccept : Bool
deriving Inhabited, Repr

abbrev Program := List SDecl

/-- An `ochr` block: a name, the blocks it `uses`, and its own declarations. A block's
program, when checked, is the declarations its used blocks export (`Ochr.Test.libOf`)
followed by its own; each block is checked afresh wherever it is used (no caching). -/
inductive Block where
  | mk (name : String) (uses : List Block) (decls : Program)
deriving Inhabited

def Block.name : Block → String
  | .mk n _ _ => n
def Block.uses : Block → List Block
  | .mk _ us _ => us
def Block.decls : Block → Program
  | .mk _ _ ds => ds

/-- The blocks `b` uses, transitively, each once (by name), a block after the blocks it
uses. `b` itself is not included. -/
partial def Block.closure (b : Block) : List Block :=
  b.uses.foldl (fun acc u => add acc u) []
where
  add (acc : List Block) (u : Block) : List Block :=
    if acc.any (·.name == u.name) then acc
    else
      let acc := u.uses.foldl add acc
      if acc.any (·.name == u.name) then acc else acc ++ [u]

/-- The names a declaration introduces into a block's flat namespace: its own name and, for
an inductive type, its constructors'. -/
def SDecl.introduces (d : SDecl) : List String :=
  d.name :: (d.ind?.getD []).map (·.1)

/-- Every identifier a surface term mentions (constants, types, constructors, variables). -/
partial def STerm.idents : STerm → List String
  | .ident x => [x]
  | .num _ | .unitLit | .top | .sort _ => []
  | .app _ as => as.flatMap STerm.idents
  | .call f as => f.idents ++ as.flatMap STerm.idents
  | .ctorP c ps as => c :: (ps ++ as).flatMap STerm.idents
  | .deref t | .proj _ t | .amp t => t.idents
  | .assign a b | .seq a b | .pair a b | .andI a b | .and a b | .prod a b | .ascribe a b
  | .arrow a b => a.idents ++ b.idents
  | .letIn _ T t u => (T.map STerm.idents).getD [] ++ t.idents ++ u.idents
  | .matchGen p arms => p.idents ++ arms.flatMap fun (c, _, t) => c :: t.idents
  | .pi bs c => bs.flatMap (·.2.idents) ++ c.idents
  | .fix _ bs r _ b => bs.flatMap (·.2.idents) ++ r.idents ++ b.idents

/-- The names a declaration mentions (a superset of the constants it depends on). -/
def SDecl.mentions (d : SDecl) : List String :=
  d.params.flatMap (·.2.idents) ++ d.ret.idents ++ d.body.idents ++
    d.indParams.flatMap (·.2.idents) ++ (d.indSort.map STerm.idents).getD [] ++
    (d.ind?.getD []).flatMap fun (_, fs) => fs.flatMap (·.2.idents)

/-- Name clashes in `b`'s flat namespace: a name `b` declares that a block it uses (other
than by `reject`) also declares, or one name declared by two of the blocks it uses. The
`ochr` command reports these as an error when the block is elaborated. -/
def Block.clashes (b : Block) (implicit : List Block := []) : List String := Id.run do
  let mut seen : List (String × String) := []     -- name ↦ the block declaring it
  let mut out := []
  let used := implicit ++ b.closure.filter fun u => !implicit.any (·.name == u.name)
  for u in used do
    for d in u.decls.filter (·.expectAccept) do
      for n in d.introduces do
        match seen.lookup n with
        | some home => if home != u.name then out := out ++ [s!"{n} is declared by both {home} and {u.name}, which {b.name} uses"]
        | none => seen := seen ++ [(n, u.name)]
  let own := b.decls.map (·.name)
  for n in own.eraseDups do
    if own.count n > 1 then out := out ++ [s!"{b.name} declares {n} more than once"]
  for d in b.decls do
    for n in d.introduces do
      if let some home := seen.lookup n then
        out := out ++ [s!"{b.name} declares {n}, which {home} (used by {b.name}) already declares; the declarations of a block and the blocks it uses share one namespace"]
  pure out

/-- Resolution context: innermost first. Aliases (pattern variables) do not count as
binders; their place is shifted by the binders pushed since. -/
inductive Entry where
  | bound (x : String)
  | alias (x : String) (p : Place)

abbrev Ctx := List Entry

def shiftPlace (k : Nat) (p : Place) : Place := p.mapRoot fun i => .var (i + k)

def lookup (ctx : Ctx) (x : String) : Option Place := go ctx 0
where
  go : Ctx → Nat → Option Place
    | [], _ => none
    | .bound y :: rest, k => if y == x then some (.var k) else go rest (k + 1)
    | .alias y p :: rest, k => if y == x then some (shiftPlace k p) else go rest k

/-- The declared inductive types of the program: constructor name ↦ (type, index, field
names), and the type names. -/
structure Tables where
  ctors : List (String × String × Nat × List String) := []
  types : List String := []

abbrev R := ReaderT Tables (Except String)

/-- The constructors and types a program declares. The library's (`Pair`, `False`,
`True`, `And`) are among them: the `Prelude` block's declarations come first in every
program (v2.1). -/
def Tables.ofProgram (p : List SDecl) : Tables :=
  p.foldl (fun t d => match d.ind? with
    | some cs =>
      { ctors := t.ctors ++ (cs.zipIdx.map fun ((cn, fs), i) => (cn, d.name, i, fs.map (·.1))),
        types := t.types ++ [d.name] }
    | none => t) {}

def builtinNames : List String := ["Nat", "Unit", "Z", "refl", "S", "Id", "Eq", "cong"]

partial def toPlace (ctx : Ctx) : STerm → R Place
  | .ident x => match lookup ctx x with
    | some p => pure p
    | none => throw s!"{x} is not a place (not a local variable)"
  | .deref t => return .deref (← toPlace ctx t)
  | .proj 1 t => return .fst (← toPlace ctx t)
  | .proj 2 t => return .snd (← toPlace ctx t)
  | t => throw s!"not a place: {repr t}"

def isPlace (ctx : Ctx) (t : STerm) : Bool := ((toPlace ctx t).run {}).toOption.isSome

/-- The position of the parameter named by `by x`. -/
def decIndex (bs : List (String × STerm)) : Option String → R (Option Nat)
  | none => pure none
  | some x => match bs.findIdx? (·.1 == x) with
    | some j => pure (some j)
    | none => throw s!"`by {x}`: {x} is not a parameter"

def succFn : Term :=
  .fix ⟨"_"⟩ [⟨"n"⟩] [.nat] .nat none (.succ (.place (.var 0)))

mutual
partial def resolve (ctx : Ctx) (ty : Bool) (t : STerm) : R Term := do
  match t with
  | .ident x =>
    match lookup ctx x with
    | some p => pure (.place p)
    | none =>
      let tb ← read
      if tb.types.contains x then return .tind x []
      if let some (_, ty, i, fs) := tb.ctors.find? (·.1 == x) then
        if fs.isEmpty then return .ctor ty i ⟨x⟩ [] []
        throw s!"constructor {x} takes {fs.length} fields"
      match x with
      | "Nat" => pure .nat
      | "Unit" => pure .unit
      | "Z" => pure .zero
      | "refl" => pure (.ctor "True" 0 ⟨"I"⟩ [] [])      -- notation for True's constructor (v2.0)
      | "S" => pure succFn
      | _ => pure (.const x)
  | .num n => pure (Term.ofNat n)
  | .app "S" [a] => return .succ (← resolve ctx false a)
  | .app "Id" [A, a, b] => return .id (← resolve ctx true A) (← resolve ctx false a) (← resolve ctx false b)
  | .app "Eq" [A, a, b] => return .eq (← resolve ctx true A) (← resolve ctx false a) (← resolve ctx false b)
  | .app "cong" [f, h] => return .cong (← resolve ctx false f) (← resolve ctx false h)

  | .app "trans" [h, k] => return .prim "trans" [← resolve ctx false h, ← resolve ctx false k]
  | .app "symm" [h] => return .prim "symm" [← resolve ctx false h]
  | .app f as => throw s!"{f} applied by juxtaposition to {as.length} arguments (calls are written f(a, …))"
  | .call (.ident "J") [A, a, b, P, h, u] =>
    if (lookup ctx "J").isSome then return .call (← resolve ctx false (.ident "J")) (← [A, a, b, P, h, u].mapM (resolve ctx false)) false
    return .prim "J" [← resolve ctx true A, ← resolve ctx false a, ← resolve ctx false b,
                      ← resolve ctx false P, ← resolve ctx false h, ← resolve ctx false u]
  | .call (.ident "clone") [p] =>      -- D53 prototype: a built-in copy of a place
    if (lookup ctx "clone").isSome then return .call (← resolve ctx false (.ident "clone")) [← resolve ctx false p] false
    return .prim "clone" [← resolve ctx false p]
  | .call (.ident c) as =>
    let tb ← read
    if (lookup ctx c).isNone && tb.types.contains c then
      return .tind c (← as.mapM (resolve ctx true))       -- D(ā): the parameters are types
    match (if (lookup ctx c).isSome then none else tb.ctors.find? (·.1 == c)) with
    | some (_, ty, i, fs) =>
      if fs.length != as.length then throw s!"constructor {c} takes {fs.length} fields, given {as.length}"
      return .ctor ty i ⟨c⟩ [] (← as.mapM (resolve ctx false))
    | none => return .call (← resolve ctx false (.ident c)) (← as.mapM (resolve ctx false)) false
  | .call f as => return .call (← resolve ctx false f) (← as.mapM (resolve ctx false)) false
  | .ctorP c ps as =>
    let tb ← read
    let some (_, ty, i, fs) := tb.ctors.find? (·.1 == c) | throw s!"{c} is not a constructor"
    if fs.length != as.length then throw s!"constructor {c} takes {fs.length} fields, given {as.length}"
    return .ctor ty i ⟨c⟩ (← ps.mapM (resolve ctx true)) (← as.mapM (resolve ctx false))
  | .deref _ => return .place (← toPlace ctx t)
  | .proj i a =>
    if isPlace ctx t then return .place (← toPlace ctx t)
    else if i == 1 then return .fst (← resolve ctx false a) else return .snd (← resolve ctx false a)
  | .amp a =>
    if ty then return .ref (← resolve ctx true a)
    else return .borrow (← toPlace ctx a)
  | .assign p a => return .assign (← toPlace ctx p) (← resolve ctx false a)
  | .letIn x A a u =>
    let a' ← resolve ctx false a
    let a' ← match A with
      | some A => pure (.ascribe a' (← resolve ctx true A))
      | none => pure a'
    return .letIn ⟨x⟩ a' (← resolve (.bound x :: ctx) ty u)
  | .seq a b => return .seq (← resolve ctx false a) (← resolve ctx ty b)
  | .matchGen sc arms =>
    let p ← toPlace ctx sc
    match arms with
    | [("Z", [], z), ("S", [y], s)] =>
      let ctxS := if y == "_" then ctx else .alias y (.fst p) :: ctx
      return .matchNat p (← resolve ctx ty z) (← resolve ctxS ty s)
    | [] => return .matchInd p "" []      -- no arms (v2.0): the scrutinee's type has no constructors
    | (c0, _, _) :: _ =>
      let tb ← read
      let some (_, tyName, _, _) := tb.ctors.find? (·.1 == c0)
        | throw s!"{c0} is not a constructor (Nat's are written Z => …, S y => …, in that order)"
      let cs := tb.ctors.filter (·.2.1 == tyName)
      let mut out := #[]
      for (cn, _, i, fs) in cs do
        let some (_, vars, body) := arms.find? (·.1 == cn) | throw s!"match on {tyName}: no arm for {cn}"
        if vars.length != fs.length then throw s!"pattern {cn} needs {fs.length} variables"
        -- pattern variables are the sub-places p.fᵢ (RULES §1, D32), naming their constructor
        let ctxA := (vars.zip (fs.zipIdx)).foldl (fun acc (v, (fname, j)) =>
          if v == "_" then acc else .alias v (.field ⟨tyName, i, j, fname⟩ p) :: acc) ctx
        out := out.push (Hint.mk cn, ← resolve ctxA ty body)
      if arms.length != cs.length then throw s!"match on {tyName}: {arms.length} arms for {cs.length} constructors"
      return .matchInd p tyName out.toList
  | .pi bs cod =>
    let (ctx', hs, ds) ← binders ctx bs
    return .pi hs ds (← resolve ctx' true cod)
  | .arrow A B => return .pi [⟨"_"⟩] [← resolve ctx true A] (← resolve (.bound "_" :: ctx) true B)
  | .fix f bs ret dec body =>
    let (ctx', hs, ds) ← binders ctx bs
    let ret' ← resolve ctx' true ret
    let bodyCtx := (bs.reverse.map fun (x, _) => Entry.bound x) ++ (.bound f :: ctx)
    return .fix ⟨f⟩ hs ds ret' (← decIndex bs dec) (← resolve bodyCtx false body)
  | .unitLit => pure .tt
  | .pair a b =>      -- `(a, b)`: notation for the library's `Mk(a, b)` of `Pair` (D52)
    return .ctor "Pair" 0 ⟨"Mk"⟩ [] [← resolve ctx false a, ← resolve ctx false b]
  | .andI a b => return .ctor "And" 0 ⟨"Intro"⟩ [] [← resolve ctx false a, ← resolve ctx false b]
  | .top => pure (.tind "True" [])
  | .and P Q => return .tind "And" [← resolve ctx true P, ← resolve ctx true Q]
  | .prod A B => return .tind "Pair" [← resolve ctx true A, ← resolve ctx true B]   -- `A × B` (D52)
  | .ascribe a A => return .ascribe (← resolve ctx false a) (← resolve ctx true A)
  | .sort l => pure (.sort l)

/-- Resolve a telescope; each binder's type sees the earlier binders. -/
partial def binders (ctx : Ctx) : List (String × STerm) → R (Ctx × List Hint × List Term)
  | [] => pure (ctx, [], [])
  | (x, A) :: bs => do
    let A' ← resolve ctx true A
    let (ctx', hs, ds) ← binders (.bound x :: ctx) bs
    pure (ctx', ⟨x⟩ :: hs, A' :: ds)
end

/-- A top-level declaration becomes an `Item`. Inside a definition's body its own name
is its `self` binder (whose value is the global function). -/
def resolveDecl (d : SDecl) : R Item := do
  if let some cs := d.ind? then
    -- the parameters are a telescope; the field types are in their scope (v2.0, D46)
    let (ctx', hs, ps) ← binders [] d.indParams
    let cs' ← cs.mapM fun (cn, fs) => do
      pure (cn, ← fs.mapM fun (fname, FT) => do pure (fname, ← resolve ctx' true FT))
    let sort ← match d.indSort with
      | none | some (.sort 1) => pure 1
      | some (.sort 0) => pure 0
      | some _ => throw s!"{d.name}: an inductive type is in Prop or Type"
    return .ind { name := d.name, params := hs.zip ps, sort := sort, ctors := cs' }
  let (ctx', hs, ds) ← binders [] d.params
  let cod ← resolve ctx' true d.ret
  let body ←
    if d.params.isEmpty then resolve [] false d.body
    else resolve ((d.params.reverse.map fun (x, _) => Entry.bound x) ++ [.bound d.name]) false d.body
  pure (.defn { name := d.name, hs := hs, doms := ds, cod := cod, dec := ← decIndex d.params d.dec, body := body })

/-- Resolve a whole program's declarations with its constructor table. -/
def resolveProgram (p : List SDecl) (d : SDecl) : Except String Item :=
  (resolveDecl d).run (Tables.ofProgram p)

end Ochr.Surface
