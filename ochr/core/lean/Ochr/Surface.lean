import Ochr.Check

/-!
# Surface syntax: named terms and their resolution to de Bruijn terms

The `ochr` command (in `Ochr/Notation.lean`) parses paper-style programs into the
named `STerm` below; `resolve` turns them into core `Term`s. Resolution decides:
* `&t` is the borrow type in a *type position* (binder and result types, the type
  argument of `Id`/`Eq`, Π domains and codomain, `×`, `→`, ascriptions) and a borrow
  `&p` elsewhere;
* a pattern variable `y` in `match p { … | S y => u }` is the sub-place `p.1`
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
  | deref (t : STerm)
  | proj (i : Nat) (t : STerm)                   -- t.1, t.2
  | amp (t : STerm)
  | assign (p t : STerm)
  | letIn (x : String) (ty : Option STerm) (t u : STerm)
  | seq (t u : STerm)
  | matchNat (scrut z : STerm) (y : String) (s : STerm)
  | pi (bs : List (String × STerm)) (cod : STerm)
  | arrow (A B : STerm)
  | fix (f : String) (bs : List (String × STerm)) (ret body : STerm)
  | unitLit
  | pair (a b : STerm)
  | andI (a b : STerm)
  | top
  | and (P Q : STerm)
  | prod (A B : STerm)
  | ascribe (t A : STerm)
  | sort (l : Nat)
deriving Inhabited, Repr

structure SDecl where
  name : String
  params : List (String × STerm)
  ret : STerm
  body : STerm
  expectAccept : Bool
deriving Inhabited, Repr

abbrev Program := List SDecl

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

abbrev R := Except String

def builtinNames : List String := ["Nat", "Unit", "Z", "refl", "S", "Id", "Eq", "cong"]

partial def toPlace (ctx : Ctx) : STerm → R Place
  | .ident x => match lookup ctx x with
    | some p => pure p
    | none => throw s!"{x} is not a place (not a local variable)"
  | .deref t => return .deref (← toPlace ctx t)
  | .proj 1 t => return .fst (← toPlace ctx t)
  | .proj 2 t => return .snd (← toPlace ctx t)
  | t => throw s!"not a place: {repr t}"

def isPlace (ctx : Ctx) (t : STerm) : Bool := (toPlace ctx t).toOption.isSome

def succFn : Term :=
  .fix ⟨"_"⟩ [⟨"n"⟩] [.nat] .nat (.succ (.place (.var 0)))

mutual
partial def resolve (ctx : Ctx) (ty : Bool) (t : STerm) : R Term := do
  match t with
  | .ident x =>
    match lookup ctx x with
    | some p => pure (.place p)
    | none => match x with
      | "Nat" => pure .nat
      | "Unit" => pure .unit
      | "Z" => pure .zero
      | "refl" => pure .refl
      | "S" => pure succFn
      | _ => pure (.const x)
  | .num n => pure (Term.ofNat n)
  | .app "S" [a] => return .succ (← resolve ctx false a)
  | .app "Id" [A, a, b] => return .id (← resolve ctx true A) (← resolve ctx false a) (← resolve ctx false b)
  | .app "Eq" [A, a, b] => return .eq (← resolve ctx true A) (← resolve ctx false a) (← resolve ctx false b)
  | .app "cong" [f, h] => return .cong (← resolve ctx false f) (← resolve ctx false h)
  | .app "J" [A, P, h, u] =>
    return .prim "J" [← resolve ctx true A, ← resolve ctx false P, ← resolve ctx false h, ← resolve ctx false u]
  | .app "trans" [h, k] => return .prim "trans" [← resolve ctx false h, ← resolve ctx false k]
  | .app "symm" [h] => return .prim "symm" [← resolve ctx false h]
  | .app f as => throw s!"{f} applied by juxtaposition to {as.length} arguments (calls are written f(a, …))"
  | .call f as => return .call (← resolve ctx false f) (← as.mapM (resolve ctx false)) false
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
  | .matchNat sc z y s =>
    let p ← toPlace ctx sc
    let ctxS := if y == "_" then ctx else .alias y (.fst p) :: ctx
    return .matchNat p (← resolve ctx ty z) (← resolve ctxS ty s)
  | .pi bs cod =>
    let (ctx', hs, ds) ← binders ctx bs
    return .pi hs ds (← resolve ctx' true cod)
  | .arrow A B => return .pi [⟨"_"⟩] [← resolve ctx true A] (← resolve (.bound "_" :: ctx) true B)
  | .fix f bs ret body =>
    let (ctx', hs, ds) ← binders ctx bs
    let ret' ← resolve ctx' true ret
    let bodyCtx := (bs.reverse.map fun (x, _) => Entry.bound x) ++ (.bound f :: ctx)
    return .fix ⟨f⟩ hs ds ret' (← resolve bodyCtx false body)
  | .unitLit => pure .tt
  | .pair a b => return .pair (← resolve ctx false a) (← resolve ctx false b)
  | .andI a b => return .andI (← resolve ctx false a) (← resolve ctx false b)
  | .top => pure .top
  | .and P Q => return .and (← resolve ctx true P) (← resolve ctx true Q)
  | .prod A B => return .prod (← resolve ctx true A) (← resolve ctx true B)
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

/-- A top-level declaration becomes a `Def`; inside its body its own name is its `self`
binder (whose value is the global function). -/
def resolveDecl (d : SDecl) : R Def := do
  let (ctx', hs, ds) ← binders [] d.params
  let cod ← resolve ctx' true d.ret
  let body ←
    if d.params.isEmpty then resolve [] false d.body
    else resolve ((d.params.reverse.map fun (x, _) => Entry.bound x) ++ [.bound d.name]) false d.body
  pure { name := d.name, hs := hs, doms := ds, cod := cod, body := body }

end Ochr.Surface
