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
* `match e { … }` on a term `e` that is not a place is `let x = e; match x { … }` with a
  fresh `x`, and `let C(x̄) = e; u` is `match e { C(x̄) => u }` when `C`'s type has one
  constructor (surface desugarings: the core matches places only);
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
  | rewrite (rev : Bool) (h t : STerm)           -- `rewrite h in t`, `rewrite ← h in t` (D60)
  | split (f : String) (t : STerm)                -- `split f in t` (D61)
  | splitArms (f : String) (arms : List (String × List String × STerm))   -- `split f { C(x̄) => t, … }` (D61)
  | letPat (c : String) (vars : List String) (scrut body : STerm)   -- `let C(x̄) = e; u`: `match e { C(x̄) => u }`, C's type having one constructor
  | loc (start stop : Nat) (t : STerm)           -- where `t` is written (byte offsets; the editor)
deriving Inhabited, Repr

/-- Where a surface term is written, if the `ochr` command recorded it. -/
def STerm.loc? : STerm → Option Loc
  | .loc s e _ => some ⟨s, e⟩
  | _ => none

/-- The term, without its location. -/
def STerm.unloc : STerm → STerm
  | .loc _ _ t => t.unloc
  | t => t

structure SDecl where
  name : String
  params : List (String × STerm) := []
  ret : STerm := .unitLit
  body : STerm := .unitLit
  dec : Option String := none
  ind? : Option (List (String × List (String × STerm))) := none   -- an inductive declaration
  indParams : List (String × STerm) := []                         -- its uniform parameters (v2.0)
  indSort : Option STerm := none                                  -- its sort (default Type₀)
  indCopy : Bool := false                                         -- declared `copy` (D53)
  indAbstract : Bool := false                                     -- declared `abstract` (K3)
  indUnsized : Bool := false                                      -- declared `unsized` (K2)
  implBy : Option String := none                                  -- `implemented by "sym"` (K3)
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

mutual
/-- `Block.closure`'s step: add `u` after the blocks it uses, unless already there (by name). -/
def Block.closureAdd (acc : List Block) : Block → List Block
  | u@(.mk n us _) =>
    if acc.any (·.name == n) then acc
    else
      let acc := Block.closureAddList acc us
      if acc.any (·.name == n) then acc else acc ++ [u]
termination_by structural u => u

/-- `us.foldl Block.closureAdd acc`. -/
def Block.closureAddList (acc : List Block) : List Block → List Block
  | [] => acc
  | u :: us => Block.closureAddList (Block.closureAdd acc u) us
termination_by structural us => us
end

/-- The blocks `b` uses, transitively, each once (by name), a block after the blocks it
uses. `b` itself is not included. -/
def Block.closure (b : Block) : List Block :=
  Block.closureAddList [] b.uses

mutual
/-- What `Block.closureAdd` adds lies in `u` (`Block.sizeOf_lt_of_mem_closure`). -/
theorem Block.mem_closureAdd {acc : List Block} {x : Block} :
    ∀ {u : Block}, x ∈ Block.closureAdd acc u → x ∈ acc ∨ sizeOf x ≤ sizeOf u
  | .mk n us ds, h => by
    unfold Block.closureAdd at h
    split at h
    · exact .inl h
    · dsimp only at h
      split at h
      · rcases Block.mem_closureAddList h with h | ⟨u', hu', hs⟩
        · exact .inl h
        · right; have := List.sizeOf_lt_of_mem hu'; simp only [Block.mk.sizeOf_spec]; omega
      · rcases List.mem_append.mp h with h | h
        · rcases Block.mem_closureAddList h with h | ⟨u', hu', hs⟩
          · exact .inl h
          · right; have := List.sizeOf_lt_of_mem hu'; simp only [Block.mk.sizeOf_spec]; omega
        · simp only [List.mem_singleton] at h; subst h; exact .inr (Nat.le_refl _)
termination_by structural u => u

theorem Block.mem_closureAddList {acc : List Block} {x : Block} :
    ∀ {us : List Block}, x ∈ Block.closureAddList acc us → x ∈ acc ∨ ∃ u ∈ us, sizeOf x ≤ sizeOf u
  | [], h => .inl h
  | u :: us, h => by
    unfold Block.closureAddList at h
    rcases Block.mem_closureAddList h with h | ⟨u', hu', hs⟩
    · rcases Block.mem_closureAdd h with h | h
      · exact .inl h
      · exact .inr ⟨u, List.mem_cons_self .., h⟩
    · exact .inr ⟨u', List.mem_cons_of_mem _ hu', hs⟩
termination_by structural us => us
end

/-- A block `b` uses, transitively, is smaller than `b`: the measure of `Ochr.Test.libWith`. -/
theorem Block.sizeOf_lt_of_mem_closure {b u : Block} (h : u ∈ b.closure) : sizeOf u < sizeOf b := by
  cases b with
  | mk n us ds =>
    unfold Block.closure at h
    rcases Block.mem_closureAddList h with h | ⟨u', hu', hs⟩
    · cases h
    · have := List.sizeOf_lt_of_mem hu'; simp only [Block.uses, Block.mk.sizeOf_spec] at this ⊢; omega

/-- The names a declaration introduces into a block's flat namespace: its own name and, for
an inductive type, its constructors'. -/
def SDecl.introduces (d : SDecl) : List String :=
  d.name :: (d.ind?.getD []).map (·.1)

mutual
/-- Every identifier a surface term mentions (constants, types, constructors, variables). -/
def STerm.idents : STerm → List String
  | .ident x => [x]
  | .num _ | .unitLit | .top | .sort _ => []
  | .app _ as => STerm.identsList as
  | .call f as => f.idents ++ STerm.identsList as
  | .ctorP c ps as => c :: (STerm.identsList ps ++ STerm.identsList as)
  | .deref t | .proj _ t | .amp t => t.idents
  | .assign a b | .seq a b | .pair a b | .andI a b | .and a b | .prod a b | .ascribe a b
  | .rewrite _ a b
  | .arrow a b => a.idents ++ b.idents
  | .letIn _ T t u => STerm.identsOpt T ++ t.idents ++ u.idents
  | .matchGen p arms => p.idents ++ STerm.identsArms arms
  | .split f t => f :: t.idents
  | .splitArms f arms => f :: STerm.identsArms arms
  | .letPat c _ sc b => c :: sc.idents ++ b.idents
  | .pi bs c => STerm.identsBinders bs ++ c.idents
  | .fix _ bs r _ b => STerm.identsBinders bs ++ r.idents ++ b.idents
  | .loc _ _ t => t.idents
termination_by structural t => t

def STerm.identsList : List STerm → List String
  | [] => []
  | t :: ts => t.idents ++ STerm.identsList ts
termination_by structural ts => ts

def STerm.identsOpt : Option STerm → List String
  | none => []
  | some t => t.idents
termination_by structural o => o

/-- A match's arms: each constructor's name and its body's identifiers. -/
def STerm.identsArms : List (String × List String × STerm) → List String
  | [] => []
  | (c, _, t) :: as => (c :: t.idents) ++ STerm.identsArms as
termination_by structural as => as

/-- A telescope's types. -/
def STerm.identsBinders : List (String × STerm) → List String
  | [] => []
  | (_, A) :: bs => A.idents ++ STerm.identsBinders bs
termination_by structural bs => bs
end

mutual
/-- The term with every location removed (for code that inspects a term's shape and was
written before terms had locations, such as the fuzzer's generators). -/
def STerm.strip : STerm → STerm
  | .loc _ _ t => t.strip
  | .app f as => .app f (STerm.stripList as)
  | .call f as => .call f.strip (STerm.stripList as)
  | .ctorP c ps as => .ctorP c (STerm.stripList ps) (STerm.stripList as)
  | .deref t => .deref t.strip
  | .proj i t => .proj i t.strip
  | .amp t => .amp t.strip
  | .assign a b => .assign a.strip b.strip
  | .letIn x T t u => .letIn x (STerm.stripOpt T) t.strip u.strip
  | .seq a b => .seq a.strip b.strip
  | .matchGen p arms => .matchGen p.strip (STerm.stripArms arms)
  | .pi bs c => .pi (STerm.stripBinders bs) c.strip
  | .arrow a b => .arrow a.strip b.strip
  | .fix f bs r d b => .fix f (STerm.stripBinders bs) r.strip d b.strip
  | .pair a b => .pair a.strip b.strip
  | .andI a b => .andI a.strip b.strip
  | .and a b => .and a.strip b.strip
  | .prod a b => .prod a.strip b.strip
  | .ascribe a b => .ascribe a.strip b.strip
  | .rewrite r h t => .rewrite r h.strip t.strip
  | .split f t => .split f t.strip
  | .splitArms f arms => .splitArms f (STerm.stripArms arms)
  | .letPat c xs sc b => .letPat c xs sc.strip b.strip
  | t => t
termination_by structural t => t

def STerm.stripList : List STerm → List STerm
  | [] => []
  | t :: ts => t.strip :: STerm.stripList ts
termination_by structural ts => ts

def STerm.stripOpt : Option STerm → Option STerm
  | none => none
  | some t => some t.strip
termination_by structural o => o

def STerm.stripArms : List (String × List String × STerm) → List (String × List String × STerm)
  | [] => []
  | (c, xs, t) :: as => (c, xs, t.strip) :: STerm.stripArms as
termination_by structural as => as

def STerm.stripBinders : List (String × STerm) → List (String × STerm)
  | [] => []
  | (x, A) :: bs => (x, A.strip) :: STerm.stripBinders bs
termination_by structural bs => bs
end

/-- The declaration with every location removed (`STerm.strip`). -/
def SDecl.strip (d : SDecl) : SDecl :=
  { d with params := d.params.map fun (x, A) => (x, A.strip), ret := d.ret.strip, body := d.body.strip,
           ind? := d.ind?.map (·.map fun (c, fs) => (c, fs.map fun (x, A) => (x, A.strip))),
           indParams := d.indParams.map fun (x, A) => (x, A.strip), indSort := d.indSort.map STerm.strip }

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

/-- What resolving a declaration records for the editor (`resolveLocated`): where each
resolved node is written (`Locs`, by the node's address), and where a resolution error is. -/
structure RState where
  record : Bool := false
  locs : Locs := {}
  ambiguous : Std.HashMap USize Unit := {}   -- a node written in two places (a shared constant)
  failAt : Option Loc := none

/-- Record that the resolved node `r` is written at `l` (a call with its arguments' ranges). -/
def RState.recordLoc (st : RState) (r : Term) (l : Loc) (args : Array (Option Loc)) : RState :=
  let a := termAddr r
  if !st.record || !isNodeAddr a || st.ambiguous.contains a then st else
  match st.locs.table.get? a with
  | some l' => if l' == l then st else
    { st with locs := { st.locs with table := st.locs.table.erase a, args := st.locs.args.erase a },
              ambiguous := st.ambiguous.insert a () }
  | none =>
    let ls := { st.locs with table := st.locs.table.insert a l, keep := st.locs.keep.push r }
    { st with locs := if args.isEmpty then ls else { ls with args := ls.args.insert a args } }

abbrev R := ReaderT Tables (ExceptT String (StateM RState))

/-- The constructors and types a program declares. The library's (`Pair`, `False`,
`True`, `And`) are among them: the `Prelude` block's declarations come first in every
program (v2.1). -/
def builtinNames : List String := ["Nat", "Unit", "Z", "refl", "S", "Id", "Eq", "cong"]

/-- The names resolution reads itself: the built-in types `Nat` and `Unit`, their constructors,
`refl`, and the built-in forms (`Id`, `Eq`, `cong`, `J`, `clone`, `trans`, `symm`). No
declaration may take one: the built-in meaning would win at some uses and the declaration at
others (reviewer-6's A3: a user `Unit` with two constructors was accepted, and `Unit` then
meant it, not the built-in type with η). -/
def reservedNames : List String := builtinNames ++ ["J", "clone", "trans", "symm"]

/-- A declaration that takes a reserved name, or has a constructor that does. -/
def SDecl.reservedName? (d : SDecl) : Option String :=
  if reservedNames.contains d.name then some d.name
  else (d.ind?.getD []).map (·.1) |>.find? reservedNames.contains

def Tables.ofProgram (p : List SDecl) : Tables :=
  p.foldl (fun t d => match d.ind? with
    | some cs =>
      -- a declaration taking a reserved name is rejected, and shadows nothing
      if d.reservedName?.isSome then t else
      { ctors := t.ctors ++ (cs.zipIdx.map fun ((cn, fs), i) => (cn, d.name, i, fs.map (·.1))),
        types := t.types ++ [d.name] }
    | none => t) {}

/-- How a term prints as an atom, given how it prints (`s = t.show`): parenthesised unless
it is one. -/
def STerm.atomWrap (t : STerm) (s : String) : String :=
  match t.unloc with
  | .ident _ | .num _ | .app .. | .call .. | .ctorP .. | .deref _ | .proj .. | .unitLit | .pair .. | .andI ..
  | .top | .sort _ | .ascribe .. => s
  | _ => s!"({s})"

mutual
/-- A term as it is written (in call form), for messages. -/
def STerm.show : STerm → String
  | .loc _ _ t => t.show
  | .ident x => x
  | .num n => toString n
  | .app f as | .call (.ident f) as => s!"{f}({", ".intercalate (STerm.showList as)})"
  | .call f as => s!"{f.atomWrap f.show}({", ".intercalate (STerm.showList as)})"
  | .ctorP c ps as => s!"{c}[{", ".intercalate (STerm.showList ps)}]({", ".intercalate (STerm.showList as)})"
  | .deref t => s!"*{t.atomWrap t.show}"
  | .proj i t => s!"{t.atomWrap t.show}.{i}"
  | .amp t => s!"&{t.atomWrap t.show}"
  | .assign p t => s!"{p.show} := {t.show}"
  | .letIn x _ t u => s!"let {x} = {t.show}; {u.show}"
  | .seq a b => s!"{a.show}; {b.show}"
  | .matchGen sc _ => s!"match {sc.show} \{ … }"
  | .split f t => s!"split {f} in {t.show}"
  | .splitArms f _ => s!"split {f} \{ … }"
  | .pi _ c => s!"Π(…). {c.show}"
  | .arrow a b => s!"{a.atomWrap a.show} → {b.show}"
  | .fix "_" _ _ _ _ => "λ(…) => …"
  | .fix f _ _ _ _ => s!"fix {f} …"
  | .unitLit => "()"
  | .pair a b => s!"({a.show}, {b.show})"
  | .andI a b => s!"⟨{a.show}, {b.show}⟩"
  | .top => "⊤"
  | .and a b => s!"{a.atomWrap a.show} ∧ {b.atomWrap b.show}"
  | .prod a b => s!"{a.atomWrap a.show} × {b.atomWrap b.show}"
  | .ascribe a A => s!"({a.show} : {A.show})"
  | .sort 0 => "Prop"
  | .sort 1 => "Type"
  | .sort l => s!"Type{l - 1}"
  | .rewrite rev h t => s!"rewrite {if rev then "← " else ""}{h.show} in {t.show}"
  | .letPat c xs sc b => s!"let {c}({", ".intercalate xs}) = {sc.show}; {b.show}"
termination_by structural t => t

/-- `ts.map STerm.show`. -/
def STerm.showList : List STerm → List String
  | [] => []
  | t :: ts => t.show :: STerm.showList ts
termination_by structural ts => ts
end

/-- `STerm.show`, parenthesised unless it is an atom. -/
def STerm.atom (t : STerm) : String := t.atomWrap t.show

def toPlace (ctx : Ctx) : STerm → R Place
  | .loc _ _ t => toPlace ctx t
  | .ident x => match lookup ctx x with
    | some p => pure p
    | none => throw s!"{x} is not a place (not a local variable)"
  | .deref t => return .deref (← toPlace ctx t)
  | .proj 0 t => return .fst (← toPlace ctx t)
  | .proj 1 t => return .snd (← toPlace ctx t)
  | t => throw s!"{t.show} is not a place (a variable, *p, or a field of a place): bind it first, let v = {t.show}; …"
termination_by structural t => t

/-- A place whose root is a dereferenced call, `*f(ā)` (also `(*f(ā)).1`, `**f(ā)`): the call,
and the place with the variable `x` in the call's position. Such a place is written for
`let x = f(ā); … *x …`, the temporary ending with the enclosing read, assignment, borrow,
`clone` or match (Rust's `*v.get_mut(i) = x`). A surface desugaring: the core has no such place. -/
def callRoot (x : String) : STerm → Option (STerm × STerm)
  | .loc s e t => (callRoot x t).map fun (c, p) => (c, .loc s e p)
  | .deref t => match t.unloc with
    | .call .. => some (t, .deref (.ident x))
    | _ => (callRoot x t).map fun (c, p) => (c, .deref p)
  | .proj i t => (callRoot x t).map fun (c, p) => (c, .proj i p)
  | _ => none
termination_by structural t => t

/-- The temporary that `*f(ā)` binds `f(ā)` to: named after the call, so that a message about
it (D53: reading `*f(ā)` moves out through the borrow) can say which. No user name has `⋄`. -/
def derefTemp (c : STerm) : String :=
  match c.unloc with
  | .call f _ => s!"⋄*{f.atom}(…)"
  | _ => "⋄*"

/-- The temporary that `match e { … }` binds a term `e` that is not a place to, named after
the term for messages, as `derefTemp`. No user name has `⋄`. -/
def matchTemp (sc : STerm) : String :=
  match sc.unloc with
  | .call f _ => s!"⋄{f.atom}(…)"
  | _ => "⋄match"

/-- `*f(ā)` written where a place is expected (`callRoot`), bound first: `let x = f(ā); k(p)`. -/
def withCallRoot (t : STerm) (k : STerm → STerm) : Option STerm := do
  let (c, _) ← callRoot "" t
  let x := derefTemp c
  let (c, p) ← callRoot x t
  pure (.letIn x none c (k p))

/-- `t` is written as a place (`toPlace` would accept it): a total, syntactic test. -/
def isPlace (ctx : Ctx) : STerm → Bool
  | .loc _ _ t => isPlace ctx t
  | .ident x => (lookup ctx x).isSome
  | .deref t | .proj 0 t | .proj 1 t => isPlace ctx t
  | _ => false
termination_by structural t => t

/-- The position of the parameter named by `by x`. -/
def decIndex (bs : List (String × STerm)) : Option String → R (Option Nat)
  | none => pure none
  | some x => match bs.findIdx? (·.1 == x) with
    | some j => pure (some j)
    | none => throw s!"`by {x}`: {x} is not a parameter"

def succFn : Term :=
  .fix ⟨"_"⟩ [⟨"n"⟩] [.nat] .nat none (.succ (.place (.var 0)))

-- the editor: each resolved node is a fresh object, so its address identifies one place in
-- the source (a closed term such as `refl`'s would otherwise be hoisted and shared)
set_option compiler.extract_closed false

/-- The built-ins written by juxtaposition (`Eq A a b`, `Id A t u`, `cong f h`, `trans h k`,
`symm h`) may also be written as calls, `Eq(A, a, b)`, so that everything is a call. A call whose
head is one of these names is read as the juxtaposition form. They are reserved names, so no user
definition can be shadowed. -/
def STerm.builtinCall : STerm → STerm
  | t@(.call f as) => match f.unloc with
    | .ident n => if ["Eq", "Id", "cong", "trans", "symm"].contains n then .app n as else t
    | _ => t
  | t => t

mutual
/-- Resolve a surface term against `ctx` (`ty`: in a type position). `fuel` bounds the
recursion: each step, including re-resolving a desugared term (`*f(ā)` bound first, a match
on a term that is not a place, a destructuring `let`), spends one unit, and running out is an
error, not an answer. -/
def resolveF (fuel : Nat) (ctx : Ctx) (ty : Bool) (t : STerm) : R Term := do
  let fuel' + 1 := fuel | throw "out of fuel"   -- FUEL-OUTCOME: the out-of-fuel outcome once no-fallbacks lands
  match t.builtinCall with
  | .loc s e u =>
    let r ← onFail (resolveF fuel' ctx ty u)
      (modify fun st => if st.failAt.isNone then { st with failAt := some ⟨s, e⟩ } else st)
    let args := match u with
      | .call _ as => as.toArray.map STerm.loc?
      | _ => #[]
    modify (·.recordLoc r ⟨s, e⟩ args)
    -- a match's scrutinee is a place, not a term: record its range with the match
    let scrut? := match u with
      | .matchGen sc _ | .letPat _ _ sc _ => some sc
      | _ => none
    if let some sc := scrut? then
      if let some l := sc.loc? then
        modify fun st => if st.record && st.locs.table.contains (termAddr r) then
          { st with locs := { st.locs with scruts := st.locs.scruts.insert (termAddr r) l } } else st
    pure r
  -- a call's head is matched on below (`J`, `clone`, a constructor, a type); its range is the call's
  | .call (.loc _ _ f) as => resolveF fuel' ctx ty (.call f as)
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
      | "?" => pure (.prim "hole" [])     -- a hole, `?` or `sorry` (docs/07)
      | _ => pure (.const x)
  | .num n => pure (Term.ofNat n)
  | .app "S" [a] => return .succ (← resolveF fuel' ctx false a)
  | .app "Id" [A, a, b] => return .id (← resolveF fuel' ctx true A) (← resolveF fuel' ctx false a) (← resolveF fuel' ctx false b)
  | .app "Eq" [A, a, b] => return .eq (← resolveF fuel' ctx true A) (← resolveF fuel' ctx false a) (← resolveF fuel' ctx false b)
  | .app "cong" [f, h] => return .cong (← resolveF fuel' ctx false f) (← resolveF fuel' ctx false h)

  | .app "trans" [h, k] => return .prim "trans" [← resolveF fuel' ctx false h, ← resolveF fuel' ctx false k]
  | .app "symm" [h] => return .prim "symm" [← resolveF fuel' ctx false h]
  | .app f as => throw s!"{f} applied by juxtaposition to {as.length} arguments (calls are written f(a, …))"
  | .call (.ident "J") [A, a, b, P, h, u] =>
    if (lookup ctx "J").isSome then return .call (← resolveF fuel' ctx false (.ident "J")) (← [A, a, b, P, h, u].mapM (resolveF fuel' ctx false)) false
    return .prim "J" [← resolveF fuel' ctx true A, ← resolveF fuel' ctx false a, ← resolveF fuel' ctx false b,
                      ← resolveF fuel' ctx false P, ← resolveF fuel' ctx false h, ← resolveF fuel' ctx false u]
  | .call (.ident "clone") [p] =>      -- D53: the built-in copy of a place
    if (lookup ctx "clone").isSome then return .call (← resolveF fuel' ctx false (.ident "clone")) [← resolveF fuel' ctx false p] false
    if let some t' := withCallRoot p fun p' => .call (.ident "clone") [p'] then return ← resolveF fuel' ctx ty t'
    match ← resolveF fuel' ctx false p with
    | t@(.place _) => return .prim "clone" [t]
    | _ => throw "clone takes a place: clone(p)"
  | .call (.ident c) as =>
    let tb ← read
    if (lookup ctx c).isNone && tb.types.contains c then
      return .tind c (← as.mapM (resolveF fuel' ctx true))       -- D(ā): the parameters are types
    match (if (lookup ctx c).isSome then none else tb.ctors.find? (·.1 == c)) with
    | some (_, ty, i, fs) =>
      if fs.length != as.length then throw s!"constructor {c} takes {fs.length} fields, given {as.length}"
      return .ctor ty i ⟨c⟩ [] (← as.mapM (resolveF fuel' ctx false))
    | none => return .call (← resolveF fuel' ctx false (.ident c)) (← as.mapM (resolveF fuel' ctx false)) false
  | .call f as => return .call (← resolveF fuel' ctx false f) (← as.mapM (resolveF fuel' ctx false)) false
  | .ctorP c ps as =>
    let tb ← read
    let some (_, ty, i, fs) := tb.ctors.find? (·.1 == c) | throw s!"{c} is not a constructor"
    if fs.length != as.length then throw s!"constructor {c} takes {fs.length} fields, given {as.length}"
    return .ctor ty i ⟨c⟩ (← ps.mapM (resolveF fuel' ctx true)) (← as.mapM (resolveF fuel' ctx false))
  | .deref _ =>
    if let some t' := withCallRoot t id then return ← resolveF fuel' ctx ty t'
    return .place (← toPlace ctx t)
  | .proj i a =>
    if let some t' := withCallRoot t id then return ← resolveF fuel' ctx ty t'
    if isPlace ctx t then return .place (← toPlace ctx t)
    else if i == 0 then return .fst (← resolveF fuel' ctx false a) else return .snd (← resolveF fuel' ctx false a)
  | .amp a =>
    if ty then return .ref (← resolveF fuel' ctx true a)
    if let some t' := withCallRoot a .amp then return ← resolveF fuel' ctx ty t'
    return .borrow (← toPlace ctx a)
  | .assign p a =>
    -- `*f(ā) := t`: the value first, then the place, as `p := t` evaluates them (and Rust)
    if let some t' := withCallRoot p fun p' => .assign p' (.ident "⋄val") then
      return ← resolveF fuel' ctx ty (.letIn "⋄val" none a t')
    return .assign (← toPlace ctx p) (← resolveF fuel' ctx false a)
  | .letIn x A a u =>
    let a' ← resolveF fuel' ctx false a
    let a' ← match A with
      | some A => pure (.ascribe a' (← resolveF fuel' ctx true A))
      | none => pure a'
    return .letIn ⟨x⟩ a' (← resolveF fuel' (.bound x :: ctx) ty u)
  | .seq a b => return .seq (← resolveF fuel' ctx false a) (← resolveF fuel' ctx ty b)
  | .matchGen sc arms =>
    if let some t' := withCallRoot sc fun p => .matchGen p arms then return ← resolveF fuel' ctx ty t'
    -- `match e { … }` on a term that is not a place is `let x = e; match x { … }`, with a
    -- fresh `x` (a surface desugaring). A place is matched in place, its arms binding its
    -- sub-places; binding it first would move it
    unless isPlace ctx sc do
      let x := matchTemp sc
      let a ← resolveF fuel' ctx false sc
      let m ← resolveF fuel' (.bound x :: ctx) ty (.matchGen (.ident x) arms)
      -- the editor: the term's range is the scrutinee of the match on the temporary
      if let some l := sc.loc? then
        modify fun st => if st.record then
          { st with locs := { st.locs with scruts := st.locs.scruts.insert (termAddr m) l } } else st
      return .letIn ⟨x⟩ a m
    let p ← toPlace ctx sc
    match arms with
    | [("Z", [], z), ("S", [y], s)] =>
      let ctxS := if y == "_" then ctx else .alias y (.fst p) :: ctx
      return .matchNat p (← resolveF fuel' ctx ty z) (← resolveF fuel' ctxS ty s)
    | [] => return .matchInd p "" []      -- no arms (v2.0): the scrutinee's type has no constructors
    | (c0, _, _) :: _ =>
      let tb ← read
      let some (_, tyName, _, _) := tb.ctors.find? (·.1 == c0)
        | throw (if c0 == "true" || c0 == "false" then
            s!"{c0} is not a constructor: `if` and a match on true/false need a declared Bool := false | true (use the block that declares it)"
          else s!"{c0} is not a constructor (Nat's are written Z => …, S y => …, in that order)")
      let cs := tb.ctors.filter (·.2.1 == tyName)
      let mut out := #[]
      for (cn, _, i, fs) in cs do
        let some (_, vars, body) := arms.find? (·.1 == cn) | throw s!"match on {tyName}: no arm for {cn}"
        if vars.length != fs.length then throw s!"pattern {cn} needs {fs.length} variables"
        -- pattern variables are the sub-places p.fᵢ (RULES §1, D32), naming their constructor
        let ctxA := (vars.zip (fs.zipIdx)).foldl (fun acc (v, (fname, j)) =>
          if v == "_" then acc else .alias v (.field ⟨tyName, i, j, fname⟩ p) :: acc) ctx
        out := out.push (Hint.mk cn, ← resolveF fuel' ctxA ty body)
      if arms.length != cs.length then throw s!"match on {tyName}: {arms.length} arms for {cs.length} constructors"
      return .matchInd p tyName out.toList
  | .letPat c vars sc body =>
    -- `let C(x̄) = e; u` is `match e { C(x̄) => u }`, for a type with one constructor only (a
    -- surface desugaring): with more, the other constructors would have no arm
    let tb ← read
    let tyName ← match tb.ctors.find? (·.1 == c) with
      | some (_, tyName, _, _) => pure tyName
      | none => if c == "Z" || c == "S" then pure "Nat" else throw s!"let {c}(…) = …: {c} is not a constructor"
    let cs := if tyName == "Nat" then ["Z", "S"] else (tb.ctors.filter (·.2.1 == tyName)).map (·.1)
    unless cs.length == 1 do
      throw s!"let {c}(…) = …: {tyName} has {cs.length} constructors ({", ".intercalate cs}), and a destructuring let needs a type with exactly one: use match"
    resolveF fuel' ctx ty (.matchGen sc [(c, vars, body)])
  | .pi bs cod =>
    let (ctx', hs, ds) ← bindersF fuel' ctx bs
    return .pi hs ds (← resolveF fuel' ctx' true cod)
  | .arrow A B => return .pi [⟨"_"⟩] [← resolveF fuel' ctx true A] (← resolveF fuel' (.bound "_" :: ctx) true B)
  | .fix f bs ret dec body =>
    let (ctx', hs, ds) ← bindersF fuel' ctx bs
    let ret' ← resolveF fuel' ctx' true ret
    let bodyCtx := (bs.reverse.map fun (x, _) => Entry.bound x) ++ (.bound f :: ctx)
    return .fix ⟨f⟩ hs ds ret' (← decIndex bs dec) (← resolveF fuel' bodyCtx false body)
  | .unitLit => pure .tt
  | .pair a b =>      -- `(a, b)`: notation for the library's `Mk(a, b)` of `Pair` (D52)
    return .ctor "Pair" 0 ⟨"Mk"⟩ [] [← resolveF fuel' ctx false a, ← resolveF fuel' ctx false b]
  | .andI a b => return .ctor "And" 0 ⟨"Intro"⟩ [] [← resolveF fuel' ctx false a, ← resolveF fuel' ctx false b]
  | .rewrite rev h u =>     -- D60: a typing rule, `J` with the motive read off the goal
    return .prim (if rev then "rewriteR" else "rewrite") [← resolveF fuel' ctx false h, ← resolveF fuel' ctx false u]
  | .split f u =>           -- D61: [Split] on the goal's stuck result of `f`
    return .prim "split" [.const f, ← resolveF fuel' ctx false u]
  | .splitArms f arms =>    -- D61: the split value is bound to a hidden variable, matched on
    return .prim "splitArms" [.const f, ← resolveF fuel' ctx false (.letIn "⋄split" none .unitLit (.matchGen (.ident "⋄split") arms))]
  | .top => pure (.tind "True" [])
  | .and P Q => return .tind "And" [← resolveF fuel' ctx true P, ← resolveF fuel' ctx true Q]
  | .prod A B => return .tind "Pair" [← resolveF fuel' ctx true A, ← resolveF fuel' ctx true B]   -- `A × B` (D52)
  | .ascribe a A => return .ascribe (← resolveF fuel' ctx false a) (← resolveF fuel' ctx true A)
  | .sort l => pure (.sort l)
termination_by structural fuel

/-- Resolve a telescope; each binder's type sees the earlier binders. -/
def bindersF (fuel : Nat) (ctx : Ctx) (bs : List (String × STerm)) : R (Ctx × List Hint × List Term) := do
  match bs with
  | [] => pure (ctx, [], [])
  | (x, A) :: bs =>
    let fuel' + 1 := fuel | throw "out of fuel"   -- FUEL-OUTCOME
    let A' ← resolveF fuel' ctx true A
    let (ctx', hs, ds) ← bindersF fuel' (.bound x :: ctx) bs
    pure (ctx', ⟨x⟩ :: hs, A' :: ds)
termination_by structural fuel
end

/-- `resolveF` with the checker's fuel budget. -/
def resolve (ctx : Ctx) (ty : Bool) (t : STerm) (fuel : Nat := 2000000) : R Term := resolveF fuel ctx ty t

/-- `bindersF` with the checker's fuel budget. -/
def binders (ctx : Ctx) (bs : List (String × STerm)) (fuel : Nat := 2000000) : R (Ctx × List Hint × List Term) :=
  bindersF fuel ctx bs

/-- A top-level declaration becomes an `Item`. Inside a definition's body its own name
is its `self` binder (whose value is the global function). `fuel`: the checker's budget,
which bounds resolution's recursion (`resolveF`). -/
def resolveDecl (d : SDecl) (fuel : Nat := 2000000) : R Item := do
  if let some x := d.reservedName? then
    throw s!"{x} is built in: a declaration may not redeclare it"
  if let some cs := d.ind? then
    -- the parameters are a telescope; the field types are in their scope (v2.0, D46), and in
    -- that of the constructor's fields (D64, dependent fields): the parameters are `var 0 …`
    -- as before, and field `j` of `k` is `var (np + k - 1 - j)`, so a field type that
    -- mentions no field reads as it did. Which fields a field type may mention (the earlier
    -- ones) is [Ind]'s check, not resolution's, so that it can say so
    let (ctx', hs, ps) ← binders [] d.indParams fuel
    let cs' ← cs.mapM fun (cn, fs) => do
      let ctxF := ctx' ++ fs.reverse.map fun (fname, _) => Entry.bound fname
      pure (cn, ← fs.mapM fun (fname, FT) => do pure (fname, ← resolve ctxF true FT fuel))
    let sort ← match d.indSort.map STerm.unloc with
      | none | some (.sort 1) => pure 1
      | some (.sort 0) => pure 0
      | some _ => throw s!"{d.name}: an inductive type is in Prop or Type"
    return .ind { name := d.name, params := hs.zip ps, sort := sort, ctors := cs', copy := d.indCopy,
                  abstract := d.indAbstract, unsized := d.indUnsized }
  let (ctx', hs, ds) ← binders [] d.params fuel
  let cod ← resolve ctx' true d.ret fuel
  let body ←
    if d.params.isEmpty then resolve [] false d.body fuel
    else resolve ((d.params.reverse.map fun (x, _) => Entry.bound x) ++ [.bound d.name]) false d.body fuel
  pure (.defn { name := d.name, hs := hs, doms := ds, cod := cod, dec := ← decIndex d.params d.dec, body := body,
                implBy := d.implBy })

/-- Resolve a whole program's declarations with its constructor table. -/
def resolveProgram (p : List SDecl) (d : SDecl) (fuel : Nat := 2000000) : Except String Item :=
  ((resolveDecl d fuel).run (Tables.ofProgram p)).run.run' {}

/-- The editor: `resolveProgram`, recording where `d`'s terms are written (`RState.locs`),
and, on a failure, the innermost located term around it (`RState.failAt`). -/
def resolveLocated (p : List SDecl) (d : SDecl) (fuel : Nat := 2000000) : Except String Item × RState :=
  ((resolveDecl d fuel).run (Tables.ofProgram p)).run.run { record := true }

end Ochr.Surface
