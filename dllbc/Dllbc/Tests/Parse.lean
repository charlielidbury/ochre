import Dllbc.Program
import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# `prog_parse { … }` fragments — free names, bound where they land (docs/22)

A fragment written OUTSIDE the binder that would bind its names is a term with
free names, and nothing more (docs/22 §1): `%`-spliced into a block, its names
resolve by the same scope rule as everything else — lexically inside the
fragment, dynamically at its edge (§6, the hygiene ruling). A name nothing
binds reaches the boundary free and is refused there (§5).

Every equality here is `Term.beq` against what the same text elaborates to
written INLINE, and with no binder ids left it is EXACT: a spliced fragment is
the inline program, byte for byte.
-/

open Dllbc
open Dllbc.StdLemmas (LeReflRaw)

namespace Dllbc.Tests.Parse

/-! ## (a) A spec fragment, bound by a telescope

    `Direct.lean`'s skeleton idiom: a return type written outside its `fn`
    header. The fragment's `v` and `i` are free; spliced at the header they are
    the header's own parameters. -/

def specFrag : Term := prog_parse { Id (List Nat) (*v) (Take i (old *v)) }

example : Term.freeVars [] specFrag = ["v", "i", "v"] := by native_decide

def specInline : Term := prog_parse {
  fn F (v : &mut List Nat, i : Nat) -> Id (List Nat) (*v) (Take i (old *v)) { Refl };
  () }

def specSpliced : Term := prog_parse {
  fn F (v : &mut List Nat, i : Nat) -> %specFrag { Refl };
  () }

example : Term.beq specSpliced specInline = true := by native_decide

-- …and a twin that lies about the spec differs from the honest one exactly where
-- the fragment differs, which is the whole of what the skeleton idiom wanted.
def specLie : Term := prog_parse { Id (List Nat) (*v) (Take (S i) (old *v)) }
example : Term.beq (prog_parse { fn F (v : &mut List Nat, i : Nat) -> %specLie { Refl }; () })
                   specInline = false := by native_decide

/-! ## (b) A free `hd`, captured by the match arm it lands in

    `Direct.lean:497-500`'s exact limit under two namespaces: "a `%` splice …
    has no way to say 'the `hd` this match will bind'". The fragment says
    `hd`; the arm binds it. -/

def armFrag : Term := prog_parse { *hd := 0; () }

example : Term.freeVars [] armFrag = ["hd"] := by native_decide

def armSpliced : Term := prog{
  fn Zero (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => %armFrag } };
  () }

def armInline : Term := prog{
  fn Zero (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } } };
  () }

example : Term.beq armSpliced armInline = true := by native_decide
example : progOk armSpliced = true := by native_decide

-- The same fragment under two arms is each arm's `hd`: a fragment's free name
-- is the NEAREST binder of that name where it lands.
def armSplicedTwice : Term := prog{
  fn Zero (v : &mut List Nat, w : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => %armFrag };
    match w { Nil => (), Cons(hd, tl) => %armFrag } };
  () }

def armInlineTwice : Term := prog{
  fn Zero (v : &mut List Nat, w : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } };
    match w { Nil => (), Cons(hd, tl) => { *hd := 0; () } } };
  () }

example : Term.beq armSplicedTwice armInlineTwice = true := by native_decide

/-! ## (c) The shadowing pin: a fragment's OWN `hd` is not captured

    Lexical inside, dynamic at the edge (docs/22 §6). The fragment binds its
    own `hd`, so its `hd` occurrences mean the fragment's `let` — the arm's
    `hd` is shadowed for them — and the program computes with the `let`'s
    value, not the arm's. -/

def shadowFrag : Term := prog_parse { let hd = 7; hd }

example : Term.freeVars [] shadowFrag = [] := by native_decide

def shadowSpliced : Term := prog{
  fn Peek (v : List Nat) -> Nat { match v { Nil => 0, Cons(hd, tl) => %shadowFrag } };
  let l = Cons(1, Nil); let r = Peek(l); () }

def shadowInline : Term := prog{
  fn Peek (v : List Nat) -> Nat { match v { Nil => 0, Cons(hd, tl) => { let hd = 7; hd } } };
  let l = Cons(1, Nil); let r = Peek(l); () }

example : Term.beq shadowSpliced shadowInline = true := by native_decide
-- The arm's `hd` is 1; the fragment's is 7; `r` is 7.
example : ((runProgram shadowSpliced).toOption.bind (·.lookup "r")) == some (Val.nat 7) := by
  native_decide

/-! ## (d) The boundary: a name nothing binds is refused, with the pinned message

    A fragment spliced where nothing binds `hd` reaches `atBoundary` with it
    free (§5): the program is refused before any rule runs, by the `fnElabOrFail`
    precedent — a term the machine cannot accept, naming the offender. -/

def unboundSpliced : Term := prog_parse {
  fn Zero (v : &mut List Nat) -> Unit { %armFrag };
  () }

example : progRejects unboundSpliced "unbound identifier 'hd'" = true := by native_decide
example : progRejects unboundSpliced unboundNeedle = true := by native_decide

-- A bare fragment, never spliced, is refused by the same boundary — and by the
-- executing machine, which is what makes this a boundary and not a checker-side
-- courtesy.
example : progRejects armFrag "unbound identifier 'hd'" = true := by native_decide
example : progRuns armFrag = false := by native_decide

-- A free name in a branch the walk never takes is still refused: the boundary
-- scans the term, it does not wait for a rule to meet the name.
def deadBranch : Term := prog_parse {
  fn Peek (b : Bool) -> Unit { match b { True => (), False => %armFrag } };
  () }
example : progRejects deadBranch "unbound identifier 'hd'" = true := by native_decide

-- The closed braces are unchanged: och's law still refuses a free name at Lean
-- elaboration, at the identifier — `ty{ }` below, and `prog{ }`, which walks
-- the same resolver with the parse flag off. Pinned as the Lean error it is.
/-- error: Unknown identifier `hd` -/
#guard_msgs in
example : Term := ty{ *hd := 0; () }

-- …and a name Lean knows is resolved as the closed braces resolve it.
def lemmaByName : Term := prog_parse { LeReflRaw Z }
example : Term.freeVars [] lemmaByName = [] := by native_decide
example : Term.beq lemmaByName ty{ LeReflRaw Z } = true := by native_decide

/-! ## A free scrutinee

    `match v { … }` for free `v` is `.matchE "v" …` — the scrutinee is a name
    like any other occurrence — and spliced under the parameter it IS the inline
    match, arm binders and all. -/

def scrutFrag : Term := prog_parse { match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } } }

example : Term.freeVars [] scrutFrag = ["v"] := by native_decide

def scrutSpliced : Term := prog{ fn Zero (v : &mut List Nat) -> Unit { %scrutFrag }; () }
def scrutInline : Term := prog{
  fn Zero (v : &mut List Nat) -> Unit { match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } } }; () }

example : Term.beq scrutSpliced scrutInline = true := by native_decide
example : progRejects scrutFrag "unbound identifier 'v'" = true := by native_decide

/-! ## Splices compose

    A fragment inside a fragment: the inner one's free names are bound by the
    outer one's binders where the outer binds them, and by the program where it
    does not. -/

def innerFrag : Term := prog_parse { Cons(hd, tl) }
def outerFrag : Term := prog_parse { match v { Nil => Nil, Cons(hd, tl) => %innerFrag } }

example : Term.freeVars [] innerFrag = ["hd", "tl"] := by native_decide
example : Term.freeVars [] outerFrag = ["v"] := by native_decide

def composed : Term := prog{ fn Copy (v : List Nat) -> List Nat { %outerFrag }; () }
def composedInline : Term := prog{
  fn Copy (v : List Nat) -> List Nat { match v { Nil => Nil, Cons(hd, tl) => Cons(hd, tl) } }; () }
example : Term.beq composed composedInline = true := by native_decide
example : progOk composed = true := by native_decide

/-! ## The splice and the bare name are one form

    `%e` splices a Lean-level `Term`; a bare name that resolves to a Lean
    constant or local of type `Term` IS that splice (`prog{ }`'s documented
    fallback, and `ident_or_free%`'s first rung in a fragment). The de-splice
    sweep (dllbc-desplice) rewrites `%X` to `X` on this equality; these are its
    ground-truth pins, one per shape: a fragment citing a name the walker does
    not bind, a `%(Term.var "x")` leaf as the bare free name, and a literal
    numeral splice as the numeral (`buildNat` emits one `Term.nat k` node). -/

example : Term.beq (prog_parse { fn F (v : &mut List Nat, i : Nat) -> specFrag { Refl }; () })
                   (prog_parse { fn F (v : &mut List Nat, i : Nat) -> %specFrag { Refl }; () }) = true := by
  native_decide
example : Term.beq (prog_parse { Id Nat r (S(S(Z))) })
                   (prog_parse { Id Nat %(Dllbc.Term.var "r") (S(S(Z))) }) = true := by native_decide
example : Term.beq (prog_parse { 1056 }) (prog_parse { %(Term.nat 1056) }) = true := by native_decide

/-! ## The two limits a fragment has, stated

    A fragment is parsed without the splice site's binders in view, and two of
    the walker's decisions are made at parse:

      * the TABLES — constructors, kernel constants, aliases — win over a name
        the fragment does not bind (docs/22 §7.1). So a fragment cannot cite a
        splice-site binder named `k`, `j`, `natRec`: its `k` is the `Id`
        eliminator. Inline, a binder named `k` shadows the table because the
        walker finds it first;
      * `F(x)` on a head the fragment does not bind is a declaration-table
        `.call`, for `retarget` to rewrite under a `fn F` — which it does,
        exactly as a closed program's calls are rewritten — while inline
        `F(x)` under a `let F = …` is an app spine on the local. A fragment
        that wants the local writes the spine itself, `F x`. -/

def kFrag : Term := prog_parse { S(k) }
example : Term.beq kFrag (.ctorApp "S" [.const "k"]) = true := by native_decide

def callFrag : Term := prog_parse { let r = F(3); () }
example : (match callFrag with
           | .seq (.letIn _ (.call "F" [_])) _ => true
           | _ => false) = true := by native_decide

def callUnderFn : Term := prog{ fn F (x : Nat) -> Nat { x }; %callFrag }
def callUnderFnInline : Term := prog{ fn F (x : Nat) -> Nat { x }; let r = F(3); () }
example : Term.beq callUnderFn callUnderFnInline = true := by native_decide

def spineFrag : Term := prog_parse { let r = F 3; () }
def spineUnderLet : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Nat); %spineFrag }
def spineUnderLetInline : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let r = F 3; () }
example : Term.beq spineUnderLet spineUnderLetInline = true := by native_decide
example : progOk spineUnderLet = true := by native_decide

end Dllbc.Tests.Parse
