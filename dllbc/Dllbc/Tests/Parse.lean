import Dllbc.Program
import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# `prog_parse { … }` — fragments with free identifiers (docs/22)

The acceptance battery for capture-on-splice. A fragment written OUTSIDE the
binder that would bind its names keeps them as `Term.ident`; the block it is
`%`-spliced into binds them against its own binders at that point; one that
reaches the boundary unbound is rejected with the pinned message.

Every `Term`-equality claim here is `Term.beq` against what `prog{ }` produces
for the same text written INLINE, so the assertion is "a spliced fragment is the
inline program, byte for byte", not merely an equivalent one.
-/

open Dllbc
open Dllbc.StdLemmas (LeReflRaw)

namespace Dllbc.Tests.Parse

/-! ## (a) A spec fragment, bound against a telescope

    `Direct.lean`'s skeleton idiom: a return type written outside its `fn`
    header. The fragment's `v` and `i` are free; bound at the positional ids the
    header gives them, it is the header's own elaboration. -/

def specFrag : Term := prog_parse { Id (List Nat) (*v) (Take i (old *v)) }

example : specFrag.freeIdents = ["v", "i", "v"] := by native_decide

-- The inline spelling.
def specInline : Term := prog_parse {
  fn F (v : &mut List Nat, i : Nat) -> Id (List Nat) (*v) (Take i (old *v)) { Refl };
  () }

-- The fragment bound BY HAND against `[v ↦ ⟨0,"v"⟩, i ↦ ⟨1,"i"⟩]` — the
-- `seedTelescope` convention — and spliced: the splice-site bind at the header
-- then has nothing left to do, so this pins `bindFree` itself.
def specHandBound : Term := prog_parse {
  fn F (v : &mut List Nat, i : Nat) -> %(specFrag.bindFree [("v", 0), ("i", 1)] []) { Refl };
  () }

example : Term.beq specHandBound specInline = true := by native_decide

-- …and the same fragment spliced bare at the header IS the inline program. This
-- is the splice-site bind doing the work, with no hand context anywhere.
def specSpliced : Term := prog_parse {
  fn F (v : &mut List Nat, i : Nat) -> %specFrag { Refl };
  () }

example : Term.beq specSpliced specInline = true := by native_decide

/-! ## (b) A free `hd`, captured by the match arm it lands in

    `Direct.lean:497-500`'s exact limit: "a `%` splice … has no way to say 'the
    `hd` this match will bind'". The fragment says `hd`; the arm binds it. -/

def armFrag : Term := prog_parse { *hd := 0; () }

example : armFrag.freeIdents = ["hd"] := by native_decide

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

-- A fragment's free name is bound at the NEAREST splice-site binder of that
-- name: the same fragment under a different arm captures that arm's `hd`, which
-- is what "unhygienic on purpose" buys.
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

    Lexical inside, dynamic at the edge (docs/22 §4). The fragment binds its own
    `hd`, so its occurrence resolved at parse to the fragment's binder — at the
    fragment's own id 0 — and the arm's `hd` never sees it. -/

def shadowFrag : Term := prog_parse { let hd = 7; let h = hd; () }

example : shadowFrag.freeIdents = [] := by native_decide

def shadowSpliced : Term := prog{
  fn Peek (v : List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => %shadowFrag } };
  () }

-- The inner `hd` is the fragment's binder at the fragment's own id 0, not the
-- arm's `hd` (id 1 here: `v` is 0, and the arm mints `hd` at 1, `tl` at 2).
-- Read straight off the arm body.
def consArmBody : Term → Option Term
  | .seq (.letIn _ (.seal _ (.lam _ _ (.matchE _ _ [_, .mk "Cons" _ body])) _)) _ => some body
  | _ => none

example : (match consArmBody shadowSpliced with
           | some (.seq (.letIn x _) (.seq (.letIn _ (.var y)) _)) =>
             x == ⟨0, "hd"⟩ && y == ⟨0, "hd"⟩
           | _ => false) = true := by native_decide

example : progOk shadowSpliced = true := by native_decide

/-! ## (d) The boundary: an unbound free identifier is a loud rejection

    Spliced where nothing binds `hd`, the fragment reaches `atBoundary` with
    its `.ident` intact and the program is refused with the pinned message. -/

def unboundSpliced : Term := prog_parse {
  fn Zero (v : &mut List Nat) -> Unit { %armFrag };
  () }

example : progRejects unboundSpliced "free identifier 'hd' has no binder at the splice site" = true := by
  native_decide
example : progRejects unboundSpliced freeIdentNeedle = true := by native_decide

-- A bare fragment, never spliced, is refused by the same boundary — and by the
-- executing machine too, which is what makes this a boundary and not a
-- checker-side courtesy.
example : progRejects armFrag "free identifier 'hd'" = true := by native_decide
example : progRuns armFrag = false := by native_decide

-- The free name in a branch the walk never reaches is still loud: the boundary
-- scans the term, it does not wait for a rule to meet the node.
def deadBranch : Term := prog_parse {
  fn Peek (b : Bool) -> Unit { match b { True => (), False => %armFrag } };
  () }
example : progRejects deadBranch "free identifier 'hd'" = true := by native_decide

-- A name Lean knows is resolved as the closed braces resolve it: `prog_parse`
-- only emits an `.ident` for a name nobody knows.
def lemmaByName : Term := prog_parse { LeReflRaw Z }
example : lemmaByName.freeIdents = [] := by native_decide
example : Term.beq lemmaByName ty{ LeReflRaw Z } = true := by native_decide

-- The closed braces are unchanged: och's law still refuses a free name at Lean
-- elaboration in `ty{ }` (and in `prog{ }`, which walks the same resolver with
-- the same flag off). Pinned as the Lean error it always was.
/-- error: Unknown identifier `hd` -/
#guard_msgs in
example : Term := ty{ *hd := 0; () }

/-! ## A free SCRUTINEE — the one `Var`-carried free occurrence (docs/22 §2.2)

    `match v { … }` for free `v` cannot be an `.ident` (the scrutinee is a `Var`
    by §3), so it carries the `freeSlot` tag; `bindFree` rewrites it by name and
    the boundary reports it like any other. -/

def scrutFrag : Term := prog_parse { match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } } }

example : scrutFrag.freeIdents = ["v"] := by native_decide

def scrutSpliced : Term := prog{ fn Zero (v : &mut List Nat) -> Unit { %scrutFrag }; () }
def scrutInline : Term := prog{
  fn Zero (v : &mut List Nat) -> Unit { match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } } }; () }

-- Not `beq` on the whole program: the fragment mints its arm binders from 0
-- where the inline body mints them from 1 (after `v`), and the arm body cites
-- `hd`. The ids are decoration under the name-keyed Ω (M32 R1); the
-- scrutinee's binding is what the splice supplies, and it is asserted directly
-- — the tag before the splice, `v`'s positional slot after — and by the check
-- and the concrete run.
def scrutOf : Term → Option Var
  | .seq (.letIn _ (.seal _ (.lam _ _ (.matchE x _ _)) _)) _ => some x
  | _ => none

example : (match scrutFrag with | .matchE x _ _ => x == ⟨freeSlot, "v"⟩ | _ => false) = true := by
  native_decide
example : scrutOf scrutSpliced == some ⟨0, "v"⟩ := by native_decide
example : scrutOf scrutInline == some ⟨0, "v"⟩ := by native_decide
example : progOk scrutSpliced = true := by native_decide
example : progRuns (prog_parse {
  fn Zero (v : &mut List Nat) -> Unit { %scrutFrag };
  let x = Cons(1, Nil); let b = &m x; Zero(b); () }) = true := by native_decide

-- Unbound, it is "unbound at runtime" to the store and rejected at the boundary
-- first — never a by-name hit on a live `v`.
example : progRejects scrutFrag "free identifier 'v'" = true := by native_decide

/-! ## A lowercase kernel constant is the splice site's binder when one is in view

    `k` is the `Id` eliminator AND the name every `S(k) =>` arm binds. Inline
    the local wins because it is looked up before the table; a fragment has no
    local to find, classifies `k` as the constant, and `bindFree`'s `.const`
    row lets the splice site's binder claim it — so the spliced program is the
    inline one. With no binder anywhere it stays the eliminator. -/

def kFrag : Term := prog_parse { S(k) }
example : kFrag.freeIdents = [] := by native_decide
example : Term.beq kFrag (.ctorApp "S" [.const "k"]) = true := by native_decide

def kSpliced : Term := prog{ fn Bump (n : Nat) -> Nat { match n { Z => 0, S(k) => %kFrag } }; () }
def kInline : Term := prog{ fn Bump (n : Nat) -> Nat { match n { Z => 0, S(k) => S(k) } }; () }
example : Term.beq kSpliced kInline = true := by native_decide

example : Term.beq (Term.rejectFree prog_parse { k }) (.const "k") = true := by native_decide
example : Term.beq (Term.rejectFree (.ident "natRec")) (.const "natRec") = true := by native_decide

/-! ## A call whose head the splice site binds

    `F(y)` in a fragment that does not bind `F` is a `.call`, exactly as in a
    closed program. Spliced under a `let F = …` it is the spine inline `F(y)`
    would have been ("scope beats the table"); spliced under a `fn F` it stays
    a `.call` for `retarget`, as every closed program's calls do. -/

def callFrag : Term := prog_parse { let r = F(3); () }

example : (match callFrag with
           | .seq (.letIn _ (.call "F" [_])) _ => true
           | _ => false) = true := by native_decide

-- The call's right-hand side, compared on its own: the `let r` binder's id is
-- the fragment's 0 against the inline block's 1, and the RHS is the claim.
def secondRhs : Term → Option Term
  | .seq (.letIn _ _) (.seq (.letIn _ rhs) _) => some rhs
  | _ => none

def callUnderLet : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat);
  %callFrag }
def callUnderLetInline : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let r = F(3); () }
example : (match secondRhs callUnderLet, secondRhs callUnderLetInline with
           | some a, some b => Term.beq a b && Term.beq a (Term.appSpine (.var ⟨0, "F"⟩) [Term.nat 3])
           | _, _ => false) = true := by native_decide
example : progOk callUnderLet = true := by native_decide

def callUnderFn : Term := prog{ fn F (x : Nat) -> Nat { x }; %callFrag }
def callUnderFnInline : Term := prog{ fn F (x : Nat) -> Nat { x }; let r = F(3); () }
example : (match secondRhs callUnderFn, secondRhs callUnderFnInline with
           | some a, some b => Term.beq a b && Term.beq a (Term.appSpine (.var ⟨declSlot, "F"⟩) [Term.nat 3])
           | _, _ => false) = true := by native_decide
example : progOk callUnderFn = true := by native_decide

/-! ## Splices compose: a fragment inside a fragment

    The inner splice binds what the fragment binds and leaves the rest; the
    outer splice binds that. -/

def innerFrag : Term := prog_parse { Cons(hd, tl) }
def outerFrag : Term := prog_parse { match v { Nil => Nil, Cons(hd, tl) => %innerFrag } }

example : innerFrag.freeIdents = ["hd", "tl"] := by native_decide
example : outerFrag.freeIdents = ["v"] := by native_decide

def composed : Term := prog{ fn Copy (v : List Nat) -> List Nat { %outerFrag }; () }
example : progOk composed = true := by native_decide

end Dllbc.Tests.Parse
