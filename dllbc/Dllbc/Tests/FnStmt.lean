import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.DeclMacro
import Dllbc.Std
import Dllbc.Migrate

/-!
# The `fn` statement ≡ `decl{ }` + `progOf` — the sweep's safety net (M28 θ)

`fn` is now a statement of the one grammar (Uni.lean), and the corpus is about to
be moved onto it site by site. This module is what polices that move: for a
battery covering every shape the lowering treats differently, it asserts that

    prog{ fn a …; fn b …; TAIL }   ==   progOf [declA, declB] (prog{ TAIL })

as `Term`s, by `==`. **Literal equality, not α-equivalence** — and that is worth
stating because it was not a foregone conclusion. The statement binds its slot at
`progBase + next`, `progOf` binds the `i`-th declaration at `progBase + i`, and
those agree exactly when the statements are consecutive and start a block, which
is the migration's shape. (Interleave a `let` between two `fn`s and the second
slot shifts; the programs stay equivalent but stop being equal, so the net is
written on consecutive chains.)

## What each case is for

  * **A** non-recursive, plus a caller — the ordinary shape, and the `retarget`
    path for an unpermuted call.
  * **B** `[k]` on parameter 0 — `hoist` is the identity, so the permutation is
    invisible. Most of the corpus.
  * **C** `[k]` NOT on parameter 0 — `hoist` moves the scrutinee to the front, so
    every CALL to it must permute its arguments to match. This is the case that
    made the design what it is: minting a `.callV` at the surface (the obvious
    implementation) would skip the permutation and silently pass the wrong
    argument, and eight functions in this corpus have a non-first `[k]`.
  * **D** a dependent return type — the return type is elaborated against the
    telescope's positional context, and the statement must use the same one.
  * **E** the refusal path, which has no `decl{ }` counterpart to compare against
    and is asserted directly: a `fn` the lowering refuses must be REJECTED, with
    the refusal's own words in the message.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.FnStmt

/-! ## A. Non-recursive, and a caller that reaches it -/

def pushD : FnDef :=
  decl{ fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () } }
def callerD : FnDef :=
  decl{ fn caller () -> Unit { let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () } }

def aStmt : Term := prog{
  fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  fn caller () -> Unit { let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () };
  ()
}

example : (match FnMacro.progOf [pushD, callerD] .unit with
           | .ok t => t == aStmt | .error _ => false) = true := by native_decide

-- …and it is the same PROGRAM, not merely the same tree: it checks.
example : progOk aStmt = true := by native_decide

/-! ## B. `[k]` on parameter 0 — hoist is the identity -/

def countdownD : FnDef :=
  decl{ fn countdown [n] (n : Nat, b : Bool) -> Unit {
    match n { Z => (), S(k) => { countdown(k, b); () } } } }
def bCallerD : FnDef := decl{ fn caller () -> Unit { countdown(3, True); () } }

def bStmt : Term := prog{
  fn countdown [n] (n : Nat, b : Bool) -> Unit {
    match n { Z => (), S(k) => { countdown(k, b); () } } };
  fn caller () -> Unit { countdown(3, True); () };
  ()
}

example : (match FnMacro.progOf [countdownD, bCallerD] .unit with
           | .ok t => t == bStmt | .error _ => false) = true := by native_decide
example : progOk bStmt = true := by native_decide

/-! ## C. `[k]` NOT on parameter 0 — the permutation the design exists for -/

def dec2D : FnDef :=
  decl{ fn dec2 [n] (b : Bool, n : Nat) -> Unit {
    match n { Z => (), S(k) => { dec2(b, k); () } } } }
def cCallerD : FnDef := decl{ fn caller () -> Unit { dec2(True, 3); () } }

def cStmt : Term := prog{
  fn dec2 [n] (b : Bool, n : Nat) -> Unit {
    match n { Z => (), S(k) => { dec2(b, k); () } } };
  fn caller () -> Unit { dec2(True, 3); () };
  ()
}

example : (match FnMacro.progOf [dec2D, cCallerD] .unit with
           | .ok t => t == cStmt | .error _ => false) = true := by native_decide
example : progOk cStmt = true := by native_decide

-- **The permutation is real, and not vacuous.** A caller writes arguments in
-- DECLARATION order — `dec2(True, 3)` — and the assembled call passes the
-- scrutinee first, because `hoist` moved it there. The negative twin at the same
-- position: writing the arguments in the callee's HOISTED order is the type error
-- it should be, so the accept above is the permutation happening and not the two
-- orders being interchangeable.
def cStmtSwapped : Term := prog{
  fn dec2 [n] (b : Bool, n : Nat) -> Unit {
    match n { Z => (), S(k) => { dec2(b, k); () } } };
  fn caller () -> Unit { dec2(3, True); () };
  ()
}
example : progRejects cStmtSwapped "parameter type" = true := by native_decide

/-! ## D. A dependent return type -/

def idOfD : FnDef :=
  decl{ fn idOf (n : Nat) -> Id Nat n n { Refl } }
def dCallerD : FnDef := decl{ fn caller () -> Unit { let r = idOf(2); () } }

def dStmt : Term := prog{
  fn idOf (n : Nat) -> Id Nat n n { Refl };
  fn caller () -> Unit { let r = idOf(2); () };
  ()
}

example : (match FnMacro.progOf [idOfD, dCallerD] .unit with
           | .ok t => t == dStmt | .error _ => false) = true := by native_decide
example : progOk dStmt = true := by native_decide

/-! ## E. The refusal path

    `fnElab` refuses on the elaborated `Term`s, after the macro has run, so a
    refused `fn` cannot become a Lean error the way `decl{ }`'s syntactic checks
    do. It becomes a term the checker refuses distinctively instead. `[v]` — a
    decrease through a borrow's PAYLOAD — is §7 cost 4's own example and the
    refusal the corpus actually hits. -/

def refusedStmt : Term := prog{
  fn zero_all [v] (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; zero_all(tl); () } } };
  ()
}

-- It is REJECTED, by the needle no other error produces…
example : progRejects refusedStmt FnMacro.fnRefusedNeedle = true := by native_decide
-- …and the refusal's own diagnosis survives into the message, so the programmer
-- is told what to do rather than that something is unknown.
example : progRejects refusedStmt "§12 decision 8" = true := by native_decide
-- It can never pass green: the sentinel is reached at the BINDING, not at a call,
-- so a refused function that nothing calls still fails.
example : progOk refusedStmt = false := by native_decide

/-! ## F. `[k]` naming a non-parameter stays a LEAN error

    The one refusal that is cheap syntactically is the one `decl{ }` already made
    syntactic, and it stays there — the macro has to resolve `[k]` to an index
    anyway, so it can say so at elaboration. Not assertable as a test (it fails
    the build by design); recorded here so the sweep knows which errors appear
    when. Writing `fn f [zzz] (n : Nat) -> Unit { () }` gives:

        fn: decreasing argument 'zzz' is not a parameter of 'f'
-/

end Dllbc.Tests.FnStmt
