import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.DeclMacro
import Dllbc.Migrate

/-!
# §12 test suite — dependent call-site instantiation

The keystone (§5.3, stated since M6, implemented now): a call instantiates the
callee's telescope at the actuals. `processArgs` threads a substitution — for a
pure/owned argument the consumed value, for a borrow argument the actual borrow
(so a later `*b` in a type reflects to the payload snapshot just passed, §5.2) —
and reads the remaining parameter types, the return type, and the owed types at
those actuals. Nothing downstream (lemma application, spec-carrying calls, the
two recursive quicksort calls composing by transitivity) works without it.

Two supporting moves land here too: the return type is now pinned at entry (a
dependent return type may mention a parameter the body consumes, so it cannot be
re-read at return), and — the σ-refinement interaction — an instantiated return
or owed type may mention a caller σ, so it must refine when that σ does. The
"refinement reaches all σ-bearing state" invariant (built in M10 for
obligations) is extended to groups and the pinned return type; this milestone is
its first external consumer.

Plus the two mechanical dream-program clears: Term-level `Std` (so `Le`/`Sorted`
sit at telescope positions) and `if`-sugar over the Bool match.
-/

open Dllbc
open Dllbc.Std (le_reflT)

namespace Dllbc.Tests.S12Inst

/-! ## The dependent return type, instantiated at the actual -/

-- `use_refl (n : Nat) → Le n n = le_refl n`. The body ⇒-lifts the proof term
-- `le_refl n` (pure lift, §11); the audit checks it against the pinned `Le n n`.
def useRefl : Decl :=
  decl{ fn use_refl (n : Nat) -> Le n n { le_reflT n } }
example : Migrate.progOkOf useRefl = true := by native_decide

-- A caller returning `Le 5 5` via `use_refl(5)`: the callee's `Le n n` is
-- instantiated at `n := 5`, so the fresh existential is typed `Le 5 5`.
def callerRet : Decl :=
  decl{ fn callerRet () -> Le 5 5 { use_refl(5) } }
example : Migrate.progOkOf callerRet ([useRefl, callerRet]) = true := by native_decide

-- Symbolic actual: `f (n : Nat) → Le n n = use_refl(n)`. Instantiation substitutes
-- the caller's σ symbolically (`Le σ σ`); the pinned return type is `Le σ σ`, and
-- the returned existential is accepted at it.
def symCall : Decl :=
  decl{ fn symCall (n : Nat) -> Le n n { use_refl(n) } }
example : Migrate.progOkOf symCall ([useRefl, symCall]) = true := by native_decide

/-! ## A dependent second parameter (the M6 misresolution case, now correct) -/

-- `needs (a : Nat, p : Le a 2) → Unit`. The second parameter's type must
-- instantiate to `Le (actual) 2` BEFORE `p` is checked.
def needs : Decl :=
  decl{ fn needs (a : Nat, p : Le a 2) -> Unit { () } }

-- `needs(1, ())`: `Le 1 2` whnf's to ⊤, which `()` inhabits — accepted.
def callNeeds1 : Decl :=
  decl{ fn callNeeds1 () -> Unit { needs(1, ()) } }
example : Migrate.progOkOf callNeeds1 ([needs, callNeeds1]) = true := by native_decide

-- `needs(3, ())`: instantiation gives `Le 3 2` = ⊥, which `()` cannot inhabit —
-- REJECTED. Without instantiation the parameter type would never resolve to ⊥.
def callNeeds3 : Decl :=
  decl{ fn callNeeds3 () -> Unit { needs(3, ()) } }
example : Migrate.progRejectsOf callNeeds3 "does not have its parameter type" ([needs, callNeeds3]) = true := by
  native_decide

/-! ## A borrow-snapshot dependency (`*b`-in-types, exercised at a CALL) -/

-- `observe (b : &mut List Nat, p : Sorted (*b)) → Unit`. The second parameter's
-- type reads the actual borrow's payload snapshot at the call site.
def observe : Decl :=
  decl{ fn observe (b : &mut List Nat, p : Sorted (*b)) -> Unit { () } }

-- Passing a borrow of `[1,2]`: `Sorted (*b)` instantiates to `Sorted [1,2]`
-- (a product of ⊤s), which the unit-pair nest inhabits — accepted.
def observeGood : Decl :=
  decl{ fn observeGood () -> Unit {
    let x = Cons(1, Cons(2, Nil));
    let bb = &mut x;
    observe(bb, Pair((), Pair((), ())));
    let y = x;
    ()
  } }
example : Migrate.progOkOf observeGood ([observe, observeGood]) = true := by native_decide

-- Passing a borrow of `[2,1]`: `Sorted [2,1]` contains ⊥ at the first bound, so
-- the same proof fails — REJECTED. The dependent parameter caught the unsortedness.
def observeBad : Decl :=
  decl{ fn observeBad () -> Unit {
    let x = Cons(2, Cons(1, Nil));
    let bb = &mut x;
    observe(bb, Pair((), Pair((), ())));
    let y = x;
    ()
  } }
example : Migrate.progRejectsOf observeBad "does not have its parameter type" ([observe, observeBad]) = true := by
  native_decide

/-! ## The σ-refinement interaction -/

-- `f (n : Nat, pf : Id Nat n 2) → Unit = { let r = use_refl(n); match pf { Refl => needsLe22(r) } }`.
-- `r` is typed `Le n n` (instantiated at the caller σ). The `Refl`-match refines
-- `n := 2`; that refinement must reach `r`'s (call-result) sctx type, turning it
-- into `Le 2 2` — which `needsLe22` then requires. Green iff the refinement
-- propagated to the instantiated call result.
def needsLe22 : Decl :=
  decl{ fn needsLe22 (q : Le 2 2) -> Unit { () } }
def refineTest : Decl :=
  decl{ fn refineTest (n : Nat, pf : Id Nat n 2) -> Unit {
    let r = use_refl(n); match pf { Refl => needsLe22(r) } } }
example : Migrate.progOkOf refineTest ([useRefl, needsLe22, refineTest]) = true := by native_decide

/-! ## `if`-sugar over the Bool match (dream-program gap 5) -/

-- `classify (b : Bool) → Nat = if b { 1 } else { 0 }` desugars to a fresh-var let
-- and a `match` on it; a symbolic `Bool` splits into two audited paths.
def classify : Decl :=
  decl{ fn classify (b : Bool) -> Nat { if b { 1 } else { 0 } } }
example : Migrate.progOkOf classify = true := by native_decide

/-! ## §12.7 The dream program, re-annotated

    Which M11 GAP[..] tags this milestone clears, and what remains.

    CLEARED by M12:
    * GAP[dependent call] — dependent call-site instantiation is in. Every
      spec-carrying call and lemma application now type-checks at its actuals;
      the two recursive quicksort calls can compose their `Sorted`/`Perm` specs
      by transitivity (once the transitivity lemma exists — see the OTHER wall).
    * GAP[Term-level Std] (gap 2) — `LeT`/`SortedT`/`countT`/`BoundT` sit at
      telescope, return, and owed positions now.
    * GAP[bool guard] / `if` (gap 5) — `if e { … } else { … }` is macro sugar
      over the Bool match; `leb`/`eqb` reflect to `Bool` and guard directly.

    STILL OPEN (the M13+ train, unchanged in priority order):
    * GAP[two-cursor swap / access-at-depth-i] — the naturalness make-or-break.
      Instantiation lets us STATE `swap`'s count-preservation spec; expressing
      the swap BODY (two reborrow cursors to depths i and j, cross-write) still
      has no depth-indexed idiom. This is the next milestone.
    * GAP[slice split: take/drop reborrows] — a prefix riding the length bound, a
      suffix as a depth-(k+1) reborrow. `take`/`drop` on list snapshots are a
      mechanical Std addition (for the SPECS); the reborrow OPERATIONS are not.
    * GAP[nested-induction lemmas] — `le_trans` and `count_swap` are the proofs
      the specs above will consume. As raw eliminator terms they are impractical
      (the M11 le_trans wall); this is the dependent-match-elaboration milestone,
      which instantiation (this milestone) is the precondition for.
    * GAP[bounded recursion / decreasing [k]] — partial correctness is fine with
      signature-only recursion; the totality index (§8) is deferred.
-/

end Dllbc.Tests.S12Inst
