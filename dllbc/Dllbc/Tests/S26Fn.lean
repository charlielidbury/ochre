import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.FnMacro
import Dllbc.AlphaEq
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S26Seal
import Dllbc.Tests.S26Modes
import Dllbc.Tests.S26Modes
import Dllbc.Tests.S26Rec

/-!
# §26 (M26-D) — `fn` is a macro

`combining-fns.md` §7: `fn f (…) -> R { body }` is a binding of `.seal ⟨recursor
term⟩ ⟨the Π⟩`, `[k]` survives only as the macro's hint for which argument becomes
the scrutinee, and the motive is derived from the signature. `Dllbc/FnMacro.lean`
is that elaboration; this file is its evidence.

**Constraint 7 is what makes the whole thing safe to attempt.** Nothing in the
kernel imports `FnMacro`, so macro output is re-checked from scratch at the seal —
where `ih` is a binder and each arm is checked at its own constructor. A bug here
produces a program that fails to check, or one that checks as a different
function; it can never produce an unsound acceptance. That is why the tests below
are allowed to be *comparisons* (does the macro agree with the hand elaboration,
does it agree with `checkFn`) rather than proofs.
-/

open Dllbc
open Dllbc.Tests.S26Seal (ok rejects)

namespace Dllbc.Tests.S26Fn

/-- Elaborate and bind, which is the `let` §8 says a declaration is. -/
def elabIn (d : Decl) : Except String Decl :=
  (FnMacro.fnElab d).map (fun t =>
    { name := "caller", telescope := [], retType := .const "Unit",
      body := .letIn ⟨900, "f"⟩ t .unit })

/-- The macro's output checks. `table` is what its NON-self calls resolve
    against — self-calls are gone by construction, having become `ih`. -/
def elabOk (d : Decl) (table : List Decl := []) : Bool :=
  match elabIn d with
  | .error _ => false
  | .ok c => ok c table

/-- The macro refuses, with `needle` in the message. -/
def elabRejects (d : Decl) (needle : String) : Bool :=
  match FnMacro.fnElab d with
  | .error e => strContains e needle
  | .ok _ => false

/-! ## §A. The non-recursive case, and the round trip that says the Π is right

    A `fn` with no `[k]` is one runtime λ sealed at its signature — the degenerate
    case §4 calls the smell test, now reached from a declaration. It lands first
    because it exercises `telePi` alone: if the Π were built wrongly, everything
    downstream would fail for a reason that had nothing to do with recursors. -/

def pushD : Decl := decl{ fn pushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () } }
example : checkFnOk pushD = true := by native_decide
example : elabOk pushD = true := by native_decide

/-- `telePi` and the kernel's `piPeel` are inverse, which is the property the
    whole elaboration rests on: the macro writes a Π, the kernel takes it apart
    again, and the telescope that comes back is the one that went in. Asserted
    directly rather than inferred from the checks passing. -/
def roundTrips (d : Decl) : Bool :=
  let tel := FnMacro.teleVars d.telescope
  match piPeel (tel.map (·.1)) (FnMacro.telePi tel d.retType) with
  | .error _ => false
  | .ok (tel', ret') => tel' == tel && ret' == d.retType

example : roundTrips pushD = true := by native_decide
example : roundTrips Tests.S23Direct.splitOff = true := by native_decide
example : roundTrips Tests.S23Direct.quicksort = true := by native_decide
-- …and over a battery, so the round trip is a property and not three points.
example :
  [pushD, Tests.S23Direct.splitOff, Tests.S23Direct.quicksort,
   Tests.S23Direct.partition, Tests.S26Modes.step].all roundTrips = true := by native_decide

/-! ## §B. `split_off` — the macro against the hand elaboration

    M26-C hand-wrote `split_off` as a sealed recursor and checked it. That makes
    it an ORACLE the macro can be held to, and a strong one: it was written before
    the macro existed, by reading §7 rather than by reading the code.

    Compared up to α, not on the nose: the macro threads binder ids linearly while
    the hand version got them from the surface elaborator, so the two agree on
    binding structure and differ on numbering — which is exactly what
    `Decl.alphaEq` was built for (its own docstring says so). -/

def splitElab : Except String Term := FnMacro.fnElab Tests.S23Direct.splitOff

/-- The hand elaboration from M26-C, extracted from its caller. -/
def splitHand : Term :=
  match Tests.S26Rec.splitSealed.body with
  | .letIn _ t _ => t
  | t => t

/-- Wrap a term as a `Decl` so `alphaEq` (which is `Decl`-shaped) can compare two. -/
def asDecl (t : Term) : Decl :=
  { name := "x", telescope := [], retType := .const "Unit", body := t }

example :
  (match splitElab with
   | .ok t => Decl.alphaEq (asDecl t) (asDecl splitHand)
   | .error _ => false) = true := by native_decide

-- …and the macro's output checks, which is the claim that matters: agreeing with
-- my hand term would be worth little if my hand term were wrong, and it is the
-- kernel that says otherwise (constraint 7 — the output is re-derived, not
-- trusted).
example : elabOk Tests.S23Direct.splitOff = true := by native_decide
-- The declared twin stays alive and checked (J1: both worlds).
example : checkFnOk Tests.S23Direct.splitOff = true := by native_decide

-- The oracle is not vacuous: α-equality can say NO. Compared against the same
-- function's BASE arm, which is a real term of the same file and shape family.
example :
  (match splitElab with
   | .ok t => Decl.alphaEq (asDecl t) (asDecl (Tests.S26Rec.splitSealed.body))
   | .error _ => false) = false := by native_decide

/-! ### B2. The macro path rejects exactly what the declared path rejects

    `S23Direct` guards `splitOff` with four twins — three spec lies and a body lie
    — precisely so its acceptance is not a coincidence, and notes the division of
    labour: the spec lies are caught on the `i = Z` path, the body lie on the
    recursive one. Running the SAME four through the macro is what turns "the
    elaborated form checks" into "the elaborated form is the same function": it
    accepts what the declaration accepts and refuses what it refuses, twin for
    twin. -/

def splitTwins : List Decl :=
  [ Tests.S23Direct.splitOffLieTake, Tests.S23Direct.splitOffLieDrop,
    Tests.S23Direct.splitOffLieSwap, Tests.S23Direct.splitOffLieHead ]

-- The declared path refuses all four…
example : splitTwins.all (fun d => !checkFnOk d) = true := by native_decide
-- …and so does the elaborated one, which is the claim.
example : splitTwins.all (fun d => !(elabOk d)) = true := by native_decide
-- Not vacuous: the honest one is accepted by BOTH paths, so the four rejections
-- above are about the lies and not about the elaboration failing wholesale.
example : (checkFnOk Tests.S23Direct.splitOff && elabOk Tests.S23Direct.splitOff)
  = true := by native_decide

/-! ## §C. `quicksort` — the flagship, and the case that fixed the elaboration

    `quicksort`'s `match fuel` is NESTED: inside `match l`'s `Cons` branch, after a
    `let`, and its `Nil` branch never mentions fuel at all. That is what ruled out
    "split the body at its `match k`" and forced the elaboration to be **the whole
    body twice, with `match k` resolved per arm** — which is the ι rule read
    backwards, and is uniform over where the match sits.

    Read the base arm to see it work: it is the entire body with the fuel match
    replaced by its `Z` branch, so the `Nil` case still returns its pair and the
    `Cons` case becomes `botElim Unit hfuel` — the dead path, discharged because
    `hfuel : Le (S (len rest)) Z` IS `Bot`. Nothing about that is special-cased. -/

def qsTable : List Decl := [Tests.S23Direct.partition, Tests.S23Direct.appendBack]

example : elabOk Tests.S23Direct.quicksort qsTable = true := by native_decide
-- The declared twin, still checked against a table that still contains it (J1).
example : checkFnOk Tests.S23Direct.quicksort
  [Tests.S23Direct.partition, Tests.S23Direct.appendBack, Tests.S23Direct.quicksort]
  = true := by native_decide

/-- **The `[k]` guard is GONE from the elaborated form, and nothing replaces it.**
    The macro's output resolves its own recursion through `ih`, so the table it is
    checked against need not contain it — there is no self-call left to admit at a
    postcondition, and therefore nothing for a decrease check to police. §7's
    "the guard evaporates", as the absence of an entry. -/
example : (match elabIn Tests.S23Direct.quicksort with
           | .ok c => (calleeNames c.body).contains "quicksort"
           | .error _ => true) = false := by native_decide

/-! ## §D. What the macro refuses, and why each refusal is the honest one -/

-- §12 decision 8. `partition [v]` decreases through a BORROW's payload, which has
-- no recursor form — §9's eliminator is filed, not built. Fuel is something a
-- programmer threads (it changes the signature, and every caller); a macro that
-- invented it would be changing the function's interface behind its author.
example : elabRejects Tests.S23Direct.partition "decision 8" = true := by native_decide

-- §6.2's declared backs are a `Decl` mechanism with no seal counterpart. M23's
-- corpus declares none, which is why the cohort is unaffected.
-- Built with `Decl.mk` positionally: `back` is a `decl{}` surface token, so it
-- cannot be written as a field name here.
def withBack : Decl :=
  Decl.mk pushD.name pushD.telescope pushD.retType pushD.body (some (.const "Unit")) none
example : elabRejects withBack "backward spec" = true := by native_decide

end Dllbc.Tests.S26Fn
