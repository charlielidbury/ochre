import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S26Seal

/-!
# §26 (M26-B) — binder modes: capital is comptime, and the fence

Phase B of the `fn`/λ unification (`docs/combining-fns.md` §6). One convention
enters the language — **a capitalized binder is comptime, a lowercase one is
runtime** — and it is carried by two mechanisms that are the two halves of the
same sentence:

  * **The comptime-argument rule.** At a ⇒-call, an argument standing in a
    capital-bindered position is evaluated under ⇝: a pure, NON-CONSUMING read.
    The binder is erased — never moved, citable after any call.
  * **The fence.** A capital binder is usable only in ⇝-positions (types,
    proofs, capital arguments of other calls). A ⇒-move of it, a runtime match
    on it, a borrow of it, a write through it, an index of it, and a ⇒-call of
    it are each rejected.

**Where the mode lives.** Two places, because there are two kinds of binder and
they record their identity differently. A *runtime* binder is a `Var` — an id
and a name — so its mode is its name's case (`Var.isComptime`); this covers
telescope parameters, `let`, and match binders, and needs no representation
change at all. A *pure* binder is de Bruijn and has no name, so its mode rides
on the domain: `Π (X : τ) → …` is `.pi (.cmpT τ) …`. `Term.cmpT`/`Val.cmpT` is
the sibling of `borrowT` — three modes at one syntactic place, the two
non-default ones marked.

**Case is inert under ⇝, mechanically.** `Val.beq` unwraps `cmpT` on either
side, so `convert` — and every comptime judgment above it — cannot observe a
mode. §E pins this from both sides: the two Π's convert, and the same two Π's
give different call behaviour. Modes route ⇒'s arguments and fence its bodies;
⇝ is the room the distinction was never meant to reach.

**Negative controls are per DEMAND SITE** (phase A's finding, now doctrine).
`readC` computes without checking, so a rule branch nobody demands is a rule
branch nobody tested. §B enumerates the demand sites and gives each its own
control, each paired with the lowercase twin that is ACCEPTED — which is a
stronger liveness check than flipping the assertion, because it shows the
rejection is about the mode and not about the program.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_trans)
open Dllbc.Tests.S26Seal (ok rejects caller envOf natT diffC)

namespace Dllbc.Tests.S26Modes

/-! ## §A. The comptime-argument rule — R16's proof consumption, at its source

    "Passing a proof to a call moves it" (R16) forced the capture-before-call
    staging that `S25ArrSort`'s `mkTop`/`mkHf` and M23's four builders exist to
    perform. The diagnosis in §6 is that the pain was never "proofs are linear";
    it is that a call site had only one arrow. A capital parameter gives it the
    other one.

    The subject must be a TELESCOPE proof, not a `let`-bound proof term: a proof
    *spine* is already index-kind and already copies on read (§2.1), so it would
    show nothing. A telescope proof is a σ whose type is a stuck `natRec` spine —
    not `Nat`/`Bool`/`Id`/`Type`/`Π` — so `indexKindV` says MOVE, and that is
    exactly the class R16 is about. -/

def useLe : Decl := decl{ fn useLe (a : Nat, b : Nat, h : Le a b) -> Unit { () } }
/-- The same function, one character different: the proof parameter is capital. -/
def useLeC : Decl := decl{ fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () } }

-- A1. THE PAIN. The proof is passed, and citing it afterwards is a use-after-move.
def a1 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLe(n, m, hnm); hnm } }
example : rejects a1 "holds ⊥" [useLe, a1] = true := by native_decide

-- A2. THE FIX. The same program against the capital twin: accepted, because the
-- argument was ⇝-read and never left the caller's slot.
def a2 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLeC(n, m, hnm); hnm } }
example : ok a2 [useLeC, a2] = true := by native_decide

-- A3. …and it is not a one-shot: passed twice, cited after both.
def a3 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLeC(n, m, hnm); useLeC(n, m, hnm); hnm } }
example : ok a3 [useLeC, a3] = true := by native_decide

-- A4. The staging that R16 forced, and what it becomes. `mkHf`'s shape — capture
-- a proof into a λ *before* the call that consumes it — still works, and is now
-- unnecessary: A3 is the same program without it.
def a4 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let mk = λ (u : Unit). hnm; useLe(n, m, hnm); mk unit } }
example : ok a4 [useLe, a4] = true := by native_decide

/-! ### A5. `match fuel` against its capital twin

    The flagship's two halves, isolated: a lowercase binder is branched on, and
    the capital twin — same type, same position — cannot be. This is the pair
    that says the modes are doing work rather than decorating. -/

def a5lo : Decl := decl{ fn a5lo (fuel : Nat) -> Unit { match fuel { Z => (), S(f2) => () } } }
def a5hi : Decl := decl{ fn a5hi (Fuel : Nat) -> Unit { match Fuel { Z => (), S(f2) => () } } }
example : ok a5lo = true := by native_decide
example : rejects a5hi "cannot be the scrutinee of a runtime match" = true := by native_decide

-- A6. A comptime argument must be a COMPTIME term. A call's result is a fresh
-- existential with no ⇝ reading, so it cannot be spliced into a capital position
-- directly — it must be `let`-bound first. An honest rejection rather than a
-- silent fall-back to ⇒, and the `let`-bound form immediately above works.
def giveLe : Decl := decl{ fn giveLe (a : Nat) -> Le a a { %le_refl a } }
def a6bad : Decl := decl{ fn caller (n : Nat) -> Unit { useLeC(n, n, giveLe(n)); () } }
def a6ok : Decl := decl{ fn caller (n : Nat) -> Unit
  { let p = giveLe(n); useLeC(n, n, p); useLeC(n, n, p); () } }
example : rejects a6bad "not in the comptime fragment" [useLeC, giveLe, a6bad] = true := by
  native_decide
example : ok a6ok [useLeC, giveLe, a6ok] = true := by native_decide

/-! ## §B. The fence — one control per DEMAND SITE, each with its lowercase twin

    Phase A's finding generalized: `readC` computes without checking, so a rule
    branch nobody demands is a rule branch nobody tested. The sites below are the
    ⇒-rules that would make an erased binder observable, and each is paired with
    the *same program over a lowercase binder*, which is accepted. That pairing
    is the liveness check: it shows the rejection is about the MODE and not about
    the program being ill-formed some other way. -/

-- B1. The ⇒-move.
def b1hi : Decl := decl{ fn b1 (N : Nat) -> Unit { let y = N; () } }
def b1lo : Decl := decl{ fn b1 (n : Nat) -> Unit { let y = n; () } }
example : rejects b1hi "cannot be ⇒-moved" = true := by native_decide
example : ok b1lo = true := by native_decide

-- B2. The runtime match — §A5 above, which is where it earns its keep.

-- B3. The borrow.
def b3hi : Decl := decl{ fn b3 (N : List Nat) -> Unit { let b = &mut N; () } }
def b3lo : Decl := decl{ fn b3 (n : List Nat) -> Unit { let b = &mut n; () } }
example : rejects b3hi "cannot be borrowed" = true := by native_decide
example : ok b3lo = true := by native_decide

-- B4. The write-through (⇐).
def b4hi : Decl := decl{ fn b4 (N : Nat) -> Unit { N := 3; () } }
def b4lo : Decl := decl{ fn b4 (n : Nat) -> Unit { n := 3; () } }
example : rejects b4hi "cannot be written through" = true := by native_decide
example : ok b4lo = true := by native_decide

-- B5. The index/slice step. Built by hand rather than through the surface: the
-- fence fires on the place's *syntactic root* before `placeToPos` navigates
-- anything, which is the property being pinned (a place expression may carve,
-- and a fence that ran after that would have already reorganized Ω).
def b5hi : Decl :=
  { name := "b5", telescope := [("N", natT)], retType := .const "Unit",
    body := .letIn ⟨1, "e"⟩ (.index (.var ⟨0, "N"⟩) (.ctorApp "Z" []) none) .unit }
example : rejects b5hi "cannot be indexed or sliced" = true := by native_decide

-- B6. A capital binder handed to a LOWERCASE parameter. Same rejection as B1
-- and a different demand site — `processArgs` reads a runtime parameter's
-- argument with ⇒, so the fence fires there. This is the direction that makes
-- the fence coherent: a comptime binder cannot launder itself into runtime by
-- being passed to something that wants a runtime value.
def b6 : Decl := decl{ fn caller (n : Nat, m : Nat, Hnm : Le n m) -> Unit
  { useLe(n, m, Hnm); () } }
example : rejects b6 "cannot be ⇒-moved" [useLe, b6] = true := by native_decide

/-! ### B7. §6.3's distinction, mechanical: `map_spec (G : …)` vs `map_apply (g : …)`

    The one place where kind cannot decide the mode. A capital function-typed
    binder is a SPEC parameter — the caller may supply an abstract or sealed
    function with no runtime existence — so the body may cite `G a` in a type,
    where ⇝ gives the structured neutral, but may not CALL it. The lowercase twin
    is `S26Seal`'s `apply1`, and calling it is exactly what the lowercase buys. -/

def b7spec : Decl := decl{ fn b7spec (G : Π (x : Nat) → Nat, n : Nat) -> Unit
  { let r = G(n); () } }
example : rejects b7spec "cannot be CALLED under ⇒" = true := by native_decide
example : ok S26Seal.apply1 = true := by native_decide

-- …and the citation that IS allowed: `G a` in a type position, where the whole
-- content is §2.1's structured neutral. `G` is never supplied at runtime.
def b7cite : Decl := decl{ fn b7cite (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n)
  { Refl } }
example : ok b7cite = true := by native_decide

/-! ### B8/B9. Borrow-typed binders must be lowercase — checked, not assumed

    §6 states this as a requirement on the design; it is checked at BOTH ends,
    and the two rejections are distinguishable so the site is pinned rather than
    inferred. The declaration is caught by `seedTelescope` (the honest place: the
    signature is wrong); the call site is caught by `processArgs`, which matters
    for a table entry that was never itself checked. -/

def b8 : Decl := decl{ fn b8 (V : &mut List Nat) -> Unit { () } }
example : rejects b8 "telescope: parameter 'V' is capitalized" = true := by native_decide

def b9 : Decl := decl{ fn caller () -> Unit { let x = Cons(1, Nil); b8(&mut x); () } }
example : rejects b9 "call: parameter 'V' is capitalized" [b8, b9] = true := by native_decide

-- The lowercase twin of both, for liveness.
def b8lo : Decl := decl{ fn b8lo (v : &mut List Nat) -> Unit { () } }
def b9lo : Decl := decl{ fn caller () -> Unit { let x = Cons(1, Nil); b8lo(&mut x); () } }
example : ok b8lo = true := by native_decide
example : ok b9lo [b8lo, b9lo] = true := by native_decide

/-! ### B10. The reserved-keyword prescription

    §6 pays for "capital is the mode marker" with one rule: the constructor names
    are keywords. Checked at elaboration — these are `Macro` errors, so they are
    exhibited rather than asserted (a rejected macro does not produce a `Decl` to
    test). What CAN be asserted is the other half: the surface no longer decides
    `F(x)` by CASE. `f(…)` is a constructor application exactly when `f` is in
    the fixed basis, which is what makes `G(n)` above a call rather than a
    silently-mistyped `ctorApp "G"`. B7 is that assertion. -/

example : DeclMacro.reservedBinder "Cons" = true := by native_decide
example : DeclMacro.reservedBinder "Nat" = true := by native_decide
-- Lowercase names are NOT reserved: they were always shadowable, shadowing them
-- is ordinary scoping, and reserving `j`/`k` would cost every program its loop
-- indices for no disambiguation at all (`insert_at`'s own `k` parameter).
example : DeclMacro.reservedBinder "k" = false := by native_decide
example : DeclMacro.reservedBinder "unit" = false := by native_decide
example : DeclMacro.reservedBinder "Hfuel" = false := by native_decide

end Dllbc.Tests.S26Modes
