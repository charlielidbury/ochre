import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.DeclMacro
import Dllbc.Migrate

/-!
# §5.3 test suite — calls as wires

Declared functions called from bodies, checked against the SIGNATURE alone
(never another body — recursion forces this). A borrow argument is consumed
and its loan annotated *owed* the type the callee promises; ending an owed loan
mints a fresh existential at that type ("the promise is collected"). A wire is
the degenerate loan group (§6.1); groups proper are M7.

Two headline tests. **The recursive cursor** `zero_all` is §2.5's rejection's
promised counterpart: the cursor written recursively, the tail borrow passed as
an *argument* — the recursive call annotates its loan owed, and the audit's
collapse mints the existential, so no overwrite and nothing to ghost. And the
**§5.3 wire**: after `push(7, b)`, reading the owner back gives a fresh σ typed
`List Nat`, NOT `Cons 7 (Cons 1 Nil)` — the imprecision is the point, the spec
is the type.
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S6Call

/-- `push (e : Nat, v : &mut List Nat)` from §4.1/M5. -/
def pushList : Decl :=
  decl{ fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () } }

/-! ## §5.3 the wire: consume and promise -/

-- `push(7, b)` consumes b and annotates its loan owed `List Nat`; the later
-- `let y = x` ends the owed loan by minting a fresh σ. y is that σ, typed a
-- list — not the concrete `Cons 7 (Cons 1 Nil)`. "The spec is the type."
def wireCaller : Decl :=
  decl{ fn caller () -> Unit { let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () } }

example : Migrate.progEnvOfT [pushList, wireCaller] wireCaller
  [("x", .bot), ("b", .bot), ("y", .sym 0)] = true := by native_decide

/-! ## The recursive cursor (§2.5's promised counterpart) -/

-- `zero_all (v : &mut List Nat) = match v { Nil => (), Cons(hd, tl) => {
--    *hd := 0; zero_all(tl); () } }` — checks end-to-end. The recursive call
-- consumes the reborrow `tl` and annotates ℓ_tl owed `List Nat`; at return the
-- audit collapses v, ending ℓ_hd normally and ℓ_tl as an existential, so
-- v holds `Cons 0 σ : List Nat`. No overwrite, nothing to ghost.
def zeroAll : Decl :=
  decl{ fn zero_all [v] (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => { *hd := 0; zero_all(tl); () }
    } } }

-- **STAYS ON THE DECLARATION PATH, and dies with it** (M27-γ). `zero_all` is the
-- `[v]` payload-decrease shape — §7 cost 4's own example, a cursor with no
-- decreasing argument but the payload — so `fnElab` declines it and there is no
-- program form to convert this to. §12 decision 8 accepted that regression and
-- blessed fuel-threading; the claim's carrier is `S26Fuel.zeroAllF`, asserted
-- `bothWays` there and again in `S27Dispose` §B. This assertion is therefore a
-- δ casualty rather than a coverage loss: it goes when `checkFn` does, and what
-- it was checking is already checked on both paths elsewhere.
example : checkFnOk zeroAll = true := by native_decide

/-! ## Type-changing ↝, exercised at last -/

-- `to_nat (v : &mut (s : Bool ↝ Nat))` — callee takes the Bool through v and
-- fills a Nat; the audit passes against the OWED type Nat, not the entry Bool.
def toNat : Decl :=
  decl{ fn to_nat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () } }

example : Migrate.progOkOf toNat = true := by native_decide

-- Caller side: borrow a `True`, call, read the owner back — it ends as a fresh
-- σ : Nat. A strong update across a boundary, both sides.
def toNatCaller : Decl :=
  decl{ fn caller () -> Nat { let x = True; let b = &mut x; to_nat(b); let y = x; y } }

example : Migrate.progOkOf toNatCaller [toNat, toNatCaller] = true := by native_decide

/-! ## Reborrow at a call site -/

-- `push(7, &mut *b)` — the reborrow Rust inserts silently; the child loan gets
-- the owed annotation and the parent recovers when it ends.
def rbCaller : Decl :=
  decl{ fn caller () -> List Nat { let x = Cons(1, Nil); let b = &mut x; push(7, &mut *b); let y = x; y } }

example : Migrate.progOkOf rbCaller [pushList, rbCaller] = true := by native_decide

/-! ## Rejections -/

-- Argument type mismatch: push a `True` where a `Nat` is owed.
example : Migrate.progRejectsOf
  (decl{ fn c () -> Unit { let x = Cons(1, Nil); let b = &mut x; push(True, b); () } })
  "parameter type" [pushList] = true := by native_decide

-- A non-borrow where a borrow argument is expected.
example : Migrate.progRejectsOf
  (decl{ fn c () -> Unit { let x = Cons(1, Nil); push(7, x); () } })
  "expected a borrow argument" [pushList] = true := by native_decide

-- Calling an unknown function.
example : Migrate.progRejectsOf
  (decl{ fn c () -> Unit { nope(); () } })
  "unknown function" [] = true := by native_decide

-- Using the consumed borrow variable after the call (it is ⊥).
example : Migrate.progRejectsOf
  (decl{ fn c () -> Unit { let x = Cons(1, Nil); let b = &mut x; push(7, b); let z = b; () } })
  "use-after-move" [pushList] = true := by native_decide

end Dllbc.Tests.S6Call
