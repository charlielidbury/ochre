import Dllbc.Boundary
import Dllbc.ProgMacro
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

**Written as programs** (M28 θ). `fn` is a statement, so a test is a program that
declares what it needs and then runs something. The shared callee is factored the
way any shared prefix is — a Lean function taking the rest of the block and
splicing it with `%`, which is let-chain composition and needs no mechanism.
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S6Call

/-- `push (e : Nat, v : &mut List Nat)` from §4.1/M5, as a PREFIX: everything
    below is written as `withPush (prog{ … })` and gets `push` in scope. -/
def withPush (rest : Term) : Term := prog{
  fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  %rest }

/-! ## §5.3 the wire: consume and promise -/

-- `push(7, b)` consumes b and annotates its loan owed `List Nat`; the later
-- `let y = x` ends the owed loan by minting a fresh σ. y is that σ, typed a
-- list — not the concrete `Cons 7 (Cons 1 Nil)`. "The spec is the type."
example : tailEnv (withPush (prog{
    let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () }))
  [("x", .bot), ("b", .bot), ("y", .sym 0)] = true := by native_decide

/-! ## The recursive cursor (§2.5's promised counterpart) -/

-- `zero_all (v : &mut List Nat) = match v { Nil => (), Cons(hd, tl) => {
--    *hd := 0; zero_all(tl); () } }` — the `[v]` payload-decrease shape, §7 cost
-- 4's own example: a cursor with no decreasing argument but the payload.
--
-- **IT HAS NO RECURSOR FORM, and the refusal is what this file asserts about it.**
-- §7 elaborates `[k]` to `natRec`/`listRec` over the parameter itself, and a borrow
-- is neither; §9's borrow-mode eliminator is FILED, not built. §12 decision 8
-- accepted the regression and blessed fuel-threading — a source change, since the
-- signature grows a parameter and a bound and every caller supplies them. The paid
-- twin is `S26Fuel.zeroAllF`, literally this function with a fuel parameter, and it
-- checks.
--
-- It was a `decl{ }` until M28 D6, because it was `S26Migrate.p6` — the whole of
-- this file's pool — and `S27Dispose` §B's residue list read the name "zero_all"
-- off it. Written as a program the decline is said directly, which is strictly more
-- than a name in a computed list: a needle no other error produces, the decision's
-- own words, and the fact that the sentinel fires at the BINDING rather than at a
-- call, so a refused function nothing calls still fails.
def zeroAll : Term := prog{
  fn zero_all [v] (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => { *hd := 0; zero_all(tl); () }
    } };
  () }
example : progRejects zeroAll FnMacro.fnRefusedNeedle = true := by native_decide
example : progRejects zeroAll "§12 decision 8" = true := by native_decide
example : progOk zeroAll = false := by native_decide

/-! ## Type-changing ↝, exercised at last -/

-- `to_nat (v : &mut (s : Bool ↝ Nat))` — callee takes the Bool through v and
-- fills a Nat; the audit passes against the OWED type Nat, not the entry Bool.
-- Named because `S27Mixed` §E asserts it too, as one of the two subjects in the
-- corpus that state a rich owed type.
def toNatProg : Term := prog{
  fn to_nat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  () }
example : progOk toNatProg = true := by native_decide

-- Caller side: borrow a `True`, call, read the owner back — it ends as a fresh
-- σ : Nat. A strong update across a boundary, both sides. The caller is a `fn`
-- too, so what is checked is the declaration and not one run of it.
example : progOk (prog{
  fn to_nat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  fn caller () -> Nat { let x = True; let b = &mut x; to_nat(b); let y = x; y };
  () }) = true := by native_decide

/-! ## Reborrow at a call site -/

-- `push(7, &mut *b)` — the reborrow Rust inserts silently; the child loan gets
-- the owed annotation and the parent recovers when it ends.
--
-- Written as ONE chain rather than `withPush (prog{ fn caller … })`: a spliced
-- tail may not declare functions, because both chains number their slots from
-- `progBase` and the inner would shadow `push`. `bindFn` refuses it — which is how
-- this line was found, having been written the wrong way first and passed green.
example : progOk (prog{
  fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  fn caller () -> List Nat { let x = Cons(1, Nil); let b = &mut x; push(7, &mut *b); let y = x; y };
  () }) = true := by native_decide

/-! ## Rejections -/

-- Argument type mismatch: push a `True` where a `Nat` is owed.
example : progRejects (withPush (prog{
    let x = Cons(1, Nil); let b = &mut x; push(True, b); () }))
  "parameter type" = true := by native_decide

-- A non-borrow where a borrow argument is expected.
example : progRejects (withPush (prog{ let x = Cons(1, Nil); push(7, x); () }))
  "expected a borrow argument" = true := by native_decide

-- Calling an unknown function.
example : progRejects (prog{ nope(); () }) "unknown function" = true := by native_decide

-- Using the consumed borrow variable after the call (it is ⊥).
example : progRejects (withPush (prog{
    let x = Cons(1, Nil); let b = &mut x; push(7, b); let z = b; () }))
  "use-after-move" = true := by native_decide

end Dllbc.Tests.S6Call
