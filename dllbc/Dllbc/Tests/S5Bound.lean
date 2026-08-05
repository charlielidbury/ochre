import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.DeclMacro
import Dllbc.Migrate

/-!
# §5 test suite — boundaries, and the two flagships

The milestone the calculus has been aiming at: `checkFn` seeds a telescope,
explores the body, and audits each path at return (§5.4). At its end the
machine is a type checker, and it checks the two flagship programs — the thing
no other artifact in this space does. Monomorphic at `T := Nat` throughout.

The headline is the **money test**: the Σ-paired `VecF` push with the length
update forgotten is REJECTED, because the pair's second field must have type
`VecF Nat σₗ` — a stuck type the concrete value cannot inhabit. Dependent
correctness catches the off-by-one that the ownership machinery alone cannot.
-/

open Dllbc

namespace Dllbc.Tests.S5Bound

/-! ## Pure library (types as terms) -/

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
/-- `VecF T n = natRec (λ_.Type) Unit (λn'. λrec. Σ(_:T). rec) n`. -/
def vecFT : Term :=
  .lam .type (.lam natT
    (.app (.app (.app (.app (.const "natRec") (.lam natT .type)) (.const "Unit"))
      (.lam natT (.lam .type (.sigmaT (.pvar 3) (.pvar 1))))) (.pvar 0)))
/-- `Σ (l : Nat). VecF Nat l` — the self-describing length-vector pair. -/
def sigVecF : Term := .sigmaT natT (.app (.app vecFT natT) (.pvar 0))

/-! ## §4.1 List push, by take and rebuild -/

-- `push (e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () }`
-- — five lines Rust rejects (E0507), accepted here: the audit sees `Cons σₑ σ`
-- convert against `List Nat`.
def pushList : Decl :=
  decl{ fn push (e : Nat, v : &mut List Nat) -> Unit {
    let tail = *v;
    *v := Cons(e, tail);
    ()
  } }

example : Migrate.progOkOf pushList = true := by native_decide

-- Take without refill: the borrow holds a hole (⊥) at return — a function
-- cannot return one (§5.4).
example : Migrate.progRejectsOf (decl{ fn push (e : Nat, v : &mut List Nat) -> Unit {
    let tail = *v; () } })
  "take without refill" = true := by native_decide

-- Pushing a `True` onto a `List Nat`: the rebuilt payload fails its owed type.
example : Migrate.progRejectsOf
  (decl{ fn push (e : Nat, v : &mut List Nat) -> Unit {
    let tail = *v; *v := Cons(True, tail); () } })
  "owed type" = true := by native_decide

/-! ## §4.2 Vec push, in place (the dependent flagship) -/

-- `push (e, v : &mut Σ (l:Nat). VecF Nat l) { match v { Pair(l, xs) => {
--    *xs := Pair(e, *xs); *l := S(*l); () } } }` — both coupled fields updated
-- in place; the audit computes `VecF Nat (S σₗ)` under the (now concrete)
-- index and closes the pair.
def vecPush : Decl :=
  decl{ fn push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
    match v { Pair(l, xs) => { *xs := Pair(e, *xs); *l := S(*l); () } }
  } }

example : Migrate.progOkOf vecPush = true := by native_decide

-- THE MONEY TEST — forget `*l := S(*l)`: the length stays σₗ while the vector
-- became one longer, so the second field is checked against the STUCK type
-- `VecF Nat σₗ` and the concrete `Pair` cannot inhabit it. REJECTED. This is
-- dependent correctness catching the forgotten length update — the ownership
-- machinery makes the mutation safe, the dependent types make it correct.
example : Migrate.progRejectsOf
  (decl{ fn push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *xs := Pair(e, *xs); () } } } })
  "owed type" = true := by native_decide

-- Both write orders check: under the Σ/VecF encoding the constructor takes no
-- index argument, so — per §4.2's mechanization note — the order is NOT forced
-- and both are honest (unlike the native `VCons` presentation).
example : Migrate.progOkOf
  (decl{ fn push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *l := S(*l); *xs := Pair(e, *xs); () } } } }) = true := by
  native_decide

/-! ## σ-typing at branch entry, and an owned-symbolic function -/

-- A `Cons` pattern on a `&mut Nat`: the branch constructor does not belong to
-- the scrutinee's type (§3.2's seam). The `Z`/`S` branches make the match
-- exhaustive over Nat, so it is the σ-typing check (not exhaustiveness, §9)
-- that catches the stray `Cons` branch.
example : Migrate.progRejectsOf
  (decl{ fn f (b : &mut Nat) -> Unit { match b { Z => (), S(m) => (), Cons(h, t) => () } } })
  "does not belong" = true := by native_decide

-- Exhaustiveness (§9): a symbolic match must cover the scrutinee type's full
-- constructor set. is_zero missing its `S` branch is rejected.
example : Migrate.progRejectsOf
  (decl{ fn is_zero (n : Nat) -> Bool { match n { Z => True } } })
  "non-exhaustive" = true := by native_decide

-- A borrow-mode match on `&mut List Nat` missing its `Nil` branch is rejected.
example : Migrate.progRejectsOf
  (decl{ fn f (v : &mut List Nat) -> Unit { match v { Cons(hd, tl) => { *hd := 0; () } } } })
  "non-exhaustive" = true := by native_decide

-- `is_zero (n : Nat) → Bool`: an owned symbolic argument, both branches audited
-- against the return type.
example : Migrate.progOkOf
  (decl{ fn is_zero (n : Nat) -> Bool { match n { Z => True, S(m) => False } } }) = true := by
  native_decide

end Dllbc.Tests.S5Bound
