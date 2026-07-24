import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro

/-!
# §18 test suite — the rewriting layer

The next ergonomics layer after the M15 recursor sugar, and the fix for the M16
`count_swapL` wall: the count-preservation algebra needed motives that abstract a
computed subterm (`eqb m a`) at EVERY occurrence, hand-written and error-prone.
The mechanism is `abstractOccurrences` — syntactic subterm abstraction at the
`Term` level, post-elaboration, de Bruijn-correct under binders — with a
round-trip guarantee: `(λx. abstractOccurrences e t) e` β-reduces back to `t`.
No matching by eye, no missed occurrence, no tactic engine.
-/

open Dllbc

namespace Dllbc.Tests.S18Rewrite

def eqbA (a b : Term) : Term := .app (.app Std.eqbFnT a) b
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-- The round-trip property: abstracting `e` out of `t` and applying it back
    recovers `t` (by conversion). -/
def roundTrips (e t : Term) : Bool :=
  let applied := Term.app (Term.lam (.const "Bool") (abstractOccurrences e t)) e
  match (do let a ← readC 2000 applied; let b ← readC 2000 t; pure (Val.convert 2000 a b)).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## `abstractOccurrences` round-trips (the mechanism, unit-tested) -/

-- Two occurrences at the top level.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (eqbA (tnat 1) (tnat 2))) = true := by native_decide
-- An occurrence under a binder — `e` shifted, the bound var and free vars kept straight.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.lam (.const "Nat") (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.pvar 0))) = true := by native_decide
-- No occurrence: `t` is unchanged (the binder is vacuous).
example : roundTrips (eqbA (tnat 1) (tnat 2)) (.idT (.const "Nat") (tnat 3) (tnat 3)) = true := by native_decide
-- The same subterm at DIFFERENT binder depths — both abstracted correctly.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.lam (.const "Nat") (eqbA (tnat 1) (tnat 2)))) = true := by
  native_decide

/-! ## The `generalizing` surface form — motive by auto-abstraction

    `elim SCRUT generalizing GOAL { arms }` forms the motive by NF-ing the goal
    (so a computed subterm hidden in a definition — `eqb` inside `count` — is
    exposed) and abstracting SCRUT at every occurrence. The user writes the
    NATURAL goal; the macro places the holes, mechanically. -/

def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.Std (eqbFnT addFnT countFnT) in
-- Casing on `eqb m a` makes two syntactically-different sides converge per branch
-- (`add Z X ≡ X`). The macro abstracts `eqb m a` at both occurrences; both Refl.
example : chk
  (pure{ λ (m : Nat). λ (a : Nat).
    elim (eqbFnT m a) generalizing
      (Id Nat (boolRec (λ (w : Bool). Nat) (S Z) Z (eqbFnT m a))
              (boolRec (λ (w : Bool). Nat) (addFnT Z (S Z)) (addFnT Z Z) (eqbFnT m a))) {
      True => Refl, False => Refl } })
  (pure{ Π (m : Nat) → Π (a : Nat) →
    Id Nat (boolRec (λ (w : Bool). Nat) (S Z) Z (eqbFnT m a))
           (boolRec (λ (w : Bool). Nat) (addFnT Z (S Z)) (addFnT Z Z) (eqbFnT m a)) }) = true := by native_decide

open Dllbc.Std (eqbFnT countFnT) in
-- The subterm hidden in `count`: the NATURAL goal (no unfolding) works because
-- the macro NF's it to expose `eqb m a` before abstracting.
example : chk
  (pure{ λ (m : Nat). λ (a : Nat). λ (l : List Nat).
    elim (eqbFnT m a) generalizing (Id Nat (countFnT m (Cons a l)) (countFnT m (Cons a l))) {
      True => Refl, False => Refl } })
  (pure{ Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) →
    Id Nat (countFnT m (Cons a l)) (countFnT m (Cons a l)) }) = true := by native_decide

/-! ## cons2_comm — the report card (M16 ~18 hand-motive lines → ~8 here)

    Count is invariant under swapping two adjacent heads. The outer `generalizing`
    takes the NATURAL goal; the True arm nests a `generalizing` whose goal is the
    outer-True instance (a `boolRec` form — the residual the branch-hypothesis
    layer will make natural); every leaf is `Refl`; the False arm collapses to
    `Refl` outright. The macro abstracts `eqb` at every occurrence, so the M16
    missed-occurrence bug cannot recur. -/

open Dllbc.Std (eqbFnT countFnT) in
example : chk
  (pure{ λ (m : Nat). λ (a : Nat). λ (b : Nat). λ (l : List Nat).
    elim (eqbFnT m a) generalizing (Id Nat (countFnT m (Cons a (Cons b l))) (countFnT m (Cons b (Cons a l)))) {
      True => elim (eqbFnT m b) generalizing
        (Id Nat (S (countFnT m (Cons b l)))
                (boolRec (λ (w : Bool). Nat) (S (S (countFnT m l))) (S (countFnT m l)) (eqbFnT m b))) {
        True => Refl, False => Refl },
      False => Refl } })
  (pure{ Π (m : Nat) → Π (a : Nat) → Π (b : Nat) → Π (l : List Nat) →
    Id Nat (countFnT m (Cons a (Cons b l))) (countFnT m (Cons b (Cons a l))) }) = true := by native_decide

/-! ## rewrite-by-Id — the branch-equation / knowledge layer

    Given an equation as an ORDINARY Id hypothesis, transport a proof by it via J
    with the abstractOccurrences motive. The essential use (which the abstraction
    layer CANNOT do — the subterm hides behind the scrutinee's own reduction):
    resolve a STUCK `count m (Cons a l)` using a RECEIVED equation `eqb m a =
    True`. This is what the count_swapL stack chains; here as the calculus-honest
    j+id_sym+abstractOccurrences construction. -/

open Dllbc.Std (eqbFnT countFnT) in
open Dllbc.StdLemmas (id_sym) in
example : chk
  (pure{ λ (m : Nat). λ (a : Nat). λ (l : List Nat). λ (hq : Id Bool (eqbFnT m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (countFnT m l)) (countFnT m l) z) (S (countFnT m l)))
      Refl (eqbFnT m a) (id_sym Bool (eqbFnT m a) True hq) })
  (pure{ Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) → Id Bool (eqbFnT m a) True →
    Id Nat (countFnT m (Cons a l)) (S (countFnT m l)) }) = true := by native_decide

end Dllbc.Tests.S18Rewrite
