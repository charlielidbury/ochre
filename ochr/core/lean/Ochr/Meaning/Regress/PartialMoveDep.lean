import Ochr.Meaning.Places
import Ochr.Examples.Nat
import Ochr.Examples.Logic

/-!
# A join drop into a dependent field after its index is moved (built; the checker's verdicts)

docs/31 D32 (fifth lead, 2026-11-20). `WP := MkWP(n : Nat, x : Pk(n))`: field `x`'s type is a
declared one-constructor inductive at a parameter read from the index `n` (not a copy type).
`Pk(n) := MkPk(a : Fin1N(n), b : Nat)`, and `Fin1N(n)` is computed from `n`.

* `JK` (ACCEPTED): the match on the known `Z` runs the arm that moves `w.0`; the other arm moves
  `(w.1).1`, so the join drops `(w.1).1` in the first arm's end state, where `w.0` is `⊥`. The
  checker drops it (`movedPlace`, `dropAtJoin`: no type is computed).
* `JKRead`, `Direct` (rejected, the controls): reading or moving into `w.1` after `w.0` is moved
  computes `w.1`'s type `Pk(w.0)`, which reads `⊥`.

Before docs/31 D32 the reference found its way into `w.1` by the hint its declaration gives field 1
at the earlier fields' current meanings: `Pk` at the parameter `moved`. In any data model whose
field types are the run's readings (`FieldsFaithful`), `Fin1N(moved)` means `err`, so `Pk(moved)`
has no element, its carrier is not `w.1`'s, and `Sem.follow` failed: the reference's drop did
nothing where the checker's writes `⊥` at `(w.1).1`, and `dropOne_step` was false at this state.

Fixed by D32: a constructor value describes itself, so the reference reads `w.1` off `w`'s meaning
and writes `moved` at `(w.1).1`, for every data model, whatever `w.1`'s declared type reads
(`drop_after_index_moved`, kernel-checked): the meaning the checker's `MkWP(⊥, MkPk(a, ⊥))` has. (Generic `k`: rejected,
`J5`'s message; at `S(Z)` the other arm runs and the join drops `w.0`, which is harmless.)
-/

open Ochr.Test

ochr PartialMoveDep uses Nats, Logic {
  inductive One := O
  def Fin1N (n : Nat) : Type := match n { Z => Void, S m => One }
  inductive Pk (n : Nat) := MkPk(a : Fin1N(n), b : Nat)
  inductive WP := MkWP(n : Nat, x : Pk(n))
  def JK (w : WP) : Nat := (let k = Z; match k { Z => (let a = w.0; Z), S j => (let c = (w.1).1; Z) }; Z)
  reject def JKRead (w : WP) : Nat := (
    let k = Z; match k { Z => (let a = w.0; Z), S j => (let c = (w.1).1; Z) }; let d = (w.1).0; Z)
  reject def Direct (w : WP) : Nat := (let a = w.0; let c = (w.1).1; Z)
  reject def JGen (w : WP) (k : Nat) : Nat := (match k { Z => (let a = w.0; Z), S j => (let c = (w.1).1; Z) }; Z)
}

namespace Ochr.Meaning.Regress.PartialMoveDep
open Ochr Ochr.Meaning

/-- **The join's drop of `(w.1).1` after `w.0` is moved, in the reference** (D32): `w` means
`MkWP(⊥, MkPk(a, b))` (partly moved, so no element), and writing `moved` at `.1.1` reads the value
alone and gives `MkWP(⊥, MkPk(a, ⊥))`, for every data model, declarations and parameters. -/
theorem drop_after_index_moved (dm : DataModel) (Γ : List IndDecl) (T : TyS) (n a b : Sem)
    (el : Option ((A : Type) × A)) :
    Sem.updAt dm Γ T (fun _ => .moved) [.proj 1, .proj 1]
        (.dat "WP" [] 0 [.moved, .dat "Pk" [n] 0 [a, b] el] none) =
      some (.dat "WP" [] 0 [.moved, .dat "Pk" [n] 0 [a, .moved] none] none) := by
  rw [Sem.updAt_dat' dm Γ T _ (.proj 1) [.proj 1] (by simp) (by decide) (fi := .dat "Pk" [n] 0 [a, b] el) rfl,
    Sem.updAt_dat' dm Γ T _ (.proj 1) [] (by simp) (by decide) (fi := b) rfl]
  have e0 : Sem.updAt dm Γ T (fun _ => .moved) [] b = some .moved := by rw [Sem.updAt.eq_def]
  rw [e0]
  simp only [Option.map_some, Step.fieldIdx, List.set_cons_succ, List.set_cons_zero]
  rw [reDat_moved dm Γ "Pk" [n] 0 [a, .moved] (by simp),
    reDat_moved dm Γ "WP" [] 0 [.moved, .dat "Pk" [n] 0 [a, .moved] none] (by simp)]

end Ochr.Meaning.Regress.PartialMoveDep
