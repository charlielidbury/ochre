import Ochr.Meaning.Places
import Ochr.Examples.Nat
import Ochr.Examples.Logic

/-!
# A read into a dependent field of an open value, made open by a write (built; the checker's verdicts)

docs/31 D32 (fifth lead, 2026-11-20). With `WP := MkWP(n : Nat, x : Pk(n))` and
`Pk(n) := MkPk(a : Fin1N(n), b : Nat)` as in `PartialMoveDep`:

* `OWK` (ACCEPTED): `w = MkWP(S(w0), y)`; the index is rewritten whole, `w.0 := S(S(Z))`, so `w`
  is open (D64): `w.1` holds a `Pk(S(w0))` while its type from the earlier fields is `Pk(2)`; then
  `(w.1).1` is read. The checker types `w.1` by its content.
* `OW`, `OWM`: the same at an unknown `w`. Rejected until main's D93 (the projection's one-arm
  match closed off as a stuck block whose arm returned `w` open, [Repack]); ACCEPTED since: a match
  on a one-constructor type refines `w` in place and runs its arm directly, so `w` stays open
  after it, as `OWK`'s does, and nothing after relies on `w`'s type (D93: a lie is caught at the
  next whole-again point, and there is none).

Before docs/31 D32 the reference decoded `w.1` at the hint its declaration gives at the current
earlier fields, `Pk(2)`, where the value was packed at `Pk(S(w0))`: at `w0 ≠ 1` the two parameter
lists differ, and decoding through equal carriers is not provably the value's own. So reading into
an open value's dependent field was beyond decoding by the position's type, whatever the join does:
(WF13) as restricted to fields after whole earlier fields was FALSE here, and tightening the join's
drop (D32 option (d)) does not reach this case.

Fixed by D32: the reference reads `(w.1).1` off `w`'s meaning, and types `w.1` by its content
(`Pk` at its own parameters, as the checker does), for every data model (`read_after_index_rewritten`,
kernel-checked).
-/

open Ochr.Test

ochr OpenWriteDep uses Nats, Logic {
  inductive One := O
  def Fin1N (n : Nat) : Type := match n { Z => Void, S m => One }
  inductive Pk (n : Nat) := MkPk(a : Fin1N(n), b : Nat)
  inductive WP := MkWP(n : Nat, x : Pk(n))
  def OWK (w0 : Nat) (y : Pk(S(w0))) : Nat := (let w = MkWP(S(w0), y); w.0 := S(S(Z)); let c = (w.1).1; c)
  def OW (w : WP) : Nat := (w.0 := S(S(Z)); let c = (w.1).1; c)
  def OWM (w : WP) : Nat := (w.0 := S(S(Z)); match w.1 { MkPk(a, b) => b })
}

namespace Ochr.Meaning.Regress.OpenWriteDep
open Ochr Ochr.Meaning

/-- **The read of `(w.1).1` after `w.0` is rewritten, in the reference** (D32): `w` means
`MkWP(2, MkPk(a, b))` whatever its element (whole and of its type or open); the read reaches `b`,
and `w.1` is typed by its content, `Pk` at its own parameter `m` (`dataTyS`). -/
theorem read_after_index_rewritten (dm : DataModel) (Γ : List IndDecl) (T : TyS) (m a b : Sem)
    (el el' : Option ((A : Type) × A)) :
    Sem.step dm Γ T (.proj 1) (.dat "WP" [] 0 [.el0 Nat 2, .dat "Pk" [m] 0 [a, b] el] el') =
      some (.dat "Pk" [m] 0 [a, b] el, dataTyS dm Γ "Pk" [m]) ∧
    ∃ T', Sem.follow dm Γ T (.dat "WP" [] 0 [.el0 Nat 2, .dat "Pk" [m] 0 [a, b] el] el') [.proj 1, .proj 1] =
      some (b, T') := ⟨rfl, _, rfl⟩

end Ochr.Meaning.Regress.OpenWriteDep
