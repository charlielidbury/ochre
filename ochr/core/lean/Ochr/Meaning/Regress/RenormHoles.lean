import Ochr.Examples.Nat

/-!
# Re-normalisation and the loans of a fill: the worst case for the witness (built)

docs/31 D27, machine fact (a) (fourth lead, 2026-11-19). The loan witness survives a checker step
only if re-normalisation does not drop a loan whose label the reference still reads. Two kinds of
re-normalisation exist; the question is which can drop a loan.

* **After a loan is substituted (an [End]).** Every sealed program is made by `closeCall`, and the
  only loan it holds is its hole, as the value written through the returned borrow,
  `*r := loan_k`, after the stuck head call `C`, which cannot read it (read off `closeCall`; what
  an [End] substitutes for the hole lands in the same place). So substituting a loan never makes a
  stuck program compute: the re-run is stuck at `C` again, and the program keeps every loan but the
  one substituted. The exception would be an `Eq` type value holding a loan, which `mkEqM`
  recomputes (`Eq(A, (loan_k, loan_m), (6, x))` at `k := 5` is `False`, and drops `m`); no type
  value holds a loan in a reachable state, since one is built by an erased run, whose reads end the
  loans first. That is a hypothesis of the statement of fact (a) (`substV_loan_keeps_stmt`).
* **After a refinement (a split).** This is the worst case: a fill stuck on `σ` computes once `σ`
  is refined, and may drop its hole. `DropArm` (accepted): `PickP(n, &a, &b)` is stuck on `n`, so
  both `a` and `b` hold fills with the hole `k` of the returned `r`. The split on `n` refines it:
  in the arm `n = Z`, `a`'s fill computes to `loan_k` and `b`'s to `b`'s old content, dropping the
  hole; `*r := (7, 7)` then reaches `a` and not `b` (`Id` by `refl` on `a.0`), and the control
  `DropArmWrong`, which claims `b.0` is `7` in that arm, is REJECTED. The witness survives because
  the reference reads the same arm under the same assignment: under an assignment with `n = Z`,
  `b` means `PickP`'s backward function at `n = Z` read at `b`, which is `b`'s old content and reads
  no label.
-/

open Ochr.Test

ochr RenormHoles uses Nats {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  def DropArm (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat := (
    let r = PickP(clone(n), &a, &b);
    match n {
      Z => (*r := (7, 7); let w = a.0; let h : Id(Nat, clone(w), 7) = refl; w),
      S m => (*r := (7, 7); let w = b.0; let h : Id(Nat, clone(w), 7) = refl; w)
    }
  )
  reject def DropArmWrong (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat := (
    let r = PickP(clone(n), &a, &b);
    match n {
      Z => (*r := (7, 7); let w = b.0; let h : Id(Nat, clone(w), 7) = refl; w),
      S m => (*r := (7, 7); let w = b.0; let h : Id(Nat, clone(w), 7) = refl; w)
    }
  )
}
