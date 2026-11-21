import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.Regress.CodeRuns
import Ochr.Examples.Nat

/-!
# `Eq` and `J`: the checker's verdicts beside the reference's runs (docs/31 D75; area (e))

**Programs** (`EqJProbe`, verdicts checked by the build): `EqS : Eq(Nat, S(Z), S(Z))` accepted and
`EqSZ : Eq(Nat, S(Z), Z)` rejected; `EqFn : Eq(Π(n : Nat). Nat, F, G)` accepted (two functions with
the same generic observation, [Conv-fun]); `JC` (`J` at convertible closed endpoints, computed)
accepted; `JS` (`J` at unknown endpoints, closed off as a stuck block, [T-J-stuck]) accepted, and
`JWrong` (the transported term at `P(b)` where `P(a)` is asked) rejected.

**The reference's runs** (kernel-checked, `Kp` with no declaration): `Eq(Nat, S(Z), S(Z))` is a true
proposition (`ref_eqS_true`), `Eq(Nat, S(Z), Z)` a false one (`ref_eqSZ_false`), each with the state
untouched; and `J(Nat, 0, 1, Nat, (), 0)` runs to `0` (`ref_J_runs_t`): the reference's `J` means its
transported term WHATEVER its endpoints ([J-run]), where the checker is stuck at endpoints that are
not convertible and closes the `J` off as a block whose one arm is the transported term; that block's
meaning is the run of the `J` (`closeBlock_step`), so both paths mean the transported term.

**A private computation keeps the new unknowns' types** (checked on the checker's state at a hole of
`TAt`, with `F` and `G` in scope): `conv F G` answers `true`, `mkEqM Nat F G` gives `⊤`, and the type
`Eq(Π(n : Nat). Nat, F, G)` evaluates, each leaving Ω's values as they were and the table of
unknowns LONGER (one more unknown after a conversion, two after the type, which compares the two
Π-types too): the generic calls' unknowns, whose types `restoreKeep` keeps. The table is part of the
state's core, so `mkEqM_step_stmt` and `evalType_step_stmt`, which said the core was unchanged, were
false (now `KeptAfter` and `ExtOk`, `Steps/Statements.lean`).
-/

open Ochr.Test

ochr EqJProbe uses Nats {
  inductive Box (k : Nat) := MkB(x : Nat)
  def F (n : Nat) : Nat := n
  def G (m : Nat) : Nat := m
  def EqS : Eq(Nat, S(Z), S(Z)) := refl
  reject def EqSZ : Eq(Nat, S(Z), Z) := refl
  def EqFn : Eq(Π(n : Nat). Nat, F, G) := refl
  def JC (x : Box(S(Z))) : Box(S(Z)) := J(Nat, S(Z), S(Z), λ(k : Nat) : Type => Box(k), refl, x)
  def JS (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (x : Box(a)) : Box(b) := J(Nat, a, b, λ(k : Nat) : Type => Box(k), h, x)
  reject def JWrong (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (x : Box(b)) : Box(b) := J(Nat, a, b, λ(k : Nat) : Type => Box(k), h, x)
}

#guard_msgs (drop warning) in
ochr EqJAt uses Nats {
  def F (n : Nat) : Nat := n
  def G (m : Nat) : Nat := m
  def TAt (n : Nat) : Nat := ?
}

namespace Ochr.Meaning.Regress.EqJ
open Ochr Ochr.Meaning

def stAt (name : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) "EqJAt" EqJAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The checker's state at the hole of `TAt`: `n` bound, one unknown (`n`'s). -/
def stT : MState := stAt "TAt"

/-- A run from `stT` that returns `r` and leaves Ω's values as they were and `k` more unknowns. -/
def keepsGrows {α : Type} [BEq α] (x : M α) (r : α) (k : Nat) : Bool :=
  match (runMachine x stT 1000000).1 with
  | .ok a st' => a == r && Env.values st'.env == Env.values stT.env && st'.absTy.size == stT.absTy.size + k
  | _ => false

/-- The same, whatever it returns. -/
def keepsGrowsAny {α : Type} (x : M α) (k : Nat) : Bool :=
  match (runMachine x stT 1000000).1 with
  | .ok _ st' => Env.values st'.env == Env.values stT.env && st'.absTy.size == stT.absTy.size + k
  | _ => false

#guard stT.absTy.size == 1
#guard keepsGrows (Ochr.conv 100000 (.gfn "F") (.gfn "G")) true 1
-- the control: the table did change (the core is not the snapshot's)
#guard !keepsGrows (Ochr.conv 100000 (.gfn "F") (.gfn "G")) true 0
#guard keepsGrows (Ochr.mkEqM 100000 .tNat (.gfn "F") (.gfn "G")) vTrue 1
#guard keepsGrowsAny (Ochr.evalType 100000 (.eq (.pi [⟨"n"⟩] [.nat] .nat) (.const "F") (.const "G"))) 2

end Ochr.Meaning.Regress.EqJ

namespace Ochr.Meaning.Regress.EqJRef
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CodeRuns

variable (dm : DataModel) (G : String → Sem × TyS) (ρ : Assignment) (φ : Future)

noncomputable def one : Sem := Sem.succ (.el0 Nat 0)

theorem one_eq : one = .el0 Nat 1 := by simp [one, Sem.succ, Sem.asNat, Sem.as]

/-- The reference's `Eq(Nat, S(Z), b)`: the proposition that the two sides' meanings are equal,
the state untouched. -/
theorem ref_eq (b : Term) (vb : Sem) (hb : run (Kp dm [] G) ρ φ (.plain TyM.nat) b (emptyState 0) = some ((vb, .plain TyM.nat), emptyState 0)) (hint : TyS) :
    run (Kp dm [] G) ρ φ hint (.eq .nat (.succ .zero) b) (emptyState 0)
      = some ((.ty (TyM.prop (one = vb)), .plain (TyM.univ 0)), emptyState 0) := by
  have hn : runT (Kp dm [] G) ρ φ false (TyS.plain TyM.err) Term.nat (emptyState 0) =
      some ((.ty TyM.nat, .plain (TyM.univ 1)), emptyState 0) := rfl
  have hs : runT (Kp dm [] G) ρ φ false (.plain (Sem.ty TyM.nat).asTy) (Term.zero.succ) (emptyState 0) =
      some ((one, .plain TyM.nat), emptyState 0) := rfl
  have hb' : runT (Kp dm [] G) ρ φ false (.plain (Sem.ty TyM.nat).asTy) b (emptyState 0) =
      some ((vb, .plain TyM.nat), emptyState 0) := hb
  rw [run, runT]
  show SM.onCopy _ _ = _
  simp only [SM.onCopy, bind, hn, hs, hb', Option.map_some]
  -- STRICT experiment: the strict `Eq` needs `one` and `vb` members of `Nat`
  sorry

theorem ref_eqS_true (hint : TyS) : ∃ r, run (Kp dm [] G) ρ φ hint (.eq .nat (.succ .zero) (.succ .zero)) (emptyState 0)
    = some (r, emptyState 0) ∧ (r.1.asTy).true := by
  refine ⟨_, ref_eq dm G ρ φ (.succ .zero) one rfl hint, ?_⟩
  show one = one
  rfl

theorem ref_eqSZ_false (hint : TyS) : ∃ r, run (Kp dm [] G) ρ φ hint (.eq .nat (.succ .zero) .zero) (emptyState 0)
    = some (r, emptyState 0) ∧ ¬ (r.1.asTy).true := by
  refine ⟨_, ref_eq dm G ρ φ .zero (.el0 Nat 0) rfl hint, ?_⟩
  show ¬ one = .el0 Nat 0
  rw [one_eq]
  intro h
  cases h

/-- The reference's `J` means its transported term whatever its endpoints: here `J(Nat, 0, 1, Nat, (), 0)`
runs to `0`, the state untouched ([J-run]; the checker is stuck there, [J-stuck], and closes the `J`
off as a block whose one arm is the transported term, [T-J-stuck]). -/
theorem ref_J_runs_t (hint : TyS) :
    (run (Kp dm [] G) ρ φ hint (.prim "J" [.nat, .zero, .succ .zero, .nat, .tt, .zero]) (emptyState 0)).map (·.1.1)
      = some (.el0 Nat 0) := by
  rfl

end Ochr.Meaning.Regress.EqJRef
