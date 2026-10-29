import Ochr.Machine

/-!
# Probe: mechanising (P) against the real machine, layer 1

(P), "a run that never inspects an unknown commutes with substituting a value for it",
needs first that the real substitution is a pure substitution on the values a run passes
around. Here: on first-order data (no closure, Π-type, sealed program or equation type
anywhere), the real fuel-indexed `substV` has no effect and computes `psV`, a structural
substitution.
-/

namespace Ochr.PProbe
open Ochr

mutual
/-- First-order data: no closure, Π-type, sealed program or equation type anywhere (the
three places `substV` does more than substitute: re-normalising a sealed program, rebuilding
an equation with `mkEqM`, substituting into a closure's term). -/
def dataV : Value → Bool
  | .succ w | .tRef w | .borrow _ w => dataV w
  | .ind _ _ _ ps fs => dataL ps && dataL fs
  | .tInd _ fs => dataL fs
  | .clo .. | .tPi .. | .sealed _ | .tEq .. => false
  | _ => true
termination_by structural v => v
def dataL : List Value → Bool
  | [] => true
  | a :: as => dataV a && dataL as
termination_by structural as => as
end

mutual
/-- The fuel a substitution needs: the value's depth. -/
def depthV : Value → Nat
  | .succ w | .tRef w | .borrow _ w => depthV w + 1
  | .ind _ _ _ ps fs => max (depthL ps) (depthL fs) + 1
  | .tInd _ fs => depthL fs + 1
  | _ => 1
termination_by structural v => v
def depthL : List Value → Nat
  | [] => 0
  | a :: as => max (depthV a) (depthL as)
termination_by structural as => as
end

mutual
/-- Structural substitution, mirroring `substV`'s case split on data. -/
def psV (x r : Value) (v : Value) : Value :=
  if !(v.anyAtom (· == x)) then v else
  if v == x then r else
  match v with
  | .abs _ | .loan _ => if v == x then r else v
  | .succ w => .succ (psV x r w)
  | .borrow l w => .borrow l (psV x r w)
  | .tInd n as => .tInd n (psL x r as)
  | .tRef A => .tRef (psV x r A)
  | .ind t c h ps fs => .ind t c h (psL x r ps) (psL x r fs)
  | _ => v
termination_by structural v
def psL (x r : Value) : List Value → List Value
  | [] => []
  | a :: as => psV x r a :: psL x r as
termination_by structural as => as
end

theorem depthV_pos (v : Value) : 1 ≤ depthV v := by
  cases v <;> unfold depthV <;> omega


example : LawfulMonad M := inferInstance

mutual
/-- **The real substitution is pure on data.** With enough fuel, `substV` on first-order data
has no effect on the state and returns the structural substitution. -/
theorem substV_data (x r : Value) : (v : Value) → (fuel : Nat) → dataV v = true →
    depthV v ≤ fuel → substV fuel x r v = pure (psV x r v)
  | v, 0, _, hd => absurd hd (by have := depthV_pos v; omega)
  | .zero, f+1, _, _ | .unit, f+1, _, _ | .bot, f+1, _, _ | .proof, f+1, _, _
  | .tNat, f+1, _, _ | .tUnit, f+1, _, _ | .gfn _, f+1, _, _ | .sort _, f+1, _, _
  | .abs _, f+1, _, _ | .loan _, f+1, _, _ => by
    simp only [substV, psV]; split <;> (try split) <;> simp_all
  | .clo .., _+1, hv, _ | .tPi .., _+1, hv, _ | .sealed _, _+1, hv, _ | .tEq .., _+1, hv, _ => by
    simp [dataV] at hv
  | .succ w, f+1, hv, hd => by
    have ih := substV_data x r w f (by simpa [dataV] using hv) (by simp only [depthV] at hd; omega)
    simp only [substV, psV, ih]; split <;> (try split) <;> simp_all
  | .tRef w, f+1, hv, hd => by
    have ih := substV_data x r w f (by simpa [dataV] using hv) (by simp only [depthV] at hd; omega)
    simp only [substV, psV, ih]; split <;> (try split) <;> simp_all
  | .borrow l w, f+1, hv, hd => by
    have ih := substV_data x r w f (by simpa [dataV] using hv) (by simp only [depthV] at hd; omega)
    simp only [substV, psV, ih]; split <;> (try split) <;> simp_all
  | .tInd n as, f+1, hv, hd => by
    have ih := mapM_substV_data x r as f (by simpa [dataV] using hv) (by simp only [depthV] at hd; omega)
    simp only [substV, psV, ih]; split <;> (try split) <;> simp_all
  | .ind t c h ps fs, f+1, hv, hd => by
    simp only [dataV, Bool.and_eq_true] at hv
    simp only [depthV] at hd
    have ip := mapM_substV_data x r ps f hv.1 (by omega)
    have ifs := mapM_substV_data x r fs f hv.2 (by omega)
    simp only [substV, psV, ip, ifs]; split <;> (try split) <;> simp_all

theorem mapM_substV_data (x r : Value) : (vs : List Value) → (fuel : Nat) → dataL vs = true →
    depthL vs ≤ fuel → vs.mapM (substV fuel x r) = pure (psL x r vs)
  | [], _, _, _ => by simp [psL]
  | a :: as, f, hv, hd => by
    simp only [dataL, Bool.and_eq_true] at hv
    simp only [depthL] at hd
    have ia := substV_data x r a f hv.1 (by omega)
    have ias := mapM_substV_data x r as f hv.2 (by omega)
    simp [ia, ias, psL]
end

end Ochr.PProbe
#print axioms Ochr.PProbe.substV_data
