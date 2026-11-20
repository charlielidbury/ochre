import Ochr.Meaning.Steps.Machine.IH

/-!
# The steps not yet proved (PENDING: the machine lane's open work)

- `blockCaptures`: its K1(g) granularity loop is a `while` loop. `while` elaborates to `Loop.forIn`,
  which is `repeatM`, `@[implemented_by]` over a `partial def`: a run that never ends has an
  unspecified value, so nothing about the function's runs is provable without proving the loop
  ends from every state (or the checker bounding it by the fuel).
- the comparison (`conv`, `convList`, `convTList`, `convPi`, `convT`, `convFn`, `convFnRun`) and
  `dropAtJoin`: changes to them are landing on `main`; they are proved about the code as it will be.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_conv (ih : MachineGrows tb nf) :
    ∀ (v : Value) (w : Value), GrowsIn tb (Ochr.conv ((nf + 1)) v w) := by
  sorry

theorem step_convList (ih : MachineGrows tb nf) :
    ∀ (as : List Value) (bs : List Value), GrowsIn tb (Ochr.convList ((nf + 1)) as bs) := by
  sorry

theorem step_convTList (ih : MachineGrows tb nf) :
    ∀ (as : List Term) (bs : List Term), GrowsIn tb (Ochr.convTList ((nf + 1)) as bs) := by
  sorry

theorem step_convPi (ih : MachineGrows tb nf) :
    ∀ (P : Value) (Q : Value), GrowsIn tb (Ochr.convPi ((nf + 1)) P Q) := by
  sorry

theorem step_convT (ih : MachineGrows tb nf) :
    ∀ (t : Term) (u : Term), GrowsIn tb (Ochr.convT ((nf + 1)) t u) := by
  sorry

theorem step_convFn (ih : MachineGrows tb nf) :
    ∀ (f : Value) (g : Value), GrowsIn tb (Ochr.convFn ((nf + 1)) f g) := by
  sorry

theorem step_convFnRun (ih : MachineGrows tb nf) :
    ∀ (f : Value) (g : Value) (pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term), GrowsIn tb (Ochr.convFnRun ((nf + 1)) f g pf cs hs ds c) := by
  sorry

theorem step_dropAtJoin (ih : MachineGrows tb nf) :
    ∀ (q : Place), GrowsIn tb (Ochr.dropAtJoin ((nf + 1)) q) := by
  sorry

theorem step_blockCaptures (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (armMovedAll : List Place), GrowsIn tb (Ochr.blockCaptures ((nf + 1)) mt armMovedAll) := by
  sorry

end Ochr.Meaning.Steps.Machine
