import Ochr.Meaning.DataModel.Exists.Assembly

/-!
# What was false in the facts `exists_dataModel` assumed, checked (exists11; docs/34 §18.16)

machine10 read the six facts `Assembly.exists_dataModel` assumed against the checker's code and
found some false as stated, so the theorem held only vacuously. Each old form's counterexample is
here, run on this line's checker by the kernel (`decide +kernel`, no `native_decide`; one acceptance
natively by `#guard`). When main's D128 and D129 reach this line, `tlAccepted` and `join_regrains`
stop holding and the build fails here: that is the sign the two facts became true, and those parts go.

* `ItemFacts` concluded, at every item and state, that the stored entry holds no embedded value
  (`Term.val`) in a field or parameter type. The checker accepts core declarations holding one,
  `EV := MkEV(x : L(⟨0⟩))` and `EP (h : L(⟨0⟩)) := MkEP`, with `L (n : Nat) := MkL` declared
  (`ev_accepted`, `ep_accepted`, `itemFactsOld_false`). Resolution never builds one, so the fact is
  now `Assembly.NoValFact`, about the program's items.
* `ItemFacts` also concluded `Records.VaryValFree` of the entry. The surface declaration
  `inductive TL (A : Type) (B : (let z = A; Type)) := MkTL(x : B)` is accepted and breaks it
  (`tlAccepted`, checked natively as the kernel's reduction of that run gets stuck;
  `varyValFact_false` from it, in the kernel): `B` varies, is not a type parameter, and the field
  reads it. Now `Assembly.VaryValFact`, false until main's D128. `dTL` is written by hand following
  `resolveDecl`'s conventions; machine10 ran the surface form through the checker.
* `Assembly.FieldHeads` (the checker's part of exists10's `FieldLevels`) asks a parameter heading a
  field type to be written at a sort; `TL`'s `B` is written at a `let` (`fieldHeads_false`). False
  until main's D128.
* `DecLocal.join` (`FrameLocal/Setup.lean`) is false at a state with `B2 := A0(n : Nat) | A1`: the
  join of `match k { Z => Z, S => Z }` at the entry `[x.n]` is `[x]` (`join_regrains`,
  `decLocal_false`), a checker bug (the join re-grains places already moved), to be fixed by main's
  D129. `DecLocal` is left as stated.
* `DecStable` asked its equation at ANY earlier state; at `st0 = {inds := [E]}` with
  `E := MkE(x : F(Z))` and the later state with the global `F : Π(n : Nat). Prop`, the flags the
  decisions give the call `F(Z)` differ (`flags_differ`, `decStableOld_flags`), and the run's call
  clause erases by them. Now asked only at the states the checker reaches on the program.
-/

namespace Ochr.Meaning.DataModel.Exists.FactsCE

open Ochr Ochr.Meaning

/-! ## `ItemFacts`, the embedded values -/

/-- `L (n : Nat) := MkL`, declared. -/
def dL : IndDecl := { name := "L", params := [(⟨"n"⟩, .nat)], ctors := [("MkL", [])] }
def stL : MState := { inds := [dL] }

/-- `EV := MkEV(x : L(⟨0⟩))`: an embedded value at `L`'s value parameter. -/
def dEV : IndDecl := { name := "EV", ctors := [("MkEV", [("x", .tind "L" [.val .zero])])] }
/-- `EP (h : L(⟨0⟩)) := MkEP`: an embedded value in a parameter type. -/
def dEP : IndDecl := { name := "EP", params := [(⟨"h"⟩, .tind "L" [.val .zero])], ctors := [("MkEP", [])] }

/-- The checker accepts `it` at `st` and the last stored entry satisfies `p`. -/
def acceptsWith (it : Item) (st : MState) (fuel : Nat) (p : IndDecl → Bool) : Bool :=
  match (runMachine (checkItem it) st fuel).1 with
  | .ok () st' => (st'.inds.getLast?.map p).getD false
  | _ => false

theorem ev_accepted : acceptsWith (.ind dEV) stL 3000
    (fun d' => ((fieldTerm d' 0 0).map (·.anyAtom (fun _ => true))).getD false) = true := by
  decide +kernel

theorem ep_accepted : acceptsWith (.ind dEP) stL 3000
    (fun d' => (Knot.paramTerm d' 0).anyAtom (fun _ => true)) = true := by
  decide +kernel

/-- `ItemFacts` as it stood before exists11. -/
def ItemFactsOld : Prop :=
  ∀ (it : Item) (st st' : MState) (fuel : Nat), (runMachine (checkItem it) st fuel).1 = .ok () st' →
    (∀ d, it = .ind d → ∃ d', st'.inds = st.inds ++ [d'] ∧ Knot.IndChecks st.inds d' ∧ Knot.FieldsNoVal d' ∧
      Assembly.ParamsNoVal d' ∧ Records.VaryValFree d' ∧ st'.globals = st.globals) ∧
    (∀ d, it = .defn d → st'.inds = st.inds ∧ st.globals <+: st'.globals)

theorem acceptsWith_spec {it : Item} {st : MState} {fuel : Nat} {p : IndDecl → Bool}
    (h : acceptsWith it st fuel p = true) :
    ∃ st', (runMachine (checkItem it) st fuel).1 = .ok () st' ∧ ∃ d', st'.inds.getLast? = some d' ∧ p d' = true := by
  unfold acceptsWith at h
  split at h
  · rename_i st' hst
    refine ⟨st', hst, ?_⟩
    cases hl : st'.inds.getLast? with
    | none => rw [hl] at h; cases h
    | some d' => rw [hl] at h; exact ⟨d', rfl, h⟩
  · cases h

theorem itemFactsOld_false : ¬ ItemFactsOld := by
  intro H
  obtain ⟨st', hst, d', hl, hp⟩ := acceptsWith_spec ev_accepted
  obtain ⟨d'', hI, -, hnv, -⟩ := (H _ _ _ _ hst).1 dEV rfl
  rw [hI, List.getLast?_append, List.getLast?_singleton] at hl
  simp at hl
  subst hl
  cases hFT : fieldTerm d'' 0 0 with
  | none => rw [hFT] at hp; cases hp
  | some FT => rw [hFT] at hp; simp at hp; rw [hnv 0 0 FT hFT] at hp; cases hp

/-! ## `VaryValFree`: the surface declaration `TL` -/

/-- `inductive TL (A : Type) (B : (let z = A; Type)) := MkTL(x : B)`, as resolution builds it (the
parameters are `var 0 …`, the latest first; `tl_surface` below runs the surface form natively). -/
def dTL : IndDecl :=
  { name := "TL", params := [(⟨"A"⟩, .sort 1), (⟨"B"⟩, .letIn ⟨"z"⟩ (.place (.var 0)) (.sort 1))],
    ctors := [("MkTL", [("x", .place (.var 0))])] }
def tlItems : List Item := [.ind dTL]

/-- **The checker accepts `TL`** at the program's first stage. Checked natively (`#guard`): the
kernel's reduction of this run gets stuck (it does finish the runs of `EV` and `EP` above), so the
refutation below takes acceptance as its hypothesis and checks the rest in the kernel. -/
def tlAccepted : Bool :=
  match (runMachine (checkItem (.ind dTL)) (Assembly.stSt 3000 tlItems 0) 3000).1 with
  | .ok () _ => true
  | _ => false

#guard tlAccepted

/-- The entry the checker stores for `TL` (machine10's `checkItem_tables`): `B` is not nestable, `A` is. -/
theorem tl_nestable : nestableSet (nestTableOf []) (sortTableOf [] dTL) dTL = [true, false] := by decide +kernel

/-- **`VaryValFact` is false**, given that the checker accepts `TL` (`tlAccepted`, natively): the
stored entry's field `x : B` reads parameter `B`, which varies (its type reads `A`, which is
nestable) and is not a type parameter (`paramIsType` sees a `let`). -/
theorem varyValFact_false (hacc : tlAccepted = true) : ¬ Assembly.VaryValFact 3000 tlItems := by
  intro H
  unfold tlAccepted at hacc
  split at hacc
  · rename_i st' hst
    have hT := ((Steps.Machine.checkItem_tables _ _ _ _ hst).1 dTL rfl).1
    have h0 : (Assembly.stSt 3000 tlItems 0).inds = [] := rfl
    rw [h0, tl_nestable] at hT
    have hfree := H 0 (by decide) st' dTL _ hst rfl (by rw [hT]; rfl)
    have hv0 : Knot.paramVaries { dTL with nestable := [true, false] } 0 = true := by
      rw [Knot.paramVaries]; rfl
    have hv1 : Knot.paramVaries { dTL with nestable := [true, false] } 1 = true := by
      rw [Knot.paramVaries]
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact .inr ⟨0, by decide +kernel, by simp [hv0]⟩
    have := hfree 0 0 (.place (.var 0)) rfl 0 (by decide +kernel) (by decide) hv1
    revert this; decide +kernel
  · cases hacc

/-- **`FieldHeads`' parameter part is false**, given that the checker accepts `TL`: the field `x : B`
is headed by parameter `B`, written at a `let`, not a sort. -/
theorem fieldHeads_false (hacc : tlAccepted = true) : ¬ Assembly.FieldHeads 3000 tlItems := by
  intro H
  unfold tlAccepted at hacc
  split at hacc
  · rename_i st' hst
    have hT := ((Steps.Machine.checkItem_tables _ _ _ _ hst).1 dTL rfl).1
    have h0 : (Assembly.stSt 3000 tlItems 0).inds = [] := rfl
    rw [h0, tl_nestable] at hT
    obtain ⟨l, -, hl⟩ := (H 0 (by decide) st' dTL _ hst rfl (by rw [hT]; rfl)).1 0 0 0 rfl (by decide)
    cases hl
  · cases hacc

/-! ## `DecLocal.join`: the join re-grains a place already moved -/

/-- `B2 := A0(n : Nat) | A1`. -/
def dB2 : IndDecl := { name := "B2", ctors := [("A0", [("n", Term.nat)]), ("A1", [])] }
def gN : FieldRef := { ty := "B2", ctor := 0, idx := 0, name := "n" }
def stB2 : MState := { inds := [dB2] }
/-- `var 0 : B2` (`x`), `var 1 : Nat` (`k`). -/
def scB2 : List DeclInfo := [.ind "B2" [], .other]
/-- The entry `[x.n]`; the term `match k { Z => Z, S => Z }`, which does not mention `x`. -/
def entryB2 : List Place := [.field gN (.var 0)]
def tB2 : Term := .matchNat (.var 1) .zero .zero

/-- The join answers a place rooted at `x` with no step (the whole `x`): not in the entry, and `x`
is not free in the term. -/
def joinBad : Bool :=
  match (runMachine (joinMovesD entryB2 tB2 50) (scopeState stB2 scB2) 100000).1 with
  | .ok ps _ => ps.any fun q => q.root == 0 && q.steps.2.isEmpty
  | _ => false

theorem join_regrains : joinBad = true := by decide +kernel

/-- **`DecLocal` is false at `stB2`**, where the decisions' join reads the machine's answer (that
the machine's answers agree across fuels is the machine lane's `decide_fuel_agree`). -/
theorem decLocal_false (fuel : Nat) (hag : FuelAgree (joinMovesD entryB2 tB2) (scopeState stB2 scB2)) :
    ¬ FrameLocal.DecLocal (chainDecisions fuel stB2) := by
  intro H
  have hj := join_regrains
  unfold joinBad at hj
  split at hj
  · rename_i ps st'' hrun
    have hR := Steps.Machine.runs_of_runMachine_fst hrun
    have hrd : (chainDecisions fuel stB2).joinMoves scB2 entryB2 tB2 = ps := readDecisionFF_of_runs hag hR
    obtain ⟨q, hq, hq0⟩ := List.any_eq_true.1 hj
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hq0
    rcases H.join scB2 entryB2 tB2 q (by rw [hrd]; exact hq) with h | h
    · simp only [entryB2, List.mem_singleton] at h
      subst h
      simp [Place.steps] at hq0
    · rw [hq0.1] at h
      exact absurd h (by decide +kernel)
  · cases hj

/-! ## `DecStable` at an arbitrary earlier state: the pair `E`, `F` -/

/-- `E := MkE(x : F(Z))`; the global `F : Π(n : Nat). Prop`, only in the later state. -/
def tFZ : Term := .call (.const "F") [.zero] false
def dE : IndDecl := { name := "E", ctors := [("MkE", [("x", tFZ)])] }
def gF : GDef := { name := "F", ty := .tPi [] (.pi [⟨"n"⟩] [.nat] (.sort 0)) [], fn? := none, val := .gfn "F" }
def stE0 : MState := { inds := [dE] }
def stE1 : MState := { inds := [dE], globals := [gF] }

/-- The flags of `F(Z)`: none known at the earlier state (`F` is unknown there), the first flag set at
the later one (`F(Z)`'s reading is `Prop`). -/
def flagsAt (st : MState) : Option (Bool × Bool) :=
  match (runMachine (flagsD tFZ 50) (scopeState st []) 100000).1 with
  | .ok fl _ => some fl
  | _ => none

theorem flags_differ : flagsAt stE0 = some (false, false) ∧ flagsAt stE1 = some (true, false) := by
  decide +kernel

theorem flagsAt_runs {st : MState} {fl : Bool × Bool} (h : flagsAt st = some fl) :
    ∃ b st'', Steps.Runs (flagsD tFZ 50) (scopeState st []) b fl st'' := by
  unfold flagsAt at h
  split at h
  · rename_i fl' st'' hrun
    cases h
    exact ⟨_, _, Steps.Machine.runs_of_runMachine_fst hrun⟩
  · cases h

/-- **The decisions at the two states differ at `F(Z)`** (given, as `decLocal_false`, that the
machine's answers agree across fuels). The run's call clause erases by these flags (`SM.erasedIf`),
so at a meaning of `F` that is not a proof the field type's run is undefined under the later state's
decisions and defined under the earlier one's: the old `DecStable`, asked at `st0 := stE0`,
`st := stE1`, `d := dE`, was false (argued from the run's call clause; the flags are checked). -/
theorem decStableOld_flags (fuel : Nat) (hag0 : FuelAgree (flagsD tFZ) (scopeState stE0 []))
    (hag1 : FuelAgree (flagsD tFZ) (scopeState stE1 [])) :
    (chainDecisions fuel stE0).flags [] tFZ = (false, false) ∧ (chainDecisions fuel stE1).flags [] tFZ = (true, false) := by
  obtain ⟨b0, s0, h0⟩ := flagsAt_runs flags_differ.1
  obtain ⟨b1, s1, h1⟩ := flagsAt_runs flags_differ.2
  exact ⟨readDecisionFF_of_runs hag0 h0, readDecisionFF_of_runs hag1 h1⟩

end Ochr.Meaning.DataModel.Exists.FactsCE

