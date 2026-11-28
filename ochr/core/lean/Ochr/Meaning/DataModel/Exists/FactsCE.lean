import Ochr.Meaning.DataModel.Exists.Assembly

/-!
# What was false in the facts `exists_dataModel` assumed, checked (exists11; docs/34 §18.16)

machine10 read the six facts `Assembly.exists_dataModel` assumed against the checker's code and
found some false as stated, so the theorem held only vacuously. Each old form's counterexample is
here, run on this line's checker by the kernel (`decide +kernel`, no `native_decide`; one acceptance
natively by `#guard`). When main's D128 reaches this line, `tlAccepted` stops holding and the build
fails here: that is the sign the two facts it refutes became true, and those parts go. (Main's D129 has
reached it, machine11: `join_regrains` failed, and the join's part is kept below as a pin of the new
answer.)

* `ItemFacts` concluded, at every item and state, that the stored entry holds no embedded value
  (`Term.val`) in a field or parameter type. The checker accepts core declarations holding one,
  `EV := MkEV(x : L(⟨0⟩))` and `EP (h : L(⟨0⟩)) := MkEP`, with `L (n : Nat) := MkL` declared
  (`ev_accepted`, `ep_accepted`, `itemFactsOld_false`). Resolution never builds one, so the fact is
  now `Assembly.NoValFact`, about the program's items.
* HISTORICAL since main's D128 (merged by machine12: `TL` is now REJECTED, `[D128] the parameter B of TL is declared
  at (let z = A; Type), which reads as the sort Type without being written as one`; `tlAccepted` is false, pinned
  below, and the two refutations that take it as a hypothesis are vacuous). What exists11 found before D128:
  `ItemFacts` also concluded `Records.VaryValFree` of the entry. The surface declaration
  `inductive TL (A : Type) (B : (let z = A; Type)) := MkTL(x : B)` is accepted and breaks it
  (`tlAccepted`, checked natively as the kernel's reduction of that run gets stuck;
  `varyValFact_false` from it, in the kernel): `B` varies, is not a type parameter, and the field
  reads it. Now `Assembly.VaryValFact`, false until main's D128. `dTL` is written by hand following
  `resolveDecl`'s conventions; machine10 ran the surface form through the checker.
* `Assembly.FieldHeads` (the checker's part of exists10's `FieldLevels`) asks a parameter heading a
  field type to be written at a sort; `TL`'s `B` is written at a `let` (`fieldHeads_false`). False
  until main's D128.
* HISTORICAL (a state of the old checker): `DecLocal.join` (`FrameLocal/Setup.lean`) was false at a
  state with `B2 := A0(n : Nat) | A1`: the join of `match k { Z => Z, S => Z }` at the entry `[x.n]`
  was `[x]`, a checker bug (the join re-grained places already moved). Main's D129 (merged by
  machine11) carries the entry's places as they are; the join is now `[x.n]` (`join_keeps_entry`), and
  the old refutation (`join_regrains`, `decLocal_false`) no longer holds, so it is gone. `DecLocal` is
  as stated; machine11 read its join part TRUE against the new `jdMatch`.
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

/-- **Whether the checker accepts `TL`** at the program's first stage. Checked natively (`#guard`): the
kernel's reduction of this run gets stuck (it does finish the runs of `EV` and `EP` above), so the
refutation below takes acceptance as its hypothesis and checks the rest in the kernel. Before main's D128 it was
accepted; since D128 (machine12's merge) it is REJECTED (the guard below). -/
def tlAccepted : Bool :=
  match (runMachine (checkItem (.ind dTL)) (Assembly.stSt 3000 tlItems 0) 3000).1 with
  | .ok () _ => true
  | _ => false

-- REJECTED since main's D128 (accepted before: the guard was `#guard tlAccepted`)
#guard !tlAccepted

/-- The entry the checker stores for `TL` (machine10's `checkItem_tables`): `B` is not nestable, `A` is. -/
theorem tl_nestable : nestableSet (nestTableOf []) (sortTableOf [] dTL) dTL = [true, false] := by decide +kernel

/-- HISTORICAL (vacuous since main's D128: `tlAccepted` is false). **`VaryValFact` was false**, given that the checker accepts `TL` (`tlAccepted`, natively): the
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

/-- HISTORICAL (vacuous since main's D128: `tlAccepted` is false). **`FieldHeads`' parameter part was false**, given that the checker accepts `TL`: the field `x : B`
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

/-! ## `DecLocal.join`: the join kept the entry's places (main's D129)

Before D129 the join of `tB2` at the entry `[x.n]` answered the whole `x` (neither in the entry nor
free in the term), which refuted `DecLocal.join` (exists11's `join_regrains`, `decLocal_false`, a
state of the old checker). Since D129 the entry's places are carried as they are: the pin below is
the new answer. -/

/-- `B2 := A0(n : Nat) | A1`. -/
def dB2 : IndDecl := { name := "B2", ctors := [("A0", [("n", Term.nat)]), ("A1", [])] }
def gN : FieldRef := { ty := "B2", ctor := 0, idx := 0, name := "n" }
def stB2 : MState := { inds := [dB2] }
/-- `var 0 : B2` (`x`), `var 1 : Nat` (`k`). -/
def scB2 : List DeclInfo := [.ind "B2" [], .other]
/-- The entry `[x.n]`; the term `match k { Z => Z, S => Z }`, which does not mention `x`. -/
def entryB2 : List Place := [.field gN (.var 0)]
def tB2 : Term := .matchNat (.var 1) .zero .zero

/-- The join's answer at `stB2`, if it succeeds. -/
def joinAt : Option (List Place) :=
  match (runMachine (joinMovesD entryB2 tB2 50) (scopeState stB2 scB2) 100000).1 with
  | .ok ps _ => some ps
  | _ => none

/-- **The join keeps the entry `[x.n]` as it is** (main's D129; before it, `[x]`). -/
theorem join_keeps_entry : (joinAt == some entryB2) = true := by decide +kernel

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

/-! ## `VaryValFact` after D140: a declaration only a run rejects (exists13)

D140 checks a parameter that is a field's WHOLE type (written `Prop` or `Type`). A parameter standing at a
type parameter of an applied declaration (`Box(B)`) is checked by D55 (`typePos` through `declOf`'s `.tind`
clause), which accepts a declared reading `.any` (a hole, a match with no arms) as it accepts a sort, and by
D128, which looks only at `.sort` readings. So the `.any` case of `VaryValFact` is closed by D140 at a
whole field type only; `VS` below is rejected by the evaluation of its parameter's type alone. -/

/-- `inductive Box (A : Type) := MkBox(x : A)`, as stored (`A` nestable). -/
def dBoxV : IndDecl :=
  { name := "Box", params := [(⟨"A"⟩, .sort 1)], ctors := [("MkBox", [("x", .place (.var 0))])], nestable := [true] }

/-- `inductive VS (A : Type) (B : (A; ?)) := MkVS(y : Box(B))`, as resolution builds it. `B` varies (its type
reads `A`, which stays nestable: `B` is read only at `Box`'s nestable parameter), and is not a type parameter
(its type is written as a sequence). -/
def dVS : IndDecl :=
  { name := "VS", params := [(⟨"A"⟩, .sort 1), (⟨"B"⟩, .seq (.place (.var 0)) (.prim "hole" []))],
    ctors := [("MkVS", [("y", .tind "Box" [.place (.var 0)])])] }

/-- The checker's verdict on `VS` after `Box`: rejected, since main's D141 by the parameter check from syntax (`B`'s
type reads "any"), before anything runs; before D141 by the evaluation of `B`'s type (`?: the type expected here is
not known`), after D55, D128, D118, D133 and D140 had passed. Natively. -/
def vsVerdict : String :=
  match (runMachine (checkItem (.ind dVS)) { inds := [dBoxV] } 3000).1 with
  | .ok () _ => "accepted"
  | .fail (.error m _) => m
  | _ => "other"

-- flipped by D141: the rejection is D141's (it was the evaluation's, "the type expected here is not known")
#guard (vsVerdict.splitOn "[D141] the parameter B of VS").length > 1

/-- The entry the checker would store for `VS`: `A` nestable, `B` not. -/
theorem vs_nestable : nestableSet (nestTableOf [dBoxV]) (sortTableOf [dBoxV] dVS) dVS = [true, false] := by
  decide +kernel

/-- **Had the checker accepted `VS`, `VaryValFree` would fail at its entry**: the field `y : Box(B)` reads `B`,
which varies and is not a type parameter. So `VaryValFact` rests, at `VS`, on the run that evaluates `B`'s type,
not on D140. -/
theorem vs_not_varyValFree : ¬ Records.VaryValFree { dVS with nestable := [true, false] } := by
  intro hfree
  have hv0 : Knot.paramVaries { dVS with nestable := [true, false] } 0 = true := by
    rw [Knot.paramVaries]; rfl
  have hv1 : Knot.paramVaries { dVS with nestable := [true, false] } 1 = true := by
    rw [Knot.paramVaries]
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact .inr ⟨0, by decide +kernel, by simp [hv0]⟩
  have := hfree 0 0 (.tind "Box" [.place (.var 0)]) rfl 0 (by decide +kernel) (by decide) hv1
  revert this; decide +kernel

end Ochr.Meaning.DataModel.Exists.FactsCE
