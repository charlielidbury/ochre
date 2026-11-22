import Ochr.Meaning.Steps.FragAsg

/-!
# The fragment theorem (lead10, lead11, lead12)

`frag_sim`: the evaluation step (`EvalSim`) for every term of the fragment, by induction on the typing, from the facts
about the checker (and the decision table) bundled as `FragFacts`; every case is proved (lead12).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- **The facts about the checker (and its decision table) the fragment theorem assumes**: each a
`Prop` of `FormMachine.lean`, `FragMachine.lean` or `Frag.lean`; those the machine lane has proved are
discharged where the theorem is instantiated. -/
structure FragFacts (D : Decisions) : Prop where
  eval : EvalInv
  zero : ZeroInv
  succ : SuccInv
  varNum : VarNumInv
  varLent : VarLentInv
  varBot : VarBotInv
  invEnd : InvEnd
  inv : InvSteps
  low : EvalLow
  dec : FragDec D
  run : FragRun D
  pl : PlaceLocal D
  letInv : LetInv
  dropNoop : DropNoopInv
  dropBor : DropBorrowInv
  dropLent : DropLentFail
  popUnit : InvPopUnit
  bindUnit : InvBindUnit
  seqInv : SeqInv
  borNum : BorrowNumInv
  borLent : BorrowLentInv
  borBot : BorrowBotInv
  lendG : InvLendG
  /-- D112's invalidation is empty (the fuel-free table's, by definition) -/
  noInv : ∀ sc p, D.invalidated sc p = []
  seqBor : SeqBorInv
  popBot : InvPopBot
  asgVar : AssignVarInv
  setBotNum : InvSetBotNum
  asgDeref : AssignDerefInvF

/-- **The fragment theorem** (the evaluation step, `EvalSim`, at every fragment term): for every term the fragment types,
every fuel, `Δ` and assignment, the step at `eval` from a state meeting `FSt`, by induction on the
typing, each sub-term's step an induction hypothesis at every extension. Every case is proved: `Z`,
`S`, the read (`fvar_core`), `let` (`letF_core`), `;` (`seqI_core`, `seqB_core`), `&x` (`borF_core`),
`x := u` (`asgF_core`), `*y := u` (`asgDF_core`). Assumes only the facts of `FragFacts`, about the
checker alone and about its decision table (the list, with which are proved, is `OPEN.md`'s). -/
theorem frag_sim {K : RunCtx} {φ : Future} (hf : FragFacts K.D) (hc : Strict.FundCtx K) :
    ∀ Γ t A, FTy Γ t A → ∀ n (Δ : Nat → TyS) (ρ : Assignment),
      EvalSim { K with Δ := Δ } ρ φ n t (FSt Γ) (· = true) := by
  obtain ⟨hE, hZ, hS, hVN, hV, hVB, hIE, hI, hlow, hdec, hR, hPL, hL, hDN, hDB, hDL, hIU, hIBU, hSq, hBN, hBL, hBB,
    hILG, hNI, hSB, hIPB, hAV, hISB, hAD⟩ := hf
  have hnat := hR.nat
  intro Γ t A hty
  induction hty with
  | zero Γ =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.zero Γ) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => ColumnC.zero_coreSim hZ hI) n
  | succ Γ u hu ih =>
    intro n Δ ρ
    refine frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.succ Γ u hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => ?_) n
    exact succ_core hS hI (ih m Δ ρ) (fun a b hk ha => ha.kern hk) (fun st hst => (hdec Γ u .nat st hu hst).1)
      (fun s => frag_hint hu _ _ _ s)
      (fun st₀ st₁ bh v₀ T₀ hP hfr hm htd hD h => by
        obtain ⟨hv, rfl⟩ := hnat Γ u m st₀ st₁ bh v₀ T₀ hu hP hfr hm htd hD h
        exact ⟨hv, fun T e => by cases e; rfl⟩)
  | var Γ i hi =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.var Γ i hi) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => (fvar_core (K := { K with Δ := Δ }) hVN hV hVB hIE hI hPL hi).restrict) n
  | bor Γ i hi =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.bor Γ i hi) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => borF_core (K := { K with Δ := Δ }) hBN hBL hBB hIE hILG hPL hNI hi) n
  | asg Γ i u hi hu ih =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.asg Γ i u hi hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => asgF_core (K := { K with Δ := Δ }) hAV hR hdec hI hIE hISB hPL hNI
        ⟨hc.globals, hc.sorts⟩ hi hu (ih m Δ ρ)) n
  | asgD Γ i u hi hu ih =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.asgD Γ i u hi hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => asgDF_core (K := { K with Δ := Δ }) hAD hR hdec hI hPL hNI
        ⟨hc.globals, hc.sorts⟩ hi hu (ih m Δ ρ)) n
  | letIn Γ x u w A B hu hw ihu ihw =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.letIn Γ x u w A B hu hw) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => letF_core (K := { K with Δ := Δ }) hL hR hdec hDN hDB hDL hI hIU hIBU hIE
        hPL ⟨hc.globals, hc.sorts⟩ hu hw (ihu m Δ ρ) (ihw m)) n
  | seq Γ u w A B hu hw ihu ihw =>
    intro n Δ ρ
    refine frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.seq Γ u w A B hu hw) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => ?_) n
    by_cases hA : A = .ref
    · subst hA
      exact seqB_core (K := { K with Δ := Δ }) hSB hR hdec hIE hIPB hPL ⟨hc.globals, hc.sorts⟩ hu hw (ihu m Δ ρ) (ihw m)
    · exact seqI_core (K := { K with Δ := Δ }) hSq hR hdec hI ⟨hc.globals, hc.sorts⟩ hu hw hA (ihu m Δ ρ) (ihw m)

end Ochr.Meaning.Steps.Form
