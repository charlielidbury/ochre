import Ochr.Meaning.Steps.TopOne
import Ochr.Meaning.Steps.KnotR

/-!
# The acceptance test of the top at one RECURSIVE definition: the program and its decisions (lead46, 2026-11-28; docs/31 D259 on)

`consistency_of_master`'s links at the program `def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }` after the
library (the column `R`'s function, `Steps/RecR.lean`). This file: the program, its resolution (kernel), the stage at
which `R` is checked, and the decisions every link reads at `R`'s code, at EVERY state whose Σ starts with `R`'s entry
(computed by `rfl`: the checker's decision procedures at those terms read neither the declarations nor the unknowns'
types, so the kernel evaluates them with the rest of the state free).
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly
open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form.ColumnR Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Steps.Form.ColumnI (psI outI)

-- The program of the acceptance test: one recursive function after the library.
open Ochr.Test in
ochr TopRP {
  def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }
}

/-- The program `q`. -/
def q : Program := TopRP.decls

/-- The whole program the checker checks: the library, then `q`. -/
def pq : Program := Prelude.decls ++ q

/-- The fuel of the test. -/
def F : Nat := 100000

/-- The resolution of the `i`-th declaration. -/
def resAt (i : Nat) : Except Exhausted (Except String Item) := (runResolve pq (pq.getD i default) F false).1

/-- The item `R`, as resolved: the column's `defR`. -/
def isRItem : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.defn ⟨n, [h], [.nat], .nat, some 0,
      .matchNat (.var 0) .zero (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false), none⟩)) =>
    n == "R" && h.name == "n"
  | _ => false

theorem pq_length : pq.length = 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem res_ind : One.isIndItem (resAt 0) = true ∧ One.isIndItem (resAt 1) = true ∧ One.isIndItem (resAt 2) = true ∧
    One.isIndItem (resAt 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem res_R : isRItem (resAt 4) = true := by decide +kernel

theorem defR_of {x : Except Exhausted (Except String Item)} (h : isRItem x = true) : x = .ok (.ok (.defn defR)) := by
  unfold isRItem at h; split at h
  · rename_i n hh
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hn⟩ := h
    cases hh; simp only at hn; subst hn; rfl
  · cases h

/-- Every item of a resolution of `pq` is the resolution of its declaration. -/
theorem items_at {items : List Item} (hr : ResolvesTo pq F items) (i : Nat) (it : Item) (hi : items[i]? = some it) :
    resAt i = .ok (.ok it) := by
  have hlt : i < pq.length := by rw [← hr.1]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨_, h, -⟩ := hr.2 i (pq.getD i default) it (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl) hi
  exact h

/-- **The resolved items**: four inductive declarations, then `R`. -/
theorem items_shape {items : List Item} (hr : ResolvesTo pq F items) :
    items.length = 5 ∧ (∀ i, i < 4 → ∀ it, items[i]? = some it → ∃ d, it = .ind d) ∧
      items[4]? = some (.defn defR) := by
  have hl : items.length = 5 := by rw [hr.1, pq_length]
  obtain ⟨h0, h1, h2, h3⟩ := res_ind
  refine ⟨hl, fun i hi it hit => ?_, ?_⟩
  · have e := items_at hr i it hit
    have hind : One.isIndItem (resAt i) = true := by
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | 2, _ => exact h2
      | 3, _ => exact h3
    rw [e] at hind
    obtain ⟨d, hd⟩ := One.ind_of hind
    exact ⟨d, by cases hd; rfl⟩
  · have h4 : items[4]? = some items[4] := List.getElem?_eq_getElem (by omega)
    have e := items_at hr 4 _ h4
    have h1 := defR_of res_R
    rw [e] at h1
    rw [h4]
    injection h1 with h1
    injection h1 with h1
    rw [h1]

/-- **A stage of `R`'s program at an item that is a definition**: the item is `R`, at the stage after the library,
whose Σ has no global and whose meanings are none. -/
theorem atStage_R {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {items : List Item}
    (hr : ResolvesTo pq F items) {P : ProgState} {d : Def} (hin : AtStage dm D Γ F items P (.defn d)) :
    d = defR ∧ P.globals = [] ∧ P.means = [] := by
  obtain ⟨hl, hind, h4⟩ := items_shape hr
  obtain ⟨k, hk, rfl⟩ := hin
  have hk5 : k < 5 := hl ▸ (List.getElem?_eq_some_iff.1 hk).1
  have hk4 : k = 4 := by
    rcases Nat.lt_or_ge k 4 with h | h
    · obtain ⟨d', hd'⟩ := hind k h _ hk
      cases hd'
    · omega
  subst hk4
  rw [h4] at hk
  injection hk with hk
  injection hk with hk
  subst hk
  have htake : ∀ it ∈ items.take 4, ∃ d, it = .ind d := by
    intro it hit
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hit
    rw [List.getElem_take] at e
    simp only [List.length_take] at hi
    exact hind i (by omega) it (by rw [← e]; exact List.getElem?_eq_getElem _)
  refine ⟨rfl, ?_, ?_⟩
  · have h := progMeaningFrom_sigAfter dm D Γ (fun _ => .err) {} F {} (items.take 4)
    simp only at h
    unfold progMeaning
    have h1 := congrArg Prod.fst h
    simp only at h1
    rw [h1]
    exact One.sigAfterFrom_globals_ind {} F _ _ htake
  · unfold progMeaning
    exact One.progMeaningFrom_means_ind dm D Γ _ {} F _ {} htake

/-! ## The decisions at `R`'s code, at every state whose Σ starts with `R`'s entry -/

/-- `R`'s entry in Σ, as `checkDef` appends it (`model` as the checker decides). -/
abbrev gE (m : Bool) : GDef := fnEntry defR m

theorem gE_false : gE false = gR := rfl

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)
open Ochr.Meaning.Steps.Form.ColumnR.Aux (pdRun jmRun cpRun)
open Ochr.Meaning.Steps.Form.ColumnP (RI pn0)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem ok_flags_body (st : MState) : isOk (flagsRun bodyR) (scopeState st RI) 1000 = true := by rfl
theorem val_flags_body (st : MState) : outVal (flagsRun bodyR) (scopeState st RI) 1000 = (false, false) := by rfl
theorem ok_flags_call (st : MState) : isOk (flagsRun callR) (scopeState st RI) 1000 = true := by rfl
theorem val_flags_call (st : MState) : outVal (flagsRun callR) (scopeState st RI) 1000 = (false, false) := by rfl
theorem ok_flags_n0 (st : MState) : isOk (flagsRun (.place pn0)) (scopeState st RI) 1000 = true := by rfl
theorem val_flags_n0 (st : MState) : outVal (flagsRun (.place pn0)) (scopeState st RI) 1000 = (false, false) := by rfl
theorem ok_pd_n0 (st : MState) : isOk (pdRun pn0) (scopeState st RI) 1000 = true := by rfl
theorem val_pd_n0 (st : MState) : isOther (outVal (pdRun pn0) (scopeState st RI) 1000) = true := by rfl
theorem ok_pd_n (st : MState) : isOk (pdRun (.var 0)) (scopeState st RI) 1000 = true := by rfl
theorem val_pd_n (st : MState) : isOther (outVal (pdRun (.var 0)) (scopeState st RI) 1000) = true := by rfl
theorem ok_cp (st : MState) : isOk cpRun st 1000 = true := by rfl
theorem val_cp (st : MState) : outVal cpRun st 1000 = false := by rfl
theorem ok_jm (st : MState) : isOk (jmRun bodyR) (scopeState st RI) 1000 = true := by rfl
theorem val_jm (st : MState) : outVal (jmRun bodyR) (scopeState st RI) 1000 = [.var 0] := by rfl
theorem ok_td_nat (st : MState) (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOk (typeDeclRun .nat) (scopeState st sc) 1000 = true := by
  rcases hsc with rfl | rfl <;> rfl
theorem val_td_nat (st : MState) (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOther (outVal (typeDeclRun .nat) (scopeState st sc) 1000) = true := by
  rcases hsc with rfl | rfl <;> rfl
theorem ok_piSort (st : MState) : isOk (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState st []) 1000 = true := by rfl
theorem val_piSort (st : MState) : outVal (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState st []) 1000 = 1 := by rfl
theorem ok_flags_fix (st : MState) : isOk (flagsRun fixR) (scopeState st []) 1000 = true := by rfl
theorem val_flags_fix (st : MState) : outVal (flagsRun fixR) (scopeState st []) 1000 = (false, false) := by rfl

theorem ok_flags_seal (st : MState) (m : Bool) (rest : List GDef) (h : st.globals = gE m :: rest) :
    isOk (flagsRun sealR) (scopeState st []) 1000 = true := by
  cases st; simp only at h; subst h; cases m <;> rfl
theorem val_flags_seal (st : MState) (m : Bool) (rest : List GDef) (h : st.globals = gE m :: rest) :
    outVal (flagsRun sealR) (scopeState st []) 1000 = (false, false) := by
  cases st; simp only at h; subst h; cases m <;> rfl

end Aux

/-- **`DecR` at every table aligned with the checker at a state whose Σ starts with `R`'s entry** (PROVED: the decision
procedures at `R`'s code, run by the kernel with the rest of the state free). -/
theorem decR_of {D : Decisions} {st : MState} (hd : DecTab D st) {m : Bool} {rest : List GDef}
    (hg : st.globals = gE m :: rest) : DecR D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  open Ochr.Meaning.Steps.Form.ColumnC.Aux in
  open Ochr.Meaning.Steps.Form.ColumnP in
  have hpd : D.placeDecl RI pn0 = .other :=
    (hd.placeDecl 100 RI pn0 _ 1000 _ (runs_out (ColumnR.Aux.pdRun pn0) _ 1000 (Aux.ok_pd_n0 st))).trans
      (isOther_eq (Aux.val_pd_n0 st))
  have hpd0 : D.placeDecl RI (.var 0) = .other :=
    (hd.placeDecl 100 RI (.var 0) _ 1000 _ (runs_out (ColumnR.Aux.pdRun (.var 0)) _ 1000 (Aux.ok_pd_n st))).trans
      (isOther_eq (Aux.val_pd_n st))
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out ColumnR.Aux.cpRun _ 1000 (Aux.ok_cp st)), Aux.val_cp]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hd.flags 100 RI bodyR _ 1000 _ (runs_out (flagsRun bodyR) _ 1000 (Aux.ok_flags_body st)), Aux.val_flags_body]
  · rw [hd.flags 100 RI callR _ 1000 _ (runs_out (flagsRun callR) _ 1000 (Aux.ok_flags_call st)), Aux.val_flags_call]
  · rw [hd.flags 100 RI (.place pn0) _ 1000 _ (runs_out (flagsRun (.place pn0)) _ 1000 (Aux.ok_flags_n0 st)),
      Aux.val_flags_n0]
  · rw [hpd]; exact hcp
  · rw [hpd0]; exact hcp
  · rw [hd.joinMoves 100 RI [] bodyR _ 1000 _ (runs_out (ColumnR.Aux.jmRun bodyR) _ 1000 (Aux.ok_jm st)), Aux.val_jm]
  · rw [hd.flags 100 [] sealR _ 1000 _ (runs_out (flagsRun sealR) _ 1000 (Aux.ok_flags_seal st m rest hg)),
      Aux.val_flags_seal st m rest hg]
  · rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat st [] (.inl rfl)))]
    exact isOther_eq (Aux.val_td_nat st [] (.inl rfl))
  · rw [hd.typeDecl 100 [.other] .nat _ 1000 _
      (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat st [.other] (.inr rfl)))]
    exact isOther_eq (Aux.val_td_nat st [.other] (.inr rfl))
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 (Aux.ok_piSort st)), Aux.val_piSort]
  · rw [hd.flags 100 [] fixR _ 1000 _ (runs_out (flagsRun fixR) _ 1000 (Aux.ok_flags_fix st)), Aux.val_flags_fix]

/-- **`DecR` at the chain's decisions of every state whose Σ starts with `R`'s entry.** -/
theorem decR_chain (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest) :
    DecR (chainDecisions F st) :=
  decR_of (One.decTab_chain F st) hg


/-! ## The links that read only decisions and the model at `R`'s code -/

section
variable {dm : DataModel} {Γ : List IndDecl}

/-- The context of `R`'s stage at a state, its decisions the chain's. -/
noncomputable abbrev KS (dm : DataModel) (Γ : List IndDecl) (P : ProgState) (st : MState) : RunCtx := P.ctx dm (chainDecisions F) Γ st

theorem decR_KS (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest) :
    DecR (KS dm Γ P st).D := decR_chain st hg

/-- **`FixFitsAt` at `R`** (PROVED at any state whose Σ starts with `R`'s entry): `Π(n : Nat). Nat` at level `1`. -/
theorem fixFits_R (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest) :
    FixFitsAt dm (chainDecisions F) Γ P defR st := by
  intro ρ φ
  have hd := decR_KS (dm := dm) (Γ := Γ) P st hg
  show PiFits dm.read (lG (KS dm Γ P st) [⟨"n"⟩] [.nat] .nat) (psG (KS dm Γ P st) ρ φ [.nat]) (outG (KS dm Γ P st) ρ φ [.nat] .nat)
    (fun _ => True)
  rw [psG_R _ ρ hd, outG_R _ ρ, lG_R _ hd]
  exact ⟨by decide, fun _ _ _ => Nat.le_refl 1⟩

/-- **`FixPartsAt` at `R`** (PROVED): the domain `Nat` and the codomain `Nat` have a level at every member. -/
theorem fixParts_R (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest) :
    FixPartsAt dm (chainDecisions F) Γ P defR st := by
  have hd := decR_KS (dm := dm) (Γ := Γ) P st hg
  show PiOk dm.read (psG (KS dm Γ P st) (fun _ => .err) noFuture [.nat]) [] (outG (KS dm Γ P st) (fun _ => .err) noFuture [.nat] .nat)
  rw [psG_R _ _ hd, outG_R _ _]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- **`FixClosedAt` at `R`** (PROVED): its `fix` term is closed. -/
theorem fixClosed_R : FixClosedAt defR := rfl

/-- **`FixFlagAt` at `R`** (PROVED, vacuous: the table does not read `R`'s `fix` term as a proof). -/
theorem fixFlag_R (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest) :
    FixFlagAt dm (chainDecisions F) Γ P defR st := by
  intro h
  have hd := decR_KS (dm := dm) (Γ := Γ) P st hg
  have : ((KS dm Γ P st).D.flags [] fixR).2 = true := h
  rw [hd.2.2.2.2] at this
  cases this

/-- **The knot at `R`, computed** (PROVED at any state whose Σ starts with `R`'s entry): every stage of `R`'s closure
as the stage's context forms it is good at member arguments below its bound (the column's computation of the body's
run, `goodBelow_stgK`, in the general vocabulary). -/
theorem stG_good_R (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest)
    (ρ : Assignment) (φ : Future) (b : Nat) (a : List Sem)
    (ha : DomMembers dm.read (psG (KS dm Γ P st) ρ φ defR.doms) a) (hlt : fixRank defR.dec a < b) :
    ∃ o, stG (KS dm Γ P st) ρ φ defR.hs defR.doms defR.cod defR.dec defR.body b a = some o ∧
      OutGood' dm.read (psG (KS dm Γ P st) ρ φ defR.doms) (outG (KS dm Γ P st) ρ φ defR.doms defR.cod) a o := by
  have hd := decR_KS (dm := dm) (Γ := Γ) P st hg
  change DomMembers dm.read (psG (KS dm Γ P st) ρ φ [.nat]) a at ha
  rw [psG_R _ ρ hd] at ha
  obtain ⟨n, rfl⟩ := domMembers_one ha
  change rkR [.el0 Nat n] < b at hlt
  rw [rkR_nat] at hlt
  obtain ⟨o, ho, hr, hf⟩ := goodBelow_stgK (φ := φ) (KS dm Γ P st) ρ hd b n hlt
  refine ⟨o, ?_, ?_⟩
  · show fixStage (KS dm Γ P st) ρ φ (fbG (KS dm Γ P st) ρ φ [.nat] .nat) (lG (KS dm Γ P st) [⟨"n"⟩] [.nat] .nat) formG
      (psG (KS dm Γ P st) ρ φ [.nat]) (outG (KS dm Γ P st) ρ φ [.nat] .nat) (some 0) 0 bodyR b [.el0 Nat n] = some o
    rw [psG_R _ ρ hd, outG_R _ ρ, lG_R _ hd]
    exact ho
  · show OutGood' dm.read (psG (KS dm Γ P st) ρ φ [.nat]) (outG (KS dm Γ P st) ρ φ [.nat] .nat) [.el0 Nat n] o
    rw [psG_R _ ρ hd, outG_R _ ρ]
    exact ⟨hr, fun h => absurd h (by simp [outI]), by rw [hf]; rfl⟩

/-- **`FixLeafAt` at `R`** (PROVED at any witness, at any state whose Σ starts with `R`'s entry): its conclusion, stage
`b + 1` good at member arguments of rank below `b + 1`, holds at `R` outright (`stG_good_R`); the link's hypotheses
(the simulation's conclusion at the leaves, the fundamental lemma's) are not needed there. So at `R` the leaf link says
nothing the column did not already compute; its content (N3 at the leaf's type, [Return], the pop) is exercised only
where a body's run is not computed directly. -/
theorem fixLeaf_R (P : ProgState) (st : MState) {m : Bool} {rest : List GDef} (hg : st.globals = gE m :: rest)
    (w : FixWit) : FixLeafAt dm (chainDecisions F) Γ P defR st w := by
  intro ρ ρa Δa φ π b a ha hlt _ _ _ _ _ _
  exact stG_good_R P st hg ρ φ (b + 1) a ha hlt

/-- The name test that admits every global but `R`. -/
def NR : DataModel.Exists.Knot.NameOk := ⟨fun _ => true, fun _ => true, fun n => n != "R"⟩

/-- **`BodyCongrAt` at `R`** (PROVED at every stage, state and table): `R`'s body names itself only through its own
binding and holds no unknown, so its run reads neither the assignment nor `Δ`, nor the function under check (`RunCtx.cur`, which
no run reads: `Knot.runT_congrN` with the function under check changed), nor the global `R`'s meaning. -/
theorem bodyCongr_R (D : MState → Decisions) (P : ProgState) (st : MState) :
    BodyCongrAt dm D Γ P defR st := by
  intro ρ ρa Δa φ b h s
  have hA := Ochr.Meaning.runT_congrA (ctxBΔ dm D Γ P defR st ρ φ b Δa) (ctxB dm D Γ P defR st ρ φ b).Δ ρa ρ φ true bodyR h s
    (fun σ hσ => by simp [bodyR, Term.anyAtom, Term.anyAtomList] at hσ)
  refine hA.trans ?_
  have hN := DataModel.Exists.Knot.runT_congrN (P.ctx dm D Γ st) dm (ctxB dm D Γ P defR st ρ φ b).C NR ρ φ
    (cur' := some ("R", b))
    ⟨fun _ _ _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩, fun n hn => by
      have hn' : n ≠ "R" := by simpa [NR] using hn
      show (if n = "R" then _ else _) = _
      rw [if_neg hn']; rfl⟩ true bodyR h s rfl
  exact hN.symm

end

end Ochr.Meaning.Steps.Form.Top.RT
