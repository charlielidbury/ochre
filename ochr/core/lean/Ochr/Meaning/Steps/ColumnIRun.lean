import Ochr.Meaning.Steps.ColumnIFix
import Ochr.Meaning.Steps.ColumnCFF
import Ochr.Meaning.Steps.Machine.FragRuns
import Ochr.Meaning.Steps.ParGuards

/-!
# The column `I`: the reference's `.fix` run of `I` from the checker's acceptance (model5, 2026-11-21)

`def I (n : Nat) : Nat := S(#0)` (core; the check of the surface's `succFn`, docs/31 D124). Since docs/31
D126 the reference runs a closure's body in the checker's frames (`SState.under`): for `I`, formed in
the empty state, the body state at an argument `a` IS `SM'` of the checker's start state `stI` under
`σ0 ↦ a` (`start_I`), so the body's reference run is `body_runI`'s, with no assumed bridge between frame
shapes (the deleted `FrameDrop0`). Assembled here: the body inside `fixBodyAt` (`fixBodyAt_I`), the
closure's membership and the `.fix` run (`column_I_run`), with the machine lane's proved facts
discharged (`column_I_ff`), and from `checkDef`'s acceptance through the checker fact `FixRunI`
(`column_I_def`).

What `column_I_ff` assumes, fact by fact: `VarNumAInv` (the read of a variable holding a numeral over
an unknown) and `InvNumA` (the state-level lemmas for such numerals), both facts about the checker read
against it and judged true, unproved. Nothing about the model. `column_I_def` assumes `FixRunI` too
(the inversion of `checkDef defI` down to the body's run; `#guard`ed below).
-/

namespace Ochr.Meaning.Steps.Form.ColumnI

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness

section
variable {dm : DataModel} {D : Decisions} {ρ : Assignment} {φ : Future}

/-- **The checker's start state, read as a reference state** under `σ0 ↦ a`: the frames `[{}, frI]`. -/
theorem env_SM (a : Nat) : (SM' (KI dm D φ) (ρAt ρ a) stI).env = [{}, frI dm.read φ a] := by
  have hv0 : ∀ ψ, Env.mean (KI dm D φ).dm (KI dm D φ).M (KI dm D φ).Γ (ρAt ρ a) ψ stI.env (.bind 1 0) = selfSem dm.read φ :=
    fun ψ => by
      have := Aux.valAt_SM_eq (dm := dm) (D := D) (φ := φ) (ρ := ρAt ρ a) (.bind 1 0) ψ
      unfold SM' at this; rw [sstate_valAt] at this; exact this
  have hv1 : ∀ ψ, Env.mean (KI dm D φ).dm (KI dm D φ).M (KI dm D φ).Γ (ρAt ρ a) ψ stI.env (.bind 1 1) = .el0 Nat a :=
    fun ψ => by
      have := Aux.valAt_SM_eq (dm := dm) (D := D) (φ := φ) (ρ := ρAt ρ a) (.bind 1 1) ψ
      unfold SM' at this; rw [sstate_valAt] at this; exact this
  have ht0 : Binding.refTy (KI dm D φ).dm (KI dm D φ).M (KI dm D φ).Γ (ρAt ρ a) stI.env 1 0 selfB = .plain (selfTy dm.read) := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KI, CI, selfB, RunCtx.M, codeMeaning]
  have ht1 : Binding.refTy (KI dm D φ).dm (KI dm D φ).M (KI dm D φ).Γ (ρAt ρ a) stI.env 1 1 nB = .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]
    rfl
  unfold SM' MState.sstate
  simp only [stI, List.zipIdx, List.map, frI, Nat.zero_add]
  rw [show (#[{}, { binds := #[selfB, nB] }] : Env) = stI.env from rfl, ht0, ht1]
  simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
  exact ⟨⟨funext hv0, rfl⟩, funext hv1, rfl⟩


/-- `stI` lends nothing. -/
theorem sitesOf_stI (l : Nat) : Env.sitesOf stI.env l = [] := by
  unfold Env.sitesOf; rw [Aux.allPos_stI]
  simp [valAt, stI, selfB, nB, Value.sitesOf]

/-- Two reference states with the same fields are equal. -/
theorem sstate_ext {s t : SState} (h1 : s.env = t.env) (h2 : s.shape = t.shape) (h3 : s.nextLoan = t.nextLoan)
    (h4 : s.lent = t.lent) (h5 : s.heldTy = t.heldTy) (h6 : s.heldMem = t.heldMem) : s = t := by
  cases s; cases t; simp_all

/-- **`fixBodyAt`'s state for `I` is the checker's start state** (docs/31 D126): `self` (the stage-0
closure at the weakened type) and the parameter `a`, pushed on the empty state under its fresh bottom
frame, give exactly `SM'` of `stI` under `σ0 ↦ a`; no bridge between frame shapes is left. For any `fb`
that reads the parameter at `Nat`, `.other` and the codomain `.other` (the `.fix` clause's, `fixDecI`). -/
theorem start_I (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    (a : Nat) :
    ([Sem.el0 Nat a].zip psI).foldl (fixStep fb)
        ((emptyState 0).under.pushBind { ty := .plain (selfTy dm.read), val := fun _ => selfSem dm.read φ, decl := .pi fb.2.2 }, [], [])
      = (SM' (KI dm D φ) (ρAt ρ a) stI, [.el0 Nat a], []) := by
  have he := env_SM (dm := dm) (D := D) (ρ := ρ) (φ := φ) a
  simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
    Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append, Prod.mk.injEq, and_true]
  apply sstate_ext
  · rw [he]; rfl
  · funext p
    show p.down?.bind (fun _ => none) = Env.shape stI.env p
    rw [Aux.shape_stI]; cases p.down? <;> rfl
  · rfl
  · funext l
    show ([] : List Site) = Env.sitesOf stI.env l
    rw [sitesOf_stI]
  · rfl
  · rfl


/-- **`I`'s body run inside the `.fix` clause** (stage 1, rank 0): at every number `a`, `fixBodyAt`
returns `S(a)` and no final (no borrow parameter), from the checker's successful run of the body
(`body_runI`; the run reads neither the assignment, the tail flag nor the hint, `runT_bodyI`, and leaves
no live label, so the pop's ends are `EndsOk []`). -/
theorem fixBodyAt_I (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') (a : Nat) :
    ∃ o, fixBodyAt (KI dm D φ) ρ φ fb (emptyState 0) psI outI (selfTy dm.read) 0 bodyI (selfSem dm.read φ) [.el0 Nat a]
        = some o ∧ o.result = .el0 Nat (a + 1) ∧ o.finals = [] := by
  obtain ⟨r, s', hr, hr1, -, hl⟩ := body_runI hE hS hI hV hN hlow dm D ρ φ a hDI hk hm htd hD h
  refine ⟨⟨r.1, [], r.2.label⟩, ?_, hr1, rfl⟩
  unfold fixBodyAt
  dsimp only
  rw [start_I (dm := dm) (D := D) (ρ := ρ) (φ := φ) fb h1 h2 a]
  dsimp only
  rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `I` returns data
  rw [runT_bodyI (KI dm D φ) φ ρ (ρAt ρ a) true st.tailNext (fb.2.1 [.el0 Nat a])
    (hintM (KI dm D φ) (ρAt ρ a) hint), hr]
  dsimp only
  rw [hl]
  simp [endsOk_nil]


/-- `I` captures nothing. -/
theorem capOrder_fixI : capOrder fixI = [] := rfl

/-- **`I`'s closure, as the reference's `.fix` clause forms it from the empty state** (where a global's
function is formed, `Program.defMeaning`): the run succeeds, at the Π-type `Π(n : Nat). Nat`
(`piTyAt _ 1 psI outI`), leaves the state as it was, and the closure is a MEMBER of that type
(`Witness.fixClo_mem_nonrec`: at every member argument the body runs to a member of `Nat`; `run_fix_of_mem`).
From the checker's successful run of the body from a state with `stI`'s kernel, at a table aligned with
the checker at `stI` and at the run's end. The checker facts are hypotheses: `EvalInv`, `SuccInv`,
`InvSteps`, `EvalLow` (proved by the machine lane; discharged in `column_I_ff`), `VarNumAInv`, `InvNumA`
(read against the checker and judged true, unproved). -/
theorem column_I_run (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') (tl : Bool) (hint' : TyS) :
    ∃ f, runT (KI dm D φ) ρ φ tl hint' fixI (emptyState 0) = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧
      f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  obtain ⟨hd1, hd2, hps, hfl⟩ := fixDecI hDI
  have hsc : scopeOf (emptyState 0) = [] := rfl
  have hpd : (KI dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (KI dm D φ) (emptyState 0) [⟨"n"⟩] [.nat] .nat = 1 := hps
  have h1 : bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat] = [(fun _ => .plain TyM.nat, .other)] :=
    bindsOf_nat _ ρ φ _ hpd
  have h2 : (KI dm D φ).D.typeDecl ((KI dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat = .other := by
    show D.typeDecl (D.teleDecls [] [.nat]) .nat = .other
    simp [Decisions.teleDecls, hd1, hd2]
  have hty : fixTy (KI dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, runDoms_nat _ ρ φ _ hpd, codOf_nat]; rfl
  have hmem : fixClo (KI dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat none bodyI ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
    unfold fixClo
    rw [hty, hsort, runDoms_nat _ ρ φ _ hpd, codOf_nat]
    refine fixClo_mem_nonrec _ 1 (emptyState 0) psI outI _ 0 bodyI ⟨Nat.le_refl 1, by omega⟩ rfl
      (fun _ _ => Nat.le_refl 1) fun args ha => ?_
    obtain ⟨hlen, hargs⟩ := ha
    match args, hlen with
    | [x], _ =>
      obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
      subst hx
      obtain ⟨o, ho, hr, hf⟩ := fixBodyAt_I (dm := dm) (D := D) (ρ := ρ) (φ := φ) hE hS hI hV hN hlow
        (bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat],
          fixCod (KI dm D φ) ρ φ (emptyState 0) (bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat]) ([.nat].map Term.isRefTy) .nat,
          (KI dm D φ).D.typeDecl ((KI dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat) h1 h2 hDI hk hm htd hD h m
      refine ⟨o, ho, ⟨?_, fun i d hi hd => ?_⟩, by rw [hf]; rfl⟩
      · rw [hr]; exact ⟨m + 1, rfl⟩
      · rcases i with _ | i
        · simp [psI] at hi; subst hi; cases hd
        · simp [psI] at hi
  refine ⟨_, ?_, hmem⟩
  unfold fixI
  rw [run_fix_of_mem tl hint' ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none bodyI (emptyState 0) hfl (by rw [← fixI, capOrder_fixI]; trivial) (by rw [hty]; exact hmem), hty]
  rfl

end

/-- **The column `I` at the checker's own decisions**: for every successful typed run of the checker's
`eval` on `I`'s body from a state with `stI`'s kernel (`checkFix`'s body state), in the plain mode with no
handed-down reading, the reference's `.fix` clause, under the fuel-free table at the run's end, forms
`I`'s closure from the empty state: the run succeeds at `Π(n : Nat). Nat` and the closure is a member of
it; for every data model, assignment, future, tail flag and hint. Assumes 2 facts about the checker:
`VarNumAInv`, `InvNumA` (read and judged true, unproved). `EvalInv`, `SuccInv`, `InvSteps`, `EvalLow`,
`DecBack` and the tables' growth are the machine lane's proofs. -/
theorem column_I_ff (hV : VarNumAInv) (hN : InvNumA) (dm : DataModel) (ρ : Assignment) (φ : Future)
    {n : Nat} {hc : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true bodyI hc) st bh (v, T?) st') (tl : Bool) (hint : TyS) :
    ∃ f, runT (KI dm (checkerDecisionsFF st') φ) ρ φ tl hint fixI (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  have hD : DecTab (checkerDecisionsFF st') st' :=
    decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')
  have hDI : DecTab (checkerDecisionsFF st') stI :=
    DecTab.of_kern hk.symm (Machine.decBack _ st st' hD (grows_eval _ _ _ _ st bh _ st' h))
  exact column_I_run Machine.evalInvR succInv Machine.invSteps hV hN Machine.evalLow hDI hk hm htd hD h tl hint

/-- **The checker's acceptance of `I`, inverted down to its body's run** (a fact about the checker,
assumed; the machine lane's to prove): where `checkDef defI` succeeds from the empty state, `checkFix`
ran the body's typed `eval` (the general case of `checkTail`, `S(#0)` being no form it splits on, at
the goal `Nat`) from a state with `stI`'s kernel, in the plain mode, with no handed-down reading.
Checked by running the checker: the start state is `Steps/ParGuards`' (`kernelOk`, `modeOk`, recorded
at the entry of a body with `I`'s signature; the kernel does not depend on the body) and the derivation
of `checkDef defI` below. -/
def FixRunI : Prop :=
  ∀ (fuel : Nat) (st₁ : MState), Runs (checkDef ParGuards.defI) {} fuel () st₁ →
    ∃ (n : Nat) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
      Kern stI st ∧ Mode st ∧ st.tailDecl = none ∧ Runs (Ochr.eval n true bodyI (some .tNat)) st bh (v, T?) st'

namespace Guards

/-- The trace of `checkDef defI` from the empty state (`Config.trace`, and with `derivation` the rules
applied, in the paper's names). -/
def linesOf (cfg : Config) : List String :=
  match runMachine (checkDef ParGuards.defI) { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

-- `checkFix` sets the goal, runs the body to one path end of type `Nat`: no split, no join
#guard linesOf { trace := true } == ["[Def] I: goal Nat", "[Def] I: path ends with type Nat against goal Nat"]
-- the body's run is the read of `n` (moved) and the return of `S(σ0) : Nat`, holding no borrow
#guard linesOf { trace := true, derivation := true } ==
  ["[Def] I: goal Nat", "[Read] its declared type is not a copy type: moved out",
    "[Return] I returns it: S(σ0) : Nat, with 0 place(s) held by borrow",
    "[Def] I: path ends with type Nat against goal Nat"]

end Guards

/-- **The column `I` from the checker's acceptance of `def I`**: where `checkDef defI` succeeds from the
empty state, there is a run of the checker's body (its end state `st'`) such that, under the fuel-free
table at its end, the reference forms `I`'s closure from the empty state, a member of `Π(n : Nat). Nat`.
Assumes 3 facts about the checker: `FixRunI`, `VarNumAInv`, `InvNumA`. -/
theorem column_I_def (hF : FixRunI) (hV : VarNumAInv) (hN : InvNumA) (dm : DataModel) (ρ : Assignment) (φ : Future)
    {fuel : Nat} {st₁ : MState} (hacc : Runs (checkDef ParGuards.defI) {} fuel () st₁) (tl : Bool) (hint : TyS) :
    ∃ st' : MState, ∃ f, runT (KI dm (checkerDecisionsFF st') φ) ρ φ tl hint fixI (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  obtain ⟨n, st, st', bh, v, T?, hk, hm, htd, h⟩ := hF fuel st₁ hacc
  exact ⟨st', column_I_ff hV hN dm ρ φ hk hm htd h tl hint⟩

end Ochr.Meaning.Steps.Form.ColumnI
