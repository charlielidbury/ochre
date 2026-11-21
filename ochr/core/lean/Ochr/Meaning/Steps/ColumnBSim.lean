import Ochr.Meaning.Steps.ColumnBRuns

/-!
# The step for the body of `B`, composed (lead9)

`def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`: the column's steps (`let_core`, `letB_core`,
`seq_core`, `succ_core`, `zero_core`, `borrow_core`, `assignDeref_core`, `readEnd_core`, each lifted
to `eval` by `eval_of_core`) composed into the step for the body, every side condition discharged
for this program from the states by exact environment (`ColumnBRuns`), the checker's runs of the
sub-terms (`ColumnBRuns`) and the decisions at `B`'s three scopes (`ColumnBStart`). The steps under a
`let` hold at every extension of `Δ` and the assignment (the tail runs after the right-hand side made
unknowns), so each is stated `∀ Δ' ρ'`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnB

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnC ColumnC.Aux

theorem readings_E1 {st : MState} {p : Bool} {xv : Value} (h : st.env.erase = E1 p xv) :
    DecideScope.topReadings st = [duC] :=
  (readings_of h (erase_E1 _ _)).trans rfl

theorem PXY.declY {c : Value} {st : MState} (h : PXY c st) : ∀ f j b, ckVarPos st.env 0 = some (.bind f j) →
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .ref .other := by
  obtain ⟨p, q, l, hp⟩ := h
  obtain ⟨-, -, hl, hck, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  intro f j b hc hb
  rw [hck, ck_E2_0] at hc; cases hc
  rw [hl] at hb; have hb' : some (byB q (.borrow l c)) = some b := hb; cases hb'; rfl

theorem PXY.declX {c : Value} {st : MState} (h : PXY c st) :
    ∀ b, st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some b → b.decl = .other := by
  obtain ⟨p, q, l, hp⟩ := h
  obtain ⟨-, -, hl, -, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  intro b hb
  rw [hl] at hb; have hb' : some (bx p (.loan l)) = some b := hb; cases hb'; rfl

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- (I)'s context conditions read no `Δ`. -/
theorem fundCtx_ext (hc : Strict.FundCtx K) (Δ' : Nat → TyS) : Strict.FundCtx { K with Δ := Δ' } :=
  ⟨hc.globals, hc.sorts⟩

/-- The read of `x` that ends `y`, and the write through `y`, at any extension. -/
theorem sim_write_read (hE : EvalInv) (hZ : ZeroInv) (hA : AssignDerefInv) (hVE : VarEndInv) (hI : InvSteps)
    (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K) (hd : DecTab K.D stC)
    (hInv : ∀ sc p, K.D.invalidated sc p = []) (g : Nat) (Δ' : Nat → TyS) (ρ' : Assignment) :
    EvalSim { K with Δ := Δ' } ρ' φ (g + 6) (.place (.var 1)) (PXY .zero) (· = true) ∧
      EvalSim { K with Δ := Δ' } ρ' φ (g + 6) writeB (PXY (.succ .zero)) (· = true) := by
  refine ⟨?_, ?_⟩
  · exact eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.readings, declOf_x1 hd]; exact duC_ok)
      (readEnd_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hVE hI hPL (n := g + 3)
        (fun _ h => h.readPre) (fun _ h => h.declX))
  · have hz : EvalSim { K with Δ := Δ' } ρ' φ (g + 3) .zero (PXY (.succ .zero)) :=
      eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
        (fun st hst => by rw [hst.readings, declOf_Zy hd]; exact duC_ok) (zero_coreSim hZ hI)
    exact eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.readings]; exact declOf_write_ok hd)
      (assignDeref_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hA hI hPL (fundCtx_ext hc Δ') (n := g + 3) (i := 0) (u := .zero)
        hz (fun a b h ha => ha.kern h) (fun _ h => h.derefVar (.succ .zero)) (fun _ h => h.declY)
        (fun st h => by rw [h.readings]; exact flags_Zy hd) (fun T s => by rw [runT_zero, runT_zero])
        (fun st₀ st₁ bh hint v₀ T₀ hP hm htd hD h => by
          obtain ⟨rfl, rfl, hk, -⟩ := run_zero hE hZ hm hD (by rw [hP.readings]; exact flags_Zy hd)
            (by rw [hP.readings, declOf_Zy hd]; exact duC_ok) htd h
          exact ⟨.zero, hk.env, fun T e => by cases e; rfl⟩)
        (fun sc => hInv sc _))

/-- The sequence `*y := Z; x`, at any extension. -/
theorem sim_seq (hE : EvalInv) (hZ : ZeroInv) (hA : AssignDerefInv) (hVE : VarEndInv) (hSq : SeqInv)
    (hI : InvSteps) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K) (hd : DecTab K.D stC)
    (hInv : ∀ sc p, K.D.invalidated sc p = []) (g : Nat) (Δ' : Nat → TyS) (ρ' : Assignment) :
    EvalSim { K with Δ := Δ' } ρ' φ (g + 9) seqB (PXY (.succ .zero)) (· = true) :=
  eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
    (fun st hst => by rw [hst.readings, declOf_seq hd]; exact duC_ok)
    (seq_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hSq hI (fundCtx_ext hc Δ') (n := g + 6)
      (fun st stW hst hW => by rw [hst.readings, hW.readings]; exact (declOf_seq hd).trans (declOf_x1 hd).symm)
      (sim_write_read hE hZ hA hVE hI hPL hc hd hInv g Δ' ρ').2 (fun a b h ha => ha.kern h)
      (fun Δ'' ρ'' => (sim_write_read hE hZ hA hVE hI hPL hc hd hInv g Δ'' ρ'').1)
      (fun st h => by rw [h.readings]; exact flags_write hd) (fun st h => by rw [h.readings]; exact flags_x1 hd)
      (fun st₀ st₁ bh v₀ T₀ hP hm htd hD h => by
        obtain ⟨rfl, -, hm₁, -⟩ := run_write hE hZ hA hd hP hm htd hD h
        exact ⟨rfl, hm₁⟩)
      (fun st st₀ st₁ bh v₀ T₀ hP hk hm htd hD h => (run_write hE hZ hA hd (hP.kern hk) hm htd hD h).2.2.2)
      (fun a b h ha => ha.kern h) (fun _ _ => by simp [seqB, writeB, Term.valsOk])
      (fun m σ hσ => by simp [seqB, writeB, Term.anyAtom] at hσ) (by decide))

/-- `&x`, at any extension. -/
theorem sim_bor (hE : EvalInv) (hB : BorrowNumInv) (hI : InvSteps) (hd : DecTab K.D stC)
    (hInv : ∀ sc p, K.D.invalidated sc p = []) (g : Nat) (Δ' : Nat → TyS) (ρ' : Assignment) :
    EvalSim { K with Δ := Δ' } ρ' φ (g + 9) (.borrow (.var 0)) PX (· = true) :=
  eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
    (fun st hst => by rw [hst.readings, declOf_bor hd]; exact duY_ok)
    (borrow_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hB hI (n := g + 6) (i := 0)
      (fun _ h => h.borrowPre) (fun sc => hInv sc _))

/-- The inner `let y = &x; *y := Z; x`, at any extension. -/
theorem sim_inner (hE : EvalInv) (hZ : ZeroInv) (hB : BorrowNumInv) (hA : AssignDerefInv) (hVE : VarEndInv)
    (hSq : SeqInv) (hL : LetInv) (hDN : DropNoopInv) (hI : InvSteps) (hPL : PlaceLocal K.D)
    (hc : Strict.FundCtx K) (hd : DecTab K.D stC) (hInv : ∀ sc p, K.D.invalidated sc p = []) (g : Nat)
    (Δ' : Nat → TyS) (ρ' : Assignment) :
    EvalSim { K with Δ := Δ' } ρ' φ (g + 12) innerB PX (· = true) :=
  eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
    (fun st hst => by rw [hst.readings, declOf_inner hd]; exact duC_ok)
    (letB_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hL hDN hI hPL (fundCtx_ext hc Δ') (n := g + 9)
      (fun st stB hst hXB => by rw [hst.readings, hXB.readings]; exact (declOf_inner hd).trans (declOf_seq hd).symm)
      (sim_bor hE hB hI hd hInv g Δ' ρ') (fun a b h ha => ha.kern h)
      (fun Δ'' ρ'' => sim_seq hE hZ hA hVE hSq hI hPL hc hd hInv g Δ'' ρ'')
      (fun st h => by rw [h.readings]; exact flags_bor hd) (fun st h => by rw [h.readings]; exact flags_seq hd)
      (fun st h => by rw [h.readings, declOf_bor hd]; rfl)
      (fun st st₀ st₁ bh v₀ T₀ hP hk hm htd hD h => by
        obtain ⟨p, l, rfl, rfl, hm₁, he₁⟩ := run_bor hE hB hd (hP.kern hk) hm htd hD h
        obtain ⟨ha, hv, -⟩ := env_facts he₁ (erase_E1 _ _)
        refine ⟨l, .succ .zero, rfl, .succ .zero, rfl, fun q l' hq => ?_, size_E1 he₁, ?_, hm₁⟩
        · rw [ha, allPos_E1, List.mem_singleton] at hq; subst hq; rw [hv]; rfl
        · rw [readings_E1 he₁, hP.readings])
      (fun st st₀ st₁ bh v₀ p hP hk hm htd hD h => by
        obtain ⟨p', l, rfl, -, -, he₁⟩ := run_bor hE hB hd (hP.kern hk) hm htd hD h
        refine ⟨p', p, l, ?_⟩
        show Env.erase (Env.pushBindE st₁.env _ _ _ _ _) = _
        rw [readings_E1 he₁, declOf_bor hd, erase_pushBindE, he₁, push_E1])
      (fun a b h ha => ha.kern h) (fun _ _ => by simp [seqB, writeB, Term.valsOk])
      (fun m σ hσ => by simp [seqB, writeB, Term.anyAtom] at hσ) (by decide)
      (fun stB st₂ bh r T? hXB hm htd hD h => by
        obtain ⟨-, -, p, q, xv, -, he⟩ := run_seq hE hZ hA hVE hSq hd hXB hm htd hD h
        obtain ⟨fr, hfr, hbs⟩ := top_of_erase ((erase_E2 p q xv .bot).trans he.symm)
          (fr := { binds := #[bx p xv, byB q .bot] }) rfl
        exact ⟨fr, byB q .bot, hfr, by rw [hbs]; rfl, .inl rfl⟩))

/-- **The step for the body of `B`** (`let x = S(Z); let y = &x; *y := Z; x`, typed, at any fuel from
`15`): composed from the column's steps, every side condition of each discharged for this program
from the machine facts, the state-level lemmas, the table aligned at `stC` and local in its places,
with D112's invalidation empty. -/
theorem sim_bodyB (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hB : BorrowNumInv) (hA : AssignDerefInv)
    (hVE : VarEndInv) (hSq : SeqInv) (hL : LetInv) (hDN : DropNoopInv) (hI : InvSteps) (hPL : PlaceLocal K.D)
    (hc : Strict.FundCtx K) (hd : DecTab K.D stC) (hInv : ∀ sc p, K.D.invalidated sc p = []) (g : Nat) :
    EvalSim K ρ φ (g + 15) bodyB P0 (· = true) := by
  have hz : EvalSim K ρ φ (g + 9) .zero P0 :=
    eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.readings]; exact declOf_Z_ok hd) (zero_coreSim hZ hI)
  have hsz : EvalSim K ρ φ (g + 12) (.succ .zero) P0 (· = true) :=
    eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.readings, declOf_SZ hd]; exact duC_ok)
      (succ_core hS hI hz.restrict (fun a b h ha => ha.kern h) (fun st hst => by rw [hst.readings]; exact flags_Z hd)
        (fun s => by rw [runT_zero, runT_zero])
        (fun st₀ st₁ bh v₀ T₀ hT₀ _ hm₀ htd₀ hD₁ h => by
          obtain ⟨rfl, rfl, -, -⟩ := run_zero hE hZ hm₀ hD₁ (by rw [hT₀.readings]; exact flags_Z hd)
            (by rw [hT₀.readings]; exact declOf_Z_ok hd) htd₀ h
          exact ⟨.zero, fun T hT => by cases hT; rfl⟩))
  have hlet : CoreSim K ρ φ (g + 13) bodyB P0 (· = true) :=
    let_core hL hDN hI hPL hc (n := g + 12)
      (fun st stB hst hXB => by rw [hst.readings, hXB.readings]; exact (declOf_bodyB hd).trans (declOf_inner hd).symm)
      hsz (fun a b h ha => ha.kern h)
      (fun Δ' ρ' => sim_inner hE hZ hB hA hVE hSq hL hDN hI hPL hc hd hInv g Δ' ρ')
      (fun st hst => by rw [hst.readings]; exact flags_SZ hd) (fun st hst => by rw [hst.readings]; exact flags_inner hd)
      (fun st hst => by rw [hst.readings, declOf_SZ hd]; rfl)
      (fun st st₀ st₁ bh v₀ T₀ hP hk₀ hm₀ htd₀ hD₁ h => by
        have hP₀ := hP.kern hk₀
        obtain ⟨rfl, hT', he, hm₁⟩ := run_SZ hE hZ hS hm₀ hD₁ (by rw [hP₀.readings]; exact flags_SZ hd)
          (by rw [hP₀.readings]; exact flags_Z hd) (by rw [hP₀.readings, declOf_SZ hd]; exact duC_ok)
          (by rw [hP₀.readings]; exact declOf_Z_ok hd) htd₀ h
        refine ⟨.succ .zero, hT', ?_, ((topReadings_kern hk₀).trans (topReadings_of_erase he)).symm, hm₁⟩
        rw [← size_of_erase he, size_of_erase (hP₀.trans erase_stC.symm)]; exact Nat.zero_lt_one)
      (fun st st₀ st₁ bh v₀ p hP hk hm₀ htd₀ hD₁ h => by
        have hP₀ := hP.kern hk
        obtain ⟨rfl, -, he, -⟩ := run_SZ hE hZ hS hm₀ hD₁ (by rw [hP₀.readings]; exact flags_SZ hd)
          (by rw [hP₀.readings]; exact flags_Z hd) (by rw [hP₀.readings, declOf_SZ hd]; exact duC_ok)
          (by rw [hP₀.readings]; exact declOf_Z_ok hd) htd₀ h
        refine ⟨p, ?_⟩
        show Env.erase (Env.pushBindE st₁.env _ _ _ _ _) = _
        rw [← topReadings_of_erase he, hP₀.readings, declOf_SZ hd, erase_pushBindE, ← he, hP₀, push_E0])
      (fun a b h ha => ha.kern h) (fun _ _ => by simp [innerB, seqB, writeB, Term.valsOk])
      (fun m σ hσ => by simp [innerB, seqB, writeB, Term.anyAtom] at hσ) (by decide)
      (fun stB st₂ bh r T? hXB hm htd hD h => (run_inner hE hZ hB hA hVE hSq hL hDN hd hXB hm htd hD h).2.2)
  exact eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
    (fun st hst => by rw [hst.readings, declOf_bodyB hd]; exact duC_ok) hlet

end

/-! ## The assembly -/

/-- **The column applied to `def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`.** At every data
model, assignment and future, and every table of decisions aligned with the checker at the end of the
run, local in its places, with D112's invalidation empty: for every run of the checker on the body
from a state with `stC`'s kernel, in mode (where `checkDef` evaluates a constant's body), the strict
run of the body from the reference state succeeds, and its value is `0`, a member of `Nat`, at the
type `Nat`. Assumed: facts about the checker alone (`FormMachine.lean`), the table's growth and
`DecTab.back`. -/
theorem column_B (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hB : BorrowNumInv) (hA : AssignDerefInv)
    (hVE : VarEndInv) (hSq : SeqInv) (hL : LetInv) (hDN : DropNoopInv) (hI : InvSteps) (hback : DecBack)
    {g : Nat} (hgrow : GrowsM (Ochr.eval (g + 15) true bodyB (some .tNat))) (dm : DataModel) (D : Decisions)
    (hPL : PlaceLocal D) (hInv : ∀ sc p, D.invalidated sc p = []) (ρ : Assignment) (φ : Future)
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hk : Kern stC st) (hm : Mode st)
    (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval (g + 15) true bodyB (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm D) ρ φ st.tailNext (hintM (KC dm D) ρ (some .tNat)) bodyB (SM' (KC dm D) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 0 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat := by
  have hd : DecTab D stC := DecTab.of_kern hk.symm (hback D st st' hD (hgrow st bh _ st' h))
  have hP : P0 st := hk.env.symm.trans erase_stC
  obtain ⟨rfl, rfl⟩ := run_bodyB (D := D) hE hZ hS hB hA hVE hSq hL hDN hd hP hm (.inl htd) hD h
  have hsc : scopeOf (SM' (KC dm D) ρ stC) = [] := by rw [scopeOf_sstate']; exact topReadings_stC
  obtain ⟨ρ', Δ', π', r, s', -, hx, hmean, hagree, -, -, -⟩ :=
    sim_bodyB (K := KC dm D) (ρ := ρ) (φ := φ) hE hZ hS hB hA hVE hSq hL hDN hI hPL (fundCtx_KC dm D) hd hInv g
      st st' true (some .tNat) _ _ (SM' (KC dm D) ρ stC) id hP rfl hm (.inl htd) ((pre_stC dm D ρ).of_kern hk)
      ((rel_stC dm D ρ φ).of_kern hk) (sgood_stC dm D ρ φ) (by simp [bodyB, Term.valsOk])
      (fun σ h => by simp [bodyB, Term.anyAtom] at h) (by decide)
      (by rw [hsc]; exact flags_bodyB hd) (fun e => by cases e) hD bh h
  have h0 : r.1 = .el0 Nat 0 := by rw [← hmean]; rfl
  refine ⟨r, s', hx, h0, by rw [h0]; exact ⟨0, rfl⟩, ?_⟩
  rw [← hagree _ rfl]; rfl

end Ochr.Meaning.Steps.Form.ColumnB
