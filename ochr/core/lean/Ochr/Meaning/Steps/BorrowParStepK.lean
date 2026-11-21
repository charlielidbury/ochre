import Ochr.Meaning.Steps.BorrowParStep
import Ochr.Meaning.Steps.MoveOut
import Ochr.Meaning.Steps.BotWriteGood
import Ochr.Meaning.Steps.ColumnBRuns

/-!
# `K`'s body step in the form (lead20, 2026-11-22; docs/31 D145)

`def K (r : &Nat) : &Nat := r`. The body reads the borrow parameter whole, which MOVES the borrow out of `r`:

* in the checker (`BodyKInv`, pinned in `Steps/BorrowParGuards.lean`): the value `borrow₀ σ0 : &Nat` in flight, `r ↦ ⊥`
  (`endK`), the cell `r° ↦ loan₀` untouched, label `0` still live (now held by the value in flight);
* in the reference (`readPlace` at a copy decision `false`): [Access] at `r` ends nothing (label `π 0`'s one site is the
  cell, `Rel.sites`), the content is read at the typed future (`ρ σ0`'s number `m`), `r` is set to `moved`, label `π 0` is
  taken from it and parked in a fresh temporary of the top frame holding `m`; the result is `m` at `r`'s stored type
  labelled `π 0`.

What relates the returned borrow on the two sides: the checker's value in flight `borrow₀ σ0` and the reference's
parked temporary are each label `0`'s / `π 0`'s one holder (`Rel.sim`'s temporary clauses), with the same content
(`m`); the cell is the label's one site on both sides (`Rel.sites`), unchanged; the record (`heldMem (π 0)`, the
argument) and the held type (`Nat`) are unchanged, and the holder's type is now the recorded one (`holderTy` of a
temporary is `heldTy`, which a good state's equals the old binding's stored type, `ColumnWrite.heldTy_eq_holderTy`).
The relation after is `MoveOut.rel_moveOut`, general.

The end of the body (`fixBodyAt`, D141): the codomain is a borrow, so the frame pop keeps label `π 0` (the returned
label, `keep`) and ends nothing; the cell's final is the future at `π 0`, what the caller leaves in the returned borrow.
In the checker, [Return] checks the value `borrow₀ σ0 : &Nat` against the goal `&Nat` and finds `0 place(s) held by
borrow` (the returned borrow reborrows none of the body's own places: it is the parameter's, lent at the cell); nothing
ends, and `checkFix` discards the body state, the cell with it (the derivation is pinned in `Steps/BorrowParGuards.lean`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The invariant across moving a borrow out of a binding into flight** (a fact about the checker alone, for the
machine lane; docs/31 D145): a binding holding `borrow_l w`, `w` a numeral over unknowns of type `Nat` (`NumAt`), read
whole: the binding set to `⊥` and `borrow_l w` pushed as the top temporary (the value in flight, at any stored type).
`Inv` before gives `Inv` after. Its instance at `K`'s body (`r` at `stK`) is the checker's own end state (guarded:
`Steps/BorrowParGuards.lean`, `endK` is `stK` with `r ↦ ⊥`, and the value is `r`'s borrow). Not run (`Inv` is not
computable). -/
def InvMoveBorrow : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j l : Nat) (w : Value) (T? : Option Value),
    valAt st.env (.bind f j) = .borrow l w → NumAt st w → Inv D Γ st.norm →
    Inv D Γ ({ st with env := Env.setAtE st.env (.bind f j) .bot }.withTempT (.borrow l w) T?).norm

theorem lookup_stK_r {st : MState} (hk : Kern stK st) :
    st.env[1]?.bind (fun fr : Frame => fr.binds[1]?) = some (rB (.borrow 0 (.abs 0))) := by
  rw [← lookup_erase, ← hk.env, lookup_erase]; rfl

theorem ckVarPos_stK {st : MState} (hk : Kern stK st) : ckVarPos st.env 0 = some (.bind 1 1) := by
  rw [← ckVarPos_erase, ← hk.env, ckVarPos_erase]; rfl

theorem valAt_stK_r {st : MState} (hk : Kern stK st) : valAt st.env (.bind 1 1) = .borrow 0 (.abs 0) := by
  rw [← valAt_erase, ← hk.env, valAt_erase]; rfl

/-- The checker's end state is `K`'s start with `r ↦ ⊥`, up to the kernel. -/
theorem kern_moveK {st st' : MState} (hk : Kern stK st) (hk' : Kern endK st') :
    Kern { st with env := Env.setAtE st.env (.bind 1 1) .bot } st' := by
  refine ⟨?_, hk.globals.symm.trans hk'.globals, hk.inds.symm.trans hk'.inds, hk.nextLoan.symm.trans hk'.nextLoan,
    hk.nextAbs.symm.trans hk'.nextAbs, hk.absTy.symm.trans hk'.absTy, hk.absDecl.symm.trans hk'.absDecl,
    hk.refs.symm.trans hk'.refs, hk.etaRefs.symm.trans hk'.etaRefs, hk.goal.symm.trans hk'.goal,
    hk.neutrals.symm.trans hk'.neutrals, hk.liveScope.symm.trans hk'.liveScope⟩
  show Env.erase (Env.setAtE st.env (.bind 1 1) .bot) = st'.env.erase
  rw [ColumnB.erase_setAtE, ← hk.env, ← hk'.env]
  simp [stK, endK, Env.setAtE, Env.erase, Frame.erase, cellR, selfK, rB]

theorem erase_setAtE_erase (E : Env) (f j : Nat) (v : Value) :
    Env.erase (Env.setAtE (Env.erase E) (.bind f j) v) = Env.setAtE (Env.erase E) (.bind f j) v := by
  simp only [Env.erase, Env.setAtE]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_modify]
    split
    · simp [Frame.erase]
    · simp [Frame.erase]

/-- The unknowns a state names after a binding is set to `⊥`, read off its kernel, it named before. -/
theorem refd_setBot_norm {st : MState} {f j : Nat} (hp : Pos.bind f j ∈ allPos st.env) :
    ∀ σ, ({ st with env := Env.setAtE st.env (.bind f j) .bot } : MState).norm.Refd σ → st.norm.Refd σ := by
  intro σ h
  have e : ({ st with env := Env.setAtE st.env (.bind f j) .bot } : MState).norm =
      { st.norm with env := Env.setAtE st.norm.env (.bind f j) .bot } := by
    unfold MState.norm; rw [ColumnB.erase_setAtE, erase_setAtE_erase]
  rw [e] at h
  exact refd_setAtE (st := st.norm) (steps := []) (by rw [show st.norm.env = st.env.erase from rfl, allPos_erase]; exact hp)
    (by simp [Value.updAt]) h

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **`K`'s body, simulated** (`Sim`): for every checker run of `r`'s typed `eval` from a state with `stK`'s kernel, plain
mode, no handed-down reading, at decisions that classify `r` as neither a statement nor a proof and read it as not
copied, every related good reference state runs `r` to the number `ρ σ0` at `r`'s stored type labelled `π 0`, with `r`
moved and the borrow parked in a temporary; related again with `borrow₀ σ0` in flight at `&Nat` (`rel_moveOut`).
ASSUMES 2 facts about the checker, `BodyKInv` and `InvMoveBorrow`; no model fact. -/
theorem body_simK (hB : BodyKInv) (hI : InvMoveBorrow) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stK st) (hm : Mode st) (htd : st.tailDecl = none)
    (hfl : K.D.flags (DecideScope.topReadings st) bodyK = (false, false))
    (hcp : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var 0)) = false)
    (h : Runs (Ochr.eval n true bodyK hint) st bh (v, T?) st') :
    Sim K ρ φ st st' (runT K ρ φ st.tailNext (hintM K ρ hint) bodyK) v T? := by
  obtain ⟨rfl, rfl, hk'⟩ := hB n hint st st' bh v T? hk hm htd h
  have hkm := kern_moveK hk hk'
  intro s π hp hr hS
  have hb := lookup_stK_r hk
  have hvb := valAt_stK_r hk
  have hres : resolve s (.var 0) = some (.bind 1 1, []) :=
    rel_resolve_ck K ρ φ st s π (.var 0) _ hr (ckVarPos_stK hk)
  have hns : ∀ l, (valAt st.env (.bind 1 1)).sitesOf l (.bind 1 1) [] = [] := fun l => by
    rw [hvb]; simp [Value.sitesOf]
  have hacc : s.access (.bind 1 1) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
  have hposA : Pos.bind 1 1 ∈ allPos st.env := (lookup_pos hb).1
  have hσT : st.absTy[0]? = some .tNat := by rw [← hk.absTy]; rfl
  have hRσ : st.norm.Refd 0 := .val (.borrow 0 (.abs 0)) (by
    show _ ∈ Env.values st.env.erase
    rw [values_erase]; exact List.mem_map.mpr ⟨_, hposA, hvb⟩) (by
      simp only [Value.hasAbs, Value.anyAtom]
      first | rfl | simp [BEq.beq, Value.beq] | (unfold BEq.beq; simp [Value.beq]))
  obtain ⟨m, hmρ⟩ := asg_abs_nat hp.asg hRσ hσT
  have hval : s.valAt (.bind 1 1) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 (s.typedFuture φ) ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind 1 1) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind 1 1) = _
    simp only [Env.mean, hb, rB, Value.mean]; exact hmρ
  obtain ⟨-, htyS⟩ := rel_bind_ty hr hb (by rfl)
  have htyN : (s.tyAt (.bind 1 1)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hb, rB]; rfl
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hco : contentOf K φ (.var 0) s = some ((.el0 Nat m, s.tyAt (.bind 1 1), .bind 1 1, []), s) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow, hval]
  have hshC : Env.shape st.env (.bind 1 1) = some 0 := by rw [shape_eq_shapeOf, hvb]; rfl
  have hshq : s.shape (.bind 1 1) = some (π 0) := hr.sim.2.1 _ 0 (by simp [IsTemp]) hshC
  have hrg : ReadGood K.dm.read (s.tyAt (.bind 1 1)).m (.el0 Nat m) := .inl (by rw [htyN]; exact ⟨m, rfl⟩)
  have hset : setContent K φ (.bind 1 1) [] .moved s = some (⟨⟩, s.setAt (.bind 1 1) fun _ => .moved) := by
    simp [setContent, Attack.updAt_nil]
  have hst : readPlace K φ (.var 0) false s = some ((.el0 Nat m, { s.tyAt (.bind 1 1) with label := some (π 0) }),
      ((s.setAt (.bind 1 1) fun _ => .moved).takeLabel (π 0)).pushTempShaped (fun _ => .el0 Nat m) (π 0)) := by
    unfold readPlace
    rw [hco]
    simp only [bind, Option.bind, Sem.whole, hrg, not_true_eq_false, if_false, List.isEmpty_nil, if_true,
      Bool.false_eq_true]
    rw [hset, hshq]
  have hrun : runT K ρ φ st.tailNext (hintM K ρ hint) bodyK s = some ((.el0 Nat m, { s.tyAt (.bind 1 1) with label := some (π 0) }),
      ((s.setAt (.bind 1 1) fun _ => .moved).takeLabel (π 0)).pushTempShaped (fun _ => .el0 Nat m) (π 0)) := by
    have hcok : ContentOk K φ (.var 0) s := by
      unfold ContentOk; rw [hres]; exact accessOk_noSites (rel_noSites_at hr hns)
    have hfl' : K.D.flags (scopeOf s) (.place (.var 0)) = (false, false) := by rw [hsc]; exact hfl
    have hcp' : K.D.copy (K.D.placeDecl (scopeOf s) (.var 0)) = false := by rw [hsc]; exact hcp
    simp only [bodyK, runT, SM.erasedIf, hfl', hcp', Bool.false_eq_true, if_false, SM.stmtIf, SM.guarded_of hcok]
    exact hst
  -- the relation after: `rel_moveOut`, then the checker's end kernel
  have hlive0 : s.Live (π 0) := (SState.live_iff _ _).mpr ⟨_, hr.holders _ _ hshq, hshq⟩
  have hheld : s.heldTy (π 0) = (s.tyAt (.bind 1 1)).m := by
    rw [heldTy_eq_holderTy hS hlive0]
    have hh : s.holderOf (π 0) = some (.bind 1 1) := by
      obtain ⟨r, hr₀⟩ := SState.holderOf_of_live hlive0
      rw [hr₀, hS.uniq _ _ _ (SState.holderOf_spec hr₀).2 hshq]
    unfold holderTy; rw [hh]
  have hsz : st.env.size = 2 := by rw [← Env.erase_size, ← hk.env, Env.erase_size]; rfl
  have hrel₀ := rel_moveOut hr hS.uniq (by omega) hposA hvb (Value.NumA.abs 0).inertA hheld (.el0 Nat m)
    (fun _ _ => hmρ)
  have hrel : Rel K ρ φ π (st'.withTempT vK (some (.tRef .tNat)))
      (((s.setAt (.bind 1 1) fun _ => .moved).takeLabel (π 0)).pushTempShaped (fun _ => .el0 Nat m) (π 0)) :=
    Rel.of_kern ((kern_withTemp _ vK (some (.tRef .tNat))).trans (hkm.withTempT vK (some (.tRef .tNat)))) hrel₀
  -- `Pre` after
  have hNA : NumAt st (.abs 0) := ⟨.abs 0, fun σ' h' => by rw [abs_hasAbs_eq h']; exact hσT⟩
  have hinv : Inv K.D K.Γ (st'.withTempT vK (some (.tRef .tNat))).norm := by
    rw [← (hkm.withTempT vK (some (.tRef .tNat))).norm]
    exact hI K.D K.Γ st 1 1 0 (.abs 0) _ hvb hNA hp.inv
  have hasg : Asg K ρ (st'.withTempT vK (some (.tRef .tNat))).norm := by
    rw [← (hkm.withTempT vK (some (.tRef .tNat))).norm]
    refine hp.asg.of_refd rfl rfl rfl rfl rfl ?_
    refine refd_withTempT_to rfl (refd_setBot_norm hposA) (fun σ' h' => ?_)
    simp only [vK, Value.hasAbs, Value.anyAtom, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · simp [BEq.beq, Value.beq] at h'
    · rw [abs_hasAbs_eq (σ := 0) (σ' := σ') (by simpa [Value.hasAbs, Value.anyAtom] using h')]; exact hRσ
  refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk'.absTy, ← hk.absTy]; exact Nat.le_refl _,
      by rw [← hk'.nextLoan, ← hk.nextLoan]; exact Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩,
    hrun, hmρ, fun T e => ?_, rfl, ⟨hp.ctx.of_eq ?_ ?_, hinv, hasg⟩, hrel⟩
  · cases e; show (Value.tyS K.dm K.M K.Γ ρ (.tRef .tNat)).m = (s.tyAt (.bind 1 1)).m; rw [htyN]; rfl
  · show st'.inds = st.inds; rw [← hk'.inds, ← hk.inds]; rfl
  · show st'.globals = st.globals; rw [← hk'.globals, ← hk.globals]; rfl

end

end Ochr.Meaning.Steps.Form.ColumnW
