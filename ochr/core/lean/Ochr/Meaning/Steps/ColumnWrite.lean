import Ochr.Meaning.Steps.ColumnC

/-!
# The column: a write at a field of a place (lead7)

`x.0 := u` in a typed run of a top-level constant's body, where `x` is bound at `Nat` to a number
`S(w)` and `u`'s value is a number: the strict run's write at the field `0` (the predecessor),
under ruling (A)'s tests (the write's access ends nothing, `AssignOk`; the path update is defined at
every typed future, `setContent`; the state after holds open members everywhere, `lentOk`).

* `heldTy_eq_holderTy`: for a live label, its record's type is its holder's stored type, at every
  good state (`SGood.holderTy`). This is the fact docs/31 lists as what the relation lacks for the
  strict end tests (and for `DropOneAsm.dropOne_exists`, `MovedPlace.joinDropOne_noop`,
  `EqJAsm.J_step_asm`): it is not a clause of `Rel`, and it need not be, wherever the reference
  state is good, which in this form (`Steps/Form.lean`) every step assumes.
* `typedFut_rel`: so a typed future of a good state (each live label a whole member of its record's
  type) is one the relation compares at.
* `rel_setNum`: the write of a number over a number at a binding, on both sides, keeps the relation.
* `stateOk_setNum`: and leaves a state holding open members everywhere (the write test, `lentOk`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-! ## The record's type is the holder's, at a good state -/

/-- **For a live label, the record's type is its holder's stored type** at every good state. -/
theorem heldTy_eq_holderTy {dm : DataModel} {Γ : List IndDecl} {φ : Future} {s : SState}
    (hs : Strict.SGood dm Γ φ s) {l : Nat} (hl : s.Live l) : s.heldTy l = holderTy s l := by
  obtain ⟨r, hr⟩ := SState.holderOf_of_live hl
  have hsh := (SState.holderOf_spec hr).2
  unfold holderTy; rw [hr]
  cases r with
  | bind f i => exact (hs.holderTy f i l hsh).symm
  | temp f i => rfl

/-- **A typed future of a good state is one the relation compares at.** -/
theorem typedFut_rel {K : RunCtx} {φ : Future} {s : SState} (hs : Strict.SGood K.dm K.Γ φ s) {ψ : Future}
    (h : TypedFut K φ s ψ) : RelF φ s ψ ∧ TypedLive K s ψ :=
  ⟨h.1, fun l hl => ⟨Strict.mem_whole (DataModel.read_wholeFields K.dm) (h.2 l hl),
    by rw [← heldTy_eq_holderTy hs hl]; exact h.2 l hl⟩⟩

/-! ## A number written over a number at a binding -/

theorem sitesOf_setAtE_inert {env : Env} {pos : Pos} {v' : Value} (hp : pos ∈ allPos env)
    (hw : (valAt env pos).Inert) (hv' : v'.Inert) (l : Nat) :
    Env.sitesOf (Env.setAtE env pos v') l = Env.sitesOf env l := by
  unfold Env.sitesOf
  rw [allPos_setAtE]
  congr 1; funext q
  by_cases hq : q = pos
  · subst hq; rw [valAt_setAtE_self v' hp, hv'.sitesOf, hw.sitesOf]
  · rw [valAt_setAtE_other env pos q v' hq]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The write of a number over a number at a binding keeps the relation**: the checker's new
value and the reference's new meaning agree at every future the relation compares at; nothing else
changes (a number holds no borrow, is lent nothing, names no label). -/
theorem rel_setNum {π : Nat → Nat} {st : MState} {s : SState} {f i : Nat} {v' : Value} {g : SVal} {k : Nat}
    (hs : Rel K ρ φ π st s) (hp : Pos.bind f i ∈ allPos st.env) (hsp : Pos.bind f i ∈ s.positions)
    (hw : (valAt st.env (.bind f i)).Num) (hv' : v'.Num)
    (hk : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint v' = .el0 Nat k)
    (hg : ∀ ψ, RelF φ s ψ ∧ TypedLive K s ψ → g ψ = .el0 Nat k) :
    Rel K ρ φ π { st with env := Env.setAtE st.env (.bind f i) v' } (s.setAt (.bind f i) g) := by
  have hhold : ∀ l, v'.holdsBorrow l = (valAt st.env (Pos.bind f i)).holdsBorrow l := fun l => by
    rw [hv'.holdsBorrow, hw.holdsBorrow]
  have hlive : ∀ l, liveLoan (Env.setAtE st.env (Pos.bind f i) v') l = liveLoan st.env l := liveLoan_setAtE hp hhold
  have hshape : ∀ q, Env.shape (Env.setAtE st.env (Pos.bind f i) v') q = Env.shape st.env q := by
    intro q
    by_cases hq : q = Pos.bind f i
    · rw [hq, shape_eq_shapeOf, shape_eq_shapeOf, valAt_setAtE_self v' hp, hv'.inert.shape, hw.inert.shape]
    · exact shape_setAtE_other st.env (Pos.bind f i) q v' hq
  have hF : ∀ ψ, (RelF φ (s.setAt (Pos.bind f i) g) ψ ∧ TypedLive K (s.setAt (Pos.bind f i) g) ψ) →
      RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l hl => hψ.1 l (fun h => hl ((SState.live_setAt _ _ _ l).mp h)),
      fun l hl => by
        have := hψ.2 l ((SState.live_setAt _ _ _ l).mpr hl)
        rwa [holderTy_setAt] at this⟩
  have hp' : Pos.bind f i ∈ allPos (Env.setAtE st.env (Pos.bind f i) v') := by rw [allPos_setAtE]; exact hp
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun p q l hp hq => by
    rw [SState.shape_setAt'] at hp hq; exact hs.uniq p q l hp hq⟩
  · rw [skel_setAtE K ρ st f i v', hs.skel]
    exact (skel_setAt s _ _).symm
  · intro l hl ho
    rw [SState.nextLoan_setAt']
    refine hs.fresh l hl ?_
    obtain ⟨w, hw', ha⟩ := ho
    rcases mem_values_setAtE hw' with rfl | hw''
    · rw [hv'.inert.anyAtom _ (by rfl) (by rfl) (fun _ => by rfl)] at ha; cases ha
    · exact ⟨w, hw'', ha⟩
  · intro ψ hψ p hpt
    have hψ0 := hF ψ hψ
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) v') p = _
    by_cases hpp : p = Pos.bind f i
    · rw [hpp, valAt_setAt_self _ _ _ hsp, hg ψ hψ0, mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp',
        valAt_setAtE_self v' hp, hk]
    · rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) p v' _ hpp, SState.valAt_setAt_ne _ _ _ _ (Ne.symm hpp)]
      exact hs.sim.1 ψ hψ0 p hpt
  · intro p l hpt hsh
    have hsh' : Env.shape st.env p = some l := by rw [← hshape p]; exact hsh
    rw [SState.shape_setAt]
    exact hs.sim.2.1 p l hpt hsh'
  · intro p l' hpt hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨l, h1, h2⟩ := hs.sim.2.2.1 p l' hpt hsh
    exact ⟨l, by show Env.shape _ p = _; rw [hshape p]; exact h1, h2⟩
  · intro f' i' l hsh
    have hsh' : Env.shape st.env (.temp f' i') = some l := by rw [← hshape]; exact hsh
    obtain ⟨j, hj, hval⟩ := hs.sim.2.2.2.1 f' i' l hsh'
    refine ⟨j, by rw [SState.shape_setAt]; exact hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) v') (.temp f' i') = _
    rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) _ v' _ (by simp), SState.valAt_setAt_ne _ _ _ _ (by simp)]
    exact hval ψ (hF ψ hψ)
  · intro f' j l' hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨i', l, h1, h2⟩ := hs.sim.2.2.2.2 f' j l' hsh
    exact ⟨i', l, by show Env.shape _ _ = _; rw [hshape]; exact h1, h2⟩
  · intro l l' hl hl' he
    rw [hlive] at hl hl'
    exact hs.inj l l' hl hl' he
  · intro l hl x
    rw [hlive] at hl
    rw [SState.lent_setAt, hs.sites l hl x, sitesOf_setAtE_inert hp hw.inert hv'.inert l]
  · intro p l h
    rw [SState.shape_setAt'] at h
    rw [SState.positions_setAt]
    exact hs.holders p l h
  · intro l hl
    rw [holderTy_setAt]
    have hrec := hs.records l ((SState.live_setAt _ _ _ l).mp hl)
    rcases f with _ | f <;> exact hrec

/-- **The write test after a number is written at a binding of `Nat`**: every position holds an
open member of its type at every typed future (`lentOk`'s `StateOk`), from the state before being
good. -/
theorem stateOk_setNum {s : SState} {pos : Pos} {g : SVal} {k : Nat} (hs : Strict.SGood K.dm K.Γ φ s)
    (hsh : s.shape pos = none) (hty : (s.tyAt pos).m = TyM.nat)
    (hg : ∀ ψ, TypedFut K φ s ψ → g ψ = .el0 Nat k) : StateOk K φ (s.setAt pos g) := by
  intro ψ hψ
  have hψ' : TypedFut K φ s ψ :=
    ⟨fun l hl => hψ.1 l (by rwa [Strict.liveLabels_setAt]),
     fun l hl => by have := hψ.2 l (by rwa [Strict.liveLabels_setAt]); rwa [Strict.heldTy_setAt] at this⟩
  refine ⟨fun f i hpi => ?_, fun q l hq => ?_⟩
  · rw [SState.positions_setAt] at hpi
    rw [Steps.tyAt_setAt]
    by_cases hp : Pos.bind f i = pos
    · subst hp
      rw [valAt_setAt_self _ _ _ hpi, hg ψ hψ', hty]
      exact .inl (DataModel.pmem_of_mem K.dm K.Γ (by simp [Sem.whole]) ⟨k, rfl⟩)
    · rw [SState.valAt_setAt_ne _ _ _ _ (Ne.symm hp)]
      exact hs.bind ψ hψ' f i hpi
  · rw [SState.shape_setAt] at hq
    have hqp : q ≠ pos := fun e => by rw [e, hsh] at hq; cases hq
    rw [SState.valAt_setAt_ne _ _ _ _ (Ne.symm hqp), Strict.heldTy_setAt]
    exact hs.holder ψ hψ' q l hq

end

/-! ## The strict run's write at `x.0` -/

theorem resolve_setAt (s : SState) (p : Pos) (g : SVal) (q : Place) : resolve (s.setAt p g) q = resolve s q := by
  have e := skel_setAt s p g
  have hl : (s.setAt p g).env.length = s.env.length := by simpa using congrArg List.length e
  have hlast : ((s.setAt p g).env.getLast?).map (fun fr => fr.binds.length) =
      (s.env.getLast?).map (fun fr => fr.binds.length) := by
    have := congrArg (fun L => L.getLast?.map List.length) e
    simpa [List.getLast?_map, Function.comp_def] using this
  unfold resolve SState.varPos SState.topIdx
  rcases h1 : (s.setAt p g).env.getLast? with _ | fr1 <;> rcases h2 : s.env.getLast? with _ | fr2 <;>
    simp_all

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The assignment clause of the strict run, where the aligned table does not erase it. -/
theorem runT_assign (tl : Bool) (hint : TyS) (p : Place) (u : Term) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.assign p u) = (false, false)) :
    runT K ρ φ tl hint (.assign p u) s = (do
      let T : TyS := if u.assignHinted then (match contentOf K φ p s with
        | some ((_, T, _, _), _) => T
        | none => .plain .err) else .plain .err
      let ((v, R), s) ← runT K ρ φ false T u s
      if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
        match SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) s with
        | some (r, s₁) =>
          let s₂ := invalidate K φ p s₁
          if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
        | none => none
      else none) := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl]; rfl

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **A typed write at the field `0` of a variable bound at `Nat` to a number, at `evalCore`**
(`x.0 := u`, in a top-level constant's body), for a right-hand side whose value is a number and whose
run leaves Ω as it was. The strict run's tests all pass: the access ends nothing (`AssignOk`, nothing
is lent at a binding holding a number); the field update is defined at every typed future (there `x`
means its number, by the relation, at the futures it compares at, which every typed future of a good
state is: `typedFut_rel`); the state after holds open members everywhere (`stateOk_setNum`). -/
theorem assign_core (hA : AssignNumInv) (hI : InvSteps) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K)
    {n i : Nat} {u : Term}
    {P Pu : MState → Prop} (hu : EvalSim K ρ φ n u Pu) (hPu : ∀ a b, Kern a b → P a → Pu b)
    (hP : ∀ st, P st → NumVar i st)
    (hdx : ∀ st, P st → ∀ f j b, ckVarPos st.env i = some (.bind f j) →
      st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .other)
    (hflu : ∀ st, P st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hhint : ∀ (T : TyS) (s : SState), runT K ρ φ false T u s = runT K ρ φ false (.plain TyM.err) u s)
    (hnum : ∀ st₀ st₁ bh hint v₀ T₀, Pu st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u hint) st₀ bh (v₀, T₀) st₁ → v₀.Num ∧ Env.erase st₀.env = Env.erase st₁.env)
    (hinv : ∀ sc, K.D.invalidated sc (.proj 0 (.var i)) = []) :
    CoreSim K ρ φ (n + 1) (.assign (.proj 0 (.var i)) u) P (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd _ hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  have htyped : ∀ f j b, ckVarPos st.env i = some (.bind f j) →
      st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.ty = some .tNat := by
    obtain ⟨f0, j0, b0, hpos0, hb0, -, ht0⟩ := hP st hPst
    intro f j b hpos hb
    rw [hpos0, Option.some.injEq, Pos.bind.injEq] at hpos
    obtain ⟨rfl, rfl⟩ := hpos
    rw [hb0, Option.some.injEq] at hb
    subst hb; exact ht0
  obtain ⟨st₀, st₁, st₂, hu', v₀, T₀, bh₁, f, j, b, w, hk₀, hm₀, htn₀, htd₀, hru, hD₁, hq, hki, -, hpos₂, hlk₂, hbw, hk'i,
    rfl, rfl⟩ := hA n i u hint st st' bh v T? K.D hm htn htd htyped hD h
  have hPu₀ := hPu st st₀ hk₀ hPst
  obtain ⟨hv₀, he₀₁⟩ := hnum st₀ st₁ bh₁ hu' v₀ T₀ hPu₀ hm₀ htd₀ hD₁ hru
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hv
  -- the step for `u`
  have hOu := hu st₀ st₁ true hu' v₀ T₀ s π hPu₀ trivial hm₀ (.inl htd₀) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hvu
    (fun σ hσ => by rw [← hk₀.absTy]; exact hab σ (by simp [Term.anyAtom, hσ]))
    (by simpa [Term.hasHolePrim] using hnh)
    (by rw [scopeOf_rel hr]; exact hflu st hPst) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, -, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := by rw [← hhint]; exact hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  -- `u`'s value: a number, with no label
  obtain ⟨m, hmv⟩ := hv₀.vmean
  have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hrul : ru.2.label = none := by rw [hlu, num_heldLabel hv₀]; rfl
  -- after `u` and the quiet steps, `x` is as it was: `S(w)`, a number, at `Nat`
  have hr₂ : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ st₂ s₁ :=
    rel_of_withTempT_num hv₀ (hr₁.of_quiet (hq.withTempT v₀ T₀) hp₁.labels)
  obtain ⟨f', j', b', hpos', hlk', hnb', htb'⟩ := (hP st hPst).of_erase (hk₀.env.trans (he₀₁.trans hq.env))
  rw [hpos₂, Option.some.injEq, Pos.bind.injEq] at hpos'
  obtain ⟨rfl, rfl⟩ := hpos'
  rw [hlk₂, Option.some.injEq] at hlk'
  subst hlk'
  have hwn : w.Num := by rw [hbw] at hnb'; cases hnb' with | succ h => exact h
  obtain ⟨mw, hmw⟩ := hwn.vmean
  have hmx : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint b.val = .el0 Nat (mw + 1) := by
    intro dm C Γ ρ φ hint; rw [hbw, Value.mean, hmw, Sem.succ, Sem.asNat_el0]
  -- the reference's `x`: the same position, at `Nat`, holding no borrow, lent nothing, meaning `S(w)`
  have hvb₂ : valAt st₂.env (.bind f j) = b.val := by
    rw [valAt_bind_eq]; rcases hfr : st₂.env[f]? with _ | fr
    · rw [hfr] at hlk₂; cases hlk₂
    · rw [hfr] at hlk₂; simp only [Option.bind_some] at hlk₂; simp [hlk₂]
  have hposA : Pos.bind f j ∈ allPos st₂.env := by
    rcases hfr : st₂.env[f]? with _ | fr
    · rw [hfr] at hlk₂; cases hlk₂
    · rw [hfr] at hlk₂; exact bind_mem_allPos st₂.env f j fr b hfr hlk₂
  obtain ⟨hposS, htyS⟩ := rel_bind_ty hr₂ hlk₂
  have htyN : (s₁.tyAt (.bind f j)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hlk₂, htb']; rfl
  have hns : ∀ l, (valAt st₂.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
    rw [hvb₂]; exact hnb'.sitesOf l _ _
  have hk' := hk'i hns
  have hacc : ∀ hit, s₁.access (.bind f j) hit = s₁ := fun _ => access_noSites (rel_noSites_at hr₂ hns)
  have haok : ∀ hit, AccessOk K φ s₁ (.bind f j) hit := fun _ => accessOk_noSites (rel_noSites_at hr₂ hns)
  have hshS : s₁.shape (.bind f j) = none := by
    rcases e : s₁.shape (.bind f j) with _ | l'
    · rfl
    · obtain ⟨l, h1, -⟩ := hr₂.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
      have : Env.shape st₂.env (.bind f j) = some l := h1
      rw [shape_eq_shapeOf, hvb₂, hnb'.inert.shape] at this; cases this
  have hres : resolve s₁ (.proj 0 (.var i)) = some (.bind f j, [.proj 0]) :=
    rel_resolve_ck { K with Δ := Δ₁ } ρ₁ φ st₂ s₁ π₁ (.proj 0 (.var i)) _ hr₂ hpos₂
  have hx : ∀ ψ, RelF φ s₁ ψ ∧ TypedLive { K with Δ := Δ₁ } s₁ ψ → s₁.valAt (.bind f j) ψ = .el0 Nat (mw + 1) := by
    intro ψ hψ; rw [← hr₂.sim.1 ψ hψ (.bind f j) (by simp [IsTemp])]; exact mean_numVar hlk₂ hmx _
  -- the write: `x` means `S(u's value)` wherever the relation compares
  let g : SVal := fun φ' =>
    (Sem.updAt K.dm K.Γ (s₁.tyAt (.bind f j)) (fun _ => ru.1) [.proj 0] (s₁.valAt (.bind f j) φ')).getD .err
  have hupd : ∀ ψ, RelF φ s₁ ψ ∧ TypedLive { K with Δ := Δ₁ } s₁ ψ →
      Sem.updAt K.dm K.Γ (s₁.tyAt (.bind f j)) (fun _ => ru.1) [.proj 0] (s₁.valAt (.bind f j) ψ) =
        some (.el0 Nat (m + 1)) := by
    intro ψ hψ
    rw [hx ψ hψ, hru1, Sem.updAt.eq_def]
    simp only [Sem.asNat_el0]
    rw [Sem.updAt.eq_def]
    simp only [Option.map_some]
    rw [Sem.succ, Sem.asNat_el0]
  have hgv : ∀ ψ, RelF φ s₁ ψ ∧ TypedLive { K with Δ := Δ₁ } s₁ ψ → g ψ = .el0 Nat (m + 1) := fun ψ hψ => by
    show (Sem.updAt _ _ _ _ _ _).getD _ = _; rw [hupd ψ hψ]; rfl
  -- the reference's run of the write: every test passes
  have hco : contentOf K φ (.proj 0 (.var i)) s₁ =
      some ((.el0 Nat mw, { (TyS.plain TyM.nat) with label := none }, .bind f j, [.proj 0]), s₁) := by
    have hval : s₁.valAt (.bind f j) (s₁.typedFuture φ) = .el0 Nat (mw + 1) :=
      hx _ ⟨relF_typedFuture φ s₁, hr₂.typedFuture_typed φ⟩
    unfold contentOf; rw [hres]; simp only; rw [hacc]
    simp [Sem.follow, Sem.step, hval, Sem.asNat_el0]
  have hpt : placeTy K φ (.proj 0 (.var i)) s₁ = .plain TyM.nat := by
    unfold placeTy; rw [hco]; rfl
  have htest : ∀ ψ, TypedFut K φ s₁ ψ →
      (Sem.updAt K.dm K.Γ (s₁.tyAt (.bind f j)) (fun _ => ru.1) [.proj 0] (s₁.valAt (.bind f j) ψ)).isSome :=
    fun ψ hψ => by rw [hupd ψ (typedFut_rel hS₁ hψ)]; rfl
  have hAok : AssignOk K φ (.proj 0 (.var i)) s₁ := by
    unfold AssignOk; rw [hres]; exact ⟨fun _ => haok _, fun h => by cases h⟩
  have hsc : setContent K φ (.bind f j) [.proj 0] ru.1 s₁ = some (⟨⟩, s₁.setAt (.bind f j) g) := by
    unfold setContent; rw [if_pos htest]
  have hasg : assignAt K φ (.proj 0 (.var i)) ru.1 ru.2.label s₁ =
      some ((.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g) := by
    unfold assignAt; rw [hres]; simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
    rw [hacc, hsc, hrul]
  have hinvs : invalidate K φ (.proj 0 (.var i)) (s₁.setAt (.bind f j) g) = s₁.setAt (.bind f j) g := by
    unfold invalidate; rw [hinv]; rfl
  have hinvok : InvalidateOk K φ (.proj 0 (.var i)) (s₁.setAt (.bind f j) g) := by
    unfold InvalidateOk; rw [hinv]; trivial
  have hlent : lentOk K φ (.proj 0 (.var i)) (s₁.setAt (.bind f j) g) := by
    unfold lentOk; rw [resolve_setAt, hres]
    exact .inr (.inr (stateOk_setNum hS₁ hshS htyN (fun ψ hψ => hgv ψ (typedFut_rel hS₁ hψ))))
  have hxa : runT K ρ φ st.curTail (hintM K ρ hint) (.assign (.proj 0 (.var i)) u) s =
      some ((.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g) := by
    rw [runT_assign _ _ _ _ s hfl]
    simp only [hhint, hxu', bind, Option.bind]
    rw [hpt, if_pos ⟨by rw [hru1]; exact ⟨m, rfl⟩, fun l hl => by rw [hrul] at hl; cases hl⟩]
    unfold SM.guarded; rw [if_pos hAok, hasg]
    simp only [hinvs, if_pos (And.intro hinvok hlent)]
  -- the conclusion: `()` at `Unit`, the checker's state after related to the reference's
  have hmS : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint (.succ v₀) = .el0 Nat (m + 1) := by
    intro dm C Γ ρ φ hint; rw [Value.mean, hmv, Sem.succ, Sem.asNat_el0]
  have hX : Asg { K with Δ := Δ₁ } ρ₁ ({ st₂ with env := Env.setAtE st₂.env (.bind f j) (.succ v₀) } : MState).norm := by
    have hA₂ : Asg { K with Δ := Δ₁ } ρ₁ (st₂.withTempT v₀ T₀).norm :=
      Asg.of_quiet (hq.withTempT v₀ T₀) hp₁.asg hp₁.inv.wf6
    refine hA₂.of_refd rfl rfl rfl rfl rfl fun σ hσ => refd_mono_withTempT v₀ T₀ σ ?_
    refine refd_sub (st := st₂) (st' := { st₂ with env := Env.setAtE st₂.env (.bind f j) (.succ v₀) })
      rfl rfl rfl rfl ?_ ?_ ?_ σ hσ
    · intro w' hw' σ' hσ'
      rcases mem_values_setAtE hw' with rfl | hw''
      · rw [(Value.Num.succ hv₀).hasAbs] at hσ'; cases hσ'
      · exact ⟨w', hw'', hσ'⟩
    · intro f' i' b' T σ' hb' hT hσ'
      obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
      exact .ty f' i' b'' T (by rw [show st₂.norm.env = st₂.env.erase from rfl, lookup_erase]; exact hb'')
        (by rw [hty'']; exact hT) hσ'
    · intro f' i' b' P ws j' σ' hb' hl hσ'
      obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
      exact .lazyTy f' i' b'' P ws j' (by rw [show st₂.norm.env = st₂.env.erase from rfl, lookup_erase]; exact hb'')
        (by rw [hlz'']; exact hl) hσ'
  refine ⟨ρ₁, Δ₁, π₁, (.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g, ⟨?_, ?_, ?_, ?_⟩, hxa, rfl,
    fun T hT => by cases hT; rfl, rfl, ?_, ?_⟩
  · rw [hk₀.absTy, ← hk'.absTy]; exact Nat.le_trans he₁.abs hq.absSize
  · rw [hk₀.nextLoan, ← hk'.nextLoan]; exact Nat.le_trans he₁.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he₁.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he₁.ren l hl
  · refine ⟨hp₁.ctx.of_eq ?_ ?_, ?_, ?_⟩
    · show st'.inds = st₁.inds; rw [← hk'.inds, ← hq.inds]
    · show st'.globals = st₁.globals; rw [← hk'.globals, ← hq.globals]
    · have h₁ : Inv K.D K.Γ st₁.norm := hI.popInert K.D K.Γ st₁ v₀ T₀ (.inl hv₀) hp₁.inv
      have h₂ : Inv K.D K.Γ st'.norm := by
        rw [← hk'.norm]
        exact hI.setNum K.D K.Γ st₂ f j _ hPL
          (fun b' hb' => hdx st hPst f j b'
            (by rw [← ckVarPos_erase, hk₀.env.trans (he₀₁.trans hq.env), ckVarPos_erase]; exact hpos₂)
            (by rw [← lookup_erase, hk₀.env.trans (he₀₁.trans hq.env), lookup_erase]; exact hb'))
          (by rw [hvb₂]; exact hnb') (.succ hv₀) (hki K.D K.Γ h₁)
      exact hI.pushInert K.D K.Γ st' _ _ (.inr rfl) h₂
    · have : Asg { K with Δ := Δ₁ } ρ₁ st'.norm := by rw [← hk'.norm]; exact hX
      exact asg_withTempT_inert this Value.inert_unit _
  · have hR := rel_setNum hr₂ hposA hposS (by rw [hvb₂]; exact hnb') (Value.Num.succ hv₀) hmS hgv
    exact rel_withTempT_inert (hR.of_kern hk') Value.inert_unit _

end

end Ochr.Meaning.Steps.Form
