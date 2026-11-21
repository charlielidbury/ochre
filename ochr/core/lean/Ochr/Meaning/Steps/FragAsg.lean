import Ochr.Meaning.Steps.FragSeqB

/-!
# `x := u` in the fragment (lead12)

A write at a root number variable: `u`'s value, a number, overwrites `x`'s content, a number or `⊥`
(nothing ends), or `x` is lent and the write's access ends its borrow first (`FragEnd.rel_end`). The
reference's `assignAt` at a root: [Access] of `x`, the write. The tail shared by the three cases is
`write_out`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

theorem updAt_nil (dm : DataModel) (Γ : List IndDecl) (T : TyS) (f : Sem → Sem) (a : Sem) :
    Sem.updAt dm Γ T f [] a = some (f a) := by
  rw [Sem.updAt.eq_def]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **`assignAt` at a root holding no borrow**: the access, then the write. -/
theorem assignAt_root {s s₁ : SState} {i : Nat} {pos : Pos} (hres : resolve s (.var i) = some (pos, []))
    (hsh : s.shape pos = none) (hacc : s.access pos (dataHit []) = s₁) (hsh₁ : s₁.shape pos = none) (a : Sem) :
    assignAt K φ (.var i) a none s = some ((.el0 Unit (), .plain TyM.unit), s₁.setAt pos (fun _ => a)) := by
  unfold assignAt; rw [hres]
  simp only [List.isEmpty_nil, hsh, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, if_true]
  rw [hacc, hsh₁]
  simp only
  unfold setContent
  rw [if_pos (fun ψ _ => by rw [updAt_nil]; rfl)]
  simp only [updAt_nil, Option.getD_some]

/-- A root's type, read after its access. -/
theorem placeTy_root {s s₁ : SState} {i : Nat} {pos : Pos} (hres : resolve s (.var i) = some (pos, []))
    (hacc : s.access pos (dataHit []) = s₁) : placeTy K φ (.var i) s = .plain (s₁.tyAt pos).m := by
  unfold placeTy contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow]

/-- **The tail of `x := u`**, shared by the three cases: after `u`'s step (to `st₁`, related to `s₁`), a
quiet stretch (`st₂`) and the access of `x` (the checker's environment `E₂`, the reference's state
`s₁'`, related; `x` holding an inert value there), the write of `u`'s number at `x` on both sides. -/
theorem write_out (hI : InvSteps) (hInv : ∀ sc p, K.D.invalidated sc p = []) {st st₀ st₁ st₂ st' : MState}
    {E₂ : Env} {s s₁ s₁' : SState} {π π₁ : Nat → Nat} {ρ₁ : Assignment} {Δ₁ : Nat → TyS} {tl : Bool}
    {hint : Option Value} {i f j k : Nat} {u : Term} {ru : Res} {v₀ : Value} {T₀ : Option Value}
    (hhint : ∀ (T : TyS) (s : SState), runT K ρ φ false T u s = runT K ρ φ false (.plain TyM.err) u s)
    (hfl : K.D.flags (scopeOf s) (.assign (.var i) u) = (false, false))
    (hk₀ : Kern st st₀) (he₁ : Ext K ρ π st₀ st₁ ρ₁ Δ₁ π₁) (hq : Quiet st₁ st₂)
    (hp₁ : Pre { K with Δ := Δ₁ } ρ₁ (st₁.withTempT v₀ T₀))
    (hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁)) (hv₀ : v₀.Num)
    (hmv : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint v₀ = .el0 Nat k)
    (hru1 : ru.1 = .el0 Nat k) (hrul : ru.2.label = none)
    (hres₁ : resolve s₁ (.var i) = some (.bind f j, [])) (hshS : s₁.shape (.bind f j) = none)
    (hacc : s₁.access (.bind f j) (dataHit []) = s₁') (haok : AccessOk K φ s₁ (.bind f j) (dataHit []))
    (hsh₁' : s₁'.shape (.bind f j) = none) (htyN : (s₁'.tyAt (.bind f j)).m = TyM.nat)
    (hrE : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ ({ st₂ with env := E₂ } : MState) s₁')
    (hx : Pos.bind f j ∈ allPos E₂) (hxs : Pos.bind f j ∈ s₁'.positions) (hw : (valAt E₂ (.bind f j)).Inert)
    (hinvE : Inv K.D K.Γ ({ st₂ with env := Env.setAtE E₂ (.bind f j) v₀ } : MState).norm)
    (haE : Asg { K with Δ := Δ₁ } ρ₁ ({ st₂ with env := E₂ } : MState).norm)
    (hk : Kern { st₂ with env := Env.setAtE E₂ (.bind f j) v₀ } st') :
    Out K ρ φ π st st' s (runT K ρ φ tl (hintM K ρ hint) (.assign (.var i) u)) .unit (some .tUnit) := by
  have hpt : placeTy K φ (.var i) s₁ = .plain (s₁'.tyAt (.bind f j)).m := placeTy_root hres₁ hacc
  have hAok : AssignOk K φ (.var i) s₁ := by
    unfold AssignOk; rw [hres₁]
    refine ⟨fun _ => haok, fun _ l hl => ?_⟩
    simp only [List.isEmpty_nil, hshS, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, hacc,
      hsh₁'] at hl
    cases hl
  have hasg : assignAt K φ (.var i) ru.1 ru.2.label s₁ =
      some ((.el0 Unit (), .plain TyM.unit), s₁'.setAt (.bind f j) (fun _ => ru.1)) := by
    rw [hrul]; exact assignAt_root hres₁ hshS hacc hsh₁' _
  have hinvs : invalidate K φ (.var i) (s₁'.setAt (.bind f j) (fun _ => ru.1)) = s₁'.setAt (.bind f j) (fun _ => ru.1) := by
    unfold invalidate; rw [hInv]; rfl
  have hinvok : InvalidateOk K φ (.var i) (s₁'.setAt (.bind f j) (fun _ => ru.1)) := by
    unfold InvalidateOk; rw [hInv]; trivial
  have hxa : runT K ρ φ tl (hintM K ρ hint) (.assign (.var i) u) s =
      some ((.el0 Unit (), .plain TyM.unit), s₁'.setAt (.bind f j) (fun _ => ru.1)) := by
    rw [runT_assign _ _ _ _ s hfl]
    simp only [hhint, hxu', bind, Option.bind]
    rw [hpt, if_pos ⟨by rw [hru1, htyN]; exact ⟨k, rfl⟩, fun l hl => by rw [hrul] at hl; cases hl⟩]
    unfold SM.guarded; rw [if_pos hAok, hasg]
    simp only [hinvs, if_pos (And.intro hinvok (lentOk_var i _))]
  refine ⟨ρ₁, Δ₁, π₁, (.el0 Unit (), .plain TyM.unit), s₁'.setAt (.bind f j) (fun _ => ru.1), ⟨?_, ?_, ?_, ?_⟩, hxa,
    rfl, fun T hT => by cases hT; rfl, rfl, ?_, ?_⟩
  · rw [hk₀.absTy, ← hk.absTy]; exact Nat.le_trans he₁.abs hq.absSize
  · rw [hk₀.nextLoan, ← hk.nextLoan]; exact Nat.le_trans he₁.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he₁.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he₁.ren l hl
  · refine ⟨hp₁.ctx.of_eq ?_ ?_, ?_, ?_⟩
    · show st'.inds = st₁.inds; rw [← hk.inds, ← hq.inds]
    · show st'.globals = st₁.globals; rw [← hk.globals, ← hq.globals]
    · exact hI.pushInert K.D K.Γ st' _ _ (.inr rfl) (by rw [← hk.norm]; exact hinvE)
    · have : Asg { K with Δ := Δ₁ } ρ₁ st'.norm := by
        rw [← hk.norm]; exact asg_setAtE_noAbs (st := ({ st₂ with env := E₂ } : MState)) hv₀.hasAbs haE
      exact asg_withTempT_inert this Value.inert_unit _
  · have hR := rel_setNum hrE hx hxs hw hv₀ hmv (fun ψ _ => by show ru.1 = _; rw [hru1])
    exact rel_withTempT_inert (hR.of_kern hk) Value.inert_unit _

/-- **`x := u` of the fragment, at `evalCore`** (`x` a number variable of the top frame, `u : Nat`):
the step for `u`; then, at `u`'s end, `x` holds a number or `⊥` (nothing ends: the write) or is lent
(the write's access ends its borrow, `rel_end`, `lent_access`, then the write); `write_out`. Assumes
`AssignVarInv`, `FragRun`, `FragDec`, `InvSteps`, `InvEnd`, `InvSetBotNum`, `PlaceLocal` and an
empty invalidation. -/
theorem asgF_core (hAV : AssignVarInv) (hR : FragRun K.D) (hdec : FragDec K.D) (hI : InvSteps) (hIE : InvEnd)
    (hISB : InvSetBotNum) (hPL : PlaceLocal K.D) (hInv : ∀ sc p, K.D.invalidated sc p = []) (hc : Strict.FundCtx K)
    {Γ : List FT} {i : Nat} {u : Term} (hi : Γ[i]? = some .nat) (hu : FTy Γ u .nat) {m : Nat}
    (ihu : EvalSim K ρ φ m u (FSt Γ) (· = true)) :
    CoreSim K ρ φ (m + 1) (.assign (.var i) u) (FSt Γ) (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨st₀, st₁, hu', v₀, T₀, bh₁, hk₀, hm₀, htn₀, htd₀, hru, hD₁, rfl, rfl, hpost⟩ :=
    hAV m i u hint st st' bh v T? K.D hm htn htd (fun f j b hpos hb => (hPst.natVar hi hpos b hb).1) hD h
  have hP₀ : FSt Γ st₀ := hPst.kern hk₀
  obtain ⟨rfl, hv₀, -, -, -, hF₁⟩ := hR Γ u .nat m hu' st₀ st₁ bh₁ v₀ T₀ hu hP₀ hm₀ (.inl htd₀) hD₁ hru
  -- the step for `u`
  have hOu := ihu st₀ st₁ true hu' v₀ (some FT.nat.ty) s π hP₀ rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS (hu.valsOk _) (fun σ hσ => hu.absBelow _ σ hσ) hu.noHole
    (by rw [scopeOf_rel hr]; exact (hdec Γ u .nat st hu hPst).1) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, -, hlu, hp₁, hr₁⟩ := hOu
  have hhint : ∀ (T : TyS) (s : SState), runT K ρ φ false T u s = runT K ρ φ false (.plain TyM.err) u s :=
    fun T s => frag_hint hu false T _ s
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := by rw [← hhint]; exact hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u (hu.valsOk _) false (.plain TyM.err) s s₁ ru hS hxu'
  obtain ⟨k, hmv⟩ := hv₀.vmean
  have hru1 : ru.1 = .el0 Nat k := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hrul : ru.2.label = none := by rw [hlu, num_heldLabel hv₀]; rfl
  -- after `u` and the quiet stretch: a fragment state, `x` there
  have hP₁ : FSt Γ st₁ := hF₁.untemp (.inl hv₀)
  have hinv₁ : Inv K.D K.Γ st₁.norm := hI.popInert K.D K.Γ st₁ v₀ _ (.inl hv₀) hp₁.inv
  obtain ⟨f, j, b, hpos₁, hb₁, hty₁, hrd₁, hhold₁⟩ := hP₁.top i .nat hi
  obtain ⟨st₂, hq, hki, -, hkNB, hkL⟩ := hpost f j b hpos₁ hb₁ hv₀
  replace hki := hki (fun T e => by cases e; rfl)
  have hinv₂ : Inv K.D K.Γ st₂.norm := hki K.D K.Γ hinv₁
  have hr₂ : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ st₂ s₁ :=
    rel_of_withTempT_num hv₀ (hr₁.of_quiet (hq.withTempT v₀ _) hp₁.labels)
  have ha₂ : Asg { K with Δ := Δ₁ } ρ₁ st₂.norm :=
    asg_of_withTempT (Asg.of_quiet (hq.withTempT v₀ _) hp₁.asg hp₁.inv.wf6)
  have hP₂ : FSt Γ st₂ := hP₁.of_erase hq.env
  have hpos₂ : ckVarPos st₂.env i = some (.bind f j) := by rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hpos₁
  have hb₂ : st₂.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
    rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb₁
  obtain ⟨hx₂, hxv₂⟩ := lookup_pos hb₂
  have hres₁ : resolve s₁ (.var i) = some (.bind f j, []) :=
    rel_resolve_ck { K with Δ := Δ₁ } ρ₁ φ st₂ s₁ π₁ (.var i) _ hr₂ hpos₂
  obtain ⟨hxs, htyS⟩ := rel_bind_ty hr₂ hb₂
  have htyN : (s₁.tyAt (.bind f j)).m = TyM.nat := by rw [htyS]; simp only [Env.hintAt, hb₂, hty₁]; rfl
  have hshS : s₁.shape (.bind f j) = none := by
    rcases e : s₁.shape (.bind f j) with _ | l'
    · rfl
    · obtain ⟨l, h1, -⟩ := hr₂.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
      have : Env.shape st₂.env (.bind f j) = some l := h1
      rw [shape_eq_shapeOf, hxv₂] at this
      rcases hhold₁ with hn | hb | ⟨l₀, hl₀⟩
      · rw [hn.inert.shape] at this; cases this
      · rw [hb] at this; cases this
      · rw [hl₀] at this; cases this
  rcases hhold₁ with hn | hbot | ⟨l, hl⟩
  · -- `x` holds a number: nothing ends
    have hns : ∀ l, (valAt st₂.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
      rw [hxv₂]; exact hn.sitesOf l _ _
    exact write_out (E₂ := st₂.env) hI hInv hhint hfl hk₀ he₁ hq hp₁ hxu' hv₀ hmv hru1 hrul hres₁ hshS
      (access_noSites (rel_noSites_at hr₂ hns)) (accessOk_noSites (rel_noSites_at hr₂ hns)) hshS htyN hr₂ hx₂ hxs
      (by rw [hxv₂]; exact hn.inert)
      (hI.setNum K.D K.Γ st₂ f j v₀ hPL (fun b' hb' => by rw [hb₂] at hb'; cases hb'; exact hrd₁)
        (by rw [hxv₂]; exact hn) hv₀ hinv₂) ha₂ (hkNB (.inl hn))
  · -- `x` was moved: `⊥` overwritten
    have hns : ∀ l, (valAt st₂.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
      rw [hxv₂, hbot]; simp [Value.sitesOf]
    exact write_out (E₂ := st₂.env) hI hInv hhint hfl hk₀ he₁ hq hp₁ hxu' hv₀ hmv hru1 hrul hres₁ hshS
      (access_noSites (rel_noSites_at hr₂ hns)) (accessOk_noSites (rel_noSites_at hr₂ hns)) hshS htyN hr₂ hx₂ hxs
      (by rw [hxv₂, hbot]; exact Value.inert_bot)
      (hISB K.D K.Γ st₂ f j v₀ hPL (fun b' hb' => by rw [hb₂] at hb'; cases hb'; exact ⟨hrd₁, hty₁⟩)
        (by rw [hxv₂, hbot]) hv₀ hinv₂) ha₂ (hkNB (.inr hbot))
  · -- `x` lent: the write's access ends its borrow first
    obtain ⟨f', j', c, he⟩ := hP₂.fend hx₂ (by rw [hxv₂, hl])
    obtain ⟨r, cM, hhold, hrs, hrph, -, -, -, -⟩ := end_holder hr₂ hS₁ he
    have hrr : r = .bind f' j' := hrph f' j' rfl
    obtain ⟨r₂, hhold₂, hrE⟩ := rel_end hr₂ hS₁ he hP₂.loansLive
    have hr₂' : r = r₂ := by rw [hhold] at hhold₂; exact Option.some.inj hhold₂
    subst hr₂'
    have hend := end_ok hr₂ hS₁ he
    obtain ⟨hacc, haok⟩ := lent_access hr₂ hS₁ he hrs hrr
    have hinvE := hIE K.D K.Γ st₂ _ _ l c hPL he
      (fun f₀ j₀ e b₀ hb₀ => by cases e; rw [hb₂] at hb₀; cases hb₀; exact hrd₁) hinv₂
    have hxE : Pos.bind f j ∈ allPos (endE st₂.env (.bind f j) (.bind f' j') c) := by rw [FEnd.allPos_endE]; exact hx₂
    have hxvE : valAt (endE st₂.env (.bind f j) (.bind f' j') c) (.bind f j) = c := by rw [he.valAt_endE, if_pos rfl]
    have hdE : ∀ b', (endE st₂.env (.bind f j) (.bind f' j') c)[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b' → b'.decl = .other := fun b' hb' => by
      obtain ⟨b₃, hb₃, -, hd₃⟩ := lookup_setAtE_decl hb'
      obtain ⟨b₄, hb₄, -, hd₄⟩ := lookup_setAtE_decl hb₃
      rw [hb₂] at hb₄; cases hb₄; rw [← hd₃, ← hd₄]; exact hrd₁
    have hshE : (s₁.endAt (π₁ l) r).shape (.bind f j) = none := by
      rw [SState.endAt_shape]; simp only
      rw [if_neg (fun e => he.ne (by rw [← hrr, ← e]))]; exact hshS
    have hinvW : Inv K.D K.Γ ({ st₂ with env := Env.setAtE (endE st₂.env (.bind f j) (.bind f' j') c) (.bind f j) v₀ } : MState).norm :=
      hI.setNum K.D K.Γ ({ st₂ with env := (endE st₂.env (.bind f j) (.bind f' j') c) } : MState) f j v₀ hPL hdE (by rw [hxvE]; exact he.c) hv₀ hinvE
    have haE : Asg { K with Δ := Δ₁ } ρ₁ ({ st₂ with env := (endE st₂.env (.bind f j) (.bind f' j') c) } : MState).norm := asg_endE he.c ha₂
    have hkW : Kern ({ st₂ with env := Env.setAtE (endE st₂.env (.bind f j) (.bind f' j') c) (.bind f j) v₀ } : MState) st' :=
      hkL f' j' l c (he.of_erase hq.env.symm)
    have htyE : ((s₁.endAt (π₁ l) r).tyAt (.bind f j)).m = TyM.nat := by rw [endAt_tyAt']; exact htyN
    have hxsE : Pos.bind f j ∈ (s₁.endAt (π₁ l) r).positions := by rw [SState.endAt_positions]; exact hxs
    have hwE : (valAt (endE st₂.env (.bind f j) (.bind f' j') c) (.bind f j)).Inert := by rw [hxvE]; exact he.c.inert
    exact write_out (E₂ := (endE st₂.env (.bind f j) (.bind f' j') c)) hI hInv hhint hfl hk₀ he₁ hq hp₁ hxu' hv₀ hmv hru1 hrul hres₁ hshS hacc (haok hend)
      hshE htyE hrE hxE hxsE hwE hinvW haE hkW

end

end Ochr.Meaning.Steps.Form
