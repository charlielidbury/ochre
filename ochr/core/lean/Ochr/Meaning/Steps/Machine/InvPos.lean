import Ochr.Meaning.Steps.Machine.InvEnv
import Ochr.Meaning.SitesFollow
import Ochr.StabilityFootprint

/-!
# `Inv` across a change that keeps the positions up to simple values (machine lane)

`PosRel a b τ`: every position of `b` holds a bland value, or the value at `τ p` in `a` up to bland
values and the content of a borrow of a number; every position of `a` holds a bland value or is
reached; `τ` is the identity at every position whose value can hold a site (it moves only a borrow of
a number: `let y = &x`'s push). Then the clauses of `Inv` that read positions (WF1's holders, WF2,
WF12, WF14, (L)) carry over (`inv_of_posRel`): the live loans, the sites and the holders are `a`'s.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

structure PosRel (a b : Env) (τ : Pos → Pos) : Prop where
  fwd : ∀ p ∈ allPos b, (valAt b p).Bland ∨
    (τ p ∈ allPos a ∧ VEq (valAt a (τ p)) (valAt b p) ∧ (τ p = p ∨ (valAt b p).NumBorrow))
  bwd : ∀ q ∈ allPos a, (valAt a q).Bland ∨ ∃ p ∈ allPos b, τ p = q ∧ VEq (valAt a q) (valAt b p)
  inj : ∀ p ∈ allPos b, ∀ p' ∈ allPos b, τ p = τ p' → p = p'

theorem VEq.holdsBorrow {u v : Value} (h : VEq u v) (l : Nat) : u.holdsBorrow l = v.holdsBorrow l := by
  rcases h with rfl | ⟨hu, hv⟩ | ⟨m, w, w', rfl, rfl, hw, hw'⟩
  · rfl
  · rw [hu.holdsBorrow, hv.holdsBorrow]
  · simp [Value.holdsBorrow, hw.holdsBorrow, hw'.holdsBorrow]

theorem VEq.shapeOf {u v : Value} (h : VEq u v) : shapeOf u = shapeOf v := by
  rcases h with rfl | ⟨hu, hv⟩ | ⟨m, w, w', rfl, rfl, -, -⟩
  · rfl
  · rw [hu.shapeOf, hv.shapeOf]
  · rfl

/-- A value with a site is neither bland nor a borrow of a number. -/
theorem not_siteless {v : Value} {l : Nat} {pos : Pos} {x : Site} (hx : x ∈ v.sitesOf l pos []) :
    ¬ v.Bland ∧ ¬ v.NumBorrow :=
  ⟨fun h => (by rw [h.sitesOf] at hx; cases hx), fun h => (by rw [h.sitesOf] at hx; cases hx)⟩

theorem liveLoan_iff {env : Env} {l : Nat} :
    liveLoan env l = true ↔ ∃ p ∈ allPos env, (valAt env p).holdsBorrow l = true := by
  simp [liveLoan, findBorrow, List.find?_isSome]

section
variable {a b : Env} {τ : Pos → Pos} (hr : PosRel a b τ)
include hr

theorem PosRel.live (l : Nat) : liveLoan b l = liveLoan a l := by
  apply Bool.eq_iff_iff.mpr
  rw [liveLoan_iff, liveLoan_iff]
  constructor
  · rintro ⟨p, hp, h⟩
    rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
    · rw [hb.holdsBorrow] at h; cases h
    · exact ⟨τ p, hq, by rw [he.holdsBorrow]; exact h⟩
  · rintro ⟨q, hq, h⟩
    rcases hr.bwd q hq with hb | ⟨p, hp, -, he⟩
    · rw [hb.holdsBorrow] at h; cases h
    · exact ⟨p, hp, by rw [← he.holdsBorrow]; exact h⟩

theorem PosRel.sites (l : Nat) (x : Site) : x ∈ Env.sitesOf b l ↔ x ∈ Env.sitesOf a l := by
  constructor
  · intro h
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp h
    rcases hr.fwd p hp with hb | ⟨hq, he, ht | hn⟩
    · exact absurd hb (not_siteless hx).1
    · rcases he with e | ⟨-, hv⟩ | ⟨m, w, w', -, e, -, hw'⟩
      · rw [ht] at e; rw [← e] at hx; rw [ht] at hq; exact mem_env_sitesOf hq hx
      · exact absurd hv (not_siteless hx).1
      · exact absurd ⟨m, w', e, hw'⟩ (not_siteless hx).2
    · exact absurd hn (not_siteless hx).2
  · intro h
    obtain ⟨q, hq, hx⟩ := List.mem_flatMap.mp h
    rcases hr.bwd q hq with hb | ⟨p, hp, hτ, he⟩
    · exact absurd hb (not_siteless hx).1
    · rcases hr.fwd p hp with hb | ⟨-, -, ht | hn⟩
      · rcases he with e | ⟨hu, -⟩ | ⟨m, w, w', e, -, hw, -⟩
        · rw [e] at hx; exact absurd hb (not_siteless hx).1
        · exact absurd hu (not_siteless hx).1
        · exact absurd ⟨m, w, e, hw⟩ (not_siteless hx).2
      · rw [ht] at hτ; subst hτ
        rcases he with e | ⟨hu, -⟩ | ⟨m, w, w', e, -, hw, -⟩
        · rw [e] at hx; exact mem_env_sitesOf hp hx
        · exact absurd hu (not_siteless hx).1
        · exact absurd ⟨m, w, e, hw⟩ (not_siteless hx).2
      · rcases he with e | ⟨hu, -⟩ | ⟨m, w, w', e, -, hw, -⟩
        · rw [e] at hx; exact absurd hn (not_siteless hx).2
        · exact absurd hu (not_siteless hx).1
        · exact absurd ⟨m, w, e, hw⟩ (not_siteless hx).2

end

theorem VEq.outerLoans {u v : Value} (h : VEq u v) : u.outerLoans = v.outerLoans := by
  rcases h with rfl | ⟨hu, hv⟩ | ⟨m, w, w', rfl, rfl, hw, hw'⟩
  · rfl
  · rw [hu.outerLoans, hv.outerLoans]
  · simp [Value.outerLoans, hw.outerLoans, hw'.outerLoans]

theorem VEq.loans {u v : Value} (h : VEq u v) : u.loans = v.loans := by
  rcases h with rfl | ⟨hu, hv⟩ | ⟨m, w, w', rfl, rfl, hw, hw'⟩
  · rfl
  · rw [hu.loans, hv.loans]
  · simp [Value.loans, hw.loans, hw'.loans]

/-- A sum over a list is at most one over another when every nonzero term is matched, injectively,
by an equal term. -/
theorem sum_le_of_inj {α : Type _} [BEq α] [LawfulBEq α] (τ : α → α) (g₁ g₂ : α → Nat) :
    ∀ (L₁ L₂ : List α), L₁.Nodup → (∀ p ∈ L₁, g₁ p ≠ 0 → τ p ∈ L₂ ∧ g₁ p = g₂ (τ p)) →
    (∀ p ∈ L₁, ∀ p' ∈ L₁, τ p = τ p' → p = p') → (L₁.map g₁).sum ≤ (L₂.map g₂).sum
  | [], _, _, _, _ => by simp
  | p :: L₁, L₂, hn, h, hi => by
    simp only [List.map_cons, List.sum_cons]
    have hn' := List.nodup_cons.mp hn
    have hi' : ∀ q ∈ L₁, ∀ q' ∈ L₁, τ q = τ q' → q = q' :=
      fun q hq q' hq' => hi q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')
    by_cases h0 : g₁ p = 0
    · rw [h0, Nat.zero_add]
      exact sum_le_of_inj τ g₁ g₂ L₁ L₂ hn'.2 (fun q hq => h q (List.mem_cons_of_mem _ hq)) hi'
    · obtain ⟨hm, he⟩ := h p (List.mem_cons_self ..) h0
      rw [((List.perm_cons_erase hm).map g₂).sum_nat, List.map_cons, List.sum_cons, he]
      apply Nat.add_le_add_left
      refine sum_le_of_inj τ g₁ g₂ L₁ _ hn'.2 (fun q hq hq0 => ?_) hi'
      obtain ⟨hm', he'⟩ := h q (List.mem_cons_of_mem _ hq) hq0
      refine ⟨(List.mem_erase_of_ne fun e => ?_).mpr hm', he'⟩
      have := hi q (List.mem_cons_of_mem _ hq) p (List.mem_cons_self ..) e
      subst this; exact hn'.1 hq

/-- The label test of `MState.Occurs` at a borrow of a number reads only its label. -/
theorem occ_numBorrow {m l : Nat} {w : Value} (hw : w.Num) :
    (Value.borrow m w).anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) =
      (m == l) := by
  simp only [Value.anyAtom]
  rw [hw.anyAtom (P := fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) rfl (fun _ => rfl)]
  show (false || (m == l) || false) = (m == l)
  cases (m == l) <;> rfl

section
variable {a b : Env} {τ : Pos → Pos} (hr : PosRel a b τ)
include hr

theorem PosRel.values : ∀ v ∈ Env.values b, v ∈ Env.values a ∨ v.Simple := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
  rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
  · exact .inr hb.simple
  · rcases he with e | ⟨-, hb⟩ | ⟨m, w, w', -, e, -, hw'⟩
    · exact .inl (mem_values_iff.mpr ⟨τ p, hq, e⟩)
    · exact .inr hb.simple
    · exact .inr (Value.NumBorrow.simple ⟨m, w', e, hw'⟩)

theorem PosRel.shape (hu : ∀ p ∈ allPos a, ∀ q ∈ allPos a, ∀ l, Env.shape a p = some l → Env.shape a q = some l → p = q) :
    ∀ p ∈ allPos b, ∀ q ∈ allPos b, ∀ l, Env.shape b p = some l → Env.shape b q = some l → p = q := by
  have key : ∀ p ∈ allPos b, ∀ l, Env.shape b p = some l → τ p ∈ allPos a ∧ Env.shape a (τ p) = some l := by
    intro p hp l h
    rw [shape_eq_shapeOf] at h ⊢
    rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
    · rw [hb.shapeOf] at h; cases h
    · exact ⟨hq, by rw [he.shapeOf]; exact h⟩
  intro p hp q hq l h h'
  obtain ⟨hp', e⟩ := key p hp l h
  obtain ⟨hq', e'⟩ := key q hq l h'
  exact hr.inj p hp q hq (hu _ hp' _ hq' l e e')

theorem PosRel.wf2 (h2 : WF2 a) : WF2 b := by
  refine ⟨fun v hv l hl => ?_, fun l => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
    · rw [hb.outerLoans] at hl; cases hl
    · rw [← he.outerLoans] at hl
      rw [hr.live]; exact h2.1 _ (mem_values_iff.mpr ⟨τ p, hq, rfl⟩) l hl
  · refine Nat.le_trans ?_ (h2.2 l)
    simp only [Env.values, List.flatMap_map, List.count_flatMap]
    refine sum_le_of_inj τ _ _ _ _ (allPos_nodup b) (fun p hp h0 => ?_) hr.inj
    rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
    · simp [hb.outerLoans] at h0
    · exact ⟨hq, by simp [Function.comp, he.outerLoans]⟩

theorem PosRel.loansLive (hL : ∀ v ∈ Env.values a, ∀ l ∈ v.loans, liveLoan a l = true) :
    ∀ v ∈ Env.values b, ∀ l ∈ v.loans, liveLoan b l = true := by
  intro v hv l hl
  obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
  rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
  · rw [hb.loans] at hl; cases hl
  · rw [← he.loans] at hl
    rw [hr.live]; exact hL _ (mem_values_iff.mpr ⟨τ p, hq, rfl⟩) l hl

theorem PosRel.wf12 (h : WF12 a) : WF12 b := by
  intro k l hk hl x hx hf y hy hpos hpre
  rw [hr.live] at hk hl
  rw [hr.sites] at hx hy
  obtain ⟨z, hz, h1, h2, h3⟩ := h k l hk hl x hx hf y hy hpos hpre
  exact ⟨z, (hr.sites l z).mpr hz, h1, h2, h3⟩

theorem PosRel.wf14 (h : WF14 a) : WF14 b := by
  intro pos path hf l hl x hx hpos k hk
  have hxv := mem_sitesOf_at hx hpos
  have hp : pos ∈ allPos b := by
    obtain ⟨p, hp, hx'⟩ := List.mem_flatMap.mp hx
    have := (sitesOf_prefix l p [] (valAt b p) x hx').1
    rw [← hpos, this]; exact hp
  rcases hr.fwd pos hp with hb | ⟨-, he, ht | hn⟩
  · exact absurd hb (not_siteless hxv).1
  · rcases he with e | ⟨-, hv⟩ | ⟨m, w, w', -, e, -, hw'⟩
    · rw [ht] at e
      rw [← e] at hf
      rw [hr.live] at hl
      exact h pos path hf l hl x ((hr.sites l x).mp hx) hpos k hk
    · exact absurd hv (not_siteless hxv).1
    · exact absurd ⟨m, w', e, hw'⟩ (not_siteless hxv).2
  · exact absurd hn (not_siteless hxv).2

theorem PosRel.occurs (l : Nat) (h : ∃ v ∈ Env.values b,
    v.anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) = true) :
    ∃ v ∈ Env.values a,
    v.anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) = true := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
  rcases hr.fwd p hp with hb | ⟨hq, he, -⟩
  · rw [hb.anyAtom rfl (fun _ => rfl) rfl rfl] at h; cases h
  · refine ⟨_, mem_values_iff.mpr ⟨τ p, hq, rfl⟩, ?_⟩
    rcases he with e | ⟨-, hv⟩ | ⟨m, w, w', e, e', hw, hw'⟩
    · rw [e]; exact h
    · rw [hv.anyAtom rfl (fun _ => rfl) rfl rfl] at h; cases h
    · rw [e]; rw [e', occ_numBorrow hw'] at h; rw [occ_numBorrow hw]; exact h

end

/-- **`Inv` across a change that keeps the positions up to simple values**: the tables kept, the
bindings' types old or clean, the readings' two clauses given. -/
theorem inv_of_posRel {D : Decisions} {Γ : List IndDecl} {a b : MState} {τ : Pos → Pos} (hi : Inv D Γ a)
    (hr : PosRel a.env b.env τ) (ht : TabSame a b) (hb : BindsFrom a b)
    (hfits : ∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true)
    (hpc : ∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) (hK : KindFrom a b) : Inv D Γ b := by
  have hi' := hi
  obtain ⟨⟨-, w1b⟩, w2, -, -, -, -, -, -, w12, w14, -, -, sf, -⟩ := hi'
  exact inv_step hi ht hr.values (fun l h => .inl (hr.occurs l h)) hb (hr.shape w1b) (hr.wf2 w2) (hr.wf12 w12)
    (hr.wf14 w14) (hr.loansLive sf.loans) hfits hpc hK

/-- The readings' two clauses where the readings are kept and every changed content fits what its
place is read as and is no proof. -/
theorem readClauses_of {D : Decisions} {Γ : List IndDecl} {a b : MState} (hi : Inv D Γ a)
    (hR : topReadings b = topReadings a)
    (hc : ∀ p v, ckContent b.env p = some v → ckContent a.env p = some v ∨ (v ≠ .proof ∧
      ∀ n args, D.placeDecl (topReadings a) p = .ind n args → (Γ.find? (·.name == n)).isSome → v.fitsInd n = true)) :
    (∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true) ∧
    (∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, sf, -⟩ := hi
  rw [hR]
  refine ⟨fun p v n args h hd hn => ?_, fun p hg h => ?_⟩
  · rcases hc p v h with h' | ⟨-, h'⟩
    · exact sf.fits p v n args h' hd hn
    · exact h' n args hd hn
  · rcases hc p _ h with h' | ⟨h', -⟩
    · exact sf.proofCopy p hg h'
    · exact absurd rfl h'

theorem erase_modify (env : Env) (f : Nat) (g h : Frame → Frame) (hg : ∀ fr, (g fr).erase = h fr.erase) :
    Env.erase (env.modify f g) = (Env.erase env).modify f h := by
  apply _root_.Array.ext_getElem?
  intro k
  simp only [Env.erase_get?, Array.getElem?_modify]
  split
  · cases env[k]? with
    | none => rfl
    | some fr => exact congrArg some (hg fr)
  · cases env[k]? <;> rfl

theorem erase_setAtE (env : Env) (p : Pos) (v : Value) : (Env.setAtE env p v).erase = Env.setAtE env.erase p v := by
  cases p <;> exact erase_modify _ _ _ _ fun _ => rfl

theorem erase_pushBindE (env : Env) (h : Hint) (ty : Option Value) (v : Value) (pf : Bool) (d : DeclInfo) :
    (Env.pushBindE env h ty v pf d).erase = Env.pushBindE env.erase h ty v pf d := by
  unfold Env.pushBindE; rw [Env.erase_size]; exact erase_modify _ _ _ _ fun _ => rfl

theorem erase_popBindE (env : Env) : (Env.popBindE env).erase = Env.popBindE env.erase := by
  unfold Env.popBindE; rw [Env.erase_size]; exact erase_modify _ _ _ _ fun _ => rfl

theorem norm_withEnv (st : MState) (e : Env) : ({ st with env := e } : MState).norm = { st.norm with env := e.erase } := rfl

theorem norm_withTempT (st : MState) (v : Value) (T? : Option Value) :
    (st.withTempT v T?).norm = { st.norm with env := Env.pushTempE st.norm.env v } := by
  show { st.norm with env := (st.withTempT v T?).env.erase } = _
  rw [erase_withTempT]; rfl

end Ochr.Meaning.Steps.Machine
