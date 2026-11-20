import Ochr.Meaning.RunCongr

/-!
# The run at two assignments and two Δs (the assignment congruence)

The run reads the assignment at an unknown's meaning (`meanV`'s `.abs σ`) and Δ at an unknown's
hint (`valT`'s `.abs σ`), nothing else: its state holds meanings, not values. So two assignments,
and two Δs, that agree at the unknowns a term holds give it the same run, and two that agree at
the unknowns a value holds give it the same meaning (`run_congrA`, `meanV_congrA`). This is what
extends an assignment at a fresh unknown without changing any old meaning (`freshAbs_sim`, and
every step that creates unknowns). The proof follows `RunCongr.lean` (the futures' congruence),
without its state invariant.
-/

namespace Ochr.Meaning

section
variable (K : RunCtx) (Δ' : Nat → TyS) (ρ ρ' : Assignment) (φ : Future)

/-- The two assignments and Δs agree at `σ`. -/
def AgreeA (σ : Nat) : Prop := ρ σ = ρ' σ ∧ K.Δ σ = Δ' σ

/-- The context with the other Δ. -/
abbrev KA : RunCtx := { K with Δ := Δ' }

theorem fixBodyAt_congrA {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, run K ρ φ hint body s₂ = run (KA K Δ') ρ' φ hint body s₂)
    (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) (selfM : Sem) (args : List Sem) :
    fixBodyAt K ρ φ fb s ps out piT start body selfM args = fixBodyAt (KA K Δ') ρ' φ fb s ps out piT start body selfM args := by
  unfold fixBodyAt
  dsimp only
  generalize (args.zip ps).foldl (fixStep fb) (s.pushBind { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi fb.2.2 }, [], []) = F
  obtain ⟨s₂, acc, cells⟩ := F
  dsimp only
  rw [hb]

theorem fixStage_congrA {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, run K ρ φ hint body s₂ = run (KA K Δ') ρ' φ hint body s₂)
    (l : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) :
    ∀ k, fixStage K ρ φ fb l s ps out piT start body k = fixStage (KA K Δ') ρ' φ fb l s ps out piT start body k
  | 0 => rfl
  | k + 1 => by
    show fixBodyAt K ρ φ fb s ps out piT start body (closureAt l φ ps out (fixStage K ρ φ fb l s ps out piT start body k))
      = fixBodyAt (KA K Δ') ρ' φ fb s ps out piT start body (closureAt l φ ps out (fixStage (KA K Δ') ρ' φ fb l s ps out piT start body k))
    rw [fixStage_congrA hb l s ps out piT start k]
    funext args
    exact fixBodyAt_congrA K Δ' ρ ρ' φ hb s ps out piT start _ args

theorem fixG_congrA {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, run K ρ φ hint body s₂ = run (KA K Δ') ρ' φ hint body s₂)
    (l : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) (dec : Option Nat) :
    fixG K ρ φ fb l s ps out piT start dec body = fixG (KA K Δ') ρ' φ fb l s ps out piT start dec body := by
  cases dec with
  | none => exact funext fun args => fixBodyAt_congrA K Δ' ρ ρ' φ hb s ps out piT start _ args
  | some j =>
    funext args
    show fixStage K ρ φ fb l s ps out piT start body (fixRank K ps (some j) args + 1) args
      = fixStage (KA K Δ') ρ' φ fb l s ps out piT start body (fixRank (KA K Δ') ps (some j) args + 1) args
    rw [fixStage_congrA K Δ' ρ ρ' φ hb]
    rfl

end

section
variable (K : RunCtx) (Δ' : Nat → TyS) (ρ ρ' : Assignment) (φ : Future)

mutual
/-- **The run at two assignments and two Δs** that agree at the unknowns the term holds. -/
theorem run_congrA : ∀ (t : Term) (hint : TyS) (s : SState),
    (∀ σ, t.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) →
    run K ρ φ hint t s = run (KA K Δ') ρ' φ hint t s
  | .place p, hint, s, ha => by rw [run, run]; rfl
  | .borrow p, hint, s, ha => by rw [run, run]; rfl
  | .seq u w, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrA u _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro a s₁ _
    apply SM.bind_congr rfl
    intro _ s₂ _
    exact run_congrA w hint _ fun σ h => ha σ (by simp [Term.anyAtom, h])
  | .succ u, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrA u _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro a s₁ _; rfl
  | .ref A, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrA A _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro a s₁ _; rfl
  | .const n, hint, s, ha => by rw [run, run]
  | .sort l, hint, s, ha => by rw [run, run]
  | .nat, hint, s, ha => by rw [run, run]
  | .unit, hint, s, ha => by rw [run, run]
  | .zero, hint, s, ha => by rw [run, run]
  | .tt, hint, s, ha => by rw [run, run]
  | .cong f g, hint, s, ha => by rw [run, run]
  | .val v, hint, s, ha => by
    have hv : ∀ σ, v.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ := fun σ h => ha σ h
    rw [run_val_def, run_val_def, meanV_congrA v hint hv]
    cases v with
    | clo caps t rd =>
      simp only [valT]
      rw [capsVals_congrA caps fun σ h => hv σ (by simp [Value.anyAtom, h]),
        capsTys_congrA rd fun σ h => hv σ (by simp [Value.anyAtom, h]),
        piShapeOf_congrA t _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
    | tPi caps t rd =>
      simp only [valT]
      rw [capsVals_congrA caps fun σ h => hv σ (by simp [Value.anyAtom, h]),
        capsTys_congrA rd fun σ h => hv σ (by simp [Value.anyAtom, h]),
        piShapeOf_congrA t _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
    | sealed t =>
      simp only [valT]
      rw [run_congrA t hint _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
    | abs σ =>
      simp only [valT]
      rw [(hv σ (by simp [Value.anyAtom, BEq.beq, Value.beq])).2]
    | _ => rfl
  | .ascribe u A, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (SM.onCopy_congr (run_congrA A _ s fun σ h => ha σ (by simp [Term.anyAtom, h])))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (run_congrA u _ _ fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro _ _ _; rfl
  | .eq A a b, hint, s, ha => by
    rw [run, run]
    apply SM.onCopy_congr
    apply SM.bind_congr (run_congrA A _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    rintro ⟨TA, _⟩ s₁ _
    apply SM.bind_congr (SM.onCopy_congr (run_congrA a _ s₁ fun σ h => ha σ (by simp [Term.anyAtom, h])))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (run_congrA b _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])))
    intro _ _ _; rfl
  | .id A t u, hint, s, ha => by
    rw [run, run]
    apply Option.bind_congr' (SM.onCopy_congr (run_congrA A _ s fun σ h => ha σ (by simp [Term.anyAtom, h])))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (run_congrA t _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    rintro ⟨r₁, s₁'⟩ _
    apply Option.bind_congr' (run_congrA u _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    rintro ⟨r₂, s₂'⟩ _
    rfl
  | .tind n args, hint, s, ha => by
    rw [run, run]
    cases hd : K.Γ.find? (·.name == n) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrA d args 0 [] s fun σ h => ha σ (by simp [Term.anyAtom, h]))
      intro _ _ _; rfl
  | .call f args hd, hint, s, ha => by
    rw [run, run]
    dsimp only
    refine SM.erasedIf_congr ?_
    have hhead : SM.headOf f (fun p => readPlace K φ p true) (run K ρ φ (.plain .err) f) s
        = SM.headOf f (fun p => readPlace (KA K Δ') φ p true) (run (KA K Δ') ρ' φ (.plain .err) f) s :=
      SM.headOf_congr (fun p => rfl) (run_congrA f _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    apply SM.bind_congr hhead
    intro fv s₁ _
    apply SM.bind_congr (runArgs_congrA _ _ args 0 [] s₁ fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro _ _ _; rfl
  | .matchNat p z u, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₁⟩ _
    dsimp only
    split
    · apply Option.bind_congr' (run_congrA z hint s₁ fun σ h => ha σ (by simp [Term.anyAtom, h]))
      intro _ _; rfl
    · apply Option.bind_congr' (run_congrA u hint s₁ fun σ h => ha σ (by simp [Term.anyAtom, h]))
      intro _ _; rfl
    · rfl
  | .matchInd p n arms, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₁⟩ _
    dsimp only
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrA arms hint c s₁ fun σ h => ha σ (by simp [Term.anyAtom, h]))
      intro _ _; rfl
    · rfl
  | .letIn x u w, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply Option.bind_congr' (run_congrA u _ s fun σ h => ha σ (by simp [Term.anyAtom, h]))
    rintro ⟨⟨v, T⟩, s₁⟩ _
    dsimp only
    apply Option.bind_congr' (run_congrA w hint _ fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro _ _; rfl
  | .assign p u, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    rw [show contentOf (KA K Δ') φ p s = contentOf K φ p s from rfl]
    dsimp only
    apply Option.bind_congr' (run_congrA u _ _ fun σ h => ha σ (by simp [Term.anyAtom, h]))
    intro _ _; rfl
  | .pi hs ds c, hint, s, ha => by
    rw [run, run]
    have hbs := runBinds_congrA s (K.D.paramDecls (scopeOf s) ds) ds [] fun σ h => ha σ (by simp [Term.anyAtom, h])
    have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) c (extendBy s bs acc) :=
      fun bs acc => run_congrA c _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])
    dsimp only
    rw [hbs]
    cases c with
    | ref U =>
      have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) U (extendBy s bs acc) :=
        fun bs acc => run_congrA U _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])
      simp only [hU]
    | _ => simp only [hc]
  | .ctor ty c hh ps args, hint, s, ha => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrA d ps 0 [] s fun σ h => ha σ (by simp [Term.anyAtom, h]))
      intro psM s₁ h1
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      dsimp only
      exact SM.bind_congr (runFields_congrA _ d c args 0 _ [] s₁ fun σ h => ha σ (by simp [Term.anyAtom, h]))
        (fun _ _ _ => rfl)

  | .prim n args, hint, s, ha => by
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState),
        run K ρ φ hint t s = run (KA K Δ') ρ' φ hint t s := fun t hm hint s =>
      runAll_congrA args t hm hint s
        (fun σ h => ha σ (by simp only [Term.anyAtom]; exact anyAtomList_of_mem hm h))
    by_cases h1 : n = "symm"
    · subst h1; rw [run, run]
    by_cases h2 : n = "trans"
    · subst h2; rw [run, run]
    by_cases h3 : n = "rewrite"
    · subst h3; rw [run, run]
    by_cases h4 : n = "rewriteR"
    · subst h4; rw [run, run]
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, hargs⟩ := hJ
      have hm : ∀ x, x ∈ [A, a, b, P, h', t] → x ∈ args := fun x hx => by rw [hargs]; exact hx
      rw [hargs, run, run]
      refine SM.erasedIf_congr ?_
      apply SM.bind_congr (SM.onCopy_congr (hall A (hm A (by simp)) _ s))
      intro _ s₁ e1; have e := SM.onCopy_state e1; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall a (hm a (by simp)) _ _))
      intro _ s₂ e2; have e := SM.onCopy_state e2; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall b (hm b (by simp)) _ _))
      intro _ s₃ e3; have e := SM.onCopy_state e3; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall P (hm P (by simp)) _ _))
      intro _ s₄ e4; have e := SM.onCopy_state e4; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall h' (hm h' (by simp)) _ _))
      intro _ s₅ e5; have e := SM.onCopy_state e5; subst e
      exact hall t (hm t (by simp)) _ _
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl <;>
        (rw [hargs, run, run]
         exact SM.erasedIf_congr (SM.headOf_congr (fun p => rfl) (hall u hu _ _)))
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    rw [run.eq_39 K ρ φ hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3,
      run.eq_39 (KA K Δ') ρ' φ hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3]
  | .fix self hs ds c dec body, hint, s, ha => by
    have hbs : bindsOf K ρ φ s ds = bindsOf (KA K Δ') ρ' φ s ds :=
      runBinds_congrA s (K.D.paramDecls (scopeOf s) ds) ds [] (fun σ h => ha σ (by simp [Term.anyAtom, h]))
    have hds : runDoms K ρ φ s ds = runDoms (KA K Δ') ρ' φ s ds := by unfold runDoms; rw [hbs]
    have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) c (extendBy s bs acc) :=
      fun bs acc => run_congrA c _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])
    have hb : ∀ (hint : TyS) (s₂ : SState), run K ρ φ hint body s₂ = run (KA K Δ') ρ' φ hint body s₂ :=
      fun hint s₂ => run_congrA body hint s₂ fun σ h => ha σ (by simp [Term.anyAtom, h])
    have hout : ∀ bs, fixOut K ρ φ s bs c = fixOut (KA K Δ') ρ' φ s bs c := by
      intro bs
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrA U _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])
        simp only [fixOut, hU]
      | _ => simp only [fixOut, hc]
    have hcod : ∀ bs, fixCod K ρ φ s bs c = fixCod (KA K Δ') ρ' φ s bs c := by
      intro bs
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrA U _ _ fun σ h => ha σ (by simp [Term.anyAtom, h])
        simp only [fixCod, hU]
      | _ => simp only [fixCod, hc]
    rw [run_fix_def, run_fix_def, hds, hbs, hout, hcod]
    rw [fixG_congrA K Δ' ρ ρ' φ hb]
    rfl

theorem meanV_congrA : ∀ (v : Value) (hint : TyS),
    (∀ σ, v.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) → meanV K ρ φ hint v = meanV (KA K Δ') ρ' φ hint v
  | .abs σ, hint, hv => (hv σ (by simp [Value.anyAtom, BEq.beq, Value.beq])).1
  | .succ w, hint, hv => by
    show (meanV K ρ φ _ w).succ = (meanV (KA K Δ') ρ' φ _ w).succ
    rw [meanV_congrA w _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .borrow _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV (KA K Δ') ρ' φ hint w
    exact meanV_congrA w hint fun σ h => hv σ (by simp [Value.anyAtom, h])
  | .gloan _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV (KA K Δ') ρ' φ hint w
    exact meanV_congrA w hint fun σ h => hv σ (by simp [Value.anyAtom, h])
  | .tRef A, hint, hv => by
    show meanV K ρ φ _ A = meanV (KA K Δ') ρ' φ _ A
    exact meanV_congrA A _ fun σ h => hv σ (by simp [Value.anyAtom, h])
  | .tEq A a b, hint, hv => by
    rw [meanV, meanV]
    rw [meanV_congrA A _ fun σ h => hv σ (by simp [Value.anyAtom, h]),
      meanV_congrA a _ fun σ h => hv σ (by simp [Value.anyAtom, h]),
      meanV_congrA b _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .clo caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrA caps fun σ h => hv σ (by simp [Value.anyAtom, h]),
      capsTys_congrA rd fun σ h => hv σ (by simp [Value.anyAtom, h]),
      run_congrA t _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .tPi caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrA caps fun σ h => hv σ (by simp [Value.anyAtom, h]),
      capsTys_congrA rd fun σ h => hv σ (by simp [Value.anyAtom, h]),
      run_congrA t _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .sealed t, hint, hv => by
    rw [meanV, meanV]
    rw [run_congrA t _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .ind ty c h ps fs, hint, hv => by
    rw [meanV, meanV]
    dsimp only
    split
    · rename_i d _
      rw [meanParams_congrA d ps _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
      split
      · rename_i ps' _
        rw [meanFields_congrA d ps' c fs _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
      · rfl
    · rfl
  | .tInd n args, hint, hv => by
    rw [meanV, meanV]
    dsimp only
    split
    · rename_i d _
      rw [meanParams_congrA d args _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
    · rfl
  | .zero, _, _ => rfl
  | .unit, _, _ => rfl
  | .gfn _, _, _ => rfl
  | .bot, _, _ => rfl
  | .loan _, _, _ => rfl
  | .proof, _, _ => rfl
  | .tNat, _, _ => rfl
  | .tUnit, _, _ => rfl
  | .sort _, _, _ => rfl

theorem runAll_congrA : ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (hint : TyS) (s : SState),
    (∀ σ, t.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) →
    run K ρ φ hint t s = run (KA K Δ') ρ' φ hint t s
  | [], t, h, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, hint, s, ha => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ha ⊢; exact run_congrA a hint s ha
    · exact runAll_congrA as t h hint s ha

theorem runBinds_congrA (s : SState) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind),
    (∀ σ, Term.anyAtomList (· == .abs σ) ds = true → AgreeA K Δ' ρ ρ' σ) →
    runBinds K ρ φ s dcs pre ds = runBinds (KA K Δ') ρ' φ s dcs pre ds
  | [], _, _ => rfl
  | d :: ds, pre, ha => by
    have hds := fun pre' => runBinds_congrA s dcs ds pre' (fun σ h => ha σ (by simp [Term.anyAtomList, h]))
    have hd : (fun acc => run K ρ φ (.plain .err) d (extendBy s pre acc))
        = (fun acc => run (KA K Δ') ρ' φ (.plain .err) d (extendBy s pre acc)) :=
      funext fun acc => run_congrA d _ _ (fun σ h => ha σ (by simp [Term.anyAtomList, h]))
    cases d with
    | ref A =>
      have hA : (fun acc => run K ρ φ (.plain .err) A (extendBy s pre acc))
          = (fun acc => run (KA K Δ') ρ' φ (.plain .err) A (extendBy s pre acc)) :=
        funext fun acc => run_congrA A _ _ (fun σ h => ha σ (by simp [Term.anyAtomList, Term.anyAtom, h]))
      simp only [runBinds, hA, hds]
    | _ => simp only [runBinds, hd, hds]

theorem runArgs_congrA (stmt : Bool) (shape : Option (List PiParam × PiOut)) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState),
    (∀ σ, Term.anyAtomList (· == .abs σ) args = true → AgreeA K Δ' ρ ρ' σ) →
    runArgs K ρ φ stmt shape i earlier args s = runArgs (KA K Δ') ρ' φ stmt shape i earlier args s
  | [], _, _, _, _ => rfl
  | a :: as, i, earlier, s, ha => by
    simp only [runArgs]
    apply SM.bind_congr (SM.stmtIf_congr (run_congrA a _ s (fun σ h => ha σ (by simp [Term.anyAtomList, h]))))
    intro r s₁ _
    apply SM.bind_congr (runArgs_congrA stmt shape as _ _ s₁ (fun σ h => ha σ (by simp [Term.anyAtomList, h])))
    intro _ _ _; rfl

theorem runFields_congrA (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (sol : List (Option Sem)) (earlier : List Sem) (s : SState),
    (∀ σ, Term.anyAtomList (· == .abs σ) args = true → AgreeA K Δ' ρ ρ' σ) →
    runFields K ρ φ stmt d c i sol earlier args s = runFields (KA K Δ') ρ' φ stmt d c i sol earlier args s
  | [], _, _, _, _, _ => rfl
  | a :: as, i, sol, earlier, s, ha => by
    simp only [runFields]
    apply SM.bind_congr (SM.stmtIf_congr (run_congrA a _ s (fun σ h => ha σ (by simp [Term.anyAtomList, h]))))
    intro r s₁ _
    apply SM.bind_congr (runFields_congrA stmt d c as _ _ _ s₁ (fun σ h => ha σ (by simp [Term.anyAtomList, h])))
    intro _ _ _; rfl

theorem runParams_congrA (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState),
    (∀ σ, Term.anyAtomList (· == .abs σ) args = true → AgreeA K Δ' ρ ρ' σ) →
    runParams K ρ φ d i earlier args s = runParams (KA K Δ') ρ' φ d i earlier args s
  | [], _, _, _, _ => rfl
  | a :: as, i, earlier, s, ha => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (run_congrA a _ s (fun σ h => ha σ (by simp [Term.anyAtomList, h]))))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrA d as _ _ _ (fun σ h => ha σ (by simp [Term.anyAtomList, h])))
    intro _ _ _; rfl

theorem runArm_congrA : ∀ (arms : List (Hint × Term)) (hint : TyS) (c : Nat) (s : SState),
    (∀ σ, Term.anyAtomArms (· == .abs σ) arms = true → AgreeA K Δ' ρ ρ' σ) →
    runArm K ρ φ hint c arms s = runArm (KA K Δ') ρ' φ hint c arms s
  | [], _, _, _, _ => rfl
  | (_, t) :: rest, hint, c, s, ha => by
    simp only [runArm]
    split
    · exact run_congrA t hint s (fun σ h => ha σ (by simp [Term.anyAtomArms, h]))
    · exact runArm_congrA rest hint (c - 1) s (fun σ h => ha σ (by simp [Term.anyAtomArms, h]))

theorem capsVals_congrA : ∀ (vs : List Value),
    (∀ σ, Value.anyAtomList (· == .abs σ) vs = true → AgreeA K Δ' ρ ρ' σ) →
    capsVals K ρ φ vs = capsVals (KA K Δ') ρ' φ vs
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [capsVals]
    rw [meanV_congrA v _ (fun σ h => hv σ (by simp [Value.anyAtomList, h])),
      capsVals_congrA vs (fun σ h => hv σ (by simp [Value.anyAtomList, h]))]

theorem capsTys_congrA : ∀ (rd : List (DeclInfo × Value)),
    (∀ σ, Value.anyAtomRd (· == .abs σ) rd = true → AgreeA K Δ' ρ ρ' σ) →
    capsTys K ρ φ rd = capsTys (KA K Δ') ρ' φ rd
  | [], _ => rfl
  | (d, T) :: rest, hv => by
    simp only [capsTys]
    rw [meanV_congrA T _ (fun σ h => hv σ (by simp [Value.anyAtomRd, h])),
      tyShape_congrA T (fun σ h => hv σ (by simp [Value.anyAtomRd, h])),
      tyDataV_congrA T (fun σ h => hv σ (by simp [Value.anyAtomRd, h])),
      capsTys_congrA rest (fun σ h => hv σ (by simp [Value.anyAtomRd, h]))]

theorem tyShape_congrA : ∀ (T : Value),
    (∀ σ, T.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) → tyShape K ρ φ T = tyShape (KA K Δ') ρ' φ T
  | .tPi caps t rd, hv => by
    rw [tyShape, tyShape]
    rw [capsVals_congrA caps fun σ h => hv σ (by simp [Value.anyAtom, h]),
      capsTys_congrA rd fun σ h => hv σ (by simp [Value.anyAtom, h]),
      piShapeOf_congrA t _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
  | .tRef A, hv => by
    rw [tyShape, tyShape]
    exact tyShape_congrA A fun σ h => hv σ (by simp [Value.anyAtom, h])
  | .zero, _ | .succ _, _ | .unit, _ | .gfn _, _ | .clo _ _ _, _ | .borrow _ _, _ | .gloan _ _, _ | .loan _, _ | .bot, _ | .abs _, _
  | .sealed _, _ | .proof, _ | .tNat, _ | .tUnit, _ | .tEq _ _ _, _ | .sort _, _ | .ind _ _ _ _ _, _ | .tInd _ _, _ => by
    simp only [tyShape]

theorem tyDataV_congrA : ∀ (T : Value),
    (∀ σ, T.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) → tyDataV K ρ φ T = tyDataV (KA K Δ') ρ' φ T
  | .tInd n args, hv => by
    rw [tyDataV, tyDataV]
    dsimp only
    split
    · rename_i d _
      rw [meanParams_congrA d args _ _ fun σ h => hv σ (by simp [Value.anyAtom, h])]
    · rfl
  | .tRef A, hv => by
    rw [tyDataV, tyDataV]
    exact tyDataV_congrA A fun σ h => hv σ (by simp [Value.anyAtom, h])
  | .zero, _ | .succ _, _ | .unit, _ | .gfn _, _ | .clo _ _ _, _ | .borrow _ _, _ | .gloan _ _, _ | .loan _, _ | .bot, _ | .abs _, _
  | .sealed _, _ | .proof, _ | .tNat, _ | .tUnit, _ | .tEq _ _ _, _ | .sort _, _ | .ind _ _ _ _ _, _ | .tPi _ _ _, _ => by
    simp only [tyDataV]

theorem meanFields_congrA (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ σ, Value.anyAtomList (· == .abs σ) vs = true → AgreeA K Δ' ρ ρ' σ) →
    meanFields K ρ φ d ps c i earlier vs = meanFields (KA K Δ') ρ' φ d ps c i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanFields]
    rw [meanV_congrA v _ (fun σ h => hv σ (by simp [Value.anyAtomList, h])),
      meanFields_congrA d ps c vs _ _ (fun σ h => hv σ (by simp [Value.anyAtomList, h]))]

theorem meanParams_congrA (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ σ, Value.anyAtomList (· == .abs σ) vs = true → AgreeA K Δ' ρ ρ' σ) →
    meanParams K ρ φ d i earlier vs = meanParams (KA K Δ') ρ' φ d i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanParams]
    rw [meanV_congrA v _ (fun σ h => hv σ (by simp [Value.anyAtomList, h])),
      meanParams_congrA d vs _ _ (fun σ h => hv σ (by simp [Value.anyAtomList, h]))]

theorem piShapeOf_congrA : ∀ (t : Term) (s : SState),
    (∀ σ, t.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) →
    piShapeOf K ρ φ s t = piShapeOf (KA K Δ') ρ' φ s t
  | t, s, ha => by
    cases t with
    | pi hs ds c =>
      have hbs := runBinds_congrA s (K.D.paramDecls (scopeOf s) ds) ds [] (fun σ h => ha σ (by simp [Term.anyAtom, h]))
      have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) c (extendBy s bs acc) :=
        fun bs acc => run_congrA c _ _ (fun σ h => ha σ (by simp [Term.anyAtom, h]))
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrA U _ _ (fun σ h => ha σ (by simp [Term.anyAtom, h]))
        simp only [piShapeOf, hU, hbs]
      | _ => simp only [piShapeOf, hc, hbs]
    | fix self hs ds c dec body =>
      have hbs := runBinds_congrA s (K.D.paramDecls (scopeOf s) ds) ds [] (fun σ h => ha σ (by simp [Term.anyAtom, h]))
      have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) c (extendBy s bs acc) :=
        fun bs acc => run_congrA c _ _ (fun σ h => ha σ (by simp [Term.anyAtom, h]))
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run (KA K Δ') ρ' φ (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrA U _ _ (fun σ h => ha σ (by simp [Term.anyAtom, h]))
        simp only [piShapeOf, hU, hbs]
      | _ => simp only [piShapeOf, hc, hbs]
    | _ => simp only [piShapeOf]
end

end

end Ochr.Meaning
