import Ochr.Meaning.RunCongr

/-!
# A run reads its hint's type only, not its label (lead35; docs/31 D223)

The hint reaches a run's value, state and result through `hint.m` alone: a tail or an arm, `split`'s term and the operand
of `clone`/`peek`/`inplace` run at it, a bare constructor reads its record (`hint.data`, a function of `hint.m`), and an
embedded value is typed at it with its label dropped (`valT`, then `label := none`). So two hints with the same type and
different labels give the same run. The frame property's assignment clause needs it: the hint of an assignment's
right-hand side is the place's stored type, whose label is the closure's in the closure and its image in place.
-/

namespace Ochr.Meaning
open Classical

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem tailHint_m {tl : Bool} {h h' : TyS} (hm : h.m = h'.m) : (tailHint tl h).m = (tailHint tl h').m := by
  cases tl <;> simp [tailHint, hm]

theorem data_of_m {h h' : TyS} (hm : h.m = h'.m) : h.data = h'.data := by simp only [TyS.data, hm]

mutual
/-- **A run reads its hint's type only.** -/
theorem runT_hintM : ∀ (tl : Bool) (t : Term) (h h' : TyS), h.m = h'.m → runT K ρ φ tl h t = runT K ρ φ tl h' t
  | tl, .letIn x u w, h, h', hm => by
    rw [runT, runT, runT_hintM tl w (tailHint tl h) (tailHint tl h') (tailHint_m hm)]
  | tl, .seq u w, h, h', hm => by
    rw [runT, runT, runT_hintM tl w (tailHint tl h) (tailHint tl h') (tailHint_m hm)]
  | tl, .matchNat p z u, h, h', hm => by
    rw [runT, runT, runT_hintM tl z (tailHint tl h) (tailHint tl h') (tailHint_m hm),
      runT_hintM tl u (tailHint tl h) (tailHint tl h') (tailHint_m hm)]
  | tl, .matchInd p ty arms, h, h', hm => by
    rw [runT, runT]
    simp only [fun c => runArm_hintM tl arms c (tailHint tl h) (tailHint tl h') (tailHint_m hm)]
  | tl, .ctor ty c hd ps args, h, h', hm => by
    rw [runT, runT, data_of_m hm]
  | tl, .val v, h, h', hm => by
    funext s
    rw [runT_val_def, runT_val_def, meanV_hintM v h h' hm, valT_hintM v h h' hm]
  | tl, .prim n [], h, h', _ => by
    funext s
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n []) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [u], h, h', hm => by
    funext s
    by_cases hc : n = "clone" ∨ n = "peek" ∨ n = "inplace"
    · rcases hc with rfl | rfl | rfl <;> rw [runT, runT, runT_hintM false u h h' hm]
    by_cases e1 : n = "symm"
    · subst e1; rfl
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [u]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [a, b], h, h', hm => by
    funext s
    by_cases e2 : n = "trans" ∨ n = "rewrite" ∨ n = "rewriteR"
    · rcases e2 with rfl | rfl | rfl <;> rfl
    by_cases hsp : n = "split" ∧ ∃ f, a = .const f
    · obtain ⟨rfl, f, rfl⟩ := hsp
      rw [runT, runT, runT_hintM tl b h h' hm]
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [a, b]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [a, b, c], h, h', _ => by
    funext s
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [a, b, c]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [a, b, c, d], h, h', _ => by
    funext s
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [a, b, c, d]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [a, b, c, d, e], h, h', _ => by
    funext s
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [a, b, c, d, e]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n [A, a, b, P, h₀, t], h, h', _ => by
    funext s
    by_cases hJ : n = "J"
    · subst hJ; rfl
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n [A, a, b, P, h₀, t]) s = none := fun hint => by
      rw [runT]
      · rfl
      all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .prim n (a :: b :: c :: d :: e :: f :: g :: rest), h, h', _ => by
    funext s
    have fail : ∀ hint : TyS, runT K ρ φ tl hint (.prim n (a :: b :: c :: d :: e :: f :: g :: rest)) s = none :=
      fun hint => by
        rw [runT]
        · rfl
        all_goals (intros; simp_all)
    rw [fail h, fail h']
  | tl, .place p, h, h', _ => rfl
  | tl, .borrow p, h, h', _ => rfl
  | tl, .assign p t, h, h', _ => rfl
  | tl, .const n, h, h', _ => rfl
  | tl, .sort l, h, h', _ => rfl
  | tl, .pi hs ds c, h, h', _ => by
    first | rfl | (rw [runT, runT]) | (rw [runT, runT]; rfl)
  | tl, .fix sf hs ds c dec b, h, h', _ => by
    first | rfl | (rw [runT, runT]) | (rw [runT, runT]; rfl)
  | tl, .call f args hd, h, h', _ => rfl
  | tl, .nat, h, h', _ => rfl
  | tl, .zero, h, h', _ => rfl
  | tl, .succ t, h, h', _ => rfl
  | tl, .unit, h, h', _ => rfl
  | tl, .tt, h, h', _ => rfl
  | tl, .eq A t u, h, h', _ => rfl
  | tl, .cong f hh, h, h', _ => rfl
  | tl, .ref A, h, h', _ => rfl
  | tl, .id A t u, h, h', _ => rfl
  | tl, .ascribe t A, h, h', _ => rfl
  | tl, .tind n args, h, h', _ => rfl

theorem runArm_hintM : ∀ (tl : Bool) (arms : List (Hint × Term)) (c : Nat) (h h' : TyS), h.m = h'.m →
    runArm K ρ φ tl h c arms = runArm K ρ φ tl h' c arms
  | _, [], c, h, h', _ => rfl
  | tl, (x, t) :: rest, c, h, h', hm => by
    funext s
    simp only [runArm]
    split
    · rw [runT_hintM tl t h h' hm]
    · rw [runArm_hintM tl rest (c - 1) h h' hm]

/-- **A value means the same at hints with the same type.** -/
theorem meanV_hintM : ∀ (v : Value) (h h' : TyS), h.m = h'.m → meanV K ρ φ h v = meanV K ρ φ h' v
  | .borrow l w, h, h', hm => meanV_hintM w h h' hm
  | .gloan l w, h, h', hm => meanV_hintM w h h' hm
  | .sealed t, h, h', hm => by
    show (match runT K ρ φ false h t (emptyState _) with | some ((v, _), _) => v | none => .err)
      = (match runT K ρ φ false h' t (emptyState _) with | some ((v, _), _) => v | none => .err)
    rw [runT_hintM false t h h' hm]
  | .ind ty c hd ps fs, h, h', hm => by
    simp only [meanV, data_of_m hm]
  | .zero, _, _, _ => rfl
  | .unit, _, _, _ => rfl
  | .gfn _, _, _, _ => rfl
  | .clo _ _ _, _, _, _ => rfl
  | .loan _, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .abs _, _, _, _ => rfl
  | .proof, _, _, _ => rfl
  | .tNat, _, _, _ => rfl
  | .tUnit, _, _, _ => rfl
  | .tEq _ _ _, _, _, _ => rfl
  | .tRef _, _, _, _ => rfl
  | .tPi _ _ _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .tInd _ _, _, _, _ => rfl
  | .succ _, _, _, _ => rfl

/-- An embedded value's type, label dropped, at hints with the same type. -/
theorem valT_hintM : ∀ (v : Value) (h h' : TyS), h.m = h'.m →
    ({ valT K ρ φ h v with label := none } : TyS) = { valT K ρ φ h' v with label := none }
  | .sealed t, h, h', hm => by
    simp only [valT, runT_hintM false t h h' hm]
    split
    · split <;> simp [hm]
    · simp [hm]
  | .ind ty c hd ps fs, h, h', hm => by
    simp only [valT, data_of_m hm]
    split
    · split <;> simp [hm]
    · simp [hm]
  | .clo caps t rd, h, h', hm => by
    simp only [valT]; split <;> simp [hm]
  | .loan l, h, h', hm => by
    simp only [valT]; split <;> simp [hm]
  | .zero, _, _, _ => rfl
  | .unit, _, _, _ => rfl
  | .gfn _, _, _, _ => rfl
  | .abs _, _, _, _ => rfl
  | .succ _, _, _, _ => rfl
  | .borrow _ _, _, _, hm => by simp [valT, hm]
  | .gloan _ _, _, _, hm => by simp [valT, hm]
  | .bot, _, _, hm => by simp [valT, hm]
  | .proof, _, _, hm => by simp [valT, hm]
  | .tNat, _, _, hm => by simp [valT, hm]
  | .tUnit, _, _, hm => by simp [valT, hm]
  | .tEq _ _ _, _, _, hm => by simp [valT, hm]
  | .tRef _, _, _, hm => by simp [valT, hm]
  | .tPi _ _ _, _, _, hm => by simp [valT, hm]
  | .sort _, _, _, hm => by simp [valT, hm]
  | .tInd _ _, _, _, hm => by simp [valT, hm]
end

end

end Ochr.Meaning
