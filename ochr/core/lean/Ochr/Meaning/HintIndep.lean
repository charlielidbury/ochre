import Ochr.Meaning.Lemmas

/-!
# Hint-independence of a run with a hint-free tail

The hint reaches a run only at its tail positions: the bodies of `let` and `;`, the arms of a
match, `J`'s transported term, the operand of `peek`/`clone`/`inplace`, and at a tail an embedded
value (`.val`, read at the hint) or a constructor term without parameters (`hint.data`). A term
whose tails read none of these (`Term.tailHintFree`) runs to the same value and state at every
hint; only the result's type component carries the hint. A value is `topHintFree` when the hint
reaches its meaning through no bare constructor and no sealed program with a hint-reading tail.

This is what discharges `HintFree` for a sealed content — a borrow of a closed-off call's
result, `⌈…; peek(*r)⌉`, whose tail is a read — where `Lemmas.hintFree_of_recorded` stops
(docs/31, item 2's residual).
-/

namespace Ochr.Meaning

-- `Term.tailHintFree`, `Term.armsHintFree` and `Value.topHintFree` are in `Value.lean` (read by
-- (WF16), `WF.lean`).

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The value, the result's label and the state of a run, without the rest of the result's type
(the label is read after a borrow-typed non-tail match, D90 [Entry]'s lending). -/
def resVS (x : Res × SState) : Sem × Option Nat × SState := (x.1.1, x.1.2.label, x.2)

theorem Option.bind_none' {α β : Type _} (f : α → Option β) : (none : Option α).bind f = none := rfl
theorem Option.bind_some' {α β : Type _} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

/-- A continuation that reads only the value and the state of its input keeps the equality of
runs up to the result's type. -/
theorem bind_resVS_congr {o o' : Option (Res × SState)} (ih : o.map resVS = o'.map resVS)
    (f : Res × SState → Option (Res × SState))
    (hf : ∀ x y, resVS x = resVS y → (f x).map resVS = (f y).map resVS) :
    (o.bind f).map resVS = (o'.bind f).map resVS := by
  cases o with
  | none => cases o' with
    | none => rfl
    | some y => simp at ih
  | some x => cases o' with
    | none => simp at ih
    | some y =>
      simp only [Option.map_some, Option.some.injEq] at ih
      simp only [Option.bind]
      exact hf x y ih

/-- The continuations of the run's tail clauses: the value kept, the state transformed. -/
theorem tailCont_ok (g : SState → SState) :
    ∀ x y : Res × SState, resVS x = resVS y →
      (some ((x.1.1, x.1.2), g x.2) : Option (Res × SState)).map resVS
        = (some ((y.1.1, y.1.2), g y.2)).map resVS := by
  intro x y hxy
  simp only [resVS, Prod.mk.injEq] at hxy
  simp only [Option.map_some, resVS, hxy.1, hxy.2.1, hxy.2.2]

/-- A continuation whose result, up to its type but its label, does not depend on its input's
type but its label. -/
theorem tailCont_ok' (f : Res × SState → Option (Res × SState))
    (hf : ∀ (a : Sem) (A B : TyS) (sx : SState), A.label = B.label →
      (f ((a, A), sx)).map resVS = (f ((a, B), sx)).map resVS) :
    ∀ x y, resVS x = resVS y → (f x).map resVS = (f y).map resVS := by
  intro x y hxy
  obtain ⟨⟨a, A⟩, sx⟩ := x
  obtain ⟨⟨b, B⟩, sy⟩ := y
  simp only [resVS, Prod.mk.injEq] at hxy
  obtain ⟨rfl, hl, rfl⟩ := hxy
  exact hf a A B sx hl

/-- A bind whose continuations agree up to the result's type. -/
theorem SM_bind_congr {α : Type 3} (c : SM α) (k k' : α → SM Res) (s : SState)
    (hk : ∀ a s', (k a s').map resVS = (k' a s').map resVS) :
    ((c >>= k) s).map resVS = ((c >>= k') s).map resVS := by
  simp only [Bind.bind, Monad.toBind, instMonadSM]
  cases hcs : c s with
  | none => rfl
  | some x => exact hk x.1 x.2

/-- A statement position keeps the equality of runs up to the result's type. -/
theorem stmtIf_resVS_congr (b : Bool) {x x' : SM Res} {s : SState} (h : (x s).map resVS = (x' s).map resVS) :
    (SM.stmtIf b x s).map resVS = (SM.stmtIf b x' s).map resVS := by
  cases b with
  | false => exact h
  | true =>
    simp only [SM.stmtIf, if_true]
    cases hx : x s <;> cases hx' : x' s <;> simp [hx, hx', resVS] at h ⊢
    exact h.1

/-- An erased or statement position keeps the equality of runs up to the result's type. -/
theorem erasedIf_resVS_congr (fl : Bool × Bool) {x x' : SM Res} {s : SState} (h : (x s).map resVS = (x' s).map resVS) :
    (SM.erasedIf fl x s).map resVS = (SM.erasedIf fl x' s).map resVS := by
  unfold SM.erasedIf
  split
  · -- an erased clause runs on a copy and keeps only whether it ran to `•`: read from its value
    cases hx : x s <;> cases hx' : x' s <;> simp only [hx, hx', Option.map_some, Option.map_none,
      reduceCtorEq, Option.some.injEq] at h ⊢
    rename_i a a'
    obtain ⟨⟨v, T⟩, s₁⟩ := a
    obtain ⟨⟨v', T'⟩, s₁'⟩ := a'
    simp only [resVS, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    cases v <;> rfl
  · exact stmtIf_resVS_congr _ h

/-- An erased match on a proof keeps the equality of its arms' runs up to their types. -/
theorem anyArm_resVS {n : Nat} {f g : Nat → SM Res} {s : SState}
    (h : ∀ c, (f c s).map resVS = (g c s).map resVS) :
    (SM.anyArm n f s).map resVS = (SM.anyArm n g s).map resVS := by
  have key : ∀ c, SM.ranProof (f c s) = SM.ranProof (g c s) ∧
      ((f c s).map fun x => ((x.1.1, { x.1.2 with label := none }), s)).map resVS =
      ((g c s).map fun x => ((x.1.1, { x.1.2 with label := none }), s)).map resVS := by
    intro c
    have hc := h c
    cases hf : f c s with
    | none => cases hg : g c s with
      | none => simp
      | some y => rw [hf, hg] at hc; cases hc
    | some x => cases hg : g c s with
      | none => rw [hf, hg] at hc; cases hc
      | some y =>
        rw [hf, hg] at hc
        obtain ⟨⟨v, R⟩, s₁⟩ := x
        obtain ⟨⟨v', R'⟩, s₂⟩ := y
        simp only [Option.map_some, Option.some.injEq, resVS, Prod.mk.injEq] at hc
        obtain ⟨rfl, -, -⟩ := hc
        cases v <;> simp [resVS, SM.ranProof]
  unfold SM.anyArm
  have hp : (fun c => SM.ranProof (f c s)) = (fun c => SM.ranProof (g c s)) := funext fun c => (key c).1
  rw [hp]
  split
  · rename_i c _; exact (key c).2
  · rfl

mutual
/-- **A run with a hint-free tail reads no hint**: same value, same state at every hint. -/
theorem runT_hintIndep : ∀ (tl : Bool) (t : Term), Term.tailHintFree K.Γ t = true → ∀ (h h' : TyS) (s : SState),
    (runT K ρ φ tl h t s).map resVS = (runT K ρ φ tl h' t s).map resVS
  | tl, .letIn x u w, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [runT, runT]
    refine erasedIf_resVS_congr _ ?_
    cases hu : runT K ρ φ false (.plain .err) u s with
    | none => simp only [Bind.bind, hu, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨⟨v, T⟩, s₁⟩ := x
      simp only [Bind.bind, hu, Option.bind_some']
      exact bind_resVS_congr (runT_hintIndep tl w ht h h' _) _ (tailCont_ok' _ (fun _ _ _ _ hl => by simp only [Option.map_some, resVS, hl]))
  | tl, .seq u w, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [runT, runT]
    refine erasedIf_resVS_congr _ ?_
    cases hu : runT K ρ φ false (.plain .err) u s with
    | none => simp only [Bind.bind, Monad.toBind, instMonadSM, hu]
    | some x =>
      simp only [Bind.bind, Monad.toBind, instMonadSM, hu]
      exact runT_hintIndep tl w ht h h' _
  | tl, .matchNat p z u, ht, h, h', s => by
    simp only [Term.tailHintFree, Bool.and_eq_true] at ht
    rw [runT, runT]
    refine erasedIf_resVS_congr _ ?_
    cases hc : tagOf K φ p natTag s with
    | none => simp only [Bind.bind, hc, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨tg, s₁⟩ := x
      simp only [Bind.bind, hc, Option.bind_some']
      split <;> rename_i heq <;> (try simp only [heq])
      all_goals first
        | rfl
        | exact bind_resVS_congr (runT_hintIndep tl z ht.1 h h' _) _ (tailCont_ok' _ (fun _ _ _ _ hl => by simp only [Option.map_some, resVS, hl]))
        | exact bind_resVS_congr (runT_hintIndep tl u ht.2 h h' _) _ (tailCont_ok' _ (fun _ _ _ _ hl => by simp only [Option.map_some, resVS, hl]))
  | tl, .matchInd p ty arms, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [runT, runT]
    refine erasedIf_resVS_congr _ ?_
    cases hc : tagOf K φ p indTag s with
    | none => simp only [Bind.bind, hc, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨tg, s₁⟩ := x
      simp only [Bind.bind, hc, Option.bind_some']
      split <;> rename_i heq <;> (try simp only [heq])
      all_goals first
        | rfl
        | exact bind_resVS_congr (runArm_hintIndep tl arms ht _ h h' _) _ (tailCont_ok' _ (fun _ _ _ _ hl => by simp only [Option.map_some, resVS, hl]))
        | (split <;> first | rfl | exact anyArm_resVS fun c => runArm_hintIndep tl arms ht c h h' _)
  | tl, .ctor ty c hd ps args, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [runT, runT]
    refine erasedIf_resVS_congr _ ?_
    cases hfind : K.Γ.find? (·.name == ty) with
    | none => simp only [hfind]
    | some d =>
      rw [hfind] at ht
      -- the record known before the fields does not read the hint: the parameters are written,
      -- or there are none
      have hrh : (!ps.isEmpty || d.params.isEmpty) = true := by simpa using ht
      simp only [hfind, hrh, if_true]
  | tl, .val v, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    have e := meanV_hintIndep v ht h h'
    rw [runT_val_def, runT_val_def, e]
    cases v with
    | ind ty c hd ps fs =>
      -- the strict test reads the type, which the hint reaches only at a bare constructor of a
      -- parametrised type (not hint-free) or where the meaning is `err` (no test: a failure)
      simp only [strictVal]
      by_cases he : meanV K ρ φ h' (.ind ty c hd ps fs) = .err
      · simp only [he, if_true]
      · simp only [he, if_false]
        have hT : valT K ρ φ h (.ind ty c hd ps fs) = valT K ρ φ h' (.ind ty c hd ps fs) := by
          cases hfd : K.Γ.find? (·.name == ty) with
          | none => exact absurd (by simp only [meanV, hfd]) he
          | some d =>
            cases ps with
            | nil =>
              simp only [Value.topHintFree, hfd] at ht
              simp only [valT, hfd, ht, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
            | cons p ps => simp only [valT, hfd, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
        rw [hT]
    | clo | sealed => simp only [strictVal]; split <;> simp only [Option.map_none, Option.map_some, resVS]
    | _ => simp only [strictVal, pure, Option.map_some, resVS]
  | tl, .prim n args, ht, h, h', s => by
    -- only `peek`/`clone` of a place are tail-hint-free primitives, and those read no hint
    rcases args with _ | ⟨u, _ | ⟨u2, rest⟩⟩
    · simp [Term.tailHintFree] at ht
    · cases u <;> first
        | (simp only [Term.tailHintFree, Bool.or_eq_true, beq_iff_eq] at ht
           rcases ht with rfl | rfl <;> rfl)
        | (simp [Term.tailHintFree] at ht)
    · simp [Term.tailHintFree] at ht
  | tl, .place p, _, h, h', s => rfl
  | tl, .borrow p, _, h, h', s => rfl
  | tl, .assign p t, _, h, h', s => rfl
  | tl, .const n, _, h, h', s => rfl
  | tl, .sort l, _, h, h', s => rfl
  | tl, .pi hs ds c, _, h, h', s => by
    first | rfl | (rw [runT, runT]) | (rw [runT, runT]; rfl)
  | tl, .fix sf hs ds c dec b, _, h, h', s => by
    first | rfl | (rw [runT, runT]) | (rw [runT, runT]; rfl)
  | tl, .call f args hd, _, h, h', s => rfl
  | tl, .nat, _, h, h', s => rfl
  | tl, .zero, _, h, h', s => rfl
  | tl, .succ t, _, h, h', s => rfl
  | tl, .unit, _, h, h', s => rfl
  | tl, .tt, _, h, h', s => rfl
  | tl, .eq A t u, _, h, h', s => rfl
  | tl, .cong f hh, _, h, h', s => rfl
  | tl, .ref A, _, h, h', s => rfl
  | tl, .id A t u, _, h, h', s => rfl
  | tl, .ascribe t A, _, h, h', s => rfl
  | tl, .tind n args, _, h, h', s => rfl

theorem runArm_hintIndep : ∀ (tl : Bool) (arms : List (Hint × Term)), Term.armsHintFree K.Γ arms = true →
    ∀ (c : Nat) (h h' : TyS) (s : SState),
    (runArm K ρ φ tl h c arms s).map resVS = (runArm K ρ φ tl h' c arms s).map resVS
  | _, [], _, c, h, h', s => rfl
  | tl, (x, t) :: rest, ha, c, h, h', s => by
    simp only [Term.armsHintFree, Bool.and_eq_true] at ha
    simp only [runArm]
    split
    · exact runT_hintIndep tl t ha.1 h h' s
    · exact runArm_hintIndep tl rest ha.2 (c - 1) h h' s

/-- **A top-hint-free value means the same at every hint.** -/
theorem meanV_hintIndep : ∀ (v : Value), Value.topHintFree K.Γ v = true → ∀ (h h' : TyS),
    meanV K ρ φ h v = meanV K ρ φ h' v
  | .borrow l w, hv, h, h' => by
    simp only [Value.topHintFree] at hv
    exact meanV_hintIndep w hv h h'
  | .gloan l w, hv, h, h' => by
    simp only [Value.topHintFree] at hv
    exact meanV_hintIndep w hv h h'
  | .sealed t, hv, h, h' => by
    simp only [Value.topHintFree] at hv
    show (match runT K ρ φ false h t (emptyState _) with | some ((v, _), _) => v | none => .err)
      = (match runT K ρ φ false h' t (emptyState _) with | some ((v, _), _) => v | none => .err)
    have := runT_hintIndep false t hv h h' (emptyState 0)
    cases hr : runT K ρ φ false h t (emptyState 0) <;>
      cases hr' : runT K ρ φ false h' t (emptyState 0) <;>
      simp [hr, hr', resVS] at this ⊢
    · exact this.1
  | .ind ty c hd ps fs, hv, h, h' => by
    simp only [meanV]
    cases ps with
    | nil =>
      simp only [Value.topHintFree] at hv
      split
      · next d hd' =>
        rw [hd'] at hv
        simp [hv]
      · rfl
    | cons p ps => simp
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
end

/-- `runT_hintIndep` at a position that is not a tail. -/
theorem run_hintIndep (t : Term) (ht : Term.tailHintFree K.Γ t = true) (h h' : TyS) (s : SState) :
    (run K ρ φ h t s).map resVS = (run K ρ φ h' t s).map resVS :=
  runT_hintIndep K ρ φ false t ht h h' s

end

end Ochr.Meaning
