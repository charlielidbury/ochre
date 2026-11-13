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

mutual
/-- No tail of the term reads the hint. -/
def _root_.Ochr.Term.tailHintFree (Γ : List IndDecl) : Term → Bool
  | .letIn _ _ w => Term.tailHintFree Γ w
  | .seq _ w => Term.tailHintFree Γ w
  | .matchNat _ z u => Term.tailHintFree Γ z && Term.tailHintFree Γ u
  | .matchInd _ _ arms => Term.armsHintFree Γ arms
  | .ctor ty _ _ ps _ =>
    !ps.isEmpty || (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | .val v => Value.topHintFree Γ v
  -- a primitive is conservatively hint-reading, except the reads [Close] puts at its tails
  -- (`peek`/`clone` of a place); `J`'s transported term and `inplace` are not needed yet
  | .prim n [.place _] => n == "peek" || n == "clone"
  | .prim _ _ => false
  | _ => true
termination_by structural t => t

def _root_.Ochr.Term.armsHintFree (Γ : List IndDecl) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: rest => Term.tailHintFree Γ t && Term.armsHintFree Γ rest
termination_by structural arms => arms

/-- The hint reaches the value's meaning through no bare constructor and no sealed program with a
hint-reading tail. -/
def _root_.Ochr.Value.topHintFree (Γ : List IndDecl) : Value → Bool
  | .borrow _ w => Value.topHintFree Γ w
  | .sealed t => Term.tailHintFree Γ t
  | .ind ty _ _ [] _ => (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | _ => true
termination_by structural v => v
end

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The value and the state of a run, without the result's type. -/
def resVS (x : Res × SState) : Sem × SState := (x.1.1, x.2)

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
  simp only [Option.map_some, resVS, hxy.1, hxy.2]

/-- A continuation whose result, up to its type, does not depend on its input's type. -/
theorem tailCont_ok' (f : Res × SState → Option (Res × SState))
    (hf : ∀ (a : Sem) (A B : TyS) (sx : SState), (f ((a, A), sx)).map resVS = (f ((a, B), sx)).map resVS) :
    ∀ x y, resVS x = resVS y → (f x).map resVS = (f y).map resVS := by
  intro x y hxy
  obtain ⟨⟨a, A⟩, sx⟩ := x
  obtain ⟨⟨b, B⟩, sy⟩ := y
  simp only [resVS, Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  exact hf a A B sx

/-- A bind whose continuations agree up to the result's type. -/
theorem SM_bind_congr {α : Type 3} (c : SM α) (k k' : α → SM Res) (s : SState)
    (hk : ∀ a s', (k a s').map resVS = (k' a s').map resVS) :
    ((c >>= k) s).map resVS = ((c >>= k') s).map resVS := by
  simp only [Bind.bind, Monad.toBind, instMonadSM]
  cases hcs : c s with
  | none => rfl
  | some x => exact hk x.1 x.2

mutual
/-- **A run with a hint-free tail reads no hint**: same value, same state at every hint. -/
theorem run_hintIndep : ∀ (t : Term), Term.tailHintFree K.Γ t = true → ∀ (h h' : TyS) (s : SState),
    (run K ρ φ h t s).map resVS = (run K ρ φ h' t s).map resVS
  | .letIn x u w, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [run, run]
    cases hu : run K ρ φ (.plain .err) u s with
    | none => simp only [Bind.bind, hu, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨⟨v, T⟩, s₁⟩ := x
      simp only [Bind.bind, hu, Option.bind_some']
      exact bind_resVS_congr (run_hintIndep w ht h h' _) _ (tailCont_ok' _ (fun _ _ _ _ => rfl))
  | .seq u w, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [run, run]
    cases hu : run K ρ φ (.plain .err) u s with
    | none => simp only [Bind.bind, Monad.toBind, instMonadSM, hu]
    | some x =>
      simp only [Bind.bind, Monad.toBind, instMonadSM, hu]
      exact run_hintIndep w ht h h' _
  | .matchNat p z u, ht, h, h', s => by
    simp only [Term.tailHintFree, Bool.and_eq_true] at ht
    rw [run, run]
    cases hc : contentOf K φ p s with
    | none => simp only [Bind.bind, hc, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
      simp only [Bind.bind, hc, Option.bind_some']
      split <;> rename_i heq <;> (try simp only [heq])
      all_goals first
        | rfl
        | exact bind_resVS_congr (run_hintIndep z ht.1 h h' _) _ (tailCont_ok' _ (fun _ _ _ _ => rfl))
        | exact bind_resVS_congr (run_hintIndep u ht.2 h h' _) _ (tailCont_ok' _ (fun _ _ _ _ => rfl))
  | .matchInd p ty arms, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [run, run]
    cases hc : contentOf K φ p s with
    | none => simp only [Bind.bind, hc, Option.bind_none', Option.map_none]
    | some x =>
      obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
      simp only [Bind.bind, hc, Option.bind_some']
      split <;> rename_i heq <;> (try simp only [heq])
      all_goals first
        | rfl
        | exact bind_resVS_congr (runArm_hintIndep arms ht _ h h' _) _ (tailCont_ok' _ (fun _ _ _ _ => rfl))
  | .ctor ty c hd ps args, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    rw [run, run]
    cases hfind : K.Γ.find? (·.name == ty) with
    | none => simp only [hfind]
    | some d =>
      rw [hfind] at ht
      have hc : (ps.isEmpty && !d.params.isEmpty) = false := by
        cases hp : ps.isEmpty <;> cases hq : d.params.isEmpty <;> simp_all
      first
        | (simp only [hfind, hc, Bool.false_eq_true, if_false])
        | (simp only [hfind, hc]; rfl)
  | .val v, ht, h, h', s => by
    simp only [Term.tailHintFree] at ht
    have e := meanV_hintIndep v ht h h'
    -- the `.val` clause's equation is split by its match on `v`: case on `v` first
    cases v <;> (rw [run, run] <;> first
      | (simp only [Option.map_some, resVS, e])
      | (intros; simp_all))
  | .prim n args, ht, h, h', s => by
    -- only `peek`/`clone` of a place are tail-hint-free primitives, and those read no hint
    rcases args with _ | ⟨u, _ | ⟨u2, rest⟩⟩
    · simp [Term.tailHintFree] at ht
    · cases u <;> first
        | (simp only [Term.tailHintFree, Bool.or_eq_true, beq_iff_eq] at ht
           rcases ht with rfl | rfl <;> rfl)
        | (simp [Term.tailHintFree] at ht)
    · simp [Term.tailHintFree] at ht
  | .place p, _, h, h', s => rfl
  | .borrow p, _, h, h', s => rfl
  | .assign p t, _, h, h', s => rfl
  | .const n, _, h, h', s => rfl
  | .sort l, _, h, h', s => rfl
  | .pi hs ds c, _, h, h', s => by
    first | rfl | (rw [run, run]) | (rw [run, run]; rfl)
  | .fix sf hs ds c dec b, _, h, h', s => by
    first | rfl | (rw [run, run]) | (rw [run, run]; rfl)
  | .call f args hd, _, h, h', s => rfl
  | .nat, _, h, h', s => rfl
  | .zero, _, h, h', s => rfl
  | .succ t, _, h, h', s => rfl
  | .unit, _, h, h', s => rfl
  | .tt, _, h, h', s => rfl
  | .eq A t u, _, h, h', s => rfl
  | .cong f hh, _, h, h', s => rfl
  | .ref A, _, h, h', s => rfl
  | .id A t u, _, h, h', s => rfl
  | .ascribe t A, _, h, h', s => rfl
  | .tind n args, _, h, h', s => rfl

theorem runArm_hintIndep : ∀ (arms : List (Hint × Term)), Term.armsHintFree K.Γ arms = true →
    ∀ (c : Nat) (h h' : TyS) (s : SState),
    (runArm K ρ φ h c arms s).map resVS = (runArm K ρ φ h' c arms s).map resVS
  | [], _, c, h, h', s => rfl
  | (x, t) :: rest, ha, c, h, h', s => by
    simp only [Term.armsHintFree, Bool.and_eq_true] at ha
    simp only [runArm]
    split
    · exact run_hintIndep t ha.1 h h' s
    · exact runArm_hintIndep rest ha.2 (c - 1) h h' s

/-- **A top-hint-free value means the same at every hint.** -/
theorem meanV_hintIndep : ∀ (v : Value), Value.topHintFree K.Γ v = true → ∀ (h h' : TyS),
    meanV K ρ φ h v = meanV K ρ φ h' v
  | .borrow l w, hv, h, h' => by
    simp only [Value.topHintFree] at hv
    exact meanV_hintIndep w hv h h'
  | .sealed t, hv, h, h' => by
    simp only [Value.topHintFree] at hv
    show (match run K ρ φ h t (emptyState _) with | some ((v, _), _) => v | none => .err)
      = (match run K ρ φ h' t (emptyState _) with | some ((v, _), _) => v | none => .err)
    have := run_hintIndep t hv h h' (emptyState 0)
    cases hr : run K ρ φ h t (emptyState 0) <;>
      cases hr' : run K ρ φ h' t (emptyState 0) <;>
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

end

end Ochr.Meaning
