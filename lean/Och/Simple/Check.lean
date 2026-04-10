import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Macro

/-!
# Bidirectional Subtype Checker for Simple Och (with μ)

A fuel-indexed checker for the subtype relation `Sub`, extended with
cycle-detection support for μ on either side.

## Structure

- `synthLam fuel Γ e` : `Option (Expr × Expr)`
  Synthesizes a function type for `e`: if it returns `some (D, R)` then
  `Sub Γ e (.lam D R)` holds. For `e = μA.body`, applies the inductive
  Sub.mu rule: checks `body ⊑ A↑` and synthesises on `A`.
- `subCheck fuel seen Γ a b` : `Bool`
  Decides `Sub Γ a b`. The `seen` list records pairs `(a, b)` that are
  already being checked on the stack. **At every entry point** we first
  consult `seen` — if `(a, b) ∈ seen`, return `true` immediately
  (cycle break). Then we proceed by fuel-indexed structural recursion.

## μ cases (in `subCheck`)

- `b = μA.body` (a ≠ b): unfold RHS and recurse with `(a, b)` added to seen.
  The cycle-break case appeals to `seen` justification.
- `a = μA.body` (b ≠ μ): unfold LHS and recurse with `(a, b)` added to seen.
- `a = b` is caught by [Refl] (after the seen check).

## Soundness

Soundness (`subCheck_sound` / `synthLam_sound`) holds modulo a known gap on
the cycle-break cases. When a recursive call is short-circuited because
`(a, b) ∈ seen`, soundness assumes that the ENTRY in `seen` is itself
justified — but justifying it requires the very `Sub Γ a b` we are trying
to prove. The inductive `Sub` has no coinductive rule, so this is
genuinely circular without coinductive / step-indexed / logical-relation
machinery. It is `sorry`'d here and discussed inline.

Concretely: 5 sorrys remain in this file, one per (a-shape, b-shape) cycle
break case. They are isolated to the cycle-break branches; all other
rules (Refl, Top, Var, Lam-Lam, App, Asc-L, Asc-R, mu via the inductive
Sub.mu) have fully constructive soundness proofs.

## What this checker does NOT yet handle: `dtrue ⊑ dBool`

The dependent-boolean encoding (dtrue, dfalse, dBool) is the canonical
"self-typed" example. With this checker it does NOT yet verify, but the
blocker is **NOT cycle detection** — the cycle is already caught
correctly. The blocker is a missing inductive rule. Detailed diagnosis:

1. muR unfolds dBool, then muL unfolds dtrue: we reach `dtrueU ⊑ dBoolU`
   which is a lam-lam comparison.
2. The Lam contravariant chain on the parameter types eventually reaches
   `dtrue ⊑ dBool` again — and the seen set DOES catch this. (Verified
   directly: pre-loading seen with `(dtrue, dBool)` makes
   `subCheck dtrue dBool` return true.)
3. The BLOCKER is the BODY check (in extended context, with seen cleared).
   It reaches the subgoal `t ⊑ P dBool` where `t : P dtrue` and
   `P : dBool→⊤`. Both sides reduce to `⊤`, but the inductive `Sub` has
   only an [App] rule that reduces apps on the LEFT — there is no
   [Beta-R] / [App-R] rule that lets us reduce `app f a` on the RIGHT.
   We get stuck at `⊤ ⊑ P dBool`, which has no derivation.

Unblocking dtrue ⊑ dBool therefore requires extending `Sub` with the
symmetric dual of `Sub.app`:

    | appR : Sub Γ g (.lam D R) → Sub Γ b D → Sub Γ a (R.subst 0 b) →
             Sub Γ a (.app g b)

and updating `subCheckStep`, `Properties.lean` (weaken_gen, narrow,
trans, subst_gen) and `Soundness.lean` (semanticSubst, evalPreservation).
That extension is left as follow-up work. The seen-set machinery in this
file is therefore necessary but not sufficient for the dependent-bool
encoding.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- Decidable membership in a list of (Expr × Expr). -/
def seenMem (p : Expr × Expr) : List (Expr × Expr) → Bool
  | [] => false
  | q :: rest => (p.1 == q.1 && p.2 == q.2) || seenMem p rest

mutual

/-- Synthesize a "function type" for `e`: returns `some (D, R)` such that
    `Sub Γ e (.lam D R)` is derivable (see `synthLam_sound`).
    When `e = μA.body`, the μ is unfolded. -/
def synthLam (fuel : Nat) (Γ : Ctx) (e : Expr) : Option (Expr × Expr) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .lam D R => some (D, R)
    | .var x =>
      match Γ.get? x with
      | none => none
      | some T => synthLam fuel Γ T
    | .asc e' τ =>
      if subCheck fuel [] Γ e' τ then synthLam fuel Γ τ else none
    | .app f' a' =>
      match synthLam fuel Γ f' with
      | none => none
      | some (D'', R'') =>
        if subCheck fuel [] Γ a' D'' then synthLam fuel Γ (R''.subst 0 a')
        else none
    | .top => none
    | .mu A body =>
      -- Use Sub.mu: synthesize on A, and check body ⊑ A↑ in extended ctx.
      if subCheck fuel [] (A :: Γ) body (A.shift 0 1) then synthLam fuel Γ A
      else none

/-- Decide `Sub Γ a b` up to the supplied `fuel`.

    The dispatch is structured to make soundness easy to prove: the rules are
    tried in a deterministic order (Seen → Refl → Top → muR → Asc-R → Asc-L
    → Var → Lam → App → muL) with non-overlapping conditions.

    The `seen` set is consulted FIRST at every entry point. This catches
    cycles that emerge after several layers of structural recursion (e.g.
    `dtrue ⊑ dBool` arising as the contravariant subgoal of a deeper
    Lam–Lam comparison). -/
def subCheck (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr) : Bool :=
  if seenMem (a, b) seen then true  -- [Cycle] — unconditional cycle break
  else
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if a == b then true  -- [Refl]
    else if b == .top then true  -- [Top]
    else
      match b with
      -- [muR]: unfold RHS first, recording the goal so deeper recursion can
      -- detect a cycle back to this exact subgoal.
      | .mu A body =>
        subCheck fuel ((a, .mu A body) :: seen) Γ a (body.subst 0 (.mu A body))
      | _ =>
        match a with
        -- [muL]: unfold LHS too.
        | .mu A body =>
          subCheck fuel ((.mu A body, b) :: seen) Γ (body.subst 0 (.mu A body)) b
        | _ => subCheckStep fuel seen Γ a b

/-- Post-Refl/Top/muR dispatcher. Factored out so the soundness proof can
    pattern-match uniformly on the shape of `a` / `b`. At entry, `b` is not μ. -/
def subCheckStep (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr) : Bool :=
  match b with
  -- [Asc-R]: a ⊑ (e : τ)
  | .asc e τ => subCheck fuel seen Γ e τ && subCheck fuel seen Γ a e
  -- b = μ is handled before subCheckStep is called — return false here
  -- so the soundness proof has a clean unreachable case.
  | .mu _ _ => false
  | _ =>
    match a with
    -- [Asc-L]: (e : τ) ⊑ b
    | .asc e τ => subCheck fuel seen Γ e τ && subCheck fuel seen Γ τ b
    -- [Var]
    | .var x =>
      match Γ.get? x with
      | none => false
      | some T => subCheck fuel seen Γ T b
    -- [Lam] — only fires when b is also a lam
    | .lam A₁ b₁ =>
      match b with
      | .lam A₂ b₂ =>
        -- Clear seen when entering a binder: seen entries refer to Γ.
        subCheck fuel seen Γ A₂ A₁ && subCheck fuel [] (A₂ :: Γ) b₁ b₂
      | _ => false
    -- [App]
    | .app f arg =>
      match synthLam fuel Γ f with
      | none => false
      | some (D, R) =>
        subCheck fuel seen Γ arg D && subCheck fuel seen Γ (R.subst 0 arg) b
    | .top => false
    -- a = μ is handled upstream by subCheck — return false here.
    | .mu _ _ => false

end  -- mutual

/-- Top-level `check` (alias for `subCheck` with empty `seen`). -/
def check (fuel : Nat) (Γ : Ctx) (e τ : Expr) : Bool :=
  subCheck fuel [] Γ e τ

-- ============================================================
-- Soundness: subCheck and synthLam are sound w.r.t. the inductive Sub
-- ============================================================

/-- Justification for an entry in the `seen` set: we assume the entry is a
    derivable subtyping judgement. In the full soundness theorem this is
    discharged by the outer caller (see `CheckSoundness.lean`). -/
def SeenJustified (seen : List (Expr × Expr)) (Γ : Ctx) : Type :=
  ∀ p, seenMem p seen = true → Sub Γ p.1 p.2

-- Helper: destructing conjunction from Bool.and_eq_true
private theorem bool_and_split {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x <;> cases y <;> simp_all

mutual

/-- `synthLam` soundness: if `synthLam fuel Γ e = some (D, R)` then
    `Sub Γ e (.lam D R)`. -/
noncomputable def synthLam_sound :
    (fuel : Nat) → (Γ : Ctx) → (e : Expr) → (D R : Expr) →
    synthLam fuel Γ e = some (D, R) → Sub Γ e (.lam D R)
  | 0, _, _, _, _, h => by simp [synthLam] at h
  | fuel + 1, Γ, e, D, R, h => by
    cases e with
    | lam D' R' =>
      simp only [synthLam] at h
      obtain ⟨hD, hR⟩ : D' = D ∧ R' = R := by
        have := h
        simp at this
        exact this
      subst hD; subst hR
      exact Sub.refl Γ (.lam D' R')
    | var x =>
      simp only [synthLam] at h
      cases hget : Γ.get? x with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have ih := synthLam_sound fuel Γ T D R h
        exact Sub.var Γ x (.lam D R) T hget ih
    | asc e' τ =>
      simp only [synthLam] at h
      by_cases hcheck : subCheck fuel [] Γ e' τ = true
      · rw [if_pos hcheck] at h
        have hsub_eτ : Sub Γ e' τ := subCheck_sound fuel [] Γ e' τ
          (fun _ hp => by simp [seenMem] at hp) hcheck
        have ih : Sub Γ τ (.lam D R) := synthLam_sound fuel Γ τ D R h
        exact Sub.ascL Γ e' τ (.lam D R) hsub_eτ ih
      · rw [if_neg hcheck] at h; simp at h
    | app f a =>
      simp only [synthLam] at h
      cases hf : synthLam fuel Γ f with
      | none => rw [hf] at h; simp at h
      | some p =>
        obtain ⟨D'', R''⟩ := p
        rw [hf] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        by_cases hcheck : subCheck fuel [] Γ a D'' = true
        · rw [if_pos hcheck] at h
          have hf_sub : Sub Γ f (.lam D'' R'') := synthLam_sound fuel Γ f D'' R'' hf
          have ha_sub : Sub Γ a D'' := subCheck_sound fuel [] Γ a D''
            (fun _ hp => by simp [seenMem] at hp) hcheck
          have hR_sub : Sub Γ (R''.subst 0 a) (.lam D R) :=
            synthLam_sound fuel Γ (R''.subst 0 a) D R h
          exact Sub.app Γ f a (.lam D R) D'' R'' hf_sub ha_sub hR_sub
        · rw [if_neg hcheck] at h; simp at h
    | top => simp [synthLam] at h
    | mu A body =>
      -- synthLam unfolds via Sub.mu: requires Sub Γ A (lam D R) and
      -- Sub (A::Γ) body (A.shift 0 1).
      simp only [synthLam] at h
      by_cases hck : subCheck fuel [] (A :: Γ) body (A.shift 0 1) = true
      · rw [if_pos hck] at h
        have hbody_sub : Sub (A :: Γ) body (A.shift 0 1) :=
          subCheck_sound fuel [] (A :: Γ) body (A.shift 0 1)
            (fun _ hp => by simp [seenMem] at hp) hck
        have hA_sub : Sub Γ A (.lam D R) := synthLam_sound fuel Γ A D R h
        exact Sub.mu Γ A body (.lam D R) hA_sub hbody_sub
      · rw [if_neg hck] at h; simp at h

/-- `subCheck` soundness: if `subCheck fuel seen Γ a b = true` and every
    entry of `seen` is justified, then `Sub Γ a b`.

    The top-level `seen` check is dispatched first. If it fires, we appeal
    to `hjust` directly. Otherwise we proceed by fuel-induction as before.
-/
noncomputable def subCheck_sound :
    (fuel : Nat) → (seen : List (Expr × Expr)) → (Γ : Ctx) → (a b : Expr) →
    SeenJustified seen Γ →
    subCheck fuel seen Γ a b = true → Sub Γ a b
  | 0, seen, Γ, a, b, hjust, h => by
    unfold subCheck at h
    by_cases hseen : seenMem (a, b) seen = true
    · exact hjust (a, b) hseen
    · rw [if_neg hseen] at h; simp at h
  | fuel + 1, seen, Γ, a, b, hjust, h => by
    unfold subCheck at h
    by_cases hseen0 : seenMem (a, b) seen = true
    · exact hjust (a, b) hseen0
    · rw [if_neg hseen0] at h
      simp only at h
      by_cases heq : (a == b) = true
      · have : a = b := beq_iff_eq.mp heq
        subst this
        exact Sub.refl Γ a
      · rw [if_neg heq] at h
        by_cases htop : (b == .top) = true
        · have : b = .top := beq_iff_eq.mp htop
          subst this
          exact Sub.top Γ a
        · rw [if_neg htop] at h
          cases hb : b with
          | mu A body =>
            subst hb
            simp only at h
            -- THE muR GAP: we have descended via muR, but the recursive
            -- subCheck call (with `(a, μA.body)` added to seen) returned
            -- true. To produce a `Sub Γ a (μA.body)`, we would need to
            -- extract from that recursive call a witness — but the
            -- recursive call may itself appeal to the seen entry we just
            -- added (coinductive break). Sound only modulo this gap.
            sorry
          | top => subst hb; exfalso; apply htop; simp
          | var x_b =>
            subst hb; simp only at h
            cases ha : a with
            | mu A body =>
              subst ha; simp only at h
              -- muL cycle-break gap (analogous to muR above).
              sorry
            | _ => subst ha; exact subCheckStep_sound fuel seen Γ _ _ hjust htop h
          | lam A_b b_b =>
            subst hb; simp only at h
            cases ha : a with
            | mu A body =>
              subst ha; simp only at h
              sorry  -- muL gap
            | _ => subst ha; exact subCheckStep_sound fuel seen Γ _ _ hjust htop h
          | app f_b a_b =>
            subst hb; simp only at h
            cases ha : a with
            | mu A body =>
              subst ha; simp only at h
              sorry  -- muL gap
            | _ => subst ha; exact subCheckStep_sound fuel seen Γ _ _ hjust htop h
          | asc e τ =>
            subst hb; simp only at h
            cases ha : a with
            | mu A body =>
              subst ha; simp only at h
              sorry  -- muL gap
            | _ => subst ha; exact subCheckStep_sound fuel seen Γ _ _ hjust htop h

/-- `subCheckStep` soundness. At entry, `b` is not μ and not ⊤. -/
noncomputable def subCheckStep_sound :
    (fuel : Nat) → (seen : List (Expr × Expr)) → (Γ : Ctx) → (a b : Expr) →
    SeenJustified seen Γ →
    ¬ (b == .top) = true →
    subCheckStep fuel seen Γ a b = true → Sub Γ a b := by
  intro fuel seen Γ a b hjust htop h
  unfold subCheckStep at h
  cases hb : b with
  | asc e τ =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    obtain ⟨h1, h2⟩ := bool_and_split h
    have hs1 : Sub Γ e τ := subCheck_sound fuel seen Γ e τ hjust h1
    have hs2 : Sub Γ a e := subCheck_sound fuel seen Γ a e hjust h2
    exact Sub.ascR Γ a e τ hs1 hs2
  | var x_b =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel seen Γ e τ hjust h1
      have hs2 : Sub Γ τ (.var x_b) := subCheck_sound fuel seen Γ τ (.var x_b) hjust h2
      exact Sub.ascL Γ e τ (.var x_b) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.var x_b) := subCheck_sound fuel seen Γ T (.var x_b) hjust h
        exact Sub.var Γ x_a (.var x_b) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel seen Γ arg D hjust h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.var x_b) :=
          subCheck_sound fuel seen Γ (R.subst 0 arg) (.var x_b) hjust h2
        exact Sub.app Γ f arg (.var x_b) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | mu _ _ =>
      subst ha
      simp at h
  | top =>
    subst hb
    exfalso; apply htop; simp
  | lam A₂ b₂ =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel seen Γ e τ hjust h1
      have hs2 : Sub Γ τ (.lam A₂ b₂) := subCheck_sound fuel seen Γ τ (.lam A₂ b₂) hjust h2
      exact Sub.ascL Γ e τ (.lam A₂ b₂) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.lam A₂ b₂) := subCheck_sound fuel seen Γ T (.lam A₂ b₂) hjust h
        exact Sub.var Γ x_a (.lam A₂ b₂) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ A₂ A₁ := subCheck_sound fuel seen Γ A₂ A₁ hjust h1
      -- Body uses fresh empty seen (cleared on context extension).
      have hjust' : SeenJustified [] (A₂ :: Γ) := fun _ hp => by simp [seenMem] at hp
      have hs2 : Sub (A₂ :: Γ) b₁ b₂ :=
        subCheck_sound fuel [] (A₂ :: Γ) b₁ b₂ hjust' h2
      exact Sub.lam Γ A₁ A₂ b₁ b₂ hs1 hs2
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel seen Γ arg D hjust h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.lam A₂ b₂) :=
          subCheck_sound fuel seen Γ (R.subst 0 arg) (.lam A₂ b₂) hjust h2
        exact Sub.app Γ f arg (.lam A₂ b₂) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | mu _ _ =>
      subst ha
      simp at h
  | app f_b a_b =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel seen Γ e τ hjust h1
      have hs2 : Sub Γ τ (.app f_b a_b) := subCheck_sound fuel seen Γ τ (.app f_b a_b) hjust h2
      exact Sub.ascL Γ e τ (.app f_b a_b) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.app f_b a_b) := subCheck_sound fuel seen Γ T (.app f_b a_b) hjust h
        exact Sub.var Γ x_a (.app f_b a_b) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel seen Γ arg D hjust h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.app f_b a_b) :=
          subCheck_sound fuel seen Γ (R.subst 0 arg) (.app f_b a_b) hjust h2
        exact Sub.app Γ f arg (.app f_b a_b) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | mu _ _ =>
      subst ha
      simp at h
  | mu _ _ =>
    -- subCheckStep returns false when b = μ (handled upstream by subCheck).
    subst hb
    simp at h

end  -- mutual soundness

-- ============================================================
-- Sanity tests
-- ============================================================

section Tests

private def BOOL : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 2)))
private def TRUE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))
private def FALSE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

-- Reflexivity
example : check 10 [] .top .top = true := by native_decide
example : check 10 [] BOOL BOOL = true := by native_decide

-- Top
example : check 10 [] BOOL .top = true := by native_decide
example : check 10 [] (.var 0) .top = true := by native_decide

-- TRUE ⊑ BOOL
example : check 10 [] TRUE BOOL = true := by native_decide
-- FALSE ⊑ BOOL
example : check 10 [] FALSE BOOL = true := by native_decide

-- Var
example : check 10 [.top] (.var 0) .top = true := by native_decide

-- Lambda contravariance
example : check 10 [] (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) = true := by
  native_decide

-- μ tests
-- μ on the LEFT — uses Sub.mu (the inductive rule):
-- μ(s : ⊤). ⊤ ⊑ ⊤
example : check 10 [] (.mu .top .top) .top = true := by native_decide

-- μ on the RIGHT (cycle detection):
-- ⊤ ⊑ μ(s : ⊤). ⊤   (unfolds to ⊤ ⊑ ⊤ via [Refl])
example : check 10 [] .top (.mu .top .top) = true := by native_decide

-- Cycle break: μ(s : ⊤). s ⊑ μ(s : ⊤). s — refl handles this
example : check 10 [] (.mu .top (.var 0)) (.mu .top (.var 0)) = true := by native_decide

-- A non-trivial cycle: ⊤ ⊑ μ(s : ⊤). s — unfolds to ⊤ ⊑ μs.s, cycle hit, true
example : check 10 [] .top (.mu .top (.var 0)) = true := by native_decide

-- ── Dependent booleans: dtrue ⊑ dBool ───────────────────────────────
-- The dependent-boolean encoding (dtrue, dfalse, dBool) is the canonical
-- "self-typed" example. With this checker's cycle detection it does NOT yet
-- verify — but the blocker is NOT cycle detection. Diagnosis:
--
-- 1. After muR/muL unfold both sides, we reach the lam-lam comparison
--    `dtrueU ⊑ dBoolU`. The CONTRAVARIANT chain on domain types reaches
--    the original goal `dtrue ⊑ dBool`, which the seen set DOES catch
--    correctly. (Verified directly: with seen pre-loaded with
--    `(dtrue, dBool)`, `subCheck` returns `true` on `dtrue ⊑ dBool`.)
--
-- 2. The BLOCKER is the BODY check, which clears `seen` (because the
--    context grows) and reaches the subgoal
--        `t ⊑ P dBool`     where `t : P dtrue` and `P : dBool→⊤`.
--    Both sides reduce to `⊤`, but the inductive `Sub` in `Subtype.lean`
--    has only an [App] rule that reduces apps on the LEFT — there is no
--    [Beta-R] / [App-R] rule that lets us reduce `app f a` on the RIGHT.
--    So we get stuck at `⊤ ⊑ P dBool` which has no derivation under the
--    current rule set.
--
-- Unblocking dtrue ⊑ dBool therefore requires extending `Sub` with
--    | appR : Sub Γ g (.lam D R) → Sub Γ b D → Sub Γ a (R.subst 0 b) →
--             Sub Γ a (.app g b)
-- and updating `subCheckStep`, `Properties.lean` (weaken_gen, narrow,
-- trans, subst_gen) and `Soundness.lean` (semanticSubst, evalPreservation)
-- accordingly. That extension is left as follow-up work — see
-- `docs/ideas/` for design notes.
--
-- The simpler μ-on-the-right cases below DO work via cycle detection.

end Tests

end Och.Simple
