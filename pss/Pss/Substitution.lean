import Pss.Declarative
import Pss.Induction
import Pss.Basic
import Pss.Weakening

/-!
# Substitution for the declarative system (§5, Lemma 5.4)

De Bruijn rendering of the paper's `[x ↦ t']` acting at position `|Ξ|`:
`sigmaAt n t'` substitutes `t'` for variable `n` (suitably shifted) and
lowers all higher variables by one; `Ctx.substAt` applies it pointwise to a
context suffix. The transport theorem and the Lemma 5.4 statement follow in
the second half of this file.
-/

namespace Pss

/-! ## The single-variable substitution at depth `n` -/

/-- `sigmaAt n t'` is the paper's `[x ↦ t']` for the variable at de Bruijn
index `n`: variables `< n` are untouched, variable `n` becomes `t'.shift n`,
and variables `> n` are lowered by one. `sigmaAt 0 t'` is `Term.subst1`'s
substitution. -/
def sigmaAt : Nat → Term → Nat → Term
  | 0, t' => Term.scons t' Term.var
  | n + 1, t' => Term.liftSubst (sigmaAt n t')

theorem sigmaAt_lt {n x : Nat} (t' : Term) (h : x < n) :
    sigmaAt n t' x = .var x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    cases x with
    | zero => rfl
    | succ x =>
      show (sigmaAt n t' x).rename _ = _
      rw [ih (by omega)]
      rfl

theorem sigmaAt_self (n : Nat) (t' : Term) :
    sigmaAt n t' n = t'.shift n := by
  induction n with
  | zero => exact (Term.shift_zero t').symm
  | succ n ih =>
    show (sigmaAt n t' n).rename _ = _
    rw [ih]
    exact Term.shift_shift t' n

theorem sigmaAt_gt {n y : Nat} (t' : Term) (h : n ≤ y) :
    sigmaAt n t' (y + 1) = .var y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    cases y with
    | zero => omega
    | succ y =>
      show (sigmaAt n t' (y + 1)).rename _ = _
      rw [ih (by omega)]
      rfl

/-- Substituting under one shift skips the shifted binder:
`(↑b).subst (⇑σ) = ↑(b.subst σ)`. -/
theorem Term.shift_subst_lift (σ : Nat → Term) (b : Term) :
    (b.shift 1).subst (Term.liftSubst σ) = (b.subst σ).shift 1 := by
  show (b.rename _).subst _ = (b.subst _).rename _
  rw [Term.subst_rename, Term.rename_subst]
  congr 1

/-- A term shifted past the substituted variable is merely unshifted by one:
`(b.shift (n+1)).subst (sigmaAt n t') = b.shift n`. -/
theorem subst_sigmaAt_shift (b t' : Term) (n : Nat) :
    (b.shift (n + 1)).subst (sigmaAt n t') = b.shift n := by
  show (b.rename _).subst _ = b.rename _
  rw [Term.subst_rename, Term.rename_eq_subst]
  congr 1
  funext x
  show sigmaAt n t' (x + (n + 1)) = .var (x + n)
  have h : x + (n + 1) = (x + n) + 1 := by omega
  rw [h, sigmaAt_gt t' (by omega)]

/-! ## Pointwise substitution in a context suffix -/

/-- `[x ↦ t']Γ'` (Lemma 5.4): substitute pointwise in the context suffix
inside the binding being eliminated. Entry `u` at depth `|Ξ|` from the
binding is scoped in its own tail, so it is substituted at that depth. -/
def Ctx.substAt (t' : Term) : Ctx → Ctx
  | [] => []
  | u :: Ξ => u.subst (sigmaAt Ξ.length t') :: Ctx.substAt t' Ξ

@[simp] theorem Ctx.substAt_length (t' : Term) (Ξ : Ctx) :
    (Ctx.substAt t' Ξ).length = Ξ.length := by
  induction Ξ with
  | nil => rfl
  | cons u Ξ ih => simp [Ctx.substAt, ih]

/-! ## Bound transport along `substAt` -/

/-- The bound of the variable being substituted is the marker entry itself:
`|Ξ| ≤ t ∈ Ξ ++ t :: Γ₀`, shifted into whole-context scope. -/
theorem Ctx.bound_at_split {Ξ Γ₀ : Ctx} {t b : Term}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) Ξ.length b) : b = t.shift (Ξ.length + 1) := by
  induction Ξ generalizing b with
  | nil => cases h with | here => rfl
  | cons s Ξ ih =>
    cases h with
    | there h' =>
      rw [ih h', Term.shift_shift]
      rfl

/-- Bounds of variables inside `Ξ` transport pointwise. -/
theorem Ctx.bound_substAt_lt {Ξ Γ₀ : Ctx} {t b t' : Term} {x : Nat}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) x b) (hx : x < Ξ.length) :
    Ctx.Bound (Ctx.substAt t' Ξ ++ Γ₀) x (b.subst (sigmaAt Ξ.length t')) := by
  induction Ξ generalizing x b with
  | nil => simp at hx
  | cons s Ξ ih =>
    cases h with
    | here =>
      show Ctx.Bound _ 0 ((s.shift 1).subst (Term.liftSubst _))
      rw [Term.shift_subst_lift]
      exact .here
    | there h' =>
      rename_i b' x'
      show Ctx.Bound _ (x' + 1) ((b'.shift 1).subst (Term.liftSubst _))
      rw [Term.shift_subst_lift]
      exact .there (ih h' (by simp at hx; omega))

/-- Bounds of variables outside the binding lower by one. -/
theorem Ctx.bound_substAt_gt {Ξ Γ₀ : Ctx} {t b t' : Term} {y : Nat}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) (y + 1) b) (hy : Ξ.length ≤ y) :
    Ctx.Bound (Ctx.substAt t' Ξ ++ Γ₀) y (b.subst (sigmaAt Ξ.length t')) := by
  induction Ξ generalizing y b with
  | nil =>
    cases h with
    | there h' =>
      rename_i b'
      show Ctx.Bound Γ₀ y ((b'.shift 1).subst1 t')
      rw [Term.shift_subst1 b' t']
      exact h'
  | cons s Ξ ih =>
    cases y with
    | zero => simp at hy
    | succ y =>
      cases h with
      | there h' =>
        rename_i b'
        show Ctx.Bound _ (y + 1) ((b'.shift 1).subst (Term.liftSubst _))
        rw [Term.shift_subst_lift]
        exact .there (ih h' (by simp at hy; omega))

end Pss
