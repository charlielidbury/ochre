/-!
# Syntax of System λ⊲

Hutchins, *Pure Subtype Systems* (POPL 2010), Figure 1 — syntax and notation.

The paper's syntax:

```
s, t, u ::=            Terms
    x                    variable
    Top                  universal supertype
    λx ≤ t. u            function
    t(u)                 application

v, w ::= Top | λx ≤ t. u    Values
```

Formalization tweak (permitted): variables are de Bruijn indices, so binders
are nameless. In `lam t u` the bound `t` is scoped *outside* the binder and
the body `u` binds one variable. Substitution is the standard simultaneous
(σ-calculus style) presentation; `subst1` is the paper's single-variable
substitution `[x ↦ s]u`.
-/

namespace Pss

/-- Terms of System λ⊲ (Figure 1). `lam t u` is `λx ≤ t. u`; `app t u` is `t(u)`. -/
inductive Term : Type where
  | var : Nat → Term
  | top : Term
  | lam : Term → Term → Term
  | app : Term → Term → Term
deriving Repr, DecidableEq

namespace Term

/-- Values `v, w ::= Top | λx ≤ t. u` (Figure 1). -/
inductive Value : Term → Prop where
  | top : Value .top
  | lam (t u : Term) : Value (.lam t u)

/-! ## Renaming and substitution -/

/-- Lift a renaming under one binder (`⇑ρ`): `0 ↦ 0`, `n+1 ↦ ρ n + 1`. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply a renaming to the free variables of a term. -/
def rename (ρ : Nat → Nat) : Term → Term
  | var x => var (ρ x)
  | top => top
  | lam t u => lam (t.rename ρ) (u.rename (liftRen ρ))
  | app t u => app (t.rename ρ) (u.rename ρ)

/-- Shift all free variables up by `d`. -/
def shift (t : Term) (d : Nat := 1) : Term := t.rename (· + d)

/-- Cons a term onto a substitution: `(s .: σ) 0 = s`, `(s .: σ) (n+1) = σ n`. -/
def scons (s : Term) (σ : Nat → Term) : Nat → Term
  | 0 => s
  | n + 1 => σ n

/-- Lift a substitution under one binder (`⇑σ`). -/
def liftSubst (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => (σ n).rename (· + 1)

/-- Apply a simultaneous substitution to the free variables of a term. -/
def subst (σ : Nat → Term) : Term → Term
  | var x => σ x
  | top => top
  | lam t u => lam (t.subst σ) (u.subst (liftSubst σ))
  | app t u => app (t.subst σ) (u.subst σ)

/-- `[x ↦ s]u` (Figure 1, Notation): capture-avoiding substitution of `s` for
the outermost bound variable of `u` (de Bruijn index 0). -/
def subst1 (u s : Term) : Term := u.subst (scons s var)

/-! ## The substitution lemma library

Standard σ-calculus composition laws, proved once and for all. These are the
only de Bruijn boilerplate; everything else in the development works with
`subst1`, `shift` and the corollaries at the end of this section.
-/

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n; cases n <;> rfl

theorem liftRen_comp (ρ ρ' : Nat → Nat) :
    liftRen (ρ' ∘ ρ) = liftRen ρ' ∘ liftRen ρ := by
  funext n; cases n <;> rfl

@[simp] theorem rename_id (t : Term) : t.rename id = t := by
  induction t with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [rename, iht, ihu]
  | app t u iht ihu => simp [rename, iht, ihu]

theorem rename_rename (ρ ρ' : Nat → Nat) (t : Term) :
    (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ) := by
  induction t generalizing ρ ρ' with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [rename, iht, ihu, liftRen_comp]
  | app t u iht ihu => simp [rename, iht, ihu]

@[simp] theorem liftSubst_var : liftSubst var = var := by
  funext n; cases n <;> rfl

@[simp] theorem subst_var (t : Term) : t.subst var = t := by
  induction t with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [subst, iht, ihu]
  | app t u iht ihu => simp [subst, iht, ihu]

/-- Renaming is the special case of substitution by variables. -/
theorem rename_eq_subst (ρ : Nat → Nat) (t : Term) :
    t.rename ρ = t.subst (var ∘ ρ) := by
  induction t generalizing ρ with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu =>
    have : liftSubst (var ∘ ρ) = var ∘ liftRen ρ := by
      funext n; cases n <;> rfl
    simp [rename, subst, iht, ihu, this]
  | app t u iht ihu => simp [rename, subst, iht, ihu]

theorem liftSubst_comp_liftRen (σ : Nat → Term) (ρ : Nat → Nat) :
    liftSubst (σ ∘ ρ) = liftSubst σ ∘ liftRen ρ := by
  funext n; cases n <;> rfl

/-- Substituting after renaming composes the renaming into the substitution. -/
theorem subst_rename (σ : Nat → Term) (ρ : Nat → Nat) (t : Term) :
    (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
  induction t generalizing σ ρ with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [rename, subst, iht, ihu, liftSubst_comp_liftRen]
  | app t u iht ihu => simp [rename, subst, iht, ihu]

theorem liftSubst_rename_comm (σ : Nat → Term) (ρ : Nat → Nat) :
    liftSubst (fun x => (σ x).rename ρ)
      = fun x => (liftSubst σ x).rename (liftRen ρ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show ((σ n).rename ρ).rename (· + 1) = ((σ n).rename (· + 1)).rename (liftRen ρ)
    rw [rename_rename, rename_rename]
    rfl

/-- Renaming after substitution pushes the renaming into the substitution. -/
theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Term) (t : Term) :
    (t.subst σ).rename ρ = t.subst (fun x => (σ x).rename ρ) := by
  induction t generalizing σ ρ with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [rename, subst, iht, ihu, liftSubst_rename_comm]
  | app t u iht ihu => simp [rename, subst, iht, ihu]

theorem liftSubst_subst_comm (σ τ : Nat → Term) :
    liftSubst (fun x => (σ x).subst τ)
      = fun x => (liftSubst σ x).subst (liftSubst τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show ((σ n).subst τ).rename (· + 1) = ((σ n).rename (· + 1)).subst (liftSubst τ)
    rw [rename_subst, subst_rename]
    rfl

/-- Composition of substitutions. -/
theorem subst_subst (σ τ : Nat → Term) (t : Term) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t generalizing σ τ with
  | var x => rfl
  | top => rfl
  | lam t u iht ihu => simp [subst, iht, ihu, liftSubst_subst_comm]
  | app t u iht ihu => simp [subst, iht, ihu]

/-! ### Corollaries for single-variable substitution -/

/-- Substituting into a freshly shifted term is the identity: `[x ↦ s](↑t) = t`. -/
@[simp] theorem shift_subst1 (t s : Term) : (t.shift 1).subst1 s = t := by
  show ((t.rename (· + 1)).subst (scons s var)) = t
  rw [subst_rename]
  show t.subst (fun x => var x) = t
  exact subst_var t

/-- Renaming commutes with `subst1`. -/
theorem rename_subst1 (ρ : Nat → Nat) (u s : Term) :
    (u.subst1 s).rename ρ = (u.rename (liftRen ρ)).subst1 (s.rename ρ) := by
  show (u.subst (scons s var)).rename ρ
      = ((u.rename (liftRen ρ)).subst (scons (s.rename ρ) var))
  rw [rename_subst, subst_rename]
  congr 1
  funext n; cases n <;> rfl

/-- Substitution commutes with `subst1`:
`σ([x ↦ s]u) = [x ↦ σ(s)](⇑σ u)`. -/
theorem subst_subst1 (σ : Nat → Term) (u s : Term) :
    (u.subst1 s).subst σ = (u.subst (liftSubst σ)).subst1 (s.subst σ) := by
  show (u.subst (scons s var)).subst σ
      = (u.subst (liftSubst σ)).subst (scons (s.subst σ) var)
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show σ n = ((σ n).rename (· + 1)).subst (scons (s.subst σ) var)
    rw [subst_rename]
    exact (subst_var (σ n)).symm

/-- `subst1` commutes with itself (the "substitution lemma"):
`[y ↦ s]([x ↦ t]u) = [x ↦ [y ↦ s]t](([y ↦ ↑s]) u)` in de Bruijn form. -/
theorem subst1_subst1 (u t s : Term) :
    (u.subst1 t).subst1 s = (u.subst (liftSubst (scons s var))).subst1 (t.subst1 s) := by
  exact subst_subst1 (scons s var) u t

/-! ## Free variables

`ClosedUnder n t` encodes the paper's `fv(t) ⊆ dom(Γ)` for a context of
length `n`: every free variable of `t` is a de Bruijn index `< n`.
-/

/-- `fv(t) ⊆ {0, …, n−1}` (Figure 1 Notation / Figure 2 P-CTX2). -/
inductive ClosedUnder : Nat → Term → Prop where
  | var {n x : Nat} : x < n → ClosedUnder n (var x)
  | top {n : Nat} : ClosedUnder n top
  | lam {n : Nat} {t u : Term} :
      ClosedUnder n t → ClosedUnder (n + 1) u → ClosedUnder n (lam t u)
  | app {n : Nat} {t u : Term} :
      ClosedUnder n t → ClosedUnder n u → ClosedUnder n (app t u)

end Term

/-! ## Type contexts -/

/-- Type contexts `Γ ::= ∅ | Γ, x ≤ t` (Figure 1). The head of the list is the
innermost binding: entry `i` is the bound of de Bruijn variable `i`, and is
scoped in the tail of the list (the bindings to its right). `dom(Γ)` is
`{0, …, Γ.length − 1}`. -/
abbrev Ctx := List Term

namespace Ctx

/-- `x ≤ t ∈ Γ` (Figure 1, Notation): variable `x` is bound by `t` in `Γ`.
The bound is shifted so that it is scoped in the *whole* of `Γ` — with names
this is invisible; with de Bruijn indices each `there`/`here` step shifts by
one. -/
inductive Bound : Ctx → Nat → Term → Prop where
  | here {Γ : Ctx} {t : Term} : Bound (t :: Γ) 0 (t.shift 1)
  | there {Γ : Ctx} {u t : Term} {x : Nat} :
      Bound Γ x t → Bound (u :: Γ) (x + 1) (t.shift 1)

end Ctx

/-! ## One-hole term contexts -/

/-- One-hole contexts (Figure 1, Notation):
`C ::= [] | C(t) | t(C) | λx ≤ C. t | λx ≤ t. C`. -/
inductive TermCtx : Type where
  | hole : TermCtx
  | appL : TermCtx → Term → TermCtx
  | appR : Term → TermCtx → TermCtx
  | lamBound : TermCtx → Term → TermCtx
  | lamBody : Term → TermCtx → TermCtx

/-- `C[t]`: plug `t` into the hole of `C`. As in the paper this is literal
(capture-permitting) replacement — with de Bruijn indices, a term plugged
under `lamBody` refers to the binder by index 0. -/
def TermCtx.fill : TermCtx → Term → Term
  | .hole, s => s
  | .appL C t, s => .app (C.fill s) t
  | .appR t C, s => .app t (C.fill s)
  | .lamBound C t, s => .lam (C.fill s) t
  | .lamBody t C, s => .lam t (C.fill s)

/-! ## The type relations ⊲ -/

/-- The metavariable `⊲` (Figure 1, "Type relations"): ranges over subtyping
`≤` and type equivalence `≡`. Judgments and rules stated with `⊲` in the
paper are indexed by `Rel` here, so each such rule is literally two rules. -/
inductive Rel : Type where
  | le  -- ≤ subtype
  | eq  -- ≡ type equivalence
deriving Repr, DecidableEq

end Pss
