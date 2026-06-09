import Pss.Syntax
import Pss.Star

/-!
# Operational semantics of System λ⊲

Figure 1, "Reduction":

```
      t ⟶ t'
  ───────────────  (E-CONG)        (λx ≤ t. u)(s) ⟶ [x ↦ s]u   (E-APP)
  C[t] ⟶ C[t']
```

Reduction is full β-reduction closed under arbitrary one-hole contexts `C`
(including under binders and inside bounds), exactly as in the paper.

`Step` is the paper-faithful presentation. `Step.Compat` is the standard
per-constructor compatible closure; `step_iff_compat` proves the two
coincide, which both sanity-checks the `C[·]` encoding and provides the more
convenient induction principle for the metatheory.
-/
namespace Pss

/-- Small-step reduction `t ⟶ t'` (Figure 1). -/
inductive Step : Term → Term → Prop where
  /-- `(λx ≤ t. u)(s) ⟶ [x ↦ s]u` (E-APP). -/
  | eapp {t u s : Term} : Step (.app (.lam t u) s) (u.subst1 s)
  /-- `t ⟶ t'  ⟹  C[t] ⟶ C[t']` (E-CONG). -/
  | econg {t t' : Term} (C : TermCtx) :
      Step t t' → Step (C.fill t) (C.fill t')

/-- Multi-step reduction `t ⟶* t'`. -/
abbrev Steps : Term → Term → Prop := Star Step

/-- A term is strongly normalizing if all reduction sequences from it are
finite (accessibility of the inverse step relation). Used to *state*
Theorem 4.4 (System λ⊲ is **not** strongly normalizing). -/
def StronglyNormalizing (t : Term) : Prop := Acc (fun a b => Step b a) t

/-- An infinite reduction sequence, as a function enumerating its terms. -/
def InfiniteReduction (f : Nat → Term) : Prop := ∀ n, Step (f n) (f (n + 1))

namespace Step

/-- The compatible closure of β: E-CONG unrolled into one congruence rule per
term constructor. Equivalent to `Step` (`step_iff_compat`) and the more
convenient induction principle. -/
inductive Compat : Term → Term → Prop where
  | eapp {t u s : Term} : Compat (.app (.lam t u) s) (u.subst1 s)
  | appL {t t' : Term} (u : Term) : Compat t t' → Compat (.app t u) (.app t' u)
  | appR (t : Term) {u u' : Term} : Compat u u' → Compat (.app t u) (.app t u')
  | lamBound {t t' : Term} (u : Term) : Compat t t' → Compat (.lam t u) (.lam t' u)
  | lamBody (t : Term) {u u' : Term} : Compat u u' → Compat (.lam t u) (.lam t u')

theorem Compat.fill {t t' : Term} (C : TermCtx) (h : Compat t t') :
    Compat (C.fill t) (C.fill t') := by
  induction C with
  | hole => exact h
  | appL C u ih => exact .appL u ih
  | appR u C ih => exact .appR u ih
  | lamBound C u ih => exact .lamBound u ih
  | lamBody u C ih => exact .lamBody u ih

/-- The paper's context-closure presentation and the per-constructor
compatible closure define the same reduction relation. -/
theorem step_iff_compat {t t' : Term} : Step t t' ↔ Compat t t' := by
  constructor
  · intro h
    induction h with
    | eapp => exact .eapp
    | econg C _ ih => exact ih.fill C
  · intro h
    induction h with
    | eapp => exact .eapp
    | appL u _ ih => exact .econg (.appL .hole u) ih
    | appR t _ ih => exact .econg (.appR t .hole) ih
    | lamBound u _ ih => exact .econg (.lamBound .hole u) ih
    | lamBody t _ ih => exact .econg (.lamBody t .hole) ih

/-! Depth-one congruence helpers for `Step` itself. -/

theorem appL {t t' : Term} (u : Term) (h : Step t t') :
    Step (.app t u) (.app t' u) := .econg (.appL .hole u) h

theorem appR (t : Term) {u u' : Term} (h : Step u u') :
    Step (.app t u) (.app t u') := .econg (.appR t .hole) h

theorem lamBound {t t' : Term} (u : Term) (h : Step t t') :
    Step (.lam t u) (.lam t' u) := .econg (.lamBound .hole u) h

theorem lamBody (t : Term) {u u' : Term} (h : Step u u') :
    Step (.lam t u) (.lam t u') := .econg (.lamBody t .hole) h

end Step

end Pss
