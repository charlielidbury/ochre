import PSS.Sub
import PSS.SyntaxLemmas

/-!
# Substitution preserves well-formedness (Lemma 5.4)

**Main theorem** (`PSS.subst_wf`):
If `Wf (σ :: Γ) body`, `Wf Γ v`, and `Sub Γ v σ`, then `Wf Γ (body.subst 0 v)`.

## Structure

We prove a generalized form (`subst_wf_gen`) at arbitrary substitution depth j
with a context split `Γ₁ ++ σ :: Γ₂` where `j = Γ₁.length`. This is required
because the lambda case produces a recursive call at depth `j + 1`.

### What is proved (no sorry)
- `subst_wf_gen`: the generalized Wf substitution lemma
  - VAR case: all three sub-cases (k < j, k = j, k > j)
  - TOP case: trivial
  - LAM case: uses shift composition lemma and the generalized IH
  - APP case: delegates to `subst_sub_gen` for subtyping
- `subst_wf`: the top-level theorem (specialization of `subst_wf_gen` at j = 0)
- `wf_shift_gen`: generalized weakening (shift preserves Wf)
- `wf_shift`: weakening specialized to position 0
- `Expr.shift_zero`, `Expr.shift_shift`, `Expr.shift_succ_zero`:
  shift algebra lemmas

### Remaining axioms (standard de Bruijn infrastructure)
- `shift_sub_gen`: shift preserves Sub at arbitrary depth.
  By induction on Sub. Straightforward for refl/top/trans/lam/app_cong.
  beta_L/beta_R need shift/subst commutation; bvar needs context lookup
  after shift.
- `subst_sub_gen`: substitution preserves Sub at arbitrary depth.
  By induction on Sub. Uses shift/subst commutation for beta_L/beta_R;
  uses context lookup for bvar.

Both are standard and self-contained (no mutual dependency with Wf).
-/

open Expr

namespace PSS

/-! ## Shift algebra -/

/-- Shifting by 0 is the identity. -/
theorem Expr.shift_zero (e : Expr) (c : Nat) : e.shift 0 c = e := by
  induction e generalizing c with
  | bvar k => simp only [Expr.shift]; split <;> simp
  | top => rfl
  | lam dom body ih_dom ih_body => simp [Expr.shift, ih_dom, ih_body]
  | app f a ih_f ih_a => simp [Expr.shift, ih_f, ih_a]

/-- Two shifts at the same cutoff compose additively. -/
theorem Expr.shift_shift (e : Expr) (d d' c : Nat) :
    (e.shift d c).shift d' c = e.shift (d + d') c := by
  induction e generalizing c with
  | bvar k =>
    show (if k < c then Expr.bvar k else Expr.bvar (k + d)).shift d' c =
         if k < c then Expr.bvar k else Expr.bvar (k + (d + d'))
    by_cases hkc : k < c
    · simp only [if_pos hkc, Expr.shift, if_pos hkc]
    · simp only [if_neg hkc, Expr.shift]
      have : ¬ (k + d < c) := by omega
      simp only [if_neg this]; congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.lam (ih_dom c)) (ih_body (c + 1))
  | app f a ih_f ih_a =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.app (ih_f c)) (ih_a c)

/-- Corollary: `(v.shift j 0).shift 1 0 = v.shift (j + 1) 0`.
    Used in the lambda case to match the substitution definition's
    `body.subst (j+1) (s.shift 1 0)` with the IH at depth `j + 1`. -/
theorem Expr.shift_succ_zero (v : Expr) (j : Nat) :
    (v.shift j 0).shift 1 0 = v.shift (j + 1) 0 := by
  have h := Expr.shift_shift v j 1 0
  simp [Nat.add_comm] at h; exact h

/-! ## substPrefix: the output context after substitution -/

/-- After substituting away the variable at position `|Γ₁|` in context
    `Γ₁ ++ σ :: Γ₂` with value `v`, the prefix entries become:
    entry at index `i` is substituted at depth `|Γ₁| - 1 - i`. -/
def substPrefix : Ctx → Expr → Ctx
  | [], _ => []
  | dom :: Γ₁, v => dom.subst Γ₁.length (v.shift Γ₁.length 0) :: substPrefix Γ₁ v

@[simp] theorem substPrefix_nil (v : Expr) : substPrefix [] v = [] := rfl
@[simp] theorem substPrefix_cons (dom : Expr) (Γ₁ : Ctx) (v : Expr) :
    substPrefix (dom :: Γ₁) v =
      dom.subst Γ₁.length (v.shift Γ₁.length 0) :: substPrefix Γ₁ v := rfl
@[simp] theorem substPrefix_length (Γ₁ : Ctx) (v : Expr) :
    (substPrefix Γ₁ v).length = Γ₁.length := by
  induction Γ₁ with
  | nil => rfl
  | cons _ _ ih => simp [substPrefix, ih]

/-! ## shiftPrefix: the output context after weakening -/

/-- After inserting `|Δ|` new binders at position `|Γ₁|` in context
    `Γ₁ ++ Γ₂`, the prefix entries are shifted. Entry at index `i`
    is shifted by `d` at cutoff `|Γ₁| - 1 - i` (= the number of
    binders between it and the insertion point). -/
def shiftPrefix : Ctx → Nat → Ctx
  | [], _ => []
  | dom :: Γ₁, d => dom.shift d Γ₁.length :: shiftPrefix Γ₁ d

@[simp] theorem shiftPrefix_nil (d : Nat) : shiftPrefix [] d = [] := rfl
@[simp] theorem shiftPrefix_cons (dom : Expr) (Γ₁ : Ctx) (d : Nat) :
    shiftPrefix (dom :: Γ₁) d = dom.shift d Γ₁.length :: shiftPrefix Γ₁ d := rfl
@[simp] theorem shiftPrefix_length (Γ₁ : Ctx) (d : Nat) : (shiftPrefix Γ₁ d).length = Γ₁.length := by
  induction Γ₁ with
  | nil => rfl
  | cons _ _ ih => simp [shiftPrefix, ih]

/-! ## Axioms: shift/subst preserve Sub -/

/-- Shift preserves subtyping at arbitrary depth.
    By induction on Sub. Straightforward for most constructors.
    beta_L/beta_R require `shift (subst body 0 arg) = subst (shift body) 0 (shift arg)`,
    a standard shift/subst commutation lemma.
    bvar requires `(Γ₁ ++ Γ₂).get? k` related to `(shiftPrefix Γ₁ d ++ Δ ++ Γ₂).get? k'`. -/
axiom shift_sub_gen (Γ₁ : Ctx) (Δ : Ctx) {Γ₂ : Ctx} {a b : Expr}
    (h : Sub (Γ₁ ++ Γ₂) a b) :
    Sub (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂)
        (a.shift Δ.length Γ₁.length) (b.shift Δ.length Γ₁.length)

/-- Substitution preserves subtyping at arbitrary depth.
    By induction on Sub. Uses shift/subst commutation for beta_L/beta_R.
    bvar case requires context lookup after substitution. -/
axiom subst_sub_gen (Γ₁ : Ctx) {σ : Expr} {Γ₂ : Ctx} {a b v : Expr}
    (hsub : Sub (Γ₁ ++ σ :: Γ₂) a b)
    (hwfv : Wf Γ₂ v) (hvsig : Sub Γ₂ v σ) :
    Sub (substPrefix Γ₁ v ++ Γ₂)
        (a.subst Γ₁.length (v.shift Γ₁.length 0))
        (b.subst Γ₁.length (v.shift Γ₁.length 0))

/-! ## Weakening (shift preserves Wf) -/

/-- Generalized weakening: inserting binders at position `|Γ₁|` preserves Wf.
    Proved by matching on the Wf derivation. Uses `shift_sub_gen` for the app case. -/
noncomputable def wf_shift_gen (Γ₁ : Ctx) (Δ : Ctx) {Γ₂ : Ctx} {e : Expr}
    (h : Wf (Γ₁ ++ Γ₂) e) :
    Wf (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂) (e.shift Δ.length Γ₁.length) := by
  match h with
  | .var (k := k) hk =>
    simp only [Expr.shift]
    split
    · next hlt =>
      apply Wf.var
      simp only [List.length_append, shiftPrefix_length]
      have := hk; simp only [List.length_append] at this; omega
    · next hge =>
      apply Wf.var
      simp only [List.length_append, shiftPrefix_length]
      have := hk; simp only [List.length_append] at this; omega
  | .top => exact .top
  | .lam (dom := dom) (body := bd) hdom hbody =>
    simp only [Expr.shift]
    apply Wf.lam
    · exact wf_shift_gen Γ₁ Δ hdom
    · have ih := wf_shift_gen (dom :: Γ₁) Δ hbody
      simp only [shiftPrefix_cons, List.length_cons, List.cons_append] at ih
      exact ih
  | .app (f := f) (a := a) (s := s) hwf_f hwf_a hwf_s hsub_f hsub_a =>
    simp only [Expr.shift]
    have hshift_lam : (Expr.lam s .top).shift Δ.length Γ₁.length =
           .lam (s.shift Δ.length Γ₁.length) .top := by
      simp [Expr.shift]
    exact .app
      (wf_shift_gen Γ₁ Δ hwf_f)
      (wf_shift_gen Γ₁ Δ hwf_a)
      (wf_shift_gen Γ₁ Δ hwf_s)
      (hshift_lam ▸ shift_sub_gen Γ₁ Δ hsub_f)
      (shift_sub_gen Γ₁ Δ hsub_a)

/-- Weakening at position 0: if `Wf Γ e` then `Wf (Δ ++ Γ) (e.shift |Δ| 0)`. -/
noncomputable def wf_shift (Δ : Ctx) {Γ : Ctx} {e : Expr}
    (h : Wf Γ e) : Wf (Δ ++ Γ) (e.shift Δ.length 0) := by
  have h' := wf_shift_gen (Γ₁ := []) Δ h
  simp [shiftPrefix] at h'
  exact h'

/-! ## Substitution preserves Wf (generalized) -/

/-- Generalized substitution lemma: substituting at position `j = |Γ₁|`
    in context `Γ₁ ++ σ :: Γ₂` preserves well-formedness.
    All cases fully proved; the app case uses `subst_sub_gen`. -/
noncomputable def subst_wf_gen (Γ₁ : Ctx) (σ : Expr) (Γ₂ : Ctx)
    (body v : Expr)
    (hwfb : Wf (Γ₁ ++ σ :: Γ₂) body)
    (hwfv : Wf Γ₂ v) (hvsig : Sub Γ₂ v σ) :
    Wf (substPrefix Γ₁ v ++ Γ₂)
       (body.subst Γ₁.length (v.shift Γ₁.length 0)) := by
  match hwfb with
  | .var (k := k) hk =>
    simp only [Expr.subst]
    split
    · -- k = j: replaced by v.shift j 0
      -- Need: Wf (substPrefix Γ₁ v ++ Γ₂) (v.shift |Γ₁| 0)
      -- By weakening at position 0 with Δ = substPrefix Γ₁ v
      have h := wf_shift (substPrefix Γ₁ v) hwfv
      rw [substPrefix_length] at h
      exact h
    · split
      · -- k > j: bvar (k - 1)
        next hne hgt =>
        apply Wf.var
        simp only [List.length_append, substPrefix_length]
        have : k < (Γ₁ ++ σ :: Γ₂).length := hk
        simp only [List.length_append, List.length_cons] at this
        omega
      · -- k < j: bvar k
        next hne hle =>
        apply Wf.var
        simp only [List.length_append, substPrefix_length]
        have : k < (Γ₁ ++ σ :: Γ₂).length := hk
        simp only [List.length_append, List.length_cons] at this
        simp only [beq_iff_eq] at hne
        omega
  | .top => exact .top
  | .lam (dom := dom) (body := bd) hdom hbody =>
    simp only [Expr.subst]
    apply Wf.lam
    · exact subst_wf_gen Γ₁ σ Γ₂ dom v hdom hwfv hvsig
    · -- Rewrite the shift composition:
      -- (v.shift j 0).shift 1 0 = v.shift (j + 1) 0
      rw [Expr.shift_succ_zero]
      -- Apply IH with extended prefix (dom :: Γ₁):
      have ih := subst_wf_gen (dom :: Γ₁) σ Γ₂ bd v hbody hwfv hvsig
      simp only [substPrefix_cons, List.length_cons, List.cons_append] at ih
      exact ih
  | .app (f := f) (a := a) (s := s) hwf_f hwf_a hwf_s hsub_f hsub_a =>
    simp only [Expr.subst]
    exact .app
      (subst_wf_gen Γ₁ σ Γ₂ f v hwf_f hwfv hvsig)
      (subst_wf_gen Γ₁ σ Γ₂ a v hwf_a hwfv hvsig)
      (subst_wf_gen Γ₁ σ Γ₂ s v hwf_s hwfv hvsig)
      (subst_sub_gen Γ₁ hsub_f hwfv hvsig)
      (subst_sub_gen Γ₁ hsub_a hwfv hvsig)

/-! ## Top-level theorem: subst_wf (Lemma 5.4) -/

/-- Substitution preserves well-formedness (Lemma 5.4).
    Replaces the `subst_wf` axiom in Soundness.lean. -/
noncomputable def subst_wf {Γ : Ctx} {σ body v : Expr}
    (hwfb : Wf (σ :: Γ) body)
    (hwfv : Wf Γ v) (hvsig : Sub Γ v σ) :
    Wf Γ (body.subst 0 v) := by
  have h := subst_wf_gen [] σ Γ body v hwfb hwfv hvsig
  simp only [substPrefix, List.nil_append, List.length_nil] at h
  rw [Expr.shift_zero] at h
  exact h

end PSS
