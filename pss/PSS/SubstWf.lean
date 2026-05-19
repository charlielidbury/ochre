import PSS.Sub
import PSS.SyntaxLemmas

/-!
# Substitution preserves well-formedness (Lemma 5.4)

**Main theorem** (`PSS.subst_wf`):
If `Wf (σ :: Γ) body`, `Wf Γ v`, and `Sub Γ v σ`, then `Wf Γ (body.subst 0 v)`.

## Structure

All four generalized lemmas (`shift_sub_gen`, `wf_shift_gen`, `subst_sub_gen`,
`subst_wf_gen`) are proved in a single `mutual` block because:
- The Sub lemmas' `trans` case needs the Wf lemmas (for the middle-term guard)
- The Wf lemmas' `app` case needs the Sub lemmas (for the subtyping witnesses)

Termination: all recursive calls are on strict sub-terms of the mutually
inductive `Sub`/`Wf` derivation.
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

/-- Corollary: `(v.shift j 0).shift 1 0 = v.shift (j + 1) 0`. -/
theorem Expr.shift_succ_zero (v : Expr) (j : Nat) :
    (v.shift j 0).shift 1 0 = v.shift (j + 1) 0 := by
  have h := Expr.shift_shift v j 1 0
  simp [Nat.add_comm] at h; exact h

/-! ## substPrefix: the output context after substitution -/

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

/-! ## Context lookup helpers -/

private theorem list_get?_append_left {α : Type} {l₁ l₂ : List α} {k : Nat}
    (h : k < l₁.length) : (l₁ ++ l₂).get? k = l₁.get? k := by
  simp only [List.get?_eq_getElem?, List.getElem?_append_left (by exact h)]

private theorem list_get?_append_right {α : Type} {l₁ l₂ : List α} {k : Nat}
    (h : l₁.length ≤ k) : (l₁ ++ l₂).get? k = l₂.get? (k - l₁.length) := by
  simp only [List.get?_eq_getElem?]
  rw [List.getElem?_append_right (by exact h)]

/-! ### shiftPrefix lookup -/

/-- Lookup in shiftPrefix: the k-th entry of `shiftPrefix Γ₁ d` is the k-th entry
    of `Γ₁` shifted by `d` at cutoff `|Γ₁| - 1 - k`. -/
theorem shiftPrefix_get? {Γ₁ : Ctx} {d : Nat}
    (k : Nat) (hk : k < Γ₁.length) :
    (shiftPrefix Γ₁ d).get? k = (Γ₁.get? k).map (fun t => t.shift d (Γ₁.length - 1 - k)) := by
  induction Γ₁ generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    cases k with
    | zero =>
      simp only [shiftPrefix, List.get?, List.length_cons, Option.map]
      rfl
    | succ k' =>
      simp only [shiftPrefix, List.get?, List.length_cons]
      have hk' : k' < tl.length := by simp [List.length_cons] at hk; omega
      rw [ih k' hk']
      cases htl : tl.get? k' with
      | none => rfl
      | some t =>
        simp only [Option.map]
        congr 2; omega

/-- Lookup in the full shifted context for an index in the prefix. -/
theorem shiftCtx_get?_prefix {Γ₁ Δ Γ₂ : Ctx} {k : Nat} {t : Expr}
    (hk : k < Γ₁.length)
    (hget : (Γ₁ ++ Γ₂).get? k = some t) :
    (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂).get? k =
      some (t.shift Δ.length (Γ₁.length - 1 - k)) := by
  have hget' : Γ₁.get? k = some t := by
    rwa [list_get?_append_left hk] at hget
  rw [list_get?_append_left (by simp [shiftPrefix_length]; omega)]
  rw [list_get?_append_left (by simp [shiftPrefix_length]; omega)]
  rw [shiftPrefix_get? k hk, hget']
  rfl

/-- Lookup in the full shifted context for an index past the prefix. -/
theorem shiftCtx_get?_suffix {Γ₁ Δ Γ₂ : Ctx} {k : Nat} {t : Expr}
    (hge : ¬(k < Γ₁.length))
    (hget : (Γ₁ ++ Γ₂).get? k = some t) :
    (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂).get? (k + Δ.length) = some t := by
  have hge' : Γ₁.length ≤ k := by omega
  have hget' : Γ₂.get? (k - Γ₁.length) = some t := by
    rwa [list_get?_append_right hge'] at hget
  -- Rewrite the list as (prefix ++ Δ) ++ Γ₂
  rw [show (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂) =
    (shiftPrefix Γ₁ Δ.length ++ Δ) ++ Γ₂ from by rw [List.append_assoc]]
  have hlen : (shiftPrefix Γ₁ Δ.length ++ Δ).length ≤ k + Δ.length := by
    simp [shiftPrefix_length]; omega
  rw [list_get?_append_right hlen]
  have : k + Δ.length - (shiftPrefix Γ₁ Δ.length ++ Δ).length = k - Γ₁.length := by
    simp [shiftPrefix_length]; omega
  rw [this]
  exact hget'

/-! ### substPrefix lookup -/

/-- Lookup in substPrefix: the k-th entry is the k-th entry of Γ₁ after substitution. -/
theorem substPrefix_get? {Γ₁ : Ctx} {v : Expr}
    (k : Nat) (hk : k < Γ₁.length) :
    (substPrefix Γ₁ v).get? k =
      (Γ₁.get? k).map (fun t => t.subst (Γ₁.length - 1 - k) (v.shift (Γ₁.length - 1 - k) 0)) := by
  induction Γ₁ generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    cases k with
    | zero =>
      simp only [substPrefix, List.get?, List.length_cons, Option.map]
      rfl
    | succ k' =>
      simp only [substPrefix, List.get?, List.length_cons]
      have hk' : k' < tl.length := by simp [List.length_cons] at hk; omega
      rw [ih k' hk']
      cases htl : tl.get? k' with
      | none => rfl
      | some t =>
        simp only [Option.map]
        have h1 : tl.length - 1 - k' = tl.length + 1 - 1 - (k' + 1) := by omega
        rw [h1]

/-- Lookup in substPrefix ++ Γ₂ for k < |Γ₁| (prefix). -/
theorem substCtx_get?_prefix {Γ₁ : Ctx} {Γ₂ : Ctx} {σ : Expr} {k : Nat} {t v : Expr}
    (hk : k < Γ₁.length)
    (hget : (Γ₁ ++ σ :: Γ₂).get? k = some t) :
    (substPrefix Γ₁ v ++ Γ₂).get? k =
      some (t.subst (Γ₁.length - 1 - k) (v.shift (Γ₁.length - 1 - k) 0)) := by
  have hget' : Γ₁.get? k = some t := by
    rwa [list_get?_append_left hk] at hget
  rw [list_get?_append_left (by simp; omega)]
  rw [substPrefix_get? k hk, hget']
  rfl

/-- Lookup in substPrefix ++ Γ₂ for k > |Γ₁| (suffix). -/
theorem substCtx_get?_suffix {Γ₁ : Ctx} {Γ₂ : Ctx} {σ : Expr} {k : Nat} {t v : Expr}
    (hk : k > Γ₁.length)
    (hget : (Γ₁ ++ σ :: Γ₂).get? k = some t) :
    (substPrefix Γ₁ v ++ Γ₂).get? (k - 1) = some t := by
  have hget' : Γ₂.get? (k - Γ₁.length - 1) = some t := by
    rw [list_get?_append_right (by omega)] at hget
    -- hget : (σ :: Γ₂).get? (k - |Γ₁|) = some t, and k - |Γ₁| ≥ 1
    -- Rewrite index: k - |Γ₁| = (k - |Γ₁| - 1) + 1
    rw [show k - Γ₁.length = (k - Γ₁.length - 1) + 1 from by omega] at hget
    -- Now hget : (σ :: Γ₂).get? ((k - |Γ₁| - 1) + 1) = some t
    -- which is Γ₂.get? (k - |Γ₁| - 1) = some t
    exact hget
  have hlen : (substPrefix Γ₁ v).length ≤ k - 1 := by simp; omega
  rw [list_get?_append_right hlen]
  simp only [substPrefix_length]
  have : k - 1 - Γ₁.length = k - Γ₁.length - 1 := by omega
  rw [this]
  exact hget'

/-! ## Mutual block: shift/subst preserve Sub and Wf -/

mutual

/-- Shift preserves subtyping at arbitrary depth. -/
noncomputable def shift_sub_gen (Γ₁ : Ctx) (Δ : Ctx) {Γ₂ : Ctx} {a b : Expr}
    (h : Sub (Γ₁ ++ Γ₂) a b) :
    Sub (shiftPrefix Γ₁ Δ.length ++ Δ ++ Γ₂)
        (a.shift Δ.length Γ₁.length) (b.shift Δ.length Γ₁.length) := by
  match h with
  | .refl e => exact .refl (e.shift Δ.length Γ₁.length)
  | .top e => simp [Expr.shift]; exact .top (e.shift Δ.length Γ₁.length)
  | .trans h1 h2 hw =>
    exact .trans (shift_sub_gen Γ₁ Δ h1) (shift_sub_gen Γ₁ Δ h2) (wf_shift_gen Γ₁ Δ hw)
  | .bvar (k := k) (t := t) hk =>
    simp only [Expr.shift]
    split
    · -- k < |Γ₁|: variable is in the prefix
      next hlt =>
      have hlook := shiftCtx_get?_prefix (Δ := Δ) (Γ₂ := Γ₂) hlt hk
      have hsub := Sub.bvar hlook
      -- hsub : Sub _ (.bvar k) ((t.shift d (|Γ₁|-1-k)).shift (k+1) 0)
      -- goal : Sub _ (.bvar k) ((t.shift (k+1) 0).shift d |Γ₁|)
      -- By shift_comm: (t.shift d₂ c₂).shift d₁ c₁ = (t.shift d₁ c₁).shift d₂ (c₂ + d₁) when c₁ ≤ c₂
      -- With d₂ = |Δ|, c₂ = |Γ₁|-1-k, d₁ = k+1, c₁ = 0:
      -- LHS of shift_comm = (t.shift |Δ| (|Γ₁|-1-k)).shift (k+1) 0
      -- RHS = (t.shift (k+1) 0).shift |Δ| (|Γ₁|-1-k + (k+1))
      --     = (t.shift (k+1) 0).shift |Δ| |Γ₁|
      conv at hsub =>
        rhs
        rw [Expr.shift_comm t (k + 1) Δ.length 0 (Γ₁.length - 1 - k) (Nat.zero_le _)]
        rw [show Γ₁.length - 1 - k + (k + 1) = Γ₁.length from by omega]
      exact hsub
    · -- k ≥ |Γ₁|: variable is in Γ₂
      next hge =>
      have hlook := shiftCtx_get?_suffix (Γ₁ := Γ₁) (Δ := Δ) (Γ₂ := Γ₂) hge hk
      have hsub := Sub.bvar hlook
      -- hsub : Sub _ (.bvar (k+|Δ|)) (t.shift (k+|Δ|+1) 0)
      -- goal : Sub _ (.bvar (k+|Δ|)) ((t.shift (k+1) 0).shift |Δ| |Γ₁|)
      have hle : Γ₁.length ≤ k + 1 := by omega
      -- Rewrite goal: (t.shift (k+1) 0).shift |Δ| |Γ₁|
      -- = (t.shift (k+1) 0).shift |Δ| (0 + |Γ₁|)
      -- = t.shift (k+1+|Δ|) 0                          by shift_shift_of_le
      -- = t.shift (k+|Δ|+1) 0
      have hconv : (Expr.shift (k + 1) 0 t).shift Δ.length Γ₁.length =
          Expr.shift (k + Δ.length + 1) 0 t := by
        rw [show Γ₁.length = 0 + Γ₁.length from by omega]
        rw [Expr.shift_shift_of_le t (k + 1) Δ.length Γ₁.length 0 hle]
        congr 1; omega
      rw [hconv]
      exact hsub
  | .lam (dom := dom) (dom' := dom') (body := body) (body' := body')
      hsub1 hsub2 hsub3 =>
    simp only [Expr.shift]
    apply Sub.lam
    · exact shift_sub_gen Γ₁ Δ hsub1
    · exact shift_sub_gen Γ₁ Δ hsub2
    · have ih := shift_sub_gen (dom :: Γ₁) Δ hsub3
      simp only [shiftPrefix_cons, List.length_cons, List.cons_append] at ih
      exact ih
  | .app_cong hf ha ha' =>
    simp only [Expr.shift]
    exact .app_cong (shift_sub_gen Γ₁ Δ hf) (shift_sub_gen Γ₁ Δ ha)
      (shift_sub_gen Γ₁ Δ ha')
  | .beta_L (dom := dom) (body := body) (arg := arg) =>
    simp only [Expr.shift]
    rw [Expr.shift_subst_comm body arg Δ.length Γ₁.length 0 (Nat.zero_le _)]
    exact .beta_L
  | .beta_R (dom := dom) (body := body) (arg := arg) =>
    simp only [Expr.shift]
    rw [Expr.shift_subst_comm body arg Δ.length Γ₁.length 0 (Nat.zero_le _)]
    exact .beta_R

/-- Generalized weakening: inserting binders at position `|Γ₁|` preserves Wf. -/
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

/-- Substitution preserves subtyping at arbitrary depth. -/
noncomputable def subst_sub_gen (Γ₁ : Ctx) {σ : Expr} {Γ₂ : Ctx} {a b v : Expr}
    (hsub : Sub (Γ₁ ++ σ :: Γ₂) a b)
    (hwfv : Wf Γ₂ v) (hvsig : Sub Γ₂ v σ) :
    Sub (substPrefix Γ₁ v ++ Γ₂)
        (a.subst Γ₁.length (v.shift Γ₁.length 0))
        (b.subst Γ₁.length (v.shift Γ₁.length 0)) := by
  match hsub with
  | .refl e => exact .refl (e.subst Γ₁.length (v.shift Γ₁.length 0))
  | .top e =>
    simp only [Expr.subst]
    exact .top (e.subst Γ₁.length (v.shift Γ₁.length 0))
  | .trans h1 h2 hw =>
    exact .trans (subst_sub_gen Γ₁ h1 hwfv hvsig)
                 (subst_sub_gen Γ₁ h2 hwfv hvsig)
                 (subst_wf_gen Γ₁ σ Γ₂ _ v hw hwfv hvsig)
  | .bvar (k := k) (t := t) hk =>
    simp only [Expr.subst]
    split
    · -- k = j (= |Γ₁|): the substituted variable
      next heq =>
      simp only [beq_iff_eq] at heq; subst heq
      -- (Γ₁ ++ σ :: Γ₂).get? |Γ₁| = some t, so t = σ
      have ht : t = σ := by
        rw [list_get?_append_right (by omega)] at hk
        simp only [List.get?, Nat.sub_self] at hk
        exact (Option.some.injEq _ _).mp hk |>.symm
      -- Goal: Sub _ (v.shift |Γ₁| 0) ((t.shift (|Γ₁|+1) 0).subst |Γ₁| (v.shift |Γ₁| 0))
      -- Rewrite t to σ, then use shift_subst_cancel
      rw [ht]
      -- Goal: Sub _ (v.shift |Γ₁| 0) ((σ.shift (|Γ₁|+1) 0).subst |Γ₁| (v.shift |Γ₁| 0))
      have heq : (σ.shift Γ₁.length 0).shift 1 Γ₁.length = σ.shift (Γ₁.length + 1) 0 := by
        have h := Expr.shift_shift_of_le σ Γ₁.length 1 Γ₁.length 0 (Nat.le_refl _)
        simp only [Nat.zero_add] at h
        exact h
      rw [← heq, Expr.shift_subst_cancel]
      -- Now: Sub _ (v.shift |Γ₁| 0) σ
      -- By weakening hvsig at position 0 with Δ = substPrefix Γ₁ v:
      have hsub_shifted := shift_sub_gen (Γ₁ := []) (substPrefix Γ₁ v) hvsig
      simp only [shiftPrefix, List.nil_append, substPrefix_length] at hsub_shifted
      exact hsub_shifted
    · split
      · -- k > j: bvar (k - 1)
        next hne hgt =>
        simp only [beq_iff_eq] at hne
        have hgt' : k > Γ₁.length := by omega
        -- Lookup: (Γ₁ ++ σ :: Γ₂).get? k = some t with k > |Γ₁|
        have hlook := substCtx_get?_suffix (v := v) hgt' hk
        have hsub' := Sub.bvar hlook
        -- hsub' : Sub _ (.bvar (k-1)) (t.shift ((k-1)+1) 0)
        -- goal  : Sub _ (.bvar (k-1)) ((t.shift (k+1) 0).subst |Γ₁| (v.shift |Γ₁| 0))
        -- Since (k-1)+1 = k (because k > 0):
        have hk_pos : k ≥ 1 := by omega
        have hk_eq : k - 1 + 1 = k := by omega
        rw [hk_eq] at hsub'
        -- hsub' : Sub _ (.bvar (k-1)) (t.shift k 0)
        -- Rewrite target: t.shift (k+1) 0 = (t.shift k 0).shift 1 |Γ₁| since |Γ₁| ≤ k
        have hle : Γ₁.length ≤ k := by omega
        have heq2 : (t.shift k 0).shift 1 Γ₁.length = t.shift (k + 1) 0 := by
          rw [show Γ₁.length = 0 + Γ₁.length from by omega]
          exact Expr.shift_shift_of_le t k 1 Γ₁.length 0 hle
        rw [← heq2, Expr.shift_subst_cancel]
        exact hsub'
      · -- k < j: bvar k
        next hne hle =>
        simp only [beq_iff_eq] at hne
        have hlt : k < Γ₁.length := by omega
        have hlook := substCtx_get?_prefix (σ := σ) (v := v) hlt hk
        have hsub' := Sub.bvar hlook
        -- hsub' : Sub _ (.bvar k) ((t.subst (|Γ₁|-1-k) (v.shift (|Γ₁|-1-k) 0)).shift (k+1) 0)
        -- goal  : Sub _ (.bvar k) ((t.shift (k+1) 0).subst |Γ₁| (v.shift |Γ₁| 0))
        -- By shift_subst_comm_ge:
        -- (t.subst j s).shift d c = (t.shift d c).subst (j+d) (s.shift d c)  when c ≤ j
        -- With j = |Γ₁|-1-k, s = v.shift (|Γ₁|-1-k) 0, d = k+1, c = 0:
        rw [Expr.shift_subst_comm_ge t (v.shift (Γ₁.length - 1 - k) 0)
            (k + 1) 0 (Γ₁.length - 1 - k) (Nat.zero_le _)] at hsub'
        -- Now hsub' has: (t.shift (k+1) 0).subst (|Γ₁|-1-k+(k+1)) ((v.shift (|Γ₁|-1-k) 0).shift (k+1) 0)
        rw [show Γ₁.length - 1 - k + (k + 1) = Γ₁.length from by omega] at hsub'
        -- Simplify the value: (v.shift (|Γ₁|-1-k) 0).shift (k+1) 0 = v.shift |Γ₁| 0
        rw [Expr.shift_shift] at hsub'
        rw [show Γ₁.length - 1 - k + (k + 1) = Γ₁.length from by omega] at hsub'
        exact hsub'
  | .lam (dom := dom) (dom' := dom') (body := body) (body' := body')
      hsub1 hsub2 hsub3 =>
    simp only [Expr.subst]
    apply Sub.lam
    · exact subst_sub_gen Γ₁ hsub1 hwfv hvsig
    · exact subst_sub_gen Γ₁ hsub2 hwfv hvsig
    · rw [Expr.shift_succ_zero]
      have ih := subst_sub_gen (dom :: Γ₁) hsub3 hwfv hvsig
      simp only [substPrefix_cons, List.length_cons, List.cons_append] at ih
      exact ih
  | .app_cong hf ha ha' =>
    simp only [Expr.subst]
    exact .app_cong (subst_sub_gen Γ₁ hf hwfv hvsig) (subst_sub_gen Γ₁ ha hwfv hvsig)
      (subst_sub_gen Γ₁ ha' hwfv hvsig)
  | .beta_L (dom := dom) (body := body) (arg := arg) =>
    simp only [Expr.subst]
    rw [Expr.subst_subst_comm_zero body arg (v.shift Γ₁.length 0) Γ₁.length]
    rw [Expr.shift_succ_zero]
    exact .beta_L
  | .beta_R (dom := dom) (body := body) (arg := arg) =>
    simp only [Expr.subst]
    rw [Expr.subst_subst_comm_zero body arg (v.shift Γ₁.length 0) Γ₁.length]
    rw [Expr.shift_succ_zero]
    exact .beta_R
termination_by sizeOf hsub
decreasing_by all_goals (simp_wf; omega)

/-- Generalized substitution lemma: substituting at position `j = |Γ₁|`
    in context `Γ₁ ++ σ :: Γ₂` preserves well-formedness. -/
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
      -- Weakening at position 0 with Δ = substPrefix Γ₁ v
      have h := wf_shift_gen (Γ₁ := []) (substPrefix Γ₁ v) hwfv
      simp only [shiftPrefix, List.nil_append, substPrefix_length] at h
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
    · rw [Expr.shift_succ_zero]
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
termination_by sizeOf hwfb
decreasing_by all_goals (simp_wf; omega)

end

/-- Weakening at position 0: if `Wf Γ e` then `Wf (Δ ++ Γ) (e.shift |Δ| 0)`. -/
noncomputable def wf_shift (Δ : Ctx) {Γ : Ctx} {e : Expr}
    (h : Wf Γ e) : Wf (Δ ++ Γ) (e.shift Δ.length 0) := by
  have h' := wf_shift_gen (Γ₁ := []) Δ h
  simp [shiftPrefix] at h'
  exact h'

/-! ## Top-level theorem: subst_wf (Lemma 5.4) -/

/-- Substitution preserves well-formedness (Lemma 5.4). -/
noncomputable def subst_wf {Γ : Ctx} {σ body v : Expr}
    (hwfb : Wf (σ :: Γ) body)
    (hwfv : Wf Γ v) (hvsig : Sub Γ v σ) :
    Wf Γ (body.subst 0 v) := by
  have h := subst_wf_gen [] σ Γ body v hwfb hwfv hvsig
  simp only [substPrefix, List.nil_append, List.length_nil] at h
  rw [Expr.shift_zero] at h
  exact h

end PSS
