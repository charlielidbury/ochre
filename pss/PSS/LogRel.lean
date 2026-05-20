import PSS.Syntax
import PSS.Sub
import PSS.Eval
import PSS.SubstWf
import PSS.Soundness

/-!
# Step-indexed Logical Relation for PSS Type Safety (typeNorm version)

## Motivation

All syntactic approaches to PSS type safety hit the same wall: composing
`trans(h1, beta_L, hw)` doesn't decrease any simple measure.

This file takes a **semantic** approach using step-indexed logical relations.

## Key design decision: typeNorm-based SemVal

Previous versions used `concEval` to normalize application-type positions.
This made `SubSem` FALSE for `beta_L` and `app_cong` because the concEval
fuel was tied to the step index.

The fix: use `typeNorm`, a pure syntactic beta-normalizer for types, and
define `SemVal k t v = IsVal v /\ forall n nf, typeNorm n t = some nf -> SemVal_nf k nf v`.
The normalization fuel `n` is universally quantified and decoupled from the
step index `k`, eliminating the asymmetry.

`typeNorm` is defined so that:
  `typeNorm (n+1) (app (lam d b) a) = typeNorm n (b.subst 0 a)`
using the RAW body `b`. This makes beta_L trivial.

## fundamental_subSem case status:

- refl: PROVED
- top: PROVED
- bvar: PROVED (vacuous)
- trans: PROVED
- beta_L: PROVED (was FALSE in old definition!)
- beta_R: PROVED (was sorry in old definition)
- lam: sorry (needs context generalization / closing substitution)
- app_cong: sorry (needs typeNorm congruence for Sub-related apps)
-/

open Expr

namespace PSS.LogRel

/-! ## Type normalizer -/

/-- Pure syntactic beta-normalizer for type expressions.
    Reduces syntactic beta-redexes by substituting the RAW body:
      typeNorm (n+1) (app (lam d b) a) = typeNorm n (b.subst 0 a)
    For non-redex expressions, normalizes sub-expressions.
    Returns `none` on out-of-fuel. -/
noncomputable def typeNorm : Nat → Expr → Option Expr
  | 0, _ => none
  | _ + 1, .bvar k => some (.bvar k)
  | _ + 1, .top => some .top
  | _ + 1, .lam d b => some (.lam d b)
  | n + 1, .app (.lam _d b) a => typeNorm n (b.subst 0 a)
  | n + 1, .app f a => do
    let f' ← typeNorm n f
    let a' ← typeNorm n a
    some (.app f' a')

/-- Key identity: typeNorm of a syntactic beta-redex equals typeNorm of the reductum. -/
theorem typeNorm_beta (n : Nat) (d b a : Expr) :
    typeNorm (n + 1) (.app (.lam d b) a) = typeNorm n (b.subst 0 a) := by
  simp [typeNorm]

/-- typeNorm on top. -/
@[simp] theorem typeNorm_top' (n : Nat) : typeNorm (n + 1) .top = some .top := rfl

/-- typeNorm on bvar. -/
@[simp] theorem typeNorm_bvar' (n k : Nat) : typeNorm (n + 1) (.bvar k) = some (.bvar k) := rfl

/-- If typeNorm succeeds on a lam, the result is exactly that lam. -/
theorem typeNorm_lam_eq {n : Nat} {d b : Expr}
    (h : n > 0) : typeNorm n (.lam d b) = some (.lam d b) := by
  cases n with
  | zero => omega
  | succ n => simp [typeNorm]

/-- If typeNorm succeeds on a lam, the result is always a lam. -/
theorem typeNorm_lam_shape {n : Nat} {d b nf : Expr}
    (h : typeNorm n (.lam d b) = some nf) :
    ∃ d' b', nf = .lam d' b' := by
  cases n with
  | zero => simp [typeNorm] at h
  | succ n => simp [typeNorm] at h; exact ⟨d, b, h.symm⟩

/-- typeNorm is monotone in fuel. -/
theorem typeNorm_fuel_mono {j k : Nat} {e nf : Expr}
    (hjk : j ≤ k) (hev : typeNorm j e = some nf) :
    typeNorm k e = some nf := by
  induction j generalizing k e nf with
  | zero => simp [typeNorm] at hev
  | succ n ih =>
    match k, hjk with
    | k + 1, hjk =>
    match e with
    | .bvar m => simp [typeNorm] at hev ⊢; exact hev
    | .top => simp [typeNorm] at hev ⊢; exact hev
    | .lam d b =>
      simp [typeNorm] at hev ⊢; exact hev
    | .app (.lam _d b) a =>
      simp only [typeNorm] at hev ⊢
      exact ih (show n ≤ k by omega) hev
    | .app (.bvar m) a =>
      simp only [typeNorm, Option.bind] at hev ⊢
      match hf : typeNorm n (.bvar m), ha : typeNorm n a with
      | some f', some a' =>
        simp [hf, ha] at hev
        have hf' := ih (show n ≤ k by omega) hf
        have ha' := ih (show n ≤ k by omega) ha
        simp [hf', ha']; exact hev
      | some _, none => simp [hf, ha] at hev
      | none, _ => simp [hf] at hev
    | .app .top a =>
      simp only [typeNorm, Option.bind] at hev ⊢
      match hf : typeNorm n .top, ha : typeNorm n a with
      | some f', some a' =>
        simp [hf, ha] at hev
        have hf' := ih (show n ≤ k by omega) hf
        have ha' := ih (show n ≤ k by omega) ha
        simp [hf', ha']; exact hev
      | some _, none => simp [hf, ha] at hev
      | none, _ => simp [hf] at hev
    | .app (.app f1 f2) a =>
      simp only [typeNorm, Option.bind] at hev ⊢
      match hf : typeNorm n (.app f1 f2), ha : typeNorm n a with
      | some f', some a' =>
        simp [hf, ha] at hev
        have hf' := ih (show n ≤ k by omega) hf
        have ha' := ih (show n ≤ k by omega) ha
        simp [hf', ha']; exact hev
      | some _, none => simp [hf, ha] at hev
      | none, _ => simp [hf] at hev

/-- typeNorm always succeeds on lam (with fuel >= 1). -/
theorem typeNorm_lam_total (d b : Expr) :
    ∃ n nf, typeNorm n (.lam d b) = some nf :=
  ⟨1, .lam d b, rfl⟩

/-! ## Semantic value and expression types -/

/-- A value is Top or a lambda. -/
def IsVal (v : Expr) : Prop := v = .top ∨ ∃ d b, v = .lam d b

theorem isVal_top : IsVal .top := Or.inl rfl
theorem isVal_lam (d b : Expr) : IsVal (.lam d b) := Or.inr ⟨d, b, rfl⟩

/-- Step-indexed semantic value type for normal-form types.

    The body condition for lam uses `SemVal` (not `SemVal_nf`) in the
    conclusion, via the typeNorm-based SemVal definition. This lets the
    identity extension proof go through, since the IH provides SemVal. -/
noncomputable def SemVal_nf : Nat → Expr → Expr → Prop
  | 0, _, v => IsVal v
  | _ + 1, .top, v => IsVal v
  | _ + 1, .bvar _, _ => False
  | k + 1, .lam s t, v =>
    ∃ s' t', v = .lam s' t' ∧
      ∀ j, j < k + 1 → ∀ av,
        (IsVal av ∧ ∀ n nf, typeNorm n s = some nf → SemVal_nf j nf av) →
        av.closedAt 0 = true → PSS.Wf [] av → PSS.Sub [] av s →
        ∀ i, i ≤ j → ∀ w, concEval i (t'.subst 0 av) = .ok w →
          (IsVal w ∧ ∀ n nf, typeNorm n (t.subst 0 av) = some nf → SemVal_nf (j - i) nf w)
  | _ + 1, .app _ _, v => IsVal v
termination_by k => k

/-- Step-indexed semantic value type (typeNorm version).

    `SemVal k τ v` means:
    - v is a value (IsVal v), AND
    - for all normalization fuel n and all normal forms τ_nf,
      if typeNorm n τ = some τ_nf then SemVal_nf k τ_nf v. -/
def SemVal (k : Nat) (τ : Expr) (v : Expr) : Prop :=
  IsVal v ∧ ∀ n τ_nf, typeNorm n τ = some τ_nf → SemVal_nf k τ_nf v

/-- Semantic expression type. -/
def SemExpr (k : Nat) (τ : Expr) (e : Expr) : Prop :=
  ∀ j, j ≤ k → ∀ v, concEval j e = .ok v → SemVal (k - j) τ v

/-! ## SemVal_nf basic properties -/

theorem semVal_nf_zero (τ v : Expr) : SemVal_nf 0 τ v ↔ IsVal v :=
  ⟨fun h => by unfold SemVal_nf at h; exact h,
   fun hv => by unfold SemVal_nf; exact hv⟩

theorem semVal_nf_isVal (k : Nat) (τ v : Expr) (h : SemVal_nf k τ v) : IsVal v := by
  induction k generalizing τ v with
  | zero => exact (semVal_nf_zero τ v).mp h
  | succ k _ =>
    match τ with
    | .top => unfold SemVal_nf at h; exact h
    | .bvar _ => unfold SemVal_nf at h; exact absurd h id
    | .lam _ _ =>
      unfold SemVal_nf at h
      obtain ⟨s', t', heq, _⟩ := h
      exact Or.inr ⟨s', t', heq⟩
    | .app _ _ => unfold SemVal_nf at h; exact h

theorem semVal_nf_top (k : Nat) (v : Expr) (hv : IsVal v) : SemVal_nf k .top v := by
  cases k with
  | zero => exact (semVal_nf_zero .top v).mpr hv
  | succ k => unfold SemVal_nf; exact hv

theorem top_not_in_semVal_nf_lam (k : Nat) (s t : Expr) :
    ¬ SemVal_nf (k + 1) (.lam s t) .top := by
  unfold SemVal_nf; intro ⟨_, _, h, _⟩; cases h

theorem semVal_nf_lam_is_lam {k : Nat} {s t v : Expr}
    (h : SemVal_nf (k + 1) (.lam s t) v) : ∃ d b, v = .lam d b := by
  unfold SemVal_nf at h; exact let ⟨s', t', heq, _⟩ := h; ⟨s', t', heq⟩

/-- SemVal_nf is anti-monotone in the step index. -/
theorem semVal_nf_antimono : ∀ (j k : Nat) (τ v : Expr),
    j ≤ k → SemVal_nf k τ v → SemVal_nf j τ v := by
  intro j
  induction j with
  | zero =>
    intro k τ v _ h; exact (semVal_nf_zero τ v).mpr (semVal_nf_isVal k τ v h)
  | succ j ih =>
    intro k τ v hjk h
    match k, hjk with
    | k + 1, hjk =>
    match τ with
    | .top => unfold SemVal_nf at h ⊢; exact h
    | .bvar _ => unfold SemVal_nf at h; exact absurd h id
    | .lam s t =>
      unfold SemVal_nf at h ⊢
      obtain ⟨s', t', heq, hbody⟩ := h
      refine ⟨s', t', heq, fun j' hj' av hav hcl hwf hsub i hi w hw => ?_⟩
      have := hbody j' (by omega) av
      -- hav gives SemVal j' s av. But the body expects the same shape at k+1 level.
      -- Since j' < j + 1 ≤ k + 1, we can use hav directly since the quantification is at j'.
      -- The av condition is: IsVal av ∧ ∀ n nf, typeNorm n s = some nf → SemVal_nf j' nf av
      -- The body at k+1 expects the same at j' (which is < k+1).
      -- So hav works directly.
      exact this hav hcl hwf hsub i hi w hw
    | .app _ _ => unfold SemVal_nf at h ⊢; exact h

/-! ## SemVal basic properties -/

theorem semVal_top (k : Nat) (v : Expr) (hv : IsVal v) : SemVal k .top v :=
  ⟨hv, fun n τ_nf hn => by
    cases n with
    | zero => simp [typeNorm] at hn
    | succ n => simp [typeNorm] at hn; subst hn; exact semVal_nf_top k v hv⟩

theorem semVal_isVal (k : Nat) (τ v : Expr) (h : SemVal k τ v) : IsVal v := h.1

theorem semVal_zero_iff (τ v : Expr) : SemVal 0 τ v ↔ IsVal v :=
  ⟨fun h => h.1,
   fun hv => ⟨hv, fun _ _ _ => (semVal_nf_zero _ v).mpr hv⟩⟩

/-! ## Semantic Canonical Forms -/

/-- Top is not in SemVal (k+1) (lam s t), if lam s t normalizes. -/
theorem top_not_in_semVal_lam (k : Nat) (s t : Expr)
    (hnorm : ∃ n nf, typeNorm n (.lam s t) = some nf) :
    ¬ SemVal (k + 1) (.lam s t) .top := by
  intro ⟨_, h_all⟩
  obtain ⟨n, nf, hn⟩ := hnorm
  obtain ⟨s', t', heq⟩ := typeNorm_lam_shape hn
  subst heq
  exact top_not_in_semVal_nf_lam k s' t' (h_all n (.lam s' t') hn)

/-- Values in SemVal (k+1) (lam s t) are lambdas, if lam s t normalizes. -/
theorem semVal_lam_is_lam {k : Nat} {s t v : Expr}
    (hnorm : ∃ n nf, typeNorm n (.lam s t) = some nf)
    (h : SemVal (k + 1) (.lam s t) v) : ∃ d b, v = .lam d b := by
  obtain ⟨_, h_all⟩ := h
  obtain ⟨n, nf, hn⟩ := hnorm
  obtain ⟨s', t', heq⟩ := typeNorm_lam_shape hn
  subst heq
  exact semVal_nf_lam_is_lam (h_all n (.lam s' t') hn)

/-! ## concEval fuel monotonicity -/

theorem concEval_fuel_mono {j k : Nat} {e v : Expr}
    (hjk : j ≤ k) (hev : concEval j e = .ok v) :
    concEval k e = .ok v := by
  induction j generalizing k e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    match k, hjk with
    | k + 1, hjk =>
    unfold concEval at hev ⊢
    split at hev
    · cases hev
    · cases hev; rfl
    · cases hev; rfl
    · rename_i f a
      split at hev
      · rename_i fv av hf ha
        have hf' := ih (show n ≤ k by omega) hf
        have ha' := ih (show n ≤ k by omega) ha
        simp [hf', ha']
        split at hev
        · exact ih (show n ≤ k by omega) hev
        · cases hev
      · simp at hev
      · simp at hev
      · simp at hev
      · simp at hev

/-! ## Anti-monotonicity of SemVal -/

theorem semVal_antimono (j k : Nat) (τ v : Expr)
    (hjk : j ≤ k) (h : SemVal k τ v) : SemVal j τ v :=
  ⟨h.1, fun n τ_nf hn => semVal_nf_antimono j k τ_nf v hjk (h.2 n τ_nf hn)⟩

/-! ## Semantic subtyping -/

def SubSem (a b : Expr) : Prop :=
  ∀ k v, SemVal k a v → SemVal k b v

theorem subSem_trans {a b c : Expr} (h1 : SubSem a b) (h2 : SubSem b c) :
    SubSem a c :=
  fun k v hv => h2 k v (h1 k v hv)

theorem subSem_refl (a : Expr) : SubSem a a :=
  fun _ _ hv => hv

theorem subSem_top (a : Expr) : SubSem a .top :=
  fun k v hv => semVal_top k v hv.1

theorem subSem_top_not_lam {s t : Expr}
    (hnorm : ∃ n nf, typeNorm n (.lam s t) = some nf)
    (h : SubSem .top (.lam s t)) : False :=
  top_not_in_semVal_lam 0 s t hnorm (h 1 .top (semVal_top 1 .top isVal_top))

/-! ## Values evaluate to themselves -/

theorem concEval_val (fuel : Nat) (v : Expr) (hv : IsVal v) (hfuel : fuel > 0) :
    concEval fuel v = .ok v := by
  rcases hv with rfl | ⟨d, b, rfl⟩
  · cases fuel with | zero => omega | succ n => simp [concEval]
  · cases fuel with | zero => omega | succ n => simp [concEval]

/-! ## concEval only produces values -/

private theorem concEval_isValue' {fuel : Nat} {e v : Expr}
    (hev : concEval fuel e = .ok v) :
    v = .top ∨ ∃ d b, v = .lam d b := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · exact absurd hev (by intro h; cases h)
    · cases hev; left; rfl
    · cases hev; right; exact ⟨_, _, rfl⟩
    · split at hev
      · rename_i fv av hf ha; split at hev
        · exact ih hev
        · cases hev
      · cases hev
      · cases hev
      · cases hev
      · cases hev

/-! ## Semantic expression type for Top -/

theorem semExpr_top (k : Nat) (e : Expr) : SemExpr k .top e := by
  intro j hj v hev
  have hv := concEval_isValue' hev
  rcases hv with rfl | ⟨d, b, rfl⟩
  · exact semVal_top (k - j) .top isVal_top
  · exact semVal_top (k - j) (.lam d b) (isVal_lam d b)

/-! ## SubSem for beta_L and beta_R -/

/-- beta_L: SubSem (app (lam dom body) arg) (body.subst 0 arg).
    Proof: typeNorm_beta gives typeNorm (n+1) (app (lam d b) a) = typeNorm n (b.subst 0 a).
    Any normalization of the reductum at fuel n lifts to the redex at fuel n+1. -/
theorem subSem_beta_L {dom body arg : Expr} :
    SubSem (.app (.lam dom body) arg) (body.subst 0 arg) := by
  intro k v ⟨hval, h_all⟩
  refine ⟨hval, fun n τ_nf hn => ?_⟩
  have : typeNorm (n + 1) (.app (.lam dom body) arg) = some τ_nf := by
    rw [typeNorm_beta]; exact hn
  exact h_all (n + 1) τ_nf this

/-- beta_R: SubSem (body.subst 0 arg) (app (lam dom body) arg).
    Proof: reverse of beta_L — any normalization of the redex at fuel n+1
    yields normalization of the reductum at fuel n. -/
theorem subSem_beta_R {dom body arg : Expr} :
    SubSem (body.subst 0 arg) (.app (.lam dom body) arg) := by
  intro k v ⟨hval, h_all⟩
  refine ⟨hval, fun n τ_nf hn => ?_⟩
  cases n with
  | zero => simp [typeNorm] at hn
  | succ n =>
    rw [typeNorm_beta] at hn
    exact h_all n τ_nf hn

/-! ## Self-typing (identity extension) -/

private noncomputable def semExpr_refl_aux : (k : Nat) → (e : Expr) →
    e.closedAt 0 = true → PSS.Wf [] e → SemExpr k e e := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih_k =>
    intro e hcl hwf j hj v hev
    have hcl_v := concEval_closedAt hcl hev
    have hval_v := concEval_isValue' hev
    have hwf_v := (concEval_combined j e hcl hwf).props v hev |>.2.2
    have hval : IsVal v := by
      rcases hval_v with rfl | ⟨d', b', rfl⟩
      · exact isVal_top
      · exact isVal_lam _ _
    match e, hcl, hwf, hev with
    | .top, _, _, hev =>
      cases j with
      | zero => simp [concEval] at hev
      | succ n => simp [concEval] at hev; subst hev; exact semVal_top _ .top isVal_top
    | .lam d b, hcl, hwf, hev =>
      cases j with
      | zero => simp [concEval] at hev
      | succ n =>
        simp [concEval] at hev; subst hev
        -- Need: SemVal (k - (n+1)) (lam d b) (lam d b)
        refine ⟨isVal_lam d b, fun m nf hm => ?_⟩
        -- typeNorm m (lam d b) = some (lam d b) by typeNorm_lam_eq
        -- So nf = lam d b
        have hm_pos : m > 0 := by
          cases m with | zero => simp [typeNorm] at hm | succ _ => omega
        rw [typeNorm_lam_eq hm_pos] at hm
        cases hm  -- nf = lam d b
        cases hkn : k - (n + 1) with
        | zero => exact (semVal_nf_zero (.lam d b) (.lam d b)).mpr (isVal_lam d b)
        | succ m' =>
          unfold SemVal_nf
          -- Now type = lam d b, value = lam d b, so s = d, t = b, s' = d, t' = b.
          -- Body condition: concEval i (b.subst 0 av) = ok w → SemVal (j'-i) (b.subst 0 av) w
          -- This is EXACTLY what the IH gives us!
          refine ⟨d, b, rfl, fun j' hj' av hav hcl_av hwf_av hsub_av i hi w hw => ?_⟩
          -- j' < m' + 1 ≤ k - (n+1) ≤ k, so j' < k. Use IH.
          have hwf_db : PSS.Wf [d] b := match hwf with | .lam _ hb => hb
          have hwf_subst := PSS.subst_wf hwf_db hwf_av hsub_av
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          have hcl_subst := Expr.subst_closedAt_zero hcl.2 hcl_av
          exact ih_k j' (by omega) (b.subst 0 av) hcl_subst hwf_subst i hi w hw
    | .app f a, hcl, _, hev =>
      have hj_pos : j ≥ 1 := by
        cases j with | zero => simp [concEval] at hev | succ n => omega
      refine ⟨hval, fun m nf hm => ?_⟩
      -- typeNorm m (app f a) = some nf. Need SemVal_nf (k-j) nf v.
      -- v is the concEval result of (app f a).
      -- By IH at smaller k: v is self-typed (SemVal k' v v for k' < k).
      -- But we need v in nf, not in v.
      -- The relationship: nf is what (app f a) normalizes to as a TYPE,
      -- and v is what (app f a) evaluates to as a TERM.
      -- For well-formed closed terms, typeNorm and concEval should agree...
      -- But proving this is substantial. Sorry for now.
      cases hkj : k - j with
      | zero => exact (semVal_nf_zero nf v).mpr hval
      | succ m' => sorry

private noncomputable def semVal_self (k : Nat) (v : Expr)
    (hcl : v.closedAt 0 = true) (hwf : PSS.Wf [] v) (hval : IsVal v) :
    SemVal k v v := by
  cases k with
  | zero => exact (semVal_zero_iff v v).mpr hval
  | succ n =>
    have hev := concEval_val 1 v hval (by omega)
    have h := semExpr_refl_aux (n + 2) v hcl hwf 1 (by omega) v hev
    simp only [show n + 2 - 1 = n + 1 from by omega] at h
    exact h

noncomputable def semExpr_refl (k : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    SemExpr k e e :=
  semExpr_refl_aux k e hcl hwf

/-! ## Wf implies closedness -/

noncomputable def wf_closedAt {Γ : Ctx} {e : Expr} (h : PSS.Wf Γ e) :
    e.closedAt Γ.length = true :=
  match h with
  | .var hk => by simp only [Expr.closedAt, decide_eq_true_eq]; exact hk
  | .top => rfl
  | .lam hd hb => by
    simp only [Expr.closedAt, Bool.and_eq_true, List.length_cons]
    exact ⟨wf_closedAt hd, wf_closedAt hb⟩
  | .app hf ha _ _ _ => by
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨wf_closedAt hf, wf_closedAt ha⟩

theorem wf_closed {e : Expr} (h : PSS.Wf [] e) : e.closedAt 0 = true :=
  wf_closedAt h

/-! ## The fundamental theorem -/

theorem fundamental_top' (k : Nat) (e : Expr) :
    SemExpr k .top e := semExpr_top k e

theorem fundamental_trans {k : Nat} {e m τ : Expr}
    (h1 : SemExpr k m e) (h2 : SubSem m τ) :
    SemExpr k τ e :=
  fun j hj v hev => h2 (k - j) v (h1 j hj v hev)

/-! ### Semantic soundness of Sub -/

noncomputable def fundamental_subSem {e τ : Expr} (hsub : PSS.Sub [] e τ) :
    SubSem e τ :=
  match hsub with
  | .refl _ => subSem_refl _
  | .top _ => subSem_top _
  | .trans h1 h2 hw => subSem_trans (fundamental_subSem h1) (fundamental_subSem h2)
  | .bvar hget => absurd hget (by simp [List.get?])
  | .lam _ _ _ => sorry  -- needs context generalization
  | .app_cong _ _ _ => sorry  -- needs typeNorm congruence for Sub-related apps
  | .beta_L => subSem_beta_L
  | .beta_R => subSem_beta_R

noncomputable def fundamental_closed (e τ : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) (hsub : PSS.Sub [] e τ) :
    ∀ k, SemExpr k τ e :=
  fun k => fundamental_trans (semExpr_refl k e hcl hwf) (fundamental_subSem hsub)

/-! ## Type safety -/

noncomputable def concEval_safe (k : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    ∀ msg, concEval k e ≠ .error msg := by
  induction k generalizing e with
  | zero => simp [concEval]
  | succ n ih =>
    match e, hcl, hwf with
    | .bvar _, hcl, _ =>
      simp [Expr.closedAt, decide_eq_true_eq] at hcl
    | .top, _, _ => simp [concEval]
    | .lam _ _, _, _ => simp [concEval]
    | .app f a, hcl, hwf =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      match hwf with
      | .app (s := s) hwf_f hwf_a _hwf_s hsub_f_lam _hsub_a_s =>
        intro msg herr
        have hf_ne := ih f hcl.1 hwf_f
        have ha_ne := ih a hcl.2 hwf_a
        match hf_eq : concEval n f with
        | .error m => exact absurd hf_eq (hf_ne m)
        | .outOfFuel => simp [concEval, hf_eq] at herr
        | .ok fv =>
          match ha_eq : concEval n a with
          | .error m => exact absurd ha_eq (ha_ne m)
          | .outOfFuel => simp [concEval, hf_eq, ha_eq] at herr
          | .ok av =>
            simp [concEval, hf_eq, ha_eq] at herr
            -- Canonical forms: fv must be a lambda (not Top)
            -- We need typeNorm (lam s top) to succeed.
            -- s is well-formed, so it's a finite term. typeNorm succeeds on finite terms.
            -- For lam s top: we need typeNorm to succeed on s and on top.
            -- top is trivial. s requires typeNorm_total which we don't have in full generality.
            -- But the canonical forms argument can be done via the SYNTACTIC approach
            -- from Soundness.lean instead, which doesn't need typeNorm.
            -- Actually, fundamental_closed uses semExpr_refl which has sorrys.
            -- The semantic canonical forms need typeNorm normalization.
            -- Let's use the direct syntactic approach:
            -- From concEval_combined, fv ≤ f and f ≤ lam s top, so fv ≤ lam s top.
            -- By top_not_sub_lam (axiom), fv ≠ top.
            -- By concEval_isValue, fv is top or a lam. Since not top, it's a lam.
            have fv_data := (concEval_combined n f hcl.1 hwf_f).props fv hf_eq
            have hfv_sub_lam : PSS.Sub [] fv (.lam s .top) :=
              .trans fv_data.1 hsub_f_lam hwf_f
            have fv_not_top : fv ≠ .top := by
              intro heq; subst heq
              exact PSS.top_not_sub_lam hfv_sub_lam
            have hfv_val := concEval_isValue (hev := hf_eq)
            rcases hfv_val with rfl | ⟨d, b, rfl⟩
            · exact absurd rfl fv_not_top
            · -- fv = lam d b
              have av_data := (concEval_combined n a hcl.2 hwf_a).props av ha_eq
              have inv := PSS.lam_sub_lam_inversion hfv_sub_lam
              have hav_sub_d : PSS.Sub [] av d :=
                .trans (.trans av_data.1 _hsub_a_s hwf_a) inv.2 _hwf_s
              have hwf_body : PSS.Wf [d] b := match fv_data.2.2 with | .lam _ hb => hb
              have hwf_subst : PSS.Wf [] (b.subst 0 av) :=
                PSS.subst_wf hwf_body av_data.2.2 hav_sub_d
              have hcl_subst : (b.subst 0 av).closedAt 0 = true := by
                have hfcl := concEval_closedAt hcl.1 hf_eq
                have hacl := concEval_closedAt hcl.2 ha_eq
                simp only [Expr.closedAt, Bool.and_eq_true] at hfcl
                exact Expr.subst_closedAt_zero hfcl.2 hacl
              exact ih (b.subst 0 av) hcl_subst hwf_subst msg herr

/-! ## Summary

### fundamental_subSem cases:

| Case | Status |
|------|--------|
| `refl` | PROVED |
| `top` | PROVED |
| `bvar` | PROVED (vacuous) |
| `trans` | PROVED |
| `beta_L` | **PROVED** (was FALSE in old concEval-based definition!) |
| `beta_R` | **PROVED** (was sorry in old definition) |
| `lam` | sorry (needs context generalization) |
| `app_cong` | sorry (needs typeNorm congruence for Sub-related apps) |

### Remaining sorrys (3 total):

1. `semExpr_refl_aux` app case: needs typeNorm/concEval agreement for well-typed terms.
   When concEval j (app f a) = ok v and typeNorm m (app f a) = some nf, we need
   SemVal_nf (k-j) nf v. This requires relating the value-level evaluation result
   to the type-level normalization result. typeNorm does raw substitution while
   concEval does CBV evaluation, so they diverge when arguments are non-values.

2. `fundamental_subSem` lam case: needs context generalization (same as old definition).
   The body sub-judgment Sub [dom] body body' needs a generalized fundamental theorem
   with closing substitution environments to break the structural recursion circularity.

3. `fundamental_subSem` app_cong case: needs typeNorm congruence for Sub-related apps.
   Given Sub [] f f' and Sub [] a a', need to relate typeNorm(app f a) to typeNorm(app f' a').

### Key insight: typeNorm_beta

The property `typeNorm (n+1) (app (lam d b) a) = typeNorm n (b.subst 0 a)` is
definitional (holds by `rfl` after unfolding). This makes beta_L and beta_R trivial:
- beta_L: normalization at fuel n of reductum lifts to fuel n+1 of redex
- beta_R: normalization at fuel n+1 of redex yields fuel n of reductum

This fixes the fundamental flaw in the old concEval-based SemVal, where beta_L
and app_cong were provably FALSE due to the fuel-asymmetry between redex and reductum.

### concEval_safe

Type safety is proved WITHOUT using the semantic canonical forms at all.
Instead, it uses the SYNTACTIC canonical forms (top_not_sub_lam axiom from
Soundness.lean) directly. This means the sorrys in semExpr_refl don't affect
the type safety proof.
-/

end PSS.LogRel
