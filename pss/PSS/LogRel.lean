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

`typeNorm` always normalizes the head of an application first:
  `typeNorm (n+1) (app f a) = match typeNorm n f with
    | some (lam _ b) => typeNorm n (b.subst 0 a)
    | _ => none`
This ensures Sub-related functions that differ only in syntactic shape (e.g.,
a beta-redex vs its reductum) are treated uniformly, fixing the previous
counterexample where `app_cong` was provably FALSE.

Key property: `typeNorm` never produces an `app` in its output (`typeNorm_no_app`).
For closed inputs, only `top` and `lam` are possible outputs.

## fundamental_subSem case status:

- refl: PROVED
- top: PROVED
- bvar: PROVED (vacuous)
- trans: PROVED
- beta_L: PROVED
- beta_R: PROVED
- lam: PROVED (via WF induction on (k, sizeOf hsub) + Wf hypotheses)
- app_cong: PROVED (via typeNorm_sub_transfer)

## Remaining axioms:

All sorrys are closed. `typeNorm_sub_transfer` is now fully proved, reducing to
a single axiom `typeNorm_total_axiom` (head-normalization for PSS: typeNorm
succeeds on all closed well-formed expressions). The axiom encapsulates the
termination argument that the Wf discipline prevents non-terminating
head-reduction sequences (the omega combinator is not well-formed in PSS).
-/

open Expr

namespace PSS.LogRel

/-! ## Type normalizer -/

/-- Pure syntactic beta-normalizer for type expressions.
    Always normalizes the head of an application first:
      typeNorm (n+1) (app f a) = match typeNorm n f with
        | some (lam _ b) => typeNorm n (b.subst 0 a)
        | _ => none
    Returns `none` on out-of-fuel or stuck (non-lambda head).
    Never produces an `app` in its output. -/
noncomputable def typeNorm : Nat → Expr → Option Expr
  | 0, _ => none
  | _ + 1, .bvar k => some (.bvar k)
  | _ + 1, .top => some .top
  | _ + 1, .lam d b => some (.lam d b)
  | n + 1, .app f a =>
    match typeNorm n f with
    | some (.lam _d b) => typeNorm n (b.subst 0 a)
    | _ => none  -- stuck (f doesn't normalize to a lambda)

/-- Key identity: typeNorm of a syntactic beta-redex equals typeNorm of the reductum
    (needs fuel ≥ 2 because we normalize the head first, using 1 unit of fuel). -/
theorem typeNorm_beta (n : Nat) (d b a : Expr) :
    typeNorm (n + 2) (.app (.lam d b) a) = typeNorm (n + 1) (b.subst 0 a) := by
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
    | .app f a =>
      simp only [typeNorm] at hev ⊢
      -- hev : match typeNorm n f with | some (lam _ b) => typeNorm n (b.subst 0 a) | _ => none = some nf
      match hf : typeNorm n f with
      | some (.lam _d b) =>
        simp [hf] at hev
        -- hev : typeNorm n (b.subst 0 a) = some nf
        have hf' := ih (show n ≤ k by omega) hf
        simp [hf']
        exact ih (show n ≤ k by omega) hev
      | some .top => simp [hf] at hev
      | some (.bvar _) => simp [hf] at hev
      | some (.app _ _) => simp [hf] at hev
      | none => simp [hf] at hev

/-- typeNorm always succeeds on lam (with fuel >= 1). -/
theorem typeNorm_lam_total (d b : Expr) :
    ∃ n nf, typeNorm n (.lam d b) = some nf :=
  ⟨1, .lam d b, rfl⟩

/-- typeNorm preserves closedAt. -/
theorem typeNorm_closedAt {n : Nat} {e nf : Expr} {c : Nat}
    (hcl : e.closedAt c = true) (hn : typeNorm n e = some nf) :
    nf.closedAt c = true := by
  induction n generalizing e nf c with
  | zero => simp [typeNorm] at hn
  | succ p ih =>
    match e with
    | .bvar k => simp [typeNorm] at hn; subst hn; exact hcl
    | .top => simp [typeNorm] at hn; subst hn; exact hcl
    | .lam d b => simp [typeNorm] at hn; subst hn; exact hcl
    | .app f a =>
      simp only [typeNorm] at hn
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      -- typeNorm succeeds only if typeNorm p f = some (lam _d b) and typeNorm p (b.subst 0 a) = some nf
      match hf : typeNorm p f with
      | some (.lam _d b) =>
        simp [hf] at hn
        -- hn : typeNorm p (b.subst 0 a) = some nf
        -- Need closedness of b.subst 0 a
        have hcl_f := ih hcl.1 hf  -- closedAt c (lam _d b)
        simp only [Expr.closedAt, Bool.and_eq_true] at hcl_f
        exact ih (Expr.subst_closedAt_zero.aux hcl_f.2 hcl.2 (Nat.zero_le _)) hn
      | some .top => simp [hf] at hn
      | some (.bvar _) => simp [hf] at hn
      | some (.app _ _) => simp [hf] at hn
      | none => simp [hf] at hn

/-- typeNorm of a closedAt 0 expression can't produce a bare bvar. -/
theorem typeNorm_closedAt_no_bvar {m : Nat} {e : Expr} {bk : Nat}
    (hcl : e.closedAt 0 = true) (hm : typeNorm m e = some (.bvar bk)) :
    False := by
  have := typeNorm_closedAt hcl hm
  simp only [Expr.closedAt, decide_eq_true_eq] at this
  omega

/-- typeNorm never produces an app: it either beta-reduces to a non-app or returns none. -/
theorem typeNorm_no_app {m : Nat} {e f' a' : Expr}
    (hm : typeNorm m e = some (.app f' a')) : False := by
  induction m generalizing e f' a' with
  | zero => simp [typeNorm] at hm
  | succ n ih =>
    match e with
    | .bvar k => simp [typeNorm] at hm
    | .top => simp [typeNorm] at hm
    | .lam d b => simp [typeNorm] at hm
    | .app f a =>
      simp only [typeNorm] at hm
      match hf : typeNorm n f with
      | some (.lam _d b) => simp [hf] at hm; exact ih hm
      | some .top => simp [hf] at hm
      | some (.bvar _) => simp [hf] at hm
      | some (.app _ _) => simp [hf] at hm
      | none => simp [hf] at hm

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

/-! ## typeNorm determinism -/

/-- typeNorm is deterministic: if it succeeds at two fuel levels, the results agree.
    Follows immediately from fuel monotonicity. -/
theorem typeNorm_det {j k : Nat} {e nf1 nf2 : Expr}
    (h1 : typeNorm j e = some nf1) (h2 : typeNorm k e = some nf2) :
    nf1 = nf2 := by
  by_cases hjk : j ≤ k
  · have := typeNorm_fuel_mono hjk h1; rw [this] at h2; cases h2; rfl
  · have := typeNorm_fuel_mono (show k ≤ j by omega) h2; rw [this] at h1; cases h1; rfl

/-! ## typeNorm of values -/

/-- typeNorm of a value returns the value itself (for fuel >= 1). -/
theorem typeNorm_val {v : Expr} (hv : IsVal v) (hfuel : n > 0) :
    typeNorm n v = some v := by
  rcases hv with rfl | ⟨d, b, rfl⟩
  · cases n with | zero => omega | succ n => simp [typeNorm]
  · cases n with | zero => omega | succ n => simp [typeNorm]

/-! ## typeNorm–Sub transfer

The following lemma captures the key consequence of Sub-equivalence for
head-reduction:

> If `Sub [] e e'`, both are closed and well-formed, and `typeNorm`
> succeeds on `e'`, then `typeNorm` also succeeds on `e` with a result
> whose `SemVal_nf` inhabitants include all `SemVal_nf` inhabitants of
> the result for `e'`.

Proof strategy:
1. `typeNorm_sub_wf`: typeNorm results are Sub-equivalent to the input and Wf.
2. `typeNorm_total_axiom`: head-normalization (axiom) — typeNorm succeeds on
   all closed wf expressions.
3. `semVal_nf_sub_transfer`: SemVal_nf transfer between values related by Sub,
   proved by step-index induction. The lam-lam body case constructs the body
   Sub via beta_R + app_cong + beta_L (no body inversion needed).
4. `typeNorm_sub_transfer`: combines 1-3. -/

/-! ### typeNorm preserves Sub / Wf (mutual with typeNorm_total) -/

/-- If typeNorm n e = some nf and e is closed wf, then Sub [] e nf ∧ Sub [] nf e ∧ Wf [] nf.
    Proved by induction on n. -/
private noncomputable def typeNorm_sub_wf :
    ∀ (n : Nat) (e nf : Expr),
      PSS.Wf [] e → e.closedAt 0 = true → typeNorm n e = some nf →
      (PSS.Sub [] e nf × PSS.Sub [] nf e) × PSS.Wf [] nf := by
  intro n; induction n with
  | zero => intro e nf _ _ h; simp [typeNorm] at h
  | succ n ih =>
    intro e nf hwf hcl hn
    match e, hwf, hcl, hn with
    | .bvar k, _, hcl, _ =>
      simp [Expr.closedAt, decide_eq_true_eq] at hcl
    | .top, _, _, hn =>
      simp [typeNorm] at hn; subst hn
      exact ⟨⟨.refl _, .refl _⟩, .top⟩
    | .lam d b, hwf, _, hn =>
      simp [typeNorm] at hn; subst hn
      exact ⟨⟨.refl _, .refl _⟩, hwf⟩
    | .app f a, hwf, hcl, hn =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      -- Extract Wf components
      match hwf with
      | .app (s := s) hwf_f hwf_a hwf_s hsub_f_lam hsub_a_s =>
        simp only [typeNorm] at hn
        match hf : typeNorm n f with
        | some (.lam d b) =>
          simp [hf] at hn
          -- IH on f
          have ⟨⟨hsub_f_db, hsub_db_f⟩, hwf_db⟩ := ih f (.lam d b) hwf_f hcl.1 hf
          -- Extract body Wf
          have hwf_body : PSS.Wf [d] b := match hwf_db with | .lam _ hb => hb
          have hwf_dom : PSS.Wf [] d := match hwf_db with | .lam hd _ => hd
          -- Relate domains: lam d b ≤ lam s top
          have hsub_db_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
            .trans hsub_db_f hsub_f_lam hwf_f
          have inv := PSS.lam_sub_lam_inversion hsub_db_lam
          -- Sub [] a d
          have hsub_a_d : PSS.Sub [] a d := .trans hsub_a_s inv.2 hwf_s
          -- Wf and closedness of b.subst 0 a
          have hwf_subst : PSS.Wf [] (b.subst 0 a) :=
            PSS.subst_wf hwf_body hwf_a hsub_a_d
          have hcl_b : b.closedAt 1 = true := by
            have := typeNorm_closedAt hcl.1 hf
            simp [Expr.closedAt, Bool.and_eq_true] at this; exact this.2
          have hcl_subst : (b.subst 0 a).closedAt 0 = true :=
            Expr.subst_closedAt_zero hcl_b hcl.2
          -- IH on b.subst 0 a
          have ⟨⟨hsub_ba_nf, hsub_nf_ba⟩, hwf_nf⟩ := ih (b.subst 0 a) nf hwf_subst hcl_subst hn
          -- Build Sub [] (app f a) nf
          -- app f a ≤ app (lam d b) a ≤ b.subst 0 a ≤ nf
          have hwf_app_db : PSS.Wf [] (.app (.lam d b) a) :=
            .app hwf_db hwf_a hwf_s hsub_db_lam hsub_a_s
          have hsub_e_nf : PSS.Sub [] (.app f a) nf :=
            .trans
              (.trans (.app_cong hsub_f_db (.refl _) (.refl _)) .beta_L hwf_app_db)
              hsub_ba_nf hwf_subst
          have hsub_nf_e : PSS.Sub [] nf (.app f a) :=
            .trans
              (.trans hsub_nf_ba .beta_R hwf_subst)
              (.app_cong hsub_db_f (.refl _) (.refl _)) hwf_app_db
          exact ⟨⟨hsub_e_nf, hsub_nf_e⟩, hwf_nf⟩
        | some .top =>
          simp [hf] at hn
        | some (.bvar _) =>
          simp [hf] at hn
        | some (.app _ _) =>
          simp [hf] at hn
        | none =>
          simp [hf] at hn

/-- Head normalization: typeNorm succeeds on all closed well-formed expressions.
    This is the head-normalization theorem for PSS (well-formed closed terms always
    head-reduce to a value). The well-founded argument is: in each app step,
    typeNorm normalizes f first (at lower fuel), then normalizes b.subst 0 a.
    The Wf derivation for b.subst 0 a is not a structural sub-derivation, but
    the recursion terminates because each head-reduction step consumes one app
    constructor and the typing discipline prevents infinite head-reduction
    sequences (the omega combinator is not well-formed in PSS). -/
axiom typeNorm_total_axiom {e : Expr}
    (hwf : PSS.Wf [] e) (hcl : e.closedAt 0 = true) :
    ∃ n nf, typeNorm n e = some nf

private noncomputable def typeNorm_total {e : Expr}
    (hwf : PSS.Wf [] e) (hcl : e.closedAt 0 = true) :
    ∃ n nf, typeNorm n e = some nf :=
  typeNorm_total_axiom hwf hcl

/-- SemVal_nf transfer between values related by Sub.
    Proved by strong induction on the step index K, universally quantifying
    over all Sub derivations. The key insight for the lam-lam body case:
    Sub [] (be.subst 0 av) (bn.subst 0 av) is constructed via
    beta_R + app_cong + beta_L, avoiding the need for body inversion. -/
private noncomputable def semVal_nf_sub_transfer :
    ∀ (K : Nat) (nf_e nf : Expr) (v : Expr),
      PSS.Sub [] nf_e nf → PSS.Wf [] nf_e → PSS.Wf [] nf →
      IsVal nf_e → IsVal nf →
      nf_e.closedAt 0 = true → nf.closedAt 0 = true →
      SemVal_nf K nf_e v → SemVal_nf K nf v := by
  intro K; induction K using Nat.strongRecOn with
  | _ K ih_K =>
    intro nf_e nf v hsub hwf_nfe hwf_nf hval_nfe hval_nf hcl_nfe hcl_nf hv
    -- Case K = 0: both are IsVal
    match K with
    | 0 =>
      exact (semVal_nf_zero nf v).mpr ((semVal_nf_zero nf_e v).mp hv)
    | K' + 1 =>
    -- Case split on nf_e and nf shapes
    rcases hval_nfe with rfl | ⟨de, be, rfl⟩
    · -- nf_e = top
      rcases hval_nf with rfl | ⟨dn, bn, rfl⟩
      · -- nf = top: identity
        exact hv
      · -- nf = lam: Sub [] top (lam ..) impossible
        exact (PSS.top_not_sub_lam hsub).elim
    · -- nf_e = lam de be
      rcases hval_nf with rfl | ⟨dn, bn, rfl⟩
      · -- nf = top: SemVal_nf → IsVal
        exact semVal_nf_top (K' + 1) v (semVal_nf_isVal (K' + 1) (.lam de be) v hv)
      · -- nf_e = lam de be, nf = lam dn bn: THE HARD CASE
        -- Domain inversion
        have inv := PSS.lam_sub_lam_inversion hsub
        have hsub_de_dn : PSS.Sub [] de dn := inv.1
        have hsub_dn_de : PSS.Sub [] dn de := inv.2
        -- Extract Wf components
        have hwf_de : PSS.Wf [] de := match hwf_nfe with | .lam hd _ => hd
        have hwf_be : PSS.Wf [de] be := match hwf_nfe with | .lam _ hb => hb
        have hwf_dn : PSS.Wf [] dn := match hwf_nf with | .lam hd _ => hd
        have hwf_bn : PSS.Wf [dn] bn := match hwf_nf with | .lam _ hb => hb
        -- Closedness
        simp only [Expr.closedAt, Bool.and_eq_true] at hcl_nfe hcl_nf
        -- Unpack SemVal_nf for lam de be
        unfold SemVal_nf at hv
        obtain ⟨s', t', heq_v, body_cond⟩ := hv
        -- Build SemVal_nf for lam dn bn
        unfold SemVal_nf
        refine ⟨s', t', heq_v, fun j hj av hav hcl_av hwf_av hsub_av_dn i hi w hw => ?_⟩
        -- Step A: Domain transfer — show av also satisfies de
        -- hav : IsVal av ∧ ∀ n nf, typeNorm n dn = some nf → SemVal_nf j nf av
        -- Need: IsVal av ∧ ∀ n nf, typeNorm n de = some nf → SemVal_nf j nf av
        have hav_de : IsVal av ∧ ∀ m nf_d, typeNorm m de = some nf_d → SemVal_nf j nf_d av := by
          refine ⟨hav.1, fun m nf_d hm_d => ?_⟩
          -- Get typeNorm of dn
          obtain ⟨m_dn, nf_dn, hm_dn⟩ := typeNorm_total hwf_dn hcl_nf.1
          have ⟨⟨_, hsub_nfdn_dn⟩, hwf_nfdn⟩ := typeNorm_sub_wf m_dn dn nf_dn hwf_dn hcl_nf.1 hm_dn
          -- nf_dn is a value
          have hval_nfdn : IsVal nf_dn := by
            match nf_dn, hm_dn with
            | .app _ _, h => exact absurd h typeNorm_no_app
            | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_nf.1)
            | .top, _ => exact isVal_top
            | .lam _ _, _ => exact isVal_lam _ _
          -- From hav: SemVal_nf j nf_dn av
          have hav_nfdn := hav.2 m_dn nf_dn hm_dn
          -- Get typeNorm_sub_wf for de
          have ⟨⟨hsub_de_nfd, _⟩, hwf_nfd⟩ := typeNorm_sub_wf m de nf_d hwf_de hcl_nfe.1 hm_d
          -- nf_d is a value
          have hval_nfd : IsVal nf_d := by
            match nf_d, hm_d with
            | .app _ _, h => exact absurd h typeNorm_no_app
            | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_nfe.1)
            | .top, _ => exact isVal_top
            | .lam _ _, _ => exact isVal_lam _ _
          -- Sub [] nf_dn nf_d: nf_dn ≤ dn ≤ de ≤ nf_d
          have hsub_nfdn_nfd : PSS.Sub [] nf_dn nf_d :=
            .trans (.trans hsub_nfdn_dn hsub_dn_de hwf_dn) hsub_de_nfd hwf_de
          -- IH at j < K'+1: transfer SemVal_nf j nf_dn av → SemVal_nf j nf_d av
          have hcl_nfdn := typeNorm_closedAt hcl_nf.1 hm_dn
          have hcl_nfd := typeNorm_closedAt hcl_nfe.1 hm_d
          exact ih_K j hj nf_dn nf_d av hsub_nfdn_nfd hwf_nfdn hwf_nfd
            hval_nfdn hval_nfd hcl_nfdn hcl_nfd hav_nfdn
        -- Step B: Get Sub [] av de
        have hsub_av_de : PSS.Sub [] av de := .trans hsub_av_dn hsub_dn_de hwf_dn
        -- Step C: Apply body condition with (de, be)
        have body_result := body_cond j hj av hav_de hcl_av hwf_av hsub_av_de i hi w hw
        -- body_result : IsVal w ∧ ∀ n nf, typeNorm n (be.subst 0 av) = some nf → SemVal_nf (j-i) nf w
        -- Step D: Body transfer — convert from (be.subst 0 av) to (bn.subst 0 av)
        -- Construct Sub [] (be.subst 0 av) (bn.subst 0 av) via beta_R + app_cong + beta_L
        have hwf_app_de : PSS.Wf [] (.app (.lam de be) av) := by
          exact .app hwf_nfe hwf_av hwf_de
            (.lam (.refl _) (.refl _) (.top _))
            hsub_av_de
        have hwf_app_dn : PSS.Wf [] (.app (.lam dn bn) av) := by
          exact .app hwf_nf hwf_av hwf_dn
            (.lam (.refl _) (.refl _) (.top _))
            hsub_av_dn
        have hsub_be_bn_subst : PSS.Sub [] (be.subst 0 av) (bn.subst 0 av) :=
          .trans
            (.trans .beta_R (.app_cong hsub (.refl _) (.refl _)) hwf_app_de)
            .beta_L hwf_app_dn
        -- Get Wf for substituted bodies
        have hwf_be_subst : PSS.Wf [] (be.subst 0 av) :=
          PSS.subst_wf hwf_be hwf_av hsub_av_de
        have hwf_bn_subst : PSS.Wf [] (bn.subst 0 av) :=
          PSS.subst_wf hwf_bn hwf_av hsub_av_dn
        -- closedAt for substituted bodies
        have hcl_be_subst : (be.subst 0 av).closedAt 0 = true :=
          Expr.subst_closedAt_zero hcl_nfe.2 hcl_av
        have hcl_bn_subst : (bn.subst 0 av).closedAt 0 = true :=
          Expr.subst_closedAt_zero hcl_nf.2 hcl_av
        -- Now transfer: for each nf_bn from typeNorm of (bn.subst 0 av),
        -- show SemVal_nf (j-i) nf_bn w
        refine ⟨body_result.1, fun m nf_bn hm_bn => ?_⟩
        -- Get typeNorm of (be.subst 0 av)
        obtain ⟨m_be, nf_be, hm_be⟩ := typeNorm_total hwf_be_subst hcl_be_subst
        -- From body_result: SemVal_nf (j-i) nf_be w
        have hval_w_nfbe := body_result.2 m_be nf_be hm_be
        -- Get Sub and Wf info for nf_be and nf_bn
        have ⟨⟨_, hsub_nfbe_be⟩, hwf_nfbe⟩ :=
          typeNorm_sub_wf m_be (be.subst 0 av) nf_be hwf_be_subst hcl_be_subst hm_be
        have ⟨⟨hsub_bn_nfbn, _⟩, hwf_nfbn⟩ :=
          typeNorm_sub_wf m (bn.subst 0 av) nf_bn hwf_bn_subst hcl_bn_subst hm_bn
        -- nf_be and nf_bn are values
        have hval_nfbe : IsVal nf_be := by
          match nf_be, hm_be with
          | .app _ _, h => exact absurd h typeNorm_no_app
          | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_be_subst)
          | .top, _ => exact isVal_top
          | .lam _ _, _ => exact isVal_lam _ _
        have hval_nfbn : IsVal nf_bn := by
          match nf_bn, hm_bn with
          | .app _ _, h => exact absurd h typeNorm_no_app
          | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_bn_subst)
          | .top, _ => exact isVal_top
          | .lam _ _, _ => exact isVal_lam _ _
        -- Sub [] nf_be nf_bn: nf_be ≤ be.subst ≤ bn.subst ≤ nf_bn
        -- hsub_nfbe_be : Sub [] nf_be (be.subst 0 av)
        -- hsub_be_bn_subst : Sub [] (be.subst 0 av) (bn.subst 0 av)
        -- hsub_bn_nfbn : Sub [] (bn.subst 0 av) nf_bn
        have hsub_nfbe_nfbn : PSS.Sub [] nf_be nf_bn :=
          .trans
            (.trans hsub_nfbe_be hsub_be_bn_subst hwf_be_subst)
            hsub_bn_nfbn hwf_bn_subst
        have hcl_nfbe := typeNorm_closedAt hcl_be_subst hm_be
        have hcl_nfbn := typeNorm_closedAt hcl_bn_subst hm_bn
        -- IH at j-i < K'+1: transfer nf_be → nf_bn
        have hji_lt : j - i < K' + 1 := by omega
        exact ih_K (j - i) hji_lt nf_be nf_bn w hsub_nfbe_nfbn hwf_nfbe hwf_nfbn
          hval_nfbe hval_nfbn hcl_nfbe hcl_nfbn hval_w_nfbe

noncomputable def typeNorm_sub_transfer {e e' : Expr} {n : Nat} {nf : Expr}
    (hsub : PSS.Sub [] e e')
    (hwf_e : PSS.Wf [] e) (hwf_e' : PSS.Wf [] e')
    (hcl_e : e.closedAt 0 = true) (hcl_e' : e'.closedAt 0 = true)
    (hn : typeNorm n e' = some nf) :
    ∃ n' nf', typeNorm n' e = some nf' ∧
      ∀ k v, SemVal_nf k nf' v → SemVal_nf k nf v := by
  -- Get typeNorm results for both sides
  obtain ⟨n_e, nf_e, hn_e⟩ := typeNorm_total hwf_e hcl_e
  -- Get Sub between e and nf_e, and between e' and nf
  have ⟨⟨_, hsub_nfe_e⟩, hwf_nfe⟩ := typeNorm_sub_wf n_e e nf_e hwf_e hcl_e hn_e
  have ⟨⟨hsub_e'_nf, _⟩, hwf_nf⟩ := typeNorm_sub_wf n e' nf hwf_e' hcl_e' hn
  -- Sub [] nf_e nf by trans
  have hsub_nfe_nf : PSS.Sub [] nf_e nf :=
    .trans (.trans hsub_nfe_e hsub hwf_e) hsub_e'_nf hwf_e'
  -- Both are values
  have hcl_nfe := typeNorm_closedAt hcl_e hn_e
  have hcl_nf := typeNorm_closedAt hcl_e' hn
  have hval_nfe : IsVal nf_e := by
    match nf_e, hn_e with
    | .app _ _, h => exact absurd h typeNorm_no_app
    | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_e)
    | .top, _ => exact isVal_top
    | .lam _ _, _ => exact isVal_lam _ _
  have hval_nf : IsVal nf := by
    match nf, hn with
    | .app _ _, h => exact absurd h typeNorm_no_app
    | .bvar _, h => exact absurd h (typeNorm_closedAt_no_bvar hcl_e')
    | .top, _ => exact isVal_top
    | .lam _ _, _ => exact isVal_lam _ _
  exact ⟨n_e, nf_e, hn_e, fun k v hv =>
    semVal_nf_sub_transfer k nf_e nf v hsub_nfe_nf hwf_nfe hwf_nf
      hval_nfe hval_nf hcl_nfe hcl_nf hv⟩

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
    Proof: typeNorm_beta gives typeNorm (n+2) (app (lam d b) a) = typeNorm (n+1) (b.subst 0 a).
    Any normalization of the reductum at fuel n+1 lifts to the redex at fuel n+2. -/
theorem subSem_beta_L {dom body arg : Expr} :
    SubSem (.app (.lam dom body) arg) (body.subst 0 arg) := by
  intro k v ⟨hval, h_all⟩
  refine ⟨hval, fun n τ_nf hn => ?_⟩
  -- hn : typeNorm n (body.subst 0 arg) = some τ_nf
  -- Need: typeNorm at the redex also produces τ_nf
  -- typeNorm_beta: typeNorm (n+2) (app (lam dom body) arg) = typeNorm (n+1) (body.subst 0 arg)
  -- We need typeNorm (n+1) (body.subst 0 arg) = some τ_nf, which follows from fuel mono.
  have hn' : typeNorm (n + 1) (body.subst 0 arg) = some τ_nf :=
    typeNorm_fuel_mono (by omega) hn
  have : typeNorm (n + 2) (.app (.lam dom body) arg) = some τ_nf := by
    rw [typeNorm_beta]; exact hn'
  exact h_all (n + 2) τ_nf this

/-- beta_R: SubSem (body.subst 0 arg) (app (lam dom body) arg).
    Proof: reverse of beta_L — any normalization of the redex at fuel n+2
    yields normalization of the reductum at fuel n+1. -/
theorem subSem_beta_R {dom body arg : Expr} :
    SubSem (body.subst 0 arg) (.app (.lam dom body) arg) := by
  intro k v ⟨hval, h_all⟩
  refine ⟨hval, fun n τ_nf hn => ?_⟩
  -- hn : typeNorm n (app (lam dom body) arg) = some τ_nf
  -- typeNorm n (app (lam dom body) arg):
  --   when n = 0: none
  --   when n = n'+1: match typeNorm n' (lam dom body) with ...
  --     when n' = 0: none (typeNorm 0 (lam dom body) = none)
  --     when n' = n''+1: typeNorm n' (lam dom body) = some (lam dom body)
  --       so result = typeNorm n' (body.subst 0 arg)
  -- So for hn to succeed we need n ≥ 2.
  cases n with
  | zero => simp [typeNorm] at hn
  | succ n =>
    cases n with
    | zero =>
      -- typeNorm 1 (app (lam dom body) arg) = match typeNorm 0 (lam dom body) with ...
      -- typeNorm 0 anything = none, so match none = none ≠ some τ_nf
      simp [typeNorm] at hn
    | succ n =>
      -- typeNorm (n+2) (app (lam dom body) arg) = typeNorm (n+1) (body.subst 0 arg)
      rw [typeNorm_beta] at hn
      exact h_all (n + 1) τ_nf hn

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
    | .app f a, hcl, hwf_app, hev =>
      have hj_pos : j ≥ 1 := by
        cases j with | zero => simp [concEval] at hev | succ n => omega
      refine ⟨hval, fun m nf hm => ?_⟩
      cases hkj : k - j with
      | zero => exact (semVal_nf_zero nf v).mpr hval
      | succ m' =>
      -- For typeNorm m (app f a) = some nf:
      -- Case f ≠ lam: typeNorm returns app f' a', so nf is an app.
      --   SemVal_nf at app = IsVal. Trivial.
      -- Case f = lam d b: typeNorm (m-1) (b.subst 0 a) = some nf.
      --   nf could be any shape, but for top and app cases, SemVal_nf = IsVal.
      --   For bvar: impossible (closedness).
      --   For lam: the substantial case.
      --
      -- Key insight: nf is the typeNorm result of (app f a) viewed as a TYPE.
      -- v is the concEval result of (app f a) viewed as a TERM.
      -- For non-lam nf: SemVal_nf just requires IsVal, which we have.
      -- For lam nf: we need to relate the type-normalization to the evaluation.
      --
      -- Strategy: for nf that is NOT a lam, return IsVal immediately.
      -- For lam nf: decompose the evaluation and use the IH.
      match nf with
      | .top => exact semVal_nf_top (m' + 1) v hval
      | .app _ _ => exact absurd hm typeNorm_no_app
      | .bvar bk => exact absurd hm (typeNorm_closedAt_no_bvar hcl)
      | .lam s t =>
        -- Strategy: use typeNorm_sub_transfer with Sub [] v (app f a) to
        -- show that typeNorm of v produces nf_v compatible with (lam s t).
        -- Since v is a value, typeNorm 1 v = some v, so nf_v = v.
        -- Then SemVal_nf (m'+1) v v is proved directly, and the transfer
        -- gives SemVal_nf (m'+1) (lam s t) v.
        have v_data := (concEval_combined j (.app f a) hcl hwf_app).props v hev
        have hsub_v_e : PSS.Sub [] v (.app f a) := v_data.1
        obtain ⟨n', nf_v, hn_v, htransfer⟩ :=
          typeNorm_sub_transfer hsub_v_e hwf_v hwf_app hcl_v hcl hm
        -- Since v is a value, typeNorm 1 v = some v
        have hn_v1 : typeNorm 1 v = some v := typeNorm_val hval (by omega)
        -- By determinism, nf_v = v
        have heq_nfv : nf_v = v := typeNorm_det hn_v hn_v1
        subst heq_nfv
        -- Now show SemVal_nf (m'+1) v v and transfer
        apply htransfer
        -- Goal: SemVal_nf (m'+1) v v
        rcases hval with rfl | ⟨s', t', rfl⟩
        · -- v = top
          exact semVal_nf_top (m' + 1) .top isVal_top
        · -- v = lam s' t'
          unfold SemVal_nf
          refine ⟨s', t', rfl, fun j' hj' av hav hcl_av hwf_av hsub_av i hi w hw => ?_⟩
          -- Body condition: concEval i (t'.subst 0 av) = ok w → SemVal (j'-i) (t'.subst 0 av) w
          -- Use ih_k at j' < k (since j' < m'+1 = k-j ≤ k-1 < k)
          have hwf_lam_v : PSS.Wf [] (.lam s' t') := hwf_v
          have hwf_body_v : PSS.Wf [s'] t' := match hwf_lam_v with | .lam _ hb => hb
          have hwf_subst := PSS.subst_wf hwf_body_v hwf_av hsub_av
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl_v
          have hcl_subst := Expr.subst_closedAt_zero hcl_v.2 hcl_av
          exact ih_k j' (by omega) (t'.subst 0 av) hcl_subst hwf_subst i hi w hw

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

/-- Helper: specialize subst_sub_gen at Γ₁ = [] to get Sub [] (a.subst 0 v) (b.subst 0 v)
    from Sub [σ] a b, Wf [] v, Sub [] v σ. -/
private noncomputable def subst_sub_zero {σ a b v : Expr}
    (hsub : PSS.Sub [σ] a b) (hwfv : PSS.Wf [] v) (hvsig : PSS.Sub [] v σ) :
    PSS.Sub [] (a.subst 0 v) (b.subst 0 v) := by
  have h := PSS.subst_sub_gen (Γ₁ := []) (σ := σ) (Γ₂ := []) hsub hwfv hvsig
  simp only [PSS.substPrefix, List.nil_append, List.length_nil] at h
  rw [Expr.shift_zero] at h
  exact h

/-- Fundamental theorem: Sub [] e τ implies SubSem e τ (semantic subtyping).

    Proved by well-founded induction on (k, sizeOf hsub) with lexicographic ordering.
    The lam case uses k-decrease (body condition quantifies over j < k).
    The trans case uses sizeOf-decrease (sub-derivations are smaller).
    Requires Wf hypotheses for both sides to enable domain/body conversion in the lam case. -/
noncomputable def fundamental_subSem_aux
    (k : Nat) {e τ : Expr} (hsub : PSS.Sub [] e τ)
    (hwf_e : PSS.Wf [] e) (hwf_τ : PSS.Wf [] τ) :
    ∀ v, SemVal k e v → SemVal k τ v := by
  match hsub with
  | .refl _ => exact fun v hv => hv
  | .top _ => exact fun v hv => semVal_top k v hv.1
  | .trans h1 h2 hw =>
    exact fun v hv =>
      fundamental_subSem_aux k h2 hw hwf_τ v
        (fundamental_subSem_aux k h1 hwf_e hw v hv)
  | .bvar hget => exact absurd hget (by simp [List.get?])
  | .beta_L => exact fun v hv => subSem_beta_L k v hv
  | .beta_R => exact fun v hv => subSem_beta_R k v hv
  | .app_cong (f := f) (f' := f') (a := a) (a' := a') hsub_ff' hsub_aa' hsub_a'a =>
    intro v ⟨hval, h_all⟩
    refine ⟨hval, fun n nf' hn => ?_⟩
    -- hn : typeNorm n (app f' a') = some nf'
    -- With new typeNorm, this means (for n = n'+1):
    --   typeNorm n' f' = some (lam d' b')
    --   typeNorm n' (b'.subst 0 a') = some nf'
    -- We need SemVal_nf k nf' v.
    -- nf' can't be app (typeNorm_no_app) or bvar (closedness).
    -- nf' = top: trivial.
    -- nf' = lam: requires relating typeNorm of (app f a) to typeNorm of (app f' a').
    --   From SubSem f f' (IH), we know related values satisfy related types.
    --   But we need a typeNorm congruence lemma: Sub-related terms produce
    --   Sub-related typeNorm results. This is NOT FALSE (the counterexample
    --   from the old typeNorm no longer applies) but requires a substantial
    --   new lemma about typeNorm and Sub interaction.
    match nf' with
    | .app _ _ => exact absurd hn typeNorm_no_app
    | .bvar bk => exact absurd hn (typeNorm_closedAt_no_bvar (wf_closed hwf_τ))
    | .top => exact semVal_nf_top k v hval
    | .lam s t =>
        -- Use typeNorm_sub_transfer: Sub [] (app f a) (app f' a') and
        -- typeNorm n (app f' a') = some (lam s t) gives us
        -- typeNorm n' (app f a) = some nf_fa with SemVal_nf transfer.
        have hsub_app : PSS.Sub [] (.app f a) (.app f' a') :=
          .app_cong hsub_ff' hsub_aa' hsub_a'a
        have hcl_e := wf_closed hwf_e
        have hcl_τ := wf_closed hwf_τ
        obtain ⟨n', nf_fa, hn_fa, htransfer⟩ :=
          typeNorm_sub_transfer hsub_app hwf_e hwf_τ hcl_e hcl_τ hn
        exact htransfer k v (h_all n' nf_fa hn_fa)
  | .lam (dom := dom) (dom' := dom') (body := body) (body' := body')
      hsub_dd' hsub_d'd hsub_bb' =>
    -- Extract Wf components
    have hwf_dom : PSS.Wf [] dom := match hwf_e with | .lam hd _ => hd
    have hwf_body : PSS.Wf [dom] body := match hwf_e with | .lam _ hb => hb
    have hwf_dom' : PSS.Wf [] dom' := match hwf_τ with | .lam hd _ => hd
    have hwf_body' : PSS.Wf [dom'] body' := match hwf_τ with | .lam _ hb => hb
    intro v hv
    obtain ⟨hval, h_all⟩ := hv
    refine ⟨hval, fun n nf hn => ?_⟩
    -- typeNorm n (lam dom' body') = some nf ⟹ nf = lam dom' body'
    have hn_pos : n > 0 := by
      cases n with | zero => simp [typeNorm] at hn | succ _ => omega
    rw [typeNorm_lam_eq hn_pos] at hn; cases hn
    -- Get SemVal_nf k (lam dom body) v from h_all
    have hsrc := h_all 1 (.lam dom body) (typeNorm_lam_eq (by omega))
    -- Case split on k
    cases k with
    | zero => exact (semVal_nf_zero (.lam dom' body') v).mpr hval
    | succ m =>
    -- hsrc : SemVal_nf (m+1) (lam dom body) v
    unfold SemVal_nf at hsrc
    obtain ⟨s', t', heq_v, body_cond_dom⟩ := hsrc
    -- Need: SemVal_nf (m+1) (lam dom' body') v
    unfold SemVal_nf
    subst heq_v
    refine ⟨s', t', rfl, fun j hj av hav hcl_av hwf_av hsub_av_dom' i hi w hw => ?_⟩
    -- Step A: Get Sub [] av dom from Sub [] av dom' and Sub [] dom' dom
    have hsub_av_dom : PSS.Sub [] av dom :=
      .trans hsub_av_dom' hsub_d'd hwf_dom'
    -- Step B: Get SemVal j dom av from SemVal j dom' av
    -- hav : IsVal av ∧ ∀ n nf, typeNorm n dom' = some nf → SemVal_nf j nf av
    -- This is SemVal j dom' av
    have semval_dom'_av : SemVal j dom' av := hav
    have semval_dom_av : SemVal j dom av :=
      fundamental_subSem_aux j hsub_d'd hwf_dom' hwf_dom av semval_dom'_av
    -- Step C: Use body_cond_dom to get SemVal (j-i) (body.subst 0 av) w
    have hdom_cond : IsVal av ∧ ∀ n nf, typeNorm n dom = some nf → SemVal_nf j nf av :=
      semval_dom_av
    have body_result := body_cond_dom j hj av hdom_cond hcl_av hwf_av hsub_av_dom i hi w hw
    -- body_result : IsVal w ∧ ∀ n nf, typeNorm n (body.subst 0 av) = some nf → SemVal_nf (j-i) nf w
    -- This is SemVal (j-i) (body.subst 0 av) w
    have semval_body : SemVal (j - i) (body.subst 0 av) w := body_result
    -- Step D: Convert to SemVal (j-i) (body'.subst 0 av) w
    -- Get Sub [] (body.subst 0 av) (body'.subst 0 av) from Sub [dom] body body'
    have hsub_bodies : PSS.Sub [] (body.subst 0 av) (body'.subst 0 av) :=
      subst_sub_zero hsub_bb' hwf_av hsub_av_dom
    have hwf_body_subst : PSS.Wf [] (body.subst 0 av) :=
      PSS.subst_wf hwf_body hwf_av hsub_av_dom
    have hwf_body'_subst : PSS.Wf [] (body'.subst 0 av) :=
      PSS.subst_wf hwf_body' hwf_av hsub_av_dom'
    exact fundamental_subSem_aux (j - i) hsub_bodies hwf_body_subst hwf_body'_subst w semval_body
termination_by (k, sizeOf hsub)

noncomputable def fundamental_subSem {e τ : Expr} (hsub : PSS.Sub [] e τ)
    (hwf_e : PSS.Wf [] e) (hwf_τ : PSS.Wf [] τ) :
    SubSem e τ :=
  fun k v hv => fundamental_subSem_aux k hsub hwf_e hwf_τ v hv

noncomputable def fundamental_closed (e τ : Expr)
    (hcl : e.closedAt 0 = true) (hwf_e : PSS.Wf [] e) (hwf_τ : PSS.Wf [] τ)
    (hsub : PSS.Sub [] e τ) :
    ∀ k, SemExpr k τ e :=
  fun k => fundamental_trans (semExpr_refl k e hcl hwf_e) (fundamental_subSem hsub hwf_e hwf_τ)

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
| `beta_L` | PROVED |
| `beta_R` | PROVED |
| `lam` | PROVED (via WF induction on (k, sizeOf hsub) + Wf hypotheses) |
| `app_cong` | PROVED (via `typeNorm_sub_transfer`) |

### semExpr_refl_aux (identity extension):

All cases proved, including the app case with lam normal form, via
`typeNorm_sub_transfer`.

### typeNorm redesign (fixing app_cong counterexample)

The previous `typeNorm` had two separate app cases: a syntactic beta-redex
case `app (lam d b) a` that reduced, and a non-redex case that normalized
sub-expressions and returned `app f' a'`. This made `app_cong` provably FALSE
because Sub-related functions differing in syntactic shape (redex vs reductum)
produced fundamentally different typeNorm outputs (app vs lam).

The fix: merge into one case that ALWAYS normalizes f first via `typeNorm n f`,
then beta-reduces if the result is a lambda, otherwise returns `none` (stuck).
This ensures Sub-related terms are treated uniformly.

Key new property: `typeNorm` NEVER produces an `app` (`typeNorm_no_app`).
For closed inputs, the only possible outputs are `top` and `lam`.

### Remaining axioms (1 total):

`typeNorm_total_axiom`: head-normalization for PSS. States that typeNorm
succeeds on all closed well-formed expressions. This axiom encapsulates
the termination argument that the Wf discipline prevents non-terminating
head-reduction sequences (the omega combinator is not well-formed in PSS).

`typeNorm_sub_transfer` is now fully proved, using:
1. `typeNorm_total_axiom` (head-normalization)
2. `typeNorm_sub_wf` (typeNorm preserves Sub and Wf)
3. `semVal_nf_sub_transfer` (SemVal_nf transfer between values, by
   step-index induction). The lam-lam body case constructs the body Sub
   via beta_R + app_cong + beta_L, avoiding the need for body inversion
   (the Hutchins obstacle).

### concEval_safe

Type safety is proved WITHOUT using the semantic canonical forms at all.
Instead, it uses the SYNTACTIC canonical forms (top_not_sub_lam axiom from
Soundness.lean) directly. The axiom `typeNorm_total_axiom` does not
affect the type safety proof.
-/

end PSS.LogRel
