import PSS.Sub
import PSS.SubstWf
import PSS.Eval
import PSS.SyntaxLemmas

/-!
# Step-Indexed Logical Relation for PSS Type Safety

Uses semantic canonical forms to avoid the need for syntactic domain
inversion (`lam_sub_lam_inv`).

Key idea: `SemVal_nf` at a lambda type stores domain equivalence data
(Sub [] s d × Sub [] d s) between the *type* domain `s` and the
*value* domain `d`.  `sub_sound` transforms this data when converting
between types.  `eval_syntactic` extracts the domain equivalence to
derive `Sub [] av d` from `Sub [] av s`, enabling `subst_wf` without
syntactic inversion.

The ONLY remaining sorry is `app_cong` in `sub_sound` (inherited from before).
The critical `lam_sub_lam_inv` sorry has been eliminated.
-/

open Expr

namespace PSS.SafeLogRel

/-! ## Type Normalization -/

def typeNorm : Nat → Expr → Option Expr
  | 0, _ => none
  | _ + 1, .top => some .top
  | _ + 1, .lam d b => some (.lam d b)
  | _ + 1, .bvar n => some (.bvar n)
  | k + 1, .app f a => match typeNorm k f with
    | some (.lam _d b) => typeNorm k (b.subst 0 a)
    | _ => none

/-! ## Semantic Value Type -/

/-- Step-indexed semantic value relation on normal-form types.

The λ-case stores domain equivalence data:
* `Sub [] s d`, `Sub [] d s` — equivalence between type domain `s` and
  value domain `d`
* `Wf [d] b`, `Wf [] d` — well-formedness of the value's parts

This is wrapped in `Nonempty` since `Sub`/`Wf` live in `Type` while
`SemVal_nf` lives in `Prop`.

No body condition is needed in the semantic relation; the body is handled
syntactically via `eval_syntactic`'s IH once domain equivalence provides
`Sub [] av d` for `subst_wf`.
-/
noncomputable def SemVal_nf : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | _ + 1, .top, _ => True
  | _ + 1, .bvar _, _ => True
  | _ + 1, .app _ _, _ => True
  | _ + 1, .lam s _t, v => ∃ d b, v = .lam d b ∧
      Nonempty (PSS.Sub [] s d × PSS.Sub [] d s × PSS.Wf [d] b × PSS.Wf [] d)

def SemVal (k : Nat) (τ : Expr) (v : Expr) : Prop :=
  v.IsValue ∧ ∀ n τ_nf, typeNorm n τ = some τ_nf → SemVal_nf k τ_nf v

theorem semVal_top {k : Nat} {v : Expr} (hv : v.IsValue) : SemVal k .top v := by
  refine ⟨hv, fun n τ_nf hn => ?_⟩
  cases n with
  | zero => simp [typeNorm] at hn
  | succ m =>
    have : τ_nf = .top := by unfold typeNorm at hn; exact (Option.some.inj hn).symm
    subst this; cases k <;> simp [SemVal_nf]

theorem semVal_lam_is_lam {k : Nat} {s t v : Expr}
    (h : SemVal (k + 1) (.lam s t) v) : ∃ d b, v = .lam d b := by
  have h1 := h.2 1 (.lam s t) (by unfold typeNorm; rfl)
  simp only [SemVal_nf] at h1
  exact let ⟨d, b, heq, _⟩ := h1; ⟨d, b, heq⟩

/-- Extract domain equivalence data from SemVal at a lambda type,
    given that the value is already known to be `lam d b`. -/
noncomputable def semVal_lam_dom_equiv {k : Nat} {s t d b : Expr}
    (h : SemVal (k + 1) (.lam s t) (.lam d b)) :
    PSS.Sub [] s d × PSS.Sub [] d s × PSS.Wf [d] b × PSS.Wf [] d := by
  have h1 := h.2 1 (.lam s t) (by unfold typeNorm; rfl)
  simp only [SemVal_nf] at h1
  -- h1 : ∃ d' b', lam d b = lam d' b' ∧ Nonempty (Sub [] s d' × ...)
  -- Since lam is injective, d' = d and b' = b
  have : Nonempty (PSS.Sub [] s d × PSS.Sub [] d s × PSS.Wf [d] b × PSS.Wf [] d) := by
    obtain ⟨d', b', heq, hdata⟩ := h1
    cases heq
    exact hdata
  exact Classical.choice this

theorem top_not_semVal_lam {k : Nat} {s t : Expr} :
    ¬ SemVal (k + 1) (.lam s t) .top := by
  intro h; obtain ⟨d, b, heq⟩ := semVal_lam_is_lam h; cases heq

theorem semVal_nf_antimono (j k : Nat) (τ v : Expr)
    (hjk : j ≤ k) (h : SemVal_nf k τ v) : SemVal_nf j τ v := by
  induction j with
  | zero => simp [SemVal_nf]
  | succ j _ =>
    cases k with | zero => omega | succ k =>
    match τ with
    | .top => simp only [SemVal_nf] at *
    | .bvar _ => simp only [SemVal_nf] at *
    | .app _ _ => simp only [SemVal_nf] at *
    | .lam s t =>
      simp only [SemVal_nf] at h ⊢
      exact h  -- domain equiv data carries through unchanged

theorem semVal_antimono (hjk : j ≤ k) (h : SemVal k τ v) : SemVal j τ v :=
  ⟨h.1, fun n τ_nf hn => semVal_nf_antimono j k τ_nf v hjk (h.2 n τ_nf hn)⟩

/-! ## concEval lemmas -/

private theorem concEval_isVal {fuel : Nat} {e v : Expr}
    (hev : concEval fuel e = .ok v) : v.IsValue := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · exact absurd hev (by intro h; cases h)
    · cases hev; exact trivial
    · cases hev; exact trivial
    · split at hev
      · next fv av _ _ =>
        split at hev
        · exact ih hev
        · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)

private theorem concEval_closedAt' {fuel : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true) (hev : concEval fuel e = .ok v) :
    v.closedAt 0 = true := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · simp [Expr.closedAt, decide_eq_true_eq] at hcl
    · cases hev; rfl
    · cases hev; exact hcl
    · simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      split at hev
      · next fv av hf ha =>
        split at hev
        · next dom body _ =>
          exact ih (Expr.subst_closedAt_zero
            (by have := ih hcl.1 hf; simp [Expr.closedAt, Bool.and_eq_true] at this; exact this.2)
            (ih hcl.2 ha)) hev
        · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)
      · exact absurd hev (by intro h; cases h)

/-! ## Sub soundness

With the simplified SemVal_nf, sub_sound just transforms domain
equivalence in the lambda case. The app_cong, beta_L, beta_R cases
are straightforward since SemVal_nf at app/bvar/top types is trivially True. -/

noncomputable def sub_sound (k : Nat) {a b : Expr} (hsub : PSS.Sub [] a b)
    (hwfa : PSS.Wf [] a) (hwfb : PSS.Wf [] b) (v : Expr) (hv : SemVal k a v) :
    SemVal k b v := by
  match hsub with
  | .refl _ => exact hv
  | .top _ => exact semVal_top hv.1
  | .trans h1 h2 hwm =>
    exact sub_sound k h2 hwm hwfb v (sub_sound k h1 hwfa hwm v hv)
  | .bvar hget => exact absurd hget (by simp [List.get?])
  | .lam (dom := dom) (dom' := dom') (body := body) (body' := body')
      h_dd' h_d'd h_bb' =>
    have hwf_dom : PSS.Wf [] dom := match hwfa with | .lam hd _ => hd
    refine ⟨hv.1, fun n τ_nf hn => ?_⟩
    cases n with
    | zero => simp [typeNorm] at hn
    | succ m =>
      have : τ_nf = .lam dom' body' := by unfold typeNorm at hn; exact (Option.some.inj hn).symm
      subst this
      cases k with
      | zero => simp [SemVal_nf]
      | succ k =>
        have h_in := hv.2 1 (.lam dom body) (by unfold typeNorm; rfl)
        simp only [SemVal_nf] at h_in ⊢
        obtain ⟨d, b_val, heq_v, hdata_in⟩ := h_in
        -- Produce the output Nonempty wrapper (all in Prop)
        exact ⟨d, b_val, heq_v, by
          have ⟨hsub_dom_d, hsub_d_dom, hwf_db, hwf_d⟩ := Classical.choice hdata_in
          exact ⟨⟨.trans h_d'd hsub_dom_d hwf_dom,
                  .trans hsub_d_dom h_dd' hwf_dom,
                  hwf_db, hwf_d⟩⟩⟩
  | .app_cong _ _ _ =>
    -- Requires a "typeNorm respects Sub.app_cong" property.
    -- typeNorm at an app type beta-reduces the function, so relating the
    -- normalizations of (app f a) and (app f' a') requires connecting
    -- the typeNorm results through the Sub derivations — a substantial
    -- theorem about the interaction between syntactic normalization and
    -- the subtyping relation.
    exact ⟨hv.1, fun n τ_nf hn => sorry⟩
  | .beta_L (dom := dom_) (body := bdy) (arg := arg) =>
    refine ⟨hv.1, fun n τ_nf hn => ?_⟩
    cases n with
    | zero => simp [typeNorm] at hn
    | succ n' =>
      have hn' : typeNorm (n' + 2) (.app (.lam dom_ bdy) arg) = some τ_nf := by
        change (match typeNorm (n' + 1) (.lam dom_ bdy) with
          | some (.lam _d b) => typeNorm (n' + 1) (b.subst 0 arg) | _ => none) = some τ_nf
        simp [typeNorm]; exact hn
      exact hv.2 (n' + 2) τ_nf hn'
  | .beta_R (dom := dom_) (body := bdy) (arg := arg) =>
    refine ⟨hv.1, fun n τ_nf hn => ?_⟩
    cases n with
    | zero => simp [typeNorm] at hn
    | succ n' =>
      cases n' with
      | zero => simp [typeNorm] at hn
      | succ n'' =>
        have hmatch : typeNorm (n'' + 1) (bdy.subst 0 arg) = some τ_nf := by
          change (match typeNorm (n'' + 1) (.lam dom_ bdy) with
            | some (.lam _d b) => typeNorm (n'' + 1) (b.subst 0 arg) | _ => none) = some τ_nf at hn
          simp [typeNorm] at hn; exact hn
        exact hv.2 (n'' + 1) τ_nf hmatch
termination_by (k, sizeOf hsub)

/-! ## Syntactic eval invariant -/

structure SynEvalProps (fuel : Nat) (e : Expr) : Type where
  no_error : ∀ msg, concEval fuel e ≠ .error msg
  props : ∀ v, concEval fuel e = .ok v →
    PSS.Sub [] v e × PSS.Sub [] e v × PSS.Wf [] v

private noncomputable def eval_syntactic (fuel : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    SynEvalProps fuel e := by
  induction fuel generalizing e with
  | zero =>
    exact { no_error := fun _ h => by simp [concEval] at h,
            props := fun _ h => by simp [concEval] at h }
  | succ n ih =>
    match e, hcl, hwf with
    | .bvar _, hcl, _ =>
      exact absurd hcl (by simp [Expr.closedAt, decide_eq_true_eq])
    | .top, _, _ =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, .top⟩ }
    | .lam _ _, _, hwf =>
      exact { no_error := fun _ h => by simp [concEval] at h,
              props := fun v hev => by
                simp [concEval] at hev; subst hev; exact ⟨.refl _, .refl _, hwf⟩ }
    | .app f a, hcl, hwf =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      match hwf with
      | .app (s := s) hwf_f hwf_a hwf_s hsub_f_lam hsub_a_s =>
        have ihf := ih f hcl.1 hwf_f
        have iha := ih a hcl.2 hwf_a
        -- fv can't be Top (semantic canonical forms)
        have fv_not_top : ∀ fv, concEval n f = .ok fv → fv ≠ .top := by
          intro fv hf heq; subst heq
          have fv_data := ihf.props .top hf
          have hsub_top_lam : PSS.Sub [] .top (.lam s .top) :=
            .trans fv_data.1 hsub_f_lam hwf_f
          exact top_not_semVal_lam (sub_sound 2 hsub_top_lam .top (.lam hwf_s .top) .top
            (semVal_top trivial))
        -- fv must be a lambda
        have fv_is_lam : ∀ fv, concEval n f = .ok fv → Σ' (d b : Expr), fv = .lam d b := by
          intro fv hf
          match fv, concEval_isVal hf with
          | .top, _ => exact absurd rfl (fv_not_top .top hf)
          | .lam d b, _ => exact ⟨d, b, rfl⟩
          | .bvar _, hval => exact absurd hval id
          | .app _ _, hval => exact absurd hval id
        -- Key: build SemVal for fv and extract domain equivalence
        have app_lam_data : ∀ (d b av : Expr),
            concEval n f = .ok (.lam d b) → concEval n a = .ok av →
            SynEvalProps n (b.subst 0 av) := by
          intro d b av hf ha
          have fv_data := ihf.props (.lam d b) hf
          have av_data := iha.props av ha
          have hwf_fv : PSS.Wf [] (.lam d b) := fv_data.2.2
          have hwf_d : PSS.Wf [] d := match hwf_fv with | .lam hd _ => hd
          have hwf_db : PSS.Wf [d] b := match hwf_fv with | .lam _ hb => hb
          have hwf_av : PSS.Wf [] av := av_data.2.2
          have hcl_av := concEval_closedAt' hcl.2 ha
          have hcl_fv := concEval_closedAt' hcl.1 hf
          -- Build self-SemVal for lam d b (trivial with simplified SemVal_nf)
          have semval_fv : SemVal 1 (.lam d b) (.lam d b) := by
            refine ⟨trivial, fun nm τ_nf hn => ?_⟩
            cases nm with
            | zero => simp [typeNorm] at hn
            | succ nm' =>
              have : τ_nf = .lam d b := by unfold typeNorm at hn; exact (Option.some.inj hn).symm
              subst this
              simp only [SemVal_nf]
              exact ⟨d, b, rfl, ⟨⟨.refl _, .refl _, hwf_db, hwf_d⟩⟩⟩
          -- Use sub_sound to convert to the function type
          have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
            .trans fv_data.1 hsub_f_lam hwf_f
          have semval_at_type := sub_sound 1 hfv_sub_lam hwf_fv (.lam hwf_s .top)
            (.lam d b) semval_fv
          -- Extract domain equivalence: Sub [] s d × Sub [] d s × Wf [d] b × Wf [] d
          have ⟨hsub_sd, hsub_ds, _, _⟩ := semVal_lam_dom_equiv semval_at_type
          -- Now derive Sub [] av d from Sub [] av s + Sub [] s d
          have hsub_av_s : PSS.Sub [] av s := .trans av_data.1 hsub_a_s hwf_a
          have hsub_av_d : PSS.Sub [] av d := .trans hsub_av_s hsub_sd hwf_s
          -- Build Wf for the body substitution
          have hwf_bsubst : PSS.Wf [] (b.subst 0 av) :=
            PSS.subst_wf hwf_db hwf_av hsub_av_d
          have hcl_bsubst : (b.subst 0 av).closedAt 0 = true :=
            Expr.subst_closedAt_zero
              (by simp [Expr.closedAt, Bool.and_eq_true] at hcl_fv; exact hcl_fv.2)
              hcl_av
          -- Use the IH — no domain inversion needed!
          exact ih (b.subst 0 av) hcl_bsubst hwf_bsubst
        exact {
          no_error := by
            intro msg herr; unfold concEval at herr
            match hf_eq : concEval n f with
            | .error m => exact ihf.no_error m hf_eq
            | .outOfFuel => simp [hf_eq] at herr
            | .ok fv =>
              match ha_eq : concEval n a with
              | .error m => exact iha.no_error m ha_eq
              | .outOfFuel => simp [hf_eq, ha_eq] at herr
              | .ok av =>
                let ⟨d, b, hlam⟩ := fv_is_lam fv hf_eq
                subst hlam; simp [hf_eq, ha_eq] at herr
                exact (app_lam_data d b av hf_eq ha_eq).no_error msg herr
          props := by
            intro v hev; unfold concEval at hev
            match hf_eq : concEval n f with
            | .error m => exact absurd hf_eq (ihf.no_error m)
            | .outOfFuel => simp [hf_eq] at hev
            | .ok fv =>
              match ha_eq : concEval n a with
              | .error m => exact absurd ha_eq (iha.no_error m)
              | .outOfFuel => simp [hf_eq, ha_eq] at hev
              | .ok av =>
                let ⟨d, b, hlam⟩ := fv_is_lam fv hf_eq
                subst hlam; simp [hf_eq, ha_eq] at hev
                have rec_data := app_lam_data d b av hf_eq ha_eq
                have v_data := rec_data.props v hev
                have fv_data := ihf.props (.lam d b) hf_eq
                have av_data := iha.props av ha_eq
                -- Build the Sub/Wf for the result
                -- We need: Sub [] v (app f a) × Sub [] (app f a) v × Wf [] v
                -- First extract domain equiv again
                have hwf_fv : PSS.Wf [] (.lam d b) := fv_data.2.2
                have hwf_d : PSS.Wf [] d := match hwf_fv with | .lam hd _ => hd
                have hwf_db : PSS.Wf [d] b := match hwf_fv with | .lam _ hb => hb
                have hwf_av : PSS.Wf [] av := av_data.2.2
                have semval_fv : SemVal 1 (.lam d b) (.lam d b) :=
                  ⟨trivial, fun nm τ_nf hn => by
                    cases nm with
                    | zero => simp [typeNorm] at hn
                    | succ nm' =>
                      have : τ_nf = .lam d b := by unfold typeNorm at hn; exact (Option.some.inj hn).symm
                      subst this; simp only [SemVal_nf]
                      exact ⟨d, b, rfl, ⟨⟨.refl _, .refl _, hwf_db, hwf_d⟩⟩⟩⟩
                have hfv_sub_lam : PSS.Sub [] (.lam d b) (.lam s .top) :=
                  .trans fv_data.1 hsub_f_lam hwf_f
                have semval_at_type := sub_sound 1 hfv_sub_lam hwf_fv (.lam hwf_s .top)
                  (.lam d b) semval_fv
                have ⟨hsub_sd, hsub_ds, _, _⟩ := semVal_lam_dom_equiv semval_at_type
                have hsub_av_s : PSS.Sub [] av s := .trans av_data.1 hsub_a_s hwf_a
                have hsub_av_d : PSS.Sub [] av d := .trans hsub_av_s hsub_sd hwf_s
                have hwf_bsubst : PSS.Wf [] (b.subst 0 av) :=
                  PSS.subst_wf hwf_db hwf_av hsub_av_d
                have h_wf_app_lam : PSS.Wf [] (.app (.lam d b) av) :=
                  .app hwf_fv hwf_av hwf_s hfv_sub_lam hsub_av_s
                exact ⟨
                  .trans (.trans v_data.1 .beta_R hwf_bsubst)
                    (.app_cong fv_data.1 av_data.1 av_data.2.1) h_wf_app_lam,
                  .trans (.trans (.app_cong fv_data.2.1 av_data.2.1 av_data.1) .beta_L h_wf_app_lam)
                    v_data.2.1 hwf_bsubst,
                  v_data.2.2⟩
        }

/-! ## Type Safety -/

theorem type_safety (e : Expr) (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    ∀ (k : Nat) (msg : String), concEval k e ≠ .error msg :=
  fun k msg => (eval_syntactic k e hcl hwf).no_error msg

end PSS.SafeLogRel
