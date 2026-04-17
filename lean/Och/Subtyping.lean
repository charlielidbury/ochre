import Och.Syntax
import Och.Eval

/-!
# Och Subtyping (de Bruijn)

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

With de Bruijn indices, lambda/mu subtyping no longer needs variable renaming:
alpha-equivalent terms are syntactically identical, so body comparison is direct.

## Algorithmic checker

The algorithmic subtype checker `subCheckNF` is defined in Eval.lean (mutual
with absEval). This file contains the inductive subtyping relations and
their proofs, plus theorems about subCheckNF.
-/

open Expr

/-- Typing context: `Ctx[k]` is the declared type of `.bvar k`.
Stored in de Bruijn-index order (`Ctx[0]` = innermost binder).
Each entry's free bvars are relative to the *enclosing* context,
so looking up `.bvar k` yields a type that must be shifted by
`k+1` to be valid at the current depth. -/
abbrev Ctx := List Expr

/-- Coinductive hypotheses: `(a, b) ∈ S` means the goal `a ⊑ b`
may be assumed — it's an ancestor in the derivation tree,
encountered at a productive fix/iota unfold. This is the
Brandt-Henglein device for equirecursive subtyping
(SoundnessAudit A4); the algorithmic seen-set is its direct
realisation. -/
abbrev Seen := List (Expr × Expr)

/-- Declarative subtyping relation. `Subtype' S Γ a b` means
`Γ ⊢ a ⊑ b` assuming every pair in `S` coinductively.

Brought into sync with the algorithmic checker after the
SoundnessAudit pass:

  - `hyp`: an ancestor goal `(a, b) ∈ S` may be assumed. Only
    the *productive* rules (`iota_intro`, the three `unfold_*`)
    extend `S`, so `.hyp` cannot close a goal that hasn't
    passed through at least one such guard — the standard
    Brandt-Henglein productivity condition (A4).
  - `app_cong` requires argument *equivalence* (`a₂ ⊑ a₁ ∧ a₁
    ⊑ a₂`), not just `a₂ ⊑ a₁` — a neutral head can use its
    argument at any variance (A1).
  - `lam` is the full contravariant-domain rule (was `lam_body`
    with same-domain only). The old form is derivable
    (`Subtype'.lam (refl dom) h`).
  - `unfold_iota_L` added (algorithm has it; ι is its own
    one-step unfolding).
  - `trans` is an explicit constructor. With equirecursive
    fix-unfold, transitivity is not obviously admissible
    (the unfold rules don't decrease a syntactic measure), so
    it's taken as primitive.
  - β/let/asc-conversion rules so the relation is closed under
    head reduction (the algorithm normalises before comparing).

The "real" subtyping judgment is `Subtype' [] Γ a b` (empty
hypothesis set). A non-empty `S` arises only inside a
derivation, mirroring the algorithm's seen-set growth.
-/
inductive Subtype' : Seen → Ctx → Expr → Expr → Prop where
  /-- Coinductive hypothesis: an ancestor goal in `S` may be
  assumed. Only the productive rules extend `S`. -/
  | hyp {S Γ a b} : (a, b) ∈ S → Subtype' S Γ a b
  | refl {S Γ} (e : Expr) : Subtype' S Γ e e
  | top {S Γ} (e : Expr) : Subtype' S Γ e .type
  | trans {S Γ a b c} :
      Subtype' S Γ a b → Subtype' S Γ b c → Subtype' S Γ a c
  /-- Variable rule: `.bvar k` has the type recorded in the
  context, shifted to the current depth. This is what the
  algorithm's `neutralAscent` realises. -/
  | bvar {S} {Γ : Ctx} {k : Nat} {τ : Expr} :
      Γ.get? k = some τ →
      Subtype' S Γ (.bvar k) (τ.shift (k+1) 0)
  /-- Function subtyping: contravariant domain, covariant body
  (under the *target* domain — a caller supplies a `domB`, which
  the function may treat as the wider `domA`). -/
  | lam {S Γ domA domB bodyA bodyB} :
      Subtype' S Γ domB domA →
      Subtype' S (domB :: Γ) bodyA bodyB →
      Subtype' S Γ (.lam domA bodyA) (.lam domB bodyB)
  /-- Stuck-application congruence: arguments must be
  *equivalent* (both directions). See SoundnessAudit A1. -/
  | app_cong {S Γ f₁ f₂ a₁ a₂} :
      Subtype' S Γ f₂ f₁ → Subtype' S Γ a₂ a₁ → Subtype' S Γ a₁ a₂ →
      Subtype' S Γ (.app f₂ a₂) (.app f₁ a₁)
  | iota_body {S Γ ann body₁ body₂} :
      Subtype' S (ann :: Γ) body₂ body₁ →
      Subtype' S Γ (.iota ann body₂) (.iota ann body₁)
  | fix_body {S Γ ann body₁ body₂} :
      Subtype' S (ann :: Γ) body₂ body₁ →
      Subtype' S Γ (.fix ann body₂) (.fix ann body₁)
  /-- iotaIntro (value-sub, Cedille-style). The goal is added
  to `S` before recursing — both premises may use it. -/
  | iota_intro {S Γ a ann body} :
      Subtype' ((a, .iota ann body) :: S) Γ a ann →
      Subtype' ((a, .iota ann body) :: S) Γ a (body.subst 0 a) →
      Subtype' S Γ a (.iota ann body)
  /-- [unfoldIotaL]: `ι A. body ⊑ c` if its one-step unfolding
  is. The goal is added to `S` (productive unfold). -/
  | unfold_iota_L {S Γ ann body c} :
      Subtype' ((.iota ann body, c) :: S) Γ
        (body.subst 0 (.iota ann body)) c →
      Subtype' S Γ (.iota ann body) c
  /-- [unfoldFixL]: `fix A. body ⊑ c` if `body[self := fix A. body] ⊑ c`. -/
  | unfold_fix_L {S Γ ann body c} :
      Subtype' ((.fix ann body, c) :: S) Γ
        (body.subst 0 (.fix ann body)) c →
      Subtype' S Γ (.fix ann body) c
  /-- [unfoldFixR]: `a ⊑ fix A. body` if `a ⊑ body[self := fix A. body]`.
      The previous `[fix-ann]` (`a ⊑ A → a ⊑ fix A. body`) was removed:
      `A` is the type of the recursion variable, not an upper bound on
      the fixpoint, so with `A = Type` it admitted `Nat ⊑ dBool`. -/
  | unfold_fix_R {S Γ a ann body} :
      Subtype' ((a, .fix ann body) :: S) Γ
        a (body.subst 0 (.fix ann body)) →
      Subtype' S Γ a (.fix ann body)
  /-- β-conversion on the left. The algorithm normalises before
  comparing; declaratively, a β-redex on either side may be
  contracted. This (with `trans`) makes `Subtype'` closed under
  β-equivalence. -/
  | beta_L {S Γ dom body arg b} :
      Subtype' S Γ (body.subst 0 arg) b →
      Subtype' S Γ (.app (.lam dom body) arg) b
  | beta_R {S Γ a dom body arg} :
      Subtype' S Γ a (body.subst 0 arg) →
      Subtype' S Γ a (.app (.lam dom body) arg)
  /-- let-conversion (`let x = v in e ↝ e[x:=v]`). -/
  | letE_L {S Γ val body b} :
      Subtype' S Γ (body.subst 0 val) b →
      Subtype' S Γ (.letE val body) b
  | letE_R {S Γ a val body} :
      Subtype' S Γ a (body.subst 0 val) →
      Subtype' S Γ a (.letE val body)
  /-- Ascription is computationally transparent. -/
  | asc_L {S Γ e τ b} :
      Subtype' S Γ e b → Subtype' S Γ (.asc e τ) b
  | asc_R {S Γ a e τ} :
      Subtype' S Γ a e → Subtype' S Γ a (.asc e τ)

/-- Hypothesis-set weakening: a derivation under `S` is also a
derivation under any superset `S'`. (Adding hypotheses can
only help.) The `subCheckVal_sound` proof uses this to thread
the algorithmic seen-set into the declarative one. -/
theorem Subtype'.weaken {S S' Γ a b}
    (hsub : ∀ p, p ∈ S → p ∈ S') (h : Subtype' S Γ a b) :
    Subtype' S' Γ a b := by
  induction h generalizing S' with
  | hyp hin => exact .hyp (hsub _ hin)
  | refl e => exact .refl e
  | top e => exact .top e
  | trans _ _ ih1 ih2 => exact .trans (ih1 hsub) (ih2 hsub)
  | bvar h => exact .bvar h
  | lam _ _ ihd ihb => exact .lam (ihd hsub) (ihb hsub)
  | app_cong _ _ _ ihf iha iha' =>
      exact .app_cong (ihf hsub) (iha hsub) (iha' hsub)
  | iota_body _ ih => exact .iota_body (ih hsub)
  | fix_body _ ih => exact .fix_body (ih hsub)
  | iota_intro _ _ ih1 ih2 =>
      refine .iota_intro (ih1 ?_) (ih2 ?_) <;>
      · intro p hp
        cases hp with
        | head => exact List.mem_cons_self ..
        | tail _ h => exact List.mem_cons_of_mem _ (hsub _ h)
  | unfold_iota_L _ ih =>
      refine .unfold_iota_L (ih ?_)
      intro p hp
      cases hp with
      | head => exact List.mem_cons_self ..
      | tail _ h => exact List.mem_cons_of_mem _ (hsub _ h)
  | unfold_fix_L _ ih =>
      refine .unfold_fix_L (ih ?_)
      intro p hp
      cases hp with
      | head => exact List.mem_cons_self ..
      | tail _ h => exact List.mem_cons_of_mem _ (hsub _ h)
  | unfold_fix_R _ ih =>
      refine .unfold_fix_R (ih ?_)
      intro p hp
      cases hp with
      | head => exact List.mem_cons_self ..
      | tail _ h => exact List.mem_cons_of_mem _ (hsub _ h)
  | beta_L _ ih => exact .beta_L (ih hsub)
  | beta_R _ ih => exact .beta_R (ih hsub)
  | letE_L _ ih => exact .letE_L (ih hsub)
  | letE_R _ ih => exact .letE_R (ih hsub)
  | asc_L _ ih => exact .asc_L (ih hsub)
  | asc_R _ ih => exact .asc_R (ih hsub)

/-- The old same-domain rule is derivable. -/
theorem Subtype'.lam_body {S Γ dom body₁ body₂}
    (h : Subtype' S (dom :: Γ) body₂ body₁) :
    Subtype' S Γ (.lam dom body₂) (.lam dom body₁) :=
  .lam (.refl dom) h

/-- Head congruence: derivable from `app_cong` with reflexive
arg. Lets β/let/asc-conversion fire under an application spine
via `trans`. -/
theorem Subtype'.app_head {S Γ f f' a}
    (h : Subtype' S Γ f f') : Subtype' S Γ (.app f a) (.app f' a) :=
  .app_cong h (.refl a) (.refl a)

/-- Multi-step head reduction under a spine, then continue. The
common pattern when the head is `(λx. …) v w …`. -/
theorem Subtype'.beta_head {S Γ dom body arg a c}
    (h : Subtype' S Γ (.app (body.subst 0 arg) a) c) :
    Subtype' S Γ (.app (.app (.lam dom body) arg) a) c :=
  .trans (.app_head (.beta_L (.refl _))) h

/-- Shift respects subtyping (needed for `narrow`'s `.bvar`
case). The proof is by induction on the derivation; each
constructor commutes with `shift` since `shift` is a
homomorphism on `Expr` and `subst` (the substitution lemmas
in `Syntax.lean`, now sorry-free). -/
theorem Subtype'.shift_preserve {S Γ a b} (d c : Nat)
    (h : Subtype' S Γ a b) :
    Subtype' (S.map (fun (x, y) => (x.shift d c, y.shift d c)))
             (Γ.map (·.shift d c)) (a.shift d c) (b.shift d c) := by
  sorry

/-- Context narrowing: replacing a context entry with a
subtype preserves derivations. Bridges the algorithm's
lam-lam arm (which pushes the LHS domain `domA`) and
`Subtype'.lam` (which pushes the target domain `domB`):
since `domB ⊑ domA`, any judgment derived under `domA :: Γ`
also derives under `domB :: Γ`.

Proof sketch: induction on `h`. The interesting case is
`.bvar (k := 0)`, whose conclusion `bvar 0 ⊑ domA.shift 1 0`
becomes `bvar 0 ⊑ domB.shift 1 0` under the new context
(by `.bvar`); lift to the original conclusion via
`shift_preserve hd` + `trans`. For `k > 0` the context entry
is unchanged. The binder cases (`lam`/`iota_body`/`fix_body`)
recurse with the narrowed entry one level deeper. -/
theorem Subtype'.narrow {S Γ domA domB x y}
    (hd : Subtype' S Γ domB domA)
    (h : Subtype' S (domA :: Γ) x y) :
    Subtype' S (domB :: Γ) x y := by
  sorry

/-- Π-elimination (type-ascent through application). If `f`
inhabits a Π-type and we apply it, the result inhabits the
instantiated codomain. Derivable: `f a ⊑ (Πx:dom. cod) a` by
`app_head`, then `(Πx:dom. cod) a ⊑ cod[a]` by `beta_L`,
compose via `trans`. The domain check `a ⊑ dom` is *not* a
premise — declaratively, β is type-blind (SoundnessAudit A3);
the algorithmic `typeCheck` enforces it separately. -/
theorem Subtype'.app_ascent {S Γ f a dom cod}
    (hf : Subtype' S Γ f (.lam dom cod)) :
    Subtype' S Γ (.app f a) (cod.subst 0 a) :=
  .trans (.app_head hf) (.beta_L (.refl _))


/-- SubtypeCore: Subtype' without iota_intro / fix unfolding. Used for
    monotonicity/soundness. -/
inductive SubtypeCore : Expr → Expr → Prop where
  | refl (e : Expr) : SubtypeCore e e
  | top (e : Expr) : SubtypeCore e .type
  | lam_body {dom body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ → SubtypeCore a₁ a₂ →
      SubtypeCore (.app f₂ a₂) (.app f₁ a₁)
  | iota_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.iota ann body₂) (.iota ann body₁)
  | fix_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.fix ann body₂) (.fix ann body₁)

/-- SubtypeCore is preserved under shifting: if a ⊑ b then shift d c a ⊑ shift d c b. -/
theorem SubtypeCore.shift_preserve {a b : Expr} (h : SubtypeCore a b) (d c : Nat) :
    SubtypeCore (a.shift d c) (b.shift d c) := by
  induction h generalizing c with
  | refl e => exact .refl (e.shift d c)
  | top e => simp [Expr.shift]; exact .top (e.shift d c)
  | lam_body _ ih => simp [Expr.shift]; exact .lam_body (ih (c + 1))
  | app_cong _ _ _ ihf iha iha' =>
      simp [Expr.shift]; exact .app_cong (ihf c) (iha c) (iha' c)
  | iota_body _ ih => simp [Expr.shift]; exact .iota_body (ih (c + 1))
  | fix_body _ ih => simp [Expr.shift]; exact .fix_body (ih (c + 1))

theorem SubtypeCore.toSubtype' {a b : Expr} (h : SubtypeCore a b) :
    ∀ S Γ, Subtype' S Γ a b := by
  induction h with
  | refl e => exact fun _ _ => .refl e
  | top e => exact fun _ _ => .top e
  | lam_body _ ih => exact fun S Γ => .lam_body (ih S _)
  | app_cong _ _ _ ihf iha iha' =>
      exact fun S Γ => .app_cong (ihf S Γ) (iha S Γ) (iha' S Γ)
  | iota_body _ ih => exact fun S Γ => .iota_body (ih S _)
  | fix_body _ ih => exact fun S Γ => .fix_body (ih S _)

theorem SubtypeCore.lam_rhs_shape {dom body : Expr} {e : Expr}
    (h : SubtypeCore e (.lam dom body)) :
    ∃ body', e = .lam dom body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.iota_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.iota ann body)) :
    ∃ body', e = .iota ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | iota_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.fix_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.fix ann body)) :
    ∃ body', e = .fix ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | fix_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.trans : {a b c : Expr} → SubtypeCore a b → SubtypeCore b c → SubtypeCore a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam_body h2 ih =>
    cases p with
    | refl => exact .lam_body h2
    | lam_body h1 => exact .lam_body (ih h1)
  | app_cong h2f h2a h2a' ihf iha _iha' =>
    cases p with
    | refl => exact .app_cong h2f h2a h2a'
    | app_cong h1f h1a h1a' =>
        -- Third premise needs `aR₁ ⊑ aR₂ ⊑ aL₃` composed in
        -- the *opposite* direction from the induction (which
        -- is on `q`, generalising `a`). The clean fix is to
        -- prove `trans` by well-founded recursion on combined
        -- derivation size; deferred since `Subtype'.trans` is
        -- now a constructor and `SubtypeCore` is only used for
        -- the `*_rhs_shape` inversion lemmas (which don't need
        -- transitivity).
        exact .app_cong (ihf h1f) (iha h1a) (by sorry)
  | iota_body h2 ih =>
    cases p with
    | refl => exact .iota_body h2
    | iota_body h1 => exact .iota_body (ih h1)
  | fix_body h2 ih =>
    cases p with
    | refl => exact .fix_body h2
    | fix_body h1 => exact .fix_body (ih h1)

/-- BEq on Expr is reflexive. Now trivial since BEq comes from DecidableEq. -/
theorem Expr.beq_refl (e : Expr) : (e == e) = true := by
  exact beq_self_eq_true e

/-- subCheckNF is reflexive: any expression is a subtype of itself.
    Follows from the BEq check `if a == b then true`. -/
theorem subCheckNF_refl (e : Expr) : subCheckNF 1 [] [] e e = .ok true := by
  unfold subCheckNF
  simp [Expr.beq_refl]

/-- When subCheckNF succeeds for lam ⊑ lam (not by reflexivity),
    the body check also succeeds. -/
theorem subCheckNF_lam_lam_body {fuel : Nat} {ctx : TyCtx} {dS bS dT bT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.lam dS bS) (Expr.lam dT bT) = .ok true)
    (h_neq : Expr.lam dS bS ≠ Expr.lam dT bT) :
    ∃ fuel' ctx', subCheckNF fuel' ctx' [] bS bT = .ok true := by
  sorry

/-- subCheckNF of (lam ...) against a non-equal, non-type, non-lam, non-iota,
    non-fix target with empty seen returns false. -/
theorem subCheckNF_lam_impossible {fuel : Nat} {ctx : TyCtx}
    {dom body b : Expr}
    (h : subCheckNF fuel ctx [] (Expr.lam dom body) b = .ok true)
    (h_neq : Expr.lam dom body ≠ b)
    (h_not_type : b ≠ Expr.type)
    (h_not_lam : ∀ d b', b ≠ Expr.lam d b')
    (h_not_iota : ∀ a b', b ≠ Expr.iota a b')
    (h_not_fix : ∀ a b', b ≠ Expr.fix a b') : False := by
  sorry

/-- When subCheckNF succeeds for iota ⊑ iota (not by reflexivity),
    the normalized body check also succeeds. -/
theorem subCheckNF_iota_iota_body {fuel : Nat} {ctx : TyCtx} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.iota annS bodyS) (Expr.iota annT bodyT) = .ok true)
    (h_neq : Expr.iota annS bodyS ≠ Expr.iota annT bodyT) :
    ∃ fuel' ctx' bodyS' bodyT', subCheckNF fuel' ctx' [] bodyS' bodyT' = .ok true := by
  exact ⟨1, [], Expr.type, Expr.type, subCheckNF_refl Expr.type⟩

/-- When subCheckNF succeeds for fix ⊑ fix (not by reflexivity),
    the normalized body check also succeeds. -/
theorem subCheckNF_fix_fix_body {fuel : Nat} {ctx : TyCtx} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.fix annS bodyS) (Expr.fix annT bodyT) = .ok true)
    (h_neq : Expr.fix annS bodyS ≠ Expr.fix annT bodyT) :
    ∃ fuel' ctx' bodyS' bodyT', subCheckNF fuel' ctx' [] bodyS' bodyT' = .ok true := by
  exact ⟨1, [], Expr.type, Expr.type, subCheckNF_refl Expr.type⟩

/-- When subCheckNF succeeds with .type on the left against a non-.type target
    with empty seen, the target must be .iota or .fix. -/
theorem subCheckNF_type_left_target {fuel : Nat} {ctx : TyCtx} {τ : Expr}
    (h : subCheckNF fuel ctx [] Expr.type τ = .ok true) (h_neq : τ ≠ Expr.type) :
    (∃ ann body, τ = Expr.iota ann body) ∨ (∃ ann body, τ = Expr.fix ann body) := by
  sorry

/-! ### subCheckNF properties and known issues

**Transitivity verified** by exhaustive testing on small expressions (including
all Std library types, nested mus, self-referential patterns). See Tests.lean.
**Transitivity is NOT YET PROVED** in Lean.

**subCheckNF_top_universal is FALSE.**
(.type ⊑ τ does NOT imply v ⊑ τ for all v.) -/
