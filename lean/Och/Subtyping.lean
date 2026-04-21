import Och.Syntax
import Och.Eval

/-!
# Och Subtyping (de Bruijn)

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

With de Bruijn indices, lambda/mu subtyping no longer needs variable renaming:
alpha-equivalent terms are syntactically identical, so body comparison is direct.

## Algorithmic checker

The algorithmic subtype checker is `NbE.subCheckVal` (`SubCheckVal.lean`),
operating on `Val`s produced by the NbE evaluator. The legacy Expr-domain
`subCheckNF`/`absEval` (formerly in `Eval.lean`) was retired once the
soundness target moved to the Val domain.
-/

open Expr

/-- Typing context: `Ctx[k]` is the declared type of `.bvar k`.
Stored in de Bruijn-index order (`Ctx[0]` = innermost binder).
Each entry's free bvars are relative to the *enclosing* context,
so looking up `.bvar k` yields a type that must be shifted by
`k+1` to be valid at the current depth. -/
abbrev Ctx := List Expr

/-- Coinductive hypotheses: `(d, a, b) ∈ S` means the goal
`a ⊑ b` was an ancestor in the derivation tree, recorded at
context depth `d` (the `Γ.length` at that point) by a
productive fix/iota unfold. The depth tag lets `.hyp` shift
the entry to the *current* depth on use, so a hypothesis
recorded under `Γ₀` can be used under any `Γ ⊇ Γ₀` without
the seen-set itself having to be rewritten through every
binder. Without the tag, `ctx_extend_at`'s binder cases are
unprovable (each entry would need a different shift cutoff
depending on where it's used; see DECISION-LOG 2026-04-18,
route (a)).

This is the Brandt-Henglein device for equirecursive
subtyping (SoundnessAudit A4); the algorithmic seen-set is
its level-domain realisation (entries are `Val × Val`,
intrinsically depth-independent). -/
abbrev Seen := List (Nat × Expr × Expr)

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
  assumed, shifted from its recorded depth `d` to the
  current depth `Γ.length`. The `d ≤ Γ.length` premise
  records that hypotheses are only used at-or-below the
  point they were introduced. Only the productive rules
  extend `S`. -/
  | hyp {S Γ d a b} :
      (d, a, b) ∈ S → d ≤ Γ.length →
      Subtype' S Γ (a.shift (Γ.length - d) 0)
                   (b.shift (Γ.length - d) 0)
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
  /-- Full ι-congruence (varying both annotation and body).
  Matches `SubV.iota_struct` and the algorithm's `.iota,.iota`
  structural arm: covariant on annotation, body at the target
  annotation. The same-annotation `.iota_body` is the special
  case `iota_cong (.refl _)`. Needed for `Equiv.subst_resp`
  (the existing `.iota_body` fixes the annotation, but
  substituting into `.iota ann body` changes both). -/
  | iota_cong {S Γ ann₁ ann₂ body₁ body₂} :
      Subtype' S Γ ann₁ ann₂ →
      Subtype' S (ann₂ :: Γ) body₁ body₂ →
      Subtype' S Γ (.iota ann₁ body₁) (.iota ann₂ body₂)
  | fix_cong {S Γ ann₁ ann₂ body₁ body₂} :
      Subtype' S Γ ann₁ ann₂ →
      Subtype' S (ann₂ :: Γ) body₁ body₂ →
      Subtype' S Γ (.fix ann₁ body₁) (.fix ann₂ body₂)
  /-- letE-congruence. Admissible via `.letE_L (.letE_R …)` +
  `subst_body` + `subst_resp`; having it as a constructor
  breaks the circularity in `Equiv.subst_resp`'s `.letE`
  case. The body is at `(val₂ :: Γ)` so `.bvar 0` ascends to
  the (target) bound value — singleton typing of the let. -/
  | letE_cong {S Γ val₁ val₂ body₁ body₂} :
      Subtype' S Γ val₁ val₂ →
      Subtype' S (val₂ :: Γ) body₁ body₂ →
      Subtype' S Γ (.letE val₁ body₁) (.letE val₂ body₂)
  /-- iotaIntro (value-sub, Cedille-style). The goal is added
  to `S` (tagged with the current depth) before recursing —
  both premises may use it. -/
  | iota_intro {S Γ a ann body} :
      Subtype' ((Γ.length, a, .iota ann body) :: S) Γ a ann →
      Subtype' ((Γ.length, a, .iota ann body) :: S) Γ
        a (body.subst 0 a) →
      Subtype' S Γ a (.iota ann body)
  /-- [unfoldIotaL]: `ι A. body ⊑ c` if its one-step unfolding
  is. The goal is added to `S` (productive unfold). -/
  | unfold_iota_L {S Γ ann body c} :
      Subtype' ((Γ.length, .iota ann body, c) :: S) Γ
        (body.subst 0 (.iota ann body)) c →
      Subtype' S Γ (.iota ann body) c
  /-- [unfoldIotaR]: `a ⊑ ι A. body` if `a ⊑ body[self := ι A. body]`.
  Symmetric to `unfold_iota_L`; together they give
  `ι A. body ≡ body[self := ι A. body]` (the ι fixpoint
  equation). `iota_intro` is the *algorithmic* form (it
  additionally checks `a ⊑ A`, which the algorithm needs
  for the seen-set discipline) but is strictly stronger
  than this rule; both are sound since semantically
  `ι A. body` *is* its one-step unfolding. -/
  | unfold_iota_R {S Γ a ann body} :
      Subtype' ((Γ.length, a, .iota ann body) :: S) Γ
        a (body.subst 0 (.iota ann body)) →
      Subtype' S Γ a (.iota ann body)
  /-- [unfoldFixL]: `fix A. body ⊑ c` if `body[self := fix A. body] ⊑ c`. -/
  | unfold_fix_L {S Γ ann body c} :
      Subtype' ((Γ.length, .fix ann body, c) :: S) Γ
        (body.subst 0 (.fix ann body)) c →
      Subtype' S Γ (.fix ann body) c
  /-- [unfoldFixR]: `a ⊑ fix A. body` if `a ⊑ body[self := fix A. body]`.
      The previous `[fix-ann]` (`a ⊑ A → a ⊑ fix A. body`) was removed:
      `A` is the type of the recursion variable, not an upper bound on
      the fixpoint, so with `A = Type` it admitted `Nat ⊑ dBool`. -/
  | unfold_fix_R {S Γ a ann body} :
      Subtype' ((Γ.length, a, .fix ann body) :: S) Γ
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
  | hyp hin hle => exact .hyp (hsub _ hin) hle
  | refl e => exact .refl e
  | top e => exact .top e
  | trans _ _ ih1 ih2 => exact .trans (ih1 hsub) (ih2 hsub)
  | bvar h => exact .bvar h
  | lam _ _ ihd ihb => exact .lam (ihd hsub) (ihb hsub)
  | app_cong _ _ _ ihf iha iha' =>
      exact .app_cong (ihf hsub) (iha hsub) (iha' hsub)
  | iota_body _ ih => exact .iota_body (ih hsub)
  | fix_body _ ih => exact .fix_body (ih hsub)
  | iota_cong _ _ ihA ihB => exact .iota_cong (ihA hsub) (ihB hsub)
  | fix_cong _ _ ihA ihB => exact .fix_cong (ihA hsub) (ihB hsub)
  | letE_cong _ _ ihV ihB => exact .letE_cong (ihV hsub) (ihB hsub)
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
  | unfold_iota_R _ ih =>
      refine .unfold_iota_R (ih ?_)
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

/-- `.hyp` specialised to same-depth use: an entry recorded
at the *current* depth needs no shift. This is the form
the algorithmic seen-bridge uses (`subCheckVal_subV` always
records and uses at the same `Γ`). -/
theorem Subtype'.hyp_here {S} {Γ : Ctx} {a b}
    (h : (Γ.length, a, b) ∈ S) : Subtype' S Γ a b := by
  have := Subtype'.hyp h (Nat.le_refl _)
  simpa using this

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

/-- Application elimination: if `f` inhabits a Π-type, applying
it lands in the (substituted) codomain. The standard elim rule,
derived as `app_head hf ; beta_L`. Used by `tyInfer_sound .app`. -/
theorem Subtype'.app_elim {S Γ f a A B}
    (hf : Subtype' S Γ f (.lam A B)) :
    Subtype' S Γ (.app f a) (B.subst 0 a) :=
  (app_head hf).trans (.beta_L (.refl _))

/-- Multi-step head reduction under a spine, then continue. The
common pattern when the head is `(λx. …) v w …`. -/
theorem Subtype'.beta_head {S Γ dom body arg a c}
    (h : Subtype' S Γ (.app (body.subst 0 arg) a) c) :
    Subtype' S Γ (.app (.app (.lam dom body) arg) a) c :=
  .trans (.app_head (.beta_L (.refl _))) h

-- `Subtype'.shift_preserve` removed: its uniform-cutoff
-- statement was wrong (Γ entries are at staggered depths;
-- entry `k` needs cutoff `c - k - 1`). The correct form is
-- `ctx_extend_at` below, which is what `narrow_at` actually
-- uses. `Equiv.shift` (SoundnessProof.lean) states the
-- `∀ Γ`-quantified version it needs locally.

/-- The per-entry transform `ctx_extend_at` applies to the
seen-set when inserting `m` new context entries between a
prefix and a suffix of length `g`: an entry recorded at
depth `d` becomes recorded at depth `d + m`, with its
expressions shifted by `m` at cutoff `d - g` (the prefix
length at the point of recording). Crucially this depends
only on `m` and `g`, *not* on the current `Γpfx`, so
`ctx_extend_at`'s binder cases (which grow `Γpfx`) see the
same map in IH and goal. -/
def Seen.extendEntry (m g : Nat) :
    Nat × Expr × Expr → Nat × Expr × Expr :=
  fun (d, x, y) => (d + m, x.shift m (d - g), y.shift m (d - g))

/-- The shift-commutation identity behind `ctx_extend_at`'s
`.hyp` case: shifting from recorded depth `d` to use-depth
`c+g` (the `.hyp` shift) and *then* shifting by `m` at
cutoff `c` (the context-extension shift) equals first
applying `extendEntry`'s per-entry shift (by `m` at cutoff
`d-g`) and *then* the `.hyp` shift in the extended context.
Holds for all `d ≤ c+g`; the two regimes `d ≤ g` (entry
recorded inside the fixed suffix; per-entry cutoff is `0`)
and `d > g` (entry recorded inside the prefix; per-entry
cutoff is `d-g > 0`) close via different `shift_shift_*`
lemmas but both are syntactic. -/
private theorem Seen.hyp_shift_commute (σ : Expr) (m c g d : Nat)
    (hd : d ≤ c + g) :
    (σ.shift (c + g - d) 0).shift m c
      = (σ.shift m (d - g)).shift (c + g - d) 0 := by
  by_cases hdg : d ≤ g
  · have hk : d - g = 0 := Nat.sub_eq_zero_of_le hdg
    rw [hk,
        Expr.shift_shift_between σ m (c+g-d) 0 c
          (Nat.zero_le _) (by omega),
        Expr.shift_shift_same σ (c+g-d) m 0,
        Nat.add_comm]
  · have hdg' : g < d := Nat.lt_of_not_le hdg
    have hkn : (d - g) + (c + g - d) = c := by omega
    have h := Expr.shift_shift_comm_gen σ m (d - g) (c + g - d)
    rw [hkn] at h
    exact h

/-- Shift each entry of a context *prefix* at the cutoff
appropriate to its position: entry `i` (which lives at depth
`i+1` relative to the prefix tail) is shifted at cutoff
`(prefix.length − 1 − i)`. After `Γpfx.shiftPrefix d` is
prepended to the new entries `Δ ++ Γtail`, the resulting
context is `Γpfx`-shaped but with each entry's internal
references past the original boundary moved by `d`. -/
def Ctx.shiftPrefix (Γpfx : Ctx) (d : Nat) : Ctx :=
  Γpfx.mapIdx (fun i τ => τ.shift d (Γpfx.length - 1 - i))

theorem Ctx.shiftPrefix_length (Γpfx : Ctx) (d : Nat) :
    (Γpfx.shiftPrefix d).length = Γpfx.length := by
  simp [Ctx.shiftPrefix, List.length_mapIdx]

theorem Ctx.shiftPrefix_nil (d : Nat) :
    Ctx.shiftPrefix [] d = [] := rfl

theorem Ctx.shiftPrefix_cons (τ : Expr) (Γpfx : Ctx) (d : Nat) :
    Ctx.shiftPrefix (τ :: Γpfx) d
    = τ.shift d Γpfx.length :: Ctx.shiftPrefix Γpfx d := by
  simp only [Ctx.shiftPrefix, List.mapIdx_cons, List.length_cons,
             Nat.succ_sub_one, Nat.sub_zero, Nat.sub_sub,
             Nat.add_comm 1]

/-- General context-extension (de Bruijn weakening): a
derivation at `Γpfx ++ Γ` lifts to one at
`Γpfx.shiftPrefix |Δ| ++ Δ ++ Γ`, with both endpoints
shifted by `|Δ|` at cutoff `|Γpfx|`, and each seen-entry
shifted at *its own* recorded prefix-cutoff via
`Seen.extendEntry`.

The seen-map depends only on `|Δ|` and `|Γ|` (not `|Γpfx|`),
so the 6 binder cases — which recurse at `(τ :: Γpfx)` —
have IH and goal seen-sets that coincide on the nose. This
is precisely what the depth tag buys: under the old
untagged `Seen`, the conclusion seen-set was
`S.map (shift |Δ| |Γpfx|)` and the binder cases were
unprovable (DECISION-LOG 2026-04-18 route (a)). -/
theorem Subtype'.ctx_extend_at {Γ} (Δ : Ctx) :
    ∀ {S ΓA a b}, Subtype' S ΓA a b →
    ∀ Γpfx, ΓA = Γpfx ++ Γ →
    Subtype'
      (S.map (Seen.extendEntry Δ.length Γ.length))
      (Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ)
      (a.shift Δ.length Γpfx.length)
      (b.shift Δ.length Γpfx.length) := by
  intro S ΓA a b h
  induction h with
  | @hyp S' Γ' d a' b' hin hle =>
    intro Γpfx hpfx
    subst hpfx
    -- Mapped entry: `(d+|Δ|, a'.shift |Δ| (d-|Γ|), …) ∈ S'.map f`.
    have hin' : (d + Δ.length,
                 a'.shift Δ.length (d - Γ.length),
                 b'.shift Δ.length (d - Γ.length))
                ∈ S'.map (Seen.extendEntry Δ.length Γ.length) :=
      List.mem_map_of_mem _ hin
    -- `.hyp` at the extended context (length `c+|Δ|+g`):
    have hle' : d + Δ.length
        ≤ (Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length := by
      simp only [List.length_append, Ctx.shiftPrefix_length,
                 List.length_append] at hle ⊢
      omega
    have hb := Subtype'.hyp hin' hle'
    -- Reduce `.hyp`'s shift amount to `c+g-d` and the goal's
    -- `|Γpfx ++ Γ|` to `c+g`:
    simp only [List.length_append, Ctx.shiftPrefix_length] at hb hle ⊢
    have hlen :
        Γpfx.length + Δ.length + Γ.length - (d + Δ.length)
          = Γpfx.length + Γ.length - d := by omega
    rw [hlen] at hb
    rw [Seen.hyp_shift_commute a' Δ.length Γpfx.length
          Γ.length d hle,
        Seen.hyp_shift_commute b' Δ.length Γpfx.length
          Γ.length d hle]
    exact hb
  | refl e => intro Γpfx _; exact .refl _
  | top e => intro Γpfx _; exact .top _
  | trans _ _ ih1 ih2 =>
    intro Γpfx hpfx
    exact .trans (ih1 Γpfx hpfx) (ih2 Γpfx hpfx)
  | @bvar S' Γ' k τ hget =>
    intro Γpfx hpfx
    subst hpfx
    by_cases hk : k < Γpfx.length
    · -- `k` is in the prefix; entry stays at position `k`
      -- but its content is shifted at cutoff
      -- `(Γpfx.length-1-k)`.
      simp only [Expr.shift, if_pos hk]
      have hgetP : Γpfx.get? k = some τ := by
        rwa [List.get?_eq_getElem?,
             List.getElem?_append_left hk,
             ← List.get?_eq_getElem?] at hget
      have hgetN :
          (Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).get? k
            = some (τ.shift Δ.length (Γpfx.length - 1 - k)) := by
        rw [List.get?_eq_getElem?,
            List.getElem?_append_left
              (by simp [List.length_append,
                        Ctx.shiftPrefix_length]; omega),
            List.getElem?_append_left
              (by simp [Ctx.shiftPrefix_length]; exact hk)]
        simp only [Ctx.shiftPrefix, List.getElem?_mapIdx]
        rw [← List.get?_eq_getElem?, hgetP]; rfl
      have hτeq :
          (τ.shift Δ.length (Γpfx.length - 1 - k)).shift (k+1) 0
            = (τ.shift (k+1) 0).shift Δ.length Γpfx.length := by
        have hcg := Expr.shift_shift_comm_gen τ Δ.length
                      (Γpfx.length - 1 - k) (k+1)
        rw [show (Γpfx.length - 1 - k) + (k + 1)
              = Γpfx.length from by omega] at hcg
        exact hcg.symm
      have hb := Subtype'.bvar
        (S := S'.map (Seen.extendEntry Δ.length Γ.length))
        hgetN
      rw [hτeq] at hb; exact hb
    · -- `k` is in `Γ`; entry moves to position `k + |Δ|`,
      -- content unchanged.
      simp only [Expr.shift, if_neg hk]
      have hk' : Γpfx.length ≤ k := Nat.le_of_not_lt hk
      have hgetT : Γ.get? (k - Γpfx.length) = some τ := by
        rwa [List.get?_eq_getElem?,
             List.getElem?_append_right hk',
             ← List.get?_eq_getElem?] at hget
      have hgetN :
          (Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).get? (k + Δ.length)
            = some τ := by
        rw [List.get?_eq_getElem?,
            List.getElem?_append_right
              (by rw [List.length_append, Ctx.shiftPrefix_length];
                  omega),
            List.length_append, Ctx.shiftPrefix_length,
            ← List.get?_eq_getElem?]
        rw [show k + Δ.length - (Γpfx.length + Δ.length)
             = k - Γpfx.length from by omega]
        exact hgetT
      have hb := Subtype'.bvar
        (S := S'.map (Seen.extendEntry Δ.length Γ.length))
        hgetN
      rw [show (τ.shift (k+1) 0).shift Δ.length Γpfx.length
           = τ.shift (k + Δ.length + 1) 0 from by
        rw [Expr.shift_shift_between τ Δ.length (k+1) 0
              Γpfx.length (Nat.zero_le _) (by omega)]
        congr 1; omega]
      exact hb
  | @lam S' Γ' dA dB bA bB _ _ ihD ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .lam (ihD Γpfx rfl) ?_
    have hb := ihB (dB :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | app_cong _ _ _ ihf iha iha' =>
    intro Γpfx hpfx
    simp only [Expr.shift]
    exact .app_cong (ihf Γpfx hpfx) (iha Γpfx hpfx) (iha' Γpfx hpfx)
  | @iota_body S' Γ' ann b₁ b₂ _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .iota_body ?_
    have hb := ih (ann :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | @fix_body S' Γ' ann b₁ b₂ _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .fix_body ?_
    have hb := ih (ann :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | @iota_cong S' Γ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .iota_cong (ihA Γpfx rfl) ?_
    have hb := ihB (a₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | @fix_cong S' Γ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .fix_cong (ihA Γpfx rfl) ?_
    have hb := ihB (a₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | @letE_cong S' Γ' v₁ v₂ b₁ b₂ _ _ ihV ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .letE_cong (ihV Γpfx rfl) ?_
    have hb := ihB (v₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simpa only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] using hb
  | @iota_intro S' Γ' a' ann body _ _ ih1 ih2 =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    have hhead :
        Seen.extendEntry Δ.length Γ.length
          ((Γpfx ++ Γ).length, a', .iota ann body)
        = ((Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length,
           a'.shift Δ.length Γpfx.length,
           (Expr.iota ann body).shift Δ.length Γpfx.length) := by
      simp [Seen.extendEntry, List.length_append,
            Ctx.shiftPrefix_length, Expr.shift]; omega
    refine .iota_intro ?_ ?_
    · have := ih1 Γpfx rfl
      simp only [List.map_cons, hhead] at this
      simpa [Expr.shift] using this
    · have := ih2 Γpfx rfl
      simp only [List.map_cons, hhead] at this
      simpa [Expr.shift, Expr.subst_shift_swap] using this
  | @unfold_iota_L S' Γ' ann body c' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    have hhead :
        Seen.extendEntry Δ.length Γ.length
          ((Γpfx ++ Γ).length, .iota ann body, c')
        = ((Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length,
           (Expr.iota ann body).shift Δ.length Γpfx.length,
           c'.shift Δ.length Γpfx.length) := by
      simp [Seen.extendEntry, List.length_append,
            Ctx.shiftPrefix_length, Expr.shift]; omega
    refine .unfold_iota_L ?_
    have := ih Γpfx rfl
    simp only [List.map_cons, hhead] at this
    simpa [Expr.shift, Expr.subst_shift_swap] using this
  | @unfold_fix_L S' Γ' ann body c' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    have hhead :
        Seen.extendEntry Δ.length Γ.length
          ((Γpfx ++ Γ).length, .fix ann body, c')
        = ((Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length,
           (Expr.fix ann body).shift Δ.length Γpfx.length,
           c'.shift Δ.length Γpfx.length) := by
      simp [Seen.extendEntry, List.length_append,
            Ctx.shiftPrefix_length, Expr.shift]; omega
    refine .unfold_fix_L ?_
    have := ih Γpfx rfl
    simp only [List.map_cons, hhead] at this
    simpa [Expr.shift, Expr.subst_shift_swap] using this
  | @unfold_fix_R S' Γ' a' ann body _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    have hhead :
        Seen.extendEntry Δ.length Γ.length
          ((Γpfx ++ Γ).length, a', .fix ann body)
        = ((Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length,
           a'.shift Δ.length Γpfx.length,
           (Expr.fix ann body).shift Δ.length Γpfx.length) := by
      simp [Seen.extendEntry, List.length_append,
            Ctx.shiftPrefix_length, Expr.shift]; omega
    refine .unfold_fix_R ?_
    have := ih Γpfx rfl
    simp only [List.map_cons, hhead] at this
    simpa [Expr.shift, Expr.subst_shift_swap] using this
  | @unfold_iota_R S' Γ' a' ann body _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    have hhead :
        Seen.extendEntry Δ.length Γ.length
          ((Γpfx ++ Γ).length, a', .iota ann body)
        = ((Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ).length,
           a'.shift Δ.length Γpfx.length,
           (Expr.iota ann body).shift Δ.length Γpfx.length) := by
      simp [Seen.extendEntry, List.length_append,
            Ctx.shiftPrefix_length, Expr.shift]; omega
    refine .unfold_iota_R ?_
    have := ih Γpfx rfl
    simp only [List.map_cons, hhead] at this
    simpa [Expr.shift, Expr.subst_shift_swap] using this
  | @beta_L S' Γ' dom body arg b' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .beta_L ?_
    have := ih Γpfx rfl
    simpa [Expr.subst_shift_swap] using this
  | @beta_R S' Γ' a' dom body arg _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .beta_R ?_
    have := ih Γpfx rfl
    simpa [Expr.subst_shift_swap] using this
  | @letE_L S' Γ' val body b' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .letE_L ?_
    have := ih Γpfx rfl
    simpa [Expr.subst_shift_swap] using this
  | @letE_R S' Γ' a' val body _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .letE_R ?_
    have := ih Γpfx rfl
    simpa [Expr.subst_shift_swap] using this
  | asc_L _ ih =>
    intro Γpfx hpfx
    simp only [Expr.shift]
    exact .asc_L (ih Γpfx hpfx)
  | asc_R _ ih =>
    intro Γpfx hpfx
    simp only [Expr.shift]
    exact .asc_R (ih Γpfx hpfx)

/-- Context-extension at the bottom (`Γpfx = []`): a
derivation at `Γ` lifts to one at `Δ ++ Γ`, both sides
shifted by `|Δ|` at cutoff `0`. The seen-set is mapped
through `Seen.extendEntry`; the common case `S = []`
gives an empty conclusion seen-set, which `narrow_at`'s
`.bvar` case then weakens to whatever `S` it needs. -/
theorem Subtype'.ctx_extend {S Γ a b} (Δ : Ctx)
    (h : Subtype' S Γ a b) :
    Subtype' (S.map (Seen.extendEntry Δ.length Γ.length))
      (Δ ++ Γ) (a.shift Δ.length 0) (b.shift Δ.length 0) := by
  have h' := ctx_extend_at (Γ := Γ) Δ h [] rfl
  simpa only [List.length_nil, Ctx.shiftPrefix_nil,
              List.nil_append] using h'

/-- Looking up the same prefix position in `Γ' ++ A :: Γ` and
`Γ' ++ B :: Γ` gives the same result when the position is in
the prefix or strictly past the head; only `k = Γ'.length`
sees the changed entry. -/
private theorem List.get?_append_replace_ne
    {α} {Γ' : List α} {A B : α} {Γ : List α} {k : Nat} {τ : α}
    (hk : k ≠ Γ'.length)
    (hget : (Γ' ++ A :: Γ).get? k = some τ) :
    (Γ' ++ B :: Γ).get? k = some τ := by
  simp only [List.get?_eq_getElem?] at hget ⊢
  rcases Nat.lt_or_ge k Γ'.length with hlt | hge
  · rwa [List.getElem?_append_left hlt] at hget ⊢
  · have hgt : Γ'.length < k := Nat.lt_of_le_of_ne hge (Ne.symm hk)
    rw [List.getElem?_append_right (Nat.le_of_lt hgt)] at hget ⊢
    have h1 : 1 ≤ k - Γ'.length := Nat.le_sub_of_add_le (by omega)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h1
    rw [hj, Nat.add_comm] at hget ⊢
    simpa using hget

private theorem List.get?_append_replace_eq
    {α} {Γ' : List α} {A B : α} {Γ : List α} {τ : α}
    (hget : (Γ' ++ A :: Γ).get? Γ'.length = some τ) :
    τ = A ∧ (Γ' ++ B :: Γ).get? Γ'.length = some B := by
  simp only [List.get?_eq_getElem?,
             List.getElem?_append_right (Nat.le_refl _),
             Nat.sub_self, List.getElem?_cons_zero,
             Option.some.injEq] at hget ⊢
  exact ⟨hget.symm, trivial⟩

/-- General context narrowing at an arbitrary depth: replacing
the entry at position `Γ'.length` (i.e., the head of the
`domA :: Γ` suffix) with a subtype `domB ⊑ domA` preserves
derivations. The prefix `Γ'` is the stack of binders
introduced *after* the narrowed one; the head-only
`Subtype'.narrow` is `Γ' := []`.

The contravariant premise `hd` is over the *empty*
seen-set: at `.bvar` with `k = Γ'.length`, `ctx_extend`
lifts `hd` to the inner context (its conclusion seen-set
is `[].map _ = []`), then `weaken` from `[]` to `S` is
vacuous. (The earlier formulation allowed an arbitrary
closed `S₀ ⊆ S`; with depth-tagged `Seen` the
"closed-so-shift-is-id" trick no longer applies, and all
SoundnessProof.lean callers pass `[]` anyway.) -/
theorem Subtype'.narrow_at {Γ domA domB}
    (hd : Subtype' [] Γ domB domA) :
    ∀ {S Δ x y}, Subtype' S Δ x y →
    ∀ Γ', Δ = Γ' ++ domA :: Γ →
    Subtype' S (Γ' ++ domB :: Γ) x y := by
  intro S Δ x y h
  induction h with
  | @hyp S' Δ' d a' b' hin hle =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      simp only [hlen]
      exact .hyp hin (hlen ▸ hle)
  | refl e => exact fun _ _ => .refl e
  | top e => exact fun _ _ => .top e
  | trans _ _ ih1 ih2 =>
      exact fun Γ' hΔ => .trans (ih1 Γ' hΔ) (ih2 Γ' hΔ)
  | @bvar S' Δ' k τ hget =>
      intro Γ' hΔ
      subst hΔ
      by_cases hk : k = Γ'.length
      · -- k = Γ'.length: the narrowed entry. `τ = domA`; new
        -- context gives `domB`. Bridge via `.trans` + lifted
        -- `hd` (over `[]`, then weakened to `S'`).
        subst hk
        obtain ⟨hτ, hgetB⟩ :=
          List.get?_append_replace_eq (B := domB) hget
        subst hτ
        refine .trans (.bvar hgetB) ?_
        have hext := (ctx_extend (S := []) (Γ' ++ [domB]) hd).weaken
          (S' := S') (fun p hp => absurd hp (List.not_mem_nil p))
        simpa [List.length_append, List.append_assoc,
               List.singleton_append, List.cons_append] using hext
      · exact .bvar (List.get?_append_replace_ne hk hget)
  | @lam S' Δ' dA dB bA bB _ _ ihd ihb =>
      intro Γ' hΔ
      subst hΔ
      exact .lam (ihd Γ' rfl)
        (ihb (dB :: Γ') (List.cons_append .. ▸ rfl))
  | app_cong _ _ _ ihf iha iha' =>
      exact fun Γ' hΔ =>
        .app_cong (ihf Γ' hΔ) (iha Γ' hΔ) (iha' Γ' hΔ)
  | @iota_body S' Δ' ann b₁ b₂ _ ih =>
      intro Γ' hΔ
      subst hΔ
      exact .iota_body
        (ih (ann :: Γ') (List.cons_append .. ▸ rfl))
  | @fix_body S' Δ' ann b₁ b₂ _ ih =>
      intro Γ' hΔ
      subst hΔ
      exact .fix_body
        (ih (ann :: Γ') (List.cons_append .. ▸ rfl))
  | @iota_cong S' Δ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
      intro Γ' hΔ
      subst hΔ
      exact .iota_cong (ihA Γ' rfl)
        (ihB (a₂ :: Γ') (List.cons_append .. ▸ rfl))
  | @fix_cong S' Δ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
      intro Γ' hΔ
      subst hΔ
      exact .fix_cong (ihA Γ' rfl)
        (ihB (a₂ :: Γ') (List.cons_append .. ▸ rfl))
  | @letE_cong S' Δ' v₁ v₂ b₁ b₂ _ _ ihV ihB =>
      intro Γ' hΔ
      subst hΔ
      exact .letE_cong (ihV Γ' rfl)
        (ihB (v₂ :: Γ') (List.cons_append .. ▸ rfl))
  | @iota_intro S' Δ' a' ann body _ _ ih1 ih2 =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      have h1 := ih1 Γ' rfl
      have h2 := ih2 Γ' rfl
      rw [hlen] at h1 h2
      exact .iota_intro h1 h2
  | @unfold_iota_L S' Δ' ann body c' _ ih =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      have h1 := ih Γ' rfl
      rw [hlen] at h1
      exact .unfold_iota_L h1
  | @unfold_fix_L S' Δ' ann body c' _ ih =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      have h1 := ih Γ' rfl
      rw [hlen] at h1
      exact .unfold_fix_L h1
  | @unfold_fix_R S' Δ' a' ann body _ ih =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      have h1 := ih Γ' rfl
      rw [hlen] at h1
      exact .unfold_fix_R h1
  | @unfold_iota_R S' Δ' a' ann body _ ih =>
      intro Γ' hΔ
      subst hΔ
      have hlen : (Γ' ++ domA :: Γ).length
                  = (Γ' ++ domB :: Γ).length := by simp
      have h1 := ih Γ' rfl
      rw [hlen] at h1
      exact .unfold_iota_R h1
  | beta_L _ ih => exact fun Γ' hΔ => .beta_L (ih Γ' hΔ)
  | beta_R _ ih => exact fun Γ' hΔ => .beta_R (ih Γ' hΔ)
  | letE_L _ ih => exact fun Γ' hΔ => .letE_L (ih Γ' hΔ)
  | letE_R _ ih => exact fun Γ' hΔ => .letE_R (ih Γ' hΔ)
  | asc_L _ ih => exact fun Γ' hΔ => .asc_L (ih Γ' hΔ)
  | asc_R _ ih => exact fun Γ' hΔ => .asc_R (ih Γ' hΔ)

/-- Head-position context narrowing: replacing `Γ`'s innermost
binder type `domA` with a subtype `domB ⊑ domA` preserves
derivations. After the A6 revert (DECISION-LOG 2026-04-18)
the algorithm's `.lam,.lam` arm pushes `domA` while
`Subtype'.lam` pushes `domB`, so the `SubV → Subtype'`
bridge's `.lam` case needs exactly this. The `hd` premise
is at the empty seen-set; `subCheckVal_sound_open` (the
sole caller, via `SubV_to_Subtype'`) supplies it at `[]`. -/
theorem Subtype'.narrow {S Γ domA domB x y}
    (hd : Subtype' [] Γ domB domA)
    (h : Subtype' S (domA :: Γ) x y) :
    Subtype' S (domB :: Γ) x y :=
  narrow_at hd h [] rfl

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

/-- Well-closedness invariant for a seen-set: every entry's
expressions are closed at their recorded depth. This is the
natural invariant on `S` throughout a derivation that started
with `S = []`: every rule that extends `S` (the four
`unfold_*_{L,R}`, `iota_intro`) records `(|Γ|, a, b)` where
`a, b` live at `Γ` — hence closed at `|Γ|`. The other rules
propagate `S` unchanged.

`wellClosed` is needed for `Subtype'.shift_above` (below): its
`.hyp` case at the shifted form requires the recorded `x, y`
to be closed at their recorded depth, so that after the
`.hyp` rule's built-in `(|Γ|-d)`-shift they land at depth
`|Γ|` and the outer `shift n |Γ|` is identity.

This invariant is what `Equiv.shift`'s nil-Γ case (`SoundnessProof.lean`)
ultimately needs; see DECISION-LOG 2026-04-21 for the
threading plan. -/
def Seen.wellClosed (S : Seen) : Prop :=
  ∀ d a b, (d, a, b) ∈ S → a.closedAt d = true ∧ b.closedAt d = true

theorem Seen.wellClosed_nil : Seen.wellClosed [] := by
  intro _ _ _ h; exact absurd h (List.not_mem_nil _)

theorem Seen.wellClosed_cons {d a b S}
    (ha : a.closedAt d = true) (hb : b.closedAt d = true)
    (hS : Seen.wellClosed S) :
    Seen.wellClosed ((d, a, b) :: S) := by
  intro d' a' b' hmem
  cases hmem with
  | head => exact ⟨ha, hb⟩
  | tail _ h => exact hS _ _ _ h

/-- A context is well-formed if each entry at position `k` is
closed at `|Γ|-k-1` — i.e., entry `k` only references Γ
entries at strictly smaller indices (further in the tail).
This is the standard de Bruijn context well-formedness
condition. Under well-formedness, `τ.shift (k+1) 0` is closed
at `|Γ|`, so an outer shift by `n` at cutoff `|Γ|` is the
identity — the basis of the `.bvar` case of `Subtype'.shift_above`.

Like `Seen.wellClosed`, this is NOT preserved by all `Subtype'`
constructors: `.lam`'s body premise at `(dB :: Γ)` requires
`dB.closedAt |Γ|`, which isn't derivable from `.lam`'s premise
alone. For derivations rooted at well-scoped source terms (the
uses this matters for), the invariant holds as a side
condition the caller maintains. -/
def Ctx.wellFormed (Γ : Ctx) : Prop :=
  ∀ k τ, Γ.get? k = some τ → τ.closedAt (Γ.length - k - 1) = true

theorem Ctx.wellFormed_nil : Ctx.wellFormed [] := by
  intro _ _ h; simp at h

theorem Ctx.wellFormed_cons {τ : Expr} {Γ : Ctx}
    (hτ : τ.closedAt Γ.length = true) (hΓ : Ctx.wellFormed Γ) :
    Ctx.wellFormed (τ :: Γ) := by
  intro k τ' hget
  cases k with
  | zero =>
    simp only [List.get?_cons_zero, Option.some.injEq] at hget
    subst hget
    simp only [List.length_cons, Nat.sub_zero, Nat.succ_sub_one]
    exact hτ
  | succ m =>
    simp only [List.get?_cons_succ] at hget
    have h := hΓ m τ' hget
    simp only [List.length_cons]
    have : Γ.length + 1 - (m + 1) - 1 = Γ.length - m - 1 := by omega
    rw [this]
    exact h

/-- The `.hyp` case of the generalised shift-above-context
lemma — the supposed "impossibility wall" of `Equiv.shift`'s
nil-Γ — is actually provable as a standalone lemma using
`Seen.wellClosed`. Given
a hypothesis application at depth d, the recorded pair (x, y)
is closed at d by `wellClosed`; after the `.hyp` rule's
built-in (|Γ|-d)-shift, both sides are closed at |Γ|, so an
outer `shift n |Γ|` is the identity. This demonstrates the
closedness-propagation route is sound; the full
`shift_above` theorem requires wellformedness propagation
through `.lam` / productive-unfold cases, which needs
closedness side-conditions on binder rules (an invasive
Subtype' schema change).

The `shift_above_closed` / `shift_nil_closed` variants below
are the practical versions for callers that supply closedness
directly. -/
theorem Subtype'.hyp_shift_above {S Γ d x y n}
    (hS : Seen.wellClosed S)
    (hin : (d, x, y) ∈ S) (hle : d ≤ Γ.length) :
    Subtype' S Γ
      ((x.shift (Γ.length - d) 0).shift n Γ.length)
      ((y.shift (Γ.length - d) 0).shift n Γ.length) := by
  obtain ⟨hxcl, hycl⟩ := hS d x y hin
  have hxcl' : (x.shift (Γ.length - d) 0).closedAt Γ.length = true := by
    have := Expr.shift_closedAt x d (Γ.length - d) 0 (Nat.zero_le _) hxcl
    have hk : d + (Γ.length - d) = Γ.length := by omega
    rw [hk] at this; exact this
  have hycl' : (y.shift (Γ.length - d) 0).closedAt Γ.length = true := by
    have := Expr.shift_closedAt y d (Γ.length - d) 0 (Nat.zero_le _) hycl
    have hk : d + (Γ.length - d) = Γ.length := by omega
    rw [hk] at this; exact this
  rw [Expr.shift_of_closedAt hxcl' n (Nat.le_refl _),
      Expr.shift_of_closedAt hycl' n (Nat.le_refl _)]
  exact Subtype'.hyp hin hle

/-- The `.bvar` case of `shift_above`, standalone. Under
`Ctx.wellFormed`, `τ` at position `k` is closed at
`(|Γ|-k-1)`; after the `.bvar` rule's `(k+1)`-shift, it's
closed at `|Γ|`, so an outer `shift n |Γ|` is identity. -/
theorem Subtype'.bvar_shift_above {S Γ k τ n}
    (hΓ : Ctx.wellFormed Γ)
    (hget : Γ.get? k = some τ) :
    Subtype' S Γ ((Expr.bvar k).shift n Γ.length)
                  ((τ.shift (k+1) 0).shift n Γ.length) := by
  have hklt : k < Γ.length := by
    rw [List.get?_eq_getElem?] at hget
    exact (List.getElem?_eq_some_iff.mp hget).1
  simp only [Expr.shift, decide_eq_true_eq, if_pos hklt]
  have hτcl := hΓ k τ hget
  have hτshiftcl : (τ.shift (k+1) 0).closedAt Γ.length = true := by
    have := Expr.shift_closedAt τ (Γ.length - k - 1) (k+1) 0
      (Nat.zero_le _) hτcl
    have hk : Γ.length - k - 1 + (k + 1) = Γ.length := by omega
    rw [hk] at this; exact this
  rw [Expr.shift_of_closedAt hτshiftcl n (Nat.le_refl _)]
  exact Subtype'.bvar hget

/-- A trivial consequence of `Subtype'.shift_above`: when both
endpoints are already closed at `|Γ|`, the shift is the
identity so the derivation is preserved without inspection.

This is the *useful* specialisation for top-level uses
(closed terms under empty context) — where the `.hyp` case
of `shift_above` needs its `wellClosed`/`wellFormed` proofs,
this direct form just rewrites via `shift_of_closedAt` and
returns `h` unchanged.

The `Equiv.shift` nil-Γ case is exactly this form: `e₁`, `e₂`
are closed-at-0 in all observed callers (substituends in
`concEval_equiv` come from `concEval` of closed terms), so a
closedness-carrying variant of `Equiv` would make `Equiv.shift`
trivially provable via this helper. -/
theorem Subtype'.shift_above_closed {S Γ a b} (n : Nat)
    (ha : a.closedAt Γ.length = true)
    (hb : b.closedAt Γ.length = true)
    (h : Subtype' S Γ a b) :
    Subtype' S Γ (a.shift n Γ.length) (b.shift n Γ.length) := by
  rw [Expr.shift_of_closedAt ha n (Nat.le_refl _),
      Expr.shift_of_closedAt hb n (Nat.le_refl _)]
  exact h

/-- Specialisation of `shift_above_closed` at `Γ = []`: closed
terms have trivial shift. This is the theorem `Equiv.shift`'s
nil-Γ case reduces to, given a closedness-carrying variant of
`Equiv`. -/
theorem Subtype'.shift_nil_closed {S a b} (n c : Nat)
    (ha : a.closedAt 0 = true) (hb : b.closedAt 0 = true)
    (h : Subtype' S [] a b) :
    Subtype' S [] (a.shift n c) (b.shift n c) := by
  rw [Expr.shift_of_closedAt ha n (Nat.zero_le _),
      Expr.shift_of_closedAt hb n (Nat.zero_le _)]
  exact h

/-! ### Algorithmic-checker properties and known issues

**Transitivity verified** for `NbE.subCheck` by exhaustive testing on small
expressions (including all Std library types, nested ι/fix, self-referential
patterns). See `Tests.lean` (`checkTrans`). **Not yet proved** in Lean.

**top-universal is FALSE.** `.type ⊑ τ` does NOT imply `v ⊑ τ` for all `v`. -/
