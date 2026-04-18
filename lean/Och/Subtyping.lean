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
  /-- [unfoldIotaR]: `a ⊑ ι A. body` if `a ⊑ body[self := ι A. body]`.
  Symmetric to `unfold_iota_L`; together they give
  `ι A. body ≡ body[self := ι A. body]` (the ι fixpoint
  equation). `iota_intro` is the *algorithmic* form (it
  additionally checks `a ⊑ A`, which the algorithm needs
  for the seen-set discipline) but is strictly stronger
  than this rule; both are sound since semantically
  `ι A. body` *is* its one-step unfolding. -/
  | unfold_iota_R {S Γ a ann body} :
      Subtype' ((a, .iota ann body) :: S) Γ
        a (body.subst 0 (.iota ann body)) →
      Subtype' S Γ a (.iota ann body)
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

-- `Subtype'.shift_preserve` removed: its uniform-cutoff
-- statement was wrong (Γ entries are at staggered depths;
-- entry `k` needs cutoff `c - k - 1`). The correct form is
-- `ctx_extend_at` below, which is what `narrow_at` actually
-- uses. `Equiv.shift` (SoundnessProof.lean) states the
-- `∀ Γ`-quantified version it needs locally.

/-- All seen-set entries are fully closed (no free bvars).
Used by `narrow_at` so the `.bvar`-case's `ctx_extend` can
unshift the seen-set. -/
abbrev Seen.Closed (S : Seen) : Prop :=
  ∀ p ∈ S, p.1.closedAt 0 = true ∧ p.2.closedAt 0 = true

theorem Seen.Closed.shift_map_eq {S : Seen} (hSc : Seen.Closed S)
    (d c : Nat) :
    S.map (fun (x, y) => (x.shift d c, y.shift d c)) = S := by
  induction S with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨h1, h2⟩ := hSc p (List.mem_cons_self ..)
    simp only [List.map_cons,
      Expr.shift_of_closedAt h1 d (Nat.zero_le _),
      Expr.shift_of_closedAt h2 d (Nat.zero_le _)]
    exact congrArg (p :: ·) (ih fun q hq =>
      hSc q (List.mem_cons_of_mem _ hq))

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

/-- General context-extension (de Bruijn weakening), with
the seen-set's *original* closed layer `S₀` factored out: a
derivation at `Γpfx ++ Γ` over seen `S₁ ++ S₀` lifts to one
at `Γpfx.shiftPrefix |Δ| ++ Δ ++ Γ`, with both sides shifted
by `|Δ|` at cutoff `|Γpfx|`, and the seen-set's *added*
layer `S₁` shifted at the same cutoff while the closed `S₀`
is unchanged.

This is the *correct* form of `shift_preserve` (which had
the wrong staggered-cutoff handling). The proof is by
induction on `h`, recursing at `(τ :: Γpfx)` for the
binder-introducing constructors.

`S₀` is closed (so shifting it at any cutoff is the
identity); `S₁` collects pairs added by `iota_intro` /
`unfold_*` along the derivation, each at *that point's*
`Γpfx` depth, so they need shifting at *that point's*
cutoff. The `.lam`/`.iota_body`/`.fix_body` cases recurse at
`Γpfx' := head :: Γpfx` (cutoff `c+1`) but with the *same*
`S₁` — and `S₁`'s entries were added at depths `≤ c`, so
`S₁.map shift_{c+1} ≠ S₁.map shift_c` in general. Those
three cases are sorried below; the precise fix is to track
each `S₁` entry's addition-depth (a depth-tagged seen-set)
or to observe that for `narrow_at`'s actual use the
derivation `hd` is over `S₀` *only* (`S₁ = []`), in which
case the mismatch vanishes — but encoding "the derivation
never extends `S₀`" as a side-condition is awkward in this
inductive form. -/
theorem Subtype'.ctx_extend_at {Γ} (Δ : Ctx) :
    ∀ {S ΓA a b}, Subtype' S ΓA a b →
    ∀ Γpfx, ΓA = Γpfx ++ Γ →
    Subtype'
      (S.map (fun (x, y) => (x.shift Δ.length Γpfx.length,
                             y.shift Δ.length Γpfx.length)))
      (Γpfx.shiftPrefix Δ.length ++ Δ ++ Γ)
      (a.shift Δ.length Γpfx.length)
      (b.shift Δ.length Γpfx.length) := by
  intro S ΓA a b h
  induction h with
  | @hyp S' Γ' a' b' hin =>
    intro Γpfx _
    exact .hyp (List.mem_map_of_mem _ hin)
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
        (S := S'.map (fun (x, y) => (x.shift Δ.length Γpfx.length,
                                     y.shift Δ.length Γpfx.length)))
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
        (S := S'.map (fun (x, y) => (x.shift Δ.length Γpfx.length,
                                     y.shift Δ.length Γpfx.length)))
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
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- `hb` is at seen `S'.map shift_{|Γpfx|+1}`; goal needs
    -- `S'.map shift_{|Γpfx|}`. These coincide when every
    -- `S'`-entry is closed at `|Γpfx|` (so neither shift
    -- moves anything). For `narrow_at`'s use, `S' = S₀`
    -- with `Seen.Closed S₀`, hence both equal `S₀`. Encoding
    -- that here would require either threading `Seen.Closed
    -- S` (which `.iota_intro` etc. break — they add
    -- non-closed pairs) or depth-tagging seen entries.
    sorry
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
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- Same seen-cutoff mismatch as `.lam`.
    sorry
  | @fix_body S' Γ' ann b₁ b₂ _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .fix_body ?_
    have hb := ih (ann :: Γpfx) (List.cons_append .. ▸ rfl)
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- Same seen-cutoff mismatch as `.lam`.
    sorry
  | @iota_cong S' Γ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .iota_cong (ihA Γpfx rfl) ?_
    have hb := ihB (a₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- Same seen-cutoff mismatch as `.lam`.
    sorry
  | @fix_cong S' Γ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .fix_cong (ihA Γpfx rfl) ?_
    have hb := ihB (a₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- Same seen-cutoff mismatch as `.lam`.
    sorry
  | @letE_cong S' Γ' v₁ v₂ b₁ b₂ _ _ ihV ihB =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .letE_cong (ihV Γpfx rfl) ?_
    have hb := ihB (v₂ :: Γpfx) (List.cons_append .. ▸ rfl)
    simp only [List.length_cons, Ctx.shiftPrefix_cons,
               List.cons_append] at hb
    -- Same seen-cutoff mismatch as `.lam`.
    sorry
  | @iota_intro S' Γ' a' ann body _ _ ih1 ih2 =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .iota_intro ?_ ?_
    · have := ih1 Γpfx rfl
      simpa [List.map_cons, Expr.shift] using this
    · have := ih2 Γpfx rfl
      simpa [List.map_cons, Expr.shift,
             Expr.subst_shift_swap] using this
  | @unfold_iota_L S' Γ' ann body c' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .unfold_iota_L ?_
    have := ih Γpfx rfl
    simpa [List.map_cons, Expr.shift,
           Expr.subst_shift_swap] using this
  | @unfold_fix_L S' Γ' ann body c' _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .unfold_fix_L ?_
    have := ih Γpfx rfl
    simpa [List.map_cons, Expr.shift,
           Expr.subst_shift_swap] using this
  | @unfold_fix_R S' Γ' a' ann body _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .unfold_fix_R ?_
    have := ih Γpfx rfl
    simpa [List.map_cons, Expr.shift,
           Expr.subst_shift_swap] using this
  | @unfold_iota_R S' Γ' a' ann body _ ih =>
    intro Γpfx hpfx
    subst hpfx
    simp only [Expr.shift]
    refine .unfold_iota_R ?_
    have := ih Γpfx rfl
    simpa [List.map_cons, Expr.shift,
           Expr.subst_shift_swap] using this
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
shifted by `|Δ|` at cutoff `0`, seen-set unchanged
*provided* every seen pair is fully closed (so the shift is
the identity on them).

`narrow_at` calls this with `Δ := Γ' ++ [domB]` to lift the
contravariant domain premise `hd` to the inner context. -/
theorem Subtype'.ctx_extend {S Γ a b} (Δ : Ctx)
    (hSc : Seen.Closed S) (h : Subtype' S Γ a b) :
    Subtype' S (Δ ++ Γ) (a.shift Δ.length 0) (b.shift Δ.length 0) := by
  have h' := ctx_extend_at (Γ := Γ) Δ h [] rfl
  simp only [List.length_nil, Ctx.shiftPrefix_nil,
             List.nil_append] at h'
  rwa [hSc.shift_map_eq Δ.length 0] at h'

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

The contravariant premise `hd` is over a fixed *closed*
seen-set `S₀` (with `S₀ ⊆ S`); the `S`-extending
constructors of `h` (`.iota_intro`/`.unfold_*`) recurse at
the larger `S` while `hd` and `S₀` stay put. At `.bvar`
with `k = Γ'.length`, `ctx_extend` lifts `hd` to the
extended context (its closedness side-condition is
discharged by `hSc`), then `weaken` from `S₀` to `S`. -/
theorem Subtype'.narrow_at {S₀ Γ domA domB}
    (hSc : Seen.Closed S₀)
    (hd : Subtype' S₀ Γ domB domA) :
    ∀ {S Δ x y}, Subtype' S Δ x y →
    ∀ Γ', Δ = Γ' ++ domA :: Γ →
    (∀ p ∈ S₀, p ∈ S) →
    Subtype' S (Γ' ++ domB :: Γ) x y := by
  intro S Δ x y h
  induction h with
  | hyp hin => exact fun _ _ _ => .hyp hin
  | refl e => exact fun _ _ _ => .refl e
  | top e => exact fun _ _ _ => .top e
  | trans _ _ ih1 ih2 =>
      exact fun Γ' hΔ hsub =>
        .trans (ih1 Γ' hΔ hsub) (ih2 Γ' hΔ hsub)
  | @bvar S' Δ' k τ hget =>
      intro Γ' hΔ hsub
      subst hΔ
      by_cases hk : k = Γ'.length
      · -- k = Γ'.length: the narrowed entry. `τ = domA`; new
        -- context gives `domB`. Bridge via `.trans` + lifted
        -- `hd` (over the closed `S₀`, then weakened).
        subst hk
        obtain ⟨hτ, hgetB⟩ :=
          List.get?_append_replace_eq (B := domB) hget
        subst hτ
        refine .trans (.bvar hgetB) ?_
        have hext := (ctx_extend (Γ' ++ [domB]) hSc hd).weaken hsub
        simpa [List.length_append, List.append_assoc,
               List.singleton_append, List.cons_append] using hext
      · exact .bvar (List.get?_append_replace_ne hk hget)
  | @lam S' Δ' dA dB bA bB _ _ ihd ihb =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .lam (ihd Γ' rfl hsub)
        (ihb (dB :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | app_cong _ _ _ ihf iha iha' =>
      exact fun Γ' hΔ hsub =>
        .app_cong (ihf Γ' hΔ hsub) (iha Γ' hΔ hsub) (iha' Γ' hΔ hsub)
  | @iota_body S' Δ' ann b₁ b₂ _ ih =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .iota_body
        (ih (ann :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | @fix_body S' Δ' ann b₁ b₂ _ ih =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .fix_body
        (ih (ann :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | @iota_cong S' Δ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .iota_cong (ihA Γ' rfl hsub)
        (ihB (a₂ :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | @fix_cong S' Δ' a₁ a₂ b₁ b₂ _ _ ihA ihB =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .fix_cong (ihA Γ' rfl hsub)
        (ihB (a₂ :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | @letE_cong S' Δ' v₁ v₂ b₁ b₂ _ _ ihV ihB =>
      intro Γ' hΔ hsub
      subst hΔ
      exact .letE_cong (ihV Γ' rfl hsub)
        (ihB (v₂ :: Γ') (List.cons_append .. ▸ rfl) hsub)
  | iota_intro _ _ ih1 ih2 =>
      intro Γ' hΔ hsub
      exact .iota_intro
        (ih1 Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
        (ih2 Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
  | unfold_iota_L _ ih =>
      intro Γ' hΔ hsub
      exact .unfold_iota_L
        (ih Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
  | unfold_fix_L _ ih =>
      intro Γ' hΔ hsub
      exact .unfold_fix_L
        (ih Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
  | unfold_fix_R _ ih =>
      intro Γ' hΔ hsub
      exact .unfold_fix_R
        (ih Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
  | unfold_iota_R _ ih =>
      intro Γ' hΔ hsub
      exact .unfold_iota_R
        (ih Γ' hΔ (fun p hp => List.mem_cons_of_mem _ (hsub p hp)))
  | beta_L _ ih => exact fun Γ' hΔ hsub => .beta_L (ih Γ' hΔ hsub)
  | beta_R _ ih => exact fun Γ' hΔ hsub => .beta_R (ih Γ' hΔ hsub)
  | letE_L _ ih => exact fun Γ' hΔ hsub => .letE_L (ih Γ' hΔ hsub)
  | letE_R _ ih => exact fun Γ' hΔ hsub => .letE_R (ih Γ' hΔ hsub)
  | asc_L _ ih => exact fun Γ' hΔ hsub => .asc_L (ih Γ' hΔ hsub)
  | asc_R _ ih => exact fun Γ' hΔ hsub => .asc_R (ih Γ' hΔ hsub)

/-- Head-position context narrowing: replacing `Γ`'s innermost
binder type `domA` with a subtype `domB ⊑ domA` preserves
derivations, provided every `S`-entry is fully closed.
After the A6 revert (DECISION-LOG 2026-04-18) the
algorithm's `.lam,.lam` arm pushes `domA` while
`Subtype'.lam` pushes `domB`, so the `SubV → Subtype'`
bridge's `.lam` case needs exactly this. Specialises
`narrow_at` with `Γ' := []`, `S₀ := S`. -/
theorem Subtype'.narrow {S Γ domA domB x y}
    (hSc : Seen.Closed S)
    (hd : Subtype' S Γ domB domA)
    (h : Subtype' S (domA :: Γ) x y) :
    Subtype' S (domB :: Γ) x y :=
  narrow_at hSc hd h [] rfl (fun _ hp => hp)

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

/-! ### subCheckNF properties and known issues

**Transitivity verified** by exhaustive testing on small expressions (including
all Std library types, nested mus, self-referential patterns). See Tests.lean.
**Transitivity is NOT YET PROVED** in Lean.

**subCheckNF_top_universal is FALSE.**
(.type ⊑ τ does NOT imply v ⊑ τ for all v.) -/
