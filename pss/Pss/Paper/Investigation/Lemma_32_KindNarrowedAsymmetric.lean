import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Aux.StackExtension
import Pss.Paper.Investigation.Lemma_32_Asymmetric

/-! # `Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric` —
**kind-narrowed** asymmetric Lemma 32.

This file ships the missing structural lemma identified by the Lemma 2
diamond walls: an asymmetric β-substitution where the source's `.sub`
head bound `t` is **decoupled** from the LHS substitution argument
`arg`. The corresponding paper-faithful surface form is:

```
  Γ;[] ⊢ arg →ᵉᵠᵘ arg'
  {t,.sub}::Γ; (Stack.shift 0 s) ⊢ body →ᵉᵠᵘ body'
  ──────────────────────────────────────────────────
  Γ; s ⊢ body[arg/0] →ᵉᵠᵘ body'[arg'/0]
```

This is the lemma the bet × bet, app × bet, bet × app cells of paper
Lemma 2 invoke (paper p. 9:25, "By Lemma 32 from `Γ, x ≡ v₁; s₁ ⊢ u₁
→ᵉᵠᵘ u₃` and `Γ; nil ⊢ v₁ →ᵉᵠᵘ v₃`"). The paper hides the
decoupling because in the named-binders presentation the abstraction's
bound `t` and the substitution argument `v₁` simply have different
named-variable identities (`x` for the bound, `v₁` is the argument
term). In de Bruijn, both occupy the same head slot and the decoupling
must be made explicit.

## Relation to existing lemmas

* `Lemma_32_Asymmetric_proved` (paper-faithful, but with bound = arg):
  source's `.sub` head bound EQUALS the LHS substitution arg. Suitable
  when the substituted variable's annotation IS the substitution
  argument itself (paper's `x ≡ v` shape).
* `MEqRedFusedKindNarrowedBetaSubstStack_proved` (kind-narrowed but
  symmetric): source's `.sub` head bound is `arg`, but substitution
  on both LHS and RHS uses `arg'` (decoupled from bound). LHS = RHS
  substitution arg.
* **This lemma** (kind-narrowed AND asymmetric): source's `.sub` head
  bound is `t` (independent), substitution by `arg` (LHS) / `arg'`
  (RHS). Combines the decoupling of the kind-narrowed form with the
  asymmetric LHS/RHS substitutions.

## Proof structure

The proof is a **direct adaptation** of `Lemma_32_Asymmetric_via_wall`,
with the following minimal changes:

1. The source context's `.sub` head bound is `t`, not `arg`. The bound
   `t` plays no role in the algebraic substitution — only its
   scopedness is needed (to admit the source-context prevalidity).
2. Where the existing asymmetric proof uses
   `BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped` (which
   assumes source bound = substitution arg), we use
   `BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed`
   (which decouples them — applied with their `arg := t`, their
   `arg' := arg`).
3. The `Me-Pro` helper is similarly adapted to use the kind-narrowed
   prevalidity transport. The `equBinds_instantiateBetaPrefix` lookup
   transport already takes the bound parameter generically (so no
   change there).
4. The `Me-Var × substituted slot` case re-uses the EXISTING
   `MEqRedStackExtensionWall_proved`. The wall's statement does not
   reference the source bound `t`; it only relates `arg → arg'` to
   their post-substitution stack-extended forms. That part is
   structurally invariant under the bound change.

The wall is therefore unchanged; we re-export it as-is.

## File layout

* `Lemma_32_KindNarrowedAsymmetric_Goal` — the universal-prefix
  statement.
* `kind_narrowed_asym_pro_helper` — `Me-Pro` step transport, the
  kind-narrowed analogue of `asym_pro_helper`.
* `Lemma_32_KindNarrowedAsymmetric_via_wall` — the induction reducing
  the kind-narrowed asymmetric Lemma 32 to the wall.
* `Lemma_32_KindNarrowedAsymmetric_proved` — the closed lemma,
  combining the via-wall reduction with the existing wall proof.
* `Lemma_32_KindNarrowedAsymmetric_proved_closed` — the empty-prefix
  specialisation (paper-surface entry point used by the bet/bet,
  app/bet, bet/app cells of Lemma 2).
-/

namespace Pss
namespace DeBruijn
namespace Paper
namespace Investigation

/-! ## Universal-prefix statement -/

/-- **Kind-narrowed asymmetric Lemma 32, generic-prefix form.** Source
context has `.sub` head with arbitrary bound `t`; LHS substitutes by
`arg`, RHS by `arg'`. -/
def Lemma_32_KindNarrowedAsymmetric_Goal : Type :=
  ∀ {Γ : Ctx} {t arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
    Term.Scoped Γ.depth t →
      Term.Scoped Γ.depth arg →
        Term.Scoped Γ.depth arg' →
          MEqRed Γ [] arg arg' →
            MEqRed (heads ++ { bound := t, kind := .sub } :: Γ) s lhs rhs →
              MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
                (Stack.instantiate heads.length
                  (Term.shiftBy 0 heads.length arg) s)
                (Term.instantiate heads.length
                  (Term.shiftBy 0 heads.length arg) lhs)
                (Term.instantiate heads.length
                  (Term.shiftBy 0 heads.length arg') rhs)

/-! ## `Me-Pro` helper (kind-narrowed)

Mirrors `asym_pro_helper` but with the source bound `t` decoupled from
the LHS substitution arg `arg`. -/

/-- Kind-narrowed asymmetric `Me-Pro` transport: the source's `bvar i`
reduces via `Me-Pro` to `α'`. After substitution by `arg` (LHS) and
`arg'` (RHS), the IH gives the bound's reduction asymmetrically; we
reassemble `Me-Pro` at the substituted bvar in the post-context whose
heads are instantiated by `arg`. -/
private noncomputable def kind_narrowed_asym_pro_helper
    {Γ : Ctx} {t arg arg' α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := t, kind := .sub } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := t, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α') := by
  -- Post-context's prevalidity: use the kind-narrowed transport with
  -- (their `arg`, their `arg'`) := (our `t`, our `arg`).
  have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
    (n := heads.length) (arg := t) (arg' := arg) rfl hArgScoped hpv
  -- equBinds transport: the `bound` parameter is `t`, the `arg` parameter is `arg`.
  rcases Ctx.equBinds_instantiateBetaPrefix
      (Γ := Γ) (bound := t) (arg := arg) (heads := heads) hb with
    ⟨j, hvar, hbind⟩
  rw [hvar]
  exact MEqRed.pro hpvTarget hbind hα

/-! ## The via-wall induction (kind-narrowed)

Carbon copy of `Lemma_32_Asymmetric_via_wall` with the source bound
generalised from `arg` to `t`, and the prevalidity transport switched
from the symmetric to the kind-narrowed form. -/

/-- **Reduction of the kind-narrowed asymmetric goal to the wall.**
Given the existing `MEqRedStackExtensionWall`, the kind-narrowed
asymmetric Lemma 32 follows by induction on the body derivation. -/
noncomputable def Lemma_32_KindNarrowedAsymmetric_via_wall
    (hWall : MEqRedStackExtensionWall) :
    ∀ n {Γ : Ctx} {t arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
      heads.length = n →
        Term.Scoped Γ.depth t →
          Term.Scoped Γ.depth arg →
            Term.Scoped Γ.depth arg' →
              MEqRed Γ [] arg arg' →
                MEqRed (heads ++ { bound := t, kind := .sub } :: Γ) s lhs rhs →
                  MEqRed
                    (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
                    (Stack.instantiate heads.length
                      (Term.shiftBy 0 heads.length arg) s)
                    (Term.instantiate heads.length
                      (Term.shiftBy 0 heads.length arg) lhs)
                    (Term.instantiate heads.length
                      (Term.shiftBy 0 heads.length arg') rhs) := by
  intro n Γ t arg arg' lhs rhs heads s hlen htScoped hArgScoped hArg'Scoped
    hArgArg' hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := t, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      exact kind_narrowed_asym_pro_helper (Γ := Γ) (t := t)
        (arg := arg) (arg' := arg') (heads := heads)
        hArgScoped hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) (arg := t) (arg' := arg) rfl hArgScoped hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg' ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArg'IH := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hOp' hArg'IH
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) (arg := t) (arg' := arg) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have hi_lt : i < Γ.depth + heads.length + 1 := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := t, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      by_cases hieq : i = heads.length
      · -- Substituted-slot subcase: apply the existing wall (which is
        -- agnostic to the source bound `t`).
        subst hieq
        have hLHSEq :
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) (.bvar heads.length) =
            Term.shiftBy 0 heads.length arg := by
          simp [Term.instantiate]
        have hRHSEq :
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') (.bvar heads.length) =
            Term.shiftBy 0 heads.length arg' := by
          simp [Term.instantiate]
        rw [hLHSEq, hRHSEq]
        exact hWall (heads := heads) (s := s')
          hArgScoped hArg'Scoped hArgArg' hpvTarget
      · -- Non-substituted-slot subcase: LHS and RHS substitutions
        -- agree on bvars away from `heads.length`, close by reflexivity.
        have hbvar_scoped :
            Term.Scoped (Γ.depth + heads.length + 1) (.bvar i) :=
          Term.Scoped.bvar hi_lt
        have hLHSScoped :
            Term.Scoped (Γ.depth + heads.length)
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) (.bvar i)) :=
          Term.instantiate_scoped heads.length (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) (.bvar i) (by omega)
            hArgShiftScoped hbvar_scoped
        have hLHSScoped' :
            Term.Scoped
              (Ctx.depth
                (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
          simpa [Ctx.depth, List.length_append,
            Ctx.length_instantiateBetaPrefix,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLHSScoped
        have hLHSeqRHS :
            Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) (.bvar i) =
              Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') (.bvar i) := by
          unfold Term.instantiate
          split <;> rfl
        rw [← hLHSeqRHS]
        exact MEqRed.refl hpvTarget hLHSScoped'
  | @tAp Γ' s' u hpv hu =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) (arg := t) (arg' := arg) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := t, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hu
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hu
      have huInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) u (by omega)
          hArgShiftScoped hu'
      have huInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using huInstScoped
      simpa [Term.instantiate] using MEqRed.tAp hpvTarget huInstScoped'
  | @bet Γ' s' tInner v v' body body' htInner hbody harg ihBody ihArg =>
      subst hC
      have hBody' :=
        ihBody (heads := { bound := tInner, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hArgIH := ihArg (heads := heads) rfl
      have hLen_succ :
          ({ bound := tInner, kind := .sub } :: heads : Ctx).length =
            heads.length + 1 := by simp
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := tInner, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) tInner,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have htInnerOriginal : Term.Scoped (Γ.depth + heads.length + 1) tInner := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := t, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at htInner
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInner
      have htInnerInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) tInner) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) tInner (by omega)
          hArgShiftScoped htInnerOriginal
      have htInnerInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) tInner) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInnerInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) tInner,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hBet :=
        MEqRed.bet
          (Γ := Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
          (s := Stack.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) s')
          (t := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) tInner)
          (v := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v)
          (v' := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') v')
          (body := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body)
          (body' := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg') body')
          htInnerInstScoped' hBodyReady hArgIH
      have hTarget :
          Term.instantiate 0
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') v')
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg') body') =
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg')
              (Term.instantiate 0 v' body') := by
        rw [hshift_succ']
        exact Term.instantiate_zero_after_many heads.length
          (Term.shiftBy 0 heads.length arg') v' body'
      simpa [Term.instantiate, hTarget, ← hshift_succ] using hBet
  | @fun_ Γ' tInner tInner' body body' hT hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := tInner, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := tInner, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) tInner,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) tInner,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            []
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        simpa using hBody'
      have hFun := MEqRed.fun_ hT' hBodyReady
      simpa [Term.instantiate, hshift_succ, hshift_succ'] using hFun
  | @fOp Γ' s' tInner tInner' α body body' hT hα hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := α, kind := .equ } :: heads)
          (by simp [List.cons_append])
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := α, kind := .equ } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hαOriginal : Term.Scoped (Γ.depth + heads.length + 1) α := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := t, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hα
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hα
      have hαInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) α (by omega)
          hArgShiftScoped hαOriginal
      have hαInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hαInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hFOp := MEqRed.fOp hT' hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ,
        hshift_succ'] using hFOp

/-! ## Closed-stack surface (heads = [] specialisation) -/

/-- Closed-stack version of the kind-narrowed asymmetric Lemma 32. The
empty preserved-prefix is the form the bet × bet, app × bet, bet × app
cells of paper Lemma 2 invoke. -/
noncomputable def Lemma_32_KindNarrowedAsymmetric_via_wall_closed
    (hWall : MEqRedStackExtensionWall)
    {Γ : Ctx} {t arg arg' lhs rhs : Term} {s : Stack}
    (htScoped : Term.Scoped Γ.depth t)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({ bound := t, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg lhs)
      (Term.instantiate 0 arg' rhs) := by
  have h' := Lemma_32_KindNarrowedAsymmetric_via_wall hWall 0
    (heads := []) rfl htScoped hArgScoped hArg'Scoped hArgArg' h
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-! ## Final, paper-faithful entry points -/

/-- **Kind-narrowed asymmetric Lemma 32, generic-prefix form.** Source
context has `.sub` head with arbitrary bound `t`; LHS substitutes by
`arg`, RHS by `arg'`. -/
noncomputable def Lemma_32_KindNarrowedAsymmetric_proved
    {Γ : Ctx} {t arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack}
    (htScoped : Term.Scoped Γ.depth t)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed (heads ++ { bound := t, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length
        (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length
        (Term.shiftBy 0 heads.length arg) lhs)
      (Term.instantiate heads.length
        (Term.shiftBy 0 heads.length arg') rhs) :=
  Lemma_32_KindNarrowedAsymmetric_via_wall MEqRedStackExtensionWall_proved
    heads.length rfl htScoped hArgScoped hArg'Scoped hArgArg' h

/-- **Kind-narrowed asymmetric Lemma 32, closed-stack surface.** This is
the form consumed by paper Lemma 2's bet × bet, app × bet, bet × app
cells.

Paper Lemma 2's `Me-Bet × Me-Bet` cell (p. 9:25) reads (after diamond
on body and arg):

> "By Lemma 32 from `Γ, x ≡ v₁; s₁ ⊢ u₁ →ᵉᵠᵘ u₃` and
>   `Γ; nil ⊢ v₁ →ᵉᵠᵘ v₃`"

In de Bruijn:
* `Γ, x ≡ v₁; s₁ ⊢ u₁ →ᵉᵠᵘ u₃` ↦ `MEqRed ({t, .sub} :: Γ) (shift 0 s)
   body₁' body₃` (with `t` the abstraction's bound, body sub-derivation
   from the body diamond's joint reduct).
* `Γ; nil ⊢ v₁ →ᵉᵠᵘ v₃` ↦ `MEqRed Γ [] arg arg'`.
* The conclusion `Γ_post; s_post ⊢ u₁[x\v₁] →ᵉᵠᵘ u₃[x\v₃]` ↦
  `MEqRed Γ s (Term.instantiate 0 arg body₁') (Term.instantiate 0 arg' body₃)`.

The decoupling of the abstraction's bound `t` from the substitution
arg `arg = v₁` is invisible in the paper presentation (named-binders
hide the structural distinction) but explicit in de Bruijn. -/
noncomputable def Lemma_32_KindNarrowedAsymmetric_proved_closed
    {Γ : Ctx} {t arg arg' lhs rhs : Term} {s : Stack}
    (htScoped : Term.Scoped Γ.depth t)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({ bound := t, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg lhs)
      (Term.instantiate 0 arg' rhs) :=
  Lemma_32_KindNarrowedAsymmetric_via_wall_closed
    MEqRedStackExtensionWall_proved
    htScoped hArgScoped hArg'Scoped hArgArg' h

end Investigation
end Paper
end DeBruijn
end Pss
