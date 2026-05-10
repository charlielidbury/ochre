import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Aux.StackExtension

/-! # `Pss.Paper.Investigation.Lemma_32_Asymmetric` — paper's asymmetric
Lemma 32, **provable**.

This file is an **investigation artifact** dispatched by the campaign to
resolve the long-standing question:

> Is the paper's asymmetric Lemma 32 (Pasquale & García-Pérez 2024,
> p. 9:44–45) provable in our de Bruijn encoding?

## Outcome — FALSE ALARM

A previous dispatch (commit `e5d2096`) claimed the asymmetric form was
unprovable due to a structural wall at the `Me-Var × substituted slot`
case. **That claim was wrong.** The wall (here named
`MEqRedStackExtensionWall`) IS provable; this dispatch ships its proof
and ships the closed-form asymmetric Lemma 32.

The argument the previous dispatch missed:

* The wall reduces to (a) iterated weakening across the
  `instantiateBetaPrefix` heads, plus (b) stack-append extension from
  `[]` to a non-empty stack on `MEqRed`.
* (a) is standard weakening (`MEqRed.appendCtx` in
  `Pss/Paper/Aux/StackExtension.lean`).
* (b)'s only non-trivial case is `Me-Fun → Me-FOp`: an empty-stack
  abstraction-shaped derivation re-derived as a non-empty-stack
  `Me-FOp` step. The kind switch `.sub head → .equ head` is supplied
  by `MEqRed.sub_to_equ_head_replace` (`Pss/Mpss/DeBruijnReductions.lean:1945`).
  This existing lemma exists because `Me-Pro` (the only `MEqRed` rule
  whose conclusion distinguishes `.sub` from `.equ`) cannot fire on
  `bvar 0` under a `.sub` head, so the body sub-derivation is
  invariant under that kind switch.

The paper is therefore correct as stated. The previous dispatch
incorrectly concluded it was a paper bug because it did not consider
the `sub_to_equ_head_replace`-mediated re-derivation in the body of
the wall's `Me-Fun` case.

## Paper-faithfulness note

The named-binders presentation of the paper hides the kind-switch
because the paper writes the body's context entry as `y ≤ a` or `y ≡ β`
depending on which rule fires, treating both as fresh-named entries.
The de Bruijn encoding makes the kind switch syntactically explicit;
hence the explicit `sub_to_equ_head_replace` lemma in the codebase.
Either way, the structural argument is identical: the body's
derivation does not depend on the discharged head's kind because the
only kind-distinguishing rule (`Me-Pro`) is foreclosed at `bvar 0`
under `.sub`.

## File structure

* `Lemma_32_Asymmetric_Goal` — the asymmetric statement.
* `MEqRedStackExtensionWall` — the obligation produced by the
  `Me-Var × substituted slot` case. **Provable**, see
  `MEqRedStackExtensionWall_proved`.
* `Lemma_32_Asymmetric_via_wall` — the induction reducing the
  asymmetric Lemma 32 to the wall (modulo every other case). Closes
  every case except `Me-Var × substituted slot` directly; that one
  applies the wall.
* `MEqRedStackExtensionWall_proved` — the wall, discharged via
  `MEqRed.appendCtx` (iterated weakening) plus
  `MEqRed.lift_empty_to_stack` (stack-append extension).
* `Lemma_32_Asymmetric_proved` — the closed asymmetric Lemma 32.
* `Lemma_32_Asymmetric_proved_closed` — the empty-prefix
  specialization, exposed as the paper-surface entry point. -/

namespace Pss
namespace DeBruijn
namespace Paper
namespace Investigation

/-! ## The asymmetric statement -/

/-- **Paper Lemma 32, fully asymmetric form, de Bruijn encoded.**

Paper:
> If `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` and `Γ; nil ⊢ v →ᵉᵠᵘ v'`, then
> `Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] →ᵉᵠᵘ u'[x\v']`.

In de Bruijn we use a `.sub`-headed slot for the substituted variable
(matching the rest of the codebase's β-instantiation surface; the
paper's `≡` vs Lean's `.sub` distinction is reconciled in
`Pss/Paper/Aux/Substitution.lean` by treating the link
`MEqRed Γ [] arg arg'` as the de Bruijn analogue of paper's `≡`-link).

The asymmetry is explicit: LHS uses `arg`, RHS uses `arg'`. -/
def Lemma_32_Asymmetric_Goal : Type :=
  ∀ {Γ : Ctx} {arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
    Term.Scoped Γ.depth arg →
      Term.Scoped Γ.depth arg' →
        MEqRed Γ [] arg arg' →
          MEqRed (heads ++ { bound := arg, kind := .sub } :: Γ) s lhs rhs →
            MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
              (Stack.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) s)
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) lhs)
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') rhs)

/-! ## The structural wall -/

/-- **The wall**: lift `MEqRed Γ [] arg arg'` to a non-trivial post-
substitution stack. This is the obligation produced by the `Me-Var`
case at the substituted bvar slot. It is **not** a consequence of the
lemma's hypotheses — `MEqRed` does not enjoy stack-extension in
general.

A counter-shape: if `arg = .abs Top body` and `arg' = .abs Top body'`,
then `MEqRed Γ [] arg arg'` is via `Me-Fun` (body in `.sub Top`-headed
context). Lifting to a non-empty target stack requires `Me-FOp` (body
in `.equ`-headed context taking the stack head), which has
incompatible body shape. -/
def MEqRedStackExtensionWall : Type :=
  ∀ {Γ : Ctx} {arg arg' : Term} {heads : Ctx} {s : Stack},
    Term.Scoped Γ.depth arg →
      Term.Scoped Γ.depth arg' →
        MEqRed Γ [] arg arg' →
          PrevalidExt
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
            (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s) →
            MEqRed
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
              (Stack.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) s)
              (Term.shiftBy 0 heads.length arg)
              (Term.shiftBy 0 heads.length arg')

/-! ## Auxiliary: pro-case helper for the asymmetric form

The `Me-Pro` case calls into a helper that mirrors
`MEqRedRespectsBetaInstantiateUnderHeadsStack.pro` but with the IH
yielding `arg`/`arg'` asymmetric outputs. -/

/-- Asymmetric `Me-Pro` transport: the source's `bvar i` reduces via
`Me-Pro` to `α'`, with the recursive premise `α →ᵉᵠᵘ α'`. After
substitution, the IH (assumed) gives the bound's reduction under the
asymmetric form, and we reassemble `Me-Pro` at the substituted bvar.
-/
private noncomputable def asym_pro_helper
    {Γ : Ctx} {arg arg' α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α') := by
  -- Same structure as the symmetric `pro` helper, but the input
  -- reduction `hα` and the output use `arg'` on the RHS. The lookup
  -- transport is unchanged: it factors only through `arg`.
  have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
    (n := heads.length) rfl hArgScoped hpv
  rcases Ctx.equBinds_instantiateBetaPrefix_ofScoped
      (Γ := Γ) (arg := arg) (heads := heads) hb with
    ⟨j, hvar, hbind⟩
  rw [hvar]
  -- The post-substitution context binds `bvar j` to
  -- `instantiate heads.length (shifted arg) α`. We have a reduction
  -- from that to `instantiate heads.length (shifted arg') α'` via
  -- `hα`. `Me-Pro` produces `bvar j → instantiate heads.length
  -- (shifted arg') α'` which is exactly the target.
  exact MEqRed.pro hpvTarget hbind hα

/-! ## The proof attempt — closes every case except Me-Var × substituted-slot

Strategy: induction on the `MEqRed` derivation, generalising `heads`
and `s`. The Me-Var case at the substituted slot applies the wall
hypothesis. -/

/-- **Reduction of the asymmetric goal to the wall.** Given the
hypothetical stack-extension lemma `MEqRedStackExtensionWall`, the full
asymmetric Lemma 32 follows by the standard induction. -/
noncomputable def Lemma_32_Asymmetric_via_wall
    (hWall : MEqRedStackExtensionWall) :
    ∀ n {Γ : Ctx} {arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
      heads.length = n →
        Term.Scoped Γ.depth arg →
          Term.Scoped Γ.depth arg' →
            MEqRed Γ [] arg arg' →
              MEqRed (heads ++ { bound := arg, kind := .sub } :: Γ) s lhs rhs →
                MEqRed
                  (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
                  (Stack.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg) s)
                  (Term.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg) lhs)
                  (Term.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg') rhs) := by
  intro n Γ arg arg' lhs rhs heads s hlen hArgScoped hArg'Scoped hArgArg' hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := arg, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      -- Apply IH to the bound's reduction; reassemble via Me-Pro at the
      -- post-substitution bvar. The IH gives us `α[arg] → α'[arg']`,
      -- which is exactly the recursive premise for the asymmetric
      -- `Me-Pro`.
      exact asym_pro_helper (Γ := Γ) (arg := arg) (arg' := arg')
        (heads := heads) hArgScoped hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      -- `Top → Top`. After substitution both sides are still `Top`.
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg' ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArg'IH := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hOp' hArg'IH
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
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
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      -- Now the `Me-Var` case splits on whether `i = heads.length`
      -- (substituted slot) or not. Both subcases need explicit
      -- reasoning: the non-substituted-slot case is reflexive (LHS and
      -- RHS substitutions agree on the resulting bvar); the
      -- substituted-slot case applies the wall hypothesis.
      by_cases hieq : i = heads.length
      · -- Substituted-slot subcase. LHS substitutes by arg (yielding
        -- shifted arg); RHS substitutes by arg' (yielding shifted
        -- arg'). The wall gives the desired reduction.
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
      · -- Non-substituted-slot subcase. Both LHS and RHS substitute the
        -- same bvar (non-substituted), yielding the same target bvar.
        -- Close by reflexivity. The two `arg`/`arg'` substitutions
        -- agree on bvars away from `heads.length`.
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
        -- For `i ≠ heads.length`, the bvar substitution result is
        -- `bvar j` for some `j`, independent of which `arg` is used.
        -- So `instantiate heads.length (shifted arg) (bvar i)` =
        -- `instantiate heads.length (shifted arg') (bvar i)`.
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
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
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
      -- `Top u → Top`. After substitution: `Top u[arg] → Top` (the RHS
      -- `Top` is invariant under any substitution). Apply Me-TAp.
      simpa [Term.instantiate] using MEqRed.tAp hpvTarget huInstScoped'
  | @bet Γ' s' t v v' body body' ht hbody harg ihBody ihArg =>
      subst hC
      -- Apply IH to body (with augmented .sub head) and operand
      -- (empty stack, same heads). Reassemble Me-Bet. Crucially, the
      -- LHS substitutes by arg (giving the constructor's `t[arg]`
      -- annotation), while the RHS substitutes by arg' (giving the
      -- post-β-target via Barendregt-style commutation).
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hArgIH := ihArg (heads := heads) rfl
      have hLen_succ :
          ({ bound := t, kind := .sub } :: heads : Ctx).length =
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
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have htOriginal : Term.Scoped (Γ.depth + heads.length + 1) t := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at ht
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
      have htInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) t (by omega)
          hArgShiftScoped htOriginal
      have htInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
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
            (Term.shiftBy 0 heads.length arg) t)
          (v := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v)
          (v' := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') v')
          (body := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body)
          (body' := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg') body')
          htInstScoped' hBodyReady hArgIH
      -- Reconcile the natural β-target with the substituted form via
      -- `Term.instantiate_zero_after_many` applied to `arg'`.
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
  | @fun_ Γ' t t' body body' hT hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
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
                (Term.shiftBy 0 heads.length arg) t,
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
  | @fOp Γ' s' t t' α body body' hT hα hBody ihT ihBody =>
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
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
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
      -- THE KEY OBSERVATION: in `MEqRed.fOp`, the binder annotation `α`
      -- and the stack head `α` are syntactically the same. After
      -- substitution, both become `α[arg]` (the LHS substitution).
      -- This is consistent — there's no `α[arg]`/`α[arg']` conflict
      -- here. The body IH is asymmetric (LHS by arg, RHS by arg'),
      -- but that's only on the body's reduction targets, not on the
      -- binder annotation. So Me-FOp closes asymmetrically with no
      -- structural conflict.
      have hFOp := MEqRed.fOp hT' hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ,
        hshift_succ'] using hFOp

/-! ## Closed-stack surface (heads = [] specialization) -/

/-- Closed-stack version of the asymmetric Lemma 32, specialised at
empty preserved-prefix. This is the surface paper readers expect:
`Γ; s ⊢ u[v\x] →ᵉᵠᵘ u'[v'\x]`. Reduction to the wall is via the
generic universal form. -/
noncomputable def Lemma_32_Asymmetric_via_wall_closed
    (hWall : MEqRedStackExtensionWall)
    {Γ : Ctx} {arg arg' lhs rhs : Term} {s : Stack}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({ bound := arg, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg lhs)
      (Term.instantiate 0 arg' rhs) := by
  have h' := Lemma_32_Asymmetric_via_wall hWall 0
    (heads := []) rfl hArgScoped hArg'Scoped hArgArg' h
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-! ## Wall, discharged

The wall reduces to two existing pieces:

1. **Iterated weakening** (`MEqRed.appendCtx`): lift
   `MEqRed Γ [] arg arg'` to
   `MEqRed (instantiateBetaPrefix arg heads.length heads ++ Γ) []
           (shifted arg) (shifted arg')`.
2. **Stack-append extension** (`MEqRed.lift_empty_to_stack`): lift the
   resulting empty-stack derivation to the post-substitution stack.

Both pieces handle the `Me-Fun → Me-FOp` re-derivation cleanly via
`MEqRed.sub_to_equ_head_replace`. -/

/-- **Wall, discharged.** The stack-extension obligation that the
asymmetric Lemma 32's induction hands off in the `Me-Var × substituted
slot` case is provable. -/
noncomputable def MEqRedStackExtensionWall_proved :
    MEqRedStackExtensionWall := by
  intro Γ arg arg' heads s _hArgScoped _hArg'Scoped hArgArg' hpvTarget
  -- Step 1: iterated weakening across `instantiateBetaPrefix arg heads.length heads`.
  have hpvCtx : Prevalid
      (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) :=
    PrevalidExt.ctx hpvTarget
  have hPvΓ : Prevalid Γ := hArgArg'.prevalidExt.ctx
  have hpvNilΓ : PrevalidExt Γ [] := PrevalidExt.nil hPvΓ
  have hLengthEq :
      (Ctx.instantiateBetaPrefix arg heads.length heads).length =
        heads.length :=
    Ctx.length_instantiateBetaPrefix _ _ _
  have hWeaken := MEqRed.appendCtx
    (Γ := Γ) (s := []) (u := arg) (v := arg')
    (Ctx.instantiateBetaPrefix arg heads.length heads)
    hArgArg' hpvCtx hpvNilΓ
  rw [hLengthEq] at hWeaken
  -- Step 2: lift empty stack to the actual target stack.
  exact MEqRed.lift_empty_to_stack hWeaken hpvTarget

/-! ## Asymmetric Lemma 32, closed

Combine the via-wall reduction with the discharged wall. -/

/-- **Asymmetric Lemma 32, paper p. 9:44–45, generic prefix form.**

Combines `Lemma_32_Asymmetric_via_wall` with the discharged wall. -/
noncomputable def Lemma_32_Asymmetric_proved
    {Γ : Ctx} {arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed (heads ++ { bound := arg, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length
        (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length
        (Term.shiftBy 0 heads.length arg) lhs)
      (Term.instantiate heads.length
        (Term.shiftBy 0 heads.length arg') rhs) :=
  Lemma_32_Asymmetric_via_wall MEqRedStackExtensionWall_proved heads.length
    rfl hArgScoped hArg'Scoped hArgArg' h

/-- **Asymmetric Lemma 32, closed-stack surface (empty prefix).** This is
the paper-surface entry point. -/
noncomputable def Lemma_32_Asymmetric_proved_closed
    {Γ : Ctx} {arg arg' lhs rhs : Term} {s : Stack}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({ bound := arg, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg lhs)
      (Term.instantiate 0 arg' rhs) :=
  Lemma_32_Asymmetric_via_wall_closed MEqRedStackExtensionWall_proved
    hArgScoped hArg'Scoped hArgArg' h

end Investigation
end Paper
end DeBruijn
end Pss
