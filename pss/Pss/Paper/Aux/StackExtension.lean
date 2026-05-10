import Pss.Mpss.DeBruijnReductions
import Pss.Mpss.DeBruijnTransitivityElim
import Pss.Paper.Aux.Weakening

/-! # `Pss.Paper.Aux.StackExtension` — `MEqRed` stack-append extension

This file ships the **stack-append extension** lemma for de Bruijn
`MEqRed`:

> Given `MEqRed Γ s u v` and `PrevalidExt Γ (s ++ s_extra)`, produce
> `MEqRed Γ (s ++ s_extra) u v`.

The lemma is proved by induction on the source derivation. The crucial
case is `Me-Fun → Me-FOp`: an empty-stack abstraction-shaped derivation
must be re-derived as a non-empty-stack `Me-FOp` step when the appended
stack is non-empty. The kind switch `.sub head → .equ head` is supplied
by `MEqRed.sub_to_equ_head_replace`
(`Pss/Mpss/DeBruijnReductions.lean:1945`), which exists precisely
because `Me-Pro` (the only `MEqRed` rule that distinguishes `.sub` from
`.equ` in its conclusion) cannot fire on `bvar 0` under a `.sub` head.

## Why this resolves the asymmetric Lemma 32 wall

`Pss/Paper/Investigation/Lemma_32_Asymmetric.lean` reduces the paper's
asymmetric Lemma 32 (Pasquale & García-Pérez 2024, p. 9:44–45) to a
single obligation: lift `MEqRed Γ [] arg arg'` to a non-empty stack
under a post-β-instantiation context. That obligation is the
combination of (a) iterated weakening across the
`instantiateBetaPrefix` heads and (b) stack-append extension from `[]`
to the post-β stack. Both parts are provable; this file proves (b).

## Paper-faithfulness check

The `sub_to_equ_head_replace` step is invisible in the paper because
the paper uses **named** binders, not de Bruijn. In the named encoding,
the `Me-Fun → Me-FOp` re-derivation simply renames the fresh variable
to match the operand binder; no kind switch is observable because the
context entry's *kind* (`.sub` vs `.equ`) is reflected only in which
typing rules apply, not in the abstract context shape. The de Bruijn
encoding makes the kind switch syntactically explicit, hence the
explicit lemma. -/

namespace Pss
namespace DeBruijn

/-! ## Stack append extension for `MEqRed`

The core induction. -/

/-- **Stack-append extension for `MEqRed`.** Given a derivation under a
specific stack `s` and a prevalid extension `s ++ s_extra`, produce
the derivation under the extended stack.

Proof by induction on the source derivation. Most cases close by
directly re-applying the same constructor with the extended stack on
the appropriate sub-derivations. The single non-trivial case is
`Me-Fun` (abstraction over empty stack) lifting to a non-empty
extended stack: this re-derives the conclusion as `Me-FOp`, switching
the body sub-derivation's head from `.sub`-bound (with `[]` stack) to
`.equ`-bound (with `Stack.shift 0 rest`) via
`MEqRed.sub_to_equ_head_replace` plus a recursive stack extension on
the body. -/
noncomputable def MEqRed.append_stack
    {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) :
    ∀ {s_extra : Stack},
      PrevalidExt Γ (s ++ s_extra) →
      MEqRed Γ (s ++ s_extra) u v := by
  induction h with
  | @pro Γp sp i α α' _ hb hred ih =>
      intro s_extra hpvAppend
      exact MEqRed.pro hpvAppend hb (ih hpvAppend)
  | @top Γp sp _ =>
      intro s_extra hpvAppend
      exact MEqRed.top hpvAppend
  | @app Γp sp u₀ u₀' v₀ v₀' hOp hArg ihOp ihArg =>
      intro s_extra hpvAppend
      have hv₀_scoped : Term.Scoped Γp.depth v₀ := hArg.scoped_left
      -- Operator's source stack is `v₀ :: sp`; appended is `v₀ :: (sp ++ s_extra)`.
      have hpvOp : PrevalidExt Γp ((v₀ :: sp) ++ s_extra) := by
        simpa [List.cons_append] using
          PrevalidExt.cons hpvAppend hv₀_scoped
      -- Operand's source stack is `[]`; we keep it unchanged in the result.
      have hOp' := ihOp hpvOp
      have hRes : MEqRed Γp (sp ++ s_extra) (.app u₀ v₀) (.app u₀' v₀') := by
        have hOp'' :
            MEqRed Γp (v₀ :: (sp ++ s_extra)) u₀ u₀' := by
          simpa [List.cons_append] using hOp'
        exact MEqRed.app hOp'' hArg
      exact hRes
  | @var Γp sp i _ hi =>
      intro s_extra hpvAppend
      exact MEqRed.var hpvAppend hi
  | @tAp Γp sp u₀ _ hu =>
      intro s_extra hpvAppend
      exact MEqRed.tAp hpvAppend hu
  | @bet Γp sp t v₀ v₀' body body' ht hbody harg ihBody _ihArg =>
      intro s_extra hpvAppend
      -- `Me-Bet`: `MEqRed Γp sp (.app (.abs t b) v₀) (instantiate 0 v₀' body')`.
      -- We want the same with `sp ++ s_extra`.
      -- Body sub-derivation has stack `Stack.shift 0 sp`; we need it at
      -- `Stack.shift 0 (sp ++ s_extra) = Stack.shift 0 sp ++ Stack.shift 0 s_extra`.
      have hShift_append :
          Stack.shift 0 (sp ++ s_extra) =
            Stack.shift 0 sp ++ Stack.shift 0 s_extra := by
        unfold Stack.shift Stack.shiftBy
        exact List.map_append _ _ _
      -- PrevalidExt the body's appended stack: weaken `hpvAppend` over the new
      -- `.sub t` head, which yields prevalid for the shifted concatenation.
      have hpvBodyHead :
          Prevalid ({ bound := t, kind := .sub } :: Γp) :=
        Prevalid.sub (PrevalidExt.ctx hpvAppend) ht
      have hpvBodyAppend :
          PrevalidExt ({ bound := t, kind := .sub } :: Γp)
            (Stack.shift 0 (sp ++ s_extra)) :=
        PrevalidExt.weaken_head hpvAppend hpvBodyHead
      have hpvBodyAppend' :
          PrevalidExt ({ bound := t, kind := .sub } :: Γp)
            (Stack.shift 0 sp ++ Stack.shift 0 s_extra) := by
        rw [← hShift_append]; exact hpvBodyAppend
      -- Apply IH to body (note the IH for `hbody` matches stack
      -- `Stack.shift 0 sp ++ s_extra'`; we instantiate `s_extra' = Stack.shift 0 s_extra`).
      have hBody' :
          MEqRed ({ bound := t, kind := .sub } :: Γp)
            (Stack.shift 0 sp ++ Stack.shift 0 s_extra) body body' :=
        ihBody hpvBodyAppend'
      have hBody'' :
          MEqRed ({ bound := t, kind := .sub } :: Γp)
            (Stack.shift 0 (sp ++ s_extra)) body body' := by
        rw [hShift_append]; exact hBody'
      exact MEqRed.bet ht hBody'' harg
  | @fun_ Γp t t' body body' hbound hbody _ihBound ihBody =>
      intro s_extra hpvAppend
      -- Source: `MEqRed Γp [] (.abs t b) (.abs t' b')`.
      -- After append: `MEqRed Γp s_extra ...`.
      cases s_extra with
      | nil =>
          -- Trivial: just re-apply Me-Fun.
          simpa [List.append_nil] using MEqRed.fun_ hbound hbody
      | cons α rest =>
          -- Non-empty: switch from Me-Fun to Me-FOp.
          have hα_scoped : Term.Scoped Γp.depth α := by
            have hpv' : PrevalidExt Γp (α :: rest) := by
              simpa [List.nil_append] using hpvAppend
            exact PrevalidExt.head_scoped hpv'
          have hpvRest : PrevalidExt Γp rest := by
            have hpv' : PrevalidExt Γp (α :: rest) := by
              simpa [List.nil_append] using hpvAppend
            exact PrevalidExt.tail hpv'
          -- Build PrevalidExt for the body in the .sub-headed extended context
          -- with the SHIFTED rest stack, which we need to invoke the IH.
          have ht_scoped : Term.Scoped Γp.depth t := hbound.scoped_left
          have hpvBodyHeadSub :
              Prevalid ({ bound := t, kind := .sub } :: Γp) :=
            Prevalid.sub (PrevalidExt.ctx hpvAppend) ht_scoped
          have hpvBodySub :
              PrevalidExt ({ bound := t, kind := .sub } :: Γp)
                (Stack.shift 0 rest) :=
            PrevalidExt.weaken_head hpvRest hpvBodyHeadSub
          -- Apply IH on body: source stack `[]`, target `[] ++ Stack.shift 0 rest = Stack.shift 0 rest`.
          have hBodyShifted :
              MEqRed ({ bound := t, kind := .sub } :: Γp)
                (Stack.shift 0 rest) body body' := by
            have := ihBody (s_extra := Stack.shift 0 rest)
              (by simpa [List.nil_append] using hpvBodySub)
            simpa [List.nil_append] using this
          -- Convert .sub head to .equ head with new bound `α`.
          have hBodyEqu :
              MEqRed ({ bound := α, kind := .equ } :: Γp)
                (Stack.shift 0 rest) body body' :=
            MEqRed.sub_to_equ_head_replace hBodyShifted hα_scoped
          -- Reassemble as Me-FOp.
          simpa [List.nil_append] using
            MEqRed.fOp hbound hα_scoped hBodyEqu
  | @fOp Γp sp t t' α body body' hbound hα hbody _ihBound ihBody =>
      intro s_extra hpvAppend
      -- Source: `MEqRed Γp (α :: sp) (.abs t b) (.abs t' b')`.
      -- After append: `MEqRed Γp (α :: (sp ++ s_extra)) ...`.
      have hShift_append :
          Stack.shift 0 (sp ++ s_extra) =
            Stack.shift 0 sp ++ Stack.shift 0 s_extra := by
        unfold Stack.shift Stack.shiftBy
        exact List.map_append _ _ _
      have hpvAppend' : PrevalidExt Γp (sp ++ s_extra) := by
        have h₁ : PrevalidExt Γp ((α :: sp) ++ s_extra) := by
          simpa [List.cons_append] using hpvAppend
        exact PrevalidExt.tail h₁
      have hpvBodyHead :
          Prevalid ({ bound := α, kind := .equ } :: Γp) :=
        Prevalid.equ (PrevalidExt.ctx hpvAppend') hα
      have hpvBodyAppend :
          PrevalidExt ({ bound := α, kind := .equ } :: Γp)
            (Stack.shift 0 (sp ++ s_extra)) :=
        PrevalidExt.weaken_head hpvAppend' hpvBodyHead
      have hpvBodyAppend' :
          PrevalidExt ({ bound := α, kind := .equ } :: Γp)
            (Stack.shift 0 sp ++ Stack.shift 0 s_extra) := by
        rw [← hShift_append]; exact hpvBodyAppend
      have hBody' :
          MEqRed ({ bound := α, kind := .equ } :: Γp)
            (Stack.shift 0 sp ++ Stack.shift 0 s_extra) body body' :=
        ihBody hpvBodyAppend'
      have hBody'' :
          MEqRed ({ bound := α, kind := .equ } :: Γp)
            (Stack.shift 0 (sp ++ s_extra)) body body' := by
        rw [hShift_append]; exact hBody'
      have hRes :
          MEqRed Γp (α :: (sp ++ s_extra)) (.abs t body) (.abs t' body') :=
        MEqRed.fOp hbound hα hBody''
      simpa [List.cons_append] using hRes

/-- **Empty-source stack-extension for `MEqRed`.** Specialization of
`MEqRed.append_stack` to the case `s = []`: lift an empty-stack
derivation to any prevalid stack. This is the form consumed by the
asymmetric Lemma 32. -/
noncomputable def MEqRed.lift_empty_to_stack
    {Γ : Ctx} {u v : Term} {s : Stack}
    (h : MEqRed Γ [] u v)
    (hpv : PrevalidExt Γ s) :
    MEqRed Γ s u v := by
  have h' := h.append_stack (s_extra := s) (by simpa [List.nil_append] using hpv)
  simpa [List.nil_append] using h'

/-! ## Iterated head-extension weakening for `MEqRed` (Type-valued)

The Prop-wrapper version `MEqRedJ_appendCtx` lives in
`Pss/Paper/Aux/Weakening.lean`. The wall discharge below needs the
Type-valued analogue (Lean's `MEqRed` is `Type`-valued; commit
`ad3ff08`), so we ship it explicitly here with the same induction
strategy. -/

private theorem stack_shift_compose_local (n : Nat) (s : Stack) :
    Stack.shift 0 (Stack.shiftBy 0 n s) = Stack.shiftBy 0 (n + 1) s := by
  induction s with
  | nil => rfl
  | cons α rest ih =>
      change
        Term.shift 0 (Term.shiftBy 0 n α) ::
            Stack.shift 0 (Stack.shiftBy 0 n rest) =
          Term.shiftBy 0 (n + 1) α :: Stack.shiftBy 0 (n + 1) rest
      have hAlpha : Term.shift 0 (Term.shiftBy 0 n α) =
          Term.shiftBy 0 (n + 1) α := by
        simpa [Term.shift] using Term.shiftBy_compose 0 n 1 α
      simp [hAlpha, ih]

private theorem stack_shiftBy_zero_id_local (s : Stack) :
    Stack.shiftBy 0 0 s = s := by
  induction s with
  | nil => rfl
  | cons α rest ih =>
      change Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 rest = α :: rest
      simp [Term.shiftBy_zero_id, ih]

/-- Type-valued iterated head-extension for `MEqRed`. Mirrors
`MEqRedJ_appendCtx` but returns the constructive derivation. -/
noncomputable def MEqRed.appendCtx
    {Γ : Ctx} {s : Stack} {u v : Term} (Γ' : Ctx)
    (h : MEqRed Γ s u v)
    (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    MEqRed (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id_local,
        Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep : MEqRed (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s)
          (Term.shiftBy 0 Γ''.length u) (Term.shiftBy 0 Γ''.length v) :=
        ih hpvTail
      have hpvEIter : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        Pss.DeBruijn.Paper.Weakening.PrevalidExt_appendCtx Γ'' hpvE hpvTail
      have hHead :
          MEqRed (head :: (Γ'' ++ Γ))
            (Stack.shift 0 (Stack.shiftBy 0 Γ''.length s))
            (Term.shift 0 (Term.shiftBy 0 Γ''.length u))
            (Term.shift 0 (Term.shiftBy 0 Γ''.length v)) :=
        hStep.weaken_head hpvEIter hpv
      have hStackCompose :
          Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
            Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose_local Γ''.length s
      have hUCompose :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hVCompose :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hStackCompose, hUCompose, hVCompose,
        List.cons_append] using hHead

end DeBruijn
end Pss
