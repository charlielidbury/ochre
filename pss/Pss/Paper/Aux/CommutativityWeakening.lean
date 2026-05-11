import Pss.Paper.ContextEvolution

/-! # `Pss.Paper.Aux.CommutativityWeakening` — paper Lemma 36

Mechanizes Lemma 36 of Pasquale & García-Pérez 2024 (p. 9:46),
"Commutativity — context weakening": stack changes can be stripped from
a single extended-context reduction, leaving the underlying empty-stack
context reduction.

The paper's proof is by induction on `s` and is reproduced verbatim in
the docstring of `Lemma_36_CommutativityContextWeakening` below. The
mechanization mirrors that proof structure, including a small helper
(`stripStackHead`) for the inversion step the paper invokes textually as
"By rule Ct-Stk we then have …".

This file is part of the paper-mirroring layer; the working de Bruijn
counterpart is `Pss.DeBruijn.ExtCtxRed.lemma_36` in
`Pss/Mpss/DeBruijnContextRed.lean`. The two are independent.
-/

namespace Pss
namespace DeBruijn
namespace Paper

namespace ContextEvolution

/-- Inversion lemma for a non-empty stack on the LHS of a context-evolution.

The paper's proof of Lemma 36 (p. 9:46) writes "By rule Ct-Stk we then
have `Γ; s_0 ↣ Γ'; s_1`, with `s' = α' :: s_1` for some term `α'`."
That is inversion: a derivation whose LHS stack is `α :: s_0` admits a
sub-derivation at the smaller stack `s_0`, and the RHS stack starts with
some `α'`.

The paper handles the case textually by appealing to "rule Ct-Stk" alone
without spelling out the reflexivity / `ctAnn` cases the de Bruijn
mechanization makes explicit. -- Paper handwaves; mechanized as:
structural recursion on the derivation, casing on each constructor. -/
theorem stripStackHead {Γ Γ' : Ctx} {s s' s_0 : Stack} {α : Term}
    (hStack : s = α :: s_0)
    (h : ContextEvolution Γ s Γ' s') :
    ∃ α' s_1, s' = α' :: s_1 ∧ ContextEvolution Γ s_0 Γ' s_1 := by
  induction h generalizing s_0 α with
  | @ctRefl Γ s =>
      -- s' = s = α :: s_0; pick α' = α, s_1 = s_0; sub-derivation is ctRefl.
      subst hStack
      exact ⟨α, s_0, rfl, ContextEvolution.ctRefl⟩
  | @ctAnn Γ_inner Γ_inner' s_inner s_inner' t t' kind hInner hred ih =>
      -- Post-fix: ctAnn now shifts the stack. Outer LHS stack is
      -- `Stack.shift 0 s_inner`. The hStack hypothesis says
      -- `Stack.shift 0 s_inner = α :: s_0`. Inversion: `s_inner = α'' :: s_0''`
      -- with `α = Term.shift 0 α''` and `s_0 = Stack.shift 0 s_0''`.
      cases s_inner with
      | nil =>
          simp [Stack.shift, Stack.shiftBy] at hStack
      | cons α'' s_0'' =>
          have hSplit : Term.shift 0 α'' = α ∧ Stack.shift 0 s_0'' = s_0 := by
            simp [Stack.shift, Stack.shiftBy] at hStack
            exact hStack
          obtain ⟨α_inner', s_1_inner', hs_inner', hInner_strip⟩ := ih rfl
          subst hs_inner'
          refine ⟨Term.shift 0 α_inner', Stack.shift 0 s_1_inner', ?_, ?_⟩
          · simp [Stack.shift, Stack.shiftBy, Term.shift]
          · have hL : ContextEvolution
                ({bound := t, kind} :: Γ_inner) (Stack.shift 0 s_0'')
                ({bound := t', kind} :: Γ_inner') (Stack.shift 0 s_1_inner') :=
              ContextEvolution.ctAnn hInner_strip hred
            rw [← hSplit.2]
            exact hL
  | @ctStk Γ Γ' s s' β β' hInner hred _ =>
      -- Outer rule is Ct-Stk; the inner premise is exactly the result.
      cases hStack
      exact ⟨β', s', rfl, hInner⟩
  | @cons_lift Γ_inner Γ_inner' s_inner s_inner' entry hInner hBoundScoped ih =>
      -- Outer LHS stack is `Stack.shift 0 s_inner`. The hStack hypothesis says
      -- `Stack.shift 0 s_inner = α :: s_0`. Inversion: `s_inner = α'' :: s_0''`
      -- with `α = Term.shift 0 α''` and `s_0 = Stack.shift 0 s_0''`.
      cases s_inner with
      | nil =>
          -- Stack.shift 0 [] = [] ≠ α :: s_0. Contradiction.
          simp [Stack.shift, Stack.shiftBy] at hStack
      | cons α'' s_0'' =>
          -- Stack.shift 0 (α'' :: s_0'') = Term.shift 0 α'' :: Stack.shift 0 s_0''.
          have hSplit : Term.shift 0 α'' = α ∧ Stack.shift 0 s_0'' = s_0 := by
            simp [Stack.shift, Stack.shiftBy] at hStack
            exact hStack
          -- Recurse on the inner derivation to split off α''.
          obtain ⟨α_inner', s_1_inner', hs_inner', hInner_strip⟩ := ih rfl
          -- s_inner' = α_inner' :: s_1_inner'. Apply cons_lift to recover the
          -- stripped evolution at the cons-context's shifted stack.
          subst hs_inner'
          refine ⟨Term.shift 0 α_inner', Stack.shift 0 s_1_inner', ?_, ?_⟩
          · -- The post-shift output stack: Stack.shift 0 (α_inner' :: s_1_inner')
            --   = Term.shift 0 α_inner' :: Stack.shift 0 s_1_inner'.
            simp [Stack.shift, Stack.shiftBy, Term.shift]
          · -- ContextEvolution (entry :: Γ_inner) (Stack.shift 0 s_0'')
            --   (entry :: Γ_inner') (Stack.shift 0 s_1_inner') via cons_lift on
            --   hInner_strip.
            have hL : ContextEvolution
                (entry :: Γ_inner) (Stack.shift 0 s_0'')
                (entry :: Γ_inner') (Stack.shift 0 s_1_inner') :=
              ContextEvolution.cons_lift hInner_strip hBoundScoped
            -- Goal stack on the LHS is `s_0` (which by hSplit.2 equals
            -- `Stack.shift 0 s_0''`).
            rw [← hSplit.2]
            exact hL

/-! ## Stack-head inversion with reduction

The richer cousin of `stripStackHead`: in addition to the smaller-stack
sub-derivation, this version also recovers the **head reduction**
`MEqRed Γ [] α α'` at the OUTER `Γ`. The `MEqRed` lives at the outer
context (not at the inner of any `ctAnn` step), so the resulting head
reduction can be fed directly to `ContextEvolution.cons_evolve` /
`MEqRed.bet` / `MEqRed.fOp` body-context builders.

This lemma was the load-bearing infrastructure for Lemma 2's FOpFOp /
AppBet / BetApp cases at general context (paper p. 9:22-25): the
extracted `α →= α'` step feeds the body context's mid-proof `Ct-Ann`
that evolves the equ-bound from the popped operand on both sides. -/

/-- Auxiliary "general inversion" lemma for `stripStackHeadWithReduction`.
This version states the conclusion under the literal `α :: s` / `α' :: s'`
forms (so the recursion is on the evolution, not on the stack shape). -/
private theorem stripStackHeadWithReduction_aux
    {Γ Γ' : Ctx} {sSrc sTgt : Stack}
    (h : ContextEvolution Γ sSrc Γ' sTgt) :
    ∀ {α α' : Term} {s s' : Stack},
      sSrc = α :: s → sTgt = α' :: s' →
      Term.Scoped Γ.depth α →
      PrevalidExt Γ sSrc →
      Nonempty (MEqRed Γ [] α α') ∧ ContextEvolution Γ s Γ' s' := by
  induction h with
  | @ctRefl Γp sp =>
      intro α α' s s' hSrc hTgt hα hpv
      -- sp = α::s = α'::s', so α = α', s = s'.
      subst hSrc
      cases hTgt
      refine ⟨⟨?_⟩, ContextEvolution.ctRefl⟩
      exact MEqRed.refl (PrevalidExt.nil (PrevalidExt.ctx hpv)) hα
  | @ctAnn Γp Γp' sp sp' t t' kind hInner hred ih =>
      intro α α' s s' hSrc hTgt hα hpv
      -- Outer LHS stack = shift 0 sp = α::s.
      cases sp with
      | nil =>
          simp [Stack.shift, Stack.shiftBy] at hSrc
      | cons α'' s_0'' =>
          have hShiftSrc :
              Term.shift 0 α'' = α ∧ Stack.shift 0 s_0'' = s := by
            simp [Stack.shift, Stack.shiftBy] at hSrc
            exact hSrc
          cases sp' with
          | nil =>
              have hLen := hInner.preserves_stack_length
              simp at hLen
          | cons α''' s_1''' =>
              have hShiftTgt :
                  Term.shift 0 α''' = α' ∧ Stack.shift 0 s_1''' = s' := by
                simp [Stack.shift, Stack.shiftBy] at hTgt
                exact hTgt
              -- Set up inner scoping / prevalidity.
              have hα_at_Γp : Term.Scoped Γp.depth α'' := by
                obtain ⟨hShiftα, _⟩ := hShiftSrc
                rw [← hShiftα] at hα
                have hScopedSucc :
                    Term.Scoped (Γp.depth + 1) (Term.shift 0 α'') := by
                  simpa [Ctx.depth_cons] using hα
                exact Term.shift_scoped_inv 0 Γp.depth α''
                  (Nat.zero_le _) hScopedSucc
              have hpvCtxOuter : Prevalid ({bound := t, kind} :: Γp) :=
                PrevalidExt.ctx hpv
              have hpvCtxInner : Prevalid Γp := Prevalid.tail hpvCtxOuter
              have hStackScopedShifted :
                  Stack.Scoped (Γp.depth + 1) (Stack.shift 0 (α'' :: s_0'')) := by
                have hStackScoped := PrevalidExt.stack_scoped hpv
                simp [Ctx.depth_cons] at hStackScoped
                exact hStackScoped
              have hStackScopedInner :
                  Stack.Scoped Γp.depth (α'' :: s_0'') :=
                Stack.Scoped.shift_inv hStackScopedShifted
              have hpvInner : PrevalidExt Γp (α'' :: s_0'') :=
                PrevalidExt.of_stack_scoped hpvCtxInner hStackScopedInner
              -- Recurse.
              obtain ⟨hHeadInner, hStripInner⟩ :=
                ih (α := α'') (α' := α''') (s := s_0'') (s' := s_1''')
                  rfl rfl hα_at_Γp hpvInner
              let hHeadInner₀ : MEqRed Γp [] α'' α''' := Classical.choice hHeadInner
              -- Lift head reduction via weaken_head.
              let hpvE_nil : PrevalidExt Γp [] := PrevalidExt.nil hpvCtxInner
              let hHeadOuter :
                  MEqRed ({bound := t, kind} :: Γp) [] (Term.shift 0 α'') (Term.shift 0 α''') := by
                have h := hHeadInner₀.weaken_head hpvE_nil hpvCtxOuter
                simpa using h
              refine ⟨⟨?_⟩, ?_⟩
              · obtain ⟨hα_eq, _⟩ := hShiftSrc
                obtain ⟨hα'_eq, _⟩ := hShiftTgt
                rw [← hα_eq, ← hα'_eq]
                exact hHeadOuter
              · obtain ⟨_, hs_eq⟩ := hShiftSrc
                obtain ⟨_, hs'_eq⟩ := hShiftTgt
                rw [← hs_eq, ← hs'_eq]
                exact ContextEvolution.ctAnn hStripInner hred
  | @ctStk Γp Γp' sp sp' β β' hInner hred _ =>
      intro α α' s s' hSrc hTgt _hα _hpv
      -- Outer LHS = β::sp = α::s, output = β'::sp' = α'::s'.
      cases hSrc
      cases hTgt
      exact ⟨⟨hred⟩, hInner⟩
  | @cons_lift Γp Γp' sp sp' entry hInner hBoundScoped ih =>
      intro α α' s s' hSrc hTgt hα hpv
      cases sp with
      | nil =>
          simp [Stack.shift, Stack.shiftBy] at hSrc
      | cons α'' s_0'' =>
          have hShiftSrc :
              Term.shift 0 α'' = α ∧ Stack.shift 0 s_0'' = s := by
            simp [Stack.shift, Stack.shiftBy] at hSrc
            exact hSrc
          cases sp' with
          | nil =>
              have hLen := hInner.preserves_stack_length
              simp at hLen
          | cons α''' s_1''' =>
              have hShiftTgt :
                  Term.shift 0 α''' = α' ∧ Stack.shift 0 s_1''' = s' := by
                simp [Stack.shift, Stack.shiftBy] at hTgt
                exact hTgt
              have hα_at_Γp : Term.Scoped Γp.depth α'' := by
                obtain ⟨hShiftα, _⟩ := hShiftSrc
                rw [← hShiftα] at hα
                have hScopedSucc :
                    Term.Scoped (Γp.depth + 1) (Term.shift 0 α'') := by
                  simpa [Ctx.depth_cons] using hα
                exact Term.shift_scoped_inv 0 Γp.depth α''
                  (Nat.zero_le _) hScopedSucc
              have hpvCtxOuter : Prevalid (entry :: Γp) :=
                PrevalidExt.ctx hpv
              have hpvCtxInner : Prevalid Γp := Prevalid.tail hpvCtxOuter
              have hStackScopedShifted :
                  Stack.Scoped (Γp.depth + 1) (Stack.shift 0 (α'' :: s_0'')) := by
                have hStackScoped := PrevalidExt.stack_scoped hpv
                simp [Ctx.depth_cons] at hStackScoped
                exact hStackScoped
              have hStackScopedInner :
                  Stack.Scoped Γp.depth (α'' :: s_0'') :=
                Stack.Scoped.shift_inv hStackScopedShifted
              have hpvInner : PrevalidExt Γp (α'' :: s_0'') :=
                PrevalidExt.of_stack_scoped hpvCtxInner hStackScopedInner
              obtain ⟨hHeadInner, hStripInner⟩ :=
                ih (α := α'') (α' := α''') (s := s_0'') (s' := s_1''')
                  rfl rfl hα_at_Γp hpvInner
              let hHeadInner₀ : MEqRed Γp [] α'' α''' := Classical.choice hHeadInner
              let hpvE_nil : PrevalidExt Γp [] := PrevalidExt.nil hpvCtxInner
              let hHeadOuter :
                  MEqRed (entry :: Γp) [] (Term.shift 0 α'') (Term.shift 0 α''') := by
                have h := hHeadInner₀.weaken_head hpvE_nil hpvCtxOuter
                simpa using h
              refine ⟨⟨?_⟩, ?_⟩
              · obtain ⟨hα_eq, _⟩ := hShiftSrc
                obtain ⟨hα'_eq, _⟩ := hShiftTgt
                rw [← hα_eq, ← hα'_eq]
                exact hHeadOuter
              · obtain ⟨_, hs_eq⟩ := hShiftSrc
                obtain ⟨_, hs'_eq⟩ := hShiftTgt
                rw [← hs_eq, ← hs'_eq]
                exact ContextEvolution.cons_lift hStripInner hBoundScoped

/-- Pull a head `α` (with scoping at `Γ.depth`) off the LHS of a
`ContextEvolution`, returning both the head reduction `α →= α'` at the
outer `Γ; nil` AND the stripped sub-derivation on the smaller stack.

The de Bruijn-faithful `ctAnn` rule shifts its stack, so every
constructor that touches the stack head produces a `shift 0`-form
outer stack; the head reduction at the outer level is then either
given directly (`ctStk`) or lifted from the inner via `weaken_head`
(`ctAnn`, `cons_lift`).

`ctRefl` produces `α = α'` and the head reduction is `MEqRed.refl`
on `α` at the outer context. -/
theorem stripStackHeadWithReduction
    {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term}
    (h : ContextEvolution Γ (α :: s) Γ' (α' :: s'))
    (hα : Term.Scoped Γ.depth α)
    (hpv : PrevalidExt Γ (α :: s)) :
    Nonempty (MEqRed Γ [] α α') ∧ ContextEvolution Γ s Γ' s' :=
  stripStackHeadWithReduction_aux h rfl rfl hα hpv

/-- **Lemma 36 (Commutativity — context weakening), paper p. 9:46.**

> *Statement.* Let `Γ; s` and `Γ'; s'` be extended contexts such that
> `Γ; s ↣ Γ'; s'`. Then we have `Γ; nil ↣ Γ'; nil`.
>
> *Proof.* By induction on `s`.
>
> If `s = nil`: Then the result holds.
>
> If `s = α :: s_0`: Then by assumption we have `Γ; α :: s_0 ↣ Γ'; s'`.
> By rule Ct-Stk, we then have `Γ; s_0 ↣ Γ'; s_1`, with `s' = α' :: s_1`
> for some term `α'`. By induction we finally have `Γ; nil ↣ Γ'; nil`.

The induction is on the structural list `s`. The base case `s = nil`
uses `preserves_stack_length` to conclude `s' = nil` from the assumption,
after which `h` itself is the goal. The cons case invokes
`stripStackHead` to obtain a smaller-stack sub-derivation and recurses. -/
theorem Lemma_36_CommutativityContextWeakening
    {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s') :
    ContextEvolution Γ [] Γ' [] := by
  induction s generalizing Γ Γ' s' with
  | nil =>
      -- Paper: "If s = nil: Then the result holds."
      -- Stack length is preserved, so s' = []; h itself is the goal.
      have hLen : ([] : Stack).length = s'.length := h.preserves_stack_length
      have hsNil : s' = [] := List.length_eq_zero.mp hLen.symm
      exact hsNil ▸ h
  | cons α s_0 ih =>
      -- Paper: "If s = α :: s_0: Then by assumption we have
      --        Γ; α :: s_0 ↣ Γ'; s'. By rule Ct-Stk, we then have
      --        Γ; s_0 ↣ Γ'; s_1, with s' = α' :: s_1 for some term α'.
      --        By induction we finally have Γ; nil ↣ Γ'; nil."
      obtain ⟨α', s_1, _, hStrip⟩ :=
        stripStackHead (s := α :: s_0) (s_0 := s_0) (α := α) rfl h
      exact ih hStrip

end ContextEvolution

end Paper
end DeBruijn
end Pss
