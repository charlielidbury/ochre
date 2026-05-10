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
  | @ctAnn Γ Γ' s s' t t' kind hInner hred ih =>
      -- Stack is unchanged by ctAnn; recurse to peel α off the inner derivation
      -- and rewrap the result with ctAnn.
      obtain ⟨α', s_1, hs', hInner_strip⟩ := ih hStack
      exact ⟨α', s_1, hs',
        ContextEvolution.ctAnn hInner_strip hred⟩
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
