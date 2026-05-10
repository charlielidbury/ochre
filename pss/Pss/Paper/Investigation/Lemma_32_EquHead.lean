import Pss.Paper.Investigation.Lemma_32_Asymmetric
import Pss.Paper.Aux.StackExtension

/-! # `Pss.Paper.Investigation.Lemma_32_EquHead` —
**`.equ`-head Lemma 32 prelude** (prevalidity transport).

Paper Lemma 32 (Pasquale & García-Pérez 2024, p. 9:44) at `.equ`-head:
if `Γ, x ≡ v, Γ' ⊢ u → u'` and `Γ; nil ⊢ v → v'`, then
`Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] → u'[x\v']`.

This file ships the prevalidity-transport prelude. The full Lemma 32 at
`.equ`-head is **not yet shipped**; only the prevalidity transport for
the `.equ`-head substituted slot is available here.

The full Lemma 32 at `.equ`-head requires a non-trivial `Me-Pro at slot
heads.length` case (paper p. 9:44, "Rule Me-Pro with u = x") which
recursively applies the lemma to the inner derivation. The
machinery is a port of `Lemma_32_KindNarrowedAsymmetric` to `.equ`-head
with the substituted slot's bound equal to `arg`.

Future work: ship the full `.equ`-head Lemma 32 here (estimated ~500
lines).
-/

namespace Pss
namespace DeBruijn
namespace Paper
namespace Investigation

/-! ## Prevalidity transport at `.equ`-head substituted slot -/

private noncomputable def prevalid_head_scoped_local
    {Γ : Ctx} {head : Term} {kind : CtxEntryKind}
    (hpv : Prevalid ({ bound := head, kind := kind } :: Γ)) :
    Term.Scoped Γ.depth head := by
  cases kind with
  | sub =>
      cases hpv with
      | sub _ hHead => exact hHead
  | equ =>
      cases hpv with
      | equ _ hHead => exact hHead

/-- Generic prevalidity transport for the preserved context prefix after
a β-instantiation removes the `.equ` entry below it. -/
noncomputable def BetaInstantiationPreservesPrevalidPrefixEquHead
    {Γ : Ctx} {arg : Term} (heads : Ctx)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : Prevalid (heads ++ { bound := arg, kind := .equ } :: Γ)) :
    Prevalid (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) := by
  induction heads with
  | nil =>
      simpa [Ctx.instantiateBetaPrefix] using Prevalid.tail hpv
  | cons head heads ih =>
      have hpvTail :
          Prevalid (heads ++ { bound := arg, kind := .equ } :: Γ) :=
        Prevalid.tail hpv
      have hTail := ih hpvTail
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hHeadScoped :
          Term.Scoped (Γ.depth + heads.length + 1) head.bound := by
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using prevalid_head_scoped_local hpv
      have hHeadInstScoped :
          Term.Scoped
            (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) head.bound) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg)
          head.bound (by omega) hArgShiftScoped hHeadScoped
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hInst
      cases head with
      | mk headBound kind =>
          cases kind with
          | sub =>
              exact Prevalid.sub hTail hHeadInstScoped
          | equ =>
              exact Prevalid.equ hTail hHeadInstScoped

/-- Generic `PrevalidExt` transport at `.equ`-head substituted slot. -/
noncomputable def BetaInstantiationPreservesPrevalidExtUnderHeadsEquHead
    {Γ : Ctx} {arg : Term} {heads : Ctx} {s : Stack} {n : Nat}
    (hlen : heads.length = n)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .equ } :: Γ) s) :
    PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
      (Stack.instantiate n (Term.shiftBy 0 n arg) s) := by
  subst hlen
  have hctx :=
    BetaInstantiationPreservesPrevalidPrefixEquHead heads hArgScoped
      (PrevalidExt.ctx hpv)
  have hArgShiftScoped :
      Term.Scoped (Γ.depth + heads.length)
        (Term.shiftBy 0 heads.length arg) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Term.shiftBy_scoped 0 heads.length Γ.depth arg
        (Nat.zero_le Γ.depth) hArgScoped
  have hsSource :
      Stack.Scoped (Γ.depth + heads.length + 1) s := by
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using PrevalidExt.stack_scoped hpv
  have hsTarget :
      Stack.Scoped
        (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
        (Stack.instantiate heads.length
          (Term.shiftBy 0 heads.length arg) s) := by
    have hStack := Stack.Scoped.instantiate
      (depth := Γ.depth + heads.length)
      (k := heads.length)
      (v := Term.shiftBy 0 heads.length arg)
      (s := s) (by omega) hArgShiftScoped hsSource
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hStack
  exact PrevalidExt.of_stack_scoped hctx hsTarget

end Investigation
end Paper
end DeBruijn
end Pss
