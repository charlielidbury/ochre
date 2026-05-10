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

/-! ## equBinds lookup transport at `.equ`-head substituted slot

Classification of the lookup result: either the lookup hit the
substituted slot (returning the bound), or it hit a preserved binding. -/

/-- Case dispatch for an `equBinds` lookup through the `.equ`-head
β-instantiation prefix. -/
inductive Ctx.EquBindsBetaEquHeadCase
    (Γ : Ctx) (arg α : Term) (heads : Ctx) (i : Nat) : Prop where
  /-- Lookup hit the substituted slot. `i = heads.length`; `α = shift_by
  (heads.length + 1) arg`. -/
  | argSlot
      (hi : i = heads.length)
      (hα : α = Term.shiftBy 0 (heads.length + 1) arg)
  /-- Lookup hit a preserved binding (in heads or Γ). -/
  | preserved
      (j : Nat)
      (var_eq :
        Term.instantiate heads.length (Term.shiftBy 0 heads.length arg)
          (.bvar i) = .bvar j)
      (bind :
        Ctx.equBinds (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) j
          (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α))

/-- Transport an `equBinds` lookup through the `.equ`-head β-instantiation
prefix. -/
noncomputable def Ctx.equBinds_beta_equHead_classify
    {Γ : Ctx} {arg α : Term} {heads : Ctx} {i : Nat}
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .equ } :: Γ) i α) :
    Ctx.EquBindsBetaEquHeadCase Γ arg α heads i := by
  induction heads generalizing i α with
  | nil =>
      -- (heads = []) Source context is {arg,.equ}::Γ.
      cases i with
      | zero =>
          -- Lookup at slot 0 hits the substituted slot. α = shift 0 arg.
          have hαEq : α = Term.shift 0 arg := by
            simp [Ctx.equBinds] at hb
            exact hb.symm
          refine Ctx.EquBindsBetaEquHeadCase.argSlot rfl ?_
          simp [Term.shift] at hαEq ⊢
          exact hαEq
      | succ i =>
          -- Lookup at slot i+1 descends into Γ.
          simp [Ctx.equBinds] at hb
          let tailTarget := Classical.choose hb
          have htailAnd := Classical.choose_spec hb
          have htailLookup : Ctx.lookupEqu Γ i = some tailTarget := htailAnd.1
          have htarget : Term.shift 0 tailTarget = α := htailAnd.2
          have htargetInst :
              Term.instantiate 0 arg α = tailTarget := by
            simpa [← htarget] using Term.instantiate_shift_id 0 arg tailTarget
          have htargetInst' :
              Term.instantiate 0 (Term.shiftBy 0 0 arg) α = tailTarget := by
            simpa [Term.shiftBy_zero_id] using htargetInst
          refine Ctx.EquBindsBetaEquHeadCase.preserved i ?_ ?_
          · simp [Term.instantiate]
          · simpa [Ctx.instantiateBetaPrefix, Ctx.equBinds, htargetInst'] using
              htailLookup
  | cons head heads ih =>
      cases head with
      | mk headBound kind =>
          cases i with
          | zero =>
              cases kind with
              | sub =>
                  -- .sub head: lookup at 0 fails. Vacuous.
                  simp [Ctx.equBinds] at hb
              | equ =>
                  -- .equ head: lookup returns shift 0 headBound = α.
                  simp [Ctx.equBinds] at hb
                  subst hb
                  have htargetInst :
                      Term.instantiate (heads.length + 1)
                          (Term.shiftBy 0 (heads.length + 1) arg)
                          (Term.shift 0 headBound) =
                        Term.shift 0
                          (Term.instantiate heads.length
                            (Term.shiftBy 0 heads.length arg) headBound) := by
                    have h := Term.instantiate_succ_shift_zero heads.length
                      (Term.shiftBy 0 heads.length arg) headBound
                    simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                      using h
                  refine Ctx.EquBindsBetaEquHeadCase.preserved 0 ?_ ?_
                  · simp [Term.instantiate]
                  · simp only [List.length_cons]
                    simp [Ctx.instantiateBetaPrefix, Ctx.equBinds, htargetInst]
          | succ i =>
              -- Recurse into the tail.
              simp [Ctx.equBinds] at hb
              let tailTarget := Classical.choose hb
              have htailAnd := Classical.choose_spec hb
              have htailLookup :
                  Ctx.lookupEqu (heads ++ { bound := arg, kind := .equ } :: Γ) i =
                    some tailTarget := htailAnd.1
              have htarget : Term.shift 0 tailTarget = α := htailAnd.2
              have hbTail :
                  Ctx.equBinds (heads ++ { bound := arg, kind := .equ } :: Γ)
                    i tailTarget := by
                simpa [Ctx.equBinds] using htailLookup
              -- Recursive classification.
              cases hcase : ih hbTail with
              | argSlot hi_eq hα_eq =>
                  -- Inner at-slot: i = heads.length, tailTarget = shift_by (heads.length+1) arg.
                  -- So α = shift 0 tailTarget = shift 0 (shift_by (heads.length+1) arg) = shift_by (heads.length+2) arg.
                  -- The outer index is i+1 = heads.length+1, which matches outer-heads.length = heads.length+1.
                  refine Ctx.EquBindsBetaEquHeadCase.argSlot ?_ ?_
                  · simp only [List.length_cons]
                    omega
                  · rw [← htarget, hα_eq]
                    -- Goal: Term.shift 0 (Term.shiftBy 0 (heads.length+1) arg)
                    --       = Term.shiftBy 0 (({headBound,kind}::heads).length + 1) arg
                    -- = Term.shiftBy 0 (heads.length + 1 + 1) arg.
                    simp only [List.length_cons]
                    have h := Term.shiftBy_compose 0 (heads.length + 1) 1 arg
                    simpa [Term.shift] using h
              | preserved j hvar hbind =>
                  -- Inner preserved: get j+1 in outer.
                  refine Ctx.EquBindsBetaEquHeadCase.preserved (j + 1) ?_ ?_
                  · -- Variable transport.
                    have hvarCurrent :
                        Term.instantiate (heads.length + 1)
                            (Term.shiftBy 0 (heads.length + 1) arg) (.bvar (i + 1)) =
                          Term.shift 0
                            (Term.instantiate heads.length
                              (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
                      have h := Term.instantiate_succ_shift_zero heads.length
                        (Term.shiftBy 0 heads.length arg) (.bvar i)
                      simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                        using h
                    simp only [List.length_cons]
                    rw [hvarCurrent, hvar]
                    simp [Term.shift]
                  · -- equBinds transport.
                    have htargetInst :
                        Term.instantiate (heads.length + 1)
                            (Term.shiftBy 0 (heads.length + 1) arg) α =
                          Term.shift 0
                            (Term.instantiate heads.length
                              (Term.shiftBy 0 heads.length arg) tailTarget) := by
                      have h := Term.instantiate_succ_shift_zero heads.length
                        (Term.shiftBy 0 heads.length arg) tailTarget
                      simpa [← htarget, Term.shift, Term.shiftBy_compose,
                        Nat.add_assoc] using h
                    let headEntry : CtxEntry :=
                      { bound := Term.instantiate heads.length
                          (Term.shiftBy 0 heads.length arg) headBound,
                        kind := kind }
                    simp only [List.length_cons]
                    change Ctx.equBinds
                      (headEntry ::
                        (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
                      (j + 1)
                      (Term.instantiate (heads.length + 1)
                        (Term.shiftBy 0 (heads.length + 1) arg) α)
                    rw [htargetInst]
                    have hlook : Ctx.lookupEqu
                        (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) j =
                          some (Term.instantiate heads.length
                            (Term.shiftBy 0 heads.length arg) tailTarget) := by
                      simpa [Ctx.equBinds] using hbind
                    -- equBinds (headEntry :: ...) (j+1) (shift 0 (instantiate ... tailTarget))
                    -- = lookupEqu (...) j = some (instantiate ... tailTarget) via shift unwrap.
                    cases kind with
                    | sub =>
                        simp [Ctx.equBinds, headEntry, hlook]
                    | equ =>
                        simp [Ctx.equBinds, headEntry, hlook]

end Investigation
end Paper
end DeBruijn
end Pss
