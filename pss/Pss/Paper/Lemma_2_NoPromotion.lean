import Pss.Mpss.DeBruijnReductions

/-! # `Pss.Paper.Lemma_2_NoPromotion` — no-promotion-of-x predicate.

This file mechanises the paper's "no promotion of variable x" side
condition on `MEqRed` derivations, as introduced in paper Lemma 2's
"Moreover" clause (Pasquale & García-Pérez 2024, p. 9:9).

> *Side condition.* If in the derivation of `Γ_0; s_0 ⊢ t_0 →ᵉᵠᵘ t_1`
> there isn't an application of Me-Pro that makes a promotion of variable
> `x`, then in the derivation `Γ_2; s_2 ⊢ t_2 →ᵉᵠᵘ t_3` there won't be an
> application of Me-Pro that makes a promotion of variable `x`.

## Encoding

In de Bruijn, "variable x" is a Nat index in the outer context. A
Me-Pro application "promotes x" iff its source slot equals `x`. Under
binders, the de Bruijn index shifts up by 1, so the body sub-derivation
checks `x + 1`.

The predicate is `Prop`-valued and defined by structural recursion on
the `MEqRed` derivation tree.

## Usage

The paper uses this side condition in exactly one place: Case Me-App
with Me-Bet (p. 9:22-23). In that case, the body diamond's RHS source
derivation (the Me-Bet body, lifted to the `.equ`-extended context via
Lemma 19) must be known not to promote the popped operand variable, so
that Lemma 30 can be invoked to commute the `.equ`-context body
reduction past the eventual β substitution.
-/

namespace Pss
namespace DeBruijn

/-- **No-promotion-of-x side condition** on an `MEqRed` derivation
(paper Lemma 2 "Moreover" clause, p. 9:9). Tracks: no Me-Pro constructor
in the derivation tree has its source `bvar i` equal to `bvar x` at its
level of nesting.

Under binders, `x` shifts up by 1, since the new binder occupies slot 0
in the body context. -/
def MEqRed.NoPromotionOf : ∀ {Γ : Ctx} {s : Stack} {u v : Term},
    Nat → MEqRed Γ s u v → Prop
  | _, _, _, _, x, .pro (i := i) _ _ inner =>
      -- Promotion of slot i. Forbidden iff i = x.
      i ≠ x ∧ NoPromotionOf x inner
  | _, _, _, _, x, .bet _ body arg =>
      -- Body lives under a new `.sub` binder; `x` shifts to `x + 1`.
      NoPromotionOf (x + 1) body ∧ NoPromotionOf x arg
  | _, _, _, _, _, .top _ => True
  | _, _, _, _, x, .app op arg =>
      NoPromotionOf x op ∧ NoPromotionOf x arg
  | _, _, _, _, _, .var _ _ => True
  | _, _, _, _, x, .fun_ tBound body =>
      -- Body lives under a new `.sub` binder; `x` shifts to `x + 1`.
      NoPromotionOf x tBound ∧ NoPromotionOf (x + 1) body
  | _, _, _, _, _, .tAp _ _ => True
  | _, _, _, _, x, .fOp tBound _ body =>
      -- Body lives under a new `.equ` binder; `x` shifts to `x + 1`.
      NoPromotionOf x tBound ∧ NoPromotionOf (x + 1) body

/-! ## Equivalence-lookup transport under `.equ → .sub` slot swap

Both prevalidity and `equBinds` transport across an `.equ → .sub` slot
swap, provided the source `equBinds` lookup targets a slot DIFFERENT
from the swapped slot. The swapped slot's lookup in the destination
`.sub` form fails (returns `none`), so requiring `i ≠ cutoff` matches
exactly the de Bruijn analog of the paper's "no promotion of x" side
condition. -/

/-- Replacing a `.equ` entry at any context index preserves equivalence
lookups AT INDICES DIFFERENT FROM THE REPLACED SLOT when swapped to a
`.sub` entry. The replaced slot itself moves from "equivalence lookup
returns the bound" (in `.equ` source) to "lookup returns none" (in
`.sub` destination), so a lookup at `cutoff` cannot be transported. -/
theorem Ctx.equBinds_replaceAt_equ_to_sub_of_ne {Γ : Ctx} {cutoff i : Nat}
    {old new α : Term} (hne : i ≠ cutoff) :
    Ctx.equBinds (Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ) i α →
    Ctx.equBinds (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) i α := by
  induction Γ generalizing cutoff i α with
  | nil =>
      cases i <;> simp [Ctx.equBinds, Ctx.replaceAt]
  | cons head Γ ih =>
      cases cutoff with
      | zero =>
          cases i with
          | zero =>
              exact absurd rfl hne
          | succ i =>
              intro h
              simp [Ctx.equBinds, Ctx.replaceAt] at h ⊢
              exact h
      | succ cutoff =>
          cases i with
          | zero =>
              intro h
              cases head with
              | mk bound kind =>
                  cases kind
                  · simp [Ctx.equBinds, Ctx.replaceAt] at h ⊢
                  · simp [Ctx.equBinds, Ctx.replaceAt] at h ⊢
                    exact h
          | succ i =>
              intro h
              have hne' : i ≠ cutoff := fun h => hne (by omega)
              simp [Ctx.equBinds, Ctx.replaceAt] at h ⊢
              cases hlook : Ctx.lookupEqu
                  (Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ) i with
              | none =>
                  simp [hlook] at h
              | some a =>
                  simp [hlook] at h
                  subst h
                  have htail : Ctx.equBinds
                      (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) i a :=
                    ih (cutoff := cutoff) (i := i) (α := a) hne'
                      (by simpa [Ctx.equBinds] using hlook)
                  exact ⟨a, by simpa [Ctx.equBinds] using htail, rfl⟩

/-- Switch a `.equ` slot to a `.sub` slot at the same context index while
preserving extended-context prevalidity. The new bound is taken to be scoped
in the slot's tail; context depth is unchanged so all preserved heads and
stack operands remain scoped. -/
noncomputable def PrevalidExt.replaceAt_equ_to_sub_same {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new : Term}
    (hpv : PrevalidExt (Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ) s)
    (hcut : cutoff < Γ.depth)
    (hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
      { bound := new, kind := .sub }) :
    PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s := by
  have hpvDouble :
      PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub }
        (Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ)) s :=
    PrevalidExt.replaceAt hpv (by simpa [Ctx.depth_replaceAt] using hcut)
      (newEntry := { bound := new, kind := .sub })
      (by simpa [CtxEntry.ScopedIn, Ctx.drop_succ_replaceAt_self] using hnew)
  simpa using hpvDouble

/-- Head-form specialization of `PrevalidExt.replaceAt_equ_to_sub_same`:
swap the innermost `.equ` head for a `.sub` head with a different (scoped)
bound. -/
noncomputable def PrevalidExt.equ_to_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    PrevalidExt ({ bound := new, kind := .sub } :: Γ) s := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .equ } :: Γ) := by
    simp [Ctx.depth]
  have hnewEntry :
      CtxEntry.ScopedIn (List.drop 1 ({ bound := old, kind := .equ } :: Γ))
        { bound := new, kind := .sub } := by
    simpa [CtxEntry.ScopedIn] using hnew
  simpa [Ctx.replaceAt] using
    (PrevalidExt.replaceAt_equ_to_sub_same
      (Γ := { bound := old, kind := .equ } :: Γ) (cutoff := 0)
      (old := old) (new := new) hpv hcut hnewEntry)

/-! ## The guarded `.equ → .sub` head bridge (NoPromotionOf version)

The unguarded `.equ → .sub` head bridge is unsound in general (a
`Me-Pro` at slot 0 in an `.equ`-head context cannot be transferred to a
`.sub`-head context, since the latter has no equ-binding at slot 0). But
**if the source derivation has `NoPromotionOf 0`**, the bridge becomes
sound: by hypothesis, no `Me-Pro` at slot 0 occurs in the derivation,
so all other constructors transfer mechanically. The new head's bound
just needs to be scoped in the tail context. -/

/-- Kind-narrowing transport across an `.equ → .sub` slot swap, guarded
by the `NoPromotionOf cutoff` side condition. The forbidden index in the
source derivation is exactly the swapped slot, since a `Me-Pro` lookup
at that slot in the destination context fails (no equ-binding at a
`.sub` slot). -/
noncomputable def MEqRed.replaceAt_equ_to_sub_aux {Γold : Ctx} {s : Stack}
    {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v) :
    ∀ {Γ : Ctx} {cutoff : Nat},
      Γold = Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ →
      cutoff < Ctx.depth Γ →
      Term.Scoped (List.length (List.drop (cutoff + 1) Γ)) new →
      h.NoPromotionOf cutoff →
      MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v := by
  induction h with
  | @pro _ _ i α α' hpv hb hα ih =>
      intro Γ cutoff hEq hcut hnew hnp
      cases hEq
      -- hnp : i ≠ cutoff ∧ NoPromotionOf cutoff hα.
      have hne : i ≠ cutoff := hnp.1
      have hαnp := hnp.2
      have hpvNew :=
        PrevalidExt.replaceAt_equ_to_sub_same (old := old) (new := new)
          hpv hcut
          (by
            unfold CtxEntry.ScopedIn
            simpa using hnew)
      exact MEqRed.pro hpvNew
        (Ctx.equBinds_replaceAt_equ_to_sub_of_ne hne hb)
        (ih rfl hcut hnew hαnp)
  | bet ht hBody hArg ihBody ihArg =>
      intro Γ cutoff hEq hcut hnew hnp
      cases hEq
      have hBodyNp := hnp.1
      have hArgNp := hnp.2
      have ihBody' :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
          hBodyNp
      refine MEqRed.bet (by simpa [Ctx.depth_replaceAt] using ht) ?_
        (ihArg rfl hcut hnew hArgNp)
      simpa [Ctx.replaceAt] using ihBody'
  | top hpv =>
      intro Γ cutoff hEq hcut hnew _hnp
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_equ_to_sub_same (old := old) (new := new)
          hpv hcut
          (by
            unfold CtxEntry.ScopedIn
            simpa using hnew)
      exact MEqRed.top hpvNew
  | app hOp hArg ihOp ihArg =>
      intro Γ cutoff hEq hcut hnew hnp
      cases hEq
      exact MEqRed.app (ihOp rfl hcut hnew hnp.1) (ihArg rfl hcut hnew hnp.2)
  | var hpv hi =>
      intro Γ cutoff hEq hcut hnew _hnp
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_equ_to_sub_same (old := old) (new := new)
          hpv hcut
          (by
            unfold CtxEntry.ScopedIn
            simpa using hnew)
      exact MEqRed.var hpvNew (by simpa [Ctx.depth_replaceAt] using hi)
  | fun_ hBound hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hnew hnp
      cases hEq
      have hBoundNp := hnp.1
      have hBodyNp := hnp.2
      have ihBody' :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
          hBodyNp
      refine MEqRed.fun_ (ihBound rfl hcut hnew hBoundNp) ?_
      simpa [Ctx.replaceAt] using ihBody'
  | tAp hpv hu =>
      intro Γ cutoff hEq hcut hnew _hnp
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_equ_to_sub_same (old := old) (new := new)
          hpv hcut
          (by
            unfold CtxEntry.ScopedIn
            simpa using hnew)
      exact MEqRed.tAp hpvNew (by simpa [Ctx.depth_replaceAt] using hu)
  | fOp hBound hα hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hnew hnp
      cases hEq
      have hBoundNp := hnp.1
      have hBodyNp := hnp.2
      have ihBody' :=
        ihBody (Γ := { bound := _, kind := .equ } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
          hBodyNp
      refine MEqRed.fOp (ihBound rfl hcut hnew hBoundNp)
        (by simpa [Ctx.depth_replaceAt] using hα) ?_
      simpa [Ctx.replaceAt] using ihBody'

/-- Kind-narrowing transport across an `.equ → .sub` slot swap, guarded
by `NoPromotionOf cutoff`. -/
noncomputable def MEqRed.replaceAt_equ_to_sub {Γ : Ctx} {s : Stack}
    {u v : Term} {cutoff : Nat} {old new : Term}
    (h : MEqRed (Ctx.replaceAt cutoff { bound := old, kind := .equ } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hnew : Term.Scoped (List.length (List.drop (cutoff + 1) Γ)) new)
    (hnp : h.NoPromotionOf cutoff) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  h.replaceAt_equ_to_sub_aux rfl hcut hnew hnp

/-- Head specialization: a `MEqRed` derivation valid at a `.equ`-head
context, with no Me-Pro promotion of slot 0, can be re-cast at a
`.sub`-head context with a different (scoped) bound. -/
noncomputable def MEqRed.equ_to_sub_head_replace_NoPromotion
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .equ } :: Γ) s u v)
    (hnp : h.NoPromotionOf 0)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s u v := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .equ } :: Γ) := by
    simp [Ctx.depth]
  have hnew' : Term.Scoped
      (List.length (List.drop 1 ({ bound := old, kind := .equ } :: Γ))) new := by
    simpa using hnew
  -- Apply the generic replaceAt_equ_to_sub_aux at cutoff = 0. Since
  -- `replaceAt 0 newEntry (head :: Γ) = newEntry :: Γ` by definition,
  -- the resulting context is `{new,.sub} :: Γ`.
  have hres : MEqRed (Ctx.replaceAt 0 { bound := new, kind := .sub }
      ({ bound := old, kind := .equ } :: Γ)) s u v :=
    h.replaceAt_equ_to_sub_aux (Γ := { bound := old, kind := .equ } :: Γ)
      (cutoff := 0) rfl hcut hnew' hnp
  simpa [Ctx.replaceAt] using hres

namespace Paper

/-- The existential `MEqRedJ`-with-side-condition form: a derivation
exists and avoids promotion of `x`. Useful in the diamond conclusion
since the conclusion ships an existential over derivations, and we want
the existential to also witness the side condition. -/
def MEqRedJWithNoPromotionOf
    (Γ : Ctx) (s : Stack) (u v : Term) (x : Nat) : Prop :=
  ∃ (h : MEqRed Γ s u v), h.NoPromotionOf x

/-- A derivation that has no promotion of `x` admits the `MEqRedJ`
wrapper. -/
theorem MEqRed.NoPromotionOf.toMEqRedJ
    {Γ : Ctx} {s : Stack} {u v : Term} {x : Nat}
    {h : MEqRed Γ s u v} (_hNP : h.NoPromotionOf x) :
    MEqRedJ Γ s u v :=
  ⟨h⟩

end Paper
end DeBruijn
end Pss
