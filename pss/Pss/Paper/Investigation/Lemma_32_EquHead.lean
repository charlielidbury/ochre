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

/-! ## Shift-arithmetic helper -/

/-- Generic identity: shifting by 1 at cutoff `c + n` on a term shifted
by `n` from cutoff `c` equals shifting by `n + 1` from cutoff `c`. This
holds because all free indices ≥ c of the inner shifted term are bumped
to ≥ c + n, hence ≥ c + n. -/
theorem Term.shiftBy_succ_at_cutoff_gen (c n : Nat) (t : Term) :
    Term.shiftBy (c + n) 1 (Term.shiftBy c n t) = Term.shiftBy c (n + 1) t := by
  induction t generalizing c n with
  | bvar i =>
      by_cases hci : c ≤ i
      · -- i ≥ c: shiftBy c n (bvar i) = bvar (i+n); since c+n ≤ i+n, shiftBy bumps.
        have h1 : c + n ≤ i + n := Nat.add_le_add_right hci n
        simp [Term.shiftBy, hci, h1, Nat.add_assoc]
      · -- i < c: shiftBy c n (bvar i) = bvar i; c + n > i so shiftBy doesn't bump.
        have h1 : ¬ c + n ≤ i := fun h => hci (by omega)
        simp [Term.shiftBy, hci, h1]
  | top =>
      simp [Term.shiftBy]
  | abs bound body ih_bound ih_body =>
      simp only [Term.shiftBy_abs]
      refine congrArg₂ Term.abs (ih_bound c n) ?_
      have := ih_body (c + 1) n
      -- this: shiftBy (c+1+n) 1 (shiftBy (c+1) n body) = shiftBy (c+1) (n+1) body
      -- goal: shiftBy (c+n+1) 1 (shiftBy (c+1) n body) = shiftBy (c+1) (n+1) body
      -- These differ by (c+1+n) vs (c+n+1) which are equal.
      have hEq : c + 1 + n = c + n + 1 := by omega
      rw [hEq] at this
      exact this
  | app fn arg ih_fn ih_arg =>
      simp [Term.shiftBy, ih_fn c n, ih_arg c n]

/-- Specialization at cutoff 0: `shiftBy n 1 (shiftBy 0 n t) = shiftBy 0
(n+1) t`. -/
theorem Term.shiftBy_succ_at_cutoff (n : Nat) (t : Term) :
    Term.shiftBy n 1 (Term.shiftBy 0 n t) = Term.shiftBy 0 (n + 1) t := by
  have h := Term.shiftBy_succ_at_cutoff_gen 0 n t
  simpa [Nat.zero_add] using h

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
β-instantiation prefix. Type-valued so it can be used in
noncomputable definitions of `MEqRed` derivations. -/
inductive Ctx.EquBindsBetaEquHeadCase
    (Γ : Ctx) (arg α : Term) (heads : Ctx) (i : Nat) : Type where
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

/-! ## `Me-Pro` helper for the `.equ`-head form -/

/-- `.equ`-head `Me-Pro` transport. Handles both subcases:
* **at-slot** (`i = heads.length`): the source `bvar heads.length` looks
  up the substituted slot, returning `shift_by (heads.length+1) arg`.
  After substitution, the source becomes `shift_by heads.length arg`,
  and the inner derivation's transported form yields exactly the
  desired output. (The inner premise's `α` equals `shift_by
  (heads.length+1) arg`, so after substitution `instantiate heads.length
  (shift_by heads.length arg) α = shift_by heads.length arg`.)
* **preserved** (`i ≠ heads.length`): standard `Me-Pro` reconstruction at
  the post-substitution context using the transported lookup. -/
private noncomputable def equ_head_pro_helper
    {Γ : Ctx} {arg arg' α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .equ } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .equ } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α') := by
  have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsEquHead
    (n := heads.length) rfl hArgScoped hpv
  have hcase := Ctx.equBinds_beta_equHead_classify (Γ := Γ) (arg := arg)
      (heads := heads) hb
  cases hcase with
  | argSlot hi_eq hα_eq =>
      -- At-slot: i = heads.length, α = shift_by (heads.length+1) arg.
      subst hi_eq
      subst hα_eq
      -- Source `bvar heads.length` substituted by `shift_by heads.length arg` at heads.length yields `shift_by heads.length arg`.
      have hSrcSubst :
          Term.instantiate heads.length (Term.shiftBy 0 heads.length arg)
              (.bvar heads.length) = Term.shiftBy 0 heads.length arg := by
        simp [Term.instantiate]
      rw [hSrcSubst]
      -- α = shift_by (heads.length+1) arg, so instantiate heads.length (shift_by heads.length arg) α = shift_by heads.length arg.
      -- (Because shift_by (heads.length+1) arg only mentions indices ≥ heads.length+1, and instantiate at heads.length decrements them.)
      -- We have hα : MEqRed ... (instantiate heads.length (shift_by heads.length arg) (shift_by (heads.length+1) arg)) (instantiate heads.length (shift_by heads.length arg') α').
      -- Need: MEqRed ... (shift_by heads.length arg) (instantiate heads.length (shift_by heads.length arg') α').
      have hSimp :
          Term.instantiate heads.length (Term.shiftBy 0 heads.length arg)
            (Term.shiftBy 0 (heads.length + 1) arg) =
            Term.shiftBy 0 heads.length arg := by
        rw [← Term.shiftBy_succ_at_cutoff heads.length arg]
        exact Term.instantiate_shiftBy_one_id heads.length
          (Term.shiftBy 0 heads.length arg) (Term.shiftBy 0 heads.length arg)
      rw [hSimp] at hα
      exact hα
  | preserved j hvar hbind =>
      -- Preserved: bvar i → bvar j, lookup gives some α-related target.
      rw [hvar]
      exact MEqRed.pro hpvTarget hbind hα

/-! ## The via-wall induction at `.equ`-head -/

/-- **Reduction of the `.equ`-head Lemma 32 goal to the wall.** Given
the existing `MEqRedStackExtensionWall`, the `.equ`-head Lemma 32 follows
by induction on the body derivation. -/
noncomputable def Lemma_32_EquHead_via_wall
    (hWall : MEqRedStackExtensionWall) :
    ∀ n {Γ : Ctx} {arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
      heads.length = n →
        Term.Scoped Γ.depth arg →
          Term.Scoped Γ.depth arg' →
            MEqRed Γ [] arg arg' →
              MEqRed (heads ++ { bound := arg, kind := .equ } :: Γ) s lhs rhs →
                MEqRed
                  (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
                  (Stack.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg) s)
                  (Term.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg) lhs)
                  (Term.instantiate heads.length
                    (Term.shiftBy 0 heads.length arg') rhs) := by
  intro n Γ arg arg' lhs rhs heads s hlen hArgScoped hArg'Scoped
    hArgArg' hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := arg, kind := .equ } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      exact equ_head_pro_helper (Γ := Γ) (arg := arg) (arg' := arg')
        (heads := heads) hArgScoped hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsEquHead
          (n := heads.length) rfl hArgScoped hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg' ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArg'IH := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hOp' hArg'IH
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsEquHead
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
            Ctx.depth (heads ++ { bound := arg, kind := .equ } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      by_cases hieq : i = heads.length
      · -- Me-Var at the substituted slot: source bvar heads.length → bvar heads.length.
        -- After substitution: source becomes shift_by heads.length arg, target becomes shift_by heads.length arg.
        -- BUT — wait, hi is `i < Γ.depth`. For our context, this requires Γ.depth = ...
        -- Actually, Me-Var requires i < Γ.depth where Γ = (heads ++ {arg,.equ}::Γ_outer).
        -- After substitution, the target becomes shift_by heads.length arg (same as source).
        -- BUT: the RHS substitution by arg' gives shift_by heads.length arg'.
        -- So we need: MEqRed Γ_target (s_target) (shift_by heads.length arg) (shift_by heads.length arg').
        -- This is the wall: from `MEqRed Γ [] arg arg'`, lift to the post-substitution context.
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
      · -- Non-substituted-slot subcase: LHS and RHS substitutions agree on
        -- bvars away from heads.length, close by reflexivity.
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
        BetaInstantiationPreservesPrevalidExtUnderHeadsEquHead
          (n := heads.length) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .equ } :: Γ) =
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
            Ctx.depth (heads ++ { bound := arg, kind := .equ } :: Γ) =
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
            Ctx.depth (heads ++ { bound := arg, kind := .equ } :: Γ) =
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

/-! ## Closed-stack surface -/

/-- **Paper-faithful `.equ`-head Lemma 32, closed-stack form.**

Given a body derivation at `.equ`-head with bound = LHS substitution
arg, and an arg reduction `arg → arg'`, produce the substituted
reduction at the tail context.

This is the form invoked by paper Lemma 2's Me-App × Me-Bet (and
symmetric Me-Bet × Me-App) cells. -/
noncomputable def Lemma_32_EquHead_proved_closed
    {Γ : Ctx} {arg arg' lhs rhs : Term} {s : Stack}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({ bound := arg, kind := .equ } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg lhs)
      (Term.instantiate 0 arg' rhs) := by
  have h' := Lemma_32_EquHead_via_wall MEqRedStackExtensionWall_proved 0
    (heads := []) rfl hArgScoped hArg'Scoped hArgArg' h
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

end Investigation
end Paper
end DeBruijn
end Pss
