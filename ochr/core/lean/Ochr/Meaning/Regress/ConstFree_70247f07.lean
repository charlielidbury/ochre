import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib
/-!
# `evalCore_step_stmt` was false at a free `K.C.global` (archived record; NOT built:
# kernel-checked against spine 70247f07, axioms propext, Classical.choice, Quot.sound)

`evalCore_const_free`: for every run context whose `K.C.global "one"` is `(err, plain err)`, at
every assignment and future, `evalCore_step_stmt K ρ φ 10` fails. The checker evaluates the
global `one : Nat := S(Z)` to `S(Z)` (the kernel runs `evalCore`); the reference run of
`.const "one"` is `K.C.global "one"`, which no hypothesis of the statement tied to Σ.

A fault of the statements (docs/31 D20, item 6): every statement quantified over a run context
and tied only its Δ to the state. Fixed after 70247f07: `CtxOk K ρ st` (the state's declarations,
a data model covering them, Δ, label-free globals, and `GlobalsOk`: `K.C.global` is Σ) is a
hypothesis of every statement. `Regress/ConstFree_flipped.lean` (built) is the positive form.
-/
open Ochr Ochr.Meaning Ochr.Meaning.Steps

namespace ConstCE

/-- `def one : Nat := S(Z)`, as a global of Σ. -/
def gOne : GDef := { name := "one", ty := .tNat, fn? := none, val := .succ .zero }
/-- The empty state after it. -/
def stG : MState := { globals := [gOne] }

/-- The checker evaluates `one` to `S(Z) : Nat` (the kernel runs `evalCore`). -/
theorem runs_const : ∃ st' left log, runMachine (Ochr.evalCore 10 true (.const "one") none) stG 10
    = (.ok (.succ .zero, some .tNat) st', left, log) := ⟨_, _, _, rfl⟩

theorem allPos_stG : allPos stG.env = [] := by
  rw [allPos_eq]; rfl

theorem noBind (f i : Nat) : (stG.env[f]?.bind fun fr => fr.binds[i]?) = none := by
  cases f with
  | zero => rfl
  | succ f => rfl

theorem not_refd (σ : Nat) : ¬ stG.Refd σ := by
  intro h
  induction h with
  | val v hv _ => simp [Env.values, allPos_stG] at hv
  | ty f i b T hb _ _ => rw [noBind] at hb; cases hb
  | lazyTy f i b P ws j hb _ _ => rw [noBind] at hb; cases hb
  | goal G hG _ => simp [stG] at hG
  | neutral n σ' hn _ => simp [stG] at hn
  | eta σ' v he _ => simp [stG] at he
  | dep σ' T _ _ _ ih => exact ih

variable (K : RunCtx)

theorem good_stG (ρ : Assignment) : Good K.dm K.M K.Γ ρ stG := by
  have hv : Env.values stG.env = [] := by simp [Env.values, allPos_stG]
  have hpos : ∀ p T, MState.posTyM K.dm K.M K.Γ ρ stG p ≠ some T := by
    intro p T h
    cases p with
    | bind f i => simp only [MState.posTyM, noBind] at h; cases h
    | temp f i => cases h
  refine ⟨⟨fun σ h _ => absurd h (not_refd σ), fun n σ h => absurd h (by simp [stG]),
      fun σ v h => absurd h (by simp [stG])⟩, ⟨fun φ _ p T h => absurd h (hpos p T),
      fun σ h _ => absurd h (not_refd σ), fun G h => by simp [MState.goalM, stG] at h⟩, ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rw [allPos_stG] at hp; cases hp
  · intro p hp; rw [allPos_stG] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro l; rw [hv]; simp
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by rw [allPos_stG] at hp; cases hp⟩⟩
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro T hT; simp [stG] at hT
  · intro G hG; simp [stG] at hG
  · simp [stG]
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro p T h; exact absurd h (hpos p T)
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro f i b hb; rw [noBind] at hb; cases hb
  · intro T hT; simp [stG] at hT
  · intro G hG; simp [stG] at hG
  · intro p hp; rw [allPos_stG] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv

/-- **`evalCore_step_stmt` is false at a free `K.C.global`.** The checker evaluates the global
`one` to `S(Z)`; the reference run of `.const "one"` is `K.C.global "one"`, which no hypothesis of
the statement ties to Σ. -/
theorem evalCore_const_free (ρ : Assignment) (φ : Future) (hC : K.C.global "one" = (.err, .plain .err)) :
    ¬ evalCore_step_stmt K ρ φ 10 := by
  intro h
  obtain ⟨st', left, log, hrun⟩ := runs_const
  obtain ⟨ρ', -, r, s', hr, hle, -⟩ := h stG st' true (.const "one") none (.succ .zero) (some .tNat)
    (good_stG K ρ) (fun σ hσ => absurd hσ (by simp [stG])) ⟨left, log, hrun⟩
  rw [run] at hr
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hr)
  rw [hC] at hle
  simp [meanV, Sem.succ, Sem.asNat, Sem.as] at hle
  cases hle
end ConstCE
