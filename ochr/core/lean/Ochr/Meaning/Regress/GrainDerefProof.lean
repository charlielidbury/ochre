import Ochr.Meaning.Steps.JoinNoop
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# The join "derefs no proof": false as stated (the slice, 2026-11-20)

`JoinNoop.grain_deref_not_proof` says: a place `q` at the join's grain whose declared reading is not
a copy has no prefix `p` holding `⋆` followed by a `*`. Its hypotheses do not say that `q` is one
the join drops (an arm, typed, moved it), and nothing else excludes `q = *h` for a variable `h`
holding a proof: a `*` step needs nothing at the grain (`StepOk .deref` is `True`), and `*h` of a
place read `prop` is read `other` (`Decide.placeDecl`'s `.deref` case), which is no copy. So the
statement derives `False` from `Good`, `CtxOk` and the relation at any state with a proof variable
in scope: `S` below, `h ↦ ⋆` declared a proposition. The checker's readings at `S` are computed by
the kernel (`placeDecl` of `*h` is `other`, `declCopy` of `other` is `false`).

With the reference's drop of the slice (`Run.dropAt`: no test of the meaning at the place), the
drop step itself is false at `q = *h`: the checker re-roots to `h` and does nothing, the reference
writes `moved` through the `*` (a `*` is the identity on meanings). The checker reads a `*` only
of a borrow (`stepV`), which (WF1) puts only at a root.

The state is reached by an accepted program (`def DP1 (h : Eq(Nat, Z, Z)) : Unit := (let k = Z;
match k { Z => (), S m => (let a = *h; ()) })`: the arm `S` is never run, so never checked, and
`jdMoves` reads its move of `*h`). PROPOSED (the slice, for main and the lead): the grain asks the
`*` step's borrow type again (`Steps.StepOk`), with the checker's `jdGrain` keeping a `*` only
through a place declared a borrow. The leaf is then proved (`JoinNoop.grain_deref_not_proof`, from
(C⋆)). The counterexample below is to the leaf at the grain as it stood (`GrainOkOld`).
-/

namespace Ochr.Meaning.Regress.GrainDerefProof
open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Regress.GenNeutralContent (outVal outSt isOk runs_out)

/-- `h ↦ ⋆`, declared a proposition (`h : Eq(Nat, 0, 0)`). -/
def hB : Binding := { hint := ⟨"h"⟩, ty := some (.tEq .tNat .zero .zero), val := .proof, decl := .prop }
def S : MState := { env := #[{ binds := #[hB] }] }

/-- The grain's step as it stood: a `*` step needed nothing. -/
def StepOkOld (Γ : List IndDecl) (r : DeclInfo) : Step → Prop
  | .proj _ | .field _ => ∃ n args d, r = .ind n args ∧ Γ.find? (·.name == n) = some d ∧ d.ctors.length = 1
  | .deref => True

/-- The grain as it stood. -/
def GrainOkOld (D : Decisions) (Γ : List IndDecl) (sc : List DeclInfo) (q : Place) : Prop :=
  ∀ (p : Place) (x : Step) (rest : List Step), p.steps.1 = q.steps.1 → q.steps.2 = p.steps.2 ++ x :: rest →
    StepOkOld Γ (D.placeDecl sc p) x

/-- `grain_deref_not_proof`'s statement, at a context, at the grain as it stood. -/
def GrainDerefStmt (K : RunCtx) (ρ : Assignment) (φ : Future) : Prop :=
  ∀ (st : MState) (s : SState) (π : Nat → Nat) (q p : Place),
    Good K.dm K.M K.Γ ρ st → CtxOk K ρ st → Rel K ρ φ π st s →
    GrainOkOld K.D K.Γ (scopeOf s) q → K.D.copy (K.D.placeDecl (scopeOf s) q) = false →
    p.steps.1 = q.steps.1 → p.steps.2 ++ [.deref] <+: q.steps.2 →
    ckContent st.env p = some .proof → False

abbrev pd : M DeclInfo := withLive true (Ochr.placeDecl 10 [] (.deref (.var 0)))

theorem pd_ok : isOk pd (scopeState S (DecideScope.topReadings S)) 100 = true := by decide +kernel
theorem pd_val : outVal pd (scopeState S (DecideScope.topReadings S)) 100 = .other := by
  have h : (match outVal pd (scopeState S (DecideScope.topReadings S)) 100 with
      | .other => true | _ => false) = true := by decide +kernel
  split at h
  · assumption
  · cases h
theorem cp_ok : isOk (Ochr.declCopy 10 .other) S 100 = true := by decide +kernel
theorem cp_val : outVal (Ochr.declCopy 10 .other) S 100 = false := by decide +kernel

/-- **The statement as it stands derives `False` at `S`**, under every context and relation that
admit `S`. -/
theorem stmt_false (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (s : SState)
    (hg : Good K.dm K.M K.Γ ρ S) (hctx : CtxOk K ρ S) (hs : Rel K ρ φ π S s) :
    ¬ GrainDerefStmt K ρ φ := by
  intro h
  have hsc := rel_scopeOf K ρ φ hs
  have hpd : K.D.placeDecl (scopeOf s) (.deref (.var 0)) = .other := by
    rw [hsc]
    have := hctx.dec.placeDecl 10 (DecideScope.topReadings S) (.deref (.var 0)) _ 100 _
      (runs_out pd _ 100 pd_ok)
    rw [this, pd_val]
  have hcp : K.D.copy .other = false := by
    have := hctx.dec.copy 10 .other _ 100 _ (runs_out (Ochr.declCopy 10 .other) S 100 cp_ok)
    rw [this, cp_val]
  refine h S s π (.deref (.var 0)) (.var 0) hg hctx hs ?_ (by rw [hpd]; exact hcp) rfl ⟨[], by simp [Place.steps]⟩ ?_
  · intro p x rest h1 h2
    have h2' : [Step.deref] = p.steps.2 ++ x :: rest := h2
    cases hp : p.steps.2 with
    | nil =>
      rw [hp] at h2'
      simp only [List.nil_append, List.cons.injEq] at h2'
      rw [← h2'.1]; trivial
    | cons y ys =>
      rw [hp] at h2'
      simp at h2'
  · rfl

end Ochr.Meaning.Regress.GrainDerefProof
