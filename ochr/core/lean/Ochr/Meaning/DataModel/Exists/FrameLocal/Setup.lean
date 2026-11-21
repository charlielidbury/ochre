import Ochr.Meaning.DataModel.Exists.FrameLocal.Join
import Ochr.Meaning.DataModel.Exists.FrameLocal.Vars

/-!
# Frame locality, part 4: the statement's hypotheses and how they pass to subterms (exists3)

* `DecLocal`: the decisions name only places rooted at the term's free variables (or at places
  already moved, which a whole binding has none of); an invalidated place shares the written one's
  root. Without it frame locality is false (docs/34 §18.5, count 3).
* `VarsAvoid Q s t`: no free variable of `t` names a position of `Q` in `s`.
* `Adm K Q β β' s`: `Twin` at `s` (its own layout), the two binding families agree on the declared
  readings, and both are `Good` (constant, whole, admitted by the strict whole-state test).
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

/-- **The decisions are local**: every place they give for a term is rooted at one of its free
variables or is among the places already moved. -/
structure DecLocal (D : Decisions) : Prop where
  inv : ∀ sc p q, q ∈ D.invalidated sc p → q.root = p.root
  join : ∀ sc entry t q, q ∈ D.joinMoves sc entry t → q ∈ entry ∨ q.root ∈ t.freeVars
  rep : ∀ sc t q, q ∈ D.rePointed sc t → q.root ∈ t.freeVars
  caps : ∀ sc entry t qk, qk ∈ (D.blockCaps sc entry t).2 → qk.1 ∈ entry ∨ qk.1.root ∈ t.freeVars

/-- No free variable of `t` names a position of `Q`. -/
def VarsAvoid (Q : Pos → Prop) (s : SState) (t : Term) : Prop :=
  ∀ v ∈ t.freeVars, ∀ pos, s.varPos v = some pos → ¬ Q pos

/-- The hypotheses of frame locality at a state. -/
structure Adm (K : RunCtx) (Q : Pos → Prop) (β β' : Pos → SBinding) (s : SState) : Prop where
  twin : Twin Q β β' s s
  decl : ∀ p, Q p → (β' p).decl = (β p).decl
  good : ∀ p, Q p → Good K (β p)
  good' : ∀ p, Q p → Good K (β' p)

section
variable {K : RunCtx} {Q : Pos → Prop} {β β' : Pos → SBinding}

theorem Adm.self {s : SState} (h : Adm K Q β β' s) : Adm K Q β β s :=
  ⟨⟨h.twin.pre, h.twin.pre, h.twin.fix, h.twin.env⟩, fun _ _ => rfl, h.good, h.good⟩

theorem Adm.next {s s₁ : SState} (h : Adm K Q β β' s) (he : EnvLe s s₁) (hfix : qset Q β s₁ = s₁) :
    Adm K Q β β' s₁ := by
  have hsh : ∀ p, Q p → s₁.shape p = none := fun p hp => by rw [← hfix]; simp [hp]
  exact ⟨⟨⟨h.twin.pre.temp, fun p hp => he.mem (h.twin.pre.pos p hp), hsh, h.twin.pre.const⟩,
    ⟨h.twin.pre.temp, fun p hp => he.mem (h.twin.pre.pos p hp), hsh, h.twin.pre'.const⟩, hfix, EnvLe.refl _⟩,
    h.decl, h.good, h.good'⟩

/-- The run's invariant, read off the equation at `β' := β`. -/
theorem fix_of_comm {α : Type 3} {x : SM α} {s s₁ : SState} {a : α} (hc : Comm Q β x s) (hfix : qset Q β s = s)
    (hx : x s = some (a, s₁)) : qset Q β s₁ = s₁ := by
  unfold Comm at hc
  rw [hfix, hx] at hc
  simp only [qmap, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
  exact hc.2.symm

theorem VarsAvoid.of_envLe {s s₁ : SState} {t : Term} (h : VarsAvoid Q s t) (he : EnvLe s s₁) : VarsAvoid Q s₁ t := by
  intro v hv pos hp; rw [varPos_of_envLe he] at hp; exact h v hv pos hp

theorem VarsAvoid.sub {s : SState} {t u : Term} (h : VarsAvoid Q s t) (hsub : ∀ x ∈ u.placeOccs 0, x ∈ t.placeOccs 0) :
    VarsAvoid Q s u := by
  intro v hv pos hp
  rcases freeVars_sub (n := 0) hsub v hv with h0 | h0
  · omega
  · exact h _ (by simpa using h0) pos hp

theorem rAvoid_of_vars {s : SState} {t : Term} (h : VarsAvoid Q s t) {p : Place} (hp : p.root ∈ t.freeVars) :
    RAvoid Q s p := rAvoid_of_root fun pos hv => h _ hp pos hv

theorem root_mem_place (p : Place) : p.root ∈ (Term.place p).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .read, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

theorem root_mem_borrow (p : Place) : p.root ∈ (Term.borrow p).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .borrow, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

theorem Adm.scope {s : SState} (h : Adm K Q β β' s) : scopeOf (qset Q β' s) = scopeOf s := scopeOf_qset h.twin.fix h.decl

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
