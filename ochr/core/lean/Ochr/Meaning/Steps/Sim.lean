import Ochr.Meaning.Steps.Statements

/-!
# The relation that lets steps compose (docs/31, D20 item 1; second lead, 2026-11-13)

Every step statement of `Statements.lean` runs the reference from `SM' K ρ st`, the checker's own
state read as a reference state, and concludes `Below (MState.mean … st') s'.toMean`. Two faults,
both of the statements:

1. **It does not compose.** After a first step the reference is in its own state `s'`, not in
   `SM' st'`, and the second step's statement says nothing about a run from `s'`.
2. **It is false wherever a borrow was held** (`Regress/StaleTemp.lean`, kernel-checked on the
   reference's side, the checker's by `#guard`): `Below` reads every position, the reference
   parks borrows in temporaries the checker does not have, and `err ⊑ ⊥` is false.

The repair chosen is the **simulation form**: a step is stated from ANY reference state `s`
related to the checker's state (`Rel`), and concludes `Rel` of the two states after. Then
sequencing is by construction (`sim_seq`), and no lemma "the run is monotone in the state" is
needed. That lemma was the alternative; it is false for the relation `Below` (two states can be
`Below`-related with a witness future that is not the one an [End] would fix: the lower reads
`5` where the upper's holder holds `7`, and a read gives `5` against `7`), and for an
ends-generated relation it needs the run to fail on a forgotten holder, which a write through
`*r` does not (`Sem.updAt` at a `deref` of `⊥`). In the simulation form the checker's own run is
a hypothesis, and the checker never uses a holder it has ended.

`Rel` has three parts, each forced by a counterexample (docs/31, D20 item 1):

* `skel`: the same frames and, in each, the same bindings with the same types and readings.
  `Below` relates meanings only; two states with the same meanings and different binding counts
  resolve `var 0` to different positions.
* `next`: the same label counter, so the two runs issue the same fresh labels (the shape is
  compared by label). This needs the audit's A15 fixed: the reference restores the counter after
  a private copy and the checker does not (D37).
* `early`: the checker's state is the reference's after some of its borrows ended early (`E`),
  compared at the SAME future (`SimEq`), with bindings position by position and a borrow in
  flight by its label. The futures range over those that agree with the run's off the labels
  live after the ends, which is D20 item 2's repair (a binding of an inert loan is the constant
  `φ ℓ` in the reference and `φ' ℓ` in the checker's state).

**Status.** The definitions and `eval_sim_stmt`, the simulation form of the central statement,
are here; `Rel.sim` (the relation implies the old order where the old order is true), `Sim.of_below`
and `sim_seq` are proved. NOT done: the 72 statements of `Statements.lean` still have the `Below`
form; migrating them is the next batch (each `Below (MState.mean … st') s'.toMean` conjunct becomes
`Rel`, each `SM' K ρ st` a universally quantified `s` with `Rel`).
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

/-- The checker's state `m'` at the SAME future as the reference state `s`: bindings position by
position (the two push and drop bindings in step), a binding's borrow at the same position, and a
borrow in flight (held by a temporary of the checker's state) held by SOME temporary of the same
frame of the reference, whose content is above it. Temporaries are otherwise not compared: the
reference parks a borrow in a temporary until it is bound and leaves the temporary behind, the
checker carries a value in flight in its monad (`Regress/StaleTemp.lean`).

`F` is the set of futures compared. -/
def SimEq (F : Future → Prop) (m' : Mean) (s : SState) : Prop :=
  (∀ φ, F φ → ∀ p, ¬ IsTemp p → m'.val φ p ⊑ s.valAt p φ) ∧
  (∀ p l, ¬ IsTemp p → m'.shape p = some l → s.shape p = some l) ∧
  (∀ f i l, m'.shape (.temp f i) = some l →
    ∃ j, s.shape (.temp f j) = some l ∧ ∀ φ, F φ → m'.val φ (.temp f i) ⊑ s.valAt (.temp f j) φ)

/-- The old order without its positional reading of temporaries: for every future of the lower
state, a future of the upper at which bindings are below position by position and a borrow in
flight is held, by label, with a content above. Implied by `Below` (`Sim.of_below`); true where
`Below` is false (`Regress/StaleTemp.lean`). -/
def Sim (m' : Mean) (s : SState) : Prop :=
  ∀ φ', ∃ φ,
    (∀ p, ¬ IsTemp p → m'.val φ' p ⊑ s.valAt p φ) ∧
    (∀ p l, ¬ IsTemp p → m'.shape p = some l → s.shape p = some l) ∧
    (∀ f i l, m'.shape (.temp f i) = some l →
      ∃ j, s.shape (.temp f j) = some l ∧ m'.val φ' (.temp f i) ⊑ s.valAt (.temp f j) φ)

theorem Sim.of_below {m' : Mean} {s : SState} (h : Below m' s.toMean) : Sim m' s := fun φ' => by
  obtain ⟨φ, hv, hs⟩ := h φ'
  exact ⟨φ, fun p _ => hv p, fun p l _ hl => hs p l hl, fun f i l hl => ⟨i, hs _ l hl, hv _⟩⟩

/-- `SimEq` at every future, then `Below`, is `Sim`. -/
theorem Sim.of_simEq_below {m' : Mean} {s₀ s : SState} (h : SimEq (fun _ => True) m' s₀)
    (hb : Below s₀.toMean s.toMean) : Sim m' s := fun φ' => by
  obtain ⟨φ, hv, hs⟩ := hb φ'
  refine ⟨φ, fun p hp => Sem.le_trans (h.1 φ' trivial p hp) (hv p), fun p l hp hl => hs p l (h.2.1 p l hp hl),
    fun f i l hl => ?_⟩
  obtain ⟨j, hj, hle⟩ := h.2.2 f i l hl
  exact ⟨j, hs _ l hj, Sem.le_trans (hle φ' trivial) (hv (.temp f j))⟩

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- What `run` reads of a binding besides its meaning: its type's meaning and data, and its
declared reading. (The label a type recorded when it was bound is read by no clause; the Π-shape
is: its agreement between a stored type read by `Value.tyS` and a type the run made is an open
lemma, so it is not part of the skeleton here.) -/
def bindSkel (b : SBinding) : TyM × Option (String × List Sem) × DeclInfo := (b.ty.m, b.ty.data, b.decl)

/-- **The reference state `s` simulates the checker's state `st`**, for a reference run at the
future `φ` (the module docstring). -/
structure Rel (st : MState) (s : SState) : Prop where
  /-- the same frames, each with the same bindings at the same types and readings -/
  skel : (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel)
  /-- the same label counter: the two runs issue the same fresh labels -/
  next : st.nextLoan = s.nextLoan
  /-- the checker's state is the reference's after the borrows of `E` ended early, at every future
  that agrees with the run's off the labels then live -/
  early : ∃ E : List Nat,
    SimEq (fun ψ => ∀ l, ¬ (E.foldl SState.endLabel s).Live l → ψ l = φ l)
      (MState.mean K.dm K.M K.Γ ρ st) (E.foldl SState.endLabel s)

/-- Steps stated in the simulation form compose: if the first runs from any reference state
related to `st` into one related to `st₁`, and the second from any related to `st₁` into one
related to `st₂`, their sequence runs from any related to `st` into one related to `st₂`. With
the `Below` form the second premise is available only at `SM' st₁`, and this fails. -/
theorem sim_seq {α β : Type 3} (x₁ : SM α) (x₂ : α → SM β) (st st₁ st₂ : MState)
    (h₁ : ∀ s, Rel K ρ φ st s → ∃ a s₁, x₁ s = some (a, s₁) ∧ Rel K ρ φ st₁ s₁)
    (h₂ : ∀ a s₁, Rel K ρ φ st₁ s₁ → ∃ b s₂, x₂ a s₁ = some (b, s₂) ∧ Rel K ρ φ st₂ s₂) :
    ∀ s, Rel K ρ φ st s → ∃ b s₂, (x₁ >>= x₂) s = some (b, s₂) ∧ Rel K ρ φ st₂ s₂ := by
  intro s hs
  obtain ⟨a, s₁, e₁, r₁⟩ := h₁ s hs
  obtain ⟨b, s₂, e₂, r₂⟩ := h₂ a s₁ r₁
  refine ⟨b, s₂, ?_, r₂⟩
  simp only [Bind.bind]
  rw [e₁]
  exact e₂

/-- **The induction step in the simulation form** (the form `eval_step_stmt` migrates to): for
every `Good` assignment `ρ` and every reference state `s` that simulates the checker's state,
the reference run of `t` from `s` does not fail, the checker's value is below its result, and the
state it reaches simulates the checker's, for an assignment `ρ'` extending `ρ`. -/
def eval_sim_stmt (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (h : Runs (Ochr.eval fuel typed t hint) st fuel (v, T?) st')
    (s : SState) (hs : Rel K ρ φ st s),
    ∃ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t s = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧
        (∀ T, T? = some T → (meanV K ρ' noFuture (.plain .err) T).asTy = r.2.m) ∧
        Rel K ρ' φ st' s' ∧ Good K.dm K.M K.Γ ρ' st'

end

end Ochr.Meaning.Steps
