import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

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

* `skel`: the same frames and, in each, the same bindings with the same types (meaning, Π-shape,
  data) and readings. `Below` relates meanings only; two states with the same meanings and
  different binding counts resolve `var 0` to different positions, and one whose bindings have
  lost their Π-shapes fails every call through a variable (docs/31 D22: the shape was first left
  out).
* `fresh`, with the renaming `π` of the checker's labels to the reference's: the two runs do
  NOT issue the same labels, and cannot be made to. The checker runs an erased term on a private
  copy and keeps the label counter (D37), so a proof that borrows consumes labels; the reference
  does not run a proof at all (the audit's A3), and its run could fail if it did. So shapes and
  futures are compared through `π`, and a step extends `π` at the labels it issues. The clause
  ranges over the labels that OCCUR in the checker's state: over every label below its counter
  it had no renaming after a statement that borrows (docs/31 D23, `Regress/CopyLabels.lean`).
  (The audit's A15, the counter after a private copy, is absorbed: `Rel.private_copy`.)
* `early`: the checker's state is the reference's after some of its borrows ended early (`E`),
  compared at the SAME future (`SimEq`), with bindings position by position and a borrow in
  flight by its label, the meanings EQUAL (with `⊑` the relation admitted a reference state with
  a value where the checker's has `⊥` inside a tuple, from which a match's join and `Id` differ:
  docs/31 D24). The futures range over those that agree with the run's off the labels
  live after the ends, which is D20 item 2's repair (a binding of an inert loan is the constant
  `φ ℓ` in the reference and `φ' ℓ` in the checker's state). With it, the loan witness (`Wit`,
  docs/31 D27): every label the reference's [Access] of a place ends, outside `E`, is one the
  checker's [Access] of that place ends. Equality after the ends reads the reference state only
  where each label of `E` has its holder's content, and [Access] reads every future: without the
  witness a reference state that reads a label only at other values of an early-ended one was
  related, and a read from it ended a label the checker kept (D25, `Regress/EarlyUnpinned.lean`).
  A tie to a `Good` checker-form preimage does not repair that (`Regress/CondDep.lean`: an unknown
  callee's backward function makes one label's dependence conditional on another's content).

**Status.** The relation (`SimEq`, `Sim`, `Rel`) is defined in `Statements.lean`, where the
three statements refuted by `Regress/StaleTemp.lean` (`eval_step_stmt`, `evalCore_step_stmt`,
`letIn_step_stmt`) are now in the simulation form. Proved here: `Rel.start` (the relation holds
at the start) and `sim_seq` (steps in this form compose); in `Statements.lean`: `Sim.of_below`,
`Sim.of_simEq_below` (nothing true under the old order is lost); and `Rel.private_copy` (the
relation survives a private copy of the checker's, reference state and renaming unchanged). NOT done: the other statements
of `Statements.lean` that run the reference from `SM' K ρ st` still have the `Below` form;
migrating them is the next batch (each `Below (MState.mean … st') s'.toMean` conjunct becomes
`Rel`, each `SM' K ρ st` a universally quantified `s` with `Rel`, the returned value read at the
future pulled back along the renaming).
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The relation holds at the start**: the checker's state read as a reference state simulates
it, with no renaming and no early end, given the loan witness with no early end (`hw`): each place
of the state reads the future only through the loans the checker's access of it ends. That holds
at the generic state of a definition, whose values are unknowns, borrows of unknowns and loans;
it is FALSE where a later field's type or a sealed field's hint reads an earlier field that is
lent, the audit's A13 (open dependent values), where the reference's access ends a borrow the
checker's keeps. (If this failed the relation would be unusable: every top-level statement starts
here.) -/
theorem Rel.start (st : MState) (hw : Wit K id [] st.env (SM' K ρ st)) : Rel K ρ φ id st (SM' K ρ st) where
  skel := rfl
  fresh := fun _ h _ => h
  early := ⟨[], ⟨fun ψ _ p _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ st).valAt p ψ
      rw [sstate_valAt]; rfl,
    fun _ _ _ h => h,
    fun f i l h => ⟨i, h, fun ψ _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ st).valAt (.temp f i) ψ
      rw [sstate_valAt]; rfl⟩⟩, hw⟩

/-! ### Where the relation starts: the witness from the state's shape

`Rel.start` assumes the loan witness with no early end. At a state whose every value is loan-free
or a bare loan, it holds outright (`wit_start`, from `meanV_congr`): a loan-free value means a
constant, and a bare loan reads its own label, whose end reads its holder's loan-free content. The
three places a run starts are of that shape:

* the generic state of a definition's check: each parameter an unknown, a proof `⋆`, a borrow of
  an unknown, each borrowed cell a bare loan;
* the empty state a sealed program re-runs from (`emptyState`): no value at all;
* a callee's frame (`runBodyCore`): its parameters bound to the arguments, loan-free or a borrow of
  loan-free content ((WF5), asserted where a call closes off), and its captures, which hold no loan
  ([Access] ends what a capture reads).

Beyond them the witness at the start is the path-local congruence of the state's meaning, which
fails exactly where a later field's type, or a sealed field's hint, reads an earlier field that is
lent (open dependent values, the audit's A13; docs/31 D27). -/

/-- A value of a state where a run starts: loan-free, or a bare loan. -/
def StartVal (v : Value) : Prop := (∀ l, v.hasLoanM l = false) ∨ ∃ l, v = .loan l

/-- A position of a state's reading reads the future through its value's loans alone. -/
theorem sm_valAt_const (st : MState) (hK : ∀ n, (K.C.global n).2.label = none) (p : Pos)
    (hlf : ∀ l, (valAt st.env p).hasLoanM l = false) (ψ ψ' : Future) :
    (SM' K ρ st).valAt p ψ = (SM' K ρ st).valAt p ψ' := by
  show (MState.sstate K.dm K.M K.Γ ρ st).valAt p ψ = (MState.sstate K.dm K.M K.Γ ρ st).valAt p ψ'
  rw [sstate_valAt, sstate_valAt]
  by_cases hp : p ∈ allPos st.env
  · rw [mean_eq_valAt _ _ _ _ _ _ p hp, mean_eq_valAt _ _ _ _ _ _ p hp, meanV_eq_mean, meanV_eq_mean]
    exact meanV_congr K ρ ψ ψ' _ _ hK fun l h => absurd h (by simp [hlf l])
  · rw [mean_eq_err _ _ _ _ _ _ p hp, mean_eq_err _ _ _ _ _ _ p hp]

/-- **The witness at the start**, for a state whose values are loan-free or bare loans. -/
theorem wit_start (st : MState) (hK : ∀ n, (K.C.global n).2.label = none)
    (hv : ∀ p, StartVal (valAt st.env p)) : Wit K id [] st.env (SM' K ρ st) := by
  intro q pos steps _ _ m hr _
  have noReach : ∀ {s : SState} {o : Sem → Sem} {m : Nat}, (∀ ψ ψ', s.valAt pos ψ = s.valAt pos ψ') →
      ¬ ReachDep s pos o m := by
    intro s o m hc hr
    have hd : ∀ {l : Nat}, ¬ s.obsDep pos o l := by
      rintro l ⟨ψ, x, hne⟩; exact hne (by rw [hc ψ (ψ.upd l x)])
    cases hr with
    | direct _ hd' => exact hd hd'
    | via _ hd' _ => exact hd hd'
  rcases hv pos with hlf | ⟨l, hl⟩
  · exact absurd hr (noReach (sm_valAt_const K ρ st hK pos hlf))
  · have hp : pos ∈ allPos st.env := by
      refine Classical.byContradiction fun hp => ?_
      refine noReach (fun ψ ψ' => ?_) hr
      show (MState.sstate K.dm K.M K.Γ ρ st).valAt pos ψ = (MState.sstate K.dm K.M K.Γ ρ st).valAt pos ψ'
      rw [sstate_valAt, sstate_valAt, mean_eq_err _ _ _ _ _ _ pos hp, mean_eq_err _ _ _ _ _ _ pos hp]
    have hS : ∀ ψ, (SM' K ρ st).valAt pos ψ = ψ l := by
      intro ψ
      show (MState.sstate K.dm K.M K.Γ ρ st).valAt pos ψ = ψ l
      rw [sstate_valAt, mean_eq_valAt _ _ _ _ _ _ pos hp, hl]; rfl
    -- what the access reaches is `l`, live
    have key : m = l ∧ (SM' K ρ st).Live l := by
      cases hr with
      | direct hlive hd =>
        obtain ⟨ψ, x, hne⟩ := hd
        refine ⟨Classical.byContradiction fun hml => hne ?_, ?_⟩
        · rw [hS, hS, Future.upd_other _ _ (Ne.symm hml)]
        · by_cases hml : m = l
          · exact hml ▸ hlive
          · exact absurd (by rw [hS, hS, Future.upd_other _ _ (Ne.symm hml)]) hne
      | via hlive hd hr' =>
        rename_i l₂
        obtain ⟨ψ, x, hne⟩ := hd
        have hl₂ : l₂ = l := Classical.byContradiction fun h =>
          hne (by rw [hS, hS, Future.upd_other _ _ (Ne.symm h)])
        subst hl₂
        exfalso
        obtain ⟨r, hr⟩ := SState.holderOf_of_live hlive
        obtain ⟨hrpos, hrsh⟩ := SState.holderOf_spec hr
        refine noReach (fun ψ ψ' => ?_) hr'
        have hposm : pos ∈ (SM' K ρ st).positions := by
          show pos ∈ (MState.sstate K.dm K.M K.Γ ρ st).positions; rw [sstate_positions]; exact hp
        have hrp : pos ≠ r := by
          intro e; subst e
          have : Env.shape st.env pos = some l₂ := hrsh
          simp [Env.shape, hl] at this
        rw [SState.endLabel_eq hr, SState.endAt_valAt _ _ _ _ hposm]
        simp only [hrp, if_false, hS, Future.upd_same]
        -- the holder's value is a borrow, so loan-free: its content reads no future
        rcases hv r with hlf | ⟨l', hl'⟩
        · exact sm_valAt_const K ρ st hK r hlf ψ ψ'
        · have : Env.shape st.env r = some l₂ := hrsh
          simp [Env.shape, hl'] at this
    obtain ⟨rfl, hlive⟩ := key
    refine ⟨m, rfl, ?_⟩
    -- the checker's access of the place ends `m`: the loan is the first thing on the path
    have hll : liveLoan st.env m = true := by
      obtain ⟨r, hr⟩ := SState.holderOf_of_live hlive
      obtain ⟨hrpos, hrsh⟩ := SState.holderOf_spec hr
      have hrpos' : r ∈ allPos st.env := by
        have := hrpos; rwa [show (SM' K ρ st).positions = allPos st.env from sstate_positions _ _ _ _ _] at this
      have hsh : Env.shape st.env r = some m := hrsh
      unfold liveLoan findBorrow
      rw [Option.isSome_iff_exists]
      cases hval : valAt st.env r with
      | borrow l' w =>
        have : l' = m := by simp [Env.shape, hval] at hsh; exact hsh
        subst this
        exact List.find?_isSome.mpr ⟨r, hrpos', by simp [hval, Value.holdsBorrow]⟩ |> Option.isSome_iff_exists.mp
      | _ => simp [Env.shape, hval] at hsh
    rw [hl]
    rcases steps with _ | ⟨st₀, ss⟩
    · simp [accLoans, loanOnPath, hll]
    · simp [accLoans, loanOnPath, hll]

/-- **The relation holds at the start of a run**: at a state whose values are loan-free or bare
loans (the generic state of a definition, the empty state of a sealed program's re-run, a callee's
frame), the checker's state read as a reference state simulates it. -/
theorem Rel.start_simple (st : MState) (hK : ∀ n, (K.C.global n).2.label = none)
    (hv : ∀ p, StartVal (valAt st.env p)) : Rel K ρ φ id st (SM' K ρ st) :=
  Rel.start K ρ φ st (wit_start K ρ st hK hv)

/-! ### A private copy (docs/31 D23; prerequisite (b) of the migration)

The checker runs a statement (a type, a proof, an erased term) on a private copy of its state and
then restores the snapshot (`restoreKeep`), keeping the name counters, the records and the types
of the unknowns created inside. The reference does not run a proof at all and runs a type on a
copy it discards, counter included. So after a statement the checker has issued labels the
reference has not, and the relation must survive with the reference state UNTOUCHED and the SAME
renaming. It does, because a label issued inside a copy occurs nowhere after it: Ω is the
snapshot's, and the records and types that survive hold no loan at all ((WF11)). -/

/-- What `restoreKeep` leaves: the snapshot's Ω and goal, the copy's counters and records. -/
theorem restoreKeep_spec (saved cur st' : MState) (fuel : Nat) (h : Runs (restoreKeep saved) cur fuel () st') :
    st'.env = saved.env ∧ st'.goal = saved.goal ∧ st'.inds = saved.inds ∧
    st'.nextLoan = cur.nextLoan ∧ st'.neutrals = cur.neutrals ∧ st'.etaRefs = cur.etaRefs := by
  unfold restoreKeep at h
  obtain ⟨-, rfl⟩ := Runs.unique h (runs_modify _ cur fuel)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A label occurs in a state through its Ω alone. -/
theorem occurs_of_env {st st' : MState} (h : st'.env = st.env) (l : Nat) : st'.Occurs l ↔ st.Occurs l := by
  unfold MState.Occurs; rw [h]

/-- **No label issued inside a private copy occurs after it**: with the labels of the snapshot's
Ω below its counter ((WF6), in the form `Occurs`), no label at or above that counter occurs in the
restored state. (Its types and records hold no loan at all: (WF11), a clause of `Good`.) -/
theorem private_copy_no_label (saved cur st' : MState) (fuel : Nat) (h : Runs (restoreKeep saved) cur fuel () st')
    (h6 : ∀ l, saved.Occurs l → l < saved.nextLoan) (l : Nat) (hl : saved.nextLoan ≤ l) : ¬ st'.Occurs l :=
  fun ho => absurd (h6 l ((occurs_of_env (restoreKeep_spec saved cur st' fuel h).1 l).mp ho)) (Nat.not_lt.mpr hl)

/-- **The relation survives a private copy**, with the reference state untouched and the same
renaming: whatever the copy did to the checker's counters and records, if Ω is the snapshot's
(and so are the declarations) the restored state is simulated as the snapshot was. This is the
step of an erased term on the checker's side; with `fresh` as first stated (every label below the
checker's counter) it was false (`Regress/CopyLabels.lean`). -/
theorem Rel.private_copy {π : Nat → Nat} {saved st' : MState} {s : SState} (hr : Rel K ρ φ π saved s)
    (henv : st'.env = saved.env) (h6 : ∀ l, saved.Occurs l → l < saved.nextLoan) : Rel K ρ φ π st' s where
  skel := by
    have e : (SM' K ρ st').env = (SM' K ρ saved).env := by
      simp only [SM', MState.sstate, henv]
    rw [e]; exact hr.skel
  fresh := fun l _ ho => hr.fresh l (h6 l ((occurs_of_env henv l).mp ho)) ((occurs_of_env henv l).mp ho)
  early := by
    have e : MState.mean K.dm K.M K.Γ ρ st' = MState.mean K.dm K.M K.Γ ρ saved := by
      simp only [MState.mean, henv]
    rw [e, henv]; exact hr.early

/-- Steps stated in the simulation form compose: if the first runs from any reference state
related to `st` into one related to `st₁`, and the second from any related to `st₁` into one
related to `st₂`, their sequence runs from any related to `st` into one related to `st₂` (each
under the renaming the step before it hands on). With the `Below` form the second premise is
available only at `SM' st₁`, and this fails. -/
theorem sim_seq {α β : Type 3} (x₁ : SM α) (x₂ : α → SM β) (st st₁ st₂ : MState)
    (h₁ : ∀ s π, Rel K ρ φ π st s → ∃ a s₁ π₁, x₁ s = some (a, s₁) ∧ Rel K ρ φ π₁ st₁ s₁)
    (h₂ : ∀ a s₁ π₁, Rel K ρ φ π₁ st₁ s₁ → ∃ b s₂ π₂, x₂ a s₁ = some (b, s₂) ∧ Rel K ρ φ π₂ st₂ s₂) :
    ∀ s π, Rel K ρ φ π st s → ∃ b s₂ π₂, (x₁ >>= x₂) s = some (b, s₂) ∧ Rel K ρ φ π₂ st₂ s₂ := by
  intro s π hs
  obtain ⟨a, s₁, π₁, e₁, r₁⟩ := h₁ s π hs
  obtain ⟨b, s₂, π₂, e₂, r₂⟩ := h₂ a s₁ π₁ r₁
  refine ⟨b, s₂, π₂, ?_, r₂⟩
  simp only [Bind.bind]
  rw [e₁]
  exact e₂

end

end Ochr.Meaning.Steps
