import Ochr.Meaning.Conv.Refine
import Ochr.Meaning.Steps.DropRuns

/-!
# N3's machine half for `mkEqM` (conv1, 2026-11-28)

The old attempt's `Rules/RefineEq.lean` against today's checker (`mkEqM` and `fieldTele` are
unchanged since; `conv` is D103's): the proposition `mkEqM` builds is one `Eq` computes to by the
rules (`Conv/Rules.lean`'s `EqTo`), and the state after is reached from the one before. `mkEqM` is
not wrapped: [Eq-inj]'s field types (`fieldTypesOf`) may leave new unknowns and η-records on old
unknowns of one-constructor types (the trial's `GrowthProbe`), so the relation is the reached-state
one (`Reach`: Ω, the goal, the refinements and the declarations kept, the tables grown), not
`NamesKept`. Assumes ONE fact, about the checker alone: `fieldTypesOf` keeps `Reach` (`FieldTysKept`).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Machine

/-- A sub-computation of `mkEqM` starts from the start state with its tables grown: Ω, the goal,
the refinements, the declarations, Σ and the comparison stack kept. -/
def Reach (st st₁ : MState) : Prop :=
  KeptAfter st st₁ ∧ st₁.globals = st.globals ∧ st₁.convStack = st.convStack

theorem Reach.refl (st : MState) : Reach st st :=
  ⟨⟨rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _⟩, rfl, rfl⟩

theorem Reach.trans {a b c : MState} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨⟨e1, g1, r1, i1, s1, t1, n1⟩, gl1, cs1⟩ := h₁
  obtain ⟨⟨e2, g2, r2, i2, s2, t2, n2⟩, gl2, cs2⟩ := h₂
  refine ⟨⟨e2.trans e1, g2.trans g1, r2.trans r1, i2.trans i1, Nat.le_trans s1 s2, fun σ hσ => ?_,
    Nat.le_trans n1 n2⟩, gl2.trans gl1, cs2.trans cs1⟩
  rw [t2 σ (Nat.lt_of_lt_of_le hσ s1), t1 σ hσ]

/-- A comparison's exit (names only) is reached. -/
theorem Reach.ofNames {a b : MState} (h : NamesKept a b) : Reach a b := by
  obtain ⟨e, -, l, s, t, -, -⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, s, t, l⟩, ?_, ?_⟩ <;> rw [e]

def StateRel.reach : StateRel := ⟨Reach, Reach.refl, Reach.trans, fun h => h.2.1, Reach.ofNames⟩

/-- **(C) The one fact this file assumes, about the checker alone**: [Eq-inj]'s field types
(`fieldTypesOf`) keep `Reach`. Read true against the code: `fieldTele` pushes a frame, binds the
parameters and the fields there, evaluates each field type with `evalType` (a statement, run on a
private copy that `restoreKeep` puts back but for names and records) and pops the frame; Ω, the
goal, the refinements, Σ, the declarations and the comparison stack are as they were, the tables
only grow (`machineGrows`). Unproved. -/
def FieldTysKept : Prop :=
  ∀ fuel d args c fs st st' bh (Ts : List (String × Value)),
    Runs (Ochr.fieldTypesOf fuel d args c fs) st bh Ts st' → Reach st st'

/-- What B for `mkEqM` takes as given, at a relation. -/
structure EqKept (R : StateRel) : Prop where
  fieldTys : ∀ fuel d args c fs st st' bh (Ts : List (String × Value)),
    Runs (Ochr.fieldTypesOf fuel d args c fs) st bh Ts st' → R.rel st st'
  inds : ∀ {a b}, R.rel a b → b.inds = a.inds

theorem EqKept.reach (hf : FieldTysKept) : EqKept StateRel.reach :=
  ⟨hf, fun h => h.1.2.2.2.1⟩

/-- `anyM` answered `false`: every element's test answered `false`, each from a state the last
left. -/
theorem runs_anyM_false {α : Type} (p : α → M Bool) (P : MState → Prop)
    (hp : ∀ x st st' bh (b : Bool), P st → Runs (p x) st bh b st' → P st') :
    ∀ (xs : List α) {st st' : MState} {bh : Nat} {b : Bool}, P st → Runs (xs.anyM p) st bh b st' →
      P st' ∧ (b = false → ∀ x ∈ xs, ∃ s₁ s₂ b₁, P s₁ ∧ Runs (p x) s₁ b₁ false s₂)
  | [], st, st', bh, b, hP, h => by
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hP, fun _ x hx => by cases hx⟩
  | x :: xs, st, st', bh, b, hP, h => by
    rw [List.anyM_cons] at h
    obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    have hP1 := hp x _ _ _ _ hP h1
    split at h2
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
      exact ⟨hP1, fun h => by cases h⟩
    · rename_i hy
      obtain ⟨hP2, hall⟩ := runs_anyM_false p P hp xs hP1 h2
      refine ⟨hP2, fun hb z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · simp only [Bool.not_eq_true] at hy
        exact ⟨st, st₁, bh, hP, hy ▸ h1⟩
      · exact hall hb z hz

/-- The field equations: `mapM` over the zipped field types and fields. -/
theorem runs_mapM_eqL (E : Syn) (G : Premises) (gs₀ : List GDef) (Γ : List IndDecl) (P : MState → Prop)
    (f : Value × (Value × Value) → M Value)
    (hf : ∀ T v w st st' bh Q, P st → Runs (f (T, (v, w))) st bh Q st' → P st' ∧ EqTo E G gs₀ Γ T v w Q) :
    ∀ (Ts fs gs : List Value) {st st' : MState} {bh : Nat} {Ps : List Value}, Ts.length = fs.length →
      fs.length = gs.length → P st → Runs ((Ts.zip (fs.zip gs)).mapM f) st bh Ps st' →
      P st' ∧ EqL E G gs₀ Γ Ts fs gs Ps
  | [], [], [], st, st', bh, Ps, _, _, hP, h => by
    rw [List.zip_nil_left, List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hP, .nil⟩
  | T :: Ts, v :: fs, w :: gs, st, st', bh, Ps, h1, h2, hP, h => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.mapM_cons] at h
    obtain ⟨Q, st₁, b₁, h3, h4⟩ := Runs.bind_inv h
    obtain ⟨Qs, st₂, b₂, h5, h6⟩ := Runs.bind_inv h4
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h6
    obtain ⟨hP1, d1⟩ := hf _ _ _ _ _ _ _ hP h3
    obtain ⟨hP2, d2⟩ := runs_mapM_eqL E G gs₀ Γ P f hf Ts fs gs (Nat.succ.inj h1) (Nat.succ.inj h2) hP1 h5
    exact ⟨hP2, .cons d1 d2⟩
  | [], _ :: _, _, _, _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, _, _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, _, _, _, _, h2, _, _ => by simp at h2

section
variable (R : StateRel)

/-- `mkEqM` at `fuel`: from any state the computation reached, the state after is reached too,
and the proposition built is one `Eq` computes to. -/
def MkEqOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (A a b P : Value) (bh : Nat), R.rel st₀ st →
    Runs (Ochr.mkEqM fuel A a b) st bh P st' →
    R.rel st₀ st' ∧ EqTo Syn.machine (machPremisesR R.rel st₀) st₀.globals st₀.inds A a b P

theorem mkEqOK_step (hk : EqKept R) {n : Nat} (ih : MkEqOK R n) : MkEqOK R (n + 1) := by
  intro st₀ st st' A a b P bh hr h
  unfold Ochr.mkEqM at h
  have fin : ∀ s₁ s₂ b₁ Q, R.rel st₀ s₁ →
      Runs (if distinctCtors a b = true then pure vFalse else pure (A.tEq a b) : M Value) s₁ b₁ Q s₂ →
      R.rel st₀ s₂ ∧ EqTo Syn.machine (machPremisesR R.rel st₀) st₀.globals st₀.inds A a b Q := by
    intro s₁ s₂ b₁ Q hr1 h1
    split at h1
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h1; exact ⟨hr1, .disj (by assumption)⟩
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h1; exact ⟨hr1, .stuck⟩
  have convOK := (allOK R n).1
  split at h
  · rename_i hbot
    obtain ⟨u, s1, b1, h1, h2⟩ := Runs.bind_inv h
    have e := runs_fire_inv h1; subst e
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
    exact ⟨hr, .disjBot (bne_iff_ne.mp hbot)⟩
  · obtain ⟨c0, s1, b1, h1, h2⟩ := Runs.bind_inv h
    clear h
    obtain ⟨r1, d1⟩ := convOK st₀ _ _ _ _ _ _ hr h1
    clear h1
    split at h2
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
      exact ⟨r1, .refl (d1 (by assumption))⟩
    · simp only at h2
      split at h2
      · obtain ⟨r2, d2⟩ := ih st₀ _ _ _ _ _ _ _ r1 h2
        exact ⟨r2, .succ d2⟩
      · rename_i t c hh ps fs u c' hh' qs gs hbot
        clear d1
        split at h2
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨rfl, rfl⟩, hlen⟩ := hc
          split at h2
          · rename_i args hargs
            obtain ⟨dd, s2, b2, h3, h4⟩ := Runs.bind_inv h2
            obtain ⟨rfl, hdd⟩ := runs_lookupInd_inv h3
            clear h3 h2
            rw [hk.inds r1] at hdd
            have hX : ∀ s₃ s₄ b₃ Q, R.rel st₀ s₃ →
                (dd.dependent c = true → ∀ j ∈ dd.indexFields c,
                  ConvV Syn.machine (machPremisesR R.rel st₀) st₀.globals (fs.getD j .bot) (gs.getD j .bot)) →
                Runs (do
                  let Ts ← fieldTypesOf n dd args c fs
                  if (Ts.length == fs.length) = true then do
                      let eqs ← List.mapM (fun x => mkEqM n x.fst x.2.fst x.2.snd)
                        ((List.map (fun x => x.snd) Ts).zip (fs.zip gs))
                      pure (andList eqs)
                    else if distinctCtors (Value.ind t c hh ps fs) (Value.ind t c hh' qs gs) = true then pure vFalse
                    else pure (A.tEq (Value.ind t c hh ps fs) (Value.ind t c hh' qs gs)) : M Value) s₃ b₃ Q s₄ →
                R.rel st₀ s₄ ∧ EqTo Syn.machine (machPremisesR R.rel st₀) st₀.globals st₀.inds A
                  (Value.ind t c hh ps fs) (Value.ind t c hh' qs gs) Q := by
              intro s₃ s₄ b₃ Q r3 hidx h5
              obtain ⟨Ts, s5, b5, h6, h7⟩ := Runs.bind_inv h5
              have r5 := R.trans r3 (hk.fieldTys _ _ _ _ _ _ _ _ _ h6)
              split at h7
              · rename_i hTl
                obtain ⟨eqs, s6, b6, h8, h9⟩ := Runs.bind_inv h7
                obtain ⟨rfl, rfl⟩ := runs_pure_inv h9
                have hTl' : (Ts.map (·.2)).length = fs.length := by
                  simpa only [List.length_map, beq_iff_eq] using hTl
                obtain ⟨r6, dl⟩ := runs_mapM_eqL Syn.machine (machPremisesR R.rel st₀) st₀.globals st₀.inds
                  (R.rel st₀) (fun x => mkEqM n x.fst x.2.fst x.2.snd)
                  (fun T v w _ _ _ _ hr' hm => ih st₀ _ _ _ _ _ _ _ hr' hm) _ fs gs hTl' hlen r5 h8
                exact ⟨r6, .inj hargs hdd hlen hidx ⟨_, _, _, _, _, r3, h6, rfl⟩ hTl' dl⟩
              · exact fin _ _ _ _ r5 h7
            split at h4
            · rename_i hdep
              obtain ⟨bl, s3, b3, h5, h6⟩ := Runs.bind_inv h4
              clear h4
              obtain ⟨r3, hall⟩ := runs_anyM_false _ (R.rel st₀)
                (fun j _ _ _ _ hr' hj => by
                  obtain ⟨y, _, _, hy1, hy2⟩ := Runs.bind_inv hj
                  obtain ⟨-, rfl⟩ := runs_pure_inv hy2
                  exact (convOK st₀ _ _ _ _ _ _ hr' hy1).1) _ r1 h5
              have hidx : bl = false → dd.dependent c = true → ∀ j ∈ dd.indexFields c,
                  ConvV Syn.machine (machPremisesR R.rel st₀) st₀.globals (fs.getD j .bot) (gs.getD j .bot) :=
                fun hbl _ j hj => by
                  obtain ⟨s₁, s₂, b₁, hr₁, hj⟩ := hall hbl j hj
                  obtain ⟨y, _, _, hy1, hy2⟩ := Runs.bind_inv hj
                  obtain ⟨hy, -⟩ := runs_pure_inv hy2
                  exact (convOK st₀ _ _ _ _ _ _ hr₁ hy1).2 (by simpa using hy)
              clear h5 hall
              split at h6
              · obtain ⟨u, s4, b4, h7, h8⟩ := Runs.bind_inv h6
                have e := runs_fire_inv h7; subst e
                split at h8
                · simp_all
                · exact fin _ _ _ _ r3 h8
              · rename_i hbl
                simp only [Bool.not_eq_true] at hbl
                subst hbl
                simp only [Bool.not_false, reduceIte] at h6
                obtain ⟨u, s4, b4, h7, h8⟩ := Runs.bind_inv h6
                have e := runs_fire_inv h7; subst e
                exact hX _ _ _ _ r3 (hidx rfl) h8
            · rename_i hdep
              obtain ⟨bl, s3, b3, h5, h6⟩ := Runs.bind_inv h4
              obtain ⟨rfl, rfl⟩ := runs_pure_inv h5
              simp only [Bool.false_eq_true, Bool.not_false, reduceIte] at h6
              exact hX _ _ _ _ r1 (fun h => absurd h hdep) h6
          · exact fin _ _ _ _ r1 h2
        · exact fin _ _ _ _ r1 h2
      · exact fin _ _ _ _ r1 h2

theorem mkEqOK_all (hk : EqKept R) : ∀ n, MkEqOK R n
  | 0 => by
    intro _ _ _ _ _ _ _ _ _ h
    unfold Ochr.mkEqM at h; exact (runs_exhausted_false h).elim
  | n + 1 => mkEqOK_step R hk (mkEqOK_all hk n)

end

/-- **N3's machine half for `mkEqM`, PROVED from one checker fact** (`FieldTysKept`): the
proposition `mkEqM` builds is one `Eq` computes to by the rules, in the machine's instance (premises:
the machine's runs of `convPi`, `convFnRun` and `fieldTypesOf` from reached states), and the state
after is reached from the one before. -/
theorem mkEqM_refine (hf : FieldTysKept) (fuel : Nat) (st st' : MState) (A a b P : Value)
    (bh : Nat) (h : Runs (Ochr.mkEqM fuel A a b) st bh P st') :
    EqTo Syn.machine (machPremisesR Reach st) st.globals st.inds A a b P ∧ Reach st st' := by
  obtain ⟨r, d⟩ := mkEqOK_all StateRel.reach (EqKept.reach hf) fuel st st st' A a b P bh (Reach.refl st) h
  exact ⟨d, r⟩

end Ochr.Meaning.Conv
