import Ochr.Meaning.Value
import Ochr.Obs

/-!
# The meaning of a state, `⟦Ω⟧_ρ` (docs/18 Def. "meaning of a state", docs/27 §3)

A state means a function of a future: at each position (a binding or a temporary of a frame)
the meaning of the value held there, with every loan read from the future. With it comes the
state's *shape*, which positions hold a borrow of which label; (WF1) makes a borrow the whole
value of its position, so the shape is a partial map from positions to labels. Ending a borrow
is a step on these meanings alone (`Mean.semEnd`), and it loses only information (`Below`).

## Which components of `MState` the meaning reads

`MState` (`Ochr/Env.lean`) has some forty fields. The meaning of a state, part (a) of the main
theorem, reads exactly `env` (the values at every position, with the frame structure) and `inds`
(to interpret constructor values and inductive types); its typed form, for membership (b) and
the goal, also reads the stored types in `env` (`Binding.ty`, `Binding.lazyTy`), `absTy` (Δ),
`goal`, and the records `neutrals` and `etaRefs`, which are conditions on the assignment (the path
condition, `WF.lean`). `globals` enters through `CodeMeaning.global`, the meanings of the
earlier definitions. Every other field is semantically irrelevant to `⟦Ω⟧`, for one of three
reasons (`MState.Core` below is the relevant part, and `mean_core` the statement):

* **Names and bounds**: `nextLoan`, `nextAbs`, `nextRecUid`, `depth`. Fresh-name counters state no
  fact (`exitWorld`'s argument); the invariant needs only that every label and `σ` in the state
  is below its counter (freshness, `WF.lean`). `depth` is a bound whose overrun is exhaustion,
  never a decision.
* **Pure caches and logs**: `classCache`, `constDecls` (caches of syntactic readings: a lemma
  says a cached value is its recomputation), `cfg`, `locs` (recording only; `Accepted` leaves
  `located` off, so `locs` is empty).
* **Inputs of decisions, not of meanings**: `refs` (refinements already substituted into the
  state; read again only by [Rec]'s subterm test and the editor), `recStack` ([Rec]'s entry values
  and candidates: a check, whose accepting direction is membership of recursive functions),
  `convStack` ([Conv-fun]'s guard: it only makes conversion answer "no" more often, so conversion
  soundness holds for every stack), `lastErased`, `lastProof`, `curDecl`, `tailDecl`,
  `liveScope`, `headEval`, `wantTy`, `wantHere`, `deferCallTy`, `callTyLater` (the declared-type
  reader's plumbing: inputs to *aligned* decisions, D77/D80, which the model reads from the same
  syntax), `erasedDepth`, `privateDepth`, `inPlace`, `modelDepth`, `copying`, `observing`,
  `typing` (run modes selecting which rule applies; `observing` relaxes [End]'s wholeness check
  inside an observation, D68), and `placeLog` (D53's log of moves and writes at root positions;
  under D84 the drop at the join and a block's captures are decided statically, from syntax and
  declared types (`Decide.jdMoves` on branch `d84`), and the log is kept only for an internal
  assertion that never fires, so it feeds no decision).

So a step lemma may change any of those freely without changing `⟦Ω⟧`; what it must then show
is that the *decision* the field feeds is of a harmless kind (docs/18 §"Decisions, by kind").
-/

namespace Ochr.Meaning

deriving instance DecidableEq for Pos

/-- The shape of an environment: the label of the borrow held at a position, if any. -/
def _root_.Ochr.Env.shape (env : Env) (p : Pos) : Option Nat :=
  match valAt env p with
  | .borrow l _ => some l
  | _ => none

/-- The meaning of a state: its positions, what each means under a future, and its shape. -/
structure Mean : Type 3 where
  pos : List Pos
  val : Future → Pos → Sem
  shape : Pos → Option Nat

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- A stored type value as the run knows it: its meaning, and for `D(ā)` its declaration and
parameters' meanings (the structured hint, D8 revised); shapes of stored Π-types are the
run's business (`piShapeOf`). Read under the constant future (docs/27 Lemma 5). -/
noncomputable def _root_.Ochr.Value.tyS (ρ : Assignment) (T : Value) : TyS :=
  { m := (Value.mean dm C Γ ρ (fun _ => .err) (.plain .err) T).asTy,
    data := match T with
      | .tInd n args =>
        match Γ.find? (·.name == n) with
        | some d => some (n, Value.meanParams dm C Γ ρ (fun _ => .err) d 0 [] args)
        | none => none
      | _ => none }

/-- The type a position's value is read at (docs/31 D8): the binding's stored type, or `err` for
a temporary or an untyped slot. Types are read under the constant future, since no stored type
holds a live loan (docs/27 Lemma 5). -/
noncomputable def _root_.Ochr.Env.hintAt (ρ : Assignment) (env : Env) : Pos → TyS
  | .bind f i =>
    match env[f]?.bind (·.binds[i]?) with
    | some b =>
      match b.ty, b.lazyTy with
      | some T, _ => Value.tyS dm C Γ ρ T
      | none, some (P, ws, j) => C.paramTy ρ P ws j
      | none, none => .plain .err
    | none => .plain .err
  | .temp _ _ => .plain .err

/-- The meaning of an environment under `ρ` and `φ`, position by position. -/
noncomputable def _root_.Ochr.Env.mean (ρ : Assignment) (φ : Future) (env : Env) (p : Pos) : Sem :=
  -- a position outside the environment means `err`, as it does in the run's state (`valAt`'s
  -- out-of-range default is `()`, which would make a dropped position compare `()` with `err`:
  -- the pilot prover's finding)
  match p with
  | .bind f i => match env[f]?.bind (·.binds[i]?) with
    | some b => Value.mean dm C Γ ρ φ (Env.hintAt dm C Γ ρ env p) b.val
    | none => .err
  | .temp f i => match env[f]?.bind (·.temps[i]?) with
    | some v => Value.mean dm C Γ ρ φ (Env.hintAt dm C Γ ρ env p) v
    | none => .err

/-- `⟦Ω⟧_ρ`: the meaning of a state, as a function of the future. -/
noncomputable def MState.mean (ρ : Assignment) (st : MState) : Mean :=
  ⟨allPos st.env, fun φ => Env.mean dm C Γ ρ φ st.env, Env.shape st.env⟩

/-- The state with a value in flight counted: `v` pushed as a temporary of the top frame. A
step's result is read through it (`Good (st.withTemp v)`), since a value the checker returns in
its monad is part of the state its rules see (the pilot prover's finding: a borrow in flight
is a borrow in Ω for (WF2)). -/
def _root_.Ochr.MState.withTemp (st : MState) (v : Value) : MState :=
  { st with env := st.env.modify (st.env.size - 1) fun fr => { fr with temps := fr.temps.push v } }

/-- The components of `MState` that `⟦Ω⟧_ρ` and its typed form read (the module docstring). -/
structure MState.Core where
  env : Env
  inds : List IndDecl
  absTy : Array Value
  goal : Option Value
  neutrals : List (Value × Nat)
  etaRefs : List (Nat × Value)

def _root_.Ochr.MState.core (st : MState) : MState.Core :=
  ⟨st.env, st.inds, st.absTy, st.goal, st.neutrals, st.etaRefs⟩

/-- The meaning of a state is a function of its core: every other field is irrelevant. -/
theorem MState.mean_core (ρ : Assignment) (st st' : MState) (h : st.core = st'.core) :
    MState.mean dm C Γ ρ st = MState.mean dm C Γ ρ st' := by
  have henv : st.env = st'.env := congrArg MState.Core.env h
  simp only [MState.mean, henv]

/-- The meaning of the type of abstract value `σ`, `⟦Δ(σ)⟧_ρ`. A type never holds a live loan
(docs/27 Lemma "types are hole-free"), so the future it is read under does not matter; the
constant future `err` is used. -/
noncomputable def MState.absTyM (ρ : Assignment) (st : MState) (σ : Nat) : TyM :=
  match st.absTy[σ]? with
  | some T => Value.tyM dm C Γ ρ (fun _ => .err) T
  | none => .err

/-- The meaning of the stored type at a position, if it has one: a binding's `ty`, or its
deferred type (D82 `lazyTy`: parameter `i` of the Π-type at the arguments as passed), through
`CodeMeaning.paramTy`; a temporary has none. -/
noncomputable def MState.posTyM (ρ : Assignment) (st : MState) : Pos → Option TyM
  | .bind f i =>
    match st.env[f]?.bind (·.binds[i]?) with
    | some b =>
      match b.ty, b.lazyTy with
      | some T, _ => some (Value.tyM dm C Γ ρ (fun _ => .err) T)
      | none, some (P, ws, j) => some (C.paramTy ρ P ws j).m
      | none, none => none
    | none => none
  | .temp _ _ => none

/-- The hint is the stored type where there is one. -/
theorem MState.hintAt_posTyM (ρ : Assignment) (st : MState) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ st p = some T) : (Env.hintAt dm C Γ ρ st.env p).m = T := by
  cases p with
  | bind f i =>
    simp only [MState.posTyM] at h
    simp only [Env.hintAt]
    split at h
    · split at h <;> simp_all [Value.tyM, Value.tyS]
    · cases h
  | temp _ _ => cases h

/-- The meaning of the goal, as a type. -/
noncomputable def MState.goalM (ρ : Assignment) (st : MState) : Option TyM :=
  st.goal.map (Value.tyM dm C Γ ρ (fun _ => .err))

end

/-! ## The information order on state meanings, and the steps on meanings -/

/-- `m'` is less informative than `m` (docs/18 Def. "less informative"): every reading of `m'`
is a reading of `m`, and `m'` holds a borrow only where `m` holds the same one. -/
def Below (m' m : Mean) : Prop :=
  ∀ φ', ∃ φ, (∀ p, m'.val φ' p ⊑ m.val φ p) ∧ ∀ p l, m'.shape p = some l → m.shape p = some l

theorem Below.refl (m : Mean) : Below m m :=
  fun φ => ⟨φ, fun _ => Sem.le_refl _, fun _ _ h => h⟩

theorem Below.trans {a b c : Mean} (h₁ : Below a b) (h₂ : Below b c) : Below a c := fun φ => by
  obtain ⟨φ₁, h₁, s₁⟩ := h₁ φ
  obtain ⟨φ₂, h₂, s₂⟩ := h₂ φ₁
  exact ⟨φ₂, fun p => Sem.le_trans (h₁ p) (h₂ p), fun p l h => s₂ p l (s₁ p l h)⟩

/-- [End ℓ] on meanings (docs/27 Def. 4): the borrow held at `r` ends; its final content is
fixed to what `r` holds now, and `r` is forgotten. -/
def Mean.semEnd (m : Mean) (r : Pos) (l : Nat) : Mean :=
  ⟨m.pos, fun φ p => if p = r then .moved else m.val (φ.upd l (m.val φ r)) p,
    fun p => if p = r then none else m.shape p⟩

/-- Ending a borrow loses only information: it narrows the futures to those in which `l` ends
with its current content, and forgets the holder. -/
theorem Mean.semEnd_below (m : Mean) (r : Pos) (l : Nat) : Below (m.semEnd r l) m := by
  intro φ'
  refine ⟨φ'.upd l (m.val φ' r), fun p => ?_, fun p l' h => ?_⟩
  · simp only [Mean.semEnd]
    split
    · exact .moved _
    · exact Sem.le_refl _
  · simp only [Mean.semEnd] at h
    split at h
    · cases h
    · exact h

/-- Forgetting a position (a [Drop], a stuck block's capture by move). -/
def Mean.forget (m : Mean) (r : Pos) : Mean :=
  ⟨m.pos, fun φ p => if p = r then .moved else m.val φ p, fun p => if p = r then none else m.shape p⟩

theorem Mean.forget_below (m : Mean) (r : Pos) : Below (m.forget r) m := by
  intro φ
  refine ⟨φ, fun p => ?_, fun p l h => ?_⟩
  · simp only [Mean.forget]; split
    · exact .moved _
    · exact Sem.le_refl _
  · simp only [Mean.forget] at h; split at h
    · cases h
    · exact h

/-- The meaning at `p` depends on label `l`: some future, changed at `l` alone, changes it. This
is what the reference run's [Access] ends (docs/27 §5: exactly the borrows the place's meaning
depends on), where the checker ends every borrow whose loan *occurs* in the content. -/
def Mean.dependsOn (m : Mean) (p : Pos) (l : Nat) : Prop :=
  ∃ φ s, m.val φ p ≠ m.val (φ.upd l s) p

end Ochr.Meaning
