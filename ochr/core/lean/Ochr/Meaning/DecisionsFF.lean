import Ochr.Meaning.Steps.Statements

/-!
# The checker's decisions with no fuel (sixth lead, docs/31 D84)

`DecTab D st` (`Steps/Statements.lean`) asks the table to agree with the checker's decision at
EVERY fuel at which that decision succeeds. The chain's first instance, `checkerDecisions st fuel`
(`DecisionsInst.lean`), reads each decision at ONE fuel and answers a default where that fuel runs
out; on a term nested deeper than that fuel a larger fuel answers otherwise, so the instance never
meets `DecTab` (`Regress/OpenFalse.decTab_fixedFuel_false`, kernel-checked at fuel `1`), and every
step statement, which assumes `CtxOk` and with it the decisions aligned, was vacuous at the chain's
decisions.

**The fuel-free instance** (`checkerDecisionsFF`): a decision's answer is the checker's answer at
some fuel at which it succeeds, and a default where it never does (a classical choice; the table is
noncomputable). It meets `DecTab` (`decTab_ff`, proved) given ONE fact about the machine alone:
successful runs of a decision at different fuels agree (`DecideFuelAgree`, stated for the
machine-only lane: the decision procedures catch nothing and never branch on exhaustion, so a
successful run took the same path at every fuel). Fuel then appears in no statement.

**Concrete runs** that read a decision's value (`Regress/EntryCheck`, `Regress/JoinProbes`, by
`#guard` on the fixed-fuel instance) keep checking the checker's decisions; their link to this table
is `readDecisionFF_of_runs`: a successful run at some fuel fixes the table's answer.
-/

namespace Ochr.Meaning
open Ochr Ochr.Meaning.Steps

/-- The decision `x` (indexed by its fuel) succeeds at `st` with the answer `a`, at some fuel and
some budget. -/
def SucceedsAt {α : Type} (x : Nat → M α) (st : MState) (a : α) : Prop :=
  ∃ f b st', Runs (x f) st b a st'

/-- Successful runs of `x` at `st` agree, whatever their fuels. -/
def FuelAgree {α : Type} (x : Nat → M α) (st : MState) : Prop :=
  ∀ a a', SucceedsAt x st a → SucceedsAt x st a' → a = a'

open Classical in
/-- A decision read with no fuel: its answer at some fuel at which it succeeds, `dflt` where it
never does. -/
noncomputable def readDecisionFF {α : Type} (st : MState) (dflt : α) (x : Nat → M α) : α :=
  if h : ∃ a, SucceedsAt x st a then h.choose else dflt

/-- **A successful run fixes the table's answer**, where the decision's runs agree across fuels. -/
theorem readDecisionFF_of_runs {α : Type} {st : MState} {dflt : α} {x : Nat → M α} (hag : FuelAgree x st)
    {f b : Nat} {a : α} {st' : MState} (h : Runs (x f) st b a st') : readDecisionFF st dflt x = a := by
  have hs : ∃ a, SucceedsAt x st a := ⟨a, f, b, st', h⟩
  simp only [readDecisionFF, hs, dif_pos]
  exact hag _ _ hs.choose_spec ⟨f, b, st', h⟩

/-- The decision procedures `DecTab` asks about, each as a function of its fuel. -/
def flagsD (t : Term) (f : Nat) : M (Bool × Bool) := do
  let d ← withLive true (Ochr.declOf f false [] [] t)
  pure ((← Ochr.preFlags t d).getD (false, false))
def placeDeclD (p : Place) (f : Nat) : M DeclInfo := withLive true (Ochr.placeDecl f [] p)
def declOfD (t : Term) (f : Nat) : M DeclInfo := withLive true (Ochr.declOf f false [] [] t)
def copyD (r : DeclInfo) (f : Nat) : M Bool := Ochr.declCopy f r
def piSortD (t : Term) (f : Nat) : M Nat := withLive true (Ochr.sortOf f (.tPi [] t []))
def joinMovesD (entry : List Place) (t : Term) (f : Nat) : M (List Place) := withLive true (Ochr.jdMoves f [] [] t entry)
def typeStateD (t : Term) (f : Nat) : M Ochr.TypeState := withLive true (Ochr.typeState f t)
def typeDeclD (T : Term) (f : Nat) : M DeclInfo := withLive true (Ochr.typeDecl f false [] [] T)

/-- **The decision procedures' answers do not depend on the fuel at which they succeed** (machine
alone; for the machine-only lane; a guess, not proved): at every state, for every decision `DecTab`
reads. -/
def DecideFuelAgree (st : MState) : Prop :=
  (∀ t, FuelAgree (flagsD t) st) ∧ (∀ p, FuelAgree (placeDeclD p) st) ∧ (∀ t, FuelAgree (declOfD t) st) ∧
  (∀ r, FuelAgree (copyD r) st) ∧ (∀ t, FuelAgree (piSortD t) st) ∧
  (∀ entry t, FuelAgree (joinMovesD entry t) st) ∧ (∀ t, FuelAgree (typeStateD t) st) ∧
  (∀ T, FuelAgree (typeDeclD T) st)

theorem decide_fuel_agree (st : MState) : DecideFuelAgree st := by
  sorry

/-- **The checker's decisions with no fuel**: each field the checker's answer at any fuel at which it
succeeds, in the scope state of the readings (`scopeState`, as `checkerDecisions₀`), the defaults
`checkerDecisions₀`'s. D90's [Entry] captures are given separately (`blockCaps`), as their own
statement moves out of `CtxOk` (the orchestrator's queue). -/
noncomputable def checkerDecisionsFF (st : MState)
    (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat) := fun _ _ _ => ([], [])) :
    Decisions where
  flags sc t := readDecisionFF (scopeState st sc) (false, false) (flagsD t)
  placeDecl sc p := readDecisionFF (scopeState st sc) .other (placeDeclD p)
  declOf sc t := readDecisionFF (scopeState st sc) .other (declOfD t)
  copy r := readDecisionFF st false (copyD r)
  piSort sc t := readDecisionFF (scopeState st sc) 1 (piSortD t)
  joinMoves sc entry t := readDecisionFF (scopeState st sc) entry (joinMovesD entry t)
  rePointed sc t := (readDecisionFF (scopeState st sc) ({} : Ochr.TypeState) (typeStateD t)).repointed
  typeDecl sc T := readDecisionFF (scopeState st sc) .other (typeDeclD T)
  blockCaps := bc
  -- `Machine.evalMatchByType`'s `largeElim` of the scrutinee's declaration (docs/31 D229; no fuel)
  subsingleton n := readDecisionFF st true (fun _ => do Ochr.largeElim (← lookupInd n))

/-- **The fuel-free table meets `DecTab`** (proved), given that the machine's decisions agree across
fuels at the scope states (`decide_fuel_agree`). -/
theorem decTab_ff (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat))
    (hag : ∀ sc, DecideFuelAgree (scopeState st sc)) (hagc : DecideFuelAgree st) :
    DecTab (checkerDecisionsFF st bc) st where
  flags fuel sc t fl b st' h := readDecisionFF_of_runs ((hag sc).1 t) (f := fuel) h
  placeDecl fuel sc p d b st' h := readDecisionFF_of_runs ((hag sc).2.1 p) (f := fuel) h
  declOf fuel sc t d b st' h := readDecisionFF_of_runs ((hag sc).2.2.1 t) (f := fuel) h
  copy fuel r c b st' h := readDecisionFF_of_runs (hagc.2.2.2.1 r) (f := fuel) h
  piSort fuel sc t l b st' h := readDecisionFF_of_runs ((hag sc).2.2.2.2.1 t) (f := fuel) h
  joinMoves fuel sc entry t ms b st' h := readDecisionFF_of_runs ((hag sc).2.2.2.2.2.1 entry t) (f := fuel) h
  rePointed fuel sc t ts b st' h := by
    show (readDecisionFF (scopeState st sc) ({} : Ochr.TypeState) (typeStateD t)).repointed = ts.repointed
    rw [readDecisionFF_of_runs ((hag sc).2.2.2.2.2.2.1 t) (f := fuel) h]
  typeDecl fuel sc T d b st' h := readDecisionFF_of_runs ((hag sc).2.2.2.2.2.2.2 T) (f := fuel) h

/-- **The decisions the top-level chain instantiates** (docs/31 D84): fuel-free, with D90's [Entry]
captures read statically at the program's fuel until their clause leaves `CtxOk` for the [Entry]
step's hypothesis (queued with the typed-temporaries migration), after which no fuel remains. -/
noncomputable def chainDecisions (fuel : Nat) (st : MState) : Decisions :=
  checkerDecisionsFF st (BlockCaps.staticBlockCaps (checkerDecisionsFF st) st.inds fuel)

/-- (leaf, OPEN) **D90's [Entry] captures at the chain's table**: the static captures equal the
checker's wherever the checker computes them. As `DecAligned` states it (every fuel of
`ckBlockCaps` against the static reading at the program's fuel) it is suspect for the reason the
fixed-fuel table failed `DecTab`; the queued change takes the clause out of `CtxOk` into the
[Entry] step's hypothesis at the state where a block is entered (measured equal at all 335 of the
suite's successful block entries), after which this leaf goes. -/
theorem chainDecisions_blockCaps (fuel : Nat) (st : MState) :
    ∀ st₀, SameDec st₀ st → ∀ f mt bc b st', Runs (ckBlockCaps f mt) st₀ b bc st' →
      (chainDecisions fuel st).blockCaps (DecideScope.topReadings st) (entryOf st) mt = bc := by
  sorry

/-- **The chain's table is the checker's at every state** (assembled): `DecTab` from the fuel-free
reading and the machine's fuel agreement (`decTab_ff`, `decide_fuel_agree`), the captures from
their leaf. What `CtxOk.dec` asks, now satisfiable at the chain's decisions. -/
theorem chainDecisions_aligned (fuel : Nat) : ∀ st, DecAligned (chainDecisions fuel st) st := fun st =>
  { toDecTab := decTab_ff st _ (fun sc => decide_fuel_agree _) (decide_fuel_agree st)
    blockCaps := chainDecisions_blockCaps fuel st }

end Ochr.Meaning
