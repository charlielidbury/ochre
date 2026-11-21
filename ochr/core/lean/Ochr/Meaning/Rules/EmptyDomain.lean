import Ochr.Meaning.Rules.Counter
import Ochr.Meaning.Regress.EqJ

/-!
# The rules trial: a comparison's generic argument at an empty type (the lead's test)

**Question.** Comparing two functions over an empty domain leaves the comparison's generic
argument, an unknown of the empty type, in the table of unknowns. Is the `ExtOk` conclusion of the
conversion statements (an extension of the assignment under which the state after is `Good`)
still true?

**Answer: for `Eq(Π(x : Empty). Nat, F, G)` yes, by the guard; in general no.**

- At `F`, `G : Π(x : Empty). Nat` the comparison leaves the unknown and no record naming it
  (checked below on the checker's state at a hole, compiled). `TypedAssignment.mem`,
  `Membership.absTy` and `DeltaOk` are each guarded by `st.Refd σ`, and nothing references the
  unknown, so it owes no member. That guard (`MState.Refd`, `Meaning/WF.lean`) is what makes this
  case true; no proof that the whole `ExtOk` holds there is attempted.
- But a comparison keeps the η-records its private copy made (`restoreKeep` keeps `etaRefs`,
  D37), and a typed run inside the copy (a parameter type or codomain evaluated at the generic
  arguments, `evalType`) refines an unknown of a one-constructor type in place (D93), recording
  `σ := C(σ̄)`. Over `inductive E1 := MkE1(e : Empty)` the record names `σ₁ : Empty`; `Refd.eta`
  makes it referenced; `TypedAssignment.mem` then asks a member of the empty type. So after
  `conv` of `Π(x : E1). match x { MkE1(e) => Nat }` and `Π(y : E1). Nat` no assignment is typed and
  `ExtOk` is false: `convPi_sound_stmt` is false (`convPi_sound_stmt_false_of_run`). The same
  record is left by `conv F3 G3` with `F3 (x : E1) (n : match x { MkE1(e) => Nat }) : Nat`
  (a later parameter's type matches on the generic argument) and by `conv P2 Q2` at a hole of a
  real program (both below).

**What is kernel-checked and what is not.** The model side is: from any state whose η-records
name an unknown stored at a declared type with no constructors, no assignment is typed, so the
statement's conclusion fails at every context admitting the start state. The machine side (that
the checker's `convPi` succeeds from the start state and leaves such a record) is checked by
`#guard`, compiled evaluation, the evidence `Regress/EqJ` uses for checker states: the kernel
cannot evaluate this run, because a match reaches `firstLiveLoanOnPath` (`Machine.lean`), which is
defined by well-founded recursion and does not reduce in the kernel. So the theorem takes the run
as a hypothesis, and the `#guard` discharges it by evaluation.

**Not a fault of the language**: the record names only unknowns made inside the comparison, which
nothing else references; a sibling copy never sees them. Either `Refd.eta` should be guarded by the
refined unknown being referenced otherwise (as `Refd.dep` is), or `restoreKeep` should drop the
records of unknowns made inside the copy.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr EmptyAt uses Nats {
  inductive Empty : Type
  inductive E1 : Type := MkE1(e : Empty)
  def F (x : Empty) : Nat := Z
  def G (y : Empty) : Nat := Z
  def EqEmpty : Eq(Π(x : Empty). Nat, F, G) := refl
  def P2 : Type := Π(x : E1). (match x { MkE1(e) => Nat })
  def Q2 : Type := Π(y : E1). Nat
  def F3 (x : E1) (n : (match x { MkE1(e) => Nat })) : Nat := Z
  def G3 (y : E1) (m : (match y { MkE1(e) => Nat })) : Nat := Z
  def TAt (n : Nat) : Nat := ?
}

namespace Ochr.Meaning.Rules.EmptyDomain
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## On the checker's state at a hole of a real program (compiled) -/

def stT : MState :=
  let r := Ochr.Test.runWith (some Prelude) "EmptyAt" EmptyAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "TAt") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

def gval (n : String) : Value := ((stT.globals.find? (·.name == n)).map (·.val)).getD .unit

/-- The run answers `true`; the table grows by `k` unknowns; the η-records naming a new unknown are
`recs`. -/
def leaves (x : M Bool) (k : Nat) (recs : Nat) : Bool :=
  match (runMachine x stT 1000000).1 with
  | .ok b st' => b && st'.absTy.size == stT.absTy.size + k &&
      (st'.etaRefs.filter fun e => e.2.anyAtom (fun | .abs σ => stT.absTy.size ≤ σ | _ => false)).length == recs
  | _ => false

#guard stT.absTy.size == 1
-- `F`, `G` over `Empty`: one more unknown (the generic argument, of type `Empty`), no record
#guard leaves (Ochr.conv 100000 (.gfn "F") (.gfn "G")) 1 0
-- over `E1` with a match in a type: a record naming the unknown of type `Empty` survives
#guard leaves (Ochr.conv 100000 (gval "P2") (gval "Q2")) 2 1
#guard leaves (Ochr.conv 100000 (.gfn "F3") (.gfn "G3")) 3 1

/-! ## The same at a hand-made start state, and the model side (kernel-checked) -/

def dEmpty : IndDecl := { name := "Empty" }
def dE1 : IndDecl := { name := "E1", ctors := [("MkE1", [("e", .tind "Empty" [])])] }
/-- The start state: nothing bound, `Empty` and `E1` declared. -/
def st0 : MState := { inds := [dEmpty, dE1] }
/-- `Π(x : E1). match x { MkE1(e) => Nat }` and `Π(y : E1). Nat`. -/
def P : Value := .tPi [] (.pi [⟨"x"⟩] [.tind "E1" []] (.matchInd (.var 0) "E1" [(⟨"e"⟩, .nat)])) []
def Q : Value := .tPi [] (.pi [⟨"y"⟩] [.tind "E1" []] .nat) []

/-- What the run leaves: an η-record naming `σ₁`, stored at `Empty`. -/
def leavesRec (st1 : MState) : Bool :=
  st1.etaRefs.any (fun e => e.2.hasAbs 1) &&
    (match st1.absTy[1]? with | some (Value.tInd "Empty" []) => true | _ => false)

theorem leavesRec_spec {st1 : MState} (h : leavesRec st1 = true) :
    (∃ e ∈ st1.etaRefs, e.2.hasAbs 1 = true) ∧ st1.absTy[1]? = some (.tInd "Empty" []) := by
  simp only [leavesRec, Bool.and_eq_true, List.any_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · assumption
  · cases h2

#guard match (runMachine (Ochr.convPi 16 P Q) st0 100).1 with
  | .ok b st1 => b && leavesRec st1
  | _ => false

/-- A declaration with no constructors has an empty carrier. -/
theorem car_empty (dm : DataModel) (d : IndDecl) (hd : d.ctors = []) (r : Rec) (x : dm.car d r) : False := by
  have hm : dm.Mem d r (dm.meanC x) := (dm.mem_iff_meanC d r _).2 ⟨x, rfl⟩
  obtain ⟨⟨c, hc⟩, -⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
  rw [hd] at hc
  exact absurd hc (Nat.not_lt_zero _)

theorem noBind0 (f i : Nat) : (st0.env[f]?.bind fun fr => fr.binds[i]?) = none := by
  rcases f with _ | f <;> simp [st0]

theorem allPos0 : allPos st0.env = [] := by decide +kernel
theorem values0 : Env.values st0.env = [] := by rw [Env.values, allPos0]; rfl

/-- `st0` is `Good` at every assignment (nothing bound, no unknown). -/
theorem good_st0 (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ st0 := by
  have hA := allPos0
  have hV := values0
  refine ⟨⟨fun σ _ h => by simp [st0] at h, fun n σ h => by simp [st0] at h, fun σ v h => by simp [st0] at h,
      fun σ r h => by simp [st0] at h⟩,
    ⟨?_, fun σ _ h => by simp [st0] at h, fun G h => by simp [MState.goalM, st0] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    cases p with
    | bind f i => simp only [MState.posTyM, noBind0] at hp; cases hp
    | temp f i => simp [MState.posTyM] at hp
  · rw [hA]; intro p hp; cases hp
  · rw [hA]; intro p hp; cases hp
  · rw [hV]; intro v hv; cases hv
  · intro l; rw [hV]; simp
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by rw [hA] at hp; cases hp⟩⟩
  · unfold WF4; rw [hV]; intro v hv; cases hv
  · exact MState.refd_lt st0 _
      (by rw [hV]; intro v hv; cases hv)
      (fun f i b T hb _ _ _ => by rw [noBind0] at hb; cases hb)
      (fun f i b P ws j hb _ => by rw [noBind0] at hb; cases hb)
      (fun G hG => by simp [st0] at hG) (fun m σ' h => by simp [st0] at h) (fun σ' v h => by simp [st0] at h)
      (fun σ' T h => by simp [st0] at h)
  · intro T hT; simp [st0] at hT
  · intro σ r h; simp [st0] at h
  · simp [st0]
  · rw [hV]; intro v hv; cases hv
  · intro p T _ f i b _ hb; rw [noBind0] at hb; cases hb
  · rw [hV]; intro v hv; cases hv
  · intro f i b hb; rw [noBind0] at hb; cases hb
  · intro T hT; simp [st0] at hT
  · intro G hG; simp [st0] at hG
  · intro p hp; rw [hA] at hp; cases hp
  · intro v hv; rw [hV] at hv; cases hv
  · intro f i b hb; rw [noBind0] at hb; cases hb
  · intro T hT; simp [st0] at hT
  · intro G hG; simp [st0] at hG
  · intro n σ h; simp [st0] at h
  · intro σ v h; simp [st0] at h
  · refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hx; simp [Env.sitesOf, hA] at hx
    · intro pos path _ l _ x hx; simp [Env.sitesOf, hA] at hx
    · refine ⟨?_, ?_⟩
      · intro v hv; rw [hV] at hv; cases hv
      · intro v hv; rw [hV] at hv; cases hv

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **No assignment is typed** at a state whose η-records name `σ₁`, stored at `Empty`, under a
context declaring `Empty` with no constructors. -/
theorem not_typed (hΓ : K.Γ = [dEmpty, dE1]) (C : CodeMeaning) (ρ' : Assignment) (st1 : MState)
    (h : leavesRec st1 = true) : ¬ TypedAssignment K.dm C K.Γ ρ' st1 := by
  intro ht
  obtain ⟨⟨e, he, h1⟩, h2⟩ := leavesRec_spec h
  have hr : st1.Refd 1 := .eta e.1 e.2 he (.inr h1)
  have hsz : 1 < st1.absTy.size := by
    rcases Nat.lt_or_ge 1 st1.absTy.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at h2; cases h2
  have hm := ht.mem 1 hr hsz
  simp only [MState.absTyM, h2, Value.tyM, Value.mean, hΓ] at hm
  simp [dEmpty, Value.meanParams, Sem.asTy, DataModel.tyM, DataModel.tyR, Sem.mem, DataModel.strictInd,
    DataModel.paramsOk] at hm
  obtain ⟨x, -⟩ := hm
  exact car_empty K.dm dEmpty rfl _ x

/-- **`convPi_sound_stmt` is false**, at every run context that admits `st0`, given the checker's
run of `convPi` from `st0` (checked by the `#guard` above): its conclusion asks an extension under
which the state after is `Good`, and that state's η-record names an unknown of the empty type. -/
theorem convPi_sound_stmt_false_of_run (hctx : CtxOk K ρ st0) (bh : Nat) (st1 : MState)
    (hrun : Runs (Ochr.convPi 16 P Q) st0 bh true st1) (hrec : leavesRec st1 = true) :
    ¬ convPi_sound_stmt K ρ φ 16 := by
  intro h
  obtain ⟨-, -, ρ', Δ', D', -, -, -, hg⟩ := h st0 st1 P Q (good_st0 K ρ) hctx bh hrun
  exact not_typed K hctx.inds _ ρ' st1 hrec hg.1

end

end Ochr.Meaning.Rules.EmptyDomain

#print axioms Ochr.Meaning.Rules.EmptyDomain.convPi_sound_stmt_false_of_run
