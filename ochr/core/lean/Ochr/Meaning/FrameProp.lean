import Ochr.Meaning.CallRef
import Ochr.Meaning.Locality
import Ochr.Meaning.Strict.Fund

/-!
# The frame property of the reference's run, with a renaming of labels (docs/31 D62, D70)

The checker runs a known callee's body in place: its frame pushed on the caller's state. The
reference applies the callee's meaning, built from runs of the body in the closure's own frame: one
frame (above frame 0, `SState.under`, docs/31 D126), its own labels from `0`, each borrow parameter at a label of its own with a CELL, a binding of
frame 0 reading the label's final content (`Run.lean`'s `.fix` clause, `bodyAt`). `callOf_inPlace`
(`Steps/Call.lean`) says the two agree; it rests on this file's one simulation, which is both the
frame property and the renaming of labels:

- a run of a term from a state whose top frame is a callee's reads and writes only that frame, and
  reaches the caller's frames only through the labels the frame holds, which the cells stand for;
- the run does not depend on which labels it issues: the closure's labels are the in-place ones
  under an injective renaming `σ` that maps the closure's counter onwards to the in-place counter
  onwards (`Lemmas.run_counter_indep` was this alone; it is now a corollary,
  `run_counter_indep_of_frame`).

The relation (`FrameRel σ s₀ ks s s'`), between an in-place state `s` and a closure state `s'`, for the
in-place state `s₀` at the call and the parameter labels `ks` (in place, in cell order):
- the closure has one frame, above its frame 0 of cells (docs/31 D126: the checker's frame 0, where
  each borrow parameter's cell is a binding); in place the caller's frames of `s₀` lie below the callee's;
- the top frames hold the same bindings and temporaries, read through `σ` (an in-place value at `ψ` is
  the closure's at `ψ ∘ σ`), so an in-place top position `p` is the closure's `upPos c p`, in frame 1;
- the caller's frames keep their structure and holders, and read what they read at the call, at the
  future that gives each parameter label its cell's value (`lowerVal`, `cellFuture`);
- holders, top-frame sites, records and counters agree through `σ`; the caller's borrows keep their
  sites. Sites of the frame's borrows in the caller's frames are not compared: the closure has none,
  and nothing the run does reads them.

`Id` (`run_frame_obs`): its observation reads every position, so in place it reads the caller's
frames where the closure reads the cells. The two agree when the caller's frames determine the cells'
values at the observation, which holds where each parameter's final content there is a member of its
type (a place lent to a returned borrow reads its final content through the backward function,
injective on members only): the hypothesis `CellsDetermined`, which the checker's acceptance of the
callee's body gives (main's D98, typing) and the reference alone does not. With no parameter the
property holds for every term (`run_frame`'s second case). docs/31 D70.
-/

namespace Ochr

mutual
/-- A term holds no `Id` (outside embedded values, whose meanings are their own runs). -/
def Term.idFree : Term → Bool
  | .id .. => false
  | .assign _ t | .succ t | .ref t => t.idFree
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.idFree && u.idFree
  | .matchNat _ z s => z.idFree && s.idFree
  | .pi _ ds c => Term.idFreeList ds && c.idFree
  | .fix _ _ ds c _ b => Term.idFreeList ds && c.idFree && b.idFree
  | .call f as _ => f.idFree && Term.idFreeList as
  | .eq a b c => a.idFree && b.idFree && c.idFree
  | .ctor _ _ _ ps as => Term.idFreeList ps && Term.idFreeList as
  | .prim _ as | .tind _ as => Term.idFreeList as
  | .matchInd _ _ as => Term.idFreeArms as
  | _ => true
termination_by structural t => t

def Term.idFreeList : List Term → Bool
  | [] => true
  | a :: as => a.idFree && Term.idFreeList as
termination_by structural as => as

def Term.idFreeArms : List (Hint × Term) → Bool
  | [] => true
  | (_, a) :: as => a.idFree && Term.idFreeArms as
termination_by structural as => as
end

end Ochr

namespace Ochr.Meaning
open Ochr

/-- Where an in-place top-frame position sits in the closure's frame: frame `1`, the closure's frame
above its frame 0 of cells (docs/31 D126), at the same index. (`c`, the number of cells, no longer
offsets the temporaries since the cells moved to frame 0; kept for the callers.) -/
def upPos (_c : Nat) : Pos → Pos
  | .bind _ i => .bind 1 i
  | .temp _ j => .temp 1 j

/-- The closure's first `c` bindings of frame 0: the cells (docs/31 D126). -/
def cellsOf (c : Nat) (s' : SState) : List SVal := ((s'.env.headD {}).binds.map (·.val)).take c

/-- The closure's future of an in-place future: each closure label read at its in-place name. -/
def renF (σ : Nat → Nat) (ψ : Future) : Future := fun l => ψ (σ l)

/-- The future at which the caller's frames are read: each parameter label (in place) its cell's
value (a closure meaning, read at the closure's future). -/
def cellFuture (σ : Nat → Nat) (ks : List Nat) (cells : List SVal) (ψ : Future) : Future :=
  ψ.updList (ks.zip (cells.map (· (renF σ ψ))))

/-- A binding of the closure's frame, in place: the same declared reading, the same code, its label
renamed, its meaning read through the renaming. -/
def BindRen (σ : Nat → Nat) (b b' : SBinding) : Prop :=
  b.ty = { b'.ty with label := b'.ty.label.map σ } ∧ b.decl = b'.decl ∧ b.recBound = b'.recBound ∧
    ∀ ψ, b.val ψ = b'.val (renF σ ψ)


/-- **The in-place state `s` and the closure's state `s'`, related through the renaming `σ`** (closure
labels to in-place labels; docs/31 D70), for the in-place state `s₀` at the call and its parameter
labels `ks`, in cell order. -/
structure FrameRel (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (s s' : SState) : Prop where
  /-- the renaming is one to one, and the closure's fresh labels are the in-place fresh labels -/
  inj : ∀ l l', σ l = σ l' → l = l'
  fresh : ∀ j, σ (s'.nextLoan + j) = s.nextLoan + j
  /-- in place, the caller's frames and the callee's; the closure, its frame alone above an empty
  frame 0 (`SState.under`, docs/31 D126) -/
  frames : s.env.length = s₀.env.length ∧ s'.env.length = 2
  /-- the caller's frames keep their bindings' types and readings and their temporaries' number -/
  lowerSkel : ∀ f, f < s₀.topIdx →
    (s.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) =
    (s₀.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length))
  /-- and read what they read at the call, each parameter label at its cell -/
  lowerVal : ∀ p, p.frameOf < s₀.topIdx → ∀ ψ,
    s.valAt p ψ = s₀.valAt p (cellFuture σ ks (cellsOf ks.length s') ψ)
  /-- the caller's holders stay -/
  lowerShape : ∀ p, p.frameOf < s₀.topIdx → s.shape p = s₀.shape p
  /-- the same bindings in the top frame, renamed; the closure's temporaries are the cells, then the
  in-place ones, renamed -/
  top : ∃ F F', s.env.getLast? = some F ∧ s'.env.getLast? = some F' ∧ F.binds.length = F'.binds.length ∧
    (∀ (i : Nat) b b', F.binds[i]? = some b → F'.binds[i]? = some b' → BindRen σ b b') ∧
    F'.temps.length = F.temps.length ∧
    ∀ (j : Nat) v, F.temps[j]? = some v → ∃ v', F'.temps[j]? = some v' ∧ ∀ ψ, v ψ = v' (renF σ ψ)
  /-- the same holders in the top frame, renamed; the cells hold nothing, and the closure nothing else -/
  topShape : ∀ p, p.frameOf = s₀.topIdx → s.shape p = (s'.shape (upPos ks.length p)).map σ
  clShape : ∀ q l, s'.shape q = some l → ∃ p, p.frameOf = s₀.topIdx ∧ q = upPos ks.length p
  /-- the same records for the frame's labels, and the same held types but for the parameters' (in
  place the caller's, in the closure none: a parameter's holder is a binding, typed by its type) -/
  held : ∀ l, s'.Live l → s.heldMem (σ l) = s'.heldMem l ∧ (σ l ∉ ks → s.heldTy (σ l) = s'.heldTy l)
  /-- the same sites in the top frame, renamed; only the frame's labels have one there; the closure
  has no other -/
  lentTop : ∀ l (x : Site), x.pos.frameOf = s₀.topIdx →
    (x ∈ s.lent (σ l) ↔ { x with pos := upPos ks.length x.pos } ∈ s'.lent l)
  lentImg : ∀ m (x : Site), x.pos.frameOf = s₀.topIdx → x ∈ s.lent m → ∃ l, m = σ l
  lentCl : ∀ l (x : Site), x ∈ s'.lent l → ∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p
  /-- the caller's borrows keep their sites -/
  lentCaller : ∀ l p, p.frameOf < s₀.topIdx → s₀.shape p = some l → s.lent l = s₀.lent l
  /-- the frame's labels are the parameters' or the run's own (at or above the counter at the call) -/
  topLabels : ∀ l, s'.Live l → σ l ∈ ks ∨ s₀.nextLoan ≤ σ l

/-- What the in-place state at the call must be for the relation to start: the caller's frames read
no label at or above the counter (nothing the callee makes), the parameter labels are below it and
distinct, and the caller holds none of them and lends nothing in the callee's frame. -/
structure FrameStart (s₀ : SState) (ks : List Nat) : Prop where
  reads : ∀ p, p.frameOf < s₀.topIdx → ∀ ψ ψ', (∀ l, l < s₀.nextLoan → ψ l = ψ' l) → s₀.valAt p ψ = s₀.valAt p ψ'
  ks_lt : ∀ k ∈ ks, k < s₀.nextLoan
  callerHeld : ∀ p l, p.frameOf < s₀.topIdx → s₀.shape p = some l → l ∉ ks ∧ l < s₀.nextLoan
  callerLent : ∀ p l (x : Site), p.frameOf < s₀.topIdx → s₀.shape p = some l → x ∈ s₀.lent l → x.pos.frameOf < s₀.topIdx
  ks_nodup : ks.Nodup

/-- The two runs agree: the same result (its label renamed) and related states, or both fail. -/
def FrameAgree (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) : Option (Res × SState) → Option (Res × SState) → Prop
  | some (r, s₁), some (r', s₁') => r.1 = r'.1 ∧ r.2 = { r'.2 with label := r'.2.label.map σ } ∧ FrameRel σ s₀ ks s₁ s₁'
  | none, none => True
  | _, _ => False

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The frame property with a renaming of labels** (docs/31 D62, D70; open, the one simulation the
call steps rest on). From related states a term runs to the same result and related states, or
fails on both sides, when it holds no `Id` or the frame has no parameter (the `Id` clause is
`run_frame_obs`, under its hypothesis). Proof: induction on the term, clause by clause. What reads a
state reads the top frame (`resolve`, `scopeOf`, `movedPlaces`), the holders and sites at the top
frame (an [Access] at a top position reaches no caller borrow: none is lent there, `FrameStart`), or
the records of the frame's labels (the read's typed future: a caller's label is read by no top
position); what writes the caller's frames is [End] of a frame label (`semEnd`: in place it reads the
holder where the closure updates the cell, both `lowerVal`'s substitution; the extra update at a
non-parameter label is invisible, the caller's frames reading below the call's counter) and a call's
fixing of its consumed arguments (`callOf`'s `mapVals`, the same); a label issued is renamed by
`σ`'s fresh clause; a closure formed in the body means its body's runs from the extended states,
related again (the property on the subterm).

RESTATED (model3, 2026-11-21, docs/31 D113): the in-place state is good (`hg`), with the context and
the term's embedded values as the fundamental lemma asks (`hc`, `hv`), so that `Strict.fund_all` carries
it through every sub-run. As first stated it was false (`Strict/FrameCE.run_frame_false`): the strict
test after a write at a field path reads every position of the state, so in place it reads the
caller's frames, of which `FrameRel` says nothing; a caller binding holding `err` made the run in place
fail where the closure's ran. Also open about `FrameRel` (not restated here): its `held` clause asks the
parameters' records (`heldMem`) to agree, which fails at the call whenever a borrow argument was written
through before the call (in place the record is the content when the borrow was made, in the closure the
argument); nothing reads a parameter's record, so the clause should ask `heldMem` off the parameters
only, and `heldTy` at the parameters too (the strict ends read it). And the call's own frames differ at
`self` (in place the callee, in the closure the stage below), which the knot owes, not this lemma. -/
theorem run_frame (hc : Strict.FundCtx K) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (hs₀ : FrameStart s₀ ks)
    (tl : Bool) (hint : TyS) (t : Term) (hv : t.valsOk (Strict.ValsP K ρ φ)) (hid : t.idFree = true ∨ ks = [])
    (s s' : SState) (h : FrameRel σ s₀ ks s s') (hg : Strict.SGood K.dm K.Γ φ s) :
    FrameAgree σ s₀ ks (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s') := by
  sorry

/-- The caller's frames tell apart any two lists of whole members of the parameters' types (`Ts`): what
an `Id` observation in place needs (a place lent to a parameter reads its final content directly, or
through an earlier call's backward function, injective on members). -/
def CellsDetermined (s₀ : SState) (ks : List Nat) (Ts : List TyM) : Prop :=
  ∀ vs vs' : List Sem, vs.length = ks.length → vs'.length = ks.length →
    (∀ (i : Nat) v, vs[i]? = some v → v.whole ∧ v ∈ₛ[K.dm.read] Ts.getD i TyM.err) →
    (∀ (i : Nat) v, vs'[i]? = some v → v.whole ∧ v ∈ₛ[K.dm.read] Ts.getD i TyM.err) →
    (∀ p, p.frameOf < s₀.topIdx → ∀ ψ : Future, s₀.valAt p (ψ.updList (ks.zip vs)) = s₀.valAt p (ψ.updList (ks.zip vs'))) →
    vs = vs'

/-- At an observation, after a side's run in the closure's frame and every live borrow ended, each
cell holds a whole member of its parameter's type at the run's future. At an accepted program this
is the checker's: no borrow ends over a moved-out content (main's D98), and a typed body writes
members. -/
def CellsAtObs (Ts : List TyM) (s' : SState) : Prop :=
  ∀ (i : Nat) c, (cellsOf Ts.length (s'.liveLabels.foldl SState.endLabel s'))[i]? = some c →
    (c φ).whole ∧ c φ ∈ₛ[K.dm.read] Ts.getD i TyM.err

/-- **The frame property at an `Id`** (docs/31 D70; open). From related states, with each side's runs
related, the in-place observations of the two sides agree exactly when the closure's do, provided the
cells at both observations hold members (`CellsAtObs`) and the caller's frames tell members apart
(`CellsDetermined`): in place the observation reads the caller's frames, the closure the cells. -/
theorem run_frame_obs (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (hs₀ : FrameStart s₀ ks) (Ts : List TyM)
    (hdet : CellsDetermined K s₀ ks Ts) (s s' : SState) (h : FrameRel σ s₀ ks s s') (reps : List Place) (ws : List Sem)
    (r₁ r₂ r₁' r₂' : Res) (s₁ s₂ s₁' s₂' : SState)
    (h₁ : FrameAgree σ s₀ ks (some (r₁, s₁)) (some (r₁', s₁'))) (h₂ : FrameAgree σ s₀ ks (some (r₂, s₂)) (some (r₂', s₂')))
    (hm₁ : CellsAtObs K φ Ts s₁') (hm₂ : CellsAtObs K φ Ts s₂') :
    (observation φ reps ws s.positions r₁ s₁ = observation φ reps ws s.positions r₂ s₂) ↔
    (observation φ reps ws s'.positions r₁' s₁' = observation φ reps ws s'.positions r₂' s₂') := by
  sorry

end

end Ochr.Meaning

namespace Ochr.Meaning
open Ochr

section
variable (K : RunCtx) (ρ : Assignment)

/-- **The renaming lemma** (m2-proofs' D; was `Lemmas.run_counter_indep`, open). The run's result does
not depend on the starting label counter: fresh labels are names. Stated for the states code runs
from: one frame of future-free bindings whose types carry no label and no holder, compared on the
result's meaning and type. As first stated (any state whose holders are below both counters) it was
false, finding 7. It is the frame property's case with no caller frame and no parameter, the renaming
the shift from one counter to the other; it was proved from `run_frame` until that was restated with
the in-place state good (model3, docs/31 D113), which this case does not need (with no caller frame
there is nothing for the state-wide test to read that the closure's run does not read too), so it is
open again, with the same proof once the frame property's no-caller-frame case is. -/
theorem run_counter_indep (φ : Future) (hint : TyS) (t : Term) (bs : List SBinding) (n n' : Nat)
    (hbs : ∀ b ∈ bs, ∀ ψ ψ', b.val ψ = b.val ψ') (hlab : ∀ b ∈ bs, b.ty.label = none) :
    (run K ρ φ hint t (stateOf n bs)).map (fun r => (r.1.1, r.1.2.m))
      = (run K ρ φ hint t (stateOf n' bs)).map (fun r => (r.1.1, r.1.2.m)) := by
  sorry

end

end Ochr.Meaning
