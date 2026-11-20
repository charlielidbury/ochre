import Ochr.Meaning.CallRef
import Ochr.Meaning.Locality

/-!
# The frame property of the reference's run (docs/31 D62, D70)

The checker runs a known callee's body in place: its frame pushed on the caller's state. The
reference applies the callee's meaning, built from runs of the body in the closure's own frame: one
frame, each borrow parameter at a label of its own with a CELL, a temporary reading the label's final
content (`Run.lean`'s `.fix` clause, `bodyAt`). `callOf_inPlace` (`Steps/Call.lean`) says the two
agree; it rests on this file's frame property: a run of a term from a state whose top frame is a
callee's reads and writes only that frame, and reaches the caller's frames only through the labels the
frame holds, which the cells stand for.

The relation (`FrameRel s₀ ks s s'`), between an in-place state `s` and a closure state `s'`, for the
in-place state `s₀` at the call and the parameter labels `ks` (in cell order):
- the closure has one frame; in place, the caller's frames of `s₀` lie below the callee's;
- the top frames hold the same bindings; the closure's temporaries are the cells, then the in-place
  frame's temporaries, so an in-place top position `p` is the closure's `upPos c p`;
- the caller's frames keep their structure and their holders, and each reads what it read at the
  call, at the future that gives each parameter label its cell's value (`lowerVal`): the run ends a
  parameter's label in place where the closure updates its cell;
- shapes, sites at the top frame, records and the counter agree; the caller's borrows keep their
  sites. Sites of the frame's borrows in the caller's frames (a parameter's, and those [End] passes
  them to) are not compared: the closure has none, and nothing the run does reads them.

Labels are the same on both sides: the closure's labels are renamed to the in-place ones separately
(the counter lemma, `Lemmas.run_counter_indep`, generalised).

`Id` is excluded here (`Term.idFree`): its observation reads every position, so in place it reads the
caller's frames where the closure reads the cells, and the two agree only when the caller's frames
determine the cells, which needs the parameters' final contents at the observation to be members (a
returned borrow's lender reads its final content decoded, through the backward function). See
docs/31 D70.
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

/-- The frame a position is in. -/
def _root_.Ochr.Pos.frameOf : Pos → Nat
  | .bind f _ => f
  | .temp f _ => f

/-- Where an in-place top-frame position sits in the closure's frame: frame `0`, a temporary after
the `c` cells. -/
def upPos (c : Nat) : Pos → Pos
  | .bind _ i => .bind 0 i
  | .temp _ j => .temp 0 (j + c)

/-- The closure frame's first `c` temporaries: the cells. -/
def cellsOf (c : Nat) (s' : SState) : List SVal := ((s'.env.headD {}).temps).take c

/-- The future at which the caller's frames are read: each parameter label its cell's value. -/
def cellFuture (ks : List Nat) (cells : List SVal) (ψ : Future) : Future :=
  ψ.updList (ks.zip (cells.map (· ψ)))

/-- **The in-place state `s` and the closure's state `s'`, related** (docs/31 D70), for the in-place
state `s₀` at the call and its parameter labels `ks`, in cell order. -/
structure FrameRel (s₀ : SState) (ks : List Nat) (s s' : SState) : Prop where
  /-- in place, the caller's frames and the callee's; the closure, its frame alone -/
  frames : s.env.length = s₀.env.length ∧ s'.env.length = 1
  /-- the caller's frames keep their bindings' types and readings and their temporaries' number -/
  lowerSkel : ∀ f, f < s₀.topIdx →
    (s.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) =
    (s₀.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length))
  /-- and read what they read at the call, each parameter label at its cell -/
  lowerVal : ∀ p, p.frameOf < s₀.topIdx → ∀ ψ, s.valAt p ψ = s₀.valAt p (cellFuture ks (cellsOf ks.length s') ψ)
  /-- the caller's holders stay -/
  lowerShape : ∀ p, p.frameOf < s₀.topIdx → s.shape p = s₀.shape p
  /-- the same bindings in the top frame; the closure's temporaries are the cells, then the in-place ones -/
  top : ∃ F F', s.env.getLast? = some F ∧ s'.env = [F'] ∧ F'.binds = F.binds ∧
    F'.temps.length = ks.length + F.temps.length ∧ F'.temps.drop ks.length = F.temps
  /-- the same holders in the top frame; the cells hold nothing, and the closure nothing else -/
  topShape : ∀ p, p.frameOf = s₀.topIdx → s'.shape (upPos ks.length p) = s.shape p
  clShape : ∀ q l, s'.shape q = some l → ∃ p, p.frameOf = s₀.topIdx ∧ q = upPos ks.length p
  /-- the same counter -/
  next : s.nextLoan = s'.nextLoan
  /-- the same records for the frame's labels, and the same held types but for the parameters' (in
  place the caller's, in the closure none: a parameter's holder is a binding, typed by its type) -/
  held : ∀ l, s'.Live l → s.heldMem l = s'.heldMem l ∧ (l ∉ ks → s.heldTy l = s'.heldTy l)
  /-- the same sites in the top frame; the closure has no other -/
  lentTop : ∀ l (x : Site), x.pos.frameOf = s₀.topIdx →
    (x ∈ s.lent l ↔ { x with pos := upPos ks.length x.pos } ∈ s'.lent l)
  lentCl : ∀ l (x : Site), x ∈ s'.lent l → ∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p
  /-- the caller's borrows keep their sites -/
  lentCaller : ∀ l p, p.frameOf < s₀.topIdx → s₀.shape p = some l → s.lent l = s₀.lent l
  /-- the frame's labels are the parameters' or the run's own (at or above the counter at the call) -/
  topLabels : ∀ l, s'.Live l → l ∈ ks ∨ s₀.nextLoan ≤ l

/-- What the in-place state at the call must be for the relation to start: the caller's frames read
no label at or above the counter (nothing the callee makes), the parameter labels are below it and
held in the top frame, and the caller holds none of them. -/
structure FrameStart (s₀ : SState) (ks : List Nat) : Prop where
  reads : ∀ p, p.frameOf < s₀.topIdx → ∀ ψ ψ', (∀ l, l < s₀.nextLoan → ψ l = ψ' l) → s₀.valAt p ψ = s₀.valAt p ψ'
  ks_lt : ∀ k ∈ ks, k < s₀.nextLoan
  callerHeld : ∀ p l, p.frameOf < s₀.topIdx → s₀.shape p = some l → l ∉ ks ∧ l < s₀.nextLoan
  ks_nodup : ks.Nodup

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The frame property of the reference's run** (docs/31 D62, D70; open). From related states an
`Id`-free term runs to related states with the same result, or fails on both sides. Proved by
induction on the term, a simulation of the two runs clause by clause: what reads a state reads the
top frame (`resolve`, `scopeOf`, `movedPlaces`), the shapes and the sites at the top frame (an
[Access] at a top position reaches no caller borrow: none is lent there), or the records of the
frame's labels (the read's typed future); what writes the caller's frames is [End] of a frame's
label (`semEnd`, which in place reads the label's holder where the closure updates the cell; both
are `lowerVal`'s substitution) and a call's fixing of its consumed arguments (`callOf`'s `mapVals`,
the same substitution); a closure formed in the body means its body's runs from the extended states,
related again (the property itself, on the subterm). -/
theorem run_frame (s₀ : SState) (ks : List Nat) (hs₀ : FrameStart s₀ ks) (tl : Bool) (hint : TyS) (t : Term)
    (hid : t.idFree = true) (s s' : SState) (h : FrameRel s₀ ks s s') :
    match runT K ρ φ tl hint t s, runT K ρ φ tl hint t s' with
    | some (r, s₁), some (r', s₁') => r = r' ∧ FrameRel s₀ ks s₁ s₁'
    | none, none => True
    | _, _ => False := by
  sorry

end

end Ochr.Meaning
