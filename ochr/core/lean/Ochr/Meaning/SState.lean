import Ochr.Meaning.State
import Ochr.Meaning.Pi

/-!
# The semantic state the reference run acts on (docs/18 Def. "reference run", docs/27 §5)

The reference run is a state transformer on *meanings*: it never sees a `Value`. Its state is
the checker's `Env` with each position holding a meaning as a function of the future (`SVal`),
each binding its declared type as a `TyM`, the shape (which positions hold a borrow of which
label), and a label counter for fresh borrows. `MState.sstate` reads a checker state into one;
`SState.toMean` forgets the types.

[Access] on this state ends exactly the borrows the accessed position's meaning depends on
(`SState.access`), in label order; that the order does not matter is a lemma of the skeleton
(WF3). [End] is `Mean.semEnd` lifted (`SState.endLabel`).
-/

namespace Ochr.Meaning

/-- A meaning as a function of the future. -/
abbrev SVal : Type 3 := Future → Sem

/-- A semantic binding: its declared type, its meaning, and, for a function's binding of itself
(D78), the recursion it may make: the decreasing parameter and the rank its argument must stay
below (docs/24 §4, guarded recursion: a call that does not decrease means the error value). -/
structure SBinding : Type 3 where
  ty : TyS
  val : SVal
  /-- its declared-type reading (`Binding.decl`), an input of the aligned decisions -/
  decl : DeclInfo := .other
  recBound : Option (Nat × Nat) := none

structure SFrame : Type 3 where
  binds : List SBinding := []
  temps : List SVal := []

structure SState : Type 3 where
  env : List SFrame
  shape : Pos → Option Nat
  nextLoan : Nat

namespace SState

def valAt (s : SState) : Pos → SVal
  | .bind f i => match s.env[f]?.bind (·.binds[i]?) with
    | some b => b.val
    | none => fun _ => .err
  | .temp f i => match s.env[f]?.bind (·.temps[i]?) with
    | some v => v
    | none => fun _ => .err

def tyAt (s : SState) : Pos → TyS
  | .bind f i => match s.env[f]?.bind (·.binds[i]?) with
    | some b => b.ty
    | none => .plain .err
  | .temp _ _ => .plain .err

def setAt (s : SState) (p : Pos) (v : SVal) : SState :=
  match p with
  | .bind f i => { s with env := s.env.modify f fun fr =>
      { fr with binds := fr.binds.modify i fun b => { b with val := v } } }
  | .temp f i => { s with env := s.env.modify f fun fr => { fr with temps := fr.temps.set i v } }

def positions (s : SState) : List Pos := Id.run do
  let mut out := #[]
  for h : f in [0:s.env.length] do
    let fr := s.env[f]
    for i in [0:fr.binds.length] do out := out.push (Pos.bind f i)
    for i in [0:fr.temps.length] do out := out.push (Pos.temp f i)
  pure out.toList

/-- Forget the types: the state as a `Mean`. -/
def toMean (s : SState) : Mean := ⟨s.positions, fun φ p => s.valAt p φ, s.shape⟩

/-- The meaning at `p` depends on label `l` (`Mean.dependsOn`). -/
def dependsOn (s : SState) (p : Pos) (l : Nat) : Prop := s.toMean.dependsOn p l

/-- Replace every position's meaning. -/
def mapVals (s : SState) (f : Pos → SVal → SVal) : SState :=
  { s with env := s.env.zipIdx.map fun (fr, fi) =>
      { binds := fr.binds.zipIdx.map fun (b, i) => { b with val := f (.bind fi i) b.val },
        temps := fr.temps.zipIdx.map fun (v, i) => f (.temp fi i) v } }

/-- [End l] (docs/27 Def. 4): the holder `r` of `l` is forgotten and every meaning reads `l`'s
final content as what `r` holds now. A label held nowhere is inert: nothing happens. -/
noncomputable def endLabel (s : SState) (l : Nat) : SState :=
  open Classical in
  match (s.positions.find? fun p => decide (s.shape p = some l)) with
  | some r =>
    let m := s.toMean.semEnd r l
    ({ s with shape := m.shape }).mapVals fun p _ => (m.val · p)
  | none => s

/-- The live labels, in label order. -/
def liveLabels (s : SState) : List Nat :=
  (s.positions.filterMap s.shape).mergeSort (· ≤ ·)

/-- [Access] of `p` for the reference run: end, in label order, every live borrow whose final
content the meaning at `p` depends on, and nothing else (docs/27 §5). Ending a borrow may make
`p` depend on another (a reborrow's loan travels back), so this is iterated as many times as
there are live labels. -/
noncomputable def access (s : SState) (p : Pos) : SState :=
  open Classical in
  let step (s : SState) : SState :=
    (s.liveLabels.filter fun l => decide (s.dependsOn p l)).foldl endLabel s
  (List.range s.liveLabels.length).foldl (fun s _ => step s) s

/-- The top frame's index. -/
def topIdx (s : SState) : Nat := s.env.length - 1

/-- De Bruijn variable `i` of the top frame, as a position. -/
def varPos (s : SState) (i : Nat) : Option Pos :=
  match s.env.getLast? with
  | some fr => if i < fr.binds.length then some (.bind s.topIdx (fr.binds.length - 1 - i)) else none
  | none => none

def pushFrame (s : SState) : SState := { s with env := s.env ++ [{}] }

def pushBind (s : SState) (b : SBinding) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with binds := fr.binds ++ [b] } }

def pushTemp (s : SState) (v : SVal) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with temps := fr.temps ++ [v] } }

def freshLoan (s : SState) : Nat × SState := (s.nextLoan, { s with nextLoan := s.nextLoan + 1 })

/-- The position holding the borrow of label `l`, if any. -/
noncomputable def holderOf (s : SState) (l : Nat) : Option Pos :=
  open Classical in s.positions.find? fun p => decide (s.shape p = some l)

/-- Take the holder of `l` away (the borrow moves elsewhere): the old holder is forgotten and no
longer in the shape. The caller records the new holder. -/
noncomputable def takeLabel (s : SState) (l : Nat) : SState :=
  match s.holderOf l with
  | some r => { (s.setAt r fun _ => .moved) with shape := fun p => if p = r then none else s.shape p }
  | none => s

/-- Park a borrow in a fresh temporary of the top frame, which becomes its holder (D14: a label
always has a holder, from its creation to its end). -/
noncomputable def pushTempShaped (s : SState) (v : SVal) (l : Nat) : SState :=
  let s' := s.pushTemp v
  match s'.env.getLast? with
  | some fr => { s' with shape := fun p => if p = .temp s'.topIdx (fr.temps.length - 1) then some l else s'.shape p }
  | none => s'

/-- The state's closed future: `φ` with every live label fixed to its holder's current content,
iterated as `access` iterates (a holder may itself read a live label). A read that skips
[Access] reads at it, so it depends on `φ` only at labels the state does not hold (D14). -/
noncomputable def closedFuture (s : SState) (φ : Future) : Future :=
  (List.range s.liveLabels.length).foldl (fun ψ _ =>
    s.liveLabels.foldl (fun ψ l =>
      match s.holderOf l with
      | some r => ψ.upd l (s.valAt r ψ)
      | none => ψ) ψ) φ

/-- Drop the last binding of the top frame ([Let]'s drop; its borrows, if any, are ended by the
reads that depend on them). -/
def dropLast (s : SState) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with binds := fr.binds.dropLast } }

end SState

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- The checker's state read as a semantic state: each binding's value as a function of the
future at its stored type, each temporary's, the shape, and the label counter. A binding of a
function of itself carries no recursion mark here (the checker's `RecCtx` is a check's input);
the reference run sets it when it pushes a frame. -/
noncomputable def _root_.Ochr.MState.sstate (ρ : Assignment) (st : MState) : SState :=
  { env := st.env.toList.zipIdx.map fun (fr, f) =>
      { binds := fr.binds.toList.zipIdx.map fun (b, i) =>
          { ty := Env.hintAt dm C Γ ρ st.env (.bind f i), val := fun φ => Env.mean dm C Γ ρ φ st.env (.bind f i),
            decl := b.decl },
        temps := fr.temps.toList.zipIdx.map fun (_, i) => fun φ => Env.mean dm C Γ ρ φ st.env (.temp f i) },
    shape := Env.shape st.env,
    nextLoan := st.nextLoan }

end

end Ochr.Meaning
