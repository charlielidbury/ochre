import Ochr.Meaning.Places
import Ochr.Meaning.Apply1

/-!
# The reference run (docs/18 Def. "reference run", the meaning of code [Q2]; docs/31 D9, D10)

`run K ρ φ hint t` is the meaning of running `t` **at the future `φ`**: a state transformer on
`SState`s returning the result's meaning at `φ` with its type (`Res := Sem × TyS`), or `none`
where the run goes wrong. It follows the machine's rules except four (docs/18): every call
applies the callee's meaning and never runs its body; before a place is read, borrowed or
matched it ends exactly the borrows the place's meaning depends on (`SState.access`); a match
on data reads the tag of the scrutinee's meaning, so nothing is stuck and nothing is split (a
match on a *free* hole, an inert loan read from `φ`, picks its arm at `φ`); `Id`, `Eq` and `J`
mean as in the model, and statements run on a copy that is thrown away (`SM.stmtIf`, at the
aligned decision `Decisions.flags` of each term whose clause can change the state: D19).

**Per-future (D10).** A position's meaning is an `SVal`, a function of the future, so that the
borrows the run itself creates can be ended (`endLabel` = `Mean.semEnd`, fixing the future at
their labels); every *read* evaluates at the ambient `φ`, so a free label (a sealed program's
hole, an inert loan) means `φ l`. The meaning of a configuration `(Ω, t)` is then the function
`fun φ => run … φ … t (Ω's sstate)`: result and state at `φ`. The run records the labels it
makes in `shape` at the position that comes to hold the borrow (a `let`'s binding, a call's
argument slot), so `access` can end them.

Structurally recursive on the term: the only recursion into code is into subterms (a `let`'s
parts, a match's arms, a Π's or closure's domain and body terms, `mkTele`). A call applies a
meaning (`applyTele`). Recursive functions mean their guarded fixpoint by stages (docs/24 §4;
the `.fix` clause). `meanV` is `Value.mean` with the code-dependent forms given by the run
(the knot, `codeMeaning`).
-/

namespace Ochr.Meaning

open Classical

/-- The run's monad: a state transformer that may fail. -/
abbrev SM (α : Type 3) : Type 3 := SState → Option (α × SState)

instance : Monad SM where
  pure a := fun s => some (a, s)
  bind x f := fun s => match x s with
    | some (a, s') => f a s'
    | none => none

def SM.fail {α : Type 3} : SM α := fun _ => none
def SM.get : SM SState := fun s => some (s, s)
def SM.set (s : SState) : SM PUnit := fun _ => some (⟨⟩, s)
def SM.modify (f : SState → SState) : SM PUnit := fun s => some (⟨⟩, f s)

/-- Run `x` on a copy of the state and discard the copy (a statement position, E1). -/
def SM.onCopy {α : Type 3} (x : SM α) : SM α := fun s => (x s).map fun (a, _) => (a, s)

/-- A statement position (docs/18 Def. "reference run": statements run on a copy that is thrown
away; `Machine.evalAt`'s and `stmtArgIf`'s `inStatement`): when `b`, `x` runs on a copy of the
state, which is discarded, and its result names no borrow (a borrow it made is the copy's). Every
clause of `run` that can change the state or return a label runs under it, at the aligned
decision `Decisions.flags` of its own term (D19, R1: the run used to ask `flags` only of calls, so
a proof-valued `let` moved its places for real). -/
def SM.stmtIf (b : Bool) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  if b then (x s).map fun r => ((r.1.1, { r.1.2 with label := none }), s) else x s

theorem SM.stmtIf_congr {b : Bool} {x x' : SM (Sem × TyS)} {s : SState} (h : x s = x' s) :
    SM.stmtIf b x s = SM.stmtIf b x' s := by
  simp only [SM.stmtIf, h]

/-- A statement's run, taken apart: not a statement and the run itself, or a statement, the state
unchanged and the result label-free. -/
theorem SM.stmtIf_some {b : Bool} {x : SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (h : SM.stmtIf b x s = some (r, s')) :
    (b = false ∧ x s = some (r, s')) ∨
    (b = true ∧ s' = s ∧ r.2.label = none ∧ ∃ r₀ s₀, x s = some (r₀, s₀) ∧ r = (r₀.1, { r₀.2 with label := none })) := by
  cases b with
  | false => exact .inl ⟨rfl, h⟩
  | true =>
    simp only [SM.stmtIf, if_true] at h
    cases hx : x s with
    | none => rw [hx] at h; cases h
    | some rs =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨rfl, rfl, rfl, rs.1, rs.2, rfl, rfl⟩

/-- An erased term (`Machine.evalAt`): a proof is not run, its value is `⋆` (docs/18: every proof
is `⋆`, and no step reads a statement's value otherwise; the audit's A3: a match on a proof of a
proposition with two constructors, into a proposition, has no arm to run); any other statement
(a type) runs on a copy (`SM.stmtIf`). `fl` is the aligned decision `Decisions.flags` of the term:
(erased, proof). -/
def SM.erasedIf (fl : Bool × Bool) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  if fl.2 then some ((.proof, .plain .err), s) else SM.stmtIf fl.1 x s

theorem SM.erasedIf_congr {fl : Bool × Bool} {x x' : SM (Sem × TyS)} {s : SState} (h : x s = x' s) :
    SM.erasedIf fl x s = SM.erasedIf fl x' s := by
  simp only [SM.erasedIf, SM.stmtIf, h]

/-- An erased term's run, taken apart: the run itself, or the state unchanged and the result
label-free. -/
theorem SM.erasedIf_some {fl : Bool × Bool} {x : SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (h : SM.erasedIf fl x s = some (r, s')) : x s = some (r, s') ∨ (s' = s ∧ r.2.label = none) := by
  unfold SM.erasedIf at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl⟩
  · rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, e, hl, -⟩
    · exact .inl h
    · exact .inr ⟨e, hl⟩

/-- A term read as a call reads its head, and as `clone`, `peek` and `inplace` read their
operand: a place in place (`rd`: not consumed, D53 (e)), anything else by its run (`rn`). -/
def SM.headOf (f : Term) (rd : Place → SM (Sem × TyS)) (rn : SM (Sem × TyS)) : SM (Sem × TyS) :=
  match f with
  | .place p => rd p
  | _ => rn

theorem SM.headOf_some {f : Term} {rd : Place → SM (Sem × TyS)} {rn : SM (Sem × TyS)} {s s' : SState}
    {r : Sem × TyS} (h : SM.headOf f rd rn s = some (r, s')) :
    (∃ p, rd p s = some (r, s')) ∨ rn s = some (r, s') := by
  cases f <;> first | exact .inr h | exact .inl ⟨_, h⟩

theorem SM.headOf_congr {f : Term} {rd rd' : Place → SM (Sem × TyS)} {rn rn' : SM (Sem × TyS)} {s : SState}
    (h1 : ∀ p, rd p s = rd' p s) (h2 : rn s = rn' s) : SM.headOf f rd rn s = SM.headOf f rd' rn' s := by
  cases f <;> first | exact h2 | exact h1 _

/-- The context of a run: the data model, the declarations, the meanings of the globals and the
decisions read from syntax. -/
structure RunCtx : Type 3 where
  dm : DataModel
  Γ : List IndDecl
  C : CodeMeaning
  D : Decisions
  /-- the types of the abstract values (Δ) as the run knows them, with Π-shapes: a call through
  an abstract function `σ_f` applies `ρ σ_f` along the shape of `Δ(σ_f)`. Fixed per checker
  state (`DeltaOk`): the reference run creates no unknowns. -/
  Δ : Nat → TyS := fun _ => .plain .err
  /-- the declared types of the loans as the run knows them (P1, PROPOSAL m2-proofs): a borrowed
  function value (`&f`) is real, so an embedded `loan_ℓ` carries the Π-shape of its position's
  declared type (by (WF9) every loan outside a sealed program sits at a typed position), as the
  value that fills it will. A loan with no shape here reads as the hint (data). -/
  Λ : Nat → TyS := fun _ => .plain .err

/-- A result: the meaning at the run's future, with its type. -/
abbrev Res : Type 3 := Sem × TyS

/-- The future updated at several labels. -/
def Future.updList (φ : Future) : List (Nat × Sem) → Future
  | [] => φ
  | (l, e) :: rest => (φ.upd l e).updList rest

/-- The empty state with one empty frame and the label counter at `n` (a sealed program's run
starts above its own loans). -/
def emptyState (n : Nat) : SState := { env := [{}], shape := fun _ => none, nextLoan := n }

/-- The state with one frame holding the given bindings (a closure's code runs in it). -/
def stateOf (n : Nat) (bs : List SBinding) : SState :=
  { env := [{ binds := bs }], shape := fun _ => none, nextLoan := n }

/-- A closure's frame: its captured values at their recorded types. -/
def capsState (vs : List Sem) (tys : List (DeclInfo × TyS)) : List SBinding :=
  (vs.zip tys).map fun (v, (d, T)) => { ty := T, val := fun _ => v, decl := d }

/-- The declared-type readings of the top frame, innermost first (`Decide.placeDecl`'s scope). -/
def scopeOf (s : SState) : List DeclInfo :=
  match s.env.getLast? with
  | some fr => (fr.binds.map (·.decl)).reverse
  | none => []

/-- A parameter as a frame binds it: its type, with its Π-shape, as a function of the earlier
arguments, and its declared reading (D19, R6: `PiParam` carries the type as a `TyM` only, so a
function parameter was bound at a type with no shape and could not be called). -/
abbrev PBind : Type 3 := (List Sem → TyS) × DeclInfo

/-- The bindings `extendBy` pushes: argument `i` at parameter `i`'s type at the earlier arguments
and at its declared reading (`.plain .err` and `other` beyond `bs`). -/
def extendBinds (bs : List PBind) (acc : List Sem) : List SBinding :=
  acc.zipIdx.map fun ai =>
    { ty := match bs[ai.2]? with | some b => { b.1 (acc.take ai.2) with label := none } | none => .plain .err, val := fun _ => ai.1, decl := match bs[ai.2]? with | some b => b.2 | none => .other }

/-- The state's top frame extended by bindings holding the given meanings (a Π's or a closure's
parameters at formation), each at its parameter's type and reading (`bs`): a later domain term or
the codomain may call an earlier parameter, and reads its declared type for copy or move. -/
def extendBy (s : SState) (bs : List PBind) (acc : List Sem) : SState :=
  (extendBinds bs acc).foldl (fun s b => s.pushBind b) s

/-- A parameter's binder from the run of its domain term at each prefix of arguments (`r`): the
type's meaning with the Π-shape the run returns, and the reading `dcs` gives parameter
`pre.length`. -/
def mkBind (dcs : List DeclInfo) (pre : List PBind) (r : List Sem → Option ((Sem × TyS) × SState)) : PBind :=
  (fun acc => match r acc with
    | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
    | none => .plain .err, dcs.getD pre.length .other)

/-- A domain term `&A`: a borrow parameter. -/
def _root_.Ochr.Term.isRefTy : Term → Bool
  | .ref _ => true
  | _ => false

/-- The parameters of a Π-term as `PiParam`s, from their binders and domain terms: `&A` marks a
borrow parameter; the type is the binder's, without its shape. -/
def psOf : List PBind → List Term → List PiParam
  | b :: bs, d :: ds => ⟨d.isRefTy, fun acc => (b.1 acc).m, fun acc => (b.1 acc).data⟩ :: psOf bs ds
  | _, _ => []

/-- Fill parameter variable `j` (of `np`) of a constructor's solution, if it is not solved yet
(`Machine.unifyParams`' variable case: in a field's type, parameter `i` is `var (np - 1 - i)`). -/
def fillParam (np j : Nat) (v : Sem) (sol : List (Option Sem)) : List (Option Sem) :=
  if j < np ∧ (sol.getD (np - 1 - j) none).isNone then sol.set (np - 1 - j) (some v) else sol

/-- Infer a constructor's unwritten parameters from a field's declared type term `FT` and the
type `R` the field's run returned (`Machine.unifyParams`, D46; the audit's A9): where `FT` is a
parameter variable, the parameter is `R` itself; where it is `D(x̄)` and `R` records its data
`D(v̄)`, each parameter variable among `x̄` is its `v`. Only unsolved parameters are filled. A
type the run does not know (`err`: an untyped proof) solves nothing, as the checker's field with
no type. Not covered: a parameter nested deeper (`List(Pair(A, B))`), and a field whose run loses
its data (a call's result, a field read: the audit's A11, A12). -/
def unifyTyS (np : Nat) (FT : Term) (R : TyS) (sol : List (Option Sem)) : List (Option Sem) :=
  match R.m with
  | .err => sol
  | _ =>
    match FT with
    | .place (.var j) => fillParam np j (.ty R.m) sol
    | .tind m as =>
      match R.data with
      | some (m', vs) =>
        if m = m' ∧ as.length = vs.length then
          (as.zip vs).foldl (fun sol av => match av.1 with
            | .place (.var j) => fillParam np j av.2 sol
            | _ => sol) sol
        else sol
      | none => sol
    | _ => sol

/-- A solution read as parameters: an unsolved one is `err` (read by no field type that is asked). -/
def solved (sol : List (Option Sem)) : List Sem := sol.map fun o => o.getD .err

/-- Field `i` of constructor `c`: its declared type term. -/
def fieldTerm (d : IndDecl) (c i : Nat) : Option Term :=
  ((d.ctors[c]?).bind (·.2[i]?)).map (·.2)

/-- Resolve a place to its root position and path. -/
def resolve (s : SState) (p : Place) : Option (Pos × List Step) :=
  let (i, steps) := p.steps
  (s.varPos i).map (·, steps)

/-- Push a binding, recording in the shape the borrow label its type carries (the binding
holds that borrow). -/
noncomputable def pushBindShaped (s : SState) (b : SBinding) : SState :=
  match b.ty.label with
  | some l =>
    let s := s.takeLabel l
    let s' := s.pushBind b
    match s'.env.getLast? with
    | some fr => { s' with shape := fun p => if p = .bind s'.topIdx (fr.binds.length - 1) then some l else s'.shape p }
    | none => s'
  | none => s.pushBind b

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The top frame's variables holding `⊥` at the run's future (D84's `entry` set of a match). -/
noncomputable def movedPlaces (s : SState) : List Place :=
  match s.env.getLast? with
  | some fr => (List.range fr.binds.length).filterMap fun i =>
      match s.varPos i with
      | some pos => if s.valAt pos (s.closedFuture φ) = .moved then some (.var i) else none
      | none => none
  | none => []

/-- The content of a place after [Access]: its meaning at `φ` (the labels it depended on that
the run holds have been ended; what remains is read from `φ`) and its type. A projected field's
type carries no data component (`Sem.follow` yields a `TyM`): a documented gap for nested
`ps = []` values under projections. -/
noncomputable def contentOf (p : Place) : SM (Sem × TyS × Pos × List Step) := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let s := s.access pos
    match Sem.follow K.dm K.Γ (s.tyAt pos).m (s.valAt pos φ) steps with
    | some (v, T) => some ((v, if steps.isEmpty then s.tyAt pos else .plain T, pos, steps), s)
    | none => none
  | none => none

/-- Set the content of a place to a constant meaning, pointwise in the future (no access: the
caller has done it). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  let T := (s.tyAt pos).m
  let old := s.valAt pos
  match Sem.updAt K.dm K.Γ T (fun _ => v) steps (old (s.closedFuture φ)) with
  | some _ => some (⟨⟩, s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => v) steps (old φ')).getD .err)
  | none => none

/-- [Read]: the content; a copy leaves the place, a move leaves `moved` (D80: by the declared
reading). Reading `⊥`, or a value holding it, is an error. -/
noncomputable def readPlace (p : Place) (copy : Bool) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  -- PROPOSAL (m2-proofs): a copy carries no holdership: the place's stored type may name a label
  -- it held when bound (or no longer holds); only a move carries the label it holds now
  if copy then some ((v, { T with label := none }), s) else do
    -- a move of a whole position holding a borrow carries the borrow: the position is no
    -- longer its holder; the borrow is parked in a temporary, which holds it until the result
    -- is bound (D14), and the result's type names the label
    let lab := if steps.isEmpty then s.shape pos else none
    let (⟨⟩, s) ← setContent K φ pos steps .moved s
    let s := match lab with
      | some l => (s.takeLabel l).pushTempShaped (fun _ => v) l
      | none => s
    some ((v, { T with label := lab }), s)

/-- [Borrow] `&p` with a fresh label `l`: the place now reads `l`'s final content at its path, and
the result is the old content, whole, with the label in its type (the holder's position records
it in the shape when the result is bound). -/
noncomputable def borrowPlace (p : Place) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  let (l, s) := s.freshLoan
  let T0 := (s.tyAt pos).m
  let old := s.valAt pos
  let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
  -- the borrow is parked in a temporary, its holder until it is bound (D14)
  let s := s.pushTempShaped (fun _ => v) l
  some ((v, { T with label := some l }), s)

/-- A call at level `L` (`Apply1.lean`): unpack the callee at its carrier and apply it along its
shape (`applyFnL`); otherwise as `callOf`. -/
noncomputable def callOfL.{u} (L : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res) :
    SM Res := fun s =>
  let argSems := args.map (·.1)
  -- PROPOSAL (m2-proofs, CE4): the arguments at borrow parameters, in parameter order, one per
  -- final content; only their labels are consumed and fixed. A labelled argument at a non-borrow
  -- parameter keeps its holder (parked), so the next access ends it.
  let refLabels : List (Option Nat) := ((args.zip ps).filter (·.2.isRef)).map (·.1.2.label)
  let fixes (fs : List Sem) : List (Nat × Sem) := (refLabels.zip fs).filterMap fun (l?, f) => l?.map (·, f)
  -- the borrow arguments' holders (parked temporaries) are consumed by the call
  let s := (refLabels.filterMap id).foldl SState.takeLabel s
  match applyFnL L ps out fv argSems with
  | some (.data r finals) =>
    let s := s.mapVals fun _ v φ' => v (φ'.updList (fixes finals))
    let B := match out with | .data B => B argSems | .ref U => U argSems
    some ((r, .plain B), s)
  | some (.ref U fwd back) =>
    let (k, s) := s.freshLoan
    let s := s.mapVals fun _ v φ' =>
      match L.dec U (φ' k) with
      | some x => v (φ'.updList (fixes (back x)))
      | none => .err
    let s := s.pushTempShaped (fun _ => L.enc U fwd) k
    some ((L.enc U fwd, ⟨U, none, some k, none⟩), s)
  | none => none

/-- A call, on the evaluated callee and arguments (docs/18 Def. "reference run", first clause):
apply the callee's meaning along its shape. For a borrow-free result each lent place's final
content is fixed to its component of the finals (the future at the argument's label); for a
result `&U`, a fresh label `k`, the result holds the forward value, and each lent place reads
its component of the backward function at the final content of `k`. A callee without a shape,
or an ill-typed application, is an error. The guard of a recursive call and a statement call's
copy are the caller's (`run`'s `.call` clause). The callee's level is read off its tag
(`Apply1.lean`: one construction for `Type₀`, `Type₁`, `Type₂`). -/
noncomputable def callOf (fv : Res) (args : List Res) : SM Res := fun s =>
  match fv.2.shape with
  | some (ps, out) =>
    match fv.1 with
    | .el0 .. => callOfL lvl0 ps out fv.1 args s
    | .el1 .. => callOfL lvl1 ps out fv.1 args s
    | .el2 .. => callOfL lvl2 ps out fv.1 args s
    | _ => none
  | none => none

/-- D84, the drop at the join, as `Machine.dropAtJoin` does it (mono-lemmas' review): every place
some arm of the match moves (`Decisions.joinMoves`, static, given the places already moved at
entry) is accessed, then set to `moved`; a place whose declared reading is copy, a proof, or a
place already `⊥` is left alone; a borrow held at a dropped root ends (`endLabel`). `entry` is
the set of places already moved when the match STARTED (`Machine.joinDrop` reads `staticJoin`
before the arm runs: the audit's A6; read after it, a place moved before the match and refilled by
the arm taken would not be dropped, though the join says it is moved). At a root
this is below the state before; at a field place it is a real change, so the match step lemma
is stated exact against the checker's drop, not below its input. -/
noncomputable def joinDrop (entry : List Place) (t : Term) (s : SState) : SState :=
  (K.D.joinMoves (scopeOf s) entry t).foldl (fun s q =>
    if K.D.copy (K.D.placeDecl (scopeOf s) q) then s else
    match resolve s q with
    | some (pos, steps) =>
      let s := s.access pos
      match Sem.follow K.dm K.Γ (s.tyAt pos).m (s.valAt pos (s.closedFuture φ)) steps with
      | some (.proof, _) | some (.moved, _) | none => s
      | some _ =>
        let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
        let T := (s.tyAt pos).m
        let old := s.valAt pos
        s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => .moved) steps (old φ')).getD .err
    | none => s) s

/-- An observation for `Id` (docs/27 Def. 5, D84 [Obs-ref]): after the side's run, each borrow
binding the side re-points (`rePointed`, static) has a fresh value written through it, the
`i`-th of `ws` for the `i`-th re-pointed binding, so that where it points is observed through
its owners; then every live borrow of the copy ends, and the result and the meaning of every
position that was there when the side STARTED (`ps₀`) are read at the run's future (the audit's
A5: read at every position of the side's end state, two sides that park different numbers of
temporaries, one borrowing and the other not, were never equal). A fresh abstract value under every assignment is every
value, so `Id` quantifies over `ws` (`run`'s `.id` clause). -/
noncomputable def observation (reps : List Place) (ws : List Sem) (ps₀ : List Pos) (r : Res) (s : SState) : List Sem :=
  let s := (reps.zipIdx).foldl (fun s (q, i) =>
    match resolve s q, ws[i]? with
    | some (pos, []), some w => s.setAt pos fun _ => w
    | _, _ => s) s
  let s := s.liveLabels.foldl SState.endLabel s
  r.1 :: ps₀.map fun p => s.valAt p φ

/-- The shape of a Π-term: its parameters' and output's meanings as functions of the earlier
parameters, read in a state. Used by `.pi`, `.fix`, `.val` of a closure, and `codeMeaning`. -/
structure PiShape : Type 3 where
  ps : List PiParam
  out : PiOut

mutual
/-- The reference run of a term at the future `φ`, at the type `hint` its context expects. -/
noncomputable def run (hint : TyS) : Term → SM Res
  | .place p => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.place p))
      (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s
  | .borrow p => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.borrow p)) (borrowPlace K φ p) s
  | .assign p u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.assign p u)) (fun s => do
    -- the right-hand side runs BEFORE the place is accessed (`evalCore`'s `.assign`, then
    -- `assignPlace`; D19, R5: accessing first ended the borrows the right-hand side reads
    -- through, `y := clone(*r)` with `r` borrowing `y`). The place's type, the hint of the
    -- right-hand side, is read on a discarded copy
    let T : TyS := match contentOf K φ p s with
      | some ((_, T, _, _), _) => T
      | none => .plain .err
    let ((v, R), s) ← run T u s
    match resolve s p with
    | none => none
    | some (pos, steps) =>
      -- [Access] before the write is of the part the place OWNS (D67, `accessInside … owned`): a
      -- borrow variable assigned whole owns nothing of its content, so nothing its content
      -- lends is ended (the audit's A2: `c := &(*c).tail` keeps the reborrow it just made); the
      -- old borrow's end carries its content, loans and all, back to its lender
      let s := if steps.isEmpty && (s.shape pos).isSome then s else s.access pos
      -- the old content's borrow, if the place held one, ends ([Drop]); a borrow written at a
      -- root makes the place its holder (WF1: a borrow is the whole value of a position)
      let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
      match setContent K φ pos steps v s with
      | none => none
      | some (⟨⟩, s) =>
        let s := match R.label, steps with
          | some l, [] => let s := s.takeLabel l; { s with shape := fun q => if q = pos then some l else s.shape q }
          | _, _ => s
        some ((.el0 Unit (), .plain (.ty0 Unit)), s)) s
  | .letIn x u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.letIn x u w)) (fun s => do
    let ((v, T), s) ← run (.plain .err) u s
    let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← run hint w s
    -- [Drop] of the binding: the borrow it holds *now* ends, then it is forgotten (PROPOSAL,
    -- m2-proofs, CE5: not the label its type carried when it was bound, which it may have moved
    -- out, while an assignment may have made it the holder of another)
    let held : Option Nat := match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none
    let s := match held with | some l => s.endLabel l | none => s
    some ((r, R), s.dropLast)) s
  | .seq u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.seq u w)) (do
    -- a discarded result holding a borrow stays parked in its temporary (D14): the borrow is
    -- ended by the access that next depends on it, or by the frame's pop
    let _ ← run (.plain .err) u
    run hint w) s
  | .matchNat p z u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchNat p z u)) (fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access]); `⊥` is an error;
    -- then D84's drop at the join
    let ((v, _, _, _), s) ← contentOf K φ p s
    let entry := movedPlaces φ s
    let arm? : Option Bool := match v.asNat with
      | some 0 => some true
      | some (_ + 1) => some false
      | none => match v with
        | .ctor "Nat" 0 [] => some true
        | .ctor "Nat" 1 _ => some false
        | _ => none
    match arm? with
    | some true => do
      let ((r, R), s) ← run hint z s
      some ((r, R), joinDrop K φ entry (.matchNat p z u) s)
    | some false => do
      let ((r, R), s) ← run hint u s
      some ((r, R), joinDrop K φ entry (.matchNat p z u) s)
    | none => none) s
  | .matchInd p n arms => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchInd p n arms)) (fun s => do
    let ((v, T, _, _), s) ← contentOf K φ p s
    let entry := movedPlaces φ s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match v with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => match T.m.dataOf K.dm K.Γ with
        | some (d, ps) => (K.dm.fieldsOf d ps v).map (·.1)
        | none => none
    match c? with
    | some c => do
      let ((r, R), s) ← runArm hint c arms s
      -- a match on a proof has no join (`Machine.evalMatchByType`: its one arm runs on every
      -- path; the audit's A4)
      some ((r, R), match v with | .proof => s | _ => joinDrop K φ entry (.matchInd p n arms) s)
    | none => none) s
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      -- the type value's own type carries the structure of the type it denotes, as a Π-term's
      -- does its shape: here the declaration and its parameters (read by an annotation, a
      -- parameter's binder, a codomain)
      pure (.ty (K.dm.tyM d psM), ⟨.univ d.sort, none, none, some (n, psM)⟩)
    | none => SM.fail
  | .ctor ty c x ps args => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ctor ty c x ps args)) (do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      -- the parameters known before the fields: the written ones, or the hint's (`evalCtor`'s
      -- `sol`); the fields' types then solve the rest (`runFields`; the audit's A9)
      let sol₀ : List (Option Sem) := if !ps.isEmpty then psM.map some else
        match hint.data with
        | some (n, ps') => if n = ty ∧ ps'.length = d.params.length then ps'.map some else List.replicate d.params.length none
        | none => List.replicate d.params.length none
      -- a constructor of a Prop-sorted inductive is a proof, `⋆` (D42); its arguments are
      -- statement positions, each on its own copy (`stmtArgIf`; D19, R4)
      let (fs, sol) ← runFields (d.sort == 0) d c 0 sol₀ [] args
      if sol.all (·.isSome) then
        let ps' := solved sol
        if d.sort == 0 then
          pure (.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩)
        else
          pure (K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩)
      else SM.fail
    | none => SM.fail) s
  | .const n => pure (K.C.global n)
  | .val v => fun s =>
    -- an embedded value, at the hint; a function or Π-type value carries its shape
    let T : TyS := match v with
      | .clo caps t rd | .tPi caps t rd =>
        { hint with shape := (piShapeOf (stateOf 0 (capsState (capsVals caps) (capsTys rd))) t).map fun sh => (sh.ps, sh.out) }
      | .gfn n => (K.C.global n).2
      | .abs σ => { hint with shape := (K.Δ σ).shape, data := (K.Δ σ).data }
      -- P1 (PROPOSAL, m2-proofs): a loan carries its declared Π-shape (`K.Λ`), as its filler will
      | .loan l => match (K.Λ l).shape with
        | some sh => { hint with shape := some sh }
        | none => hint
      -- a sealed callee (D39: the checker calls a sealed function value) carries the shape of
      -- its program's result (the spine's finding at the general closeCall_step, docs/31 item
      -- 3); its labels are its own, so only the shape is taken
      | .sealed t => match run hint t (emptyState 0) with
        | some ((_, R), _) => { hint with shape := R.shape }
        | none => hint
      | _ => hint
    -- PROPOSAL (m2-proofs): an embedded value holds no borrow the run made, so its result carries
    -- no label, whatever label the hint (a place's stored type, at an assignment) records
    some ((meanV hint v, { T with label := none }), s)
  | .sort l => pure (.ty (.univ l), .plain (.univ (sortSucc l)))
  | .pi hs ds c => fun s =>
    -- [T-Pi]: the parameters' and output's meanings as functions of the earlier parameters
    -- (`runBinds`), the carrier at the declared sort (D55, `Decisions.piSort`)
    let bs := runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc => match run (.plain .err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
      | c => .data fun acc => match run (.plain .err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    some ((.ty (piTyAt l ps out), ⟨.univ l, some (ps, out), none, none⟩), s)
  | .fix self hs ds c dec body => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.fix self hs ds c dec body)) (fun s =>
    -- [Closure] (D51, D53, D80): a closure means a function on its annotated domain, read off
    -- the reference run of its body in the forming frame extended by `self` and the parameters
    -- (the body's layout `[caps…, self, x̄]`). A recursive `fix` means its guarded fixpoint by
    -- stages (docs/24 §4): stage 0 binds `self` to `err`, stage `k + 1` to stage `k`'s closure,
    -- and the function at arguments whose decreasing argument has rank `r` is stage `r + 1`; so
    -- a call that does not decrease reaches stage 0 and means `err`, and `mkTele` then makes
    -- the closure mean `err`.
    let bs := runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc => match run (.plain .err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
      | c => .data fun acc => match run (.plain .err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
    -- the codomain with its structure: the body's hint (the audit's A8: at `.plain _`, a body
    -- that is a bare `Nil` had no parameters to read)
    let cod : List Sem → TyS := match c with
      | .ref U => fun acc => match run (.plain .err) U (extendBy s bs acc) with
        | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
        | none => .plain .err
      | c => fun acc => match run (.plain .err) c (extendBy s bs acc) with
        | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
        | none => .plain .err
    -- the carrier at the declared sort (D55, D12): `piTyAt`/`closureAt` (`Apply1.lean`)
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    let piT := piTyAt l ps out
    let start := s.nextLoan
    -- the declared readings of the parameters and the codomain (`Decide.paramDecls`): what the
    -- frame binds the parameters at, and `self` (D19, R3: bound at `other`, a parameter of a copy
    -- type was moved by its first read, and a call through `self` or a function parameter was
    -- never classified as a statement or a proof)
    let cd := K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c
    let bodyAt (selfM : Sem) (args : List Sem) : Option BodyOut :=
      -- the frame: `self`, then the parameters. A borrow parameter is set up as the generic call
      -- is ([Def]): a fresh label `lᵢ`, a *cell* (a temporary of the frame: temporaries do not
      -- shift de Bruijn indices) reading `lᵢ`'s final content, and the parameter holding the
      -- content as the borrow's holder (D14). Returning the parameter returns its label.
      let s₁ := s.pushBind { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi cd }
      -- each parameter is bound at its type WITH its Π-shape and at its declared reading (`bs`;
      -- D19, R6: bound at `.plain (dom …)`, a function parameter had no shape to be called along)
      let step (sa : SState × List Sem × List Pos) (ap : Sem × PiParam) : SState × List Sem × List Pos :=
        let (s, acc, cells) := sa
        let T : TyS := match bs[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
        let d : DeclInfo := match bs[acc.length]? with | some b => b.2 | none => .other
        if ap.2.isRef then
          let (l, s) := s.freshLoan
          let s := s.pushTemp fun ψ => ψ l
          let cell : Pos := .temp s.topIdx (((s.env.getLast?).map (·.temps.length)).getD 1 - 1)
          let s := pushBindShaped s { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
          (s, acc ++ [ap.1], cells ++ [cell])
        else
          (s.pushBind { ty := { T with label := none }, val := fun _ => ap.1, decl := d }, acc ++ [ap.1], cells)
      let (s₂, _, cells) := (args.zip ps).foldl step (s₁, [], [])
      match run (cod args) body s₂ with
      | some ((r, R), s₃) =>
        -- the frame pop ends the borrows the body made and the parameters' (their cells then
        -- read the holders' contents), except the returned borrow's, whose holder is the
        -- caller's; a borrow parameter's final content is its cell's
        -- PROPOSAL (m2-proofs, 5b): the returned borrow survives only when the codomain is a
        -- borrow; a labelled result at a data codomain (ill-typed) is ended with the rest, else
        -- its cell reads the future at the run's own label in `mkLeafData`
        let keep : Option Nat := match out with | .ref _ => R.label | .data _ => none
        let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
        let finals := cells.map fun c => s₄.valAt c
        some ⟨r, finals, R.label⟩
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem := closureAt l φ ps out g
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun _ gk => bodyAt (closureOf gk))
    let rankOf (args : List Sem) : Nat := match dec with
      | some j =>
        match args[j]?, (ps[j]?).map (·.dom (args.take j)) with
        | some a, some T =>
          match T.dataOf K.dm K.Γ with
          | some (d, ps') => match a.as (K.dm.car d ps') with | some x => K.dm.rank x | none => 0
          | none => match a.asNat with | some n => n | none => 0
        | _, _ => 0
      | none => 0
    let g : List Sem → Option BodyOut := match dec with
      | some _ => fun args => stage (rankOf args + 1) args
      | none => bodyAt .err
    -- forming the closure moves the captured places whose declared readings are not copy (D80)
    let s' := (Term.freeVars (.fix self hs ds c dec body)).foldl (fun s i =>
      if K.D.copy (K.D.placeDecl (scopeOf s) (.var i)) then s
      else match s.varPos i with
        | some pos => s.setAt pos fun _ => .moved
        | none => s) s
    some ((closureOf g, ⟨piT, some (ps, out), none, none⟩), s')) s
  | .call f args hd => fun s =>
    let fl := K.D.flags (scopeOf s) (.call f args hd)
    -- a statement call runs on a copy that is thrown away (E1; `Decisions.flags`, aligned), and
    -- its result carries no label (m2-proofs' finding 6): `SM.stmtIf`, as every clause
    -- a proof call is never applied: its value is `⋆` (P5; `Machine.callFn` at class 2), as
    -- every proof's is (`SM.erasedIf`)
    SM.erasedIf fl (do
      -- a call reads its head in place: it does not consume the function it calls (D53 (e),
      -- `evalCall`'s `inPlace`; D19, R2: `run f` moved a function variable out, so `f(f(n))`
      -- failed)
      let fv ← SM.headOf f (fun p => readPlace K φ p true) (run (.plain .err) f)
      -- a statement call's arguments are statement positions, each on its own copy (R4)
      let as ← runArgs fl.1 fv.2.shape 0 [] args
      callOf fv as) s
  | .nat => pure (.ty (.ty0 Nat), .plain (.univ 1))
  | .unit => pure (.ty (.ty0 Unit), .plain (.univ 1))
  | .zero => pure (.el0 Nat 0, .plain (.ty0 Nat))
  | .tt => pure (.el0 Unit (), .plain (.ty0 Unit))
  | .succ u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.succ u)) (do
    let (v, _) ← run (.plain (.ty0 Nat)) u
    pure (v.succ, .plain (.ty0 Nat))) s
  | .eq A a b => SM.onCopy do
    let (TA, RA) ← run (.plain .err) A
    let T : TyS := ⟨TA.asTy, RA.shape, none, RA.data⟩
    let (va, _) ← SM.onCopy (run T a)
    let (vb, _) ← SM.onCopy (run T b)
    pure (.ty (.prop (va = vb)), .plain (.univ 0))
  | .cong _ _ | .prim "symm" _ | .prim "trans" _ | .prim "rewrite" _ | .prim "rewriteR" _ =>
    pure (.proof, .plain .err)
  | .ref A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ref A)) (do
    let (TA, _) ← run (.plain .err) A
    pure (TA, .plain (.univ 1))) s
  | .id A t u => fun s => do
    -- `Id` observes: each side on a copy of the state, a fresh value written through each
    -- re-pointed borrow binding ([Obs-ref]), every borrow ended, the result and every position
    -- compared (D84: moved places are definite values, so they compare too); the proposition
    -- holds for every choice of the written values
    let ((TA, RA), _) ← SM.onCopy (run (.plain .err) A) s
    let T : TyS := ⟨TA.asTy, RA.shape, none, RA.data⟩
    let reps := K.D.rePointed (scopeOf s) t
    let o₁ ← run T t s
    let o₂ ← run T u s
    some ((.ty (.prop (∀ ws : List Sem,
      observation φ reps ws s.positions o₁.1 o₁.2 = observation φ reps ws s.positions o₂.1 o₂.2)), .plain (.univ 0)), s)
  | .prim "J" [A, a, b, P, h, t] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, h, t])) (do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (run (.plain .err) A)
    let _ ← SM.onCopy (run (.plain .err) a)
    let _ ← SM.onCopy (run (.plain .err) b)
    let _ ← SM.onCopy (run (.plain .err) P)
    let _ ← SM.onCopy (run (.plain .err) h)
    run hint t) s
  -- `clone`, `peek` and `inplace` of a place read it in place: not consumed (`inplace` is a stuck
  -- block's read-only capture; it used to be `run hint u`, a move: D19)
  | .prim "clone" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "clone" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (run hint u)) s
  | .prim "peek" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "peek" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (run hint u)) s
  | .prim "inplace" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "inplace" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (run hint u)) s
  | .prim _ _ => SM.fail
  | .ascribe u A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ascribe u A)) (do
    -- the annotation is the term's type WITH its structure: the Π-shape and the `D(ā)` data the
    -- run of the type term returns (the audit's A7: at `.plain _`, an annotated function could
    -- not be called and an annotated bare constructor had no parameters)
    let (TA, RA) ← SM.onCopy (run (.plain .err) A)
    let T : TyS := ⟨TA.asTy, RA.shape, none, RA.data⟩
    let (v, R) ← run T u
    pure (v, { T with label := R.label })) s
termination_by structural t => t

/-- Arm `c` of a match, run at the match's expected type. -/
noncomputable def runArm (hint : TyS) (c : Nat) : List (Hint × Term) → SM Res
  | [] => SM.fail
  | (_, t) :: rest => if c = 0 then run hint t else runArm hint (c - 1) rest
termination_by structural arms => arms

/-- The parameters of a Π-term as a frame binds them (`PBind`): each domain term run in the
forming state extended by the earlier parameters at THEIR types and readings (`pre`), giving the
parameter's type with its Π-shape (the run of a Π-term returns the Π's shape in its result type)
as a function of the earlier arguments; `dcs` are the telescope's declared readings. For `&A` the
content type `A` is run. (D19, R6; `psOf` reads the `PiParam`s off the result.) -/
noncomputable def runBinds (s : SState) (dcs : List DeclInfo) (pre : List PBind) : List Term → List PBind
  | [] => []
  | .ref A :: ds =>
    mkBind dcs pre (fun acc => run (.plain .err) A (extendBy s pre acc)) ::
      runBinds s dcs (pre ++ [mkBind dcs pre (fun acc => run (.plain .err) A (extendBy s pre acc))]) ds
  | d :: ds =>
    mkBind dcs pre (fun acc => run (.plain .err) d (extendBy s pre acc)) ::
      runBinds s dcs (pre ++ [mkBind dcs pre (fun acc => run (.plain .err) d (extendBy s pre acc))]) ds
termination_by structural ds => ds

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← SM.onCopy (run ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ a)
    let rest ← runParams d (i + 1) (earlier ++ [v]) as
    pure (v :: rest)
termination_by structural as => as

/-- A constructor's fields, each at its field type at the earlier fields. With `stmt` (a proof
constructor's, D42) each field is a statement position, on its own copy (`stmtArgIf`), unless its
declared type is a borrow type (`Decide.stmtArgInPlace`, read through `Decisions.declOf`).

`sol` is the parameters solved so far (`Machine.evalCtor`'s `sol`): the written ones or the
hint's, then what each field's type gives the unsolved ones (`unifyTyS`; the audit's A9: before,
an unannotated `Pair(a, b)` or `Cons(x, xs)` with no hint had no parameters and failed). A field
is run at its declared type as hint once every parameter that type reads is solved
(`Machine.fieldTypeAt`'s guard), and at no hint before. -/
noncomputable def runFields (stmt : Bool) (d : IndDecl) (c i : Nat) (sol : List (Option Sem)) (earlier : List Sem) :
    List Term → SM (List Sem × List (Option Sem))
  | [] => pure ([], sol)
  | a :: as => fun s => (do
    let T : TyS := match fieldTerm d c i with
      | some FT =>
        if FT.freeVars.all (fun j => d.params.length ≤ j || (sol.getD (d.params.length - 1 - j) none).isSome) then
          ⟨K.dm.fieldTy d (solved sol) c i earlier, none, none, K.dm.fieldData d (solved sol) c i earlier⟩
        else .plain .err
      | none => .plain .err
    let (v, R) ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (run T a)
    let sol₁ := match fieldTerm d c i with
      | some FT => unifyTyS d.params.length FT R sol
      | none => sol
    let (rest, sol₂) ← runFields stmt d c (i + 1) sol₁ (earlier ++ [v]) as
    pure (v :: rest, sol₂)) s
termination_by structural as => as

/-- A call's arguments, each at its parameter type from the callee's shape (D82, [Call-type]).
With `stmt` (a statement call's) each argument is a statement position, on its own copy
(`stmtArgIf`; D19, R4: in sequence on the call's one copy, `Lem(x, x)` found `x` moved), unless
its declared type is a borrow type, which runs in place (`Decide.stmtArgInPlace`). -/
noncomputable def runArgs (stmt : Bool) (shape : Option (List PiParam × PiOut)) (i : Nat) (earlier : List Sem) :
    List Term → SM (List Res)
  | [] => pure []
  | a :: as => fun s => (do
    let T : TyS := match shape with
      | some (ps, _) => match ps[i]? with | some p => ⟨p.dom earlier, none, none, p.data earlier⟩ | none => .plain .err
      | none => .plain .err
    let r ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (run T a)
    let rest ← runArgs stmt shape (i + 1) (earlier ++ [r.1]) as
    pure (r :: rest)) s
termination_by structural as => as

/-- The shape of a closure's or Π-closure's type, from its term, in the frame of its captures. -/
noncomputable def piShapeOf (s : SState) : Term → Option PiShape
  | .pi _ ds (.ref U) | .fix _ _ ds (.ref U) _ _ =>
    some ⟨psOf (runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds) ds,
      .ref fun acc => match run (.plain .err) U (extendBy s (runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩
  | .pi _ ds c | .fix _ _ ds c _ _ =>
    some ⟨psOf (runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds) ds,
      .data fun acc => match run (.plain .err) c (extendBy s (runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩
  | _ => none
termination_by structural t => t

/-- The meaning of a value, with the code-dependent forms given by the run itself (the knot of
`Value.mean`'s `CodeMeaning`): a sealed program is its program run from the empty state (the
label counter above its loans) at the hint; a closure or Π-closure is its term run in a frame
holding its captures at their recorded types (D51); a global is `K.C.global`. The other clauses
are `Value.mean`'s (`meanV_eq_mean`). -/
noncomputable def meanV (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (meanV (.plain (.ty0 Nat)) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (K.C.global n).1
  | .clo caps t rd => match run (.plain .err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => v
    | none => .err
  | .borrow _ w => meanV hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  -- PROPOSAL (m2-proofs, 8): a sealed program runs from the label counter 0, not from above its
  -- loans. Its fresh labels never leave its run (only the result's meaning and shape are read),
  -- and meeting one of its loans is harmless (a loan is read by the value's meaning, never through
  -- the state). A counter fixed by the term changes under substitution, which then needs the
  -- counter's independence (the renaming lemma, false as first stated: finding 7)
  | .sealed t => match run hint t (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err
  | .proof => .proof
  | .tNat => .ty (.ty0 Nat)
  | .tUnit => .ty (.ty0 Unit)
  | .tEq A a b =>
    let T := TyS.plain (meanV (.plain .err) A).asTy
    .ty (.prop (meanV T a = meanV T b))
  | .tRef A => meanV (.plain .err) A
  | .tPi caps t rd => match run (.plain .err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => .ty v.asTy
    | none => .ty .err
  | .sort l => .ty (.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let ps? := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some (meanParams d 0 [] ps)
      match ps? with
      | some ps' => if d.sort == 0 then .proof else K.dm.ctorM d ps' c (meanFields d ps' c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => .ty (K.dm.tyM d (meanParams d 0 [] args))
    | none => .ty .err
termination_by structural v => v

noncomputable def meanFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV ⟨K.dm.fieldTy d ps c i earlier, none, none, K.dm.fieldData d ps c i earlier⟩ v
    s :: meanFields d ps c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

noncomputable def meanParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ v
    s :: meanParams d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- A closure's or Π-closure's captured values, each read as a value (D51). -/
noncomputable def capsVals : List Value → List Sem
  | [] => []
  | v :: vs => meanV (.plain .err) v :: capsVals vs
termination_by structural vs => vs

/-- The captures' recorded declared types, each read as a type (D82; a type is future-free) WITH
its structure: a captured function's Π-shape, a captured `D(ā)`'s data (the audit's A10: read as
`.plain _`, a call through a captured function failed in the closure's body). -/
noncomputable def capsTys : List (DeclInfo × Value) → List (DeclInfo × TyS)
  | [] => []
  | (d, T) :: rest => (d, ⟨(meanV (.plain .err) T).asTy, tyShape T, none, tyDataV T⟩) :: capsTys rest
termination_by structural rest => rest

/-- The Π-shape of a recorded type value: a Π-closure's is its term's, in its captures' frame; a
borrow type's is its content's (as a borrow parameter is bound at its content's type). -/
noncomputable def tyShape : Value → Option (List PiParam × PiOut)
  | .tPi caps t rd => (piShapeOf (stateOf 0 (capsState (capsVals caps) (capsTys rd))) t).map fun sh => (sh.ps, sh.out)
  | .tRef T => tyShape T
  | _ => none
termination_by structural v => v

/-- The data of a recorded type value `D(ā)` or `&D(ā)`: `Value.tyData`, by the run. -/
noncomputable def tyDataV : Value → Option (String × List Sem)
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => some (n, meanParams d 0 [] args)
    | none => none
  | .tRef T => tyDataV T
  | _ => none
termination_by structural v => v
end

/-- The binders of a telescope formed in `s`: `runBinds` at the telescope's declared readings. -/
noncomputable def bindsOf (s : SState) (ds : List Term) : List PBind :=
  runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds

/-- The parameters of a Π-term formed in `s`, as the `.pi` and `.fix` clauses read them. -/
noncomputable def runDoms (s : SState) (ds : List Term) : List PiParam := psOf (bindsOf K ρ φ s ds) ds

/-- A closure's codomain with its structure, as a function of the parameters: its body's hint. -/
noncomputable def fixCod (s : SState) (bs : List PBind) (c : Term) : List Sem → TyS := match c with
  | .ref U => fun acc => match run K ρ φ (.plain .err) U (extendBy s bs acc) with
    | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
    | none => .plain .err
  | c => fun acc => match run K ρ φ (.plain .err) c (extendBy s bs acc) with
    | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
    | none => .plain .err

/-- The code meaning the run induces (the knot of `Value.mean`): each code-dependent form read by
the run **at the assignment and future it is asked at**. As first written it ignored both and read
at one fixed pair, so a state's meaning read every sealed program at the knot's future whatever
future it was asked at (`Regress/Knot_dcdd0a34.lean`: `⟦⌈loan ℓ⌉⟧` at `φ` was `φ₀ ℓ`), while
`Below`, `Mean.semEnd` and `Membership` read a state at other futures, and a step's extended
assignment `ρ'` was never the knot's. A deferred type (`paramTy`) is read under the constant
future, as every stored type is (docs/27 Lemma 5). It depends on `K.C` only through `K.C.global`. -/
noncomputable def codeMeaning (K : RunCtx) : CodeMeaning where
  global := K.C.global
  sealed ρ φ hint t := meanV K ρ φ hint (.sealed t)
  clo ρ φ caps t rd := meanV K ρ φ (.plain .err) (.clo caps t rd)
  pi ρ φ caps t rd := (meanV K ρ φ (.plain .err) (.tPi caps t rd)).asTy
  -- a deferred type is the parameter's binder WITH its structure (a function parameter's
  -- Π-shape, a `D(ā)` parameter's data), or the codomain's: as the `.fix` clause's frame binds it
  paramTy ρ P ws j := match P with
    | .tPi caps t rd =>
      match t with
      | .pi _ ds c | .fix _ _ ds c _ _ =>
        let s₀ := stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))
        let acc := ws.map (meanV K ρ noFuture (.plain .err))
        match (bindsOf K ρ noFuture s₀ ds)[j]? with
        | some b => b.1 (acc.take j)
        | none => fixCod K ρ noFuture s₀ (bindsOf K ρ noFuture s₀ ds) c acc
      | _ => .plain .err
    | _ => .plain .err
  tyShape ρ T := tyShape K ρ noFuture T

/-- The code meaning of a run context, as the step statements read a state: `MState.mean K.dm K.M
K.Γ ρ st`. There is no knot hypothesis `K.C = …`: `K.C` supplies the globals and nothing else. -/
noncomputable abbrev RunCtx.M (K : RunCtx) : CodeMeaning := codeMeaning K

/-- Δ as the run knows it, from a checker state: each abstract value's stored type with its
structure (`Value.tyS`: its data, and for a Π-type its shape from its term through
`CodeMeaning.tyShape`), read under the constant future as every stored type is. -/
noncomputable def deltaOf (K : RunCtx) (ρ : Assignment) (st : MState) : Nat → TyS := fun σ =>
  match st.absTy[σ]? with
  | some T => Value.tyS K.dm (codeMeaning K) K.Γ ρ T
  | none => .plain .err

/-- The run context knows the types of the state's unknowns: `K.Δ` is `deltaOf` at every unknown
the state has. Beyond them `K.Δ` is free, so a step that creates unknowns extends it (as it
extends the assignment) and leaves what the earlier ones read unchanged. -/
def DeltaOk (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  ∀ σ, σ < st.absTy.size → K.Δ σ = deltaOf K ρ st σ

/-- The knot at the future asked: a sealed program in a state is read at the state's future (the
positive form of `Regress/Knot_dcdd0a34.lean`). -/
theorem mean_sealed_at_future (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (l : Nat) :
    Value.mean K.dm K.M K.Γ ρ φ hint (.sealed (.val (.loan l))) = φ l := by
  show meanV K ρ φ hint (.sealed (.val (.loan l))) = φ l
  simp [meanV, run]

/-- The Π-closure clause of the knot: `meanV` of a Π-closure is already a type value. -/
theorem meanV_tPi_ty (hint : TyS) (caps : List Value) (t : Term) (rd : List (DeclInfo × Value)) :
    meanV K ρ φ hint (.tPi caps t rd) = .ty (meanV K ρ φ (.plain .err) (.tPi caps t rd)).asTy := by
  show (match run K ρ φ (.plain .err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
      | some ((v, _), _) => Sem.ty v.asTy
      | none => .ty .err)
    = .ty (match run K ρ φ (.plain .err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
      | some ((v, _), _) => Sem.ty v.asTy
      | none => .ty .err).asTy
  cases run K ρ φ (.plain .err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) <;> rfl

mutual
/-- The knot, by induction on the value: each clause is the same text, the code-dependent ones
through `codeMeaning`, the Π-closure's by `meanV_tPi_ty`. -/
theorem meanV_eq_mean_aux (hint : TyS) : (v : Value) →
    Value.mean K.dm (codeMeaning K) K.Γ ρ φ hint v = meanV K ρ φ hint v
  | .zero => rfl
  | .succ v => by
    show (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (.ty0 Nat)) v).succ
      = (meanV K ρ φ (.plain (.ty0 Nat)) v).succ
    rw [meanV_eq_mean_aux (.plain (.ty0 Nat)) v]
  | .unit => rfl
  | .gfn _ => rfl
  | .clo _ _ _ => rfl
  | .borrow _ w => meanV_eq_mean_aux hint w
  | .loan _ => rfl
  | .bot => rfl
  | .abs _ => rfl
  | .sealed _ => rfl
  | .proof => rfl
  | .tNat => rfl
  | .tUnit => rfl
  | .tEq A a b => by
    show Sem.ty (.prop (Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain .err) A).asTy) a
        = Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain .err) A).asTy) b))
      = Sem.ty (.prop (meanV K ρ φ (.plain (meanV K ρ φ (.plain .err) A).asTy) a
        = meanV K ρ φ (.plain (meanV K ρ φ (.plain .err) A).asTy) b))
    rw [meanV_eq_mean_aux (.plain .err) A, meanV_eq_mean_aux _ a, meanV_eq_mean_aux _ b]
  | .tRef A => meanV_eq_mean_aux (.plain .err) A
  | .tPi caps t rd => (meanV_tPi_ty K ρ φ hint caps t rd).symm
  | .sort _ => rfl
  | .ind ty c h ps fs => by
    have hP : ∀ d, Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d 0 [] ps = meanParams K ρ φ d 0 [] ps :=
      fun d => meanParams_eq_mean d 0 [] ps
    have hF : ∀ d ps', Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d ps' c 0 [] fs
        = meanFields K ρ φ d ps' c 0 [] fs :=
      fun d ps' => meanFields_eq_mean d ps' c 0 [] fs
    simp only [Value.mean, meanV, hP, hF]
    cases List.find? (fun x => x.name == ty) K.Γ with
    | none => rfl
    | some d =>
      cases (if (ps.isEmpty && !d.params.isEmpty) = true then
          (match hint.data with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some (meanParams K ρ φ d 0 [] ps)) <;> rfl
  | .tInd n args => by
    have hP : ∀ d, Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d 0 [] args = meanParams K ρ φ d 0 [] args :=
      fun d => meanParams_eq_mean d 0 [] args
    simp only [Value.mean, meanV, hP]
    cases List.find? (fun x => x.name == n) K.Γ <;> rfl
termination_by structural v => v

theorem meanFields_eq_mean (d : IndDecl) (ps : List Sem) (c : Nat) :
    (i : Nat) → (earlier : List Sem) → (vs : List Value) →
    Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d ps c i earlier vs = meanFields K ρ φ d ps c i earlier vs
  | _, _, [] => rfl
  | i, earlier, v :: vs => by
    show Value.mean K.dm (codeMeaning K) K.Γ ρ φ ⟨K.dm.fieldTy d ps c i earlier, none, none, K.dm.fieldData d ps c i earlier⟩ v
        :: Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d ps c (i + 1)
          (earlier ++ [Value.mean K.dm (codeMeaning K) K.Γ ρ φ ⟨K.dm.fieldTy d ps c i earlier, none, none, K.dm.fieldData d ps c i earlier⟩ v]) vs
      = meanV K ρ φ ⟨K.dm.fieldTy d ps c i earlier, none, none, K.dm.fieldData d ps c i earlier⟩ v
        :: meanFields K ρ φ d ps c (i + 1) (earlier ++ [meanV K ρ φ ⟨K.dm.fieldTy d ps c i earlier, none, none, K.dm.fieldData d ps c i earlier⟩ v]) vs
    rw [meanV_eq_mean_aux _ v, meanFields_eq_mean d ps c (i + 1) _ vs]
termination_by structural _ _ vs => vs

theorem meanParams_eq_mean (d : IndDecl) :
    (i : Nat) → (earlier : List Sem) → (vs : List Value) →
    Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d i earlier vs = meanParams K ρ φ d i earlier vs
  | _, _, [] => rfl
  | i, earlier, v :: vs => by
    show Value.mean K.dm (codeMeaning K) K.Γ ρ φ ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ v
        :: Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d (i + 1)
          (earlier ++ [Value.mean K.dm (codeMeaning K) K.Γ ρ φ ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ v]) vs
      = meanV K ρ φ ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ v
        :: meanParams K ρ φ d (i + 1) (earlier ++ [meanV K ρ φ ⟨K.dm.paramTy d i earlier, none, none, K.dm.paramData d i earlier⟩ v]) vs
    rw [meanV_eq_mean_aux _ v, meanParams_eq_mean d (i + 1) _ vs]
termination_by structural _ _ vs => vs
end

/-- The knot ties: `Value.mean` at the induced code meaning is `meanV`, at the run's future. By
induction on the value; every clause but the code-dependent ones is the same text. -/
theorem meanV_eq_mean (hint : TyS) (v : Value) :
    Value.mean K.dm (codeMeaning K) K.Γ ρ φ hint v = meanV K ρ φ hint v :=
  meanV_eq_mean_aux K ρ φ hint v

end

end Ochr.Meaning
