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

/-- An erased term (C1, docs/31 D83/D86): a proof (`fl.2`) is RUN on a copy, strictly, and is `⋆` at
`prop True` where its clause ran to `⋆` (a level-0 code is fixed by its truth, so a proof that runs has
THE true proposition as its type; the orchestrator's decision 1, applied to every proof); a statement
(`fl.1`) runs on a copy (`SM.stmtIf`). `fl` is the aligned decision `Decisions.flags` of the term:
(erased, proof). Both tests are computable. -/
noncomputable def SM.erasedIf (fl : Bool × Bool) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  if fl.2 then
    match x s with
    | some ((.proof, _), _) => some ((.proof, .plain (TyM.prop True)), s)
    | some _ => none
    | none => none
  else SM.stmtIf fl.1 x s

theorem SM.erasedIf_congr {fl : Bool × Bool} {x x' : SM (Sem × TyS)} {s : SState} (h : x s = x' s) :
    SM.erasedIf fl x s = SM.erasedIf fl x' s := by
  simp only [SM.erasedIf, SM.stmtIf, h]

/-- An erased term's run, taken apart: the run itself, or the state unchanged and the result
label-free. -/
theorem SM.erasedIf_some {fl : Bool × Bool} {x : SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (h : SM.erasedIf fl x s = some (r, s')) : x s = some (r, s') ∨ (s' = s ∧ r.2.label = none) := by
  unfold SM.erasedIf at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨rfl, rfl⟩
    · cases h
    · cases h
  · rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, e, hl, -⟩
    · exact .inl h
    · exact .inr ⟨e, hl⟩

/-- An erased term's run (C1): `•` at `True`, the state as it was. (An erased place is no longer
`•` at its stored type, the old `SM.erasedAt`: every proof that runs is at the true proposition.) -/
theorem SM.erasedIf_erased {fl : Bool × Bool} {x : SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (hfl : fl.2 = true) (h : SM.erasedIf fl x s = some (r, s')) :
    s' = s ∧ r = (.proof, .plain (TyM.prop True)) := by
  unfold SM.erasedIf at h
  rw [if_pos hfl] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h
  · cases h

/-- A run that returned a proof. -/
def SM.ranProof : Option ((Sem × TyS) × SState) → Bool
  | some ((.proof, _), _) => true
  | _ => false

/-- An erased match on a proof with other than one arm (`Or` eliminated into a proposition, the
lead's ruling 3 of 2026-11-21): the scrutinee, a proof, chooses no arm, so the arms run, each on a
copy of the state, and the match runs where one of them runs to a proof, at that arm's type, the
state as it was, no label. No arm runs (none exists, or every one fails, as on an empty
proposition, of which there is no member): the match fails. The test is computable. -/
noncomputable def SM.anyArm (n : Nat) (f : Nat → SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  match (List.range n).find? (fun c => SM.ranProof (f c s)) with
  | some c => (f c s).map fun x => ((x.1.1, { x.1.2 with label := none }), s)
  | none => none

/-- The arm `SM.anyArm` takes: one that ran to a proof; the state as it was, the label dropped. -/
theorem SM.anyArm_some {n : Nat} {f : Nat → SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (h : SM.anyArm n f s = some (r, s')) :
    ∃ c R s₁, c < n ∧ f c s = some ((.proof, R), s₁) ∧ r = (.proof, { R with label := none }) ∧ s' = s := by
  unfold SM.anyArm at h
  split at h
  · rename_i c hc
    have hmem := List.mem_of_find?_eq_some hc
    have hp := List.find?_some hc
    cases hf : f c s with
    | none => rw [hf] at h; cases h
    | some x =>
      obtain ⟨⟨v, R⟩, s₁⟩ := x
      rw [hf] at h hp
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases v <;> simp [SM.ranProof] at hp
      exact ⟨c, R, s₁, List.mem_range.mp hmem, hf, rfl, rfl⟩
  · cases h

/-- `SM.anyArm` of pointwise equal runs. -/
theorem SM.anyArm_congr {n : Nat} {f g : Nat → SM (Sem × TyS)} {s : SState} (h : ∀ c, f c s = g c s) :
    SM.anyArm n f s = SM.anyArm n g s := by
  simp only [SM.anyArm, h]

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
  Δ : Nat → TyS := fun _ => .plain TyM.err
  /-- the declared types of the loans as the run knows them (P1, PROPOSAL m2-proofs): a borrowed
  function value (`&f`) is real, so an embedded `loan_ℓ` carries the Π-shape of its position's
  declared type (by (WF9) every loan outside a sealed program sits at a typed position), as the
  value that fills it will. A loan with no shape here reads as the hint (data). -/
  Λ : Nat → TyS := fun _ => .plain TyM.err
  /-- the definition being checked and a bound (docs/31 D73, the knot of [Def]): while a function
  is checked, `CtxOk` asks of its global only membership at arguments whose decreasing component
  has rank below the bound (`Steps.MemBelow`), which the induction on the bound supplies -/
  cur : Option (String × Nat) := none

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

/-- A parameter as a frame binds it: its type (a code, with its whole structure, docs/31 D59) as
a function of the earlier arguments, and its declared reading. -/
abbrev PBind : Type 3 := (List Sem → TyS) × DeclInfo

/-- The bindings `extendBy` pushes: argument `i` at parameter `i`'s type at the earlier arguments
and at its declared reading (`err` and `other` beyond `bs`). -/
def extendBinds (bs : List PBind) (acc : List Sem) : List SBinding :=
  acc.zipIdx.map fun ai =>
    { ty := match bs[ai.2]? with | some b => { b.1 (acc.take ai.2) with label := none } | none => .plain TyM.err, val := fun _ => ai.1, decl := match bs[ai.2]? with | some b => b.2 | none => .other }

/-- The state's top frame extended by bindings holding the given meanings (a Π's or a closure's
parameters at formation), each at its parameter's type and reading (`bs`): a later domain term or
the codomain may call an earlier parameter, and reads its declared type for copy or move. -/
def extendBy (s : SState) (bs : List PBind) (acc : List Sem) : SState :=
  (extendBinds bs acc).foldl (fun s b => s.pushBind b) s

/-- A parameter's binder from the run of its domain term at each prefix of arguments (`r`): the
type the term runs to (its code), and the reading `dcs` gives parameter `pre.length`. -/
def mkBind (dcs : List DeclInfo) (pre : List PBind) (r : List Sem → Option ((Sem × TyS) × SState)) : PBind :=
  (fun acc => match r acc with
    | some ((v, _), _) => .plain v.asTy
    | none => .plain TyM.err, dcs.getD pre.length .other)

/-- A domain term `&A`: a borrow parameter. -/
def _root_.Ochr.Term.isRefTy : Term → Bool
  | .ref _ => true
  | _ => false

/-- The parameters of a Π-term as the telescope's description (`PiDom`), from their binders and
domain terms: `&A` marks a borrow parameter; the type is the binder's. -/
def psOf : List PBind → List Term → List PiDom
  | b :: bs, d :: ds => ⟨d.isRefTy, fun acc => (b.1 acc).m⟩ :: psOf bs ds
  | _, _ => []

/-- Fill parameter variable `j` (of `np`) of a constructor's solution, if it is not solved yet
(`Machine.unifyParams`' variable case: in a field's type, parameter `i` is `var (np - 1 - i)`). -/
def fillParam (np j : Nat) (v : Sem) (sol : List (Option Sem)) : List (Option Sem) :=
  if j < np ∧ (sol.getD (np - 1 - j) none).isNone then sol.set (np - 1 - j) (some v) else sol

mutual
/-- Infer a constructor's unwritten parameters from a field's declared type term `FT` and the
type `R` the field's run returned (`Machine.unifyParams`, D46; the audit's A9): where `FT` is a
parameter variable, the parameter is `R` itself; where it is `D(x̄)` and `R` is `D`'s code at a
record, each argument is read against the entry the record keeps for that parameter (docs/34
§14: a type parameter's code at `paramKey`), at any depth (`List(List(A))`, the lead's 3a), and a
level-0 value parameter's small reading (Handoff 3b: `Wrap`'s `n` from `t : Tag(3)`). Only
unsolved parameters are filled. A type the run does not know (`err`) solves nothing, as the
checker's field with no type. A parameter the record does not keep (one above level 0) is not
solved. -/
def unifyTyS (dm : DataModel) (np : Nat) : Term → TyS → List (Option Sem) → List (Option Sem)
  | .place (.var j), R, sol => if R.m.isErr then sol else fillParam np j (.ty R.m) sol
  | .tind m as, R, sol =>
    if R.m.isErr then sol else
      match R.data with
      | some (m', r) => if m = m' then unifyArgsTyS dm np r 0 as sol else sol
      | none => sol
  | _, _, sol => sol
termination_by structural FT => FT

/-- The arguments of `D(x̄)` against `D`'s record, left to right (`Machine.unifyParamsList`). -/
def unifyArgsTyS (dm : DataModel) (np : Nat) (r : Rec) : Nat → List Term → List (Option Sem) → List (Option Sem)
  | _, [], sol => sol
  | k, a :: as, sol =>
    unifyArgsTyS dm np r (k + 1) as (match r (paramKey k) with
      | .none => sol
      -- a level-0 value parameter read small (docs/34 Handoff 3b): a parameter variable at its
      -- position is solved to the meaning rebuilt from it, which gives the same record
      | .small sv => match a with
        | .place (.var j) => fillParam np j (ofSmall sv) sol
        | _ => sol
      | _ => unifyTyS dm np a (.plain (dm.paramTyOf r k)) sol)
termination_by structural _ as => as
end

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

/-- The future at which every label the state holds reads `err`: a lent part of a value then reads
`err`, which is not `moved`, so what reads `moved` under it is the value's OWN moved parts. -/
def SState.lentFuture (s : SState) (φ : Future) : Future := fun l => if l ∈ s.liveLabels then .err else φ l

/-- The top frame's places holding `⊥` (D84's `entry` set of a match), as `Machine.staticJoin` reads
them (`botPlaces` of each binding's value): every place under a variable whose content is moved,
at the grain of the value (`Sem.movedIn`), through a borrow variable's content as `*r…`, and
never under a lent part (the checker's value there is a loan, which holds no `⊥` of its own:
`lentFuture`).

As first written this was the WHOLE variables reading `moved` at the closed future, a gap recorded
when it was written. It is a fault (docs/31 D24, third lead): with `p.0` moved before a match, an
arm that refills it and another that does not, the checker's join says `p.0` is moved and drops it
after the arm taken (`Decide.jdMoves` from the entry `[p.0]`), where the run, passing the entry
`[]`, left it whole; `Id` observes the difference, and the checker proves an `Id` the run made
false (`Regress/JoinProbes.lean`: `IdRefill`, accepted). -/
noncomputable def movedPlaces (s : SState) : List Place :=
  match s.env.getLast? with
  | some fr => (List.range fr.binds.length).flatMap fun i =>
      match s.varPos i with
      | some pos => Sem.movedIn (s.valAt pos (s.lentFuture φ))
          (if (s.shape pos).isSome then .deref (.var i) else .var i)
      | none => []
  | none => []

/-- What a match reads of a place's meaning: `ob` of the content at the path and of its type,
`err` where the path does not resolve (the tag, `natTag`, `indTag`). -/
noncomputable def obsAt (T : TyS) (steps : List Step) (ob : Sem → TyS → Sem) (x : Sem) : Sem :=
  match Sem.follow K.dm K.Γ T x steps with
  | some (v, T') => ob v T'
  | none => .err

/-- The tag of a number, `Z` or `S`: what a `match` on a number observes
(`Machine.accessNeutralHead`). -/
noncomputable def natTag (v : Sem) (_ : TyS) : Sem :=
  match v.asNat with
  | some 0 => .el0 Nat 0
  | some (_ + 1) => .el0 Nat 1
  | none => match v with
    | .dat "Nat" _ 0 [] => .el0 Nat 0
    | .dat "Nat" _ 1 _ => .el0 Nat 1
    | _ => .err

/-- The tag of a data value, its constructor's index, or `•` for a proof: what a `match` on it
observes, read off the value (docs/31 D32: a constructor value describes itself; neither its
type nor its carrier is consulted, D31). -/
noncomputable def indTag (v : Sem) (_ : TyS) : Sem :=
  match v with
  | .proof => .proof
  | .dat _ _ c _ => .el0 Nat c
  | _ => .err

/-- A typed future of a state (the orchestrator's ruling (A), 2026-11-21, docs/31 D106): the run's
own off the live labels; each live label a whole MEMBER of its recorded content type. A label's
value in a future is its borrow's content when the borrow ends, and an end is strict (`EndOk`), so
no future the run realises gives a label a partly moved value; a partly moved CURRENT content of a
live borrow is state (its holder's), not future. (It was an open member until the ruling: the
relation compares only at whole futures, and a state good at open ones could be stuck where the
checker is not, `Strict/OpenFutureCE`.) -/
def TypedFut (s : SState) (ψ : Future) : Prop :=
  (∀ l, l ∉ s.liveLabels → ψ l = φ l) ∧ ∀ l ∈ s.liveLabels, ψ l ∈ₛ[K.dm.read] s.heldTy l

/-- **A future typed at held labels** (docs/31 D141): each label of `held` is given a whole member of the type it is
held at. `TypedFut`'s second clause is this at the state's live labels and their recorded types (`typedFut_iff_held`);
a function's output asks its borrow parameters' finals at the futures typed at the labels its RESULT holds
(`Steps.OutGood`, `BodyOut.held`), the labels the frame pop keeps live. -/
def HeldTyped (R : DataRead) (held : List (Nat × TyM)) (ψ : Future) : Prop :=
  ∀ l T, (l, T) ∈ held → ψ l ∈ₛ[R] T

theorem typedFut_iff_held (s : SState) (ψ : Future) :
    TypedFut K φ s ψ ↔
      (∀ l, l ∉ s.liveLabels → ψ l = φ l) ∧ HeldTyped K.dm.read (s.liveLabels.map fun l => (l, s.heldTy l)) ψ := by
  refine and_congr Iff.rfl ⟨fun h l T hm => ?_, fun h l hl => h l _ (List.mem_map.2 ⟨l, hl, rfl⟩)⟩
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hm
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact h l' hl'

/-- **STRICT END** (ruling (A)): the borrow `l` may end only where its holder's content is a member of
its recorded content type at every typed future (the checker's rule, main's D98: no borrow ends over
moved-out content). -/
def EndOk (s : SState) (l : Nat) : Prop :=
  ∀ r, s.holderOf l = some r → ∀ ψ, TypedFut K φ s ψ → s.valAt r ψ ∈ₛ[K.dm.read] s.heldTy l

/-- `ok` holds at each step of a fold, at the state that step starts from. -/
def FoldOk {α : Type} (f : SState → α → SState) (ok : SState → α → Prop) : List α → SState → Prop
  | [], _ => True
  | a :: as, s => ok s a ∧ FoldOk f ok as (f s a)

/-- Every end of `ls.foldl SState.endLabel s` is strict-OK. -/
def EndsOk (ls : List Nat) (s : SState) : Prop := FoldOk SState.endLabel (EndOk K φ) ls s

/-- One round of [Access] (`SState.access`'s step). -/
noncomputable def accRound (p : Pos) (hit : List Step → Bool) (s : SState) : SState :=
  (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s

/-- Every end [Access] makes is strict-OK: round `k`'s ends, at the state after `k` rounds. -/
def AccessOk (s : SState) (p : Pos) (hit : List Step → Bool) : Prop :=
  ∀ k, k < s.liveLabels.length →
    EndsOk K φ (((List.range k).foldl (fun t _ => accRound p hit t) s).liveLabels.filter
      (((List.range k).foldl (fun t _ => accRound p hit t) s).reached p hit))
      ((List.range k).foldl (fun t _ => accRound p hit t) s)

/-- STRICT END: the ends of a read's or a borrow's access of `p` (`contentOf`). -/
def ContentOk (p : Place) (s : SState) : Prop :=
  match resolve s p with
  | some (pos, steps) => AccessOk K φ s pos (dataHit steps)
  | none => True

/-- STRICT END: the ends of a match's access for the tag (`tagOf`). -/
def TagOk (p : Place) (s : SState) : Prop :=
  match resolve s p with
  | some (pos, steps) => AccessOk K φ s pos (tagHit steps)
  | none => True

/-- STRICT END: an assignment's ends (`assignAt`): its access, then the old borrow's end at a root. -/
def AssignOk (p : Place) (s : SState) : Prop :=
  match resolve s p with
  | some (pos, steps) =>
    ((steps.isEmpty && (s.shape pos).isSome) = false → AccessOk K φ s pos (dataHit steps)) ∧
    (steps.isEmpty = true → ∀ l,
      (if steps.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit steps)).shape pos = some l →
      EndOk K φ (if steps.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit steps)) l)
  | none => True

/-- The content of a place after [Access] for it (static, docs/31 D29: the borrows lent at, over
or under the place have ended), read at the state's typed future (`SState.typedFuture`: each live
label its recorded member, docs/31 D68), with its type. That future is typed at a related state, so
the relation compares the reading there with the checker's value, whose meaning, holding no live
loan after the access, is the same at every future; and it makes the read congruent in the future
at every state. (Until D68 the read was at the closed future, each live label fixed to its holder's
current content, which is not typed while a holder's content is partly moved.) The type of a field of a dependent value is read with the earlier fields at their
current contents, as the checker's `depFieldType` reads them through the borrow (`ctorFields`),
not at what a borrow of an earlier field will finally hold (D29, point 5 e). A projected field's
type is the structured type `Sem.follow` gives it (docs/31 D31: the hint the field's declaration
reads it at, with its data, so a value bound from it is decoded by name; it was `.plain`, which
after D31 left such a binding with no declaration to decode it by), with no label. -/
noncomputable def contentOf (p : Place) : SM (Sem × TyS × Pos × List Step) := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let T₀ := s.tyAt pos
    let s := s.access pos (dataHit steps)
    match Sem.follow K.dm K.Γ T₀ (s.valAt pos (s.typedFuture φ)) steps with
    | some (v, T) => some ((v, if steps.isEmpty then s.tyAt pos else { T with label := none }, pos, steps), s)
    | none => none
  | none => none

/-- The scrutinee of a match after [Access] for its tag only (`tagHit`: the borrows lent on the
path and at the place; `tag`: `natTag`, `indTag`): the tag at the typed future (D68), `err` where the
place has none. Borrows inside the scrutinee's fields stay live, as in the checker; an arm that
reads a field accesses it then. -/
noncomputable def tagOf (p : Place) (tag : Sem → TyS → Sem) : SM Sem := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let o := obsAt K (s.tyAt pos) steps tag
    let s := s.access pos (tagHit steps)
    some (o (s.valAt pos (s.typedFuture φ)), s)
  | none => none

/-- Set the content of a place to a constant meaning, pointwise in the future (no access: the
caller has done it). STRICT (the orchestrator's rule, 2026-11-21: every write at a field path ends
with a test over every typed future): the path update is defined at EVERY typed future, not only at
the run's (`Strict/FieldWriteCE`: a move out of a field of a place reading a live label left `err`
at the futures where that label holds no such field). On a state related to a checker state the
definedness does not depend on the future (the access before the write has ended every label read
along the path: the simulation's obligation, `OPEN.md`). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  let T := s.tyAt pos
  let old := s.valAt pos
  if ∀ ψ, TypedFut K φ s ψ → (Sem.updAt K.dm K.Γ T (fun _ => v) steps (old ψ)).isSome then
    some (⟨⟩, s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => v) steps (old φ')).getD .err)
  else none

/-- [Assign]'s write, after the right-hand side ran (the `.assign` clause's tail; the step
statement `assignPlace_step_stmt` is stated against it): [Access] of the part the place OWNS
(D67, `accessInside … owned`: a borrow variable assigned whole owns nothing of its content, so
nothing its content lends is ended; the audit's A2: `c := &(*c).tail` keeps the reborrow it just
made, and the old borrow's end carries its content, loans and all, back to its lender), the old
borrow's end at a root ([Drop]), the write, and at a root the written borrow's hold (`lab`, the
written value's label; WF1: a borrow is the whole value of a position). -/
noncomputable def assignAt (p : Place) (v : Sem) (lab : Option Nat) : SM Res := fun s =>
  match resolve s p with
  | none => none
  | some (pos, steps) =>
    let s := if steps.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit steps)
    let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
    match setContent K φ pos steps v s with
    | none => none
    | some (⟨⟩, s) =>
      let s := match lab, steps with
        | some l, [] => let s := s.takeLabel l; { s with shape := fun q => if q = pos then some l else s.shape q }
        | _, _ => s
      some ((.el0 Unit (), .plain TyM.unit), s)

/-- What a read may return: a member of the type the read gives it (a CLOSED value), or `⋆` or a
type value at `err`. -/
def ReadGood (R : DataRead) (T : TyM) (v : Sem) : Prop :=
  v ∈ₛ[R] T ∨ (T = TyM.err ∧ ((∃ X, v = .ty X) ∨ v = .proof))

/-- [Read]: the content; a copy leaves the place, a move leaves `moved` (D80: by the declared
reading). Reading `⊥`, or a value holding it, is an error. STRICT (the dependent-values unit; the
checker's [Repack] at a read whole): the value read is a member of the type the read gives it
(`ReadGood`): an open value (a tree field at a record its index no longer gives) is not read. -/
noncomputable def readPlace (p : Place) (copy : Bool) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  if ¬ ReadGood K.dm.read T.m v then none else
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

/-- A position holds an open member of its type at every typed future. -/
def PosOk (s : SState) (pos : Pos) : Prop :=
  ∀ ψ, TypedFut K φ s ψ → K.dm.pmem K.Γ (s.valAt pos ψ) (s.tyAt pos).m

/-- Every position holds what the state invariant asks at every typed future: a binding an open
member of its stored type (or no data at `err`), a borrow's holder an open member of its label's
content type. -/
def StateOk (s : SState) : Prop :=
  ∀ ψ, TypedFut K φ s ψ →
    (∀ f i, Pos.bind f i ∈ s.positions →
      K.dm.pmem K.Γ (s.valAt (.bind f i) ψ) (s.tyAt (.bind f i)).m ∨
        ((s.tyAt (.bind f i)).m = TyM.err ∧ ((∃ X, s.valAt (.bind f i) ψ = .ty X) ∨ s.valAt (.bind f i) ψ = .proof))) ∧
    (∀ q l, s.shape q = some l → K.dm.pmem K.Γ (s.valAt q ψ) (s.heldTy l))

/-- STRICT below a root (the dependent-values unit; the checker's tests where lent parts are
unknowns): after a write or a borrow at a field path, and D112's invalidation, every position holds
an open member of its type at every typed future (a write of an index, or a lent index, could leave
a later field outside the type the read gives it; the invalidation's ends pass contents on). A
write or a borrow at a root or through `*` (`[]`, `[*]`) is whole, tested by the clause itself. The
exemption of `[*]` was made when testing it rejected `*x := S(*x)` in `Regress/CallInPlace`; the cause
was the non-recursive `self` bound to `err` (docs/31 D113), now gone, so the test could come back. It
is kept out: from a good state the test at `[*]` always passes (`Strict/OpsPlace` proves the root and
`*` cases from the clause's own membership test), and restoring it means restating the regress runs
through `*`, which are stated over states with an arbitrary `self` or arbitrary meanings (docs/31
D113). -/
def lentOk (p : Place) (s : SState) : Prop :=
  match resolve s p with
  | some (_, steps) => steps = [] ∨ steps = [.deref] ∨ StateOk K φ s
  | none => True

/-- D112 [Open]: a write or a borrow of `p` invalidates the places `Decisions.invalidated` gives:
each accessed ([Access], its borrows end) and set to `⊥` where it exists. -/
noncomputable def invalidateOne (s : SState) (q : Place) : SState :=
  match resolve s q with
  | some (pos, steps) =>
    let s' := s.access pos (dataHit steps)
    match setContent K φ pos steps .moved s' with
    | some (_, s'') => s''
    | none => s'
  | none => s

noncomputable def invalidate (p : Place) (s : SState) : SState :=
  (K.D.invalidated (scopeOf s) p).foldl (invalidateOne K φ) s

/-- STRICT END (ruling (A)): the ends of one invalidated place's access. -/
def InvalOneOk (s : SState) (q : Place) : Prop :=
  match resolve s q with
  | some (pos, steps) => AccessOk K φ s pos (dataHit steps)
  | none => True

/-- STRICT END: every end D112's invalidation makes. -/
def InvalidateOk (p : Place) (s : SState) : Prop :=
  FoldOk (invalidateOne K φ) (InvalOneOk K φ) (K.D.invalidated (scopeOf s) p) s

/-- A place's type: its content's type, read on a discarded copy; `err` where the place does not
resolve. Label-free (`placeTy_label`). The strict assignment tests the value written against it. -/
noncomputable def placeTy (p : Place) (s : SState) : TyS :=
  match contentOf K φ p s with
  | some ((_, T, _, _), _) => .plain T.m
  | none => .plain TyM.err

theorem placeTy_label (p : Place) (s : SState) : (placeTy K φ p s).label = none := by
  unfold placeTy; split <;> rfl

/-- [Borrow] `&p` with a fresh label `l`: the place now reads `l`'s final content at its path, and
the result is the old content, whole, with the label in its type (the holder's position records
it in the shape when the result is bound). -/
noncomputable def borrowPlace (p : Place) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  let (l, s) := s.freshLoan
  let T0 := s.tyAt pos
  let old := s.valAt pos
  let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
  -- the borrow is parked in a temporary, its holder until it is bound (D14)
  let s := s.pushTempShaped (fun _ => v) l
  -- the place is lent to `l`, a plain borrow: one site, its loan (docs/31 D29)
  -- the content it was made from is recorded as the label's member (docs/31 D68)
  some ((v, { T with label := some l }), ((s.setLent l [⟨pos, steps, false⟩]).setHeldTy l T.m).setHeldMem l v)

/-- The borrow flags of a telescope code's parameters along the arguments given (decoded at their
parameters' codes): which arguments are borrowed. -/
noncomputable def telRefsL.{u} (L : Lvl.{u}) : {Fin C : Type u} → Tel L.Code Fin C → List Sem → List Bool
  | _, _, .param _ isRef _ c _ k, a :: as =>
    match L.dec c a with
    | some x => isRef :: telRefsL L (k x) as
    | none => []
  | _, _, .param .., [] => []
  | _, _, .dat .., _ => []
  | _, _, .ref .., _ => []

/-- A call at level `L` (`Apply1.lean`): unpack the callee at its type code's carrier and apply it
along the code (`applyFnL`). The result's type is the code the telescope reaches at the arguments,
so it keeps its whole structure (docs/31 D59: a function returned by a call can be called). -/
noncomputable def callOfL.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args : List Res) :
    SM Res := fun s =>
  let argSems := args.map (·.1)
  -- PROPOSAL (m2-proofs, CE4): the arguments at borrow parameters, in parameter order, one per
  -- final content; only their labels are consumed and fixed. A labelled argument at a non-borrow
  -- parameter keeps its holder (parked), so the next access ends it.
  let refLabels : List (Option Nat) := ((args.zip (telRefsL L t argSems)).filter (·.2)).map (·.1.2.label)
  let fixes (fs : List Sem) : List (Nat × Sem) := (refLabels.zip fs).filterMap fun (l?, f) => l?.map (·, f)
  -- the borrow arguments' holders (parked temporaries) are consumed by the call
  let s := (refLabels.filterMap id).foldl SState.takeLabel s
  match applyFnL L t fv argSems with
  | some (.data r T finals) =>
    let s := s.mapVals fun _ v φ' => v (φ'.updList (fixes finals))
    some ((r, .plain T), s)
  | some (.ref _ c fwd back) =>
    let (k, s) := s.freshLoan
    -- [Lend] (main's D90, rule 1; docs/31 D29): the result is lent every place its borrow
    -- arguments lend, each a fill, whether the checker runs the call or closes it off
    let lentK := ((refLabels.filterMap id).flatMap s.lent).map fun x : Site => { x with fill := true }
    let s := s.mapVals fun _ v φ' =>
      match L.dec c (φ' k) with
      | some x => v (φ'.updList (fixes (back x)))
      -- docs/31 D67: a final content the code does not decode fixes the consumed argument labels to
      -- `err` and leaves the rest of the position as it was (a position that reads no argument label
      -- is then unchanged in both branches, and none reads a consumed argument label after the call)
      | none => v (φ'.updList (fixes (refLabels.map fun _ => .moved)))
    let s := s.pushTempShaped (fun _ => L.enc c fwd) k
    some ((L.enc c fwd, ⟨L.toTy c, some k⟩), ((s.setLent k lentK).setHeldTy k (L.toTy c)).setHeldMem k (L.enc c fwd))
  | none => none

/-- A call, on the evaluated callee and arguments (docs/18 Def. "reference run", first clause):
apply the callee's meaning along its type's code. For a borrow-free result each lent place's final
content is fixed to its component of the finals (the future at the argument's label); for a
result `&U`, a fresh label `k`, the result holds the forward value, and each lent place reads
its component of the backward function at the final content of `k`. A callee whose type is not a
function type, or an ill-typed application, is an error. The guard of a recursive call and a
statement call's copy are the caller's (`run`'s `.call` clause). The level is the code's. -/
noncomputable def callOf (R : DataRead) (fv : Res) (args : List Res) : SM Res := fun s =>
  match fv.2.m with
  | .t0 _ (.pi _ t) => callOfL (lvl0 R) t fv.1 args s
  | .t1 _ (.pi _ t) => callOfL (lvl1 R) t fv.1 args s
  | .t2 _ (.pi _ t) => callOfL (lvl2 R) t fv.1 args s
  | _ => none

/-- [Drop] of the top frame's last binding when it holds no borrow (`Machine.endLoansOfTopBind`,
D65 amended): the borrows lent at it end, as [Access] of it whole would end them. -/
noncomputable def letLenders (s : SState) : SState :=
  match s.env.getLast? with
  | some fr => s.access (.bind s.topIdx (fr.binds.length - 1)) (dataHit [])
  | none => s

/-- [Drop] of a discarded value (`Machine.dropValue`): a borrow the result holds (its label) ends;
a value that is not a borrow holds no loan in the reference (a read accessed it). -/
noncomputable def discardEnd (R : TyS) (s : SState) : SState :=
  match R.label with
  | some l => s.endLabel l
  | none => s

/-- STRICT END: the end of a let's binding when it holds no borrow (`letLenders`'s access). -/
def LetLendersOk (s : SState) : Prop :=
  match s.env.getLast? with
  | some fr => AccessOk K φ s (.bind s.topIdx (fr.binds.length - 1)) (dataHit [])
  | none => True

/-- STRICT END: a discarded value's borrow. -/
def DiscardOk (R : TyS) (s : SState) : Prop :=
  match R.label with
  | some l => EndOk K φ s l
  | none => True

/-- The shortest strict prefix of `steps` at which a live label has a site at `pos`: where the
checker's path stops at a lent part (`Machine.movedPlace`: a place under a loan or a sealed fill
does not exist, and its longest existing prefix, a fill, is accessed whole). Sites are matched by
key (`*` erased, docs/31 D67), so a prefix that differs from the place by `*`s only may be the one
found; accessing it whole is then accessing the place (`DropOne.lentPrefix_absorbed`). -/
def lentPrefix (s : SState) (pos : Pos) (steps : List Step) : Option (List Step) :=
  ((List.range steps.length).map steps.take).find? fun ψ =>
    s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey ψ)

/-- `movedPlace`'s access of a lent prefix: the shortest strict prefix of the dropped place that
holds a site of a live label, accessed whole (docs/31 D29, point 5 f). -/
noncomputable def accessLentPrefix (pos : Pos) (steps : List Step) (s : SState) : SState :=
  match lentPrefix s pos steps with
  | some ψ => s.access pos (dataHit ψ)
  | none => s

/-- `Machine.dropAtJoin` of one place, at `(pos, steps)`: a borrow at a root, its end; a copy,
nothing; where the write cannot be made (the place is missing, or the path passes through a proof
or a moved part by a field step), nothing; otherwise [Access] and `moved`. The holder is tested first, by the
shape, as the checker tests its stored value: a holder's meaning is its content's, which reads
`moved` when the content was moved out through the borrow (D53 (h)), and the checker ends that
borrow too (docs/31 D42). A place already moved is accessed and written `moved` like any other
(docs/31 D52, the lead's (B)): the access finds nothing there ((WF14)) and the write is the
identity, where the checker does nothing; deciding it by reading `moved` from the meaning disagreed
with the checker wherever data means `moved` (a loan whose borrow's content was moved out, ended
inside an observation, D68). The place is read as every read of a place reads it (`contentOf`,
`tagOf`): after its [Access], at the typed future (docs/31 D54, D68); the access is kept only where
the place is then dropped. Read before the access, the reading was at a state no checker state is
related to (the checker reads the place, then accesses it; the reference had accessed the lent
prefix already), and relating it needed the reading to be unchanged by an access.

No test of the meaning at the place (the slice, 2026-11-20, the orchestrator's decision): a place
the shared copy decision does not call a copy is accessed and written `moved` whatever the model
reads there, and nothing is done exactly where the write cannot be made at EVERY typed future
(the orchestrator's write rule, 2026-11-21; `Sem.updAt` fails: the path passes by a field step
through a part with no fields, a proof or a moved part, which is where the checker's `movedPlace`
re-roots to a `⊥` or `⋆` prefix and does nothing; on related states the definedness does not depend
on the future, the simulation's obligation in `OPEN.md`).
It used to do nothing where the place read `⋆`, mirroring the checker's "a proof: nothing" test on
its own stored value; the two tests agree only if the checker holds `⋆` exactly where the model
reads `⋆`, which is the typing of the whole state (sort soundness, the typing of reads, open values,
the typing of sealed programs). Since main's D100 every place holding its own `⋆` is a copy
(`ShapeFacts.proofCopy`), so the checker's test is dead on related states, and with it the drop
needs no typing fact. -/
noncomputable def dropAt (q : Place) (pos : Pos) (steps : List Step) (s : SState) : SState :=
  match steps, s.shape pos with
  | [], some l => s.endLabel l
  | _, _ =>
    let s' := s.access pos (dataHit steps)
    if K.D.copy (K.D.placeDecl (scopeOf s) q) then s else
    -- the orchestrator's rule (2026-11-21): the write is made only where it is defined at EVERY typed
    -- future (on a state related to a checker state, exactly where it is defined at the run's)
    if ∀ ψ, TypedFut K φ s' ψ → (Sem.updAt K.dm K.Γ (s'.tyAt pos) (fun _ => .moved) steps (s'.valAt pos ψ)).isSome then
      s'.setAt pos fun φ' => (Sem.updAt K.dm K.Γ (s'.tyAt pos) (fun _ => .moved) steps (s'.valAt pos φ')).getD .err
    else s

/-- D84, the drop at the join, as the checker does it (`Machine.joinDrop`: `movedPlace`, then
`dropAtJoin`), for every place some arm of the match moves (`Decisions.joinMoves`, static, given
the places already moved at entry, read before the arm ran: the audit's A6):
- a place under a lent part is reached as the arm that moves out of it reaches it: the shortest
  lent prefix is accessed whole (`movedPlace`'s fill branch; docs/31 D29, point 5 f);
- a place that is missing, moved or a proof is left alone;
- a borrow held at a dropped root ends, and nothing it lends is accessed (D28 item 1: accessing
  it first ended a reborrow of part of its content, which the checker keeps live);
- a place whose declared reading is copy is left alone;
- anything else is accessed (static) and set to `moved`.
At a root this is below the state before; at a field place it is a real change, so the match
step lemma is stated exact against the checker's drop. -/
noncomputable def joinDrop (entry : List Place) (t : Term) (s : SState) : SState :=
  (K.D.joinMoves (scopeOf s) entry t).foldl (fun s q =>
    match resolve s q with
    | some (pos, steps) => dropAt K φ q pos steps (accessLentPrefix pos steps s)
    | none => s) s

/-- STRICT END: the access of a lent prefix. -/
def LentPrefixOk (pos : Pos) (steps : List Step) (s : SState) : Prop :=
  match lentPrefix s pos steps with
  | some ψ => AccessOk K φ s pos (dataHit ψ)
  | none => True

/-- STRICT END: the drop of one place: a borrow at a root ends; otherwise the access, where it is
kept (no copy, and the write made). -/
def DropOk (q : Place) (pos : Pos) (steps : List Step) (s : SState) : Prop :=
  match steps, s.shape pos with
  | [], some l => EndOk K φ s l
  | _, _ =>
    K.D.copy (K.D.placeDecl (scopeOf s) q) = false →
    (∀ ψ, TypedFut K φ (s.access pos (dataHit steps)) ψ →
      (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
        ((s.access pos (dataHit steps)).valAt pos ψ)).isSome) →
    AccessOk K φ s pos (dataHit steps)

/-- STRICT END: one step of the join's drop. -/
def JoinStepOk (s : SState) (q : Place) : Prop :=
  match resolve s q with
  | some (pos, steps) => LentPrefixOk K φ pos steps s ∧ DropOk K φ q pos steps (accessLentPrefix pos steps s)
  | none => True

/-- STRICT END: every end the join's drop makes. -/
def JoinDropOk (entry : List Place) (t : Term) (s : SState) : Prop :=
  FoldOk (fun s q => match resolve s q with
    | some (pos, steps) => dropAt K φ q pos steps (accessLentPrefix pos steps s)
    | none => s) (JoinStepOk K φ) (K.D.joinMoves (scopeOf s) entry t) s

/-- `movedPlace`'s access while a block's captures are computed: the lent prefix, accessed whole. -/
noncomputable def entryReroot (s : SState) (q : Place) : SState := match resolve s q with
  | some (pos, steps) => accessLentPrefix pos steps s
  | none => s

/-- A capture's access at a block's entry (`Machine.entryAccess`), as data. -/
noncomputable def entryCap (s : SState) (qk : Place × Nat) : SState :=
  let s := match resolve s qk.1 with
    | some (pos, steps) => s.access pos (dataHit steps)
    | none => s
  -- D112: a capture by `&` invalidates as a borrow does
  if qk.2 == 1 then invalidate K φ qk.1 s else s

/-- D90 [Entry] (static ends, rule 2): a non-tail match on a known constructor, and `J`'s
transported term, first do what the stuck block they would close off does at its entry
(`Machine.blockEntry`): `movedPlace`'s accesses of the places K1 re-roots (the reference's
`accessLentPrefix`, as at the join), then each capture accessed as data, in the block's order
(`entryAccess`: `accessPath`, and `accessInside` where the place exists; below a moved part nothing
is lent, so the reference's data access ends the same). `bc` is `Decisions.blockCaps`. -/
noncomputable def entryAccess (bc : List Place × List (Place × Nat)) (s : SState) : SState :=
  bc.2.foldl (entryCap K φ) (bc.1.foldl entryReroot s)

/-- STRICT END: one re-rooted place's access at an entry. -/
def EntryRerootOk (s : SState) (q : Place) : Prop :=
  match resolve s q with
  | some (pos, steps) => LentPrefixOk K φ pos steps s
  | none => True

/-- STRICT END: one capture's access at an entry, and its invalidation for a capture by `&`. -/
def EntryCapOk (s : SState) (qk : Place × Nat) : Prop :=
  (match resolve s qk.1 with
    | some (pos, steps) => AccessOk K φ s pos (dataHit steps)
    | none => True) ∧
  (qk.2 == 1 → InvalidateOk K φ qk.1 (match resolve s qk.1 with
    | some (pos, steps) => s.access pos (dataHit steps)
    | none => s))

/-- STRICT END: every end [Entry] makes. -/
def EntryAccessOk (bc : List Place × List (Place × Nat)) (s : SState) : Prop :=
  FoldOk entryReroot (EntryRerootOk K φ) bc.1 s ∧
    FoldOk (entryCap K φ) (EntryCapOk K φ) bc.2 (bc.1.foldl entryReroot s)

/-- The sites, as fills, of the borrows a block takes by move (`joinEnds`' marks for its
reserved label, made after the entry and before the arm). -/
noncomputable def entrySnapshot (bc : List Place × List (Place × Nat)) (s : SState) : List Site :=
  bc.2.flatMap fun qk => if qk.2 == 2 then
    match resolve s qk.1 with
    | some (pos, []) => match s.shape pos with
      | some j => (s.lent j).map fun x => { x with fill := true }
      | none => []
    | _ => []
  else []

/-- After the arm and the join of a borrow-typed non-tail match (`joinEnds`): the result's label
is lent, as fills, the places the block takes by `&` and the snapshot (its reserved label's marks,
handed to the result by `LendOp.ended g [k]`). -/
noncomputable def entryLend (bc : List Place × List (Place × Nat)) (snap : List Site) (lab : Option Nat)
    (s : SState) : SState :=
  match lab with
  | some k => s.setLent k (s.lent k ++ (bc.2.filterMap fun qk => if qk.2 == 1 then
      (resolve s qk.1).map fun ps => ({ pos := ps.1, path := ps.2, fill := true } : Site) else none) ++ snap)
  | none => s

/-- A proof's meaning, `⋆`. -/
def Sem.isProof : Sem → Bool
  | .proof => true
  | _ => false

/-- D93: the declaration named `n` has exactly one constructor (`Machine.evalMatchInd`'s
`(← lookupInd ty).ctors.length == 1`, read from the match term's declaration name). -/
def oneCtor (Γ : List IndDecl) (n : String) : Bool :=
  match Γ.find? (·.name == n) with
  | some d => d.ctors.length == 1
  | none => false

/-- A declared reading that is a borrow type. -/
def isRefDecl : DeclInfo → Bool
  | .ref _ => true
  | _ => false

/-- **[Entry] at a match** (`Machine.joinEnds`), when `ent` (not in tail position, not on a
proof): the state after the entry, and the lending to apply after the arm and the join to the
result's label (nothing unless the match's declared type is a borrow). The captures are read at
the match's start, with the places then moved (`movedPlaces`), as `blockEntry`'s `staticJoin`. -/
noncomputable def matchEntry (ent : Bool) (mt : Term) (s : SState) : SState × (Option Nat → SState → SState) :=
  if ent then
    let bc := K.D.blockCaps (scopeOf s) (movedPlaces φ s) mt
    let s₁ := entryAccess K φ bc s
    (s₁, fun lab s₂ => if isRefDecl (K.D.declOf (scopeOf s₁) mt) then entryLend bc (entrySnapshot bc s₁) lab s₂ else s₂)
  else (s, fun _ s₂ => s₂)

/-- STRICT END: [Entry]'s ends, when it is made. -/
def MatchEntryOk (ent : Bool) (mt : Term) (s : SState) : Prop :=
  ent = true → EntryAccessOk K φ (K.D.blockCaps (scopeOf s) (movedPlaces φ s) mt) s

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

/-- The values [Obs-ref] writes are of the re-pointed bindings' content types: one for each, a
member of the type its binding is declared at (a borrow binding's type is its content's). The
checker writes a fresh unknown of the borrowed type (`Machine.idType`: `absAt … T'`), which under
every assignment is every MEMBER of it. As first written `Id` ranged over every meaning, typed or
not, and was false where the checker's is true: two sides that re-point a borrow of a `Unit` at
different places (docs/31 D26, `Regress/IdUnitWrite.lean`). -/
def obsTyped (R : DataRead) (reps : List Place) (ws : List Sem) (s : SState) : Prop :=
  ws.length = reps.length ∧
  ∀ (i : Nat) (q : Place) (w : Sem), reps[i]? = some q → ws[i]? = some w →
    match resolve s q with
    | some (pos, _) => w ∈ₛ[R] (s.tyAt pos).m
    | none => True

/-- Insert into a list sorted largest first. Structurally recursive, so the kernel evaluates it on
concrete terms (a library sort defined by well-founded recursion does not reduce under `rfl`/`decide`). -/
def capInsert (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if i > j then i :: j :: js else j :: capInsert i js

/-- The variables a closure captures, oldest binding first (`Machine.capture`'s order: the
largest de Bruijn index first). An insertion sort of `freeVars` (which has no duplicates, so the
descending order is unique: this is the order `Array.qsort (· > ·)` gave before, rebuilt
structurally so that membership is provable, `mem_capOrder`). -/
def capOrder (t : Term) : List Nat := t.freeVars.foldl (fun acc i => capInsert i acc) []

theorem mem_capInsert (x i : Nat) (l : List Nat) : x ∈ capInsert i l ↔ x = i ∨ x ∈ l := by
  induction l with
  | nil => simp [capInsert]
  | cons j js ih =>
    unfold capInsert
    split
    · simp
    · simp only [List.mem_cons, ih, or_left_comm]

theorem mem_foldl_capInsert (x : Nat) (l acc : List Nat) :
    x ∈ l.foldl (fun acc i => capInsert i acc) acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons j js ih =>
    rw [List.foldl_cons, ih, mem_capInsert]; simp only [List.mem_cons, or_assoc, or_left_comm]

/-- Every captured index is a free variable of the term, and conversely. -/
theorem mem_capOrder (t : Term) (i : Nat) : i ∈ capOrder t ↔ i ∈ t.freeVars := by
  rw [capOrder, mem_foldl_capInsert]; simp

/-- One capture of a closure being formed (`Machine.capture`): the variable is accessed, then
moved unless its declared reading is copy (D80). -/
noncomputable def capStep (s : SState) (i : Nat) : SState := match s.varPos i with
  | some pos =>
    let s := s.access pos (dataHit [])
    if K.D.copy (K.D.placeDecl (scopeOf s) (.var i)) then s else s.setAt pos fun _ => .moved
  | none => s

/-- STRICT END: one capture's access when a closure is formed. -/
def CapOk (s : SState) (i : Nat) : Prop :=
  match s.varPos i with
  | some pos => AccessOk K φ s pos (dataHit [])
  | none => True

/-- The content types of the borrow parameters a telescope code reaches at the arguments, in order
(`[]` past an argument that does not decode). -/
noncomputable def telRefTysL.{u} (L : Lvl.{u}) : {Fin C : Type u} → Tel L.Code Fin C → List Sem → List TyM
  | _, _, .param _ isRef _ c _ k, a :: as =>
    match L.dec c a with
    | some x => (if isRef then [L.toTy c] else []) ++ telRefTysL L (k x) as
    | none => []
  | _, _, _, _ => []

/-- STRICT (D83): fail unless the result is a member of the type it is given. -/
noncomputable def SM.strictS (R : DataRead) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  match x s with
  | some (r, s') => if r.1 ∈ₛ[R] r.2.m then some (r, s') else none
  | none => none

/-- A result's label, if any, has the given content type in the state. -/
def labTyOk (s : SState) (lab : Option Nat) (T : TyM) : Prop := ∀ l, lab = some l → s.heldTy l = T

/-- STRICT Π-type ("well typed inside", the trial's clause 5): every domain and the codomain have a
level at every tuple of arguments that are members of the domains before them (an error domain
used to give the function type over the empty carrier, which has a level and one member). -/
def PiOk (R : DataRead) : List PiDom → List Sem → PiCod → Prop
  | [], acc, out => (out.cod acc).level.isSome = true
  | p :: ps, acc, out => (p.dom acc).level.isSome = true ∧ ∀ a, a ∈ₛ[R] p.dom acc → PiOk R ps (acc ++ [a]) out

/-- STRICT captures (the trial's clause 7): a closure's or Π-closure's captured values are members of
their recorded types, one for each. The recorded readings may run on past the captures: a stuck
block's closure keeps its PARAMETERS' readings there (`Syntax.lean`'s `Value.clo`; the checker reads
them as `rd.drop caps.length`), which this test does not read (docs/31 D137, ruling (A)). -/
def CapsOk (R : DataRead) : List Sem → List (DeclInfo × TyS) → Prop
  | [], _ => True
  | v :: vs, (_, T) :: ts => v ∈ₛ[R] T.m ∧ CapsOk R vs ts
  | _ :: _, [] => False

/-- The borrow flags of a function type's parameters along the arguments (`telRefsL` at its level). -/
noncomputable def refsOf (R : DataRead) (T : TyM) (as : List Sem) : List Bool :=
  match T with
  | .t0 _ (.pi _ t) => telRefsL (lvl0 R) t as
  | .t1 _ (.pi _ t) => telRefsL (lvl1 R) t as
  | .t2 _ (.pi _ t) => telRefsL (lvl2 R) t as
  | _ => []

/-- The content types of a function type's borrow parameters along the arguments (`telRefTysL`). -/
noncomputable def refTysOf (R : DataRead) (T : TyM) (as : List Sem) : List TyM :=
  match T with
  | .t0 _ (.pi _ t) => telRefTysL (lvl0 R) t as
  | .t1 _ (.pi _ t) => telRefTysL (lvl1 R) t as
  | .t2 _ (.pi _ t) => telRefTysL (lvl2 R) t as
  | _ => []

/-- The labels of the arguments at borrow parameters, in parameter order (`callOfL`'s `refLabels`). -/
noncomputable def refLabelsOf (R : DataRead) (fv : Res) (args : List Res) : List (Option Nat) :=
  ((args.zip (refsOf R fv.2.m (args.map (·.1)))).filter (·.2)).map (·.1.2.label)

/-- STRICT at a call: each borrow argument's label is live (a borrow ended before the call, by a later
argument's access of its lender, is not passed) and holds the content type of the parameter it is
passed at (a borrow is invariant: the callee's final content, a member of the parameter's type,
becomes what the lender reads). -/
def BorrowArgsTyped (R : DataRead) (fv : Res) (args : List Res) (s : SState) : Prop :=
  ∀ (i l : Nat), (refLabelsOf R fv args)[i]? = some (some l) →
    l ∈ s.liveLabels ∧ s.heldTy l = (refTysOf R fv.2.m (args.map (·.1))).getD i TyM.err

/-- STRICT `.val` (D83 row 8): a constructor value must be a member of the type its record names;
embedded code (a closure, a sealed program) whose strict meaning is `err` fails (the orchestrator's
ruling, consistently with strict `.fix`); any other value is typed as before. Written as a function
of the value so that each constructor's case reduces by `rfl`.

A constructor value whose meaning is `err` (its declaration or its record unknown) fails outright,
as embedded code does, rather than being tested at the type the run falls back to (the hint): the
test would read the hint, and a run whose tails read no hint must not (`HintIndep`). In a model whose
reading gives whole meanings nothing changes, since `err` is a member of no type there. -/
noncomputable def strictVal (R : DataRead) : Value → Res → SM Res
  | .ind .., r => fun s => if r.1 = .err then none else SM.strictS R (pure r) s
  -- embedded code whose strict meaning is an error (its strict run failed) fails, as strict `.fix`
  | .clo .., r | .sealed _, r => fun s => if r.1 = .err then none else some (r, s)
  | _, r => pure r

/-- A constructor value's result once its record is known (docs/34 §14): the tree at the record,
or `•` for a `Prop`-sorted declaration (D42), at the declaration's type there; no record, no
value. -/
def ctorOut (dm : DataModel) (d : IndDecl) (c : Nat) (fs : List Sem) : Option Rec → SM Res
  | some r => pure (if d.sort == 0 then .proof else DataModel.ctorR d r c fs, .plain (dm.tyR d r))
  | none => SM.fail

theorem ctorOut_inv {dm : DataModel} {d : IndDecl} {c : Nat} {fs : List Sem} {r? : Option Rec}
    {s s' : SState} {r : Res} (h : ctorOut dm d c fs r? s = some (r, s')) :
    s' = s ∧ ∃ rr, r? = some rr ∧
      r = (if d.sort == 0 then .proof else DataModel.ctorR d rr c fs, .plain (dm.tyR d rr)) := by
  cases r? with
  | none => cases h
  | some rr =>
    simp only [ctorOut, pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, rr, rfl, h.1.symm⟩

/-- A test in an `Option` computation at any universe (STRICT END, ruling (A)). -/
noncomputable def optCheck.{u} (P : Prop) : Option PUnit.{u+1} := if P then some ⟨⟩ else none

/-- A computation run only where `ok` holds of the state it starts from (STRICT END, ruling (A)). -/
noncomputable def SM.guarded {α : Type 3} (ok : SState → Prop) (x : SM α) : SM α := fun s =>
  if ok s then x s else none

/-- A state change made only where `ok` holds of the state it starts from (STRICT END, ruling (A)). -/
noncomputable def SM.guardMod (ok : SState → Prop) (f : SState → SState) : SM PUnit := fun s =>
  if ok s then some (⟨⟩, f s) else none

theorem SM.guarded_some {α : Type 3} {ok : SState → Prop} {x : SM α} {s : SState} {r : α × SState}
    (h : SM.guarded ok x s = some r) : ok s ∧ x s = some r := by
  unfold SM.guarded at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

theorem SM.guarded_of {α : Type 3} {ok : SState → Prop} {x : SM α} {s : SState} (h : ok s) :
    SM.guarded ok x s = x s := by
  unfold SM.guarded; rw [if_pos h]

theorem SM.guarded_congr {α : Type 3} {ok ok' : SState → Prop} {x x' : SM α} {s : SState}
    (hok : ok s ↔ ok' s) (hx : x s = x' s) : SM.guarded ok x s = SM.guarded ok' x' s := by
  unfold SM.guarded; rw [propext hok, hx]

theorem SM.guardMod_some {ok : SState → Prop} {f : SState → SState} {s s' : SState} {u : PUnit}
    (h : SM.guardMod ok f s = some (u, s')) : ok s ∧ s' = f s := by
  unfold SM.guardMod at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨‹_›, h.2.symm⟩
  · cases h

theorem SM.guardMod_of {ok : SState → Prop} {f : SState → SState} {s : SState} (h : ok s) :
    SM.guardMod ok f s = some (⟨⟩, f s) := by
  unfold SM.guardMod; rw [if_pos h]

theorem SM.guardMod_congr {ok ok' : SState → Prop} {f : SState → SState} {s : SState} (hok : ok s ↔ ok' s) :
    SM.guardMod ok f s = SM.guardMod ok' f s := by
  unfold SM.guardMod; rw [propext hok]

theorem optCheck_congr.{u} {P Q : Prop} (h : P ↔ Q) : optCheck.{u} P = optCheck.{u} Q := by
  rw [propext h]

theorem optCheck_some.{u} {P : Prop} {x : PUnit.{u+1}} (h : optCheck.{u} P = some x) : P := by
  unfold optCheck at h; split at h
  · assumption
  · cases h

theorem optCheck_of.{u} {P : Prop} (h : P) : optCheck.{u} P = some ⟨⟩ := by
  unfold optCheck; rw [if_pos h]

/-! ## The hints the TYPED checker hands (docs/31 D119)

The reference hands a sub-term an expected type exactly where the checker that CHECKS (`eval` with
`typed`, which `checkDef` runs) hands one: no hint to a `let`'s or a `;`'s tail, to a match's arms
or to `J`'s transported term; the place's type to an assignment's right-hand side, the parameter's
type to an argument and the field's type to a field only at the syntactic forms below. The untyped
checker (an in-place call's body, a sealed program's re-run) leaves hints out where it checks
nothing, and a strict constructor with no record fails, so the reference does not follow it. -/

/-- `evalCore`'s `.assign`: a constructor or an embedded value. -/
def _root_.Ochr.Term.assignHinted : Term → Bool
  | .ctor .. | .val _ => true
  | _ => false

/-- `evalCall`'s argument hint: a constructor, an embedded value, `rewrite`, `rewriteR`, a hole. -/
def _root_.Ochr.Term.argHinted : Term → Bool
  | .ctor .. | .val _ => true
  | .prim n _ => n == "rewrite" || n == "rewriteR" || n == "hole"
  | _ => false

/-- `evalCtor`'s field hint `fh`: a constructor, `rewrite` or `rewriteR` of a declaration with
parameters, an embedded value, or any field of a dependent constructor that its index fields type. -/
def _root_.Ochr.Term.fieldHinted (a : Term) (d : IndDecl) (c i : Nat) : Bool :=
  (decide (0 < d.params.length) && (match a with
    | .ctor .. => true
    | .prim n _ => n == "rewrite" || n == "rewriteR"
    | _ => false)) ||
  (match a with | .val _ => true | _ => false) ||
  (d.dependent c && d.fieldDependent c i)

/-- **The hint a sequencing form hands its tail or arm** (docs/31 D151's ruling (d), built in D156): in tail
position (`tl`) its own, as the checker's tail check (`checkTail`) hands the goal to a `let`'s tail, a
sequence's tail and a match's arms; out of tail position none, as the typed `eval` hands none (D119). -/
def tailHint (tl : Bool) (hint : TyS) : TyS := if tl then hint else .plain TyM.err

@[simp] theorem tailHint_true (hint : TyS) : tailHint true hint = hint := rfl
@[simp] theorem tailHint_false (hint : TyS) : tailHint false hint = .plain TyM.err := rfl

mutual


/-- The reference run of a term at the future `φ`, at the type `hint` its context expects, in
tail position when `tl` (D90's tail flag, docs/31 D29 point 2). A term is in tail position when it
is a function's body (the `.fix` clause's body run), or a tail's `let` body, sequence tail, match
arm, or the one arm of a match on a proof: exactly where the checker's `checkTail` recurses and
its untyped runs carry `MState.tailNext` (`runBody`, `evalCore`'s `.letIn` and `.seq`,
`evalMatch`'s arms, `evalMatchByType`'s one arm). Everything else, `J`'s transported term and a
sealed program's re-run included, is not; a constant's body is run by `eval`, not `checkTail`,
so it is not either. -/
noncomputable def runT (tl : Bool) (hint : TyS) : Term → SM Res
  -- C1: a proof read at a place is read, on a copy, at the place's type
  | .place p => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.place p))
      (SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)))) s
  -- STRICT: the borrowed content is a member of its type (a borrow's record is a member)
  | .borrow p => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.borrow p)) (fun s =>
      match SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
      | some (r, s₁) =>
        -- D112: the borrow invalidates; STRICT below a root: the lender stays an open member
        let s₂ := invalidate K φ p s₁
        if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
      | none => none) s
  | .assign p u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.assign p u)) (fun s => do
    -- the right-hand side runs BEFORE the place is accessed (`evalCore`'s `.assign`, then
    -- `assignPlace`; D19, R5: accessing first ended the borrows the right-hand side reads
    -- through, `y := clone(*r)` with `r` borrowing `y`). The place's type, the hint of the
    -- right-hand side, is read on a discarded copy
    -- the hint, as the TYPED checker hands it (`evalCore`'s `.assign`: `placeType?` iff `u` is a
    -- constructor or an embedded value; docs/31 D119)
    let T : TyS := if u.assignHinted then (match contentOf K φ p s with
      | some ((_, T, _, _), _) => T
      | none => .plain .err) else .plain .err
    let ((v, R), s) ← runT false T u s
    -- STRICT: the value written is a member of the place's type at the write (read on a
    -- discarded copy, `placeTy`; the hint `T` was read before the right-hand side ran)
    if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
      match SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) s with
      | some (r, s₁) =>
        -- D112: the write invalidates; STRICT below a root: the position stays an open member
        let s₂ := invalidate K φ p s₁
        if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
      | none => none
    else none) s
  | .letIn x u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.letIn x u w)) (fun s => do
    -- the binding's reading is read BEFORE `u` runs, as the checker reads it (`evalCore`'s
    -- `.letIn`: `declOf` under `withLive`, then `eval u`; docs/31 D118): `u` may write, and a
    -- reading taken after it would be of a scope the checker never read
    let d := K.D.declOf (scopeOf s) u
    let ((v, T), s) ← runT false (.plain TyM.err) u s
    let s := pushBindShaped s { ty := T, val := fun _ => v, decl := d }
    -- the tail runs with no hint, as the TYPED checker runs it (`evalCore`'s `.letIn`; docs/31 D119),
    -- except in tail position, where it runs at the `let`'s own (`checkTail`'s `.letIn`; D156)
    let ((r, R), s) ← runT tl (tailHint tl hint) w s
    -- [Drop] of the binding: the borrow it holds *now* ends, then it is forgotten (PROPOSAL,
    -- m2-proofs, CE5: not the label its type carried when it was bound, which it may have moved
    -- out, while an assignment may have made it the holder of another)
    let held : Option Nat := match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none
    -- a binding holding no borrow ends the borrows lent at it (D65, `endLoansOfTopBind`: the
    -- non-lexical reading; docs/31 D29: the checker ends them, so the reference must)
    -- STRICT END (ruling (A))
    if (match held with | some l => EndOk K φ s l | none => LetLendersOk K φ s) then
      let s := match held with | some l => s.endLabel l | none => letLenders s
      some ((r, R), s.dropLast)
    else none) s
  | .seq u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.seq u w)) (do
    -- [Drop] of a discarded value (`Machine.dropValue`): a borrow it holds ends now, as the
    -- checker ends it (docs/31 D29: the two hold the same live borrows at every point; it used
    -- to stay parked until an access depended on it, an early end of the checker's)
    let r ← runT false (.plain TyM.err) u
    -- STRICT END (ruling (A))
    SM.guardMod (DiscardOk K φ r.2) (discardEnd r.2)
    -- the tail runs with no hint, as the TYPED checker runs it (docs/31 D119), except in tail
    -- position, where it runs at the sequence's own (`checkTail`'s `.seq`; D156)
    runT tl (tailHint tl hint) w) s
  | .matchNat p z u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchNat p z u)) (fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access] for the tag: the
    -- audit's A1); `⊥` is an error; then D84's drop at the join
    let (tg, s) ← SM.guarded (TagOk K φ p) (tagOf K φ p natTag) s
    -- D90 [Entry]: not in tail position, the stuck block's captures are accessed first, and a
    -- borrow-typed match's result is lent what the block's would be (`matchEntry`)
    -- STRICT END (ruling (A)): [Entry]'s ends, and the join's
    let _ ← optCheck (MatchEntryOk K φ (!tl) (.matchNat p z u) s)
    let (s, lend) := matchEntry K φ (!tl) (.matchNat p z u) s
    let entry := movedPlaces φ s
    match tg.asNat with
    | some 0 => do
      let ((r, R), s) ← runT tl (tailHint tl hint) z s
      let _ ← optCheck (JoinDropOk K φ entry (.matchNat p z u) s)
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | some (_ + 1) => do
      let ((r, R), s) ← runT tl (tailHint tl hint) u s
      let _ ← optCheck (JoinDropOk K φ entry (.matchNat p z u) s)
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | none => none) s
  | .matchInd p n arms => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchInd p n arms)) (fun s => do
    let (tg, s) ← SM.guarded (TagOk K φ p) (tagOf K φ p indTag) s
    -- D93: a match on a type with one constructor never closes off, so it has no entry and no
    -- join, on any path (`Machine.evalMatchInd`: its one arm runs directly)
    let one := oneCtor K.Γ n
    -- D90 [Entry], not in tail position, not on a proof (`evalMatchByType` has none), and not on a
    -- one-constructor type (D93)
    -- STRICT END (ruling (A)): [Entry]'s ends, and the join's
    let _ ← optCheck (MatchEntryOk K φ (!tl && !tg.isProof && !one) (.matchInd p n arms) s)
    let (s, lend) := matchEntry K φ (!tl && !tg.isProof && !one) (.matchInd p n arms) s
    let entry := movedPlaces φ s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match tg with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => tg.asNat
    match c? with
    | some c => do
      -- an arm runs with no hint, as the TYPED checker runs it (docs/31 D119), except in tail
      -- position, where it runs at the match's own (`checkTail`'s matches; D156)
      let ((r, R), s) ← runArm tl (tailHint tl hint) c arms s
      let _ ← optCheck (tg.isProof = true ∨ one = true ∨ JoinDropOk K φ entry (.matchInd p n arms) s)
      -- a match on a proof has no join (`Machine.evalMatchByType`: its one arm runs on every
      -- path; the audit's A4)
      some ((r, R), match tg with
        | .proof => s
        | _ => if one then s else lend R.label (joinDrop K φ entry (.matchInd p n arms) s))
    -- an erased match on a proof with other than one arm: the arms on copies (`SM.anyArm`)
    | none => match tg with
      | .proof => SM.anyArm arms.length (fun c => runArm tl (tailHint tl hint) c arms) s
      | _ => none) s
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      -- the type value is the declaration's code at the parameters (docs/31 D59)
      -- STRICT: each argument is a member of its parameter type
      fun s => if paramsOk K.dm d psM then some ((.ty (K.dm.tyM d psM), .plain (TyM.univ d.sort)), s) else none
    | none => SM.fail
  | .ctor ty c x ps args => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ctor ty c x ps args)) (do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      -- the record known before the fields: the written parameters' (none, for a declaration
      -- without parameters), or the hint's (`evalCtor`'s `sol`; docs/34 §14: a code keeps a
      -- record, not parameters); otherwise the fields' types solve the parameters (`runFields`;
      -- the audit's A9)
      let rh : Option Rec := if !ps.isEmpty || d.params.isEmpty then some (K.dm.recOf d psM) else
        match hint.data with
        | some (n, r) => if n = ty then some r else none
        | none => none
      let sol₀ : List (Option Sem) := if !ps.isEmpty then psM.map some else List.replicate d.params.length none
      -- a constructor of a Prop-sorted inductive is a proof, `⋆` (D42); its arguments are
      -- statement positions, each on its own copy (`stmtArgIf`; D19, R4)
      let (fs, sol) ← runFields (d.sort == 0) d c 0 rh sol₀ [] args
      -- STRICT: the value built is a member of the type it is given (`ctorOut_mem`: fields that fit)
      -- STRICT: written parameters are members of their types
      fun s => if ps.isEmpty ∨ paramsOk K.dm d psM then
        SM.strictS K.dm.read (ctorOut K.dm d c fs (rh <|> (if sol.all (·.isSome) then some (K.dm.recOf d (solved sol)) else none))) s
      else none
    | none => SM.fail) s
  | .const n => pure (K.C.global n)
  | .val v => fun s =>
    -- an embedded value at the type it is, as the checker types it (`valType?`): a number at
    -- `Nat`, `()` at `Unit`, a constructor value at the type its record names (the record its
    -- meaning carries: the written parameters', or the hint's for a bare one), a closure at its
    -- own type (its code, from its term in its captures' frame), an unknown at its type in Δ;
    -- anything else at the hint
    let T : TyS := match v with
      | .zero | .succ _ => .plain TyM.nat
      | .unit => .plain TyM.unit
      | .ind ty _ _ ps _ => match K.Γ.find? (·.name == ty) with
        | some d =>
          let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
              (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
            else some (K.dm.recOf d (meanParams d 0 [] ps))
          match r? with
          | some r => .plain (K.dm.tyR d r)
          | none => hint
        | none => hint
      | .clo caps t rd => match runT false (.plain TyM.err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
        | some ((_, R), _) => R
        | none => hint
      | .gfn n => (K.C.global n).2
      | .abs σ => K.Δ σ
      -- P1 (PROPOSAL, m2-proofs): a loan of a function carries its declared type (`K.Λ`), as its
      -- filler will
      | .loan l => if (K.Λ l).m.isPi then K.Λ l else hint
      -- a sealed callee (D39: the checker calls a sealed function value) is typed as its
      -- program's result where that is a function (the spine's finding at the general
      -- closeCall_step, docs/31 item 3); its labels are its own
      | .sealed t => match runT false hint t (emptyState 0) with
        | some ((_, R), _) => if R.m.isPi then R else hint
        | none => hint
      | _ => hint
    -- PROPOSAL (m2-proofs): an embedded value holds no borrow the run made, so its result carries
    -- no label, whatever label the hint (a place's stored type, at an assignment) records
    -- STRICT at a constructor value (D83 row 8): it is a member of the type its record names
    strictVal K.dm.read v (meanV hint v, { T with label := none }) s
  | .sort l => pure (.ty (TyM.univ l), .plain (TyM.univ (sortSucc l)))
  | .pi hs ds c => fun s =>
    -- [T-Pi]: the parameters' and output's meanings as functions of the earlier parameters
    -- (`runBinds`), the carrier at the declared sort (D55, `Decisions.piSort`)
    let bs := runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiCod := match c with
      | .ref U => ⟨true, fun acc => match runT false (.plain TyM.err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
      | c => ⟨false, fun acc => match runT false (.plain TyM.err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    -- STRICT: every domain and the codomain have a level at every typed tuple of arguments
    if PiOk K.dm.read ps [] out then some ((.ty (piTyAt K.dm.read l ps out), .plain (TyM.univ l)), s) else none
  | .fix self hs ds c dec body => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.fix self hs ds c dec body)) (fun s =>
    -- [Closure] (D51, D53, D80): a closure means a function on its annotated domain, read off
    -- the reference run of its body in the forming frame extended by `self` and the parameters
    -- (the body's layout `[caps…, self, x̄]`), under a fresh bottom frame (docs/31 D126: the
    -- checker's `checkFix` frames, `[{}, {caps…, self, x̄}]` for a closure formed in one frame). A recursive `fix` means its guarded fixpoint by
    -- stages (docs/24 §4): stage 0 is undefined, stage `k + 1` binds `self` to stage `k`'s
    -- closure at the weakened function type (the true codomain at arguments of rank below `k`,
    -- `Unit` above, docs/34), and the function at arguments whose decreasing argument has rank
    -- `r` is stage `r + 1`; so a call that does not decrease reads `()` at `Unit`, and the
    -- closure, built strictly at the true type, is `err` unless the codomain holds it.
    let bs := runBinds s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiCod := match c with
      | .ref U => ⟨true, fun acc => match runT false (.plain TyM.err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
      | c => ⟨false, fun acc => match runT false (.plain TyM.err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
    -- the codomain, the body's hint (the audit's A8: a body that is a bare `Nil` reads its
    -- parameters off the code)
    let cod : List Sem → TyS := fun acc => .plain (out.cod acc)
    -- the code at the declared sort (D55, D12): `piTyAt`/`closureAt` (`Apply1.lean`)
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    let piT := piTyAt K.dm.read l ps out
    let start := s.nextLoan
    -- the declared readings of the parameters and the codomain (`Decide.paramDecls`): what the
    -- frame binds the parameters at, and `self` (D19, R3: bound at `other`, a parameter of a copy
    -- type was moved by its first read, and a call through `self` or a function parameter was
    -- never classified as a statement or a proof)
    let cd := K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c
    let bodyAt (selfT : TyM) (selfM : Sem) (args : List Sem) : Option BodyOut :=
      -- the frame: `self`, then the parameters. A borrow parameter is set up as the generic call
      -- is ([Def]): a fresh label `lᵢ`, a *cell* (a binding of frame 0, below the body's frame,
      -- docs/31 D126) reading `lᵢ`'s final content, and the parameter holding the content as the
      -- borrow's holder (D14). Returning the parameter returns its label.
      -- docs/31 D126: under a fresh bottom frame (`SState.under`), as the checker's `checkFix`
      -- frames the body: frame 0 for the cells, the top frame the captures, `self`, the parameters
      let s₁ := s.under.pushBind { ty := .plain selfT, val := fun _ => selfM, decl := .pi cd }
      -- each parameter is bound at its type (its code) and at its declared reading (`bs`)
      let step (sa : SState × List Sem × List Pos) (ap : Sem × PiDom) : SState × List Sem × List Pos :=
        let (s, acc, cells) := sa
        let T : TyS := match bs[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
        let d : DeclInfo := match bs[acc.length]? with | some b => b.2 | none => .other
        if ap.2.isRef then
          let (l, s) := s.freshLoan
          -- docs/31 D126: the cell is a binding of frame 0, `x° ↦ loan l` at the content type, as
          -- the checker's `checkFix` makes it
          let cell : Pos := .bind 0 (((s.env[0]?).map (·.binds.length)).getD 0)
          -- docs/31 D138: the cell is the label's one loan site, as the checker's `loan l` is
          let s := (s.pushCell { ty := .plain T.m, val := fun ψ => ψ l, decl := .other }).setLent l [⟨cell, [], false⟩]
          -- the argument is recorded as the label's member (docs/31 D68: where a label is made)
          let s := pushBindShaped ((s.setHeldMem l ap.1).setHeldTy l T.m) { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
          (s, acc ++ [ap.1], cells ++ [cell])
        else
          (s.pushBind { ty := { T with label := none }, val := fun _ => ap.1, decl := d }, acc ++ [ap.1], cells)
      let (s₂, _, cells) := (args.zip ps).foldl step (s₁, [], [])
      match runT true (cod args) body s₂ with
      | some ((r, R), s₃) =>
        -- the frame pop ends the borrows the body made and the parameters' (their cells then
        -- read the holders' contents), except the returned borrow's, whose holder is the
        -- caller's; a borrow parameter's final content is its cell's
        -- PROPOSAL (m2-proofs, 5b): the returned borrow survives only when the codomain is a
        -- borrow; a labelled result at a data codomain (ill-typed) is ended with the rest, else
        -- its cell reads the future at the run's own label in `mkLeafData`
        let keep : Option Nat := if out.isRef then R.label else none
        -- STRICT END (ruling (A)): the frame pop's ends
        if EndsOk K φ (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep) s₃ then
          let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
          let finals := cells.map fun c => s₄.valAt c
          some ⟨r, finals, R.label⟩
        else none
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem := closureAt K.dm.read l φ ps out g
    let rankOf (args : List Sem) : Nat := match dec with
      | some j =>
        match args[j]? with
        | some a => semRank a
        | none => 0
      | none => 0
    -- a stage's `self` is the stage below at the weakened function type (docs/34): built
    -- strictly, a stage good only below its bound is an element of that type, not of the true
    -- one (docs/31 D60's fill is gone)
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun k gk => bodyAt (piTyAt K.dm.read l ps (weakCod l rankOf k out))
          (closureAt K.dm.read l φ ps (weakCod l rankOf k out) (stageFn l ps rankOf k gk)))
    -- a non-recursive `fix` is the recursive one at rank `0` (`rankOf` is `0` without `dec`): its
    -- `self` is stage 0's closure at the weakened type, a member of it (`stage_mem`), never read (the
    -- checker has no `self` in scope there, D31). It was `err`, an open member of nothing, and the
    -- strict test after a write at a field path, which reads every binding, failed on every such
    -- body (`Strict/FrameCE`: `SetFstOwned`, `PartMove`, accepted, had no meaning; docs/31 D113)
    let g : List Sem → Option BodyOut := fun args => stage (rankOf args + 1) args
    -- forming the closure (`Machine.capture`) accesses each captured variable, oldest binding
    -- first, and then moves it unless its declared reading is copy (D80): the checker's [Access]
    -- before the capture ends the borrows lent at it (docs/31 D29 point 2, D37)
    -- STRICT END (ruling (A)): the captures' accesses
    if FoldOk (capStep K) (CapOk K φ) (capOrder (.fix self hs ds c dec body)) s then
    let s' := (capOrder (.fix self hs ds c dec body)).foldl (capStep K) s
    -- STRICT: the closure is a member of its function type (else it is `err`, `closureL_mem`)
    SM.strictS K.dm.read (fun s' => some ((closureOf g, .plain piT), s')) s'
    else none) s
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
      let fv ← SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT false (.plain TyM.err) f)
      -- a statement call's arguments are statement positions, each on its own copy (R4)
      let as ← runArgs fl.1 fv.2.m [] args
      -- STRICT: a borrow argument's label holds its parameter's content type
      fun s => if BorrowArgsTyped K.dm.read fv as s then callOf K.dm.read fv as s else none) s
  | .nat => pure (.ty TyM.nat, .plain (TyM.univ 1))
  | .unit => pure (.ty TyM.unit, .plain (TyM.univ 1))
  | .zero => pure (.el0 Nat 0, .plain TyM.nat)
  | .tt => pure (.el0 Unit (), .plain TyM.unit)
  | .succ u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.succ u)) (SM.strictS K.dm.read (do
    -- the argument runs with no hint, as the TYPED checker runs it (`evalCore`'s `.succ`: `eval fuel' typed u`;
    -- docs/31 D171, missed by D119, which handed it `Nat`)
    let (v, _) ← runT false (.plain TyM.err) u
    pure (v.succ, .plain TyM.nat))) s
  | .eq A a b => SM.onCopy do
    let (TA, _) ← runT false (.plain TyM.err) A
    -- each side runs with no hint, as the TYPED checker runs it (`evalCore`'s `.eq`: `eval fuel' typed a`;
    -- docs/31 D172, missed by D119, which handed it `A`)
    let (va, _) ← SM.onCopy (runT false (.plain TyM.err) a)
    let (vb, _) ← SM.onCopy (runT false (.plain TyM.err) b)
    -- STRICT: the type has a level and each side is `⊥` or a member of it (`EqOk`)
    fun s => if EqOk K.dm.read TA va vb then some ((.ty (TyM.prop (va = vb)), .plain (TyM.univ 0)), s) else none
  -- decision 1: the premise proofs run, each on a copy; `⋆` at `prop True`
  | .cong _ h => SM.onCopy (do
    let _ ← runT false (.plain TyM.err) h
    pure (.proof, .plain (TyM.prop True)))
  | .prim "symm" [h] => SM.onCopy (do
    let _ ← runT false (.plain TyM.err) h
    pure (.proof, .plain (TyM.prop True)))
  | .prim "trans" [h, k] => SM.onCopy (do
    let _ ← runT false (.plain TyM.err) h
    let _ ← runT false (.plain TyM.err) k
    pure (.proof, .plain (TyM.prop True)))
  | .prim "rewrite" [h, u] => SM.onCopy (do
    let _ ← runT false (.plain TyM.err) h
    let _ ← runT false (.plain TyM.err) u
    pure (.proof, .plain (TyM.prop True)))
  | .prim "rewriteR" [h, u] => SM.onCopy (do
    let _ ← runT false (.plain TyM.err) h
    let _ ← runT false (.plain TyM.err) u
    pure (.proof, .plain (TyM.prop True)))
  -- STRICT: `&A` is well formed iff `A : Type₀`
  | .ref A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ref A)) (SM.strictS K.dm.read (do
    let (TA, _) ← runT false (.plain TyM.err) A
    pure (TA, .plain (TyM.univ 1)))) s
  | .id A t u => fun s => do
    -- `Id` observes: each side on a copy of the state, a fresh value written through each
    -- re-pointed borrow binding ([Obs-ref]), every borrow ended, the result and every position
    -- compared (D84: moved places are definite values, so they compare too); the proposition
    -- holds for every choice of the written values among the members of the borrowed types
    let ((TA, _), _) ← SM.onCopy (runT false (.plain TyM.err) A) s
    let T : TyS := .plain TA.asTy
    let reps := K.D.rePointed (scopeOf s) t
    let o₁ ← runT false T t s
    let o₂ ← runT false T u s
    -- STRICT: the type has a level and each side is `⊥` or a member of it (`EqOk`)
    if EqOk K.dm.read TA o₁.1.1 o₂.1.1 then
      some ((.ty (TyM.prop (∀ ws : List Sem, obsTyped K.dm.read reps ws s →
        observation φ reps ws s.positions o₁.1 o₁.2 = observation φ reps ws s.positions o₂.1 o₂.2)), .plain (TyM.univ 0)), s)
    else none
  | .prim "J" [A, a, b, P, h, t] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, h, t])) (do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (runT false (.plain TyM.err) A)
    let ra ← SM.onCopy (runT false (.plain TyM.err) a)
    let _ ← SM.onCopy (runT false (.plain TyM.err) b)
    let rP ← SM.onCopy (runT false (.plain TyM.err) P)
    let _ ← SM.onCopy (runT false (.plain TyM.err) h)
    -- main's D124: the transported term is handed the motive at the first endpoint, `P(a)`, on both of the
    -- checker's typed paths (`Machine.jMotiveAt`: `P` called at `a`'s value, on a private copy); docs/31 D184
    let rPa ← SM.onCopy (callOf K.dm.read rP [ra])
    -- D90 [Entry]: `J` computes, so its transported term's stuck block's captures are accessed
    -- first; then the term runs as the one arm of D84's join (`Machine.evalCore`'s `J`)
    fun s =>
      -- STRICT END (ruling (A)): [Entry]'s ends, and the join's
      if MatchEntryOk K φ true t s then
      let s := (matchEntry K φ true t s).1
      let entry := movedPlaces φ s
      -- the transported term runs at the hint `P(a)` (`evalCore`'s `J`, in place; D119, main's D124)
      match runT false (.plain rPa.1.asTy) t s with
      | some ((r, R), s) =>
        if JoinDropOk K φ entry (.prim "J" [A, a, b, P, h, t]) s then
          some ((r, R), joinDrop K φ entry (.prim "J" [A, a, b, P, h, t]) s)
        else none
      | none => none
      else none) s
  -- `clone`, `peek` and `inplace` of a place read it in place: not consumed (`inplace` is a stuck
  -- block's read-only capture; it used to be `run hint u`, a move: D19)
  | .prim "clone" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "clone" [u]))
      (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT false hint u)) s
  | .prim "peek" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "peek" [u]))
      (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT false hint u)) s
  | .prim "inplace" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "inplace" [u]))
      (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT false hint u)) s
  -- `split f in u` ([Split], D61) is a typing device: the end-of-body check checks `u` in each world of the split at
  -- the goal; once run it is its term, at the form's own hint and tail flag (docs/31 D175, the lead's ruling).
  -- (The braces form is surface syntax only since main's D126: `split f(ā) { … }` resolves to this form.)
  | .prim "split" [.const f, u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "split" [.const f, u]))
      (runT tl hint u) s
  | .prim _ _ => SM.fail
  -- STRICT: the term's value is a member of the annotation
  | .ascribe u A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ascribe u A)) (SM.strictS K.dm.read <| do
    -- the annotation is the term's type, its code (the audit's A7: an annotated function is
    -- called along it, an annotated bare constructor reads its parameters off it)
    let (TA, _) ← SM.onCopy (runT false (.plain TyM.err) A)
    let T : TyS := .plain TA.asTy
    let (v, R) ← runT false T u
    fun s => if labTyOk s R.label T.m then some ((v, { T with label := R.label }), s) else none) s
termination_by structural t => t

/-- Arm `c` of a match, run at the match's expected type. -/
noncomputable def runArm (tl : Bool) (hint : TyS) (c : Nat) : List (Hint × Term) → SM Res
  | [] => SM.fail
  | (_, t) :: rest => if c = 0 then runT tl hint t else runArm tl hint (c - 1) rest
termination_by structural arms => arms

/-- The parameters of a Π-term as a frame binds them (`PBind`): each domain term run in the
forming state extended by the earlier parameters at THEIR types and readings (`pre`), giving the
parameter's type with its Π-shape (the run of a Π-term returns the Π's shape in its result type)
as a function of the earlier arguments; `dcs` are the telescope's declared readings. For `&A` the
content type `A` is run. (D19, R6; `psOf` reads the telescope's description off the result.) -/
noncomputable def runBinds (s : SState) (dcs : List DeclInfo) (pre : List PBind) : List Term → List PBind
  | [] => []
  | .ref A :: ds =>
    mkBind dcs pre (fun acc => runT false (.plain TyM.err) A (extendBy s pre acc)) ::
      runBinds s dcs (pre ++ [mkBind dcs pre (fun acc => runT false (.plain TyM.err) A (extendBy s pre acc))]) ds
  | d :: ds =>
    mkBind dcs pre (fun acc => runT false (.plain TyM.err) d (extendBy s pre acc)) ::
      runBinds s dcs (pre ++ [mkBind dcs pre (fun acc => runT false (.plain TyM.err) d (extendBy s pre acc))]) ds
termination_by structural ds => ds

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    -- with no hint, as the TYPED checker runs it (`evalParams`: `eval fuel' typed a`; docs/31 D172, missed by
    -- D119, which handed it the parameter's type)
    let (v, _) ← SM.onCopy (runT false (.plain TyM.err) a)
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
noncomputable def runFields (stmt : Bool) (d : IndDecl) (c i : Nat) (rh : Option Rec) (sol : List (Option Sem))
    (earlier : List Sem) : List Term → SM (List Sem × List (Option Sem))
  | [] => pure ([], sol)
  | a :: as => fun s => (do
    -- the field's type is handed as the TYPED checker hands it (`evalCtor`'s `fh`; docs/31 D119)
    let T : TyS := if a.fieldHinted d c i then (match rh with
      | some r => .plain (K.dm.fieldTyR d r c i earlier)
      | none => match fieldTerm d c i with
        | some FT =>
          if FT.freeVars.all (fun j => d.params.length ≤ j || (sol.getD (d.params.length - 1 - j) none).isSome) then
            .plain (K.dm.fieldTy d (solved sol) c i earlier)
          else .plain TyM.err
        | none => .plain TyM.err) else .plain TyM.err
    let (v, R) ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (runT false T a)
    let sol₁ := match fieldTerm d c i with
      | some FT => unifyTyS K.dm d.params.length FT R sol
      | none => sol
    let (rest, sol₂) ← runFields stmt d c (i + 1) rh sol₁ (earlier ++ [v]) as
    pure (v :: rest, sol₂)) s
termination_by structural as => as

/-- A call's arguments, each at its parameter type read off the callee's type code at the earlier
arguments (D82, [Call-type]). With `stmt` (a statement call's) each argument is a statement
position, on its own copy (`stmtArgIf`; D19, R4: in sequence on the call's one copy, `Lem(x, x)`
found `x` moved), unless its declared type is a borrow type, which runs in place
(`Decide.stmtArgInPlace`). -/
noncomputable def runArgs (stmt : Bool) (fT : TyM) (earlier : List Sem) : List Term → SM (List Res)
  | [] => pure []
  | a :: as => fun s => (do
    -- the parameter's type is handed as the TYPED checker hands it (`evalCall`; docs/31 D119)
    let T : TyS := if a.argHinted then .plain (fT.domAfter K.dm.read earlier) else .plain TyM.err
    let r ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (runT false T a)
    let rest ← runArgs stmt fT (earlier ++ [r.1]) as
    pure (r :: rest)) s
termination_by structural as => as

/-- The meaning of a value, with the code-dependent forms given by the run itself (the knot of
`Value.mean`'s `CodeMeaning`): a sealed program is its program run from the empty state (the
label counter above its loans) at the hint; a closure or Π-closure is its term run in a frame
holding its captures at their recorded types (D51); a global is `K.C.global`. The other clauses
are `Value.mean`'s (`meanV_eq_mean`). -/
noncomputable def meanV (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (meanV (.plain TyM.nat) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (K.C.global n).1
  -- STRICT: `err` unless the captures are members of their recorded types (`CapsOk`)
  | .clo caps t rd =>
    if CapsOk K.dm.read (capsVals caps) (capsTys rd) then
      match runT false (.plain TyM.err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
      | some ((v, _), _) => v
      | none => .err
    else .err
  | .borrow _ w => meanV hint w
  | .gloan _ w => meanV hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  -- PROPOSAL (m2-proofs, 8): a sealed program runs from the label counter 0, not from above its
  -- loans. Its fresh labels never leave its run (only the result's meaning and shape are read),
  -- and meeting one of its loans is harmless (a loan is read by the value's meaning, never through
  -- the state). A counter fixed by the term changes under substitution, which then needs the
  -- counter's independence (the renaming lemma, false as first stated: finding 7)
  | .sealed t => match runT false hint t (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err
  | .proof => .proof
  | .tNat => .ty TyM.nat
  | .tUnit => .ty TyM.unit
  -- STRICT (`Value.mean`'s clause): `err` unless `EqOk`
  | .tEq A a b =>
    let T := TyS.plain (meanV (.plain TyM.err) A).asTy
    if EqOk K.dm.read (meanV (.plain TyM.err) A) (meanV T a) (meanV T b) then .ty (TyM.prop (meanV T a = meanV T b))
    else .ty TyM.err
  | .tRef A => meanV (.plain TyM.err) A
  -- STRICT: `err` unless `CapsOk` (and, through the `.pi` clause, `PiOk`)
  | .tPi caps t rd =>
    if CapsOk K.dm.read (capsVals caps) (capsTys rd) then
      match runT false (.plain TyM.err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
      | some ((v, _), _) => .ty v.asTy
      | none => .ty TyM.err
    else .ty TyM.err
  | .sort l => .ty (TyM.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
        else some (K.dm.recOf d (meanParams d 0 [] ps))
      match r? with
      | some r => if d.sort == 0 then .proof else DataModel.ctorR d r c (meanFields d r c 0 [] fs)
      | none => .err
    | none => .err
  -- STRICT (`Value.mean`'s clause): `err` unless `paramsOk`
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d =>
      if paramsOk K.dm d (meanParams d 0 [] args) then .ty (K.dm.tyM d (meanParams d 0 [] args))
      else .ty TyM.err
    | none => .ty TyM.err
termination_by structural v => v

noncomputable def meanFields (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV (.plain (K.dm.fieldTyR d r c i earlier)) v
    s :: meanFields d r c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

noncomputable def meanParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV (.plain (K.dm.paramTy d i earlier)) v
    s :: meanParams d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- A closure's or Π-closure's captured values, each read as a value (D51). -/
noncomputable def capsVals : List Value → List Sem
  | [] => []
  | v :: vs => meanV (.plain TyM.err) v :: capsVals vs
termination_by structural vs => vs

/-- The captures' recorded declared types, each read as a type (D82; a type is future-free): its
code, with its whole structure (the audit's A10: a call through a captured function runs along
it). -/
noncomputable def capsTys : List (DeclInfo × Value) → List (DeclInfo × TyS)
  | [] => []
  | (d, T) :: rest => (d, .plain (meanV (.plain TyM.err) T).asTy) :: capsTys rest
termination_by structural rest => rest
end

/-- The reference run in a position that is not a tail (`runT false`): every run but a function's
body, and the tails a body's tail hands on (D90's tail flag, `runT`). -/
noncomputable abbrev run (hint : TyS) (t : Term) : SM Res := runT K ρ φ false hint t

/-- The binders of a telescope formed in `s`: `runBinds` at the telescope's declared readings. -/
noncomputable def bindsOf (s : SState) (ds : List Term) : List PBind :=
  runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds

/-- The parameters of a Π-term formed in `s`, as the `.pi` and `.fix` clauses read them. -/
noncomputable def runDoms (s : SState) (ds : List Term) : List PiDom := psOf (bindsOf K ρ φ s ds) ds

/-- A Π-term's or closure's codomain, as the `.pi` and `.fix` clauses read it: a returned borrow
or borrow-free data, its type at each tuple of arguments. -/
noncomputable def codOf (s : SState) (bs : List PBind) (c : Term) : PiCod := match c with
  | .ref U => ⟨true, fun acc => match run K ρ φ (.plain TyM.err) U (extendBy s bs acc) with
    | some ((v, _), _) => v.asTy
    | none => TyM.err⟩
  | c => ⟨false, fun acc => match run K ρ φ (.plain TyM.err) c (extendBy s bs acc) with
    | some ((v, _), _) => v.asTy
    | none => TyM.err⟩

/-- A closure's codomain, its code, as a function of the parameters: its body's hint. -/
noncomputable def fixCod (s : SState) (bs : List PBind) (c : Term) : List Sem → TyS :=
  fun acc => .plain ((codOf K ρ φ s bs c).cod acc)

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
  clo ρ φ caps t rd := meanV K ρ φ (.plain TyM.err) (.clo caps t rd)
  pi ρ φ caps t rd := (meanV K ρ φ (.plain TyM.err) (.tPi caps t rd)).asTy
  -- a deferred type is the parameter's binder, or the codomain's: as the `.fix` clause's frame
  -- binds it
  paramTy ρ P ws j := match P with
    | .tPi caps t rd =>
      match t with
      | .pi _ ds c | .fix _ _ ds c _ _ =>
        let s₀ := stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))
        let acc := ws.map (meanV K ρ noFuture (.plain TyM.err))
        match (bindsOf K ρ noFuture s₀ ds)[j]? with
        | some b => b.1 (acc.take j)
        | none => fixCod K ρ noFuture s₀ (bindsOf K ρ noFuture s₀ ds) c acc
      | _ => .plain TyM.err
    | _ => .plain TyM.err

/-- The code meaning of a run context, as the step statements read a state: `MState.mean K.dm K.M
K.Γ ρ st`. There is no knot hypothesis `K.C = …`: `K.C` supplies the globals and nothing else. -/
noncomputable abbrev RunCtx.M (K : RunCtx) : CodeMeaning := codeMeaning K

/-- Δ as the run knows it, from a checker state: each abstract value's stored type (`Value.tyS`,
its code), read under the constant future as every stored type is. -/
noncomputable def deltaOf (K : RunCtx) (ρ : Assignment) (st : MState) : Nat → TyS := fun σ =>
  match st.absTy[σ]? with
  | some T => Value.tyS K.dm (codeMeaning K) K.Γ ρ T
  | none => .plain TyM.err


/-- The knot at the future asked: a sealed program in a state is read at the state's future (the
positive form of `Regress/Knot_dcdd0a34.lean`). -/
theorem mean_sealed_at_future (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (l : Nat) :
    Value.mean K.dm K.M K.Γ ρ φ hint (.sealed (.val (.loan l))) = φ l := by
  show meanV K ρ φ hint (.sealed (.val (.loan l))) = φ l
  simp [meanV, runT, strictVal, pure]

/-- The Π-closure clause of the knot: `meanV` of a Π-closure is already a type value. -/
theorem meanV_tPi_ty (hint : TyS) (caps : List Value) (t : Term) (rd : List (DeclInfo × Value)) :
    meanV K ρ φ hint (.tPi caps t rd) = .ty (meanV K ρ φ (.plain TyM.err) (.tPi caps t rd)).asTy := by
  show (if CapsOk K.dm.read (capsVals K ρ φ caps) (capsTys K ρ φ rd) then
        match run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err)
    = .ty (if CapsOk K.dm.read (capsVals K ρ φ caps) (capsTys K ρ φ rd) then
        match run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err).asTy
  split
  · cases run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) <;> rfl
  · rfl

mutual
/-- The knot, by induction on the value: each clause is the same text, the code-dependent ones
through `codeMeaning`, the Π-closure's by `meanV_tPi_ty`. -/
theorem meanV_eq_mean_aux (hint : TyS) : (v : Value) →
    Value.mean K.dm (codeMeaning K) K.Γ ρ φ hint v = meanV K ρ φ hint v
  | .zero => rfl
  | .succ v => by
    show (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.nat) v).succ
      = (meanV K ρ φ (.plain TyM.nat) v).succ
    rw [meanV_eq_mean_aux (.plain TyM.nat) v]
  | .unit => rfl
  | .gfn _ => rfl
  | .clo _ _ _ => rfl
  | .borrow _ w => meanV_eq_mean_aux hint w
  | .gloan _ w => meanV_eq_mean_aux hint w
  | .loan _ => rfl
  | .bot => rfl
  | .abs _ => rfl
  | .sealed _ => rfl
  | .proof => rfl
  | .tNat => rfl
  | .tUnit => rfl
  | .tEq A a b => by
    show (if EqOk K.dm.read (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A)
          (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) a)
          (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) b)
        then Sem.ty (TyM.prop (Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) a
        = Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) b))
        else .ty TyM.err)
      = (if EqOk K.dm.read (meanV K ρ φ (.plain TyM.err) A)
          (meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) a)
          (meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) b)
        then Sem.ty (TyM.prop (meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) a
        = meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) b))
        else .ty TyM.err)
    rw [meanV_eq_mean_aux (.plain TyM.err) A, meanV_eq_mean_aux _ a, meanV_eq_mean_aux _ b]
  | .tRef A => meanV_eq_mean_aux (.plain TyM.err) A
  | .tPi caps t rd => (meanV_tPi_ty K ρ φ hint caps t rd).symm
  | .sort _ => rfl
  | .ind ty c h ps fs => by
    have hP : ∀ d, Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d 0 [] ps = meanParams K ρ φ d 0 [] ps :=
      fun d => meanParams_eq_mean d 0 [] ps
    have hF : ∀ d r, Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d r c 0 [] fs
        = meanFields K ρ φ d r c 0 [] fs :=
      fun d r => meanFields_eq_mean d r c 0 [] fs
    simp only [Value.mean, meanV, hP, hF]
    cases List.find? (fun x => x.name == ty) K.Γ with
    | none => rfl
    | some d =>
      cases (if (ps.isEmpty && !d.params.isEmpty) = true then
          (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
        else some (K.dm.recOf d (meanParams K ρ φ d 0 [] ps))) <;> rfl
  | .tInd n args => by
    have hP : ∀ d, Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d 0 [] args = meanParams K ρ φ d 0 [] args :=
      fun d => meanParams_eq_mean d 0 [] args
    simp only [Value.mean, meanV, hP]
    cases List.find? (fun x => x.name == n) K.Γ <;> rfl
termination_by structural v => v

theorem meanFields_eq_mean (d : IndDecl) (r : Rec) (c : Nat) :
    (i : Nat) → (earlier : List Sem) → (vs : List Value) →
    Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d r c i earlier vs = meanFields K ρ φ d r c i earlier vs
  | _, _, [] => rfl
  | i, earlier, v :: vs => by
    show Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.fieldTyR d r c i earlier)) v
        :: Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d r c (i + 1)
          (earlier ++ [Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.fieldTyR d r c i earlier)) v]) vs
      = meanV K ρ φ (.plain (K.dm.fieldTyR d r c i earlier)) v
        :: meanFields K ρ φ d r c (i + 1) (earlier ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i earlier)) v]) vs
    rw [meanV_eq_mean_aux _ v, meanFields_eq_mean d r c (i + 1) _ vs]
termination_by structural _ _ vs => vs

theorem meanParams_eq_mean (d : IndDecl) :
    (i : Nat) → (earlier : List Sem) → (vs : List Value) →
    Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d i earlier vs = meanParams K ρ φ d i earlier vs
  | _, _, [] => rfl
  | i, earlier, v :: vs => by
    show Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.paramTy d i earlier)) v
        :: Value.meanParams K.dm (codeMeaning K) K.Γ ρ φ d (i + 1)
          (earlier ++ [Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.paramTy d i earlier)) v]) vs
      = meanV K ρ φ (.plain (K.dm.paramTy d i earlier)) v
        :: meanParams K ρ φ d (i + 1) (earlier ++ [meanV K ρ φ (.plain (K.dm.paramTy d i earlier)) v]) vs
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
