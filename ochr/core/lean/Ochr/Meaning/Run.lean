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
  if fl.2 then some ((.proof, .plain TyM.err), s) else SM.stmtIf fl.1 x s

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

/-- An erased PLACE (the audit's A17, docs/31 D59): as `SM.erasedIf`, but a proof is `⋆` at the
type `T s`, the place's stored type, as the checker types a proof it reads at a place (it reads
the place's type on a private copy). So a constructor parameter solved by a proof field's type is
solved (`MkPBox(h)`). A proof that is not a place stays untyped. -/
def SM.erasedAt (fl : Bool × Bool) (T : SState → TyS) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  if fl.2 then some ((.proof, T s), s) else SM.stmtIf fl.1 x s

theorem SM.erasedAt_congr {fl : Bool × Bool} {T T' : SState → TyS} {x x' : SM (Sem × TyS)} {s : SState}
    (hT : T s = T' s) (h : x s = x' s) : SM.erasedAt fl T x s = SM.erasedAt fl T' x' s := by
  simp only [SM.erasedAt, SM.stmtIf, hT, h]

/-- An erased place's run, taken apart, where its type carries no label. -/
theorem SM.erasedAt_some {fl : Bool × Bool} {T : SState → TyS} {x : SM (Sem × TyS)} {s s' : SState}
    {r : Sem × TyS} (hT : (T s).label = none) (h : SM.erasedAt fl T x s = some (r, s')) :
    x s = some (r, s') ∨ (s' = s ∧ r.2.label = none) := by
  unfold SM.erasedAt at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, hT⟩
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
  Δ : Nat → TyS := fun _ => .plain TyM.err
  /-- the declared types of the loans as the run knows them (P1, PROPOSAL m2-proofs): a borrowed
  function value (`&f`) is real, so an embedded `loan_ℓ` carries the Π-shape of its position's
  declared type (by (WF9) every loan outside a sealed program sits at a typed position), as the
  value that fills it will. A loan with no shape here reads as the hint (data). -/
  Λ : Nat → TyS := fun _ => .plain TyM.err

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

/-- Infer a constructor's unwritten parameters from a field's declared type term `FT` and the
type `R` the field's run returned (`Machine.unifyParams`, D46; the audit's A9): where `FT` is a
parameter variable, the parameter is `R` itself; where it is `D(x̄)` and `R`'s code is `D(v̄)`,
each parameter variable among `x̄` is its `v`. Only unsolved parameters are filled. A type the run
does not know (`err`) solves nothing, as the checker's field with no type. Not covered: a
parameter nested deeper (`List(Pair(A, B))`). -/
def unifyTyS (rd : DataRead) (np : Nat) (FT : Term) (R : TyS) (sol : List (Option Sem)) : List (Option Sem) :=
  if R.m.isErr then sol else
    match FT with
    | .place (.var j) => fillParam np j (.ty R.m) sol
    | .tind m as =>
      match R.data rd with
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
    | .dat "Nat" _ 0 [] _ => .el0 Nat 0
    | .dat "Nat" _ 1 _ _ => .el0 Nat 1
    | _ => .err

/-- The tag of a data value, its constructor's index, or `•` for a proof: what a `match` on it
observes, read off the value (docs/31 D32: a constructor value describes itself; neither its
type nor its carrier is consulted, D31). -/
noncomputable def indTag (v : Sem) (_ : TyS) : Sem :=
  match v with
  | .proof => .proof
  | .dat _ _ c _ _ => .el0 Nat c
  | _ => .err

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
caller has done it). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  let T := s.tyAt pos
  let old := s.valAt pos
  match Sem.updAt K.dm K.Γ T (fun _ => v) steps (old (s.typedFuture φ)) with
  | some _ => some (⟨⟩, s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => v) steps (old φ')).getD .err)
  | none => none

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

/-- The type an erased place is `⋆` at (A17, `SM.erasedAt`): its content's type, read on a
discarded copy; `err` where the place does not resolve. Label-free (`placeTy_label`). -/
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
      | none => v (φ'.updList (fixes (refLabels.map fun _ => .err)))
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

/-- `Machine.dropAtJoin` of one place, at `(pos, steps)`: a borrow at a root, its end; missing or a
proof, nothing; a copy, nothing; otherwise [Access] and `moved`. The holder is tested first, by the
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
prefix already), and relating it needed the reading to be unchanged by an access. -/
noncomputable def dropAt (q : Place) (pos : Pos) (steps : List Step) (s : SState) : SState :=
  match steps, s.shape pos with
  | [], some l => s.endLabel l
  | _, _ =>
    let s' := s.access pos (dataHit steps)
    match Sem.follow K.dm K.Γ (s'.tyAt pos) (s'.valAt pos (s'.typedFuture φ)) steps with
    | some (.proof, _) | none => s
    | some _ =>
      if K.D.copy (K.D.placeDecl (scopeOf s) q) then s else
      s'.setAt pos fun φ' => (Sem.updAt K.dm K.Γ (s'.tyAt pos) (fun _ => .moved) steps (s'.valAt pos φ')).getD .err

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

/-- `movedPlace`'s access while a block's captures are computed: the lent prefix, accessed whole. -/
noncomputable def entryReroot (s : SState) (q : Place) : SState := match resolve s q with
  | some (pos, steps) => accessLentPrefix pos steps s
  | none => s

/-- A capture's access at a block's entry (`Machine.entryAccess`), as data. -/
noncomputable def entryCap (s : SState) (qk : Place × Nat) : SState := match resolve s qk.1 with
  | some (pos, steps) => s.access pos (dataHit steps)
  | none => s

/-- D90 [Entry] (static ends, rule 2): a non-tail match on a known constructor, and `J`'s
transported term, first do what the stuck block they would close off does at its entry
(`Machine.blockEntry`): `movedPlace`'s accesses of the places K1 re-roots (the reference's
`accessLentPrefix`, as at the join), then each capture accessed as data, in the block's order
(`entryAccess`: `accessPath`, and `accessInside` where the place exists; below a moved part nothing
is lent, so the reference's data access ends the same). `bc` is `Decisions.blockCaps`. -/
noncomputable def entryAccess (bc : List Place × List (Place × Nat)) (s : SState) : SState :=
  bc.2.foldl entryCap (bc.1.foldl entryReroot s)

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
    let s₁ := entryAccess bc s
    (s₁, fun lab s₂ => if isRefDecl (K.D.declOf (scopeOf s₁) mt) then entryLend bc (entrySnapshot bc s₁) lab s₂ else s₂)
  else (s, fun _ s₂ => s₂)

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

/-- The variables a closure captures, oldest binding first (`Machine.capture`'s order: the
largest de Bruijn index first). -/
def capOrder (t : Term) : List Nat := (t.freeVars.toArray.qsort (· > ·)).toList

/-- One capture of a closure being formed (`Machine.capture`): the variable is accessed, then
moved unless its declared reading is copy (D80). -/
noncomputable def capStep (s : SState) (i : Nat) : SState := match s.varPos i with
  | some pos =>
    let s := s.access pos (dataHit [])
    if K.D.copy (K.D.placeDecl (scopeOf s) (.var i)) then s else s.setAt pos fun _ => .moved
  | none => s

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
  | .place p => fun s => SM.erasedAt (K.D.flags (scopeOf s) (.place p)) (placeTy K φ p)
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
    let ((v, R), s) ← runT false T u s
    assignAt K φ p v R.label s) s
  | .letIn x u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.letIn x u w)) (fun s => do
    let ((v, T), s) ← runT false (.plain TyM.err) u s
    let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← runT tl hint w s
    -- [Drop] of the binding: the borrow it holds *now* ends, then it is forgotten (PROPOSAL,
    -- m2-proofs, CE5: not the label its type carried when it was bound, which it may have moved
    -- out, while an assignment may have made it the holder of another)
    let held : Option Nat := match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none
    -- a binding holding no borrow ends the borrows lent at it (D65, `endLoansOfTopBind`: the
    -- non-lexical reading; docs/31 D29: the checker ends them, so the reference must)
    let s := match held with | some l => s.endLabel l | none => letLenders s
    some ((r, R), s.dropLast)) s
  | .seq u w => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.seq u w)) (do
    -- [Drop] of a discarded value (`Machine.dropValue`): a borrow it holds ends now, as the
    -- checker ends it (docs/31 D29: the two hold the same live borrows at every point; it used
    -- to stay parked until an access depended on it, an early end of the checker's)
    let r ← runT false (.plain TyM.err) u
    SM.modify (discardEnd r.2)
    runT tl hint w) s
  | .matchNat p z u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchNat p z u)) (fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access] for the tag: the
    -- audit's A1); `⊥` is an error; then D84's drop at the join
    let (tg, s) ← tagOf K φ p natTag s
    -- D90 [Entry]: not in tail position, the stuck block's captures are accessed first, and a
    -- borrow-typed match's result is lent what the block's would be (`matchEntry`)
    let (s, lend) := matchEntry K φ (!tl) (.matchNat p z u) s
    let entry := movedPlaces φ s
    match tg.asNat with
    | some 0 => do
      let ((r, R), s) ← runT tl hint z s
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | some (_ + 1) => do
      let ((r, R), s) ← runT tl hint u s
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | none => none) s
  | .matchInd p n arms => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.matchInd p n arms)) (fun s => do
    let (tg, s) ← tagOf K φ p indTag s
    -- D93: a match on a type with one constructor never closes off, so it has no entry and no
    -- join, on any path (`Machine.evalMatchInd`: its one arm runs directly)
    let one := oneCtor K.Γ n
    -- D90 [Entry], not in tail position, not on a proof (`evalMatchByType` has none), and not on a
    -- one-constructor type (D93)
    let (s, lend) := matchEntry K φ (!tl && !tg.isProof && !one) (.matchInd p n arms) s
    let entry := movedPlaces φ s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match tg with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => tg.asNat
    match c? with
    | some c => do
      let ((r, R), s) ← runArm tl hint c arms s
      -- a match on a proof has no join (`Machine.evalMatchByType`: its one arm runs on every
      -- path; the audit's A4)
      some ((r, R), match tg with
        | .proof => s
        | _ => if one then s else lend R.label (joinDrop K φ entry (.matchInd p n arms) s))
    | none => none) s
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      -- the type value is the declaration's code at the parameters (docs/31 D59)
      pure (.ty (K.dm.tyM d psM), .plain (TyM.univ d.sort))
    | none => SM.fail
  | .ctor ty c x ps args => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ctor ty c x ps args)) (do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      -- the parameters known before the fields: the written ones, or the hint's (`evalCtor`'s
      -- `sol`); the fields' types then solve the rest (`runFields`; the audit's A9)
      let sol₀ : List (Option Sem) := if !ps.isEmpty then psM.map some else
        match hint.data K.dm.read with
        | some (n, ps') => if n = ty ∧ ps'.length = d.params.length then ps'.map some else List.replicate d.params.length none
        | none => List.replicate d.params.length none
      -- a constructor of a Prop-sorted inductive is a proof, `⋆` (D42); its arguments are
      -- statement positions, each on its own copy (`stmtArgIf`; D19, R4)
      let (fs, sol) ← runFields (d.sort == 0) d c 0 sol₀ [] args
      if sol.all (·.isSome) then
        let ps' := solved sol
        if d.sort == 0 then
          pure (.proof, .plain (K.dm.tyM d ps'))
        else
          pure (K.dm.ctorM d ps' c fs, .plain (K.dm.tyM d ps'))
      else SM.fail
    | none => SM.fail) s
  | .const n => pure (K.C.global n)
  | .val v => fun s =>
    -- an embedded value, at the hint; a closure at its own type (its code, from its term in its
    -- captures' frame), an unknown at its type in Δ
    let T : TyS := match v with
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
    some ((meanV hint v, { T with label := none }), s)
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
    some ((.ty (piTyAt K.dm.read l ps out), .plain (TyM.univ l)), s)
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
    let bodyAt (selfM : Sem) (args : List Sem) : Option BodyOut :=
      -- the frame: `self`, then the parameters. A borrow parameter is set up as the generic call
      -- is ([Def]): a fresh label `lᵢ`, a *cell* (a temporary of the frame: temporaries do not
      -- shift de Bruijn indices) reading `lᵢ`'s final content, and the parameter holding the
      -- content as the borrow's holder (D14). Returning the parameter returns its label.
      let s₁ := s.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi cd }
      -- each parameter is bound at its type (its code) and at its declared reading (`bs`)
      let step (sa : SState × List Sem × List Pos) (ap : Sem × PiDom) : SState × List Sem × List Pos :=
        let (s, acc, cells) := sa
        let T : TyS := match bs[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
        let d : DeclInfo := match bs[acc.length]? with | some b => b.2 | none => .other
        if ap.2.isRef then
          let (l, s) := s.freshLoan
          let s := s.pushTemp fun ψ => ψ l
          let cell : Pos := .temp s.topIdx (((s.env.getLast?).map (·.temps.length)).getD 1 - 1)
          -- the argument is recorded as the label's member (docs/31 D68: where a label is made)
          let s := pushBindShaped (s.setHeldMem l ap.1) { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
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
        let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
        let finals := cells.map fun c => s₄.valAt c
        some ⟨r, finals, R.label⟩
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem := closureAt K.dm.read l φ ps out g
    -- a stage's closure is filled where the stage is undefined (docs/31 D60: built strictly,
    -- every stage's closure, so every recursive closure, was `err`)
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun _ gk => bodyAt (closureFillAt K.dm.read l φ ps out gk))
    let rankOf (args : List Sem) : Nat := match dec with
      | some j =>
        match args[j]? with
        | some a => semRank K.dm K.Γ a
        | none => 0
      | none => 0
    let g : List Sem → Option BodyOut := match dec with
      | some _ => fun args => stage (rankOf args + 1) args
      | none => bodyAt .err
    -- forming the closure (`Machine.capture`) accesses each captured variable, oldest binding
    -- first, and then moves it unless its declared reading is copy (D80): the checker's [Access]
    -- before the capture ends the borrows lent at it (docs/31 D29 point 2, D37)
    let s' := (capOrder (.fix self hs ds c dec body)).foldl (capStep K) s
    some ((closureOf g, .plain piT), s')) s
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
      let fv ← SM.headOf f (fun p => readPlace K φ p true) (runT false (.plain TyM.err) f)
      -- a statement call's arguments are statement positions, each on its own copy (R4)
      let as ← runArgs fl.1 fv.2.m [] args
      callOf K.dm.read fv as) s
  | .nat => pure (.ty TyM.nat, .plain (TyM.univ 1))
  | .unit => pure (.ty TyM.unit, .plain (TyM.univ 1))
  | .zero => pure (.el0 Nat 0, .plain TyM.nat)
  | .tt => pure (.el0 Unit (), .plain TyM.unit)
  | .succ u => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.succ u)) (do
    let (v, _) ← runT false (.plain TyM.nat) u
    pure (v.succ, .plain TyM.nat)) s
  | .eq A a b => SM.onCopy do
    let (TA, _) ← runT false (.plain TyM.err) A
    let T : TyS := .plain TA.asTy
    let (va, _) ← SM.onCopy (runT false T a)
    let (vb, _) ← SM.onCopy (runT false T b)
    pure (.ty (TyM.prop (va = vb)), .plain (TyM.univ 0))
  | .cong _ _ | .prim "symm" _ | .prim "trans" _ | .prim "rewrite" _ | .prim "rewriteR" _ =>
    pure (.proof, .plain TyM.err)
  | .ref A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ref A)) (do
    let (TA, _) ← runT false (.plain TyM.err) A
    pure (TA, .plain (TyM.univ 1))) s
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
    some ((.ty (TyM.prop (∀ ws : List Sem, obsTyped K.dm.read reps ws s →
      observation φ reps ws s.positions o₁.1 o₁.2 = observation φ reps ws s.positions o₂.1 o₂.2)), .plain (TyM.univ 0)), s)
  | .prim "J" [A, a, b, P, h, t] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, h, t])) (do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (runT false (.plain TyM.err) A)
    let _ ← SM.onCopy (runT false (.plain TyM.err) a)
    let _ ← SM.onCopy (runT false (.plain TyM.err) b)
    let _ ← SM.onCopy (runT false (.plain TyM.err) P)
    let _ ← SM.onCopy (runT false (.plain TyM.err) h)
    -- D90 [Entry]: `J` computes, so its transported term's stuck block's captures are accessed
    -- first; then the term runs as the one arm of D84's join (`Machine.evalCore`'s `J`)
    fun s =>
      let s := (matchEntry K φ true t s).1
      let entry := movedPlaces φ s
      match runT false hint t s with
      | some ((r, R), s) => some ((r, R), joinDrop K φ entry (.prim "J" [A, a, b, P, h, t]) s)
      | none => none) s
  -- `clone`, `peek` and `inplace` of a place read it in place: not consumed (`inplace` is a stuck
  -- block's read-only capture; it used to be `run hint u`, a move: D19)
  | .prim "clone" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "clone" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runT false hint u)) s
  | .prim "peek" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "peek" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runT false hint u)) s
  | .prim "inplace" [u] => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "inplace" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runT false hint u)) s
  | .prim _ _ => SM.fail
  | .ascribe u A => fun s => SM.erasedIf (K.D.flags (scopeOf s) (.ascribe u A)) (do
    -- the annotation is the term's type, its code (the audit's A7: an annotated function is
    -- called along it, an annotated bare constructor reads its parameters off it)
    let (TA, _) ← SM.onCopy (runT false (.plain TyM.err) A)
    let T : TyS := .plain TA.asTy
    let (v, R) ← runT false T u
    pure (v, { T with label := R.label })) s
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
    let (v, _) ← SM.onCopy (runT false (.plain (K.dm.paramTy d i earlier)) a)
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
          .plain (K.dm.fieldTy d (solved sol) c i earlier)
        else .plain TyM.err
      | none => .plain TyM.err
    let (v, R) ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (runT false T a)
    let sol₁ := match fieldTerm d c i with
      | some FT => unifyTyS K.dm.read d.params.length FT R sol
      | none => sol
    let (rest, sol₂) ← runFields stmt d c (i + 1) sol₁ (earlier ++ [v]) as
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
    let T : TyS := .plain (fT.domAfter K.dm.read earlier)
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
  | .clo caps t rd => match runT false (.plain TyM.err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => v
    | none => .err
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
  | .tEq A a b =>
    let T := TyS.plain (meanV (.plain TyM.err) A).asTy
    .ty (TyM.prop (meanV T a = meanV T b))
  | .tRef A => meanV (.plain TyM.err) A
  | .tPi caps t rd => match runT false (.plain TyM.err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => .ty v.asTy
    | none => .ty TyM.err
  | .sort l => .ty (TyM.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let ps? := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data K.dm.read with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some (meanParams d 0 [] ps)
      match ps? with
      | some ps' => if d.sort == 0 then .proof else K.dm.ctorM d ps' c (meanFields d ps' c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => .ty (K.dm.tyM d (meanParams d 0 [] args))
    | none => .ty TyM.err
termination_by structural v => v

noncomputable def meanFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV (.plain (K.dm.fieldTy d ps c i earlier)) v
    s :: meanFields d ps c (i + 1) (earlier ++ [s]) vs
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
  simp [meanV, runT]

/-- The Π-closure clause of the knot: `meanV` of a Π-closure is already a type value. -/
theorem meanV_tPi_ty (hint : TyS) (caps : List Value) (t : Term) (rd : List (DeclInfo × Value)) :
    meanV K ρ φ hint (.tPi caps t rd) = .ty (meanV K ρ φ (.plain TyM.err) (.tPi caps t rd)).asTy := by
  show (match run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
      | some ((v, _), _) => Sem.ty v.asTy
      | none => .ty TyM.err)
    = .ty (match run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
      | some ((v, _), _) => Sem.ty v.asTy
      | none => .ty TyM.err).asTy
  cases run K ρ φ (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) <;> rfl

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
    show Sem.ty (TyM.prop (Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) a
        = Value.mean K.dm (codeMeaning K) K.Γ ρ φ
          (.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain TyM.err) A).asTy) b))
      = Sem.ty (TyM.prop (meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) a
        = meanV K ρ φ (.plain (meanV K ρ φ (.plain TyM.err) A).asTy) b))
    rw [meanV_eq_mean_aux (.plain TyM.err) A, meanV_eq_mean_aux _ a, meanV_eq_mean_aux _ b]
  | .tRef A => meanV_eq_mean_aux (.plain TyM.err) A
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
          (match hint.data K.dm.read with | some (n, ps') => if n = ty then some ps' else none | none => none)
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
    show Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.fieldTy d ps c i earlier)) v
        :: Value.meanFields K.dm (codeMeaning K) K.Γ ρ φ d ps c (i + 1)
          (earlier ++ [Value.mean K.dm (codeMeaning K) K.Γ ρ φ (.plain (K.dm.fieldTy d ps c i earlier)) v]) vs
      = meanV K ρ φ (.plain (K.dm.fieldTy d ps c i earlier)) v
        :: meanFields K ρ φ d ps c (i + 1) (earlier ++ [meanV K ρ φ (.plain (K.dm.fieldTy d ps c i earlier)) v]) vs
    rw [meanV_eq_mean_aux _ v, meanFields_eq_mean d ps c (i + 1) _ vs]
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
