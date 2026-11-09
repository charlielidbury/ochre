import Ochr.Meaning.Places

/-!
# The reference run (docs/18 Def. "reference run", the meaning of code [Q2])

`run` is the meaning of running a term: a state transformer on meanings (`SState`), returning
the result's meaning as a function of the future together with its type, or `none` where the
run goes wrong. It follows the machine's rules except four (docs/18): every call applies the
callee's meaning and never runs its body; before a place is read, borrowed or matched it ends
exactly the borrows the place's meaning depends on (`SState.access`); a match on data reads
the tag of the scrutinee's meaning, so nothing is stuck and nothing is split; `Id`, `Eq` and
`J` mean as in the model, and statements run on a copy that is thrown away.

Structurally recursive on the term: the only recursion into code is into subterms (a `let`'s
parts, a match's arms, a closure's body when its meaning is *formed*, `mkTele`). A call applies
a meaning (`applyTele`). Recursive functions mean their guarded fixpoint (docs/24 §4): a call
through a function's binding of itself at an argument whose rank does not drop below the
binding's bound is an error (`SBinding.recBound`).

## Status (milestone 2, in progress)

The first-order clauses are defined. The clauses that need the whole machinery are named
holes, listed in docs/31 §"Milestone 2": `callHole` (apply the callee's Π-shape, read off its
Π-type value by running the parameter types and codomain), `fixHole` (closure formation by
`mkTele`, with the guarded fixpoint), `piHole` (Π-type formation at the declared sort),
`matchHole` (an arm by the tag, with D84's drop at the join), `idHole` (both sides on copies,
every borrow ended, every position compared), `jHole` (the transported term), `ctorHole`
(constructor values through `DataModel.ctorM` with field hints).
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

/-- The context of a run: the data model, the declarations, the meanings of the globals and the
decisions read from syntax. -/
structure RunCtx : Type 3 where
  dm : DataModel
  Γ : List IndDecl
  C : CodeMeaning
  D : Decisions

/-- A type as the run knows it: its meaning, and, for a Π-type, its shape (parameters and
output), which applying a function value needs and which neither the opaque carrier nor the
value can give back (docs/31 D9). -/
structure TyS : Type 3 where
  m : TyM
  shape : Option (List PiParam × PiOut) := none
  /-- a borrow-typed result's label: what a call fills when it returns -/
  label : Option Nat := none

/-- A result: a meaning as a function of the future, with its type. -/
abbrev Res : Type 3 := SVal × TyS

section
variable (K : RunCtx) (ρ : Assignment)

/-- The declared-type readings of the top frame, innermost first (`Decide.placeDecl`'s scope). -/
def scopeOf (s : SState) : List DeclInfo :=
  match s.env.getLast? with
  | some fr => (fr.binds.map (·.decl)).reverse
  | none => []

/-- The state's top frame extended by bindings holding the given meanings (a Π's or a
closure's parameters at formation). -/
def extendBy (s : SState) (acc : List Sem) : SState :=
  acc.foldl (fun s a => s.pushBind { ty := .err, val := fun _ => a }) s

/-- The empty state with one empty frame (a sealed program's run starts here). -/
def emptyState : SState := { env := [{}], shape := fun _ => none, nextLoan := 0 }

/-- A closure's frame: its captured values at their recorded types. -/
def capsState (vs : List Sem) (tys : List (DeclInfo × TyM)) : List SBinding :=
  (vs.zip tys).map fun (v, (d, T)) => { ty := T, val := fun _ => v, decl := d }

/-- The state with one frame holding the given bindings (a closure's code runs in it). -/
def stateOf (bs : List SBinding) : SState := { env := [{ binds := bs }], shape := fun _ => none, nextLoan := 0 }

/-- Resolve a place to its root position and path. -/
def resolve (s : SState) (p : Place) : Option (Pos × List Step) :=
  let (i, steps) := p.steps
  (s.varPos i).map (·, steps)

/-- The content of a place after [Access]: its meaning (future-independent, so read under the
constant future) and its type. -/
noncomputable def contentOf (p : Place) : SM (Sem × TyM × Pos × List Step) := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let s := s.access pos
    match Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos noFuture) steps with
    | some (v, T) => some ((v, T, pos, steps), s)
    | none => none
  | none => none

/-- Set the content of a place (no access: the caller has done it). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  match Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps (s.valAt pos noFuture) with
  | some w => some (⟨⟩, s.setAt pos fun _ => w)
  | none => none

/-- [Read]: the content; a copy leaves the place, a move leaves `moved` (D80: by the declared
reading). Reading `⊥`, or a value holding it, is an error. -/
noncomputable def readPlace (p : Place) (copy : Bool) : SM Res := do
  let (v, T, pos, steps) ← contentOf K p
  if ¬ v.whole then SM.fail else
  if copy then pure (fun _ => v, ⟨T, none, none⟩) else do
    setContent K pos steps .moved
    pure (fun _ => v, ⟨T, none, none⟩)

/-- [Borrow] `&p` with a fresh label `l`: the place now means `l`'s final content (at the path,
inside its value), and the borrow its old content, whole. -/
noncomputable def borrowPlace (p : Place) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K p s
  if ¬ v.whole then none else
  let (l, s) := s.freshLoan
  let T0 := s.tyAt pos
  let old := s.valAt pos
  let s := s.setAt pos fun φ => (Sem.updAt K.dm K.Γ T0 (fun _ => φ l) steps (old φ)).getD .err
  some (((fun _ => v), ⟨T, none, some l⟩), s)

/-- The future updated at several labels. -/
def Future.updList (φ : Future) : List (Nat × Sem) → Future
  | [] => φ
  | (l, e) :: rest => (φ.upd l e).updList rest

/-- A call, on the evaluated callee and arguments (docs/18 Def. "reference run", first clause):
apply the callee's meaning along its shape. For a borrow-free result each lent place's final
content is fixed to its component of the finals (the future at the argument's label); for a
result `&U`, a fresh label `k`, the result holds the forward value, and each lent place reads
its component of the backward function at the final content of `k`. A callee without a shape,
or an ill-typed application, is an error. The guard of a recursive call (`SBinding.recBound`)
and a statement call's copy are the caller's (`run`'s `.call` clause). -/
noncomputable def callOf (fv : Res) (args : List Res) : SM Res := fun s =>
  match fv.2.shape with
  | some (ps, out) =>
    match (fv.1 noFuture).as (piCar0 ps [] PUnit out) with
    | some F =>
      let argSems := args.map (·.1 noFuture)
      let labels := args.filterMap (·.2.label)
      match applyTele ps [] PUnit (fun _ => []) out F argSems with
      | some (.data r finals) =>
        let s := s.mapVals fun _ v φ => v (φ.updList (labels.zip finals))
        let B := match out with | .data B => B argSems | .ref U => U argSems
        some ((fun _ => r, ⟨B, none, none⟩), s)
      | some (.ref U fwd back) =>
        let (k, s) := s.freshLoan
        let s := s.mapVals fun _ v φ =>
          match U.dec0 (φ k) with
          | some x => v (φ.updList (labels.zip (back x)))
          | none => .err
        some ((fun _ => U.enc0 fwd, ⟨U, none, some k⟩), s)
      | none => none
    | none => none
  | none => none

/-- D84, the drop at the join: every place some arm of the match moves (`Decisions.joinMoves`,
static) is set to `moved` after the match, on every path. -/
noncomputable def joinDrop (t : Term) (s : SState) : SState :=
  (K.D.joinMoves (scopeOf s) t).foldl (fun s q =>
    match resolve s q with
    | some (pos, steps) =>
      match Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => .moved) steps (s.valAt pos noFuture) with
      | some w => s.setAt pos fun _ => w
      | none => s
    | none => s) s

/-- An observation for `Id` (docs/27 Def. 5): the side's result and, after ending every live
borrow of its copy, the meaning of every position, all future-independent. -/
noncomputable def observation (r : Res) (s : SState) : List Sem :=
  let s := s.liveLabels.foldl SState.endLabel s
  r.1 noFuture :: s.positions.map fun p => s.valAt p noFuture


/-- A constructor value from its parameters' and fields' meanings (`DataModel.ctorM`); with no
parameters written, they are read off the expected type (D8). -/
noncomputable def ctorOf (d : IndDecl) (hint : TyM) (ps fs : List Sem) (c : Nat) : Option Res :=
  let ps? := if ps.isEmpty && !d.params.isEmpty then K.dm.paramsOf d hint else some ps
  ps?.map fun ps => (fun _ => K.dm.ctorM d ps c fs, ⟨K.dm.tyM d ps, none, none⟩)

mutual
/-- The reference run of a term, at the type `hint` its context expects (`err` for none). -/
noncomputable def run (hint : TyM) : Term → SM Res
  | .place p => fun s =>
    readPlace K p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s
  | .borrow p => borrowPlace K p
  | .assign p u => do
    let (_, T, pos, steps) ← contentOf K p
    let (v, _) ← run T u
    setContent K pos steps (v noFuture)
    pure (fun _ => .el0 Unit (), ⟨.ty0 Unit, none, none⟩)
  | .letIn _ u w => fun s => do
    let ((v, T), s) ← run .err u s
    let s := s.pushBind { ty := T.m, val := v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← run hint w s
    -- [Drop] of the binding: forgetting it (its borrows end through `access` where read)
    let s := s.dropLast
    some ((r, R), s)
  | .seq u w => do
    let _ ← run .err u
    run hint w
  | .matchNat p z u => fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access]); `⊥` is an error;
    -- then D84's drop at the join
    let ((v, _, _, _), s) ← contentOf K p s
    let arm? : Option Term := match v.asNat with
      | some 0 => some z
      | some (_ + 1) => some u
      | none => match v with
        | .ctor "Nat" 0 [] => some z
        | .ctor "Nat" 1 _ => some u
        | _ => none
    match arm? with
    | some z' => do
      let ((r, R), s) ← (if z' == z then run hint z s else run hint u s)
      some ((r, R), joinDrop K (.matchNat p z u) s)
    | none => none
  | .matchInd p n arms => fun s => do
    let ((v, T, _, _), s) ← contentOf K p s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match v with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => match T.dataOf K.dm K.Γ with
        | some (d, ps) => (K.dm.fieldsOf d ps v).map (·.1)
        | none => none
    match c? with
    | some c => do
      let ((r, R), s) ← runArm hint c arms s
      some ((r, R), joinDrop K (.matchInd p n arms) s)
    | none => none
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      pure (fun _ => .ty (K.dm.tyM d psM), ⟨.univ d.sort, none, none⟩)
    | none => SM.fail
  | .ctor ty c _ ps args => do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      let ps' := if ps.isEmpty && !d.params.isEmpty then K.dm.paramsOf d hint else some psM
      match ps' with
      | some ps' =>
        let fs ← runFields d ps' c 0 [] args
        match ctorOf K d hint ps' fs c with
        | some r => pure r
        | none => SM.fail
      | none => SM.fail
    | none => SM.fail
  | .const n => pure (fun _ => K.C.global n, ⟨.err, none, none⟩)
  | .val v => pure (fun φ => meanV φ hint v, ⟨hint, none, none⟩)
  | .sort l => pure (fun _ => .ty (.univ l), ⟨.univ (sortSucc l), none, none⟩)
  | .pi hs ds c => fun s =>
    -- [T-Pi]: each parameter type is a function of the earlier parameters' meanings, read by
    -- running it in the current frame extended by them (`runDoms`); the output likewise; the
    -- carrier at the declared sort (D55, `Decisions.piSort`)
    let ps := runDoms s ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc =>
        match run .err U (extendBy s acc) with
        | some ((v, _), _) => (v noFuture).asTy
        | none => .err
      | c => .data fun acc =>
        match run .err c (extendBy s acc) with
        | some ((v, _), _) => (v noFuture).asTy
        | none => .err
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    let T : TyM := match l with
      | 0 => .prop (piProp ps [] fun acc => match out with | .data B => (B acc).true | .ref _ => False)
      | 1 => .ty0 (piCar0 ps [] PUnit out)
      | 2 => .ty1 (piCar1 ps [] fun acc => match out with | .data B => B acc | .ref U => U acc)
      | 3 => .ty2 (piCar2 ps [] fun acc => match out with | .data B => B acc | .ref U => U acc)
      | _ => .err
    some ((fun _ => .ty T, ⟨.univ l, some (ps, out), none⟩), s)
  | .fix self hs ds c dec body => fun s =>
    -- [Closure] (D51, D53, D80): a closure means a function on its annotated domain, read off
    -- the reference run of its body in the forming frame extended by `self` and the parameters
    -- (the body's layout `[caps…, self, x̄]`; the captures are the forming frame's bindings, read
    -- in place). A recursive `fix` means its guarded fixpoint by stages (docs/24 §4): stage 0
    -- binds `self` to `err`, stage `k + 1` to stage `k`'s closure, and the function at arguments
    -- whose decreasing argument has rank `r` is stage `r + 1`; so a call that does not decrease
    -- reaches stage 0 and means `err`, and `mkTele` then makes the closure mean `err`.
    let ps := runDoms s ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc =>
        match run .err U (extendBy s acc) with
        | some ((v, _), _) => (v noFuture).asTy
        | none => .err
      | c => .data fun acc =>
        match run .err c (extendBy s acc) with
        | some ((v, _), _) => (v noFuture).asTy
        | none => .err
    let piT := piCar0 ps [] PUnit out
    let start := s.nextLoan
    let base := ((s.env.getLast?).map (·.binds.length)).getD 0 + 1
    -- the body at arguments, with `self` meaning `selfM`
    let bodyAt (selfM : Sem) (args : List Sem) : Option BodyOut :=
      let s₁ := s.pushBind { ty := .ty0 piT, val := fun _ => selfM }
      let s₂ := ((args.zip ps).foldl (fun (sa : SState × List Sem) (ap : Sem × PiParam) =>
        (sa.1.pushBind { ty := ap.2.dom sa.2, val := fun _ => ap.1 }, sa.2 ++ [ap.1])) (s₁, [])).1
      let codT := match out with | .data B => B args | .ref U => U args
      match run codT body s₂ with
      | some ((r, R), s₃) =>
        -- popping the frame ends the borrows the body made; a borrow parameter's final content
        -- is what its holder then holds (writes through it changed the holder's content)
        let s₄ := (s₃.liveLabels.filter (· ≥ start)).foldl SState.endLabel s₃
        let finals := (List.range ds.length).filterMap fun i =>
          if ((ps[i]?).map (·.isRef)).getD false then some (s₄.valAt (.bind s₄.topIdx (base + i))) else none
        some ⟨r, finals, R.label⟩
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem :=
      match mkTele ps [] PUnit (fun fs => some ((), fs)) out g with
      | some F => .el0 piT F
      | none => .err
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun _ gk => bodyAt (closureOf gk))
    -- the rank of the decreasing argument (`by xⱼ`), through its data carrier
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
    some ((fun _ => closureOf g, ⟨.ty0 piT, some (ps, out), none⟩), s')
  | .call f args hd => fun s =>
    let body : SM Res := do
      let fv ← run .err f
      let as ← runArgs fv.2.shape 0 [] args
      callOf fv as
    -- a statement call runs on a copy that is thrown away (E1; `Decisions.flags`, aligned)
    if (K.D.flags (scopeOf s) (.call f args hd)).1 then SM.onCopy body s else body s
  | .nat => pure (fun _ => .ty (.ty0 Nat), ⟨.univ 1, none, none⟩)
  | .unit => pure (fun _ => .ty (.ty0 Unit), ⟨.univ 1, none, none⟩)
  | .zero => pure (fun _ => .el0 Nat 0, ⟨.ty0 Nat, none, none⟩)
  | .tt => pure (fun _ => .el0 Unit (), ⟨.ty0 Unit, none, none⟩)
  | .succ u => do
    let (v, _) ← run (.ty0 Nat) u
    pure (fun φ => (v φ).succ, ⟨.ty0 Nat, none, none⟩)
  | .eq A a b => SM.onCopy do
    let (TA, _) ← run .err A
    let T := (TA noFuture).asTy
    let (va, _) ← SM.onCopy (run T a)
    let (vb, _) ← SM.onCopy (run T b)
    pure (fun φ => .ty (.prop (va φ = vb φ)), ⟨.univ 0, none, none⟩)
  | .cong _ _ | .prim "symm" _ | .prim "trans" _ | .prim "rewrite" _ | .prim "rewriteR" _ =>
    pure (fun _ => .proof, ⟨.err, none, none⟩)
  | .ref A => do
    let (TA, _) ← run .err A
    pure (TA, ⟨.univ 1, none, none⟩)
  | .id A t u => fun s => do
    -- `Id` observes: each side on a copy of the state, every borrow ended, the result and every
    -- position compared (D84: moved places are definite values, so they compare too)
    let ((TA, _), _) ← SM.onCopy (run .err A) s
    let T := (TA noFuture).asTy
    let o₁ ← (run T t s).map fun (r, s') => observation r s'
    let o₂ ← (run T u s).map fun (r, s') => observation r s'
    some ((fun _ => .ty (.prop (o₁ = o₂)), ⟨.univ 0, none, none⟩), s)
  | .prim "J" [A, a, b, P, h, t] => do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (run .err A)
    let _ ← SM.onCopy (run .err a)
    let _ ← SM.onCopy (run .err b)
    let _ ← SM.onCopy (run .err P)
    let _ ← SM.onCopy (run .err h)
    run hint t
  | .prim "clone" [u] | .prim "peek" [u] => match u with
    | .place p => readPlace K p true
    | _ => run hint u
  | .prim "inplace" [u] => run hint u
  | .prim _ _ => SM.fail
  | .ascribe u A => do
    let (TA, _) ← SM.onCopy (run .err A)
    let T := (TA noFuture).asTy
    let (v, _) ← run T u
    pure (v, ⟨T, none, none⟩)
termination_by structural t => t

/-- Arm `c` of a match, run at the match's expected type. -/
noncomputable def runArm (hint : TyM) (c : Nat) : List (Hint × Term) → SM Res
  | [] => SM.fail
  | (_, t) :: rest => if c = 0 then run hint t else runArm hint (c - 1) rest
termination_by structural arms => arms

/-- The parameters of a Π-term as the model reads them: each domain term's meaning as a function
of the earlier parameters' meanings, run in the forming state extended by them; `&A` marks a
borrow parameter with content type `A`. -/
noncomputable def runDoms (s : SState) : List Term → List PiParam
  | [] => []
  | .ref A :: ds =>
    ⟨true, fun acc => match run .err A (extendBy s acc) with
      | some ((v, _), _) => (v noFuture).asTy
      | none => .err⟩ :: runDoms s ds
  | d :: ds =>
    ⟨false, fun acc => match run .err d (extendBy s acc) with
      | some ((v, _), _) => (v noFuture).asTy
      | none => .err⟩ :: runDoms s ds
termination_by structural ds => ds

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← SM.onCopy (run (K.dm.paramTy d i earlier) a)
    let s := v noFuture
    let rest ← runParams d (i + 1) (earlier ++ [s]) as
    pure (s :: rest)
termination_by structural as => as

/-- A constructor's fields, each at its field type at the earlier fields. -/
noncomputable def runFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← run (K.dm.fieldTy d ps c i earlier) a
    let s := v noFuture
    let rest ← runFields d ps c (i + 1) (earlier ++ [s]) as
    pure (s :: rest)
termination_by structural as => as

/-- A call's arguments, each at its parameter type from the callee's shape (D82, [Call-type]). -/
noncomputable def runArgs (shape : Option (List PiParam × PiOut)) (i : Nat) (earlier : List Sem) :
    List Term → SM (List Res)
  | [] => pure []
  | a :: as => do
    let T := match shape with
      | some (ps, _) => match ps[i]? with | some p => p.dom earlier | none => .err
      | none => .err
    let r ← run T a
    let rest ← runArgs shape (i + 1) (earlier ++ [r.1 noFuture]) as
    pure (r :: rest)
termination_by structural as => as

/-- The meaning of a value, with the code-dependent forms given by the run itself (the knot of
`Value.mean`'s `CodeMeaning`): a sealed program is its program run from the empty state at the
hint, read under the future; a closure or Π-closure is its `fix`/`pi` term run in a frame
holding its captures at their recorded types (D51); a global is `K.C.global`. The other clauses
are `Value.mean`'s (`meanV_eq_mean`). -/
noncomputable def meanV (φ : Future) (hint : TyM) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (meanV φ (.ty0 Nat) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => K.C.global n
  | .clo caps t rd => match run .err t (stateOf (capsState (capsVals φ caps) (capsTys φ rd))) with
    | some ((v, _), _) => v noFuture
    | none => .err
  | .borrow _ w => meanV φ hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  | .sealed t => match run hint t emptyState with
    | some ((v, _), _) => v φ
    | none => .err
  | .proof => .proof
  | .tNat => .ty (.ty0 Nat)
  | .tUnit => .ty (.ty0 Unit)
  | .tEq A a b =>
    let T := (meanV φ .err A).asTy
    .ty (.prop (meanV φ T a = meanV φ T b))
  | .tRef A => meanV φ .err A
  | .tPi caps t rd => match run .err t (stateOf (capsState (capsVals φ caps) (capsTys φ rd))) with
    | some ((v, _), _) => v noFuture
    | none => .err
  | .sort l => .ty (.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let ps? := if ps.isEmpty && !d.params.isEmpty then K.dm.paramsOf d hint
        else some (meanParams φ d 0 [] ps)
      match ps? with
      | some ps' => K.dm.ctorM d ps' c (meanFields φ d ps' c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => .ty (K.dm.tyM d (meanParams φ d 0 [] args))
    | none => .ty .err
termination_by structural v => v

noncomputable def meanFields (φ : Future) (d : IndDecl) (ps : List Sem) (c i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV φ (K.dm.fieldTy d ps c i earlier) v
    s :: meanFields φ d ps c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

noncomputable def meanParams (φ : Future) (d : IndDecl) (i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV φ (K.dm.paramTy d i earlier) v
    s :: meanParams φ d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- A closure's or Π-closure's captured values, each read as a value (D51). -/
noncomputable def capsVals (φ : Future) : List Value → List Sem
  | [] => []
  | v :: vs => meanV φ .err v :: capsVals φ vs
termination_by structural vs => vs

/-- The captures' recorded declared types, each read as a type (D82). -/
noncomputable def capsTys (φ : Future) : List (DeclInfo × Value) → List (DeclInfo × TyM)
  | [] => []
  | (d, T) :: rest => (d, (meanV φ .err T).asTy) :: capsTys φ rest
termination_by structural rest => rest
end

/-- The code meaning the run induces, at the assignment `ρ` (the knot of `Value.mean`). Its
assignment argument is ignored: `Value.mean` is only ever read at the one assignment of the
state, which is this `ρ`. -/
noncomputable def codeMeaning : CodeMeaning where
  global := K.C.global
  sealed _ φ hint t := meanV K ρ φ hint (.sealed t)
  clo _ φ caps t rd := meanV K ρ φ .err (.clo caps t rd)
  pi _ φ caps t rd := (meanV K ρ φ .err (.tPi caps t rd)).asTy
  paramTy _ P ws j := match run K ρ .err (.val P) emptyState with
    | some ((_, T), _) => match T.shape with
      | some (ps, out) =>
        let acc := ws.map (meanV K ρ noFuture .err)
        if j < ps.length then (ps[j]?.map (·.dom (acc.take j))).getD .err
        else match out with | .data B => B acc | .ref U => U acc
      | none => .err
    | none => .err

/-- The knot ties: `Value.mean` at the induced code meaning is `meanV`. By induction on the
value; every clause but the code-dependent ones is the same text. -/
theorem meanV_eq_mean (ρ : Assignment) (φ : Future) (hint : TyM) (v : Value) :
    Value.mean K.dm (codeMeaning K ρ) K.Γ ρ φ hint v = meanV K ρ φ hint v := by
  sorry

end

end Ochr.Meaning
