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

noncomputable def fixHole (_ : RunCtx) (_ : Assignment) (t : Term) : SM Res := sorry
noncomputable def matchHole (_ : RunCtx) (_ : Assignment) (t : Term) : SM Res := sorry
noncomputable def idHole (_ : RunCtx) (_ : Assignment) (A t u : Term) : SM Res := sorry
noncomputable def jHole (_ : RunCtx) (_ : Assignment) (args : List Term) : SM Res := sorry

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
  | .matchNat p z u => matchHole K ρ (.matchNat p z u)
  | .matchInd p n arms => matchHole K ρ (.matchInd p n arms)
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
  | .val v => pure (fun φ => Value.mean K.dm K.C K.Γ ρ φ hint v, ⟨hint, none, none⟩)
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
  | .fix f hs ds c d b => fixHole K ρ (.fix f hs ds c d b)
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
  | .id A t u => idHole K ρ A t u
  | .prim "J" args => jHole K ρ args
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
end

end

end Ochr.Meaning
