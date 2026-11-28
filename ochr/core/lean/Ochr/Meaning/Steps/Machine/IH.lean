import Ochr.Meaning.Steps.Machine.MachineLeaves

/-!
# The induction hypothesis over the machine's mutual block

`Machine.lean`'s mutual block (118 functions, every one reaching every other: one strongly
connected call graph) recurs on the fuel, each call at the fuel one less. So the property is
proved for all of them at once, by induction on the fuel: `MachineGrows tb nf` says every function
of the block at fuel `nf` only extends the tables, from a state with the tables `tb`. A function
that takes a computation (a continuation, an arm, a run) assumes it of that computation.
`joinCont` returns a continuation, which keeps the property too (`joinContRet`). `joinLogged`,
`lentInFields` and `ctorArms` take no fuel and are proved on their own (`growsIn_joinLogged`, …).

The step for one function at `nf + 1` is its body walked by `grows_go ih` (`Steps/Machine/Step*.lean`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope

/-- Every successful run of `x` from a state with the tables `tb` returns a value satisfying `P`. -/
structure RetOk (tb : Tab) {α : Type} (x : M α) (P : α → Prop) : Prop where
  run : ∀ s f l a s' f' l', OnTab tb s → runAll x s f l = ((.ok (.ok (a, s')), f'), l') → P a

theorem growsIn_bind_ret {G : Tab} {α β : Type} {x : M α} {k : α → M β} {P : α → Prop} (hx : GrowsIn G x)
    (hr : RetOk G x P) (hk : ∀ a, P a → GrowsIn G (k a)) : GrowsIn G (x >>= k) := by
  intro s f l b s' f' l' hs h
  rw [runAll_bind] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h
  · intro h
    have h1 := hx s f l a s₁ f₁ l₁ hs e
    exact h1.trans (hk a (hr.run s f l a s₁ f₁ l₁ hs e) s₁ f₁ l₁ b s' f' l' (hs.of_grows h1) h)

@[grows] theorem growsIn_joinLogged {G : Tab} (st : List Place) : GrowsIn G (joinLogged st) := by
  unfold joinLogged; grows_go

@[grows] theorem growsIn_lentInFields {G : Tab} (q : Place) (g : FieldRef) : GrowsIn G (lentInFields q g) := by
  unfold lentInFields; grows_go

/-- D146's pairing of a match's arms with the constructors (main's merge, lead49): it takes no fuel. -/
@[grows] theorem growsIn_ctorArms {G : Tab} (d : IndDecl) (p : Place) (arms : List (Hint × Term)) :
    GrowsIn G (ctorArms d p arms) := by
  unfold ctorArms; grows_go

/-- Every function of the machine's mutual block at fuel `nf` only extends the tables, from a
state with the tables `tb`. -/
structure MachineGrows (tb : Tab) (nf : Nat) : Prop where
  substV : ∀ (x : Value) (r : Value) (v : Value), GrowsIn tb (Ochr.substV nf x r v)
  substT : ∀ (x : Value) (r : Value) (t : Term), GrowsIn tb (Ochr.substT nf x r t)
  substEnv : ∀ (x : Value) (r : Value) (types : Bool), GrowsIn tb (Ochr.substEnv nf x r types)
  nfSealed : ∀ (t : Term), GrowsIn tb (Ochr.nfSealed nf t)
  endBorrow : ∀ (l : Nat), GrowsIn tb (Ochr.endBorrow nf l)
  lentUnknown : ∀ (v : Value), GrowsIn tb (Ochr.lentUnknown nf v)
  repackCheck : ∀ (what : String) (v : Value) (T : Value), GrowsIn tb (Ochr.repackCheck nf what v T)
  repackAt : ∀ (p : Place) (T : Value) (what : String), GrowsIn tb (Ochr.repackAt nf p T what)
  bodyReturns : ∀ (what : String) (v : Value) (T : Value) (lent : List Place) (lentWhat : String), GrowsIn tb (Ochr.bodyReturns nf what v T lent lentWhat)
  endAll : GrowsIn tb (Ochr.endAll nf)
  obsResult : ∀ (r : Value) (T : Option Value) (σw? : Option Nat), GrowsIn tb (Ochr.obsResult nf r T σw?)
  endTopLoan : ∀ (l : Nat) (site : String) (p? : Option Place), GrowsIn tb (Ochr.endTopLoan nf l site p?)
  accessPath : ∀ (p : Place), GrowsIn tb (Ochr.accessPath nf p)
  accessInside : ∀ (p : Place) (owned : Bool), GrowsIn tb (Ochr.accessInside nf p owned)
  openWrite : ∀ (p : Place), GrowsIn tb (Ochr.openWrite nf p)
  accessNeutralHead : ∀ (p : Place), GrowsIn tb (Ochr.accessNeutralHead nf p)
  readPlace : ∀ (p : Place), GrowsIn tb (Ochr.readPlace nf p)
  copyRead : ∀ (p : Place), GrowsIn tb (Ochr.copyRead nf p)
  borrowPlace : ∀ (p : Place), GrowsIn tb (Ochr.borrowPlace nf p)
  assignPlace : ∀ (p : Place), GrowsIn tb (Ochr.assignPlace nf p)
  dropTopBind : GrowsIn tb (Ochr.dropTopBind nf)
  endLoansOfTopBind : ∀ (f : Nat), GrowsIn tb (Ochr.endLoansOfTopBind nf f)
  dropValue : ∀ (v : Value) (T : Option Value), GrowsIn tb (Ochr.dropValue nf v T)
  endLoansOfTopTemp : GrowsIn tb (Ochr.endLoansOfTopTemp nf)
  popFrame : GrowsIn tb (Ochr.popFrame nf)
  popBody : ∀ (start : Option Env) (v : Value) (T : Option Value) (site : String), GrowsIn tb (Ochr.popBody nf start v T site)
  placeType? : ∀ (p : Place), GrowsIn tb (Ochr.placeType? nf p)
  placeType : ∀ (p : Place), GrowsIn tb (Ochr.placeType nf p)
  natPlace : ∀ (q : Place), GrowsIn tb (Ochr.natPlace nf q)
  projIn : ∀ (p : Place), GrowsIn tb (Ochr.projIn nf p)
  projMatch : ∀ (q : Place) (i : Nat), GrowsIn tb (Ochr.projMatch nf q i)
  projStep : ∀ (s : Place × Nat × (Place → Place)), GrowsIn tb (Ochr.projStep nf s)
  depFieldType : ∀ (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place) (declared : Bool), GrowsIn tb (Ochr.depFieldType nf d ps g q declared)
  fieldDeclType : ∀ (p : Place), GrowsIn tb (Ochr.fieldDeclType nf p)
  packedErr : ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.packedErr nf v T)
  convVal : ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.convVal nf v T)
  valType? : ∀ (v : Value), GrowsIn tb (Ochr.valType? nf v)
  valType : ∀ (v : Value), GrowsIn tb (Ochr.valType nf v)
  sealedType? : ∀ (t : Term), GrowsIn tb (Ochr.sealedType? nf t)
  fieldTele : ∀ (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value) (hval : ∀ i v, GrowsIn tb (val i v)) (upto : Option Nat), GrowsIn tb (Ochr.fieldTele nf d ps c val upto)
  fieldTypes : ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldTypes nf d ps c)
  fieldTypesOf : ∀ (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value) (upto : Option Nat), GrowsIn tb (Ochr.fieldTypesOf nf d ps c fs upto)
  fieldsGeneric : ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldsGeneric nf d ps c)
  fieldTypeAt : ∀ (d : IndDecl) (sol : Array (Option Value)) (c : Nat) (i : Nat) (earlier : List Value), GrowsIn tb (Ochr.fieldTypeAt nf d sol c i earlier)
  indValType? : ∀ (t : String) (c : Nat) (fs : List Value), GrowsIn tb (Ochr.indValType? nf t c fs)
  bindDataFields : ∀ (p : Place) (d : IndDecl) (ps : List Value) (c : Nat) (arm : Term), GrowsIn tb (Ochr.bindDataFields nf p d ps c arm)
  piSort : ∀ (T : Value), GrowsIn tb (Ochr.piSort nf T)
  evalType : ∀ (t : Term), GrowsIn tb (Ochr.evalType nf t)
  capture : ∀ (t : Term), GrowsIn tb (Ochr.capture nf t)
  conv : ∀ (v : Value) (w : Value), GrowsIn tb (Ochr.conv nf v w)
  convList : ∀ (as : List Value) (bs : List Value), GrowsIn tb (Ochr.convList nf as bs)
  convTList : ∀ (as : List Term) (bs : List Term), GrowsIn tb (Ochr.convTList nf as bs)
  convPi : ∀ (P : Value) (Q : Value), GrowsIn tb (Ochr.convPi nf P Q)
  convT : ∀ (t : Term) (u : Term), GrowsIn tb (Ochr.convT nf t u)
  convFn : ∀ (f : Value) (g : Value), GrowsIn tb (Ochr.convFn nf f g)
  convFnRun : ∀ (f : Value) (g : Value) (pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term), GrowsIn tb (Ochr.convFnRun nf f g pf cs hs ds c)
  mkEqM : ∀ (A : Value) (a : Value) (b : Value), GrowsIn tb (Ochr.mkEqM nf A a b)
  rewriteGoal : ∀ (rev : Bool) (h : Term) (G : Value), GrowsIn tb (Ochr.rewriteGoal nf rev h G)
  expectTy : ∀ (what : String) (T : Option Value) (A : Value), GrowsIn tb (Ochr.expectTy nf what T A)
  eval : ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.eval nf typed t hint)
  evalAt : ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalAt nf typed t hint)
  jMotiveAt : ∀ (A : Term) (P : Term) (av : Value), GrowsIn tb (Ochr.jMotiveAt nf A P av)
  evalCore : ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalCore nf typed t hint)
  unknownLent : ∀ (what : String) (ls : List Nat), GrowsIn tb (Ochr.unknownLent nf what ls)
  lentProofAssign : ∀ (p : Place) (u : Term), GrowsIn tb (Ochr.lentProofAssign nf p u)
  lentLeafCheck : ∀ (p : Place) (Tv : Option Value), GrowsIn tb (Ochr.lentLeafCheck nf p Tv)
  evalTInd : ∀ (typed : Bool) (n : String) (as : List Term), GrowsIn tb (Ochr.evalTInd nf typed n as)
  evalParams : ∀ (n : String) (as : List Term) (typed : Bool), GrowsIn tb (Ochr.evalParams nf n as typed)
  checkParams : ∀ (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.checkParams nf d n vs tys)
  evalCtor : ∀ (typed : Bool) (ty : String) (c : Nat) (h : Hint) (pts : List Term) (as : List Term) (hint : Option Value), GrowsIn tb (Ochr.evalCtor nf typed ty c h pts as hint)
  stmtCallee : ∀ (fv : Value) (fT : Option Value) (cls? : Option Nat), GrowsIn tb (Ochr.stmtCallee nf fv fT cls?)
  evalCall : ∀ (typed : Bool) (f : Term) (as : List Term) (head : Bool) (cls? : Option Nat) (res? : Option DeclInfo) (given : Option (Value × List Value)), GrowsIn tb (Ochr.evalCall nf typed f as head cls? res? given)
  argHint : ∀ (fv : Value) (fT : Option Value) (ws : Array Value), GrowsIn tb (Ochr.argHint nf fv fT ws)
  funType? : ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType? nf fv fT)
  funType : ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType nf fv fT)
  callType : ∀ (piTy : Value) (ws : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.callType nf piTy ws tys)
  declCallType : ∀ (piTy : Value) (ws : Array Value), GrowsIn tb (Ochr.declCallType nf piTy ws)
  forceHint : ∀ (hint : Option Value), GrowsIn tb (Ochr.forceHint nf hint)
  paramTypes : ∀ (piTy : Value) (ws : List Value) (need : List Nat), GrowsIn tb (Ochr.paramTypes nf piTy ws need)
  bindTy? : ∀ (pos : Pos), GrowsIn tb (Ochr.bindTy? nf pos)
  endBorrowArgs : ∀ (n : Nat), GrowsIn tb (Ochr.endBorrowArgs nf n)
  runBody : ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value) (B : Option Value), GrowsIn tb (Ochr.runBody nf fv cs t rd ws B)
  runBodyCore : ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value) (B : Option Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term), GrowsIn tb (Ochr.runBodyCore nf fv cs t rd ws B self hs ds c dec body)
  callFn : ∀ (typed : Bool) (fT : Option Value) (n : Nat) (tys : Array (Option Value)) (head : Bool) (cls? : Option Nat) (recUid? : Option Nat) (res : DeclInfo) (fills : Array Bool) (want : Bool) (defer : Bool) (resTy : Option Value), GrowsIn tb (Ochr.callFn nf typed fT n tys head cls? recUid? res fills want defer resTy)
  closeCall : ∀ (n : Nat) (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)), GrowsIn tb (Ochr.closeCall nf n kind res fills tys)
  refine : ∀ (σ : Nat) (r : Value), GrowsIn tb (Ochr.refine nf σ r)
  evalMatch : ∀ (typed : Bool) (p : Place) (z : Term) (s : Term) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatch nf typed p z s expected tail)
  natScrutinee : ∀ (p : Place), GrowsIn tb (Ochr.natScrutinee nf p)
  generalizeNeutral : ∀ (p : Place) (n : Value), GrowsIn tb (Ochr.generalizeNeutral nf p n)
  sealedResultType? : ∀ (t : Term), GrowsIn tb (Ochr.sealedResultType? nf t)
  renormAll : GrowsIn tb (Ochr.renormAll nf)
  renormV : ∀ (v : Value), GrowsIn tb (Ochr.renormV nf v)
  renormT : ∀ (t : Term), GrowsIn tb (Ochr.renormT nf t)
  splitThenClose : ∀ (p : Place) (z : Term) (s : Term) (σ : Nat) (expected : Option Value), GrowsIn tb (Ochr.splitThenClose nf p z s σ expected)
  splitArmsThenClose : ∀ (mt : Term) (σ : Nat) (arms : List (M Value × Term)) (harms : ∀ a ∈ arms, GrowsIn tb a.1) (expected : Option Value), GrowsIn tb (Ochr.splitArmsThenClose nf mt σ arms expected)
  ctorRefinement : ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.ctorRefinement nf d ps c)
  scrutType : ∀ (p : Place) (ty : String), GrowsIn tb (Ochr.scrutType nf p ty)
  evalMatchByType : ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchByType nf typed p ty arms expected tail)
  evalMatchInd : ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchInd nf typed p ty arms expected tail)
  etaInPlace : ∀ (σ : Nat) (d : IndDecl) (ps : List Value), GrowsIn tb (Ochr.etaInPlace nf σ d ps)
  etaPlace : ∀ (q : Place), GrowsIn tb (Ochr.etaPlace nf q)
  movedPlace : ∀ (q : Place), GrowsIn tb (Ochr.movedPlace nf q)
  staticJoin : ∀ (mt : Term), GrowsIn tb (Ochr.staticJoin nf mt)
  joinDrop : ∀ (mt : Term) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinDrop nf mt run)
  joinCont : ∀ (mt : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.joinCont nf mt k)
  joinEnds : ∀ (mt : Term) (tail : Bool) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinEnds nf mt tail run)
  blockEntry : ∀ (mt : Term), GrowsIn tb (Ochr.blockEntry nf mt)
  entryAccess : ∀ (capsS : Array (Place × Nat)), GrowsIn tb (Ochr.entryAccess nf capsS)
  dropAtJoin : ∀ (q : Place), GrowsIn tb (Ochr.dropAtJoin nf q)
  blockCaptures : ∀ (mt : Term) (armMovedAll : List Place), GrowsIn tb (Ochr.blockCaptures nf mt armMovedAll)
  closeBlock : ∀ (mt : Term) (arms : List BlockArm) (harms : ∀ a ∈ arms, GrowsIn tb a.setup ∧ ∀ r, GrowsIn tb (a.body r)) (B? : Option Value), GrowsIn tb (Ochr.closeBlock nf mt arms B?)
  observe : ∀ (typed : Bool) (t : Term) (A : Value) (W : List Pos) (refs : List (Place × Value × Value)) (consumed : List Place), GrowsIn tb (Ochr.observe nf typed t A W refs consumed)
  idType : ∀ (typed : Bool) (A : Term) (t : Term) (u : Term), GrowsIn tb (Ochr.idType nf typed A t u)
  stuckScrutinee : ∀ (t : Term), GrowsIn tb (Ochr.stuckScrutinee nf t)
  findSplit : ∀ (f : String) (G : Value), GrowsIn tb (Ochr.findSplit nf f G)
  generalizeFound : ∀ (n : Value) (T : Value), GrowsIn tb (Ochr.generalizeFound nf n T)
  splitTarget : ∀ (f : String), GrowsIn tb (Ochr.splitTarget nf f)
  checkTail : ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTail nf t k)
  checkTailAt : ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTailAt nf t k)
  checkFix : ∀ (fv : Value) (cs : List Value) (t : Term) (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)), GrowsIn tb (Ochr.checkFix nf fv cs t capRec rd)
  joinContRet : ∀ (mt : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)),
    RetOk tb (Ochr.joinCont nf mt k) (fun k' => ∀ r R, GrowsIn tb (k' r R))

end Ochr.Meaning.Steps.Machine
