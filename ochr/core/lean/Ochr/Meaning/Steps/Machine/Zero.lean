import Ochr.Meaning.Steps.Machine.IH

/-!
# The base of the induction for the machine's block: every function at fuel `0`

Each is out of fuel at once, or (`convList`, `convTList`) answers an empty list without running.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab}

theorem zero_substV :
    ∀ (x : Value) (r : Value) (v : Value), GrowsIn tb (Ochr.substV 0 x r v) := by
  intro x r v
  unfold Ochr.substV; grows_go

theorem zero_substT :
    ∀ (x : Value) (r : Value) (t : Term), GrowsIn tb (Ochr.substT 0 x r t) := by
  intro x r t
  unfold Ochr.substT; grows_go

theorem zero_substEnv :
    ∀ (x : Value) (r : Value) (types : Bool), GrowsIn tb (Ochr.substEnv 0 x r types) := by
  intro x r types
  unfold Ochr.substEnv; grows_go

theorem zero_nfSealed :
    ∀ (t : Term), GrowsIn tb (Ochr.nfSealed 0 t) := by
  intro t
  unfold Ochr.nfSealed; grows_go

theorem zero_endBorrow :
    ∀ (l : Nat), GrowsIn tb (Ochr.endBorrow 0 l) := by
  intro l
  unfold Ochr.endBorrow; grows_go

theorem zero_lentUnknown :
    ∀ (v : Value), GrowsIn tb (Ochr.lentUnknown 0 v) := by
  intro v
  unfold Ochr.lentUnknown; grows_go

theorem zero_repackCheck :
    ∀ (what : String) (v : Value) (T : Value), GrowsIn tb (Ochr.repackCheck 0 what v T) := by
  intro what v T
  unfold Ochr.repackCheck; grows_go

theorem zero_repackAt :
    ∀ (p : Place) (T : Value) (what : String), GrowsIn tb (Ochr.repackAt 0 p T what) := by
  intro p T what
  unfold Ochr.repackAt; grows_go

theorem zero_bodyReturns :
    ∀ (what : String) (v : Value) (T : Value) (lent : List Place) (lentWhat : String), GrowsIn tb (Ochr.bodyReturns 0 what v T lent lentWhat) := by
  intro what v T lent lentWhat
  unfold Ochr.bodyReturns; grows_go

theorem zero_endAll :
    GrowsIn tb (Ochr.endAll 0) := by
  unfold Ochr.endAll; grows_go

theorem zero_obsResult :
    ∀ (r : Value) (σw? : Option Nat), GrowsIn tb (Ochr.obsResult 0 r σw?) := by
  intro r σw?
  unfold Ochr.obsResult; grows_go

theorem zero_endTopLoan :
    ∀ (l : Nat) (site : String), GrowsIn tb (Ochr.endTopLoan 0 l site) := by
  intro l site
  unfold Ochr.endTopLoan; grows_go

theorem zero_accessPath :
    ∀ (p : Place), GrowsIn tb (Ochr.accessPath 0 p) := by
  intro p
  unfold Ochr.accessPath; grows_go

theorem zero_accessInside :
    ∀ (p : Place) (owned : Bool), GrowsIn tb (Ochr.accessInside 0 p owned) := by
  intro p owned
  unfold Ochr.accessInside; grows_go

theorem zero_accessNeutralHead :
    ∀ (p : Place), GrowsIn tb (Ochr.accessNeutralHead 0 p) := by
  intro p
  unfold Ochr.accessNeutralHead; grows_go

theorem zero_readPlace :
    ∀ (p : Place), GrowsIn tb (Ochr.readPlace 0 p) := by
  intro p
  unfold Ochr.readPlace; grows_go

theorem zero_copyRead :
    ∀ (p : Place), GrowsIn tb (Ochr.copyRead 0 p) := by
  intro p
  unfold Ochr.copyRead; grows_go

theorem zero_borrowPlace :
    ∀ (p : Place), GrowsIn tb (Ochr.borrowPlace 0 p) := by
  intro p
  unfold Ochr.borrowPlace; grows_go

theorem zero_assignPlace :
    ∀ (p : Place) (v : Value), GrowsIn tb (Ochr.assignPlace 0 p v) := by
  intro p v
  unfold Ochr.assignPlace; grows_go

theorem zero_dropTopBind :
    GrowsIn tb (Ochr.dropTopBind 0) := by
  unfold Ochr.dropTopBind; grows_go

theorem zero_endLoansOfTopBind :
    ∀ (f : Nat), GrowsIn tb (Ochr.endLoansOfTopBind 0 f) := by
  intro f
  unfold Ochr.endLoansOfTopBind; grows_go

theorem zero_dropValue :
    ∀ (v : Value), GrowsIn tb (Ochr.dropValue 0 v) := by
  intro v
  unfold Ochr.dropValue; grows_go

theorem zero_endLoansOfTopTemp :
    GrowsIn tb (Ochr.endLoansOfTopTemp 0) := by
  unfold Ochr.endLoansOfTopTemp; grows_go

theorem zero_popFrame :
    GrowsIn tb (Ochr.popFrame 0) := by
  unfold Ochr.popFrame; grows_go

theorem zero_placeTypeQ :
    ∀ (p : Place), GrowsIn tb (Ochr.placeType? 0 p) := by
  intro p
  unfold Ochr.placeType?; grows_go

theorem zero_placeType :
    ∀ (p : Place), GrowsIn tb (Ochr.placeType 0 p) := by
  intro p
  unfold Ochr.placeType; grows_go

theorem zero_natPlace :
    ∀ (q : Place), GrowsIn tb (Ochr.natPlace 0 q) := by
  intro q
  unfold Ochr.natPlace; grows_go

theorem zero_projIn :
    ∀ (p : Place), GrowsIn tb (Ochr.projIn 0 p) := by
  intro p
  unfold Ochr.projIn; grows_go

theorem zero_projMatch :
    ∀ (q : Place) (i : Nat) (k : Place → Term), GrowsIn tb (Ochr.projMatch 0 q i k) := by
  intro q i k
  unfold Ochr.projMatch; grows_go

theorem zero_depFieldType :
    ∀ (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place), GrowsIn tb (Ochr.depFieldType 0 d ps g q) := by
  intro d ps g q
  unfold Ochr.depFieldType; grows_go

theorem zero_packedErr :
    ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.packedErr 0 v T) := by
  intro v T
  unfold Ochr.packedErr; grows_go

theorem zero_convVal :
    ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.convVal 0 v T) := by
  intro v T
  unfold Ochr.convVal; grows_go

theorem zero_valTypeQ :
    ∀ (v : Value), GrowsIn tb (Ochr.valType? 0 v) := by
  intro v
  unfold Ochr.valType?; grows_go

theorem zero_valType :
    ∀ (v : Value), GrowsIn tb (Ochr.valType 0 v) := by
  intro v
  unfold Ochr.valType; grows_go

theorem zero_sealedTypeQ :
    ∀ (t : Term), GrowsIn tb (Ochr.sealedType? 0 t) := by
  intro t
  unfold Ochr.sealedType?; grows_go

theorem zero_fieldTele :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value) (hval : ∀ i v, GrowsIn tb (val i v)) (upto : Option Nat), GrowsIn tb (Ochr.fieldTele 0 d ps c val upto) := by
  intro d ps c val hval upto
  unfold Ochr.fieldTele; grows_go

theorem zero_fieldTypes :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldTypes 0 d ps c) := by
  intro d ps c
  unfold Ochr.fieldTypes; grows_go

theorem zero_fieldTypesOf :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value) (upto : Option Nat), GrowsIn tb (Ochr.fieldTypesOf 0 d ps c fs upto) := by
  intro d ps c fs upto
  unfold Ochr.fieldTypesOf; grows_go

theorem zero_fieldsGeneric :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldsGeneric 0 d ps c) := by
  intro d ps c
  unfold Ochr.fieldsGeneric; grows_go

theorem zero_fieldTypeAt :
    ∀ (d : IndDecl) (sol : Array (Option Value)) (c : Nat) (i : Nat) (earlier : List Value), GrowsIn tb (Ochr.fieldTypeAt 0 d sol c i earlier) := by
  intro d sol c i earlier
  unfold Ochr.fieldTypeAt; grows_go

theorem zero_indValTypeQ :
    ∀ (t : String) (c : Nat) (fs : List Value), GrowsIn tb (Ochr.indValType? 0 t c fs) := by
  intro t c fs
  unfold Ochr.indValType?; grows_go

theorem zero_bindDataFields :
    ∀ (p : Place) (d : IndDecl) (ps : List Value) (c : Nat) (arm : Term), GrowsIn tb (Ochr.bindDataFields 0 p d ps c arm) := by
  intro p d ps c arm
  unfold Ochr.bindDataFields; grows_go

theorem zero_piSort :
    ∀ (T : Value), GrowsIn tb (Ochr.piSort 0 T) := by
  intro T
  unfold Ochr.piSort; grows_go

theorem zero_evalType :
    ∀ (t : Term), GrowsIn tb (Ochr.evalType 0 t) := by
  intro t
  have e : Ochr.evalType 0 t = inStatement (exhausted "out of fuel") := rfl
  rw [e]; grows_go

theorem zero_capture :
    ∀ (t : Term), GrowsIn tb (Ochr.capture 0 t) := by
  intro t
  unfold Ochr.capture; grows_go

theorem zero_conv :
    ∀ (v : Value) (w : Value), GrowsIn tb (Ochr.conv 0 v w) := by
  intro v w
  unfold Ochr.conv; grows_go

theorem zero_convList :
    ∀ (as : List Value) (bs : List Value), GrowsIn tb (Ochr.convList 0 as bs) := by
  intro as bs
  unfold Ochr.convList; grows_go

theorem zero_convTList :
    ∀ (as : List Term) (bs : List Term), GrowsIn tb (Ochr.convTList 0 as bs) := by
  intro as bs
  unfold Ochr.convTList; grows_go

theorem zero_convPi :
    ∀ (P : Value) (Q : Value), GrowsIn tb (Ochr.convPi 0 P Q) := by
  intro P Q
  unfold Ochr.convPi; grows_go

theorem zero_convT :
    ∀ (t : Term) (u : Term), GrowsIn tb (Ochr.convT 0 t u) := by
  intro t u
  unfold Ochr.convT; grows_go

theorem zero_convFn :
    ∀ (f : Value) (g : Value), GrowsIn tb (Ochr.convFn 0 f g) := by
  intro f g
  unfold Ochr.convFn; grows_go

theorem zero_convFnRun :
    ∀ (f : Value) (g : Value) (pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term), GrowsIn tb (Ochr.convFnRun 0 f g pf cs hs ds c) := by
  intro f g pf cs hs ds c
  unfold Ochr.convFnRun; grows_go

theorem zero_mkEqM :
    ∀ (A : Value) (a : Value) (b : Value), GrowsIn tb (Ochr.mkEqM 0 A a b) := by
  intro A a b
  unfold Ochr.mkEqM; grows_go

theorem zero_rewriteGoal :
    ∀ (rev : Bool) (h : Term) (G : Value), GrowsIn tb (Ochr.rewriteGoal 0 rev h G) := by
  intro rev h G
  unfold Ochr.rewriteGoal; grows_go

theorem zero_expectTy :
    ∀ (what : String) (T : Option Value) (A : Value), GrowsIn tb (Ochr.expectTy 0 what T A) := by
  intro what T A
  unfold Ochr.expectTy; grows_go

theorem zero_eval :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.eval 0 typed t hint) := by
  intro typed t hint
  unfold Ochr.eval; grows_go

theorem zero_evalAt :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalAt 0 typed t hint) := by
  intro typed t hint
  unfold Ochr.evalAt; grows_go

theorem zero_evalCore :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalCore 0 typed t hint) := by
  intro typed t hint
  unfold Ochr.evalCore; grows_go

theorem zero_lentProofAssign :
    ∀ (p : Place) (u : Term), GrowsIn tb (Ochr.lentProofAssign 0 p u) := by
  intro p u
  unfold Ochr.lentProofAssign; grows_go

theorem zero_evalTInd :
    ∀ (typed : Bool) (n : String) (as : List Term), GrowsIn tb (Ochr.evalTInd 0 typed n as) := by
  intro typed n as
  unfold Ochr.evalTInd; grows_go

theorem zero_evalParams :
    ∀ (n : String) (as : List Term) (typed : Bool), GrowsIn tb (Ochr.evalParams 0 n as typed) := by
  intro n as typed
  unfold Ochr.evalParams; grows_go

theorem zero_checkParams :
    ∀ (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.checkParams 0 d n vs tys) := by
  intro d n vs tys
  unfold Ochr.checkParams; grows_go

theorem zero_evalCtor :
    ∀ (typed : Bool) (ty : String) (c : Nat) (h : Hint) (pts : List Term) (as : List Term) (hint : Option Value), GrowsIn tb (Ochr.evalCtor 0 typed ty c h pts as hint) := by
  intro typed ty c h pts as hint
  unfold Ochr.evalCtor; grows_go

theorem zero_stmtCallee :
    ∀ (fv : Value) (fT : Option Value) (cls? : Option Nat), GrowsIn tb (Ochr.stmtCallee 0 fv fT cls?) := by
  intro fv fT cls?
  unfold Ochr.stmtCallee; grows_go

theorem zero_evalCall :
    ∀ (typed : Bool) (f : Term) (as : List Term) (head : Bool) (cls? : Option Nat) (res? : Option DeclInfo), GrowsIn tb (Ochr.evalCall 0 typed f as head cls? res?) := by
  intro typed f as head cls? res?
  unfold Ochr.evalCall; grows_go

theorem zero_argHint :
    ∀ (fv : Value) (fT : Option Value) (ws : Array Value), GrowsIn tb (Ochr.argHint 0 fv fT ws) := by
  intro fv fT ws
  unfold Ochr.argHint; grows_go

theorem zero_funTypeQ :
    ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType? 0 fv fT) := by
  intro fv fT
  unfold Ochr.funType?; grows_go

theorem zero_funType :
    ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType 0 fv fT) := by
  intro fv fT
  unfold Ochr.funType; grows_go

theorem zero_callType :
    ∀ (piTy : Value) (ws : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.callType 0 piTy ws tys) := by
  intro piTy ws tys
  unfold Ochr.callType; grows_go

theorem zero_declCallType :
    ∀ (piTy : Value) (ws : Array Value), GrowsIn tb (Ochr.declCallType 0 piTy ws) := by
  intro piTy ws
  unfold Ochr.declCallType; grows_go

theorem zero_paramTypes :
    ∀ (piTy : Value) (ws : List Value) (need : List Nat), GrowsIn tb (Ochr.paramTypes 0 piTy ws need) := by
  intro piTy ws need
  unfold Ochr.paramTypes; grows_go

theorem zero_bindTyQ :
    ∀ (pos : Pos), GrowsIn tb (Ochr.bindTy? 0 pos) := by
  intro pos
  unfold Ochr.bindTy?; grows_go

theorem zero_endBorrowArgs :
    ∀ (ws : Array Value), GrowsIn tb (Ochr.endBorrowArgs 0 ws) := by
  intro ws
  unfold Ochr.endBorrowArgs; grows_go

theorem zero_runBody :
    ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value), GrowsIn tb (Ochr.runBody 0 fv cs t rd ws) := by
  intro fv cs t rd ws
  unfold Ochr.runBody; grows_go

theorem zero_runBodyCore :
    ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (body : Term), GrowsIn tb (Ochr.runBodyCore 0 fv cs t rd ws self hs ds c body) := by
  intro fv cs t rd ws self hs ds c body
  unfold Ochr.runBodyCore; grows_go

theorem zero_callFn :
    ∀ (typed : Bool) (fv : Value) (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (head : Bool) (cls? : Option Nat) (recUid? : Option Nat) (res : DeclInfo) (fills : Array Bool) (want : Bool) (defer : Bool), GrowsIn tb (Ochr.callFn 0 typed fv fT ws tys head cls? recUid? res fills want defer) := by
  intro typed fv fT ws tys head cls? recUid? res fills want defer
  unfold Ochr.callFn; grows_go

theorem zero_closeCall :
    ∀ (fv : Value) (ws : Array Value) (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)), GrowsIn tb (Ochr.closeCall 0 fv ws kind res fills tys) := by
  intro fv ws kind res fills tys
  unfold Ochr.closeCall; grows_go

theorem zero_refine :
    ∀ (σ : Nat) (r : Value), GrowsIn tb (Ochr.refine 0 σ r) := by
  intro σ r
  unfold Ochr.refine; grows_go

theorem zero_evalMatch :
    ∀ (typed : Bool) (p : Place) (z : Term) (s : Term) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatch 0 typed p z s expected tail) := by
  intro typed p z s expected tail
  unfold Ochr.evalMatch; grows_go

theorem zero_natScrutinee :
    ∀ (p : Place), GrowsIn tb (Ochr.natScrutinee 0 p) := by
  intro p
  unfold Ochr.natScrutinee; grows_go

theorem zero_generalizeNeutral :
    ∀ (p : Place) (n : Value), GrowsIn tb (Ochr.generalizeNeutral 0 p n) := by
  intro p n
  unfold Ochr.generalizeNeutral; grows_go

theorem zero_sealedResultTypeQ :
    ∀ (t : Term), GrowsIn tb (Ochr.sealedResultType? 0 t) := by
  intro t
  unfold Ochr.sealedResultType?; grows_go

theorem zero_renormAll :
    GrowsIn tb (Ochr.renormAll 0) := by
  unfold Ochr.renormAll; grows_go

theorem zero_renormV :
    ∀ (v : Value), GrowsIn tb (Ochr.renormV 0 v) := by
  intro v
  unfold Ochr.renormV; grows_go

theorem zero_renormT :
    ∀ (t : Term), GrowsIn tb (Ochr.renormT 0 t) := by
  intro t
  unfold Ochr.renormT; grows_go

theorem zero_splitThenClose :
    ∀ (p : Place) (z : Term) (s : Term) (σ : Nat) (expected : Option Value), GrowsIn tb (Ochr.splitThenClose 0 p z s σ expected) := by
  intro p z s σ expected
  unfold Ochr.splitThenClose; grows_go

theorem zero_splitArmsThenClose :
    ∀ (mt : Term) (σ : Nat) (arms : List (M Value × Term)) (harms : ∀ a ∈ arms, GrowsIn tb a.1) (expected : Option Value), GrowsIn tb (Ochr.splitArmsThenClose 0 mt σ arms expected) := by
  intro mt σ arms harms expected
  unfold Ochr.splitArmsThenClose; grows_go

theorem zero_ctorRefinement :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.ctorRefinement 0 d ps c) := by
  intro d ps c
  unfold Ochr.ctorRefinement; grows_go

theorem zero_scrutType :
    ∀ (p : Place) (ty : String), GrowsIn tb (Ochr.scrutType 0 p ty) := by
  intro p ty
  unfold Ochr.scrutType; grows_go

theorem zero_evalMatchByType :
    ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchByType 0 typed p ty arms expected tail) := by
  intro typed p ty arms expected tail
  unfold Ochr.evalMatchByType; grows_go

theorem zero_evalMatchInd :
    ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchInd 0 typed p ty arms expected tail) := by
  intro typed p ty arms expected tail
  unfold Ochr.evalMatchInd; grows_go

theorem zero_etaInPlace :
    ∀ (σ : Nat) (d : IndDecl) (ps : List Value), GrowsIn tb (Ochr.etaInPlace 0 σ d ps) := by
  intro σ d ps
  unfold Ochr.etaInPlace; grows_go

theorem zero_etaPlace :
    ∀ (q : Place), GrowsIn tb (Ochr.etaPlace 0 q) := by
  intro q
  unfold Ochr.etaPlace; grows_go

theorem zero_movedPlace :
    ∀ (q : Place), GrowsIn tb (Ochr.movedPlace 0 q) := by
  intro q
  unfold Ochr.movedPlace; grows_go

theorem zero_staticJoin :
    ∀ (mt : Term), GrowsIn tb (Ochr.staticJoin 0 mt) := by
  intro mt
  unfold Ochr.staticJoin; grows_go

theorem zero_joinDrop :
    ∀ (mt : Term) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinDrop 0 mt run) := by
  intro mt run hrun
  unfold Ochr.joinDrop; grows_go

theorem zero_joinCont :
    ∀ (mt : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.joinCont 0 mt k) := by
  intro mt k hk
  unfold Ochr.joinCont; grows_go

theorem zero_joinEnds :
    ∀ (mt : Term) (tail : Bool) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinEnds 0 mt tail run) := by
  intro mt tail run hrun
  unfold Ochr.joinEnds; grows_go

theorem zero_blockEntry :
    ∀ (mt : Term), GrowsIn tb (Ochr.blockEntry 0 mt) := by
  intro mt
  unfold Ochr.blockEntry; grows_go

theorem zero_entryAccess :
    ∀ (capsS : Array (Place × Nat)), GrowsIn tb (Ochr.entryAccess 0 capsS) := by
  intro capsS
  unfold Ochr.entryAccess; grows_go

theorem zero_dropAtJoin :
    ∀ (q : Place), GrowsIn tb (Ochr.dropAtJoin 0 q) := by
  intro q
  unfold Ochr.dropAtJoin; grows_go

theorem zero_blockCaptures :
    ∀ (mt : Term) (armMovedAll : List Place), GrowsIn tb (Ochr.blockCaptures 0 mt armMovedAll) := by
  intro mt armMovedAll
  unfold Ochr.blockCaptures; grows_go

theorem zero_closeBlock :
    ∀ (mt : Term) (arms : List BlockArm) (harms : ∀ a ∈ arms, GrowsIn tb a.setup ∧ ∀ r, GrowsIn tb (a.body r)) (B? : Option Value), GrowsIn tb (Ochr.closeBlock 0 mt arms B?) := by
  intro mt arms harms B?
  unfold Ochr.closeBlock; grows_go

theorem zero_observe :
    ∀ (typed : Bool) (t : Term) (A : Value) (W : List Pos) (refs : List (Place × Value)), GrowsIn tb (Ochr.observe 0 typed t A W refs) := by
  intro typed t A W refs
  have e : Ochr.observe 0 typed t A W refs = inStatement (exhausted "out of fuel") := rfl
  rw [e]; grows_go

theorem zero_idType :
    ∀ (typed : Bool) (A : Term) (t : Term) (u : Term), GrowsIn tb (Ochr.idType 0 typed A t u) := by
  intro typed A t u
  unfold Ochr.idType; grows_go

theorem zero_stuckScrutinee :
    ∀ (t : Term), GrowsIn tb (Ochr.stuckScrutinee 0 t) := by
  intro t
  unfold Ochr.stuckScrutinee; grows_go

theorem zero_findSplit :
    ∀ (f : String) (G : Value), GrowsIn tb (Ochr.findSplit 0 f G) := by
  intro f G
  unfold Ochr.findSplit; grows_go

theorem zero_generalizeFound :
    ∀ (n : Value) (T : Value), GrowsIn tb (Ochr.generalizeFound 0 n T) := by
  intro n T
  unfold Ochr.generalizeFound; grows_go

theorem zero_splitTarget :
    ∀ (f : String), GrowsIn tb (Ochr.splitTarget 0 f) := by
  intro f
  unfold Ochr.splitTarget; grows_go

theorem zero_checkTail :
    ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTail 0 t k) := by
  intro t k hk
  unfold Ochr.checkTail; grows_go

theorem zero_checkTailAt :
    ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTailAt 0 t k) := by
  intro t k hk
  unfold Ochr.checkTailAt; grows_go

theorem zero_checkFix :
    ∀ (fv : Value) (cs : List Value) (t : Term) (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)), GrowsIn tb (Ochr.checkFix 0 fv cs t capRec rd) := by
  intro fv cs t capRec rd
  unfold Ochr.checkFix; grows_go

end Ochr.Meaning.Steps.Machine
