import Ochr.Meaning.Steps.Machine.DecideLeaves

/-!
# `GrowsIn` for the machine's functions outside its mutual block (`Machine.lean`, before it)

Reads of places, the lending of labels, the [Rec] bookkeeping, the log of moves. The ones that
recur on a value (`loanPath`, `hasDependent`) go by their functional induction; the ones that
recur on the fuel, by induction on it.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

variable {G : Tab}

@[grows] theorem growsIn_fuelLeft : GrowsIn G fuelLeft := by unfold fuelLeft; grows_go
@[grows] theorem growsIn_ppPlace p : GrowsIn G (ppPlace p) := by unfold ppPlace; grows_go
@[grows] theorem growsIn_content? p : GrowsIn G (content? p) := by unfold content?; grows_go
@[grows] theorem growsIn_underProof : (p : Place) → GrowsIn G (underProof p)
  | .var _ => by unfold underProof; grows_go
  | .deref q => by have ih : GrowsIn G (underProof q) := growsIn_underProof q; unfold underProof; grows_go
  | .proj _ q => by have ih : GrowsIn G (underProof q) := growsIn_underProof q; unfold underProof; grows_go
  | .field _ q => by have ih : GrowsIn G (underProof q) := growsIn_underProof q; unfold underProof; grows_go
@[grows] theorem growsIn_content p : GrowsIn G (content p) := by unfold content; grows_go
@[grows] theorem growsIn_setPlace p v : GrowsIn G (setPlace p v) := by unfold setPlace; grows_go
@[grows] theorem growsIn_expandRefsF refs fuel v : GrowsIn G (expandRefsF refs fuel v) := by
  induction fuel generalizing v with
  | zero => unfold expandRefsF; grows_go
  | succ n ih => unfold expandRefsF; grows_go
@[grows] theorem growsIn_expandRefs refs v : GrowsIn G (expandRefs refs v) := by unfold expandRefs; grows_go
@[grows] theorem growsIn_atRuntime : GrowsIn G atRuntime := by unfold atRuntime; grows_go
@[grows] theorem growsIn_abstractMatchCheck p ty : GrowsIn G (abstractMatchCheck p ty) := by
  unfold abstractMatchCheck; grows_go
@[grows] theorem growsIn_isUnsizedType T : GrowsIn G (isUnsizedType T) := by unfold isUnsizedType; grows_go
@[grows] theorem growsIn_unsizedCheck p v w : GrowsIn G (unsizedCheck p v w) := by unfold unsizedCheck; grows_go
@[grows] theorem growsIn_unsizedTermF fuel T seen : GrowsIn G (unsizedTerm.unsizedTermF fuel T seen) := by
  induction fuel generalizing T seen with
  | zero => unfold unsizedTerm.unsizedTermF; grows_go
  | succ n ih => unfold unsizedTerm.unsizedTermF; grows_go
@[grows] theorem growsIn_unsizedTerm T seen : GrowsIn G (unsizedTerm T seen) := by unfold unsizedTerm; grows_go
@[grows] theorem growsIn_modelSignature hs ds c : GrowsIn G (modelSignature hs ds c) := by
  unfold modelSignature; grows_go
@[grows] theorem growsIn_isCapture p : GrowsIn G (isCapture p) := by unfold isCapture; grows_go
@[grows] theorem growsIn_matchContent p : GrowsIn G (matchContent p) := by unfold matchContent; grows_go

theorem growsIn_loanPath_both (l : Nat) :
    (∀ v, GrowsIn G (loanPath v l)) ∧ (∀ t c names i ws, GrowsIn G (loanPathFields t c names l i ws)) := by
  refine Ochr.loanPath.mutual_induct (motive_1 := fun v => GrowsIn G (loanPath v l))
      (motive_2 := fun t c names i ws => GrowsIn G (loanPathFields t c names l i ws)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> first | (unfold loanPath; grows_go) | (unfold loanPathFields; grows_go)
@[grows] theorem growsIn_loanPath v l : GrowsIn G (loanPath v l) := (growsIn_loanPath_both l).1 v
@[grows] theorem growsIn_loanPathFields t c names l i ws : GrowsIn G (loanPathFields t c names l i ws) :=
  (growsIn_loanPath_both l).2 t c names i ws

/-- `lendV` and `lendT` at one fuel. -/
structure LendGrows (G : Tab) (n : Nat) : Prop where
  lendV : ∀ op v, GrowsIn G (lendV n op v)
  lendT : ∀ op t, GrowsIn G (lendT n op t)

theorem lendGrows : ∀ n, LendGrows G n
  | 0 => ⟨fun _ _ => by unfold Ochr.lendV; grows_go, fun _ _ => by unfold Ochr.lendT; grows_go⟩
  | n + 1 => by
    have ih : LendGrows G n := lendGrows n
    exact ⟨fun _ _ => by unfold Ochr.lendV; grows_go ih, fun _ _ => by unfold Ochr.lendT; grows_go ih⟩

@[grows] theorem growsIn_lendV fuel op v : GrowsIn G (lendV fuel op v) := (lendGrows fuel).lendV op v
@[grows] theorem growsIn_lendT fuel op t : GrowsIn G (lendT fuel op t) := (lendGrows fuel).lendT op t
@[grows] theorem growsIn_lendEnv fuel op : GrowsIn G (lendEnv fuel op) := by
  cases fuel <;> (unfold lendEnv; grows_go)
@[grows] theorem growsIn_throughLocalBorrow f i p : GrowsIn G (throughLocalBorrow f i p) := by
  unfold throughLocalBorrow; grows_go
@[grows] theorem growsIn_logEffect p k : GrowsIn G (logEffect p k) := by unfold logEffect; grows_go
@[grows] theorem growsIn_ctorFieldsF fuel v g : GrowsIn G (ctorFields.ctorFieldsF fuel v g) := by
  induction fuel generalizing v with
  | zero => unfold ctorFields.ctorFieldsF; grows_go
  | succ n ih => unfold ctorFields.ctorFieldsF; grows_go
@[grows] theorem growsIn_ctorFields v g : GrowsIn G (ctorFields v g) := by unfold ctorFields; grows_go
@[grows] theorem growsIn_strongUpdate p : GrowsIn G (strongUpdate p) := by unfold strongUpdate; grows_go
theorem growsIn_hasDependent_both :
    ∀ v, GrowsIn G (hasDependent v) := by
  refine Ochr.hasDependent.induct (motive_1 := fun ws => GrowsIn G (hasDependent.anyList ws))
      (motive_2 := fun v => GrowsIn G (hasDependent v)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> first | (unfold hasDependent; grows_go; done) | (unfold hasDependent.anyList; grows_go; done)
@[grows] theorem growsIn_hasDependent v : GrowsIn G (hasDependent v) := growsIn_hasDependent_both v
@[grows] theorem growsIn_borrowParamCheck ds c : GrowsIn G (borrowParamCheck ds c) := by
  unfold borrowParamCheck; grows_go
@[grows] theorem growsIn_noBorrowParam n v : GrowsIn G (noBorrowParam n v) := by unfold noBorrowParam; grows_go
@[grows] theorem growsIn_stmtArgIf fuel b a {x : M (Value × Option Value)} (hx : GrowsIn G x) :
    GrowsIn G (stmtArgIf fuel b a x) := by unfold stmtArgIf; grows_go
@[grows] theorem growsIn_fixOf fv : GrowsIn G (fixOf fv) := by unfold fixOf; grows_go
@[grows] theorem growsIn_wholeReturned v : GrowsIn G (wholeReturned v) := by unfold wholeReturned; grows_go
@[grows] theorem growsIn_wholeBorrowArgs ws w : GrowsIn G (wholeBorrowArgs ws w) := by
  unfold wholeBorrowArgs; grows_go
@[grows] theorem growsIn_capMarks t : GrowsIn G (capMarks t) := by unfold capMarks; grows_go
@[grows] theorem growsIn_markCapRec m : GrowsIn G (markCapRec m) := by unfold markCapRec; grows_go
@[grows] theorem growsIn_markLastRec u : GrowsIn G (markLastRec u) := by unfold markLastRec; grows_go
/-- D148's own-name slot (main's merge, lead49). -/
@[grows] theorem growsIn_pushSelf self rec? : GrowsIn G (pushSelf self rec?) := by unfold pushSelf; grows_go
@[grows] theorem growsIn_callRecUid f : GrowsIn G (callRecUid f) := by unfold callRecUid; grows_go
@[grows] theorem growsIn_neutralLookup v : GrowsIn G (neutralLookup v) := by unfold neutralLookup; grows_go
@[grows] theorem growsIn_recordedNeutral v : GrowsIn G (recordedNeutral v) := by unfold recordedNeutral; grows_go
@[grows] theorem growsIn_canonNeutral v : GrowsIn G (canonNeutral v) := by unfold canonNeutral; grows_go
@[grows] theorem growsIn_armMoves log f0 n0 : GrowsIn G (armMoves log f0 n0) := by unfold armMoves; grows_go
@[grows] theorem growsIn_ctorNeedsCtx fuel d c : GrowsIn G (ctorNeedsCtx fuel d c) := by
  unfold ctorNeedsCtx; grows_go
@[grows] theorem growsIn_needsCtx fuel t : GrowsIn G (needsCtx fuel t) := by
  induction fuel generalizing t with
  | zero => unfold needsCtx; grows_go
  | succ n ih => unfold needsCtx; grows_go
@[grows] theorem growsIn_readsHint fuel tl tr t : GrowsIn G (readsHint fuel tl tr t) := by
  induction fuel generalizing tl tr t with
  | zero => unfold readsHint; grows_go
  | succ n ih => unfold readsHint; grows_go
@[grows] theorem growsIn_resolveLoans fuel v : GrowsIn G (resolveLoans fuel v) := by
  induction fuel generalizing v with
  | zero => unfold resolveLoans; grows_go
  | succ n ih => unfold resolveLoans; grows_go

/-! ## [Rec]'s check: a read of the state, a loop that keeps it, a write of the state read -/

theorem keep_getThe_fuel : Keep (getThe Fuel : M Fuel) := by
  intro s f l a s' f' l' h; cases h; rfl

theorem keep_filterAuxM {α : Type} {p : α → M Bool} (hp : ∀ a, Keep (p a)) :
    ∀ (xs acc : List α), Keep (List.filterAuxM p xs acc)
  | [], acc => keep_pure acc
  | x :: xs, acc => by
    unfold List.filterAuxM
    exact keep_bind (hp x) fun b => keep_filterAuxM hp xs _

theorem keep_filterM {α : Type} {p : α → M Bool} (hp : ∀ a, Keep (p a)) (xs : List α) :
    Keep (List.filterM p xs) := by
  unfold List.filterM
  exact keep_bind (keep_filterAuxM hp xs []) fun _ => keep_pure _

theorem keep_expandRefsF refs : ∀ fuel v, Keep (expandRefsF refs fuel v)
  | 0, v => by unfold expandRefsF; exact keep_exhausted _
  | n + 1, v => by
    unfold expandRefsF
    split <;> fuel_cleanup <;>
      first
      | (split <;> first | exact keep_expandRefsF refs n _ | exact keep_pure _)
      | exact keep_bind (keep_expandRefsF refs n _) fun _ => keep_pure _
      | exact keep_bind (keep_mapM _ fun _ => keep_expandRefsF refs n _) fun _ => keep_pure _
      | exact keep_pure _

theorem keep_expandRefs refs v : Keep (expandRefs refs v) := by
  unfold expandRefs fuelLeft
  exact keep_bind (keep_bind keep_getThe_fuel fun _ => keep_pure _) fun _ => keep_expandRefsF refs _ _

theorem growsAt_set {s s₀ : MState} (h₀ : TablesGrow s s₀) : GrowsAt s (set s₀ : M Unit) := by
  intro f l a s' f' l' e
  cases e; exact h₀

@[grows] theorem growsIn_recCheck fv ws uid? : GrowsIn G (recCheck fv ws uid?) := by
  unfold recCheck
  refine growsIn_get_bind_at fun st hs => growsAt_keep_bind ?_ fun _ => growsAt_set (tablesGrow_of_eq rfl rfl rfl rfl rfl)
  keep_go
  all_goals first
    | exact keep_filterM (fun _ => by keep_go; all_goals exact keep_expandRefs _ _) _
    | skip

/-! ## The editor's located evaluation (a read of the state, notes in the log, a write of it) -/

theorem keep_modifyThe_log (g : Array LogEntry → Array LogEntry) : Keep (modifyThe (Array LogEntry) g : M Unit) := by
  intro s f l a s' f' l' h; cases h; rfl

theorem keep_noteStateAt (l : Option Loc) (exit : Bool) (v : Option (Value × Option Value)) :
    Keep (noteStateAt l exit v) := by
  unfold noteStateAt
  keep_go
  all_goals exact keep_modifyThe_log _

@[grows] theorem growsIn_locatedCore {α : Type} (t : Term) {x : M α} (flight : α → Option (Value × Option Value))
    (hx : GrowsIn G x) : GrowsIn G (locatedCore t x flight) := by
  unfold locatedCore
  refine growsIn_get_bind_at fun s hs => ?_
  split
  · exact growsAt_of_growsIn hs hx
  · dsimp only
    refine growsAt_keep_bind (keep_noteStateAt _ _ _) fun _ => ?_
    refine growsAt_set_bind (tablesGrow_of_eq rfl rfl rfl rfl rfl) hs fun _ => ?_
    grows_go
    all_goals first
      | exact growsIn_of_keep (keep_noteStateAt _ _ _)
      | skip

@[grows] theorem growsIn_located {α : Type} (t : Term) {x : M α} (flight : α → Option (Value × Option Value))
    (ownTyping : Option Bool) (hx : GrowsIn G x) : GrowsIn G (located t x flight ownTyping) := by
  unfold located; grows_go

@[grows] theorem growsIn_locatedTail (t : Term) {x : M Unit} (hx : GrowsIn G x) : GrowsIn G (locatedTail t x) := by
  unfold locatedTail; grows_go

set_option maxHeartbeats 4000000 in
/-- Main's D131: the reading's agreement with the stored type and the value, a test (it reads, never writes). -/
theorem keep_readingAgrees (fuel : Nat) (h : Hint) (T : Value) (d : DeclInfo) (v : Value) :
    Keep (readingAgrees fuel h T d v) := by
  unfold readingAgrees; keep_go
  all_goals first | exact (decideKeep _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ | skip

@[grows] theorem growsIn_readingAgrees (fuel : Nat) (h : Hint) (T : Value) (d : DeclInfo) (v : Value) :
    GrowsIn G (readingAgrees fuel h T d v) := growsIn_of_keep (keep_readingAgrees fuel h T d v)

/-- Main's D134: a call's head type taken apart, or an error. -/
@[grows] theorem growsIn_callPi (piTy : Value) (n : Nat) : GrowsIn G (callPi piTy n) := by
  unfold callPi; grows_go

end Ochr.Meaning.Steps.Machine
