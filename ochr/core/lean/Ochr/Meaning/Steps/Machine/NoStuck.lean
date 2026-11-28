import Ochr.Meaning.Steps.Machine.CallJEval

/-!
# Runs that never end stuck (machine8; for `CallJInv`)

`callFn` runs a known callee's body under `catchStuck`: a STUCK body run closes the call off
([App-close]) and the call returns a sealed program. So a fact about the value of a call needs the
body's run never to end stuck, a statement about the checker's failing runs, which no fact before
needed. `NSAt x s`: `x` run from `s` succeeds, fails with an error, or runs out of fuel, but never ends
`Fail.stuck`. Stuck is thrown at ten sites only (`stuckNow`, `stuckOn`, the head-call handler), all in
`Machine.lean`'s match and call code; the decision procedures (`Decide.lean`) throw none
(`decideNS`, by the `decideKeep` induction).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- `x` run from `s` never ends stuck. -/
def NSAt {α : Type} (x : M α) (s : MState) : Prop :=
  ∀ f l on f' l', runAll x s f l ≠ ((.ok (.error (.stuck on)), f'), l')

/-- `x` never ends stuck, from any state. -/
def NS {α : Type} (x : M α) : Prop := ∀ s, NSAt x s

theorem nsAt_bind {α β : Type} {x : M α} {k : α → M β} {s : MState} (hx : NSAt x s)
    (hk : ∀ b a s', Runs x s b a s' → NSAt (k a) s') : NSAt (x >>= k) s := by
  intro f l on f' l' h
  rw [runAll_bind] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h; exact hx f l on _ _ e
  · intro h
    obtain ⟨fb⟩ := f
    exact hk fb a s₁ (runs_of_runAll e) f₁ l₁ on f' l' h

theorem ns_bind {α β : Type} {x : M α} {k : α → M β} (hx : NS x) (hk : ∀ a, NS (k a)) : NS (x >>= k) :=
  fun s => nsAt_bind (hx s) fun _ a _ _ => hk a _

theorem ns_pure {α : Type} (a : α) : NS (pure a : M α) := by
  intro s f l on f' l' h
  simp only [runAll, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
  cases h

theorem ns_err {α : Type} (m : String) : NS (err m : M α) := by
  intro s f l on f' l' h; cases h

theorem ns_exhausted {α : Type} (m : String) : NS (exhausted m : M α) := by
  intro s f l on f' l' h; cases h

theorem nsAt_get_bind {α : Type} {k : MState → M α} {s : MState} (hk : NSAt (k s) s) : NSAt (get >>= k) s := hk

theorem ns_get_bind {α : Type} {k : MState → M α} (hk : ∀ s, NSAt (k s) s) : NS (get >>= k) := fun s => hk s

theorem nsAt_modify_bind {α : Type} {g : MState → MState} {k : PUnit → M α} {s : MState} (hk : NSAt (k ()) (g s)) :
    NSAt (modify g >>= k) s := hk

theorem ns_modify (g : MState → MState) : NS (modify g : M Unit) := by
  intro s f l on f' l' h; rw [runAll_modify] at h; cases h

theorem ns_ite {α : Type} {c : Prop} {_ : Decidable c} {x y : M α} (hx : NS x) (hy : NS y) :
    NS (if c then x else y) := by
  split <;> assumption

theorem nsAt_ite {α : Type} {c : Prop} {_ : Decidable c} {x y : M α} {s : MState} (hx : NSAt x s) (hy : NSAt y s) :
    NSAt (if c then x else y) s := by
  split <;> assumption

theorem ns_map {α β : Type} (g : α → β) {x : M α} (hx : NS x) : NS (g <$> x) := by
  rw [map_eq_pure_bind]; exact ns_bind hx fun _ => ns_pure _

theorem ns_discard {α : Type} {x : M α} (hx : NS x) : NS (discard x) := by
  unfold discard; exact ns_map _ hx

theorem ns_forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, NS (body a b)) : NS (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact ns_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact ns_bind (hb a b) (fun r => by cases r with
      | done b' => exact ns_pure b'
      | yield b' => exact ih b')

theorem ns_mapM {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a, NS (f a)) : NS (xs.mapM f) := by
  induction xs with
  | nil => exact ns_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact ns_bind (hf a) (fun b => ns_bind ih (fun bs => ns_pure _))

theorem ns_allM {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, NS (f a)) : NS (xs.allM f) := by
  induction xs with
  | nil => exact ns_pure true
  | cons a as ih =>
    unfold List.allM
    exact ns_bind (hf a) (fun b => by cases b <;> first | exact ih | exact ns_pure _)

/-- A cleanup then a rethrow of a non-stuck failure: no stuck end unless the cleanup is stuck. -/
theorem nsAt_onFail {α : Type} {x : M α} {c : M Unit} {s : MState} (hx : NSAt x s) (hc : NS c) :
    NSAt (onFail x c) s := by
  intro f l on f' l' h
  unfold onFail at h
  rw [runAll_tryCatch] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨b, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h
    dsimp only at h
    rw [runAll_bind] at h
    revert h
    rcases ec : runAll c s f₁ l₁ with ⟨⟨c₁ | c₁ | ⟨u, s₂⟩, f₂⟩, l₂⟩
    · intro h; cases h
    · intro h; cases h; exact hc s f₁ l₁ on _ _ ec
    · intro h
      dsimp only at h
      rw [runAll_throw] at h
      cases h
      exact hx f l on _ _ e
  · intro h; cases h

theorem ns_onFail {α : Type} {x : M α} {c : M Unit} (hx : NS x) (hc : NS c) : NS (onFail x c) :=
  fun s => nsAt_onFail (hx s) hc

theorem nsAt_withLive {α : Type} (b : Bool) {x : M α} {s : MState} (hx : NSAt x { s with liveScope := b }) :
    NSAt (withLive b x) s := by
  unfold withLive
  refine nsAt_get_bind (nsAt_modify_bind (nsAt_bind (nsAt_onFail hx (ns_modify _)) fun _ _ _ _ =>
    ns_bind (ns_modify _) (fun _ => ns_pure _) _))

theorem ns_withLive {α : Type} (b : Bool) {x : M α} (hx : NS x) : NS (withLive b x) :=
  fun _ => nsAt_withLive b (hx _)

theorem ns_modifyThe_log (g : Array LogEntry → Array LogEntry) : NS (modifyThe (Array LogEntry) g : M Unit) := by
  intro s f l on f' l' h; cases h

theorem NSAt.of_ns {α : Type} {x : M α} (h : NS x) (s : MState) : NSAt x s := h s


/-! ## The decision procedures never end stuck -/

set_option hygiene false in
macro "ns_step" : tactic => `(tactic| first
  | with_reducible exact ns_pure _
  | with_reducible exact ns_err _
  | with_reducible exact ns_exhausted _
  | (with_reducible refine ns_get_bind fun s => NSAt.of_ns ?_ s
     try dsimp only)
  | (with_reducible refine ns_bind ?_ (fun _ => ?_))
  | (with_reducible refine ns_withLive _ ?_)
  | (with_reducible refine ns_map _ ?_)
  | (with_reducible refine ns_discard ?_)
  | (with_reducible refine ns_forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine ns_mapM _ (fun _ => ?_))
  | (with_reducible refine ns_allM _ (fun _ => ?_))
  | split
  | (dsimp only))

macro "ns_go" : tactic => `(tactic| repeat (any_goals ns_step))

theorem ns_liveDecl (i : Nat) : NS (liveDecl i) := by unfold liveDecl; ns_go
theorem ns_lookupInd (n : String) : NS (lookupInd n) := by unfold lookupInd; ns_go
theorem ns_lookupGlobal (n : String) : NS (lookupGlobal n) := by unfold lookupGlobal; ns_go
theorem ns_absReading (σ : Nat) : NS (absReading σ) := by unfold absReading; ns_go
theorem ns_capReadings (cs : List Value) (rd : List (DeclInfo × Value)) : NS (capReadings cs rd) := by
  unfold capReadings; ns_go
theorem ns_fieldTermIsProp (d : IndDecl) (FT : Term) : NS (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp; ns_go
  all_goals exact ns_lookupInd _
theorem ns_fieldIsProof (g : FieldRef) : NS (fieldIsProof g) := by
  unfold fieldIsProof; ns_go
  all_goals first | exact ns_fieldTermIsProp _ _ | exact ns_lookupInd _
theorem ns_ctorIsProof (ty : String) : NS (ctorIsProof ty) := by
  unfold ctorIsProof; ns_go
  all_goals exact ns_lookupInd _
theorem ns_preFlags (t : Term) (d : DeclInfo) : NS (preFlags t d) := by unfold preFlags; ns_go
theorem ns_refineDecl (d : DeclInfo) : NS (refineDecl d) := by unfold refineDecl; ns_go
theorem ns_sealedSort (t : Term) : NS (sealedSort? t) := by
  unfold sealedSort?; ns_go
  all_goals first | exact ns_lookupGlobal _ | exact ns_lookupInd _ | exact ns_absReading _
/-- D143's test of a written codomain (main's merge, lead49). -/
theorem ns_codomainWritten (what : Unit → String) (c : Term) (ns : List String) (cd : DeclInfo) :
    NS (codomainWritten what c ns cd) := by
  unfold codomainWritten; ns_go

def DecideNS (fuel : Nat) : Prop :=
  (∀ sc p, NS (placeDecl fuel sc p)) ∧
  (∀ r n c i, NS (fieldAt fuel r n c i)) ∧
  (∀ d args c i, NS (fieldDecl fuel d args c i)) ∧
  (∀ r, NS (declCopy fuel r)) ∧
  (∀ F as sc ns, NS (callDecl fuel F as sc ns)) ∧
  (∀ T, NS (closedTypeDecl fuel T)) ∧
  (∀ T, NS (sortOf fuel T)) ∧
  (∀ sc ns T, NS (declSort fuel sc ns T)) ∧
  (∀ chk sc ns t, NS (declOf fuel chk sc ns t)) ∧
  (∀ chk sc ns T vis tsc, NS (typeDecl fuel chk sc ns T vis tsc)) ∧
  (∀ F vis sc ns tsc as dflt, NS dflt → NS (typeFnDecl fuel F vis sc ns tsc as dflt)) ∧
  (∀ chk sc ns T, NS (typePos fuel chk sc ns T)) ∧
  (∀ chk sc ns hs ds, NS (telescope fuel chk sc ns hs ds)) ∧
  (∀ v, NS (valueDecl fuel v)) ∧
  (∀ T, NS (valTypeDecl fuel T)) ∧
  (∀ T, NS (isPropV fuel T)) ∧
  (∀ T, NS (fnClass fuel T))

theorem decideNS_zero : DecideNS 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (unfold placeDecl; exact ns_exhausted _)
    | (unfold fieldAt; exact ns_exhausted _)
    | (unfold fieldDecl; exact ns_withLive _ (ns_exhausted _))
    | (unfold fieldDecl; exact ns_exhausted _)
    | (unfold declCopy; exact ns_exhausted _)
    | (unfold callDecl; exact ns_exhausted _)
    | (unfold closedTypeDecl; exact ns_exhausted _)
    | (unfold closedTypeDecl; exact ns_withLive _ (ns_exhausted _))
    | (unfold sortOf; exact ns_exhausted _)
    | (unfold declSort; exact ns_exhausted _)
    | (unfold declOf; exact ns_exhausted _)
    | (unfold typeDecl; exact ns_exhausted _)
    | (unfold typeFnDecl; exact ns_exhausted _)
    | (unfold typePos; exact ns_exhausted _)
    | (unfold telescope; exact ns_exhausted _)
    | (unfold valueDecl; exact ns_withLive _ (ns_exhausted _))
    | (unfold valTypeDecl; exact ns_withLive _ (ns_exhausted _))
    | (unfold isPropV; exact ns_exhausted _)
    | (unfold fnClass; exact ns_exhausted _)

set_option hygiene false in
macro "intro_nih" : tactic => `(tactic| obtain ⟨ihP, ihFA, ihFD, ihDC, ihCD, ihCT, ihSO, ihDS, ihDO, ihTD, ihTF,
  ihTP, ihTel, ihVD, ihVT, ihPV, ihFC⟩ := ih)

set_option hygiene false in
macro "ns_ih" : tactic => `(tactic| repeat (any_goals first
  | with_reducible exact ihP _ _ | with_reducible exact ihFA _ _ _ _ | with_reducible exact ihFD _ _ _ _
  | with_reducible exact ihDC _ | with_reducible exact ihCD _ _ _ _
  | with_reducible exact ihCT _ | with_reducible exact ihSO _ | with_reducible exact ihDS _ _ _
  | with_reducible exact ihDO _ _ _ _ | with_reducible exact ihTD _ _ _ _ _ _
  | with_reducible exact ihTP _ _ _ _ | with_reducible exact ihTel _ _ _ _ _ | with_reducible exact ihVD _
  | with_reducible exact ihVT _ | with_reducible exact ihPV _ | with_reducible exact ihFC _
  | with_reducible exact ns_fieldIsProof _ | with_reducible exact ns_fieldTermIsProp _ _
  | with_reducible exact ns_ctorIsProof _
  | with_reducible exact ns_preFlags _ _ | with_reducible exact ns_refineDecl _
  | with_reducible exact ns_sealedSort _
  | with_reducible exact ns_codomainWritten _ _ _ _
  | with_reducible exact ns_liveDecl _ | with_reducible exact ns_lookupInd _
  | with_reducible exact ns_lookupGlobal _ | with_reducible exact ns_absReading _
  | with_reducible exact ns_capReadings _ _
  | assumption
  | with_reducible apply ihTF
  | ns_step))

set_option maxHeartbeats 2000000 in
theorem decideNS_succ (n : Nat) (ih : DecideNS n) : DecideNS (n + 1) := by
  intro_nih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc p; unfold placeDecl; (try dsimp only); ns_ih
  · intro r n' c i; unfold fieldAt; (try dsimp only); ns_ih
  · intro d args c i; unfold fieldDecl; (try dsimp only); ns_ih
  · intro r; unfold declCopy; (try dsimp only); ns_ih
  · intro F as sc ns; unfold callDecl; (try dsimp only); ns_ih
  · intro T; unfold closedTypeDecl; (try dsimp only); ns_ih
  · intro T; unfold sortOf; (try dsimp only); ns_ih
  · intro sc ns T; unfold declSort; (try dsimp only); ns_ih
  · intro chk sc ns t
    cases t <;> (unfold declOf; (try dsimp only); ns_ih)
  · intro chk sc ns T vis tsc; unfold typeDecl; (try dsimp only); ns_ih
  · intro F vis sc ns tsc as dflt hd; unfold typeFnDecl; (try dsimp only); ns_ih
  · intro chk sc ns T; unfold typePos; (try dsimp only); ns_ih
  · intro chk sc ns hs ds; unfold telescope; (try dsimp only); ns_ih
  · intro v; unfold valueDecl; (try dsimp only); ns_ih
  · intro T; unfold valTypeDecl; (try dsimp only); ns_ih
  · intro T; unfold isPropV; (try dsimp only); ns_ih
  · intro T; unfold fnClass; (try dsimp only); ns_ih

/-- **The decision procedures never end stuck**: every function of `Decide.lean`'s mutual block the
decisions reach, at every fuel. -/
theorem decideNS : ∀ fuel, DecideNS fuel
  | 0 => decideNS_zero
  | n + 1 => decideNS_succ n (decideNS n)


/-! ## Leaves: reads and writes of the state, the log and the budget -/

theorem ns_set (s₀ : MState) : NS (set s₀ : M PUnit) := by
  intro s f l on f' l' h; cases h

theorem ns_get : NS (get : M MState) := by
  intro s f l on f' l' h; cases h

theorem ns_getThe_fuel : NS (getThe Fuel : M Fuel) := by
  intro s f l on f' l' h; cases h

theorem ns_modifyThe_fuel (g : Fuel → Fuel) : NS (modifyThe Fuel g : M Unit) := by
  intro s f l on f' l' h; cases h

theorem ns_throw_error {α : Type} (m : String) (at? : Option Loc) : NS (throw (Fail.error m at?) : M α) := by
  intro s f l on f' l' h; cases h

theorem ns_throwThe_error {α : Type} (m : String) (at? : Option Loc) : NS (throwThe Fail (Fail.error m at?) : M α) := by
  intro s f l on f' l' h; cases h

set_option hygiene false in
macro "ns_step2" : tactic => `(tactic| first
  | with_reducible exact ns_modify _
  | with_reducible exact ns_set _
  | with_reducible exact ns_get
  | with_reducible exact ns_getThe_fuel
  | with_reducible exact ns_modifyThe_fuel _
  | with_reducible exact ns_modifyThe_log _
  | with_reducible exact ns_throw_error _ _
  | with_reducible exact ns_throwThe_error _ _
  | ns_step)

macro "ns_go2" : tactic => `(tactic| repeat (any_goals ns_step2))

theorem ns_tick : NS tick := by unfold tick; ns_go2
theorem ns_topIdx : NS topIdx := by unfold topIdx; ns_go2
theorem ns_varPos (i : Nat) : NS (varPos i) := by unfold varPos; ns_go2; all_goals exact ns_topIdx
theorem ns_getAt (p : Pos) : NS (getAt p) := by unfold getAt; ns_go2
theorem ns_setAt (p : Pos) (v : Value) : NS (setAt p v) := by unfold setAt modifyFrame; ns_go2
theorem ns_ppPlace (p : Place) : NS (ppPlace p) := by unfold ppPlace; ns_go2; all_goals exact ns_topIdx
theorem ns_content (p : Place) : NS (content p) := by
  unfold content
  rcases p.steps with ⟨i, ss⟩
  refine ns_bind (ns_varPos _) fun pos => ns_bind (ns_getAt _) fun v => ?_
  split
  · exact ns_pure _
  · exact ns_bind (ns_ppPlace _) fun _ => ns_err _
theorem ns_setPlace (p : Place) (v : Value) : NS (setPlace p v) := by
  unfold setPlace
  rcases p.steps with ⟨i, ss⟩
  refine ns_bind (ns_varPos _) fun pos => ns_bind (ns_getAt _) fun w => ?_
  split
  · exact ns_setAt _ _
  · exact ns_bind (ns_ppPlace _) fun _ => ns_err _
theorem ns_fire (r : Rule) (m : Unit → String) : NS (fire r m) := by unfold fire; ns_go2
theorem ns_isCapture (p : Place) : NS (isCapture p) := by
  unfold isCapture; ns_go2; all_goals exact ns_varPos _
theorem ns_unsizedCheck (p : Place) (v : Value) (w : String) : NS (unsizedCheck p v w) := by
  unfold unsizedCheck atRuntime isUnsizedType absType; ns_go2
  all_goals first | exact ns_lookupInd _ | exact ns_ppPlace _
theorem ns_copyRead (k : Nat) (p : Place) : NS (copyRead k p) := by
  unfold copyRead; ns_go2
  all_goals first | exact (decideNS _).1 _ _ | exact (decideNS _).2.2.2.1 _
theorem ns_pushBind (h : Hint) (T : Option Value) (v : Value) (p : Bool) (d : DeclInfo) : NS (pushBind h T v p d) := by
  unfold pushBind modifyFrame; ns_go2; all_goals exact ns_topIdx
theorem ns_wanted : NS wanted := by unfold wanted; ns_go2
theorem ns_throughLocalBorrow_var (f i x : Nat) : NS (throughLocalBorrow f i (.var x)) := by
  unfold throughLocalBorrow
  simp only [Place.steps]
  exact ns_pure _
theorem ns_logEffect_var (x : Nat) (k : String) : NS (logEffect (.var x) k) := by
  unfold logEffect
  refine ns_bind (ns_varPos _) fun pos => ?_
  split
  · split
    · exact ns_bind (ns_modify _) fun _ => ns_bind (ns_throughLocalBorrow_var _ _ _) fun o => by
        split
        · exact ns_modify _
        · exact ns_pure _
    · exact ns_pure _
  · exact ns_pure _


/-! ## The read of a variable holding a number never ends stuck -/

set_option hygiene false in
macro "ns_step3" : tactic => `(tactic| first
  | with_reducible exact ns_ppPlace _
  | with_reducible exact ns_copyRead _ _
  | with_reducible exact ns_fire _ _
  | with_reducible exact ns_isCapture _
  | with_reducible exact ns_logEffect_var _ _
  | with_reducible exact ns_setPlace _ _
  | ns_step2)

macro "ns_go3" : tactic => `(tactic| repeat (any_goals ns_step3))

theorem nsAt_accessPath_num {n i f j : Nat} {bd : Binding} {st : MState} (hn : NumAt st i f j bd) :
    NSAt (accessPath n (.var i)) st := by
  cases n with
  | zero => unfold accessPath; exact ns_exhausted _ _
  | succ k =>
    unfold accessPath
    simp only [Place.steps]
    refine nsAt_get_bind (nsAt_bind (ns_varPos _ _) fun b pos s' h => ?_)
    obtain ⟨rfl, hp⟩ := runs_varPos_inv h
    rw [hn.pos] at hp; cases hp
    simp only [hn.valAt, firstLiveLoanOnPath_num hn.num]
    exact ns_pure _ _

theorem nsAt_accessInside_num {n i f j : Nat} {bd : Binding} {o : Bool} {st : MState} (hn : NumAt st i f j bd) :
    NSAt (accessInside n (.var i) o) st := by
  cases n with
  | zero => unfold accessInside; exact ns_exhausted _ _
  | succ k =>
    unfold accessInside
    refine nsAt_bind (ns_content _ _) fun b v s' h => ?_
    obtain ⟨rfl, rfl⟩ := runs_content_var hn h
    have h1 : ∀ E : Env, liveOwnedLoansIn E bd.val = [] := fun E => by
      simp [liveOwnedLoansIn, Value.Num.ownedLoans_nil hn.num]
    have h2 : ∀ E : Env, liveLoansIn E bd.val = [] := fun E => liveLoansIn_nil (Value.Num.loans_nil hn.num)
    cases o <;> (refine nsAt_get_bind ?_; simp only [h1, h2, Bool.false_eq_true, if_false, if_true,
      List.isEmpty_nil, Bool.not_true]; exact ns_pure _ _)

set_option maxHeartbeats 4000000 in
theorem nsAt_readPlace_num {n i f j : Nat} {bd : Binding} {st : MState} (hn : NumAt st i f j bd) :
    NSAt (Ochr.readPlace n (.var i)) st := by
  cases n with
  | zero => unfold Ochr.readPlace; exact ns_exhausted _ _
  | succ m =>
    unfold Ochr.readPlace
    refine nsAt_bind (nsAt_accessPath_num hn) fun b₁ _ s₁ ha => ?_
    have := runs_accessPath_num hn ha; subst this
    refine nsAt_bind (nsAt_accessInside_num hn) fun b₂ _ s₂ hai => ?_
    have := runs_accessInside_num hn hai; subst this
    refine nsAt_bind (ns_content _ _) fun b₃ w s₃ hc => ?_
    obtain ⟨rfl, rfl⟩ := runs_content_var hn hc
    refine nsAt_get_bind ?_
    rw [Value.Num.outerLoans_nil hn.num]
    simp only [List.any_nil, Bool.false_eq_true, if_false]
    refine nsAt_bind (ns_unsizedCheck _ _ _ _) fun b₄ _ s₄ hu => ?_
    have := runs_unsizedCheck_num hn.num hu; subst this
    have hx : ∀ x : Value, x.Num → x = .zero ∨ ∃ w, x = .succ w := fun x hx => by
      cases hx with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨_, rfl⟩
    have hhole := Value.Num.hasHole hn.num
    refine nsAt_get_bind (nsAt_get_bind (nsAt_ite (nsAt_modify_bind (NSAt.of_ns ?_ _)) (NSAt.of_ns ?_ _))) <;>
    rcases hx _ hn.num with e | ⟨w', e⟩ <;> rw [e] <;>
    simp only [BEq.beq, Value.beq, Bool.false_eq_true, if_false] <;> rw [← e] <;> ns_go3


/-! ## `eval` around `evalCore` never ends stuck unless `evalCore` does -/

theorem ns_getFlags : NS getFlags := by unfold getFlags; ns_go2
theorem ns_setFlags (f : Bool × Bool) : NS (setFlags f) := by unfold setFlags; ns_go2
theorem ns_jErased (n : Nat) (P : Term) : NS (jErased n P) := by
  unfold jErased; ns_go2; all_goals exact (decideNS _).2.2.2.2.2.2.2.2.1 _ _ _ _
theorem ns_leafProof : ∀ (n : Nat) (t : Term) (v : Value), NS (leafProof n t v)
  | 0, _, _ => by unfold leafProof; ns_go2
  | n + 1, t, v => by
    unfold leafProof; ns_go2
    all_goals first
      | exact ns_varPos _
      | exact ns_fieldIsProof _
      | exact ns_leafProof n _ _
      | exact ns_lookupGlobal _
      | exact (decideNS _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
      | exact (decideNS _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _

theorem nsAt_privately {α : Type} {x : M α} {s : MState} (hx : NSAt x { s with privateDepth := s.privateDepth + 1 }) :
    NSAt (Ochr.privately x) s := by
  have e : Ochr.privately x = (do
      let saved ← get
      modify fun s => { s with privateDepth := s.privateDepth + 1 }
      let r ← Ochr.onFail x (restoreKeep saved)
      restoreKeep saved
      pure r) := rfl
  rw [e]
  refine nsAt_get_bind (nsAt_modify_bind (nsAt_bind (nsAt_onFail hx ?_) fun _ _ _ _ =>
    ns_bind ?_ (fun _ => ns_pure _) _))
  all_goals (unfold restoreKeep; exact ns_modify _)

theorem nsAt_withErased {α : Type} {x : M α} {s : MState} (hx : NSAt x { s with erasedDepth := s.erasedDepth + 1 }) :
    NSAt (Ochr.withErased x) s := by
  unfold Ochr.withErased
  exact nsAt_modify_bind (nsAt_bind (nsAt_onFail hx (ns_modify _)) fun _ _ _ _ =>
    ns_bind (ns_modify _) (fun _ => ns_pure _) _)

theorem nsAt_bind_keep {α β : Type} {x : M α} {k : α → M β} {s : MState} (hx : NS x) (hk : Keep x)
    (hc : ∀ a, NSAt (k a) s) : NSAt (x >>= k) s :=
  nsAt_bind (hx s) fun _ a _ h => (runs_keep hk h) ▸ hc a

set_option maxHeartbeats 4000000 in
/-- `evalAt` ends stuck only where its `evalCore` does, run on the state itself or on a statement's
private copy; either way with the same Ω and the type demand set from the run's typing. -/
theorem nsAt_evalAt {n : Nat} {typed : Bool} {t : Term} {hint : Option Value} {s : MState}
    (hh : s.headEval = false) (htd : s.tailDecl = none) (hv : ∀ w, t ≠ .val w)
    (hc : ∀ s', s'.env = s.env → s'.wantHere = (typed || s.wantTy) → s'.wantTy = false →
      NSAt (Ochr.evalCore n typed t hint) s') :
    NSAt (Ochr.evalAt (n + 1) typed t hint) s := by
  unfold Ochr.evalAt
  -- seven reads: D130 added the deferral flag's
  refine nsAt_get_bind (nsAt_get_bind (nsAt_get_bind (nsAt_get_bind (nsAt_get_bind (nsAt_get_bind
    (nsAt_get_bind (nsAt_modify_bind (nsAt_modify_bind ?_))))))))
  rw [if_pos (by rw [hh]; cases t <;> first | rfl | exact absurd rfl (hv _)), htd]
  split
  · rename_i h; cases h
  refine nsAt_bind_keep (ns_map _ (ns_withLive _ ((decideNS _).2.2.2.2.2.2.2.2.1 _ _ _ _)))
    (keep_map _ (keep_withLive _ ((decideKeep _).2.2.2.2.2.2.2.2.1 _ _ _ _))) fun d? => ?_
  dsimp only
  refine nsAt_modify_bind ?_
  split
  all_goals (try refine nsAt_bind_keep (ns_preFlags _ _) (keep_preFlags _ _) fun pre => ?_)
  all_goals
    repeat (first | (refine nsAt_get_bind ?_) | (refine nsAt_modify_bind ?_) | (dsimp only; done) | dsimp only)
    refine nsAt_bind (nsAt_onFail (nsAt_ite ?_ ?_) (ns_modify _)) fun _ _ _ _ => NSAt.of_ns ?_ _
  all_goals first
    | exact hc _ rfl rfl rfl
    | (refine nsAt_bind ?_ fun _ _ _ _ => NSAt.of_ns ?_ _
       · rw [inStatement_eq]
         exact nsAt_privately (nsAt_withErased (nsAt_bind (hc _ rfl rfl rfl) fun _ _ _ _ =>
           ns_bind ns_getFlags (fun _ => ns_pure _) _))
       · ns_go3
         all_goals exact ns_setFlags _)
    | (ns_go3
       all_goals first
         | exact ns_getFlags
         | exact ns_ctorIsProof _
         | exact ns_jErased _ _
         | exact (decideNS _).2.2.2.2.2.2.2.2.2.1 _ _ _ _ _ _
         | exact ns_leafProof _ _ _
         | exact ns_setFlags _)

end Ochr.Meaning.Steps.Machine
