import Ochr.Meaning.Steps.FrameInduction
import Ochr.Meaning.Steps.FrameRec

/-!
# The call in place, from the frame property: the first use (lead36, 2026-11-27; docs/31 D230)

Corollary C1 of `<sec-frame-stmt>` ("a call in place"; Lean `callOf_inPlace`, open), for a GLOBAL callee whose body is
in the fragment the frame property is proved on (`Term.frameFree`: no function, function type or `Id` formed in it).
Two runs of the callee's body:
- IN PLACE (`CallRef.runCallRef`, the checker's `runBody`): its frame pushed on the caller's state (`callFrame`: `self`
  the callee's meaning at its declared type, each parameter the argument, a borrow parameter holding the ARGUMENT's
  label `kᵢ`), the body, the pop (`popCallFrame`);
- IN THE CLOSURE (`RunCongr.fixBodyAt`, the `.fix` clause's `bodyAt`): from the global's forming state `stateOf 0 []`
  under a fresh bottom frame, `self`, then each parameter (`fixStep`: a borrow parameter at a FRESH label `lᵢ = i` with a
  cell in frame 0), the body, the ends of every label but the returned one, the cells read as the finals.
`callOf` applies the closure's function `G` (`fixG`), which the fixpoint equation (`FixEqG`) equates with the closure run
whose `self` is `G` itself at its true type.

**What is proved here** (`body_agree`): from the start condition `CallStartG` (the in-place state after the push and the
closure's state after its parameters are pushed are related by the internal relation `FrameInv` under the call's renaming
`callRen`, and the call point meets `FrameStart`), the two body runs agree (`FrameAgreeI`): the frame property
`runFrameI_frameFree` APPLIES at the call, with the in-place state after the push as its `s₀` (the fourth referee's F3: its
`s₀` is that state, not the call point), the parameter labels `ks` the arguments' labels in parameter order, and the
closure's side `fixBodyAt`'s. And C1 (`callInPlace_of`): `runCallRef` and `callOf` of a global's meaning agree (both fail,
or the same result and a state to which the relation transfers), from `CallStartG`, the pop and link `CallPopG`, and the
fixpoint equation `FixEqG`.

**The gap the first use found (docs/31 D230), closed**: as first written `runBodyRef` read the callee's parameter types,
codomain and codomain reading on the CALLER's state with the capture frame pushed, the closure on its forming state: the
frame property's start (`FrameRel.top`, the parameters' stored types; the hint the body runs at) needs them EQUAL, which
held only through a frame-independence of type runs nothing stated (a type with an `Id` observes every position; one
formed in a body would read the caller's frames under the strict whole-state test). Repaired by reading them in the
closure value's own forming state (`CallRef.runBodyRef`, `Statements.bodyFrame`), as the paper's C4 says ("equal by
definition").
-/

namespace Ochr.Meaning.Steps.Form.CallInPlace

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.FrameEnd

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A global's forming state: `meanV` reads `.clo [] t []` by the `.fix` clause from it (`GlobalsOk.fn`). -/
def formG : SState := stateOf 0 []

/-- The closure's binders, body hint and codomain reading at a global's code (`run_fix_def`'s `fb`, at `formG`). -/
noncomputable def fbG (ds : List Term) (c : Term) : List PBind × (List Sem → TyS) × DeclInfo :=
  (bindsOf K ρ φ formG ds, fixCod K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c,
    K.D.typeDecl (K.D.teleDecls (scopeOf formG) ds) c)

/-- Its domains and codomain. -/
noncomputable def psG (ds : List Term) : List PiDom := runDoms K ρ φ formG ds
noncomputable def outG (ds : List Term) (c : Term) : PiCod :=
  codOf K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c

/-- The declared sort, the function type, the closure's function (`fixG`, from the counter `0`) and the global's meaning
(its closure), all at `formG`. -/
noncomputable def lG (hs : List Hint) (ds : List Term) (c : Term) : Nat := K.D.piSort (scopeOf formG) (.pi hs ds c)
noncomputable def piTG (hs : List Hint) (ds : List Term) (c : Term) : TyM :=
  piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) (outG K ρ φ ds c)
noncomputable def GG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : List Sem → Option BodyOut :=
  fixG K ρ φ (fbG K ρ φ ds c) (lG K hs ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 dec body
noncomputable def selfG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Sem :=
  closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) (outG K ρ φ ds c) (GG K ρ φ hs ds c dec body)

/-- The in-place state after the push (`runBodyRef`'s, at a global: no captures). -/
noncomputable def inStart (fres : Res) (ds : List Term) (c : Term) (args : List Res) (s : SState) : SState :=
  callFrame K ρ φ [] [] fres (fbG K ρ φ ds c).2.2 (fbG K ρ φ ds c).1 args s

/-- The closure's state after the push (`fixBodyAt`'s `s₂`), at `self` meaning `selfM` at `piT`. -/
noncomputable def clStart (ds : List Term) (c : Term) (piT : TyM) (selfM : Sem) (args : List Sem) : SState :=
  ((args.zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c))
    ((formG.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }), [], [])).1

end

/-- The parameter labels of a call: the labels its arguments carry, in parameter order (each a borrow argument's). -/
def argLabels (args : List Res) : List Nat := args.filterMap (·.2.label)

/-- **The call's renaming** of the closure's labels to the in-place ones: the cells' labels `0, …, m - 1` (fresh from the
forming state's counter `0`, in parameter order) to the parameter labels, the closure's later labels to the in-place
counter onwards. -/
def callRen (ks : List Nat) (n : Nat) (l : Nat) : Nat :=
  if h : l < ks.length then ks[l] else n + (l - ks.length)

/-! ## The call's renaming: the clauses of `FrameRel` and `FrameInv` that hold by its definition -/

theorem callRen_lt {ks : List Nat} {n l : Nat} (h : l < ks.length) : callRen ks n l = ks[l] := by
  simp [callRen, h]

theorem callRen_ge {ks : List Nat} {n l : Nat} (h : ks.length ≤ l) : callRen ks n l = n + (l - ks.length) := by
  simp [callRen, Nat.not_lt.2 h]

/-- `FrameRel.fresh` at the start: the closure's counter is `ks.length` (one cell per parameter label). -/
theorem callRen_fresh (ks : List Nat) (n j : Nat) : callRen ks n (ks.length + j) = n + j := by
  rw [callRen_ge (Nat.le_add_right _ _)]; congr 1; omega

/-- `FrameInv.srange`: every closure label goes to a parameter label or to one at or above the call's counter. -/
theorem callRen_srange (ks : List Nat) (n l : Nat) : callRen ks n l ∈ ks ∨ n ≤ callRen ks n l := by
  by_cases h : l < ks.length
  · exact .inl (by rw [callRen_lt h]; exact List.getElem_mem h)
  · exact .inr (by rw [callRen_ge (Nat.le_of_not_lt h)]; omega)

/-- `FrameRel.inj`: one to one, the parameter labels being distinct and below the call's counter. -/
theorem callRen_inj {ks : List Nat} {n : Nat} (hnd : ks.Nodup) (hlt : ∀ k ∈ ks, k < n) (l l' : Nat)
    (h : callRen ks n l = callRen ks n l') : l = l' := by
  by_cases h₁ : l < ks.length <;> by_cases h₂ : l' < ks.length
  · rw [callRen_lt h₁, callRen_lt h₂] at h
    exact (List.getElem_inj hnd).mp h
  · rw [callRen_lt h₁, callRen_ge (Nat.le_of_not_lt h₂)] at h
    have := hlt _ (List.getElem_mem h₁); omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁), callRen_lt h₂] at h
    have := hlt _ (List.getElem_mem h₂); omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁), callRen_ge (Nat.le_of_not_lt h₂)] at h; omega

/-- `AccInv.order`/`orderAll` and `mono`/`monoAll`: the parameter labels' preimages are the first, and the renaming is
monotone on the others. -/
theorem callRen_order {ks : List Nat} {n : Nat} (hlt : ∀ k ∈ ks, k < n) (l l' : Nat)
    (h : callRen ks n l ∈ ks) (h' : callRen ks n l' ∉ ks) : l < l' := by
  by_cases h₁ : l < ks.length
  · by_cases h₂ : l' < ks.length
    · exact absurd (by rw [callRen_lt h₂]; exact List.getElem_mem h₂) h'
    · omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁)] at h
    have := hlt _ h; omega

theorem callRen_mono {ks : List Nat} {n : Nat} (l l' : Nat) (h : callRen ks n l ∉ ks) (h' : callRen ks n l' ∉ ks)
    (hl : l < l') : callRen ks n l < callRen ks n l' := by
  have h₁ : ks.length ≤ l := Nat.le_of_not_lt fun hlt => h (by rw [callRen_lt hlt]; exact List.getElem_mem hlt)
  have h₂ : ks.length ≤ l' := Nat.le_of_not_lt fun hlt => h' (by rw [callRen_lt hlt]; exact List.getElem_mem hlt)
  rw [callRen_ge h₁, callRen_ge h₂]; omega

/-- The push reads the callee's meaning and its type's code only (`self` is bound at `{fres.2 with label := none}`):
`K.C.global g` and `(selfG, .plain piTG)` push the same frame where they agree there. -/
theorem inStart_fres (K : RunCtx) (ρ : Assignment) (φ : Future) {fres fres' : Res} (h1 : fres.1 = fres'.1)
    (h2 : fres.2.m = fres'.2.m) (ds : List Term) (c : Term) (args : List Res) (s : SState) :
    inStart K ρ φ fres ds c args s = inStart K ρ φ fres' ds c args s := by
  obtain ⟨a, ⟨m, l⟩⟩ := fres
  obtain ⟨a', ⟨m', l'⟩⟩ := fres'
  simp only at h1 h2
  subst h1 h2
  rfl

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The start of a call in place** (MODEL; OPEN; the paper's start lemma, `<sec-frame-fix>`). At a call point `s` of a
global's code, with arguments `args` that are members of the domains, carrying labels exactly at the borrow parameters
(held at their parameters' content types: `BorrowArgsTyped`), and the callee's meaning `fres = (selfM, piT)` a member of
its type: the in-place state after the push is a call point for the frame property (`FrameStart`, with itself as `s₀`) and
is related to the closure's state after its push by the internal relation, under `callRen`. Hypotheses on the call point
beyond goodness: lending well founded (`LendWF`, the paper's (H6), from the checker's acyclic lending through (II)'s
relation), and every site at a position (so the fresh frame holds no site). Read clause by clause against `FrameInv`
(docs/31 D230): every clause holds at the start by the push's construction (the two top frames are `self` and the
parameters, the same meanings, types and readings, the labels `kᵢ` against `lᵢ = i`; frame 0 of the closure is the
cells, each reading its own label, lent there; the caller's frames are `s₀`'s own, read at `cellFuture`, the identity at
the start), with `BorrowArgsTyped` giving the held types (`FrameRel.held`, `heldAll`), the domains' membership the
goodness of both states, and `callRen` the range, order and counter clauses by its definition. -/
def CallStartG : Prop :=
  ∀ (hs : List Hint) (ds : List Term) (c : Term) (selfM : Sem) (piT : TyM) (args : List Res) (s : SState),
    piT = piTyAt K.dm.read (K.D.piSort (scopeOf formG) (.pi hs ds c)) (psG K ρ φ ds) (outG K ρ φ ds c) →
    selfM ∈ₛ[K.dm.read] piT →
    Strict.SGood K.dm K.Γ φ s → LendWF s → (∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions) →
    DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)) →
    (∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef)) →
    BorrowArgsTyped K.dm.read (selfM, .plain piT) args s →
    FrameStart (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args) ∧
    FrameInv K φ (callRen (argLabels args) s.nextLoan) (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args)
      (inStart K ρ φ (selfM, .plain piT) ds c args s) (clStart K ρ φ ds c piT selfM (args.map (·.1)))

/-- **The first use of the frame property** (PROVED from `CallStartG`): at a call of a global whose body is frame-free, the
body's run in place (from the pushed frame) and its run in the closure (from the closure's pushed frame), at the same
hint, both fail or agree: the same result, its label renamed by `callRen`, the internal relation at the end. -/
theorem body_agree (hst : CallStartG K ρ φ) (hc : Strict.FundCtx K) (hs : List Hint) (ds : List Term) (c : Term)
    (body : Term) (hv : body.valsOk (Strict.ValsP K ρ φ)) (hf : body.frameFree = true) (selfM : Sem) (piT : TyM)
    (args : List Res) (s : SState) (hint : TyS)
    (hpi : piT = piTyAt K.dm.read (K.D.piSort (scopeOf formG) (.pi hs ds c)) (psG K ρ φ ds) (outG K ρ φ ds c))
    (hself : selfM ∈ₛ[K.dm.read] piT) (hg : Strict.SGood K.dm K.Γ φ s) (hl : LendWF s)
    (hsites : ∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions)
    (hdom : DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)))
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef))
    (hbt : BorrowArgsTyped K.dm.read (selfM, .plain piT) args s) :
    FrameAgreeI K φ (callRen (argLabels args) s.nextLoan) (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args)
      (runT K ρ φ true hint body (inStart K ρ φ (selfM, .plain piT) ds c args s))
      (runT K ρ φ true hint body (clStart K ρ φ ds c piT selfM (args.map (·.1)))) := by
  obtain ⟨hs₀, hI⟩ := hst hs ds c selfM piT args s hpi hself hg hl hsites hdom hlab hbt
  exact runFrameI_frameFree K ρ φ _ _ _ true hint body _ _ hc hs₀ hv hf hI

/-- The state the body's run in place starts from, before the push (`runCallRef`): at a borrow codomain the call first
reserves the result's label and lends it, as fills, wherever the borrow arguments are lent ([Lend], main's D99). -/
noncomputable def callPre (c : Term) (args : List Res) (s : SState) : SState :=
  match c with
  | .ref _ =>
    let lentK := ((args.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true }
    (s.freshLoan.2).setLent s.freshLoan.1 lentK
  | _ => s

/-- **Two outcomes of a call agree**: both fail, or both succeed with the same result, and the relation of any checker
state with the first state holds with the second (the counters, and the records and sites of dead labels, may differ:
the run in place made and ended the body's labels; `callOf` made none). The conclusion `Steps/Call.callOf_inPlace` asked. -/
def InPlaceAgree : Option (Res × SState) → Option (Res × SState) → Prop
  | some (r, t), some (r', t') => r = r' ∧ ∀ (st : MState) (π : Nat → Nat), Rel K ρ φ π st t → Rel K ρ φ π st t'
  | none, none => True
  | _, _ => False

/-- **The pop and the link** (MODEL; OPEN; the paper's pop lemma and the link to `callOf`, `<sec-frame-fix>`). At a call
of an accepted global (not the one under check) whose meaning is the closure of `G` at `piT` (`GlobalsOk.fn`), from
the agreement of the two body runs (`body_agree`) and the fixpoint equation at the arguments (`FixEqG`): the call in place
and `callOf` agree. Its parts, read (docs/31 D230): the pop's ends (`popEnds` from the in-place counter at the push, or
held in the callee's frame, but the returned label) are the closure's (every live label but the returned one) through
the renaming, in orders that differ only among parameter labels (`perm_fold`), their strict tests by (O1)
(`endOk_corr`, `frameRel_foldEnd`); after them the cells read the finals, and the caller's frames read the call point's at
the finals (`FrameRel.lowerVal`, `cellFuture` at constants), which is `callOf`'s `mapVals` with the fixes; the frame is
dropped, a returned borrow re-parked; at a borrow codomain the reserved label (the call point's counter) is `callOf`'s
fresh one, `endInto` its renaming; `callOf` applies `G` (`applyFnL_closureL`), which the fixpoint equation makes the
closure run the agreement is about. -/
def CallPopG : Prop :=
  ∀ (st : MState) (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat)
    (body : Term) (args : List Res) (s : SState),
    GlobalsOk K st → st.globals.find? (·.name == g) = some gd → K.cur.map (·.1) ≠ some g →
    gd.fn? = some (.fix self hs ds c dec body) →
    (K.C.global g).1 = selfG K ρ φ hs ds c dec body → (K.C.global g).2.m = piTG K ρ φ hs ds c →
    Strict.SGood K.dm K.Γ φ (callPre c args s) →
    DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)) →
    BorrowArgsTyped K.dm.read (K.C.global g) args s →
    GG K ρ φ hs ds c dec body (args.map (·.1)) = fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
      (piTG K ρ φ hs ds c) 0 body (selfG K ρ φ hs ds c dec body) (args.map (·.1)) →
    FrameAgreeI K φ (callRen (argLabels args) (callPre c args s).nextLoan)
      (inStart K ρ φ (selfG K ρ φ hs ds c dec body, .plain (piTG K ρ φ hs ds c)) ds c args (callPre c args s)) (argLabels args)
      (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body
        (inStart K ρ φ (selfG K ρ φ hs ds c dec body, .plain (piTG K ρ φ hs ds c)) ds c args (callPre c args s)))
      (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body
        (clStart K ρ φ ds c (piTG K ρ φ hs ds c) (selfG K ρ φ hs ds c dec body) (args.map (·.1)))) →
    InPlaceAgree K ρ φ (runCallRef K ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] args s)
      (callOf K.dm.read (K.C.global g) args s)

/-- `BorrowArgsTyped` reads the callee's type only. -/
theorem borrowArgsTyped_ty {fv fv' : Res} (h : fv.2.m = fv'.2.m) {args : List Res} {s : SState}
    (hb : BorrowArgsTyped K.dm.read fv args s) : BorrowArgsTyped K.dm.read fv' args s := by
  unfold BorrowArgsTyped refLabelsOf at hb ⊢
  rw [← h]; exact hb

/-- **C1, a call in place, for a frame-free body** (assembled; assumes `CallStartG`, `CallPopG`, and the context's fixpoint
clause `FixEqG`): at a call of an accepted global whose body is in the fragment the frame property is proved on, the call
run in place and `callOf` of the global's meaning agree. The frame property used is `runFrameI_frameFree`, proved. The
global's meaning is its closure at its forming state (`hselfV`, `hselfT`: what `GlobalsOk.fn` and the `.fix` clause give
where the global is a member, `hmem`). -/
theorem callInPlace_of (hst : CallStartG K ρ φ) (hpop : CallPopG K ρ φ) (hc : Strict.FundCtx K) (st : MState)
    (hfix : FixEqG K st) (hG : GlobalsOk K st) (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) (hfind : st.globals.find? (·.name == g) = some gd)
    (hcur : K.cur.map (·.1) ≠ some g) (hfn : gd.fn? = some (.fix self hs ds c dec body))
    (hv : body.valsOk (Strict.ValsP K ρ φ)) (hf : body.frameFree = true) (args : List Res) (s : SState)
    (hselfV : (K.C.global g).1 = selfG K ρ φ hs ds c dec body) (hselfT : (K.C.global g).2.m = piTG K ρ φ hs ds c)
    (hmem : (K.C.global g).1 ∈ₛ[K.dm.read] (K.C.global g).2.m)
    (hg : Strict.SGood K.dm K.Γ φ (callPre c args s)) (hl : LendWF (callPre c args s))
    (hsites : ∀ l (y : Site), y ∈ (callPre c args s).lent l → y.pos ∈ (callPre c args s).positions)
    (hdom : DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)))
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef))
    (hbt : BorrowArgsTyped K.dm.read (K.C.global g) args s)
    (hbt' : BorrowArgsTyped K.dm.read (K.C.global g) args (callPre c args s)) :
    InPlaceAgree K ρ φ (runCallRef K ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] args s)
      (callOf K.dm.read (K.C.global g) args s) := by
  -- the fixpoint equation at the global's forming state, at the arguments
  have he := hfix g gd self hs ds c dec body hfind hcur hfn ρ φ formG (args.map fun a : Res => a.1)
    (hdom : DomMembers K.dm.read (runDoms K ρ φ formG ds) (args.map fun a : Res => a.1))
  -- the start, then the frame property at the body (`body_agree`)
  have hmem' : selfG K ρ φ hs ds c dec body ∈ₛ[K.dm.read] piTG K ρ φ hs ds c := by rw [← hselfV, ← hselfT]; exact hmem
  have hbt₁ : BorrowArgsTyped K.dm.read (selfG K ρ φ hs ds c dec body, .plain (piTG K ρ φ hs ds c)) args (callPre c args s) :=
    borrowArgsTyped_ty K (by rw [hselfT]; rfl) hbt'
  have hb := body_agree K ρ φ hst hc hs ds c body hv hf _ _ args (callPre c args s)
    ((fbG K ρ φ ds c).2.1 (args.map (·.1))) rfl hmem' hg hl hsites hdom hlab hbt₁
  exact hpop st g gd self hs ds c dec body args s hG hfind hcur hfn hselfV hselfT hg hdom hbt he hb

end

end Ochr.Meaning.Steps.Form.CallInPlace
