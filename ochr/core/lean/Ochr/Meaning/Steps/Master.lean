import Ochr.Meaning.Steps.FormTail
import Ochr.Meaning.Steps.Column

/-!
# The master induction of (II): the general step, by term former (lead22, 2026-11-22; docs/31 D150)

The checker's `eval` and `checkTail` recurse on fuel (one mutual block, `Machine.lean`), so (II) for
every term is one strong induction on fuel. This file fixes the statement that induction proves, its
induction hypothesis, and the list of what remains: one named step per term former of `eval` (the 26
constructors of `Term`) and one per shape `checkTail` matches (six), each "from the induction
hypothesis at every smaller fuel, the statement at this fuel for terms of this former". The induction
itself (`master`) is proved with no `sorry`; it ASSUMES the 32 step statements, bundled as `AllSteps`.

## The statement: `EvalAt`, and how it differs from `Form.eval_sim`

`EvalAt K ρ φ n t` is `Form.eval_sim`'s statement for one term with TWO more hypotheses, both of which
the existing steps already take (`Column.EvalSim`), and without which the statement is false:

* `Mode st` (the plain mode: no head evaluation, not copying, not in place, not erased). `Pre` reads
  the state's kernel (`MState.norm`), which forgets the mode, so `eval_sim` quantifies over every mode;
  but in copying mode (inside `clone`) or in place (a call's head) the checker's read of a place of a
  non-copy type leaves the place as it was, where the reference's plain run of the same term moves it,
  and the states after are not related.
* the reading handed down (`tailDecl`) is none or the table's reading of the term. A sequencing form
  hands its tail its own reading; a reading handed down that is not the table's would make the
  checker's pre-pass erase a term the reference runs.

`EvalAt` does NOT take `Column.EvalSim`'s hypothesis that the aligned table leaves the term unerased:
the master statement is for every term, erased ones included (each step owns its erased case).

The statement for a run in tail position, `TailAt`, is `Form.TailSim` with the entry conditions of
`EvalAt` that a typed run needs (no `hok`: `checkTail` runs typed).

## The induction hypothesis, and why it has this shape

`IH K φ n`: at every fuel below `n`, at EVERY `Δ` and assignment, `EvalAt` and `TailAt` for EVERY term.
* Every fuel below: `eval (n + 1)` runs `evalAt n`, which runs `evalCore (n - 1)`, whose sub-runs are at
  `n - 2` or below through the helpers (`evalMatch`, `evalCall`, `closeBlock`, `runBody`, …); each step
  decides how far down its sub-runs are.
* Every `Δ` and assignment: a sub-run after the first starts under the extension the earlier ones
  handed on (`Ext`: `ρ'`, `Δ'`), as the fragment's `let` and `;` cases take their tails' hypotheses
  (`FragLet.letF_core`'s `ihw`). The other fields of the context (`dm`, `Γ`, `C`, `D`, `Λ`, `cur`) stay
  fixed within one check: a recursive function's stage changes `C` and `cur` (column `R`), but only
  between checks, outside this induction (the knot's induction on the bound is outside it).
* Both statements in one induction: `checkTail`'s default case runs `eval`, and `eval` reaches
  `checkTail` through `.fix` (`checkFix`), so the two are mutually recursive on fuel; one strong
  induction on the conjunction covers both, and no second induction is needed.
* Typed and untyped runs alike: an in-place call runs the callee's body untyped (`runBody`), so the
  hypothesis covers `typed = false`, with the strict run's success (`hok`) as its entry condition.
* The decision table: `DecTab K.D st'` at the END of each sub-run, which every step gets from its own
  end by `DecTab.back` (the checker's runs only extend the tables), the callee's body in place included.

What the hypothesis does NOT cover, and the steps that meet it (docs/31 D150): a sub-run in a mode other
than the plain one. `evalAt` runs an erased term's `evalCore` under `inStatement` (`erasedDepth + 1`);
`clone`/`peek` run their operand under `withCopying` and `withErased`; a function whose calls are erased
runs its body under `withErasedIf`. Those steps need either the hypothesis at `erasedDepth > 0` (the
checker reads the depth only in `atRuntime` and the capture-move check) or their own statement.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The statements -/

/-- **The evaluation step at fuel `n`, for one term**: `Form.eval_sim`'s statement for `t`, from a state in
the plain mode (`Mode`) whose handed-down reading, if any, is the table's reading of `t`. -/
def EvalAt (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    Mode st → (st.tailDecl = none ∨ st.tailDecl = some (K.D.declOf (DecideScope.topReadings st) t)) →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    (typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.eval n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.tailNext (hintM K ρ hint) t) v T?

/-- **The tail step at fuel `n`, for one term**: `Form.TailSim` for `t` with every continuation, from a
state in the plain mode with no reading handed down, for a term the strict run accepts the embedded
values of, holding the state's unknowns and no hole; the table aligned at the run's end. -/
def TailAt (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState),
    Mode st → st.tailDecl = none →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    DecTab K.D st' →
    Runs (Ochr.checkTail n t k) st bh () st' →
    TailOut K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) t) k

/-- **The induction hypothesis at fuel `n`**: at every smaller fuel, every `Δ` and every assignment, the
evaluation step and the tail step for every term. -/
def IH (K : RunCtx) (φ : Future) (n : Nat) : Prop :=
  ∀ m, m < n → ∀ (Δ : Nat → TyS) (ρ : Assignment),
    (∀ t, EvalAt { K with Δ := Δ } ρ φ m t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ m t)

/-- `Form.eval_sim` gives `EvalAt` (it is the stronger statement; it is false as it stands: the module
docstring). -/
theorem evalAt_of_eval_sim {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} (h : eval_sim K ρ φ n)
    (t : Term) : EvalAt K ρ φ n t :=
  fun st st' typed hint v T? s π _ _ hp hr hS hv hab hnh hok hD bh hrun =>
    h st st' typed t hint v T? s π hp hr hS hv hab hnh hok hD bh hrun

/-- `EvalAt` for a term the table leaves unerased is `Column.EvalSim` (the fragment's and the columns'
form, with its trivial state and typing predicates). -/
theorem evalSim_of_evalAt {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} {t : Term}
    (h : EvalAt K ρ φ n t) : EvalSim K ρ φ n t :=
  fun st st' typed hint v T? s π _ _ hm htd hp hr hS hv hab hnh _ hok hD bh hrun =>
    h st st' typed hint v T? s π hm htd hp hr hS hv hab hnh hok hD bh hrun

/-! ## The shapes `checkTail` matches -/

/-- The terms `Machine.checkTailAt` treats by their shape: `let`, `;`, the two matches, and the
primitives `split f in u`, `split f { … }`, `rewrite`/`rewriteR` with two arguments. Every other term in
tail position is evaluated (`eval fuel' true t goal`) and handed to the continuation. The patterns are
`checkTailAt`'s, in its order. -/
def tailShaped : Term → Bool
  | .letIn .. | .seq .. | .matchNat .. | .matchInd .. => true
  | .prim "split" [.const _, _] => true
  | .prim "splitArms" [.const _, .letIn ..] => true
  | .prim "rewrite" [_, _] | .prim "rewriteR" [_, _] => true
  | _ => false

/-! ## The steps, one per term former of `eval`

Each is "from the induction hypothesis at fuel `n`, at every `Δ` and assignment, `EvalAt` at fuel `n`
for every term of this former". -/

section
variable (K : RunCtx) (φ : Future)

/-- The step for a read of a place (`[Read]`; a place with a field step runs as a match, `projMatch`). -/
def StepPlace : Prop := ∀ n, IH K φ n → ∀ Δ ρ p, EvalAt { K with Δ := Δ } ρ φ n (.place p)
/-- The step for `&p` (`[Borrow]`). -/
def StepBorrow : Prop := ∀ n, IH K φ n → ∀ Δ ρ p, EvalAt { K with Δ := Δ } ρ φ n (.borrow p)
/-- The step for `p := u` (`[Assign]`). -/
def StepAssign : Prop := ∀ n, IH K φ n → ∀ Δ ρ p u, EvalAt { K with Δ := Δ } ρ φ n (.assign p u)
/-- The step for `let x = u; w` (`[Let]`, `[Drop]`). -/
def StepLetIn : Prop := ∀ n, IH K φ n → ∀ Δ ρ x u w, EvalAt { K with Δ := Δ } ρ φ n (.letIn x u w)
/-- The step for `u; w`. -/
def StepSeq : Prop := ∀ n, IH K φ n → ∀ Δ ρ u w, EvalAt { K with Δ := Δ } ρ φ n (.seq u w)
/-- The step for a match on a number (`evalMatch`: a known tag, a split closed off, [Entry], [Join]). -/
def StepMatchNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ p z u, EvalAt { K with Δ := Δ } ρ φ n (.matchNat p z u)
/-- The step for a global's name (`const`). -/
def StepConst : Prop := ∀ n, IH K φ n → ∀ Δ ρ c, EvalAt { K with Δ := Δ } ρ φ n (.const c)
/-- The step for an embedded value (`val`; outside `eval_of_core`: the pre-pass does not classify it). -/
def StepVal : Prop := ∀ n, IH K φ n → ∀ Δ ρ w, EvalAt { K with Δ := Δ } ρ φ n (.val w)
/-- The step for a universe (`sort`). -/
def StepSort : Prop := ∀ n, IH K φ n → ∀ Δ ρ l, EvalAt { K with Δ := Δ } ρ φ n (.sort l)
/-- The step for a Π-type (`[T-Pi]`, its captures on a copy). -/
def StepPi : Prop := ∀ n, IH K φ n → ∀ Δ ρ hs ds c, EvalAt { K with Δ := Δ } ρ φ n (.pi hs ds c)
/-- The step for a function value (`[Closure]`, `checkFix`'s body in tail position). -/
def StepFix : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ self hs ds c dec body, EvalAt { K with Δ := Δ } ρ φ n (.fix self hs ds c dec body)
/-- The step for a call (`evalCall`, `callFn`, the body in place, [Call-type], [Close]). -/
def StepCall : Prop := ∀ n, IH K φ n → ∀ Δ ρ f as hd, EvalAt { K with Δ := Δ } ρ φ n (.call f as hd)
/-- The step for the type `Nat`. -/
def StepNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .nat
/-- The step for `Z`. -/
def StepZero : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .zero
/-- The step for `S(u)`. -/
def StepSucc : Prop := ∀ n, IH K φ n → ∀ Δ ρ u, EvalAt { K with Δ := Δ } ρ φ n (.succ u)
/-- The step for the type `Unit`. -/
def StepUnit : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .unit
/-- The step for `()`. -/
def StepTt : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .tt
/-- The step for `Eq(A, a, b)` (each side on its own copy). -/
def StepEq : Prop := ∀ n, IH K φ n → ∀ Δ ρ A a b, EvalAt { K with Δ := Δ } ρ φ n (.eq A a b)
/-- The step for `cong f h`. -/
def StepCong : Prop := ∀ n, IH K φ n → ∀ Δ ρ f h, EvalAt { K with Δ := Δ } ρ φ n (.cong f h)
/-- The step for the borrow type `&A`. -/
def StepRef : Prop := ∀ n, IH K φ n → ∀ Δ ρ A, EvalAt { K with Δ := Δ } ρ φ n (.ref A)
/-- The step for `Id(A, t, u)` (`idType`, `observe`). -/
def StepId : Prop := ∀ n, IH K φ n → ∀ Δ ρ A a b, EvalAt { K with Δ := Δ } ρ φ n (.id A a b)
/-- The step for `(u : A)`. -/
def StepAscribe : Prop := ∀ n, IH K φ n → ∀ Δ ρ u A, EvalAt { K with Δ := Δ } ρ φ n (.ascribe u A)
/-- The step for a primitive (`J`, `symm`, `trans`, `rewrite`, `rewriteR`, `split`, `splitArms`, a hole,
`clone`, `peek`, `inplace`, an unknown name). -/
def StepPrim : Prop := ∀ n, IH K φ n → ∀ Δ ρ nm as, EvalAt { K with Δ := Δ } ρ φ n (.prim nm as)
/-- The step for a declared inductive type at its parameters (`evalTInd`). -/
def StepTInd : Prop := ∀ n, IH K φ n → ∀ Δ ρ nm as, EvalAt { K with Δ := Δ } ρ φ n (.tind nm as)
/-- The step for a constructor application (`evalCtor`). -/
def StepCtor : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ ty c h ps as, EvalAt { K with Δ := Δ } ρ φ n (.ctor ty c h ps as)
/-- The step for a match on a declared inductive (`evalMatchInd`, `evalMatchByType`). -/
def StepMatchInd : Prop := ∀ n, IH K φ n → ∀ Δ ρ p ty arms, EvalAt { K with Δ := Δ } ρ φ n (.matchInd p ty arms)

/-! ## The steps in tail position, one per shape `checkTail` matches -/

/-- `let x = u; w` in tail position (`u` evaluated, `w` checked in tail position with the drop in the
continuation). -/
def TStepLetIn : Prop := ∀ n, IH K φ n → ∀ Δ ρ x u w, TailAt { K with Δ := Δ } ρ φ n (.letIn x u w)
/-- `u; w` in tail position. -/
def TStepSeq : Prop := ∀ n, IH K φ n → ∀ Δ ρ u w, TailAt { K with Δ := Δ } ρ φ n (.seq u w)
/-- A match on a number in tail position (the split into worlds, column `P`'s general form). -/
def TStepMatchNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ p z u, TailAt { K with Δ := Δ } ρ φ n (.matchNat p z u)
/-- A match on a declared inductive in tail position (column `Not`'s general form). -/
def TStepMatchInd : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ p ty arms, TailAt { K with Δ := Δ } ρ φ n (.matchInd p ty arms)
/-- `split f in u`, `split f { … }`, `rewrite h u`, `rewriteR h u` in tail position. -/
def TStepPrim : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ nm as, tailShaped (.prim nm as) = true → TailAt { K with Δ := Δ } ρ φ n (.prim nm as)
/-- Every other term in tail position: evaluated with the goal as its hint, the result handed to the
continuation. -/
def TStepOther : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ t, tailShaped t = false → TailAt { K with Δ := Δ } ρ φ n t

/-- **The 32 step statements**: what remains of (II) for `eval` and `checkTail`, as a list one can count. -/
structure AllSteps : Prop where
  place : StepPlace K φ
  borrow : StepBorrow K φ
  assign : StepAssign K φ
  letIn : StepLetIn K φ
  seq : StepSeq K φ
  matchNat : StepMatchNat K φ
  const : StepConst K φ
  val : StepVal K φ
  sort : StepSort K φ
  pi : StepPi K φ
  fix : StepFix K φ
  call : StepCall K φ
  nat : StepNat K φ
  zero : StepZero K φ
  succ : StepSucc K φ
  unit : StepUnit K φ
  tt : StepTt K φ
  eq : StepEq K φ
  cong : StepCong K φ
  ref : StepRef K φ
  id : StepId K φ
  ascribe : StepAscribe K φ
  prim : StepPrim K φ
  tind : StepTInd K φ
  ctor : StepCtor K φ
  matchInd : StepMatchInd K φ
  tLetIn : TStepLetIn K φ
  tSeq : TStepSeq K φ
  tMatchNat : TStepMatchNat K φ
  tMatchInd : TStepMatchInd K φ
  tPrim : TStepPrim K φ
  tOther : TStepOther K φ

end

/-! ## The induction -/

/-- `{ { K with Δ := Δ } with Δ := Δ' }` is `{ K with Δ := Δ' }`. -/
theorem IH.restate {K : RunCtx} {φ : Future} {n : Nat} {Δ : Nat → TyS} (h : IH { K with Δ := Δ } φ n) :
    IH K φ n := h

/-- One step of the induction: the steps at fuel `n` from the hypothesis at `n`. -/
theorem master_step {K : RunCtx} {φ : Future} (hs : AllSteps K φ) {n : Nat} (ih : IH K φ n)
    (Δ : Nat → TyS) (ρ : Assignment) :
    (∀ t, EvalAt { K with Δ := Δ } ρ φ n t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ n t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | place p => exact hs.place n ih Δ ρ p
    | borrow p => exact hs.borrow n ih Δ ρ p
    | assign p u => exact hs.assign n ih Δ ρ p u
    | letIn x u w => exact hs.letIn n ih Δ ρ x u w
    | seq u w => exact hs.seq n ih Δ ρ u w
    | matchNat p z u => exact hs.matchNat n ih Δ ρ p z u
    | const c => exact hs.const n ih Δ ρ c
    | val w => exact hs.val n ih Δ ρ w
    | sort l => exact hs.sort n ih Δ ρ l
    | pi hs' ds c => exact hs.pi n ih Δ ρ hs' ds c
    | fix self hs' ds c dec body => exact hs.fix n ih Δ ρ self hs' ds c dec body
    | call f as hd => exact hs.call n ih Δ ρ f as hd
    | nat => exact hs.nat n ih Δ ρ
    | zero => exact hs.zero n ih Δ ρ
    | succ u => exact hs.succ n ih Δ ρ u
    | unit => exact hs.unit n ih Δ ρ
    | tt => exact hs.tt n ih Δ ρ
    | eq A a b => exact hs.eq n ih Δ ρ A a b
    | cong f h => exact hs.cong n ih Δ ρ f h
    | ref A => exact hs.ref n ih Δ ρ A
    | id A a b => exact hs.id n ih Δ ρ A a b
    | ascribe u A => exact hs.ascribe n ih Δ ρ u A
    | prim nm as => exact hs.prim n ih Δ ρ nm as
    | tind nm as => exact hs.tind n ih Δ ρ nm as
    | ctor ty c h ps as => exact hs.ctor n ih Δ ρ ty c h ps as
    | matchInd p ty arms => exact hs.matchInd n ih Δ ρ p ty arms
  · cases t with
    | letIn x u w => exact hs.tLetIn n ih Δ ρ x u w
    | seq u w => exact hs.tSeq n ih Δ ρ u w
    | matchNat p z u => exact hs.tMatchNat n ih Δ ρ p z u
    | matchInd p ty arms => exact hs.tMatchInd n ih Δ ρ p ty arms
    | prim nm as =>
      by_cases hsh : tailShaped (.prim nm as) = true
      · exact hs.tPrim n ih Δ ρ nm as hsh
      · exact hs.tOther n ih Δ ρ _ (by simpa using hsh)
    | _ => exact hs.tOther n ih Δ ρ _ rfl

/-- **The master induction**: from the 32 step statements, the evaluation step and the tail step at
every fuel, `Δ` and assignment, for every term. ASSUMES the 32 step statements (`AllSteps`) and nothing
else; what each step assumes in turn is its own (docs/31 D152's table). -/
theorem master {K : RunCtx} {φ : Future} (hs : AllSteps K φ) :
    ∀ n (Δ : Nat → TyS) (ρ : Assignment),
      (∀ t, EvalAt { K with Δ := Δ } ρ φ n t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ n t) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact master_step hs (fun m hm Δ ρ => ih m hm Δ ρ)

/-- **(II) for `eval`, at the run's own context**: every fuel, every term (the `Δ` of `K` itself). -/
theorem eval_all {K : RunCtx} {φ : Future} (hs : AllSteps K φ) (ρ : Assignment) (n : Nat) (t : Term) :
    EvalAt K ρ φ n t :=
  (master hs n K.Δ ρ).1 t

/-- **(II) for `checkTail`, at the run's own context.** -/
theorem tail_all {K : RunCtx} {φ : Future} (hs : AllSteps K φ) (ρ : Assignment) (n : Nat) (t : Term) :
    TailAt K ρ φ n t :=
  (master hs n K.Δ ρ).2 t

end Ochr.Meaning.Steps.Form.Master
