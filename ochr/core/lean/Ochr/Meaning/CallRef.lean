import Ochr.Meaning.Run

/-!
# The reference's call of a known function, in place (docs/31 D62)

`callOf` applies the callee's meaning. A closure means a function built from runs of its body in
its own frame, from the label counter 0, a borrow parameter at a fresh label read back through a
cell (`Run.lean`'s `.fix` clause, `bodyAt`). The checker runs the body in place instead: a frame
pushed on the caller's state, the body run, the frame popped (`Machine.runBody`). The induction
hypothesis reaches only a reference run from a state related to the checker's, so the step lemma
for the checker's run (`runBody_step_stmt`) compares it with the reference's run in place, defined
here. That the run in place agrees with `callOf` is a statement about the reference alone
(`Steps/Call.lean`, `callOf_inPlace`).
-/

namespace Ochr.Meaning
open Ochr

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The callee's frame pushed on `s`, as `Machine.runBodyCore` pushes it: the captures at their
recorded types (`capsState`, as `meanV` reads a closure), `self` (the callee's reading `fres`, at the
reading `.pi cd`), then the parameters, each at its type at the earlier arguments and its declared
reading (`bs`). A borrow parameter is held at the argument's own label: its holder moves from the
caller's temporary to the parameter (`pushBindShaped`), where the closure's meaning issues a fresh
label and a cell. -/
noncomputable def callFrame (cs : List Value) (rd : List (DeclInfo × Value)) (fres : Res) (cd : DeclInfo)
    (bs : List PBind) (args : List Res) (s : SState) : SState :=
  let s := (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd)).foldl SState.pushBind s.pushFrame
  let s := s.pushBind { ty := { fres.2 with label := none }, val := fun _ => fres.1, decl := .pi cd }
  let step (sa : SState × List Sem) (a : Res) : SState × List Sem :=
    let (s, acc) := sa
    let T : TyS := match bs[acc.length]? with | some b => b.1 acc | none => .plain TyM.err
    let d : DeclInfo := match bs[acc.length]? with | some b => b.2 | none => .other
    (pushBindShaped s { ty := { T with label := a.2.label }, val := fun _ => a.1, decl := d }, acc ++ [a.1])
  (args.foldl step (s, [])).1

/-- The frame's pop after the body (`Machine.runBodyCore`'s `popFrame`): every live borrow held in
the callee's frame or made by the body ends, but the returned one (`keep`), in label order as the
closure's meaning ends them (`bodyAt`); the frame goes, and the returned borrow's holder moves to a
temporary of the caller's frame. -/
noncomputable def popCallFrame (start : Nat) (keep : Option Nat) (s : SState) : SState :=
  let top := s.topIdx
  let inTop (l : Nat) : Bool := match s.holderOf l with
    | some (.bind f _) | some (.temp f _) => f == top
    | none => false
  let s₁ := (s.liveLabels.filter fun l => (decide (start ≤ l) || inTop l) && decide (some l ≠ keep)).foldl SState.endLabel s
  let held : Option (Nat × SVal) := keep.bind fun k => (s₁.holderOf k).map fun p => (k, s₁.valAt p)
  let s₂ : SState := { s₁ with env := s₁.env.dropLast, shape := fun p => match p with
    | .bind f _ | .temp f _ => if f = top then none else s₁.shape p }
  match held with
  | some (k, v) => s₂.pushTempShaped v k
  | none => s₂

/-- **The reference's run of a known callee's body in place** (the checker's `runBody`): the frame
pushed (`callFrame`), the body run in tail position at the codomain the code reaches at the
arguments (the `.fix` clause's hint, `fixCod`), the frame popped (`popCallFrame`). The parameters'
binders and the codomain are read in the callee's frame of captures, as the `.fix` clause reads them
in the closure's (`bindsOf`, `codOf`). -/
noncomputable def runBodyRef (fres : Res) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (args : List Res) : SM Res := fun s =>
  match t with
  | .fix _ _ ds c _ body =>
    let s₀ := (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd)).foldl SState.pushBind s.pushFrame
    let bs := bindsOf K ρ φ s₀ ds
    let out := codOf K ρ φ s₀ bs c
    let cd := K.D.typeDecl (K.D.teleDecls (scopeOf s₀) ds) c
    let start := s.nextLoan
    match runT K ρ φ true (.plain (out.cod (args.map (·.1)))) body (callFrame K ρ φ cs rd fres cd bs args s) with
    | some ((r, R), s₁) =>
      let keep : Option Nat := if out.isRef then R.label else none
      some ((r, { R with label := keep }), popCallFrame start keep s₁)
    | none => none
  | _ => none

/-- The run in place with the result's lending as the checker's `callFn` finishes it (static ends,
rule 1: `lendEnv (.ended g [k])`): a returned borrow is lent, as fills, every place it was lent at
(the places its borrow arguments lent), as `callOf` sets it (`setLent k lentK`). -/
noncomputable def runCallRef (fres : Res) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (args : List Res) : SM Res := fun s =>
  (runBodyRef K ρ φ fres cs t rd args s).map fun (r, s') =>
    (r, match r.2.label with
      | some k => s'.setLent k ((s'.lent k).map fun x => { x with fill := true })
      | none => s')

end

end Ochr.Meaning
