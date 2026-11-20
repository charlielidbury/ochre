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

/-- D99's renaming of a returned borrow `k` into the label `g` the call reserved: the holder of `k`
holds `g` instead, every meaning reads `g`'s final content where it read `k`'s, and `g` takes `k`'s
record and held type; `k` is gone, and so are its sites (`g` was lent before the body ran). -/
noncomputable def SState.endInto (s : SState) (k g : Nat) : SState :=
  { (s.mapVals fun _ v φ' => v (φ'.upd k (φ' g))) with
    shape := fun p => if s.shape p = some k then some g else s.shape p,
    lent := fun m => if m = k then [] else s.lent m,
    heldMem := fun m => if m = g then s.heldMem k else s.heldMem m,
    heldTy := fun m => if m = g then s.heldTy k else s.heldTy m }

/-- **The call in place, as the checker's `callFn` makes it** (static ends, rule 1, [Lend]; main's D99).
For a callee whose codomain is a borrow, the call first reserves the result's label `g` and lends it,
as fills, at every place a borrow argument was lent (the checker's marks `lent_g`), whatever the body
returns it from (`Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a` lends its result at `b`'s lender too,
docs/31 D69, `Regress/ReturnParam.lean`); then the body runs in place; then the borrow the body
returned, whichever it is (a reborrow made in the body, or a borrow argument itself, `IdP(x) := x`),
is renamed into `g` (`endInto`), so the result is always the fresh `g`, as when the call closes off
and as `callOf` gives it. As first written the result kept the body's label (an argument's, for
`IdP`), which no renaming agreeing before the call relates to `callOf`'s (D69); and it kept the sites
the pop gave it, missing `b`'s lender for `Pick2`. -/
noncomputable def runCallRef (fres : Res) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (args : List Res) : SM Res := fun s =>
  let lentK := ((args.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true }
  match t with
  | .fix _ _ _ (.ref _) _ _ =>
    let (g, s₁) := s.freshLoan
    (runBodyRef K ρ φ fres cs t rd args (s₁.setLent g lentK)).map fun (r, s') =>
      match r.2.label with
      | some k => ((r.1, { r.2 with label := some g }), s'.endInto k g)
      | none => (r, s')
  | _ => runBodyRef K ρ φ fres cs t rd args s

end

end Ochr.Meaning
