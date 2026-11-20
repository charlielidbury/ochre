import Ochr.Meaning.ApplyMem

/-!
# The strict reference run (prototype; docs/31 D83 route (C) with extension (C1))

A copy of `Run.lean`'s mutual block (`runT` and its helpers, `meanV` and its helpers), renamed with
an `S` suffix, with these changes and no others (each marked `STRICT` or `C1` at its site):

* `SM.strictS`: a clause FAILS unless its result is a member of the type it gives it. Used at
  `.ascribe`, `.succ`, `.ctor` (around `ctorOut`), `.val` at a constructor value, and `.fix` (the
  closure: a member of its function type, or `err`, `closureL_mem`; strict, the run fails on `err`).
* `.call`: applies `callOfS` (`callOf` with `moved`, not `err`, where a returned borrow's final
  content does not decode: a REPAIR, see `callOfLS`), and fails unless each borrow argument's label holds the content type of the parameter it is
  passed at (`BorrowArgsTyped`: a borrow is invariant; the callee's final content, a member of the
  parameter's type, becomes the lender's).
* `.assign`: fails unless the value written is a member of the place's type at the write.
* `SM.erasedS` (C1) replaces `SM.erasedS`/`SM.erasedAt`: a proof is RUN, on a copy, strictly, and is
  `⋆` at the type its clause gives it, only if that type is a proposition (level 0). A statement is
  unchanged (`SM.stmtIf`).
* `cong`, `symm`, `trans`, `rewrite`, `rewriteR` (the orchestrator's decision 1): their premise proofs
  run, each on a copy, and must succeed; the result is `⋆` at `prop True`. A level-0 code is fixed
  by its truth, so a proof that runs has THE true proposition as its type, whatever the checker calls
  it; that the checker's conclusion means `prop True` is the simulation's (from the premises'
  agreement and congruence of meanings).
* A result carrying a borrow label is typed at the label's content type (`labTyOk`): tested at an
  ascription and an assignment (the checker's conversion of the two types supplies it).
* A constructor with written parameters fails unless they are members of their types (`paramsOk`).
* `&A` is strict at `Type₀` (`&A` is well formed iff `A : Type₀`); a borrow `&p` is strict at the
  place's type (its record, `heldMem`, is then a member).

Everything outside the block (`contentOf`, `assignAt`, `callOf`, `ctorOut`, the drops, the stage
machinery) is `Run.lean`'s, unchanged.
-/

namespace Ochr.Meaning

open Classical

/-- STRICT (D83): fail unless the result is a member of the type it is given. -/
noncomputable def SM.strictS (R : DataRead) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  match x s with
  | some (r, s') => if r.1 ∈ₛ[R] r.2.m then some (r, s') else none
  | none => none

/-- C1: an erased term. A proof (`fl.2`) is run on a copy, strictly, and is `⋆` at the type its
clause gives it when its value is `⋆` and that type is a proposition (level `0`); a statement
(`fl.1`) runs on a copy as before. Both tests are computable (`Sem.isProof`, `TyM.level` match on
constructors), so a concrete run still reduces. -/
noncomputable def SM.erasedS (fl : Bool × Bool) (x : SM (Sem × TyS)) : SM (Sem × TyS) := fun s =>
  if fl.2 then
    match x s with
    | some ((v, T), _) => if v.isProof = true ∧ T.m.level = some 0 then some ((.proof, .plain T.m), s) else none
    | none => none
  else SM.stmtIf fl.1 x s

/-- A result's label, if any, has the given content type in the state. -/
def labTyOk (s : SState) (lab : Option Nat) (T : TyM) : Prop := ∀ l, lab = some l → s.heldTy l = T

/-- Written constructor parameters are members of their declared types at the earlier ones. -/
def paramsOk (dm : DataModel) (d : IndDecl) (ps : List Sem) : Prop :=
  ∀ i v, ps[i]? = some v → v ∈ₛ[dm.read] dm.paramTy d i (ps.take i)

/-- The borrow flags of a function type's parameters along the arguments (`telRefsL` at its level). -/
noncomputable def refsOf (R : DataRead) (T : TyM) (as : List Sem) : List Bool :=
  match T with
  | .t0 _ (.pi _ t) => telRefsL (lvl0 R) t as
  | .t1 _ (.pi _ t) => telRefsL (lvl1 R) t as
  | .t2 _ (.pi _ t) => telRefsL (lvl2 R) t as
  | _ => []

/-- The content types of a function type's borrow parameters along the arguments (`telRefTysL`). -/
noncomputable def refTysOf (R : DataRead) (T : TyM) (as : List Sem) : List TyM :=
  match T with
  | .t0 _ (.pi _ t) => telRefTysL (lvl0 R) t as
  | .t1 _ (.pi _ t) => telRefTysL (lvl1 R) t as
  | .t2 _ (.pi _ t) => telRefTysL (lvl2 R) t as
  | _ => []

/-- The labels of the arguments at borrow parameters, in parameter order (`callOfL`'s `refLabels`). -/
noncomputable def refLabelsOf (R : DataRead) (fv : Res) (args : List Res) : List (Option Nat) :=
  ((args.zip (refsOf R fv.2.m (args.map (·.1)))).filter (·.2)).map (·.1.2.label)

/-- STRICT at a call: each borrow argument's label holds the content type of the parameter it is
passed at (a borrow is invariant: the callee's final content, a member of the parameter's type,
becomes what the lender reads). -/
def BorrowArgsTyped (R : DataRead) (fv : Res) (args : List Res) (s : SState) : Prop :=
  ∀ (i l : Nat), (refLabelsOf R fv args)[i]? = some (some l) →
    s.heldTy l = (refTysOf R fv.2.m (args.map (·.1))).getD i TyM.err

/-- `callOfL` with one change (REPAIR, prototype): where the final content of a returned borrow does not
decode (a partly moved content, D53 (h)), the consumed argument labels are fixed to `moved` rather than
`err`. A lender then reads its part moved, a partly moved member, where `err` is no member of
anything; at futures giving the returned borrow a whole member nothing changes. -/
noncomputable def callOfLS.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args : List Res) :
    SM Res := fun s =>
  let argSems := args.map (·.1)
  let refLabels : List (Option Nat) := ((args.zip (telRefsL L t argSems)).filter (·.2)).map (·.1.2.label)
  let fixes (fs : List Sem) : List (Nat × Sem) := (refLabels.zip fs).filterMap fun (l?, f) => l?.map (·, f)
  let s := (refLabels.filterMap id).foldl SState.takeLabel s
  match applyFnL L t fv argSems with
  | some (.data r T finals) =>
    let s := s.mapVals fun _ v φ' => v (φ'.updList (fixes finals))
    some ((r, .plain T), s)
  | some (.ref _ c fwd back) =>
    let (k, s) := s.freshLoan
    let lentK := ((refLabels.filterMap id).flatMap s.lent).map fun x : Site => { x with fill := true }
    let s := s.mapVals fun _ v φ' =>
      match L.dec c (φ' k) with
      | some x => v (φ'.updList (fixes (back x)))
      | none => v (φ'.updList (fixes (refLabels.map fun _ => .moved)))
    let s := s.pushTempShaped (fun _ => L.enc c fwd) k
    some ((L.enc c fwd, ⟨L.toTy c, some k⟩), ((s.setLent k lentK).setHeldTy k (L.toTy c)).setHeldMem k (L.enc c fwd))
  | none => none

/-- `callOf` through `callOfLS`. -/
noncomputable def callOfS (R : DataRead) (fv : Res) (args : List Res) : SM Res := fun s =>
  match fv.2.m with
  | .t0 _ (.pi _ t) => callOfLS (lvl0 R) t fv.1 args s
  | .t1 _ (.pi _ t) => callOfLS (lvl1 R) t fv.1 args s
  | .t2 _ (.pi _ t) => callOfLS (lvl2 R) t fv.1 args s
  | _ => none

/-- STRICT `.val` (D83 row 8): a constructor value must be a member of the type its record names;
any other value is typed as before. Written as a function of the value so that each constructor's
case reduces by `rfl`. -/
noncomputable def strictVal (R : DataRead) : Value → Res → SM Res
  | .ind .., r => SM.strictS R (pure r)
  | _, r => pure r

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

mutual
/-- The reference run of a term at the future `φ`, at the type `hint` its context expects, in
tail position when `tl` (D90's tail flag, docs/31 D29 point 2). A term is in tail position when it
is a function's body (the `.fix` clause's body run), or a tail's `let` body, sequence tail, match
arm, or the one arm of a match on a proof: exactly where the checker's `checkTail` recurses and
its untyped runs carry `MState.tailNext` (`runBody`, `evalCore`'s `.letIn` and `.seq`,
`evalMatch`'s arms, `evalMatchByType`'s one arm). Everything else, `J`'s transported term and a
sealed program's re-run included, is not; a constant's body is run by `eval`, not `checkTail`,
so it is not either. -/
noncomputable def runS (tl : Bool) (hint : TyS) : Term → SM Res
  -- C1: a proof read at a place is read, on a copy, at the place's type
  | .place p => fun s => SM.erasedS (K.D.flags (scopeOf s) (.place p))
      (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s
  -- STRICT: the borrowed content is a member of its type (a borrow's record is a member)
  | .borrow p => fun s => SM.erasedS (K.D.flags (scopeOf s) (.borrow p)) (SM.strictS K.dm.read (borrowPlace K φ p)) s
  | .assign p u => fun s => SM.erasedS (K.D.flags (scopeOf s) (.assign p u)) (fun s => do
    -- the right-hand side runs BEFORE the place is accessed (`evalCore`'s `.assign`, then
    -- `assignPlace`; D19, R5: accessing first ended the borrows the right-hand side reads
    -- through, `y := clone(*r)` with `r` borrowing `y`). The place's type, the hint of the
    -- right-hand side, is read on a discarded copy
    let T : TyS := match contentOf K φ p s with
      | some ((_, T, _, _), _) => T
      | none => .plain .err
    let ((v, R), s) ← runS false T u s
    -- STRICT: the value written is a member of the place's type at the write (read on a
    -- discarded copy, `placeTy`; the hint `T` was read before the right-hand side ran)
    if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
      assignAt K φ p v R.label s else none) s
  | .letIn x u w => fun s => SM.erasedS (K.D.flags (scopeOf s) (.letIn x u w)) (fun s => do
    let ((v, T), s) ← runS false (.plain TyM.err) u s
    let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← runS tl hint w s
    -- [Drop] of the binding: the borrow it holds *now* ends, then it is forgotten (PROPOSAL,
    -- m2-proofs, CE5: not the label its type carried when it was bound, which it may have moved
    -- out, while an assignment may have made it the holder of another)
    let held : Option Nat := match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none
    -- a binding holding no borrow ends the borrows lent at it (D65, `endLoansOfTopBind`: the
    -- non-lexical reading; docs/31 D29: the checker ends them, so the reference must)
    let s := match held with | some l => s.endLabel l | none => letLenders s
    some ((r, R), s.dropLast)) s
  | .seq u w => fun s => SM.erasedS (K.D.flags (scopeOf s) (.seq u w)) (do
    -- [Drop] of a discarded value (`Machine.dropValue`): a borrow it holds ends now, as the
    -- checker ends it (docs/31 D29: the two hold the same live borrows at every point; it used
    -- to stay parked until an access depended on it, an early end of the checker's)
    let r ← runS false (.plain TyM.err) u
    SM.modify (discardEnd r.2)
    runS tl hint w) s
  | .matchNat p z u => fun s => SM.erasedS (K.D.flags (scopeOf s) (.matchNat p z u)) (fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access] for the tag: the
    -- audit's A1); `⊥` is an error; then D84's drop at the join
    let (tg, s) ← tagOf K φ p natTag s
    -- D90 [Entry]: not in tail position, the stuck block's captures are accessed first, and a
    -- borrow-typed match's result is lent what the block's would be (`matchEntry`)
    let (s, lend) := matchEntry K φ (!tl) (.matchNat p z u) s
    let entry := movedPlaces φ s
    match tg.asNat with
    | some 0 => do
      let ((r, R), s) ← runS tl hint z s
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | some (_ + 1) => do
      let ((r, R), s) ← runS tl hint u s
      some ((r, R), lend R.label (joinDrop K φ entry (.matchNat p z u) s))
    | none => none) s
  | .matchInd p n arms => fun s => SM.erasedS (K.D.flags (scopeOf s) (.matchInd p n arms)) (fun s => do
    let (tg, s) ← tagOf K φ p indTag s
    -- D93: a match on a type with one constructor never closes off, so it has no entry and no
    -- join, on any path (`Machine.evalMatchInd`: its one arm runs directly)
    let one := oneCtor K.Γ n
    -- D90 [Entry], not in tail position, not on a proof (`evalMatchByType` has none), and not on a
    -- one-constructor type (D93)
    let (s, lend) := matchEntry K φ (!tl && !tg.isProof && !one) (.matchInd p n arms) s
    let entry := movedPlaces φ s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match tg with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => tg.asNat
    match c? with
    | some c => do
      let ((r, R), s) ← runArmS tl hint c arms s
      -- a match on a proof has no join (`Machine.evalMatchByType`: its one arm runs on every
      -- path; the audit's A4)
      some ((r, R), match tg with
        | .proof => s
        | _ => if one then s else lend R.label (joinDrop K φ entry (.matchInd p n arms) s))
    | none => none) s
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParamsS d 0 [] args
      -- the type value is the declaration's code at the parameters (docs/31 D59)
      pure (.ty (K.dm.tyM d psM), .plain (TyM.univ d.sort))
    | none => SM.fail
  | .ctor ty c x ps args => fun s => SM.erasedS (K.D.flags (scopeOf s) (.ctor ty c x ps args)) (do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParamsS d 0 [] ps
      -- the record known before the fields: the written parameters' (none, for a declaration
      -- without parameters), or the hint's (`evalCtor`'s `sol`; docs/34 §14: a code keeps a
      -- record, not parameters); otherwise the fields' types solve the parameters (`runFieldsS`;
      -- the audit's A9)
      let rh : Option Rec := if !ps.isEmpty || d.params.isEmpty then some (K.dm.recOf d psM) else
        match hint.data with
        | some (n, r) => if n = ty then some r else none
        | none => none
      let sol₀ : List (Option Sem) := if !ps.isEmpty then psM.map some else List.replicate d.params.length none
      -- a constructor of a Prop-sorted inductive is a proof, `⋆` (D42); its arguments are
      -- statement positions, each on its own copy (`stmtArgIf`; D19, R4)
      let (fs, sol) ← runFieldsS (d.sort == 0) d c 0 rh sol₀ [] args
      -- STRICT: the value built is a member of the type it is given (`ctorOut_mem`: fields that fit)
      -- STRICT: written parameters are members of their types
      fun s => if ps.isEmpty ∨ paramsOk K.dm d psM then
        SM.strictS K.dm.read (ctorOut K.dm d c fs (rh <|> (if sol.all (·.isSome) then some (K.dm.recOf d (solved sol)) else none))) s
      else none
    | none => SM.fail) s
  | .const n => pure (K.C.global n)
  | .val v => fun s =>
    -- an embedded value at the type it is, as the checker types it (`valType?`): a number at
    -- `Nat`, `()` at `Unit`, a constructor value at the type its record names (the record its
    -- meaning carries: the written parameters', or the hint's for a bare one), a closure at its
    -- own type (its code, from its term in its captures' frame), an unknown at its type in Δ;
    -- anything else at the hint
    let T : TyS := match v with
      | .zero | .succ _ => .plain TyM.nat
      | .unit => .plain TyM.unit
      | .ind ty _ _ ps _ => match K.Γ.find? (·.name == ty) with
        | some d =>
          let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
              (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
            else some (K.dm.recOf d (meanParamsS d 0 [] ps))
          match r? with
          | some r => .plain (K.dm.tyR d r)
          | none => hint
        | none => hint
      | .clo caps t rd => match runS false (.plain TyM.err) t (stateOf 0 (capsState (capsValsS caps) (capsTysS rd))) with
        | some ((_, R), _) => R
        | none => hint
      | .gfn n => (K.C.global n).2
      | .abs σ => K.Δ σ
      -- P1 (PROPOSAL, m2-proofs): a loan of a function carries its declared type (`K.Λ`), as its
      -- filler will
      | .loan l => if (K.Λ l).m.isPi then K.Λ l else hint
      -- a sealed callee (D39: the checker calls a sealed function value) is typed as its
      -- program's result where that is a function (the spine's finding at the general
      -- closeCall_step, docs/31 item 3); its labels are its own
      | .sealed t => match runS false hint t (emptyState 0) with
        | some ((_, R), _) => if R.m.isPi then R else hint
        | none => hint
      | _ => hint
    -- PROPOSAL (m2-proofs): an embedded value holds no borrow the run made, so its result carries
    -- no label, whatever label the hint (a place's stored type, at an assignment) records
    -- STRICT at a constructor value (D83 row 8): it is a member of the type its record names
    strictVal K.dm.read v (meanS hint v, { T with label := none }) s
  | .sort l => pure (.ty (TyM.univ l), .plain (TyM.univ (sortSucc l)))
  | .pi hs ds c => fun s =>
    -- [T-Pi]: the parameters' and output's meanings as functions of the earlier parameters
    -- (`runBindsS`), the carrier at the declared sort (D55, `Decisions.piSort`)
    let bs := runBindsS s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiCod := match c with
      | .ref U => ⟨true, fun acc => match runS false (.plain TyM.err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
      | c => ⟨false, fun acc => match runS false (.plain TyM.err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    some ((.ty (piTyAt K.dm.read l ps out), .plain (TyM.univ l)), s)
  | .fix self hs ds c dec body => fun s => SM.erasedS (K.D.flags (scopeOf s) (.fix self hs ds c dec body)) (fun s =>
    -- [Closure] (D51, D53, D80): a closure means a function on its annotated domain, read off
    -- the reference run of its body in the forming frame extended by `self` and the parameters
    -- (the body's layout `[caps…, self, x̄]`). A recursive `fix` means its guarded fixpoint by
    -- stages (docs/24 §4): stage 0 is undefined, stage `k + 1` binds `self` to stage `k`'s
    -- closure at the weakened function type (the true codomain at arguments of rank below `k`,
    -- `Unit` above, docs/34), and the function at arguments whose decreasing argument has rank
    -- `r` is stage `r + 1`; so a call that does not decrease reads `()` at `Unit`, and the
    -- closure, built strictly at the true type, is `err` unless the codomain holds it.
    let bs := runBindsS s (K.D.paramDecls (scopeOf s) ds) [] ds
    let ps := psOf bs ds
    let out : PiCod := match c with
      | .ref U => ⟨true, fun acc => match runS false (.plain TyM.err) U (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
      | c => ⟨false, fun acc => match runS false (.plain TyM.err) c (extendBy s bs acc) with
        | some ((v, _), _) => v.asTy
        | none => TyM.err⟩
    -- the codomain, the body's hint (the audit's A8: a body that is a bare `Nil` reads its
    -- parameters off the code)
    let cod : List Sem → TyS := fun acc => .plain (out.cod acc)
    -- the code at the declared sort (D55, D12): `piTyAt`/`closureAt` (`Apply1.lean`)
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    let piT := piTyAt K.dm.read l ps out
    let start := s.nextLoan
    -- the declared readings of the parameters and the codomain (`Decide.paramDecls`): what the
    -- frame binds the parameters at, and `self` (D19, R3: bound at `other`, a parameter of a copy
    -- type was moved by its first read, and a call through `self` or a function parameter was
    -- never classified as a statement or a proof)
    let cd := K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c
    let bodyAt (selfT : TyM) (selfM : Sem) (args : List Sem) : Option BodyOut :=
      -- the frame: `self`, then the parameters. A borrow parameter is set up as the generic call
      -- is ([Def]): a fresh label `lᵢ`, a *cell* (a temporary of the frame: temporaries do not
      -- shift de Bruijn indices) reading `lᵢ`'s final content, and the parameter holding the
      -- content as the borrow's holder (D14). Returning the parameter returns its label.
      let s₁ := s.pushBind { ty := .plain selfT, val := fun _ => selfM, decl := .pi cd }
      -- each parameter is bound at its type (its code) and at its declared reading (`bs`)
      let step (sa : SState × List Sem × List Pos) (ap : Sem × PiDom) : SState × List Sem × List Pos :=
        let (s, acc, cells) := sa
        let T : TyS := match bs[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
        let d : DeclInfo := match bs[acc.length]? with | some b => b.2 | none => .other
        if ap.2.isRef then
          let (l, s) := s.freshLoan
          let s := s.pushTemp fun ψ => ψ l
          let cell : Pos := .temp s.topIdx (((s.env.getLast?).map (·.temps.length)).getD 1 - 1)
          -- the argument is recorded as the label's member (docs/31 D68: where a label is made)
          let s := pushBindShaped (s.setHeldMem l ap.1) { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
          (s, acc ++ [ap.1], cells ++ [cell])
        else
          (s.pushBind { ty := { T with label := none }, val := fun _ => ap.1, decl := d }, acc ++ [ap.1], cells)
      let (s₂, _, cells) := (args.zip ps).foldl step (s₁, [], [])
      match runS true (cod args) body s₂ with
      | some ((r, R), s₃) =>
        -- the frame pop ends the borrows the body made and the parameters' (their cells then
        -- read the holders' contents), except the returned borrow's, whose holder is the
        -- caller's; a borrow parameter's final content is its cell's
        -- PROPOSAL (m2-proofs, 5b): the returned borrow survives only when the codomain is a
        -- borrow; a labelled result at a data codomain (ill-typed) is ended with the rest, else
        -- its cell reads the future at the run's own label in `mkLeafData`
        let keep : Option Nat := if out.isRef then R.label else none
        let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
        let finals := cells.map fun c => s₄.valAt c
        some ⟨r, finals, R.label⟩
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem := closureAt K.dm.read l φ ps out g
    let rankOf (args : List Sem) : Nat := match dec with
      | some j =>
        match args[j]? with
        | some a => semRank a
        | none => 0
      | none => 0
    -- a stage's `self` is the stage below at the weakened function type (docs/34): built
    -- strictly, a stage good only below its bound is an element of that type, not of the true
    -- one (docs/31 D60's fill is gone)
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun k gk => bodyAt (piTyAt K.dm.read l ps (weakCod l rankOf k out))
          (closureAt K.dm.read l φ ps (weakCod l rankOf k out) (stageFn l ps rankOf k gk)))
    let g : List Sem → Option BodyOut := match dec with
      | some _ => fun args => stage (rankOf args + 1) args
      | none => bodyAt piT .err
    -- forming the closure (`Machine.capture`) accesses each captured variable, oldest binding
    -- first, and then moves it unless its declared reading is copy (D80): the checker's [Access]
    -- before the capture ends the borrows lent at it (docs/31 D29 point 2, D37)
    let s' := (capOrder (.fix self hs ds c dec body)).foldl (capStep K) s
    -- STRICT: the closure is a member of its function type (else it is `err`, `closureL_mem`)
    SM.strictS K.dm.read (fun s' => some ((closureOf g, .plain piT), s')) s') s
  | .call f args hd => fun s =>
    let fl := K.D.flags (scopeOf s) (.call f args hd)
    -- a statement call runs on a copy that is thrown away (E1; `Decisions.flags`, aligned), and
    -- its result carries no label (m2-proofs' finding 6): `SM.stmtIf`, as every clause
    -- a proof call is never applied: its value is `⋆` (P5; `Machine.callFn` at class 2), as
    -- every proof's is (`SM.erasedS`)
    SM.erasedS fl (do
      -- a call reads its head in place: it does not consume the function it calls (D53 (e),
      -- `evalCall`'s `inPlace`; D19, R2: `run f` moved a function variable out, so `f(f(n))`
      -- failed)
      let fv ← SM.headOf f (fun p => readPlace K φ p true) (runS false (.plain TyM.err) f)
      -- a statement call's arguments are statement positions, each on its own copy (R4)
      let as ← runArgsS fl.1 fv.2.m [] args
      -- STRICT: a borrow argument's label holds its parameter's content type
      fun s => if BorrowArgsTyped K.dm.read fv as s then callOfS K.dm.read fv as s else none) s
  | .nat => pure (.ty TyM.nat, .plain (TyM.univ 1))
  | .unit => pure (.ty TyM.unit, .plain (TyM.univ 1))
  | .zero => pure (.el0 Nat 0, .plain TyM.nat)
  | .tt => pure (.el0 Unit (), .plain TyM.unit)
  | .succ u => fun s => SM.erasedS (K.D.flags (scopeOf s) (.succ u)) (SM.strictS K.dm.read (do
    let (v, _) ← runS false (.plain TyM.nat) u
    pure (v.succ, .plain TyM.nat))) s
  | .eq A a b => SM.onCopy do
    let (TA, _) ← runS false (.plain TyM.err) A
    let T : TyS := .plain TA.asTy
    let (va, _) ← SM.onCopy (runS false T a)
    let (vb, _) ← SM.onCopy (runS false T b)
    pure (.ty (TyM.prop (va = vb)), .plain (TyM.univ 0))
  -- decision 1: the premise proofs run, each on a copy; `⋆` at `prop True`
  | .cong _ h => SM.onCopy (do
    let _ ← runS false (.plain TyM.err) h
    pure (.proof, .plain (TyM.prop True)))
  | .prim "symm" [h] => SM.onCopy (do
    let _ ← runS false (.plain TyM.err) h
    pure (.proof, .plain (TyM.prop True)))
  | .prim "trans" [h, k] => SM.onCopy (do
    let _ ← runS false (.plain TyM.err) h
    let _ ← runS false (.plain TyM.err) k
    pure (.proof, .plain (TyM.prop True)))
  | .prim "rewrite" [h, u] => SM.onCopy (do
    let _ ← runS false (.plain TyM.err) h
    let _ ← runS false (.plain TyM.err) u
    pure (.proof, .plain (TyM.prop True)))
  | .prim "rewriteR" [h, u] => SM.onCopy (do
    let _ ← runS false (.plain TyM.err) h
    let _ ← runS false (.plain TyM.err) u
    pure (.proof, .plain (TyM.prop True)))
  -- STRICT: `&A` is well formed iff `A : Type₀`
  | .ref A => fun s => SM.erasedS (K.D.flags (scopeOf s) (.ref A)) (SM.strictS K.dm.read (do
    let (TA, _) ← runS false (.plain TyM.err) A
    pure (TA, .plain (TyM.univ 1)))) s
  | .id A t u => fun s => do
    -- `Id` observes: each side on a copy of the state, a fresh value written through each
    -- re-pointed borrow binding ([Obs-ref]), every borrow ended, the result and every position
    -- compared (D84: moved places are definite values, so they compare too); the proposition
    -- holds for every choice of the written values among the members of the borrowed types
    let ((TA, _), _) ← SM.onCopy (runS false (.plain TyM.err) A) s
    let T : TyS := .plain TA.asTy
    let reps := K.D.rePointed (scopeOf s) t
    let o₁ ← runS false T t s
    let o₂ ← runS false T u s
    some ((.ty (TyM.prop (∀ ws : List Sem, obsTyped K.dm.read reps ws s →
      observation φ reps ws s.positions o₁.1 o₁.2 = observation φ reps ws s.positions o₂.1 o₂.2)), .plain (TyM.univ 0)), s)
  | .prim "J" [A, a, b, P, h, t] => fun s => SM.erasedS (K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, h, t])) (do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (runS false (.plain TyM.err) A)
    let _ ← SM.onCopy (runS false (.plain TyM.err) a)
    let _ ← SM.onCopy (runS false (.plain TyM.err) b)
    let _ ← SM.onCopy (runS false (.plain TyM.err) P)
    let _ ← SM.onCopy (runS false (.plain TyM.err) h)
    -- D90 [Entry]: `J` computes, so its transported term's stuck block's captures are accessed
    -- first; then the term runs as the one arm of D84's join (`Machine.evalCore`'s `J`)
    fun s =>
      let s := (matchEntry K φ true t s).1
      let entry := movedPlaces φ s
      match runS false hint t s with
      | some ((r, R), s) => some ((r, R), joinDrop K φ entry (.prim "J" [A, a, b, P, h, t]) s)
      | none => none) s
  -- `clone`, `peek` and `inplace` of a place read it in place: not consumed (`inplace` is a stuck
  -- block's read-only capture; it used to be `run hint u`, a move: D19)
  | .prim "clone" [u] => fun s => SM.erasedS (K.D.flags (scopeOf s) (.prim "clone" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runS false hint u)) s
  | .prim "peek" [u] => fun s => SM.erasedS (K.D.flags (scopeOf s) (.prim "peek" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runS false hint u)) s
  | .prim "inplace" [u] => fun s => SM.erasedS (K.D.flags (scopeOf s) (.prim "inplace" [u]))
      (SM.headOf u (fun p => readPlace K φ p true) (runS false hint u)) s
  | .prim _ _ => SM.fail
  -- STRICT: the term's value is a member of the annotation
  | .ascribe u A => fun s => SM.erasedS (K.D.flags (scopeOf s) (.ascribe u A)) (SM.strictS K.dm.read <| do
    -- the annotation is the term's type, its code (the audit's A7: an annotated function is
    -- called along it, an annotated bare constructor reads its parameters off it)
    let (TA, _) ← SM.onCopy (runS false (.plain TyM.err) A)
    let T : TyS := .plain TA.asTy
    let (v, R) ← runS false T u
    fun s => if labTyOk s R.label T.m then some ((v, { T with label := R.label }), s) else none) s
termination_by structural t => t

/-- Arm `c` of a match, run at the match's expected type. -/
noncomputable def runArmS (tl : Bool) (hint : TyS) (c : Nat) : List (Hint × Term) → SM Res
  | [] => SM.fail
  | (_, t) :: rest => if c = 0 then runS tl hint t else runArmS tl hint (c - 1) rest
termination_by structural arms => arms

/-- The parameters of a Π-term as a frame binds them (`PBind`): each domain term run in the
forming state extended by the earlier parameters at THEIR types and readings (`pre`), giving the
parameter's type with its Π-shape (the run of a Π-term returns the Π's shape in its result type)
as a function of the earlier arguments; `dcs` are the telescope's declared readings. For `&A` the
content type `A` is run. (D19, R6; `psOf` reads the telescope's description off the result.) -/
noncomputable def runBindsS (s : SState) (dcs : List DeclInfo) (pre : List PBind) : List Term → List PBind
  | [] => []
  | .ref A :: ds =>
    mkBind dcs pre (fun acc => runS false (.plain TyM.err) A (extendBy s pre acc)) ::
      runBindsS s dcs (pre ++ [mkBind dcs pre (fun acc => runS false (.plain TyM.err) A (extendBy s pre acc))]) ds
  | d :: ds =>
    mkBind dcs pre (fun acc => runS false (.plain TyM.err) d (extendBy s pre acc)) ::
      runBindsS s dcs (pre ++ [mkBind dcs pre (fun acc => runS false (.plain TyM.err) d (extendBy s pre acc))]) ds
termination_by structural ds => ds

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParamsS (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← SM.onCopy (runS false (.plain (K.dm.paramTy d i earlier)) a)
    let rest ← runParamsS d (i + 1) (earlier ++ [v]) as
    pure (v :: rest)
termination_by structural as => as

/-- A constructor's fields, each at its field type at the earlier fields. With `stmt` (a proof
constructor's, D42) each field is a statement position, on its own copy (`stmtArgIf`), unless its
declared type is a borrow type (`Decide.stmtArgInPlace`, read through `Decisions.declOf`).

`sol` is the parameters solved so far (`Machine.evalCtor`'s `sol`): the written ones or the
hint's, then what each field's type gives the unsolved ones (`unifyTyS`; the audit's A9: before,
an unannotated `Pair(a, b)` or `Cons(x, xs)` with no hint had no parameters and failed). A field
is run at its declared type as hint once every parameter that type reads is solved
(`Machine.fieldTypeAt`'s guard), and at no hint before. -/
noncomputable def runFieldsS (stmt : Bool) (d : IndDecl) (c i : Nat) (rh : Option Rec) (sol : List (Option Sem))
    (earlier : List Sem) : List Term → SM (List Sem × List (Option Sem))
  | [] => pure ([], sol)
  | a :: as => fun s => (do
    let T : TyS := match rh with
      | some r => .plain (K.dm.fieldTyR d r c i earlier)
      | none => match fieldTerm d c i with
        | some FT =>
          if FT.freeVars.all (fun j => d.params.length ≤ j || (sol.getD (d.params.length - 1 - j) none).isSome) then
            .plain (K.dm.fieldTy d (solved sol) c i earlier)
          else .plain TyM.err
        | none => .plain TyM.err
    let (v, R) ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (runS false T a)
    let sol₁ := match fieldTerm d c i with
      | some FT => unifyTyS K.dm d.params.length FT R sol
      | none => sol
    let (rest, sol₂) ← runFieldsS stmt d c (i + 1) rh sol₁ (earlier ++ [v]) as
    pure (v :: rest, sol₂)) s
termination_by structural as => as

/-- A call's arguments, each at its parameter type read off the callee's type code at the earlier
arguments (D82, [Call-type]). With `stmt` (a statement call's) each argument is a statement
position, on its own copy (`stmtArgIf`; D19, R4: in sequence on the call's one copy, `Lem(x, x)`
found `x` moved), unless its declared type is a borrow type, which runs in place
(`Decide.stmtArgInPlace`). -/
noncomputable def runArgsS (stmt : Bool) (fT : TyM) (earlier : List Sem) : List Term → SM (List Res)
  | [] => pure []
  | a :: as => fun s => (do
    let T : TyS := .plain (fT.domAfter K.dm.read earlier)
    let r ← SM.stmtIf (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) (runS false T a)
    let rest ← runArgsS stmt fT (earlier ++ [r.1]) as
    pure (r :: rest)) s
termination_by structural as => as

/-- The meaning of a value, with the code-dependent forms given by the run itself (the knot of
`Value.mean`'s `CodeMeaning`): a sealed program is its program run from the empty state (the
label counter above its loans) at the hint; a closure or Π-closure is its term run in a frame
holding its captures at their recorded types (D51); a global is `K.C.global`. The other clauses
are `Value.mean`'s (`meanV_eq_mean`). -/
noncomputable def meanS (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (meanS (.plain TyM.nat) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (K.C.global n).1
  | .clo caps t rd => match runS false (.plain TyM.err) t (stateOf 0 (capsState (capsValsS caps) (capsTysS rd))) with
    | some ((v, _), _) => v
    | none => .err
  | .borrow _ w => meanS hint w
  | .gloan _ w => meanS hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  -- PROPOSAL (m2-proofs, 8): a sealed program runs from the label counter 0, not from above its
  -- loans. Its fresh labels never leave its run (only the result's meaning and shape are read),
  -- and meeting one of its loans is harmless (a loan is read by the value's meaning, never through
  -- the state). A counter fixed by the term changes under substitution, which then needs the
  -- counter's independence (the renaming lemma, false as first stated: finding 7)
  | .sealed t => match runS false hint t (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err
  | .proof => .proof
  | .tNat => .ty TyM.nat
  | .tUnit => .ty TyM.unit
  | .tEq A a b =>
    let T := TyS.plain (meanS (.plain TyM.err) A).asTy
    .ty (TyM.prop (meanS T a = meanS T b))
  | .tRef A => meanS (.plain TyM.err) A
  | .tPi caps t rd => match runS false (.plain TyM.err) t (stateOf 0 (capsState (capsValsS caps) (capsTysS rd))) with
    | some ((v, _), _) => .ty v.asTy
    | none => .ty TyM.err
  | .sort l => .ty (TyM.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
        else some (K.dm.recOf d (meanParamsS d 0 [] ps))
      match r? with
      | some r => if d.sort == 0 then .proof else DataModel.ctorR d r c (meanFieldsS d r c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => .ty (K.dm.tyM d (meanParamsS d 0 [] args))
    | none => .ty TyM.err
termination_by structural v => v

noncomputable def meanFieldsS (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanS (.plain (K.dm.fieldTyR d r c i earlier)) v
    s :: meanFieldsS d r c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

noncomputable def meanParamsS (d : IndDecl) (i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanS (.plain (K.dm.paramTy d i earlier)) v
    s :: meanParamsS d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- A closure's or Π-closure's captured values, each read as a value (D51). -/
noncomputable def capsValsS : List Value → List Sem
  | [] => []
  | v :: vs => meanS (.plain TyM.err) v :: capsValsS vs
termination_by structural vs => vs

/-- The captures' recorded declared types, each read as a type (D82; a type is future-free): its
code, with its whole structure (the audit's A10: a call through a captured function runs along
it). -/
noncomputable def capsTysS : List (DeclInfo × Value) → List (DeclInfo × TyS)
  | [] => []
  | (d, T) :: rest => (d, .plain (meanS (.plain TyM.err) T).asTy) :: capsTysS rest
termination_by structural rest => rest
end

end

end Ochr.Meaning
