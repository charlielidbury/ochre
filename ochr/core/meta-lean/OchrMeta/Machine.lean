import OchrMeta.Measure

/-! # The machine: `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩`, stuck, or an error

One deterministic machine for concrete and symbolic runs (P1).  It is presented as a *clocked
functional big-step semantics*: `exec P n s t` runs `t` with fuel `n`; `Eval P s t r` holds when
some fuel produces the (non-`oof`) result `r`.  Each clause of `exec` is one rule of RULES §3. -/

namespace OchrMeta

/-- [Access]: end every live loan on the path to the place (as a head), and, when `deep`
(read, borrow, assign), every live loan anywhere inside its content; return the content.
Terminates because each [End] removes a `borrow` constructor. -/
def access (deep : Bool) (x : Var) (π : List Proj) (s : St) : Res :=
  match s.lookup x with
  | none => .err
  | some v => match walk s.live deep v π with
    | .found l => match h : endBorrow l s with
      | none => .err
      | some s' => access deep x π s'
    | .done c => .ok s c
    | .stuck => .stuck
    | .err => .err
termination_by s.env.nb
decreasing_by exact endBorrow_nb_lt h

/-- Overwrite the content of a place (whose path has no live loan left). -/
def St.setPlace (x : Var) (π : List Proj) (v : Val) (s : St) : Option St :=
  (s.lookup x).bind fun c => (c.set π v).map fun c' => s.setVar x c'

/-- Does `v` contain a loan whose borrow is held in `s` or is the top-level borrow `extra`
(the value in flight, e.g. the result a frame pop is returning)? -/
def hasLive (s : St) (extra v : Val) : Bool :=
  (v.firstLive fun l => s.live l || extra.isBorrowOf l).isSome

/-- [Drop] a value: a borrow ends; a live loan in a dropped owned value is an error. -/
def dropVal (extra : Val) (v : Val) (s : St) : Option St :=
  match v with
  | .borrow l w => endWith l w s
  | _ => if hasLive s extra v then none else some s

/-- Drop the bindings of the top frame one at a time (most recent first, the rest of the frame
still visible), then remove the frame.  `extra` is the value being returned. -/
def popFrameN (extra : Val) : Nat → St → Option St
  | 0, s => match s.env with
    | [] :: Ω => some { s with env := Ω }
    | _ => none
  | n+1, s => match s.env with
    | ((_, c) :: F) :: Ω => (dropVal extra c { s with env := F :: Ω }).bind (popFrameN extra n)
    | _ => none

def popFrame (extra : Val) (s : St) : Option St :=
  popFrameN extra ((s.env.head?.map List.length).getD 0) s

/-- Evaluate call arguments left to right, each into the temporary `tmp i` of the current frame
(so that [Access] sees arguments in flight). -/
def execArgs (ev : St → Term → Res) : Nat → St → List Term → Res
  | _, s, [] => .ok s .unit
  | i, s, a :: as => (ev s a).bind fun s v => execArgs ev (i + 1) (s.bind (.tmp i) v) as

/-- Move the temporaries `tmp i`, `i ∈ is`, out of the current frame. -/
def takeTemps : List Nat → St → Option (List Val × St)
  | [], s => some ([], s)
  | i :: is, s => (s.unbind (.tmp i)).bind fun (v, s) =>
      (takeTemps is s).map fun (vs, s) => (v :: vs, s)

/-- Split the arguments of a call for [Close]: the tuple of the sealed program's `L` (contents
`uᵢ` at borrow positions, values elsewhere) and the loans `ℓᵢ` of the borrow arguments, with
their positions. -/
def sealArgs : Nat → List (Var × Ty) → List Val → Option (List Val × List (Nat × Nat))
  | _, [], [] => some ([], [])
  | i, (_, .ref _) :: ps, .borrow l u :: ws =>
      (sealArgs (i + 1) ps ws).map fun (as, ls) => (u :: as, (i, l) :: ls)
  | _, (_, .ref _) :: _, _ :: _ => none
  | i, (_, _) :: ps, w :: ws => (sealArgs (i + 1) ps ws).map fun (as, ls) => (w :: as, ls)
  | _, _, _ => none

/-- Substitute each `loan_ℓᵢ` by its fill. -/
def fillLoans : List (Nat × Val) → St → Option St
  | [], s => some s
  | (l, w) :: fs, s => (endWith l w s).bind (fillLoans fs)

/-- [Close] the call `f(w̄)` whose body is stuck (or whose head is opaque), from the call point
`s` (arguments evaluated and moved out of their temporaries). -/
def closeCall (f : String) (d : FunDef) (ws : List Val) (s : St) : Res :=
  match sealArgs 0 d.params ws with
  | none => .err
  | some (as, ls) =>
    let args := Val.ofList as
    -- no borrows inside data: a sealed program's `L` binds borrow-free values
    if args.nb ≠ 0 then .err else
    match d.ret with
    | .ref _ =>
      -- a returned borrow must point into a borrow argument (else its loan occurs nowhere)
      if ls = [] then .err else
      let k := s.next
      let s1 := { s with next := s.next + 1 }
      match fillLoans (ls.map fun (i, l) => (l, .sealed f args (.back i) (.loan k))) s1 with
      | none => .err
      | some s2 => .ok s2 (.borrow k (.sealed f args .cur .unit))
    | .unit =>
      match fillLoans (ls.map fun (i, l) => (l, .sealed f args (.fin i) .unit)) s with
      | none => .err
      | some s2 => .ok s2 .unit
    | _ =>
      match fillLoans (ls.map fun (i, l) => (l, .sealed f args (.fin i) .unit)) s with
      | none => .err
      | some s2 => .ok s2 (.sealed f args .res .unit)

/-- The frame pushed by [Call]. -/
def paramFrame (d : FunDef) (ws : List Val) : Frame := (d.params.map Prod.fst).zip ws

/-- [Call] after the arguments: push the frame, run the body, pop; [Close] if the body is
stuck (unless `canClose = false`, the head call of a sealed program being re-run). -/
def callWith (run : St → Term → Res) (canClose : Bool) (f : String) (d : FunDef)
    (ws : List Val) (s : St) : Res :=
  match d.body with
  | none => if canClose then closeCall f d ws s else .stuck
  | some b =>
    if ws.length = d.params.length then
      match run (s.push (paramFrame d ws)) b with
      | .ok s' v => match popFrame v s' with
        | none => .err
        | some s'' => .ok s'' v
      | .stuck => if canClose then closeCall f d ws s else .stuck
      | .err => .err
      | .oof => .oof
    else .err

/-- The machine, clocked. -/
def exec (P : Prog) : Nat → St → Term → Res
  | 0, _, _ => .oof
  | n + 1, s, t =>
    match t with
    -- [Read]: borrow-free content is copied, a borrow is moved out (`p ↦ ⊥`), `⊥` is an error
    | .read p => (access true p.root p.path s).bind fun s c =>
        match c with
        | .moved => .err
        | .borrow l w => match s.setPlace p.root p.path .moved with
          | none => .err
          | some s => .ok s (.borrow l w)
        | c => .ok s c
    -- [Borrow]
    | .borrow p => (access true p.root p.path s).bind fun s c =>
        if c = .moved ∨ c.nb ≠ 0 then .err else
        match s.setPlace p.root p.path (.loan s.next) with
        | none => .err
        | some s' => .ok { s' with next := s.next + 1 } (.borrow s.next c)
    -- [Assign]: evaluate, access, overwrite, drop the old content
    | .assign p t => (exec P n s t).bind fun s v =>
        (access true p.root p.path s).bind fun s c =>
          -- no borrows inside data: only a variable may receive a borrow
          if p.path ≠ [] ∧ v.nb ≠ 0 then .err else
          match s.setPlace p.root p.path v with
          | none => .err
          | some s => match dropVal .unit c s with
            | none => .err
            | some s => .ok s .unit
    -- [Let]
    | .letIn x t u => (exec P n s t).bind fun s v =>
        (exec P n (s.bind x v) u).bind fun s w =>
          match s.unbind x with
          | none => .err
          | some (c, s) => match dropVal w c s with
            | none => .err
            | some s => .ok s w
    | .seq t u => (exec P n s t).bind fun s v =>
        match dropVal .unit v s with
        | none => .err
        | some s => exec P n s u
    | .zero => .ok s .zero
    | .unit => .ok s .unit
    -- constructors: no borrows inside data (RULES §1 scope), checked dynamically
    | .succ t => (exec P n s t).bind fun s v => if v.nb = 0 then .ok s (.succ v) else .err
    | .pair t u => (exec P n s t).bind fun s v => (exec P n s u).bind fun s w =>
        if v.nb = 0 ∧ w.nb = 0 then .ok s (.pair v w) else .err
    -- [Match]: `Z` → first arm; `S _` → second arm with `y := p.1`; a neutral → stuck
    | .mtch p tz y ts => (access false p.root p.path s).bind fun s c =>
        match c with
        | .zero => exec P n s tz
        | .succ _ => exec P n s (ts.substVar y (.fst p))
        | c => if c.isNeutral then .stuck else .err
    -- [Call]; a call at a proposition is erased (P2: it runs on a private copy, argument
    -- evaluation included, so it leaves the state unchanged and returns `⋆`)
    | .call f args cc => match P.find f with
      | none => .err
      | some d =>
        if d.ret = .prop then .ok s .star else
        (execArgs (exec P n) 0 s args).bind fun s _ =>
          match takeTemps (List.range args.length) s with
          | none => .err
          | some (ws, s) => callWith (exec P n) cc f d ws s
    -- a Prop-typed block (P2)
    | .erase _ => .ok s .star

/-- `Eval P s t r`: the run of `t` from `s` terminates with result `r`. -/
def Eval (P : Prog) (s : St) (t : Term) (r : Res) : Prop :=
  r ≠ .oof ∧ ∃ n, exec P n s t = r

end OchrMeta
