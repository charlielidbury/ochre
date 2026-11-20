import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

open Ochr.Test

ochr EntryCheck uses Nats {
  reject def NT (a : Nat) : Unit := (let r = &a; let k = S(Z); match k { Z => (a := 1; ()), S _ => () }; *r := 2; ())
  def NTOk (a : Nat) : Unit := (let r = &a; let k = S(Z); *r := 2; match k { Z => (a := 1; ()), S _ => () }; ())
  def NTTail (a : Nat) : Unit := (let r = &a; let k = S(Z); *r := 2; match k { Z => (a := 1; ()), S _ => (*r := 3; ()) })
}

#guard_msgs (drop warning) in
ochr EntryCheckAt uses Nats {
  def NTAt (a : Nat) : Unit := (let r = &a; let k = S(Z); ?)
}

namespace Ochr.Meaning.Regress.EntryCheck
open Ochr Ochr.Meaning

/-- The checker's whole state at the hole of `name`, on entry (recorded by `Config.recordStates`:
the last located term entered is the hole). -/
def stAt (name : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) "EntryCheckAt" EntryCheckAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- `NT`'s body, resolved as the checker resolves it (`runWith`: the library, then the block). -/
def ntBody : Option Term :=
  let p := libOf {} 2000000 EntryCheck ++ EntryCheck.decls
  match p.find? (fun d => d.name == "NT") with
  | some d => match (Ochr.Surface.runResolve p d 2000000 false).1 with
    | .ok (.ok (.defn df)) => some df.body
    | _ => none
  | none => none

def ntMatch : Option Term := match ntBody with
  | some (.letIn _ _ (.letIn _ _ (.seq m _))) => some m
  | _ => none

def stNT : MState := stAt "NTAt"
def mtNT : Term := ntMatch.getD .unit

/-! ## The captures: the static instance is the checker's here (D90's obligation 1, one state) -/

/-- What the stuck block of `match k { Z => (a := 1; ()), S _ => () }` captures at the match: `a` by
`&` (arm `Z` assigns it) and `k` read in place (the scrutinee), oldest binding first; nothing is
re-rooted (nothing is moved). -/
def bcNT : List Place × List (Place × Nat) := ([], [(.var 2, 1), (.var 0, 0)])

#guard mtNT.pp ["k", "r", "a", "NTAt"] == "match k { Z => a := 1; (), S _ => () }"
-- the reference's decision (the static instance, `BlockCaps.staticBlockCaps`)
#guard (checkerDecisions stNT 100000).blockCaps (DecideScope.topReadings stNT) (Steps.entryOf stNT) mtNT == bcNT
-- the checker's own captures (`blockEntry`'s first part) at the same state
#guard match (runMachine (Steps.ckBlockCaps 100000 mtNT) stNT 1000000).1 with
  | .ok bc _ => bc == bcNT
  | _ => false

/-! ## The checker: the entry ends `r` -/

-- at the match: `a ↦ loan_0`, `r ↦ borrow_0 σ0` (frame 1, positions 1 and 2), `k ↦ 1`
#guard stNT.env.size == 2 && (stNT.env[1]!).binds.size == 4
#guard Env.shape stNT.env (.bind 1 2) == some 0 && liveLoan stNT.env 0
#guard (Env.sitesOf stNT.env 0).map (fun x => (x.pos, x.path.length, x.fill)) == [(.bind 1 1, 0, false)]

/-- The checker's match, up to the arm: [Access] of the scrutinee for its tag, then the entry
(`joinEnds`, not in tail position). -/
def ckEntry (fuel : Nat) : M Unit := do
  accessPath fuel (.var 0); accessNeutralHead fuel (.var 0); discard (blockEntry fuel mtNT)

def after (x : M Unit) (st : MState) (fuel : Nat) : Option MState :=
  match (runMachine x st fuel).1 with
  | .ok () st' => some st'
  | _ => none

-- after the entry nothing is live: `r`'s borrow ended, though the arm that runs (`S _`) does not
-- touch `a`; `r` holds nothing, and no label has a site
#guard match after (ckEntry 100000) stNT 1000000 with
  | some st' => !liveLoan st'.env 0 && (allPos st'.env).all (fun p => Env.shape st'.env p == none) &&
      (Env.sitesOf st'.env 0).isEmpty
  | none => false
-- the whole match (the arm `S _`, then the join) leaves the same
#guard match after (discard (evalMatch 100000 true (.var 0) (match mtNT with | .matchNat _ z _ => z | _ => .unit)
    (match mtNT with | .matchNat _ _ u => u | _ => .unit) none false)) stNT 1000000 with
  | some st' => !liveLoan st'.env 0 && (allPos st'.env).all (fun p => Env.shape st'.env p == none)
  | none => false

/-! ## The reference: the entry ends the same borrow, and the relation's sites and holders agree

The reference state related to the checker's at the match, with the renaming the identity: the same
frames and positions, `r` holding `0`, and `0`'s one site at `a` (the checker's `Env.sitesOf`). The
meanings are not computable and are not needed by the entry, which reads sites only. -/

def sRefNT : SState :=
  { env := [{}, { binds := List.replicate 4 { ty := .plain .err, val := fun _ => .err } }],
    shape := fun p => if p = .bind 1 2 then some 0 else none,
    nextLoan := 1,
    lent := fun l => if l = 0 then [⟨.bind 1 1, [], false⟩] else [] }

-- the reference state's holders and sites are the checker's
#guard (allPos stNT.env).all fun p => Env.shape stNT.env p == if p == .bind 1 2 then some 0 else none

/-- **The reference's entry ends `r`'s borrow** (`Run.entryAccess` with the captures above): no
label is live after it, `r` holds nothing, and `0` has no site, as in the checker. So the
relation's holders and sites clauses hold after the entry with the identity renaming. -/
theorem ref_entry : (entryAccess bcNT sRefNT).liveLabels = [] ∧
    (entryAccess bcNT sRefNT).shape (.bind 1 2) = none ∧ (entryAccess bcNT sRefNT).lent 0 = [] := by
  decide +kernel

/-- Without the entry (in tail position, `NTTail`) the reference leaves `r` live, as the checker's
generic call does (a tail match is split, never closed off: D90's `G4`). -/
theorem ref_no_entry_tail (K : RunCtx) (φ : Future) :
    (matchEntry K φ false mtNT sRefNT).1.liveLabels = [0] := by
  show sRefNT.liveLabels = [0]
  decide +kernel

end Ochr.Meaning.Regress.EntryCheck
