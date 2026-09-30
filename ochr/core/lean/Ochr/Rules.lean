import Ochr.Env

/-!
# The paper's rules, by name

`Rule` has one constructor per rule of the paper's appendix (`paper/sections/appendix.typ`),
printed or defined in prose, and `Rule.name` is its printed name, character for character.
`Ext` has one constructor per decision the checker makes that no printed rule states and that
can change a verdict or a normal form (`notes/rule-audit.md` §2): the checker's extensions,
listed so that a derivation that uses one says so. Closing a divergence deletes its `Ext`.

`fire r msg` records one application of `r`. With `cfg.derivation` every application is
traced, indented by call depth, so a run prints its derivation in the paper's names; with
`cfg.trace` only the coarse rules print (goals, splits, call types, blocks, rewrites), as the
trace always has. `fireExt` does the same for an extension, printed `(checker) Name`.

`Ochr/RuleGuard.lean` checks these names against the paper when the library is built.
-/

namespace Ochr

inductive Rule where
  -- the machine: borrows (@app-machine)
  | EndL | Access | Copy | Read | Move | ReadErr | Borrow | BorrowErr | Clone | Assign | Drop
  -- sequencing and data
  | Let | Seq | Ctor
  -- functions, types and proofs
  | Global | Fix | Pi | Sort | IndType | Ref | Eq | J | JStuck | Capture
  | EraseProof | EraseType | EraseErr
  -- calls
  | ArgsNil | Args | Call | CallErr | App | AppClose | AppHead | AppNeutral | AppNeutralHead
  | Close
  -- matching
  | Match | MatchStuck | MatchErr | MatchProp | MatchNone
  -- sealed programs and stuck blocks
  | Seal | SealStuck | SealErr | Block
  -- observation, `Id`, conversion, `eq` (@app-conv)
  | Obs | ObsBorrow | Id
  | ConvRefl | ConvCong | ConvUnit | ConvPi | ConvFun
  | EqInj | EqRefl | EqDisj | EqStuck
  -- typing (@app-typing)
  | TypePos | TErase | TRead | TBorrow | TAssign | TLet | TLetAnn | TSeq | TCtor
  | TSort | TType | TInd | TRef | TEq | TPi | TJ | TRewrite
  | TGlobal | TConst | TFix | CallType | TCall | TCallProof | Rec
  | TMatch | Split | SplitGen | TSplitGoal
  | TailSplit | TailGen | TailMatch | TailLet | TailSeq | TailEnd
  | TMatchProp | TMatchErased | TMatchNone | TailProp
  -- dependent fields (D64)
  | Open | Repack
  -- definitions
  | Def | IndDecl | Const
deriving BEq, Repr, Inhabited

/-- Every rule, in the order above (for the guard and for coverage). -/
def Rule.all : List Rule :=
  [.EndL, .Access, .Copy, .Read, .Move, .ReadErr, .Borrow, .BorrowErr, .Clone, .Assign, .Drop,
   .Let, .Seq, .Ctor,
   .Global, .Fix, .Pi, .Sort, .IndType, .Ref, .Eq, .J, .JStuck, .Capture,
   .EraseProof, .EraseType, .EraseErr,
   .ArgsNil, .Args, .Call, .CallErr, .App, .AppClose, .AppHead, .AppNeutral, .AppNeutralHead,
   .Close,
   .Match, .MatchStuck, .MatchErr, .MatchProp, .MatchNone,
   .Seal, .SealStuck, .SealErr, .Block,
   .Obs, .ObsBorrow, .Id,
   .ConvRefl, .ConvCong, .ConvUnit, .ConvPi, .ConvFun,
   .EqInj, .EqRefl, .EqDisj, .EqStuck,
   .TypePos, .TErase, .TRead, .TBorrow, .TAssign, .TLet, .TLetAnn, .TSeq, .TCtor,
   .TSort, .TType, .TInd, .TRef, .TEq, .TPi, .TJ, .TRewrite,
   .TGlobal, .TConst, .TFix, .CallType, .TCall, .TCallProof, .Rec,
   .TMatch, .Split, .SplitGen, .TSplitGoal,
   .TailSplit, .TailGen, .TailMatch, .TailLet, .TailSeq, .TailEnd,
   .TMatchProp, .TMatchErased, .TMatchNone, .TailProp,
   .Open, .Repack,
   .Def, .IndDecl, .Const]

/-- The rule's name as the paper prints it: in an inference rule, or as the label of a rule the
appendix defines in prose (`*Drop* ([Drop])`, the `eq` clauses' `[Eq-inj]` …). -/
def Rule.name : Rule → String
  | .EndL => "End" | .Access => "Access" | .Copy => "Copy" | .Read => "Read" | .Move => "Move"
  | .ReadErr => "Read-err" | .Borrow => "Borrow" | .BorrowErr => "Borrow-err" | .Clone => "Clone"
  | .Assign => "Assign" | .Drop => "Drop"
  | .Let => "Let" | .Seq => "Seq" | .Ctor => "Ctor"
  | .Global => "Global" | .Fix => "Fix" | .Pi => "Pi" | .Sort => "Sort" | .IndType => "Ind"
  | .Ref => "Ref" | .Eq => "Eq" | .J => "J" | .JStuck => "J-stuck" | .Capture => "Capture"
  | .EraseProof => "Erase-proof" | .EraseType => "Erase-type" | .EraseErr => "Erase-err"
  | .ArgsNil => "Args-nil" | .Args => "Args" | .Call => "Call" | .CallErr => "Call-err"
  | .App => "App" | .AppClose => "App-close" | .AppHead => "App-head"
  | .AppNeutral => "App-neutral" | .AppNeutralHead => "App-neutral-head" | .Close => "Close"
  | .Match => "Match" | .MatchStuck => "Match-stuck" | .MatchErr => "Match-err"
  | .MatchProp => "Match-prop" | .MatchNone => "Match-none"
  | .Seal => "Seal" | .SealStuck => "Seal-stuck" | .SealErr => "Seal-err" | .Block => "Block"
  | .Obs => "Obs" | .ObsBorrow => "Obs-borrow" | .Id => "Id"
  | .ConvRefl => "Conv-refl" | .ConvCong => "Conv-cong" | .ConvUnit => "Conv-unit"
  | .ConvPi => "Conv-pi" | .ConvFun => "Conv-fun"
  | .EqInj => "Eq-inj" | .EqRefl => "Eq-refl" | .EqDisj => "Eq-disj"
  | .EqStuck => "Eq-stuck"
  | .TypePos => "Type-pos" | .TErase => "T-Erase" | .TRead => "T-Read" | .TBorrow => "T-Borrow"
  | .TAssign => "T-Assign" | .TLet => "T-Let" | .TLetAnn => "T-Let-ann" | .TSeq => "T-Seq"
  | .TCtor => "T-Ctor" | .TSort => "T-Sort" | .TType => "T-Type" | .TInd => "T-Ind"
  | .TRef => "T-Ref" | .TEq => "T-Eq" | .TPi => "T-Pi" | .TJ => "T-J" | .TRewrite => "T-Rewrite"
  | .TGlobal => "T-Global" | .TConst => "T-Const" | .TFix => "T-Fix" | .CallType => "Call-type"
  | .TCall => "T-Call" | .TCallProof => "T-Call-proof" | .Rec => "Rec"
  | .TMatch => "T-Match" | .Split => "Split" | .SplitGen => "Split-gen"
  | .TSplitGoal => "T-Split-goal"
  | .TailSplit => "Tail-split" | .TailGen => "Tail-gen" | .TailMatch => "Tail-match"
  | .TailLet => "Tail-let" | .TailSeq => "Tail-seq" | .TailEnd => "Tail-end"
  | .TMatchProp => "T-Match-prop" | .TMatchErased => "T-Match-erased" | .TMatchNone => "T-Match-none"
  | .TailProp => "Tail-prop"
  | .Open => "Open" | .Repack => "Repack"
  | .Def => "Def" | .IndDecl => "Ind-decl" | .Const => "Const"

/-- The rules the plain trace (`cfg.trace`) has always shown: goals, splits, call types. -/
def Rule.coarse : Rule → Bool
  | .Def | .CallType | .Split | .SplitGen | .TSplitGoal | .TailSplit | .TailGen | .TRewrite
  | .Block => true
  | _ => false

/-- The checker's extensions: decisions no printed rule states that can change a verdict or
a normal form. The comment on each gives its item in `notes/rule-audit.md` §2. -/
inductive Ext where
  | ErasedReadMovesBorrow    -- C3: an erased read of a borrow moves it
  | CaptureTypeFromValue     -- C6: a captured datum's type is re-derived from its value
  | TypeOfSealed             -- C8: the type of a sealed program, a live loan, an unannotated constructor
  | FieldTypeFromPattern     -- C9: a field place's type from the pattern's constructor
  | EmbeddedDecl             -- C12: an embedded value's declared type read from the value
  | CapturedPropFromValue    -- C18: a captured variable is a proposition by its value's class
  | TermProjection           -- C20: `t.1`/`t.2` of a term that is not a place
  | TailRewrite              -- C24: in tail position, the rewritten goal is the path's goal
  | ErasedCallWhole          -- C28: a borrow argument of an erased call must be whole
  | ErasedBodyCopies         -- C33: the body of a function whose calls are erased reads by copying
  | ZeroArmByType            -- C38: a zero-arm match is a proof iff the annotation's value is a proposition
  | BlockMovesByPlace        -- C41: a block's moves are read from a log, by place
  | BlockEta                 -- C42: closing off refines a one-constructor abstract value
  | BlockFieldSplit          -- C43: a block's captures split into fields, its matches pre-selected
  | BlockMoveAnyShape        -- C44: a moved capture is moved in whatever its shape
  | BlockProofNotRef         -- C45: a proof is never captured by `&`
  | BlockBorrowPartlyMoved   -- C46: a borrow moved into a block whose arm moves out through it
  | BlockNestedReads         -- C47: uses inside a nested function are reads for the captures
  | OwnerTypeFromObs         -- C50: an untyped owner typed by its observed values
  | ConvErrorFalse           -- C52: a comparison that errors or is stuck answers "no"
  | ConvCycleFalse           -- C53: a comparison already in progress answers "no"
deriving BEq, Repr, Inhabited

def Ext.name (e : Ext) : String := ((reprStr e).drop "Ochr.Ext.".length).toString

/-- One application of a rule. `msg` is built only when the line is recorded. -/
def fire (r : Rule) (msg : Unit → String := fun _ => "") : M Unit := do
  let s ← get
  if s.cfg.derivation || (s.cfg.trace && r.coarse) then
    let m := msg ()
    let ind := if s.cfg.derivation then "".pushn ' ' (2 * s.depth) else ""
    modifyThe (Array String) (·.push s!"{ind}[{r.name}]{if m.isEmpty then "" else " " ++ m}")

/-- One use of a checker extension. -/
def fireExt (e : Ext) (msg : Unit → String := fun _ => "") : M Unit := do
  let s ← get
  if s.cfg.derivation then
    let m := msg ()
    let ind := "".pushn ' ' (2 * s.depth)
    modifyThe (Array String) (·.push s!"{ind}(checker) {e.name}{if m.isEmpty then "" else ": " ++ m}")

end Ochr
