import Ochr.Notation
import Ochr.Rules

/-!
# The rule guard: the paper's rule names against the checker's

Run when the library is built. It reads `../paper/sections/*.typ` and the checker's sources and
reports every way in which the rules the paper prints and the rules the checker applies can
differ by name:

* a rule the paper prints (`ir(name: …)`, `infer(name: …)`, or a rule the appendix defines in
  prose, `proseRules`) that has no `Rule` constructor, and a `Rule` whose name the paper does not
  print;
* a name that two appendix rules share;
* a `[Name]` in the paper's text that names no rule;
* a `Rule` or `Ext` that no `fire` / `fireExt` call in `Ochr/*.lean` applies;
* a `#lean("…")` pointer of the appendix that does not name a declaration of the module it says.

The issues found must be exactly `expectedIssues` (and `notYetFired`): a new issue fails the
build, and so does a listed issue that has gone away, so the lists only change on purpose.
`notes/rule-audit.md` §4–§6 explains each. -/

namespace Ochr.RuleGuard
open Lean Elab Command

/-- The paper's sections: `../paper/sections`, or `$OCHR_PAPER_SECTIONS` if set (to check
another branch's paper). -/
def sectionsDir : IO System.FilePath := do
  pure ((← IO.getEnv "OCHR_PAPER_SECTIONS").getD "../paper/sections")

/-- Rules the appendix defines in prose, each with the text that defines it. -/
def proseRules : List (String × String) :=
  [("Access", "*[Access]*"), ("Close", "caption: [[Close]:"), ("Type-pos", "_Sorts are syntactic_ ([Type-pos])"),
   ("Rec", "*[Rec]*"), ("Call-type", "*[Call-type]*"), ("Def", "*[Def]*"),
   ("Conv-refl", "- [Conv-refl]"), ("Conv-cong", "- [Conv-cong]"), ("Conv-unit", "- [Conv-unit]"),
   ("Conv-pi", "- [Conv-pi]"), ("Conv-fun", "- [Conv-fun]")]

/-- Bracketed words of the paper's text that are content, not rule references. -/
def notRules : List String :=
  ["Figure", "Definition", "Conjecture", "Aeneas", "Verus", "Quicksort", "Hash map", "Loops"]

/-- The issues the guard currently finds, without line numbers. Remove a line when its issue
is fixed; the build fails until the list matches. -/
def expectedIssues : List String := [
  "paper rule [End] (eval.typ) has no Rule constructor",
  "name [Ind] is defined by more than one appendix rule",
  "name [Ind] is the name of more than one Rule",
  "Rule [Drop] is not printed by the paper",
  "Rule [Capture] is not printed by the paper",
  "Rule [Block] is not printed by the paper",
  "Rule [Eq-inj] is not printed by the paper",
  "Rule [Eq-refl] is not printed by the paper",
  "Rule [Eq-disj] is not printed by the paper",
  "Rule [Eq-stuck] is not printed by the paper",
  "reference [Pair] names no rule",
  "reference [Drop] names no rule",
  "pointer `Term.refsOk`: not in Ochr.Machine (it is in Ochr.Basic)",
  "pointer `refTopOk (Basic.lean)`: no declaration Ochr.refTopOk",
  "pointer `Term.placeOccs`: not in Ochr.Machine (it is in Ochr.Basic)",
  "pointer `evalCore (.pi, .fix, .sort, .prod, .ref, .eq, .tind, .prim \"J\", .const)`: no constructor .prod",
  "pointer `mkAnd`: not in Ochr.Machine (it is in Ochr.Basic)",
  "pointer `tupleVal (Obs.lean)`: no declaration Ochr.tupleVal",
  "pointer `footprint`: not in Ochr.Machine (it is in Ochr.Obs)",
  "pointer `evalCore (.sort, .nat, .unit, .prod, .ref, .eq, .pi, .id, .tind)`: no constructor .prod",
  "pointer `checkInd`: not in Ochr.Machine (it is in Ochr.Check)"
]

/-- Rules and extensions not yet tagged with a `fire` call (the tagging is in progress). -/
def notYetFired : List String :=
  Rule.all.map (·.name) ++
  ["ErasedReadMovesBorrow", "BlockRefCapture", "CaptureTypeFromValue", "TypeOfSealed",
   "FieldTypeFromPattern", "ArmsDisagree", "EmbeddedDecl", "CapturedPropFromValue",
   "TermProjection", "RewriteNothing", "TailRewrite", "ErasedCallWhole", "ErasedBodyCopies",
   "ZeroArmByType", "BlockMovesByPlace", "BlockEta", "BlockFieldSplit", "BlockMoveAnyShape",
   "BlockProofNotRef", "BlockBorrowPartlyMoved", "BlockNestedReads", "UntypedObs",
   "OwnerTypeFromObs", "ConvErrorFalse", "ConvCycleFalse", "JStuckRuns"]

/-- Every `Ext`, by name (the guard checks each is fired). -/
def extNames : List String :=
  [Ext.ErasedReadMovesBorrow, .BlockRefCapture, .CaptureTypeFromValue, .TypeOfSealed,
   .FieldTypeFromPattern, .ArmsDisagree, .EmbeddedDecl, .CapturedPropFromValue, .TermProjection,
   .RewriteNothing, .TailRewrite, .ErasedCallWhole, .ErasedBodyCopies, .ZeroArmByType,
   .BlockMovesByPlace, .BlockEta, .BlockFieldSplit, .BlockMoveAnyShape, .BlockProofNotRef,
   .BlockBorrowPartlyMoved, .BlockNestedReads, .UntypedObs, .OwnerTypeFromObs, .ConvErrorFalse,
   .ConvCycleFalse, .JStuckRuns].map (·.name)

/-! ## Reading the paper -/

def takeUntil (c : Char) (s : String) : String := String.ofList (s.toList.takeWhile (· != c))

/-- The strings quoted right after `key` on each line, with their line numbers. -/
def quotedAfter (key : String) (text : String) : List (String × Nat) :=
  (text.splitOn "\n").zipIdx.flatMap fun (line, i) =>
    ((line.splitOn key).drop 1).map fun part => (takeUntil '"' part, i + 1)

/-- Is this bracketed text shaped like a rule name (`T-Let-ann`, `End ℓ`)? -/
def ruleShaped (s : String) : Bool :=
  match s.toList with
  | c :: _ =>
    c.isUpper && s.length ≤ 24 &&
      (s.toList.all fun d => d.isAlphanum || d == '-' || d == ' ' || d == 'ℓ') &&
      (!(s.toList.contains ' ') || s.endsWith " ℓ")
  | [] => false

/-- The texts between a `[` and the next `]` with no `[` between. -/
partial def bracketsIn : List Char → List String
  | [] => []
  | '[' :: rest =>
    let inner := rest.takeWhile (fun c => c != ']' && c != '[')
    match rest.drop inner.length with
    | ']' :: more => String.ofList inner :: bracketsIn more
    | more => bracketsIn more
  | _ :: rest => bracketsIn rest

/-- Every `[Name]` of the text, with its line number. -/
def bracketed (text : String) : List (String × Nat) :=
  (text.splitOn "\n").zipIdx.flatMap fun (line, i) => (bracketsIn line.toList).map (·, i + 1)

structure Paper where
  files : List (String × String)          -- file name, text

def readPaper : IO (Option Paper) := do
  let dir ← sectionsDir
  unless ← dir.isDir do return none
  let mut files := #[]
  for e in ← dir.readDir do
    if e.fileName.endsWith ".typ" then files := files.push (e.fileName, ← IO.FS.readFile e.path)
  pure (some { files := files.toList.mergeSort (fun a b => a.1 < b.1) })

/-! ## Reading the checker -/

/-- The identifiers passed to `head` (`fire .X`, `fireExt .X`) in the checker's sources. -/
def firedNames (head : String) (srcs : List String) : List String :=
  srcs.flatMap fun s => ((s.splitOn (head ++ " .")).drop 1).map fun part =>
    String.ofList (part.toList.takeWhile fun c => c.isAlphanum)

def checkerSources : IO (List String) := do
  let mut out := #[]
  for e in ← ("Ochr" : System.FilePath).readDir do
    if e.fileName.endsWith ".lean" && e.fileName != "RuleGuard.lean" && e.fileName != "Rules.lean" then
      out := out.push (← IO.FS.readFile e.path)
  pure out.toList

/-! ## The `#lean` pointers -/

/-- A quoted string's characters (`\\"` is an escaped quote) and what follows it. -/
partial def quoted : List Char → List Char → List Char × List Char
  | '\\' :: '"' :: r, acc => quoted r ('"' :: acc)
  | '"' :: r, acc => (acc.reverse, r)
  | c :: r, acc => quoted r (c :: acc)
  | [], acc => (acc.reverse, [])

/-- The quoted arguments up to the closing parenthesis. -/
partial def quotedArgs : List Char → List String
  | '"' :: rest => let (s, r) := quoted rest []; String.ofList s :: quotedArgs r
  | ')' :: _ => []
  | _ :: rest => quotedArgs rest
  | [] => []

/-- The arguments of every `#lean("…", …)` of the appendix, with line numbers. -/
def leanPointers (text : String) : List (String × Nat) :=
  (text.splitOn "\n").zipIdx.flatMap fun (line, i) =>
    ((line.splitOn "#lean(").drop 1).flatMap fun part => (quotedArgs part.toList).map (·, i + 1)

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- The issue with one pointer, if any. -/
def pointerIssue (env : Environment) (arg : String) : Option String :=
  let bad (why : String) := some s!"pointer `{arg}`: {why}"
  -- `name (File.lean)`, `name (.case, …)` or `File.lean`
  let (item, note) := match arg.splitOn " (" with
    | [a, b] => (a, some (takeUntil ')' b))
    | _ => (arg, none)
  if item.endsWith ".lean" then
    none     -- a whole file (checked only by name, below in `run`)
  else
    let dflt : Name := if item.startsWith "Surface." then `Ochr.Surface else `Ochr.Machine
    let expected : Name := match note with
      | some f => if f.endsWith ".lean" then ("Ochr." ++ (f.dropEnd 5).toString).toName else dflt
      | none => dflt
    -- the cases named are constructors of the syntax the function matches on
    let syn : Name := if item.startsWith "Surface." then `Ochr.Surface.STerm else `Ochr.Term
    let decl : Name := ("Ochr." ++ item).toName
    if !env.contains decl then bad s!"no declaration {decl}"
    else match moduleOf env decl with
      | some m =>
        if m != expected then bad s!"not in {expected} (it is in {m})"
        else
          let cases := match note with
            | some n => if n.startsWith "." then (n.splitOn ", ").map fun (c : String) =>
                String.ofList ((c.toList.drop 1).takeWhile fun ch => ch.isAlphanum) else []
            | none => []
          match cases.find? fun c =>
              !env.contains (syn ++ c.toName) with
          | some c => bad s!"no constructor .{c}"
          | none => none
      | none => bad "not in a module"

/-! ## The check -/

def issues (env : Environment) (p : Paper) (srcs : List String) : Array String := Id.run do
  let mut out : Array String := #[]
  let appendix := (p.files.lookup "appendix.typ").getD ""
  -- the rules the paper prints: the appendix's, the body's (whose names must be the appendix's)
  let mut printed : List String := []
  for (f, t) in p.files do
    for (n, _) in quotedAfter "ir(name: \"" t ++ quotedAfter "infer(name: \"" t do
      unless printed.contains n do printed := printed ++ [n]
      unless Rule.all.any (·.name == n) do
        out := out.push s!"paper rule [{n}] ({f}) has no Rule constructor"
  for (n, anchor) in proseRules do
    if (appendix.splitOn anchor).length > 1 then
      unless printed.contains n do printed := printed ++ [n]
    else out := out.push s!"prose rule [{n}] is no longer defined by \"{anchor}\" in the appendix"
  -- names defined twice in the appendix, and by two `Rule`s
  let appNames := (quotedAfter "ir(name: \"" appendix).map (·.1)
  for n in appNames.eraseDups do
    if appNames.count n > 1 then out := out.push s!"name [{n}] is defined by more than one appendix rule"
  let codeNames := Rule.all.map (·.name)
  for n in codeNames.eraseDups do
    if codeNames.count n > 1 then out := out.push s!"name [{n}] is the name of more than one Rule"
    unless printed.contains n do out := out.push s!"Rule [{n}] is not printed by the paper"
  -- every `[Name]` of the text names a rule
  let mut seenRefs : List String := []
  for (_, t) in p.files do
    for (r, _) in bracketed t do
      if ruleShaped r && !notRules.contains r && !printed.contains r && !seenRefs.contains r then
        seenRefs := seenRefs ++ [r]
        out := out.push s!"reference [{r}] names no rule"
  -- every rule and extension is applied somewhere
  let fired := firedNames "fire" srcs
  let firedExt := firedNames "fireExt" srcs
  let reprName (r : Rule) : String := ((reprStr r).drop "Ochr.Rule.".length).toString
  for r in Rule.all do
    unless fired.contains (reprName r) do out := out.push s!"Rule [{r.name}] is never fired"
  for e in extNames do
    unless firedExt.contains e do out := out.push s!"Ext {e} is never fired"
  -- the appendix's pointers
  for (arg, _) in leanPointers appendix do
    if let some m := pointerIssue env arg then
      unless out.contains m do out := out.push m
  pure out

def expectedAll : List String :=
  expectedIssues ++ notYetFired.map fun n =>
    if Rule.all.any (·.name == n) then s!"Rule [{n}] is never fired" else s!"Ext {n} is never fired"

/-- Report-only while the tagging is in progress: a mismatch is a warning. Set to `true` once
every rule fires and the paper's issues are fixed, so that a mismatch fails the build. -/
def strict : Bool := false

def run : CommandElabM Unit := do
  let some p ← (readPaper : IO _) | logWarning "rule guard: ../paper/sections not found; skipped"
  let srcs ← (checkerSources : IO _)
  let found := issues (← getEnv) p srcs
  -- `[Ind]` is one name for two constructors, so its "never fired" line may repeat
  let found := found.toList.eraseDups
  let new := found.filter (!expectedAll.contains ·)
  let gone := expectedAll.eraseDups.filter (!found.contains ·)
  if !new.isEmpty || !gone.isEmpty then
    let msg := m!"rule guard:\n  new issues (fix them, or list them in expectedIssues):\n    {"\n    ".intercalate new}\n  listed issues that no longer occur (remove them):\n    {"\n    ".intercalate gone}"
    if strict then throwError msg else logWarning msg

#eval run

end Ochr.RuleGuard
