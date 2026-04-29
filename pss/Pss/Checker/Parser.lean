import Pss.Checker.Term
import Pss.Checker.Replay

/-! # `Pss.Checker.Parser` — S-expression and proof-trace parsing

Minimal parser for the Lisp grammar used by the artifact, sufficient to load
the proof scripts in `examples/subtyping/proofs/*.txt` directly.

Grammar:
```
sexp   ::= atom | '(' sexp* ')' | "'" sexp
atom   ::= symbol | number
symbol ::= [^()\s'"]+
```

This is **not** a full Lisp parser — we only handle whitespace, parentheses,
single-quote, and bare symbols.  Comments (`;;`) and string literals are
stripped before parsing.
-/

namespace Pss.Checker
namespace Parser

/-- Raw s-expression. -/
inductive Sexp where
  | atom (s : String)
  | list (xs : List Sexp)
  deriving Repr, Inhabited

namespace Sexp

/-- Strip `;;`-style line comments from the input. -/
def stripComments (s : String) : String :=
  let lines := s.splitOn "\n"
  let stripLine (l : String) : String :=
    match l.splitOn ";" with
    | [] => l
    | first :: _ => first
  String.intercalate "\n" (lines.map stripLine)

/-- Tokens for the s-expression parser. -/
inductive Tok where
  | lparen
  | rparen
  | quote
  | sym (s : String)
  deriving Repr

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
def isDelim (c : Char) : Bool := c == '(' || c == ')' || c == '\'' || isWs c

partial def tokenize (s : String) : List Tok :=
  go s.toList []
where
  go : List Char → List Tok → List Tok
    | [], acc => acc.reverse
    | c :: rest, acc =>
      if isWs c then go rest acc
      else if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == '\'' then go rest (.quote :: acc)
      else
        -- collect symbol chars
        let (sym, rest') := collect (c :: rest) []
        go rest' (.sym (String.mk sym.reverse) :: acc)
  collect : List Char → List Char → (List Char × List Char)
    | [], acc => (acc, [])
    | c :: rest, acc =>
      if isDelim c then (acc, c :: rest) else collect rest (c :: acc)

partial def parseTokens (tokens : List Tok) : Option (Sexp × List Tok) :=
  match tokens with
  | [] => none
  | .lparen :: rest =>
    let rec parseList (toks : List Tok) (acc : List Sexp) : Option (List Sexp × List Tok) :=
      match toks with
      | [] => none
      | .rparen :: rest' => some (acc.reverse, rest')
      | _ =>
        match parseTokens toks with
        | some (s, rest') => parseList rest' (s :: acc)
        | none => none
    match parseList rest [] with
    | some (xs, rest') => some (.list xs, rest')
    | none => none
  | .rparen :: _ => none
  | .quote :: rest =>
    match parseTokens rest with
    | some (s, rest') => some (.list [.atom "quote", s], rest')
    | none => none
  | .sym s :: rest => some (.atom s, rest)

/-- Parse one or more top-level s-expressions. -/
partial def parseAll (input : String) : Option (List Sexp) :=
  let cleaned := stripComments input
  let tokens := tokenize cleaned
  go tokens []
where
  go (toks : List Tok) (acc : List Sexp) : Option (List Sexp) :=
    match toks with
    | [] => some acc.reverse
    | _ =>
      match parseTokens toks with
      | some (s, rest) => go rest (s :: acc)
      | none => none

/-- Convert a parsed s-expression to a `Term`.

    Recognised forms:
    * `top`                                → `Term.top`
    * `(quote x)`                          → `Term.var "x"`
    * `*foo*`-style atom or any unquoted   → `Term.macroRef "foo"`
    * `(FUN x type body)`                  → `Term.fun_ "x" type body`
    * `(y body)`                           → `Term.yfix body`
    * `(OR a₁ a₂ ...)`                     → `Term.or [a₁, a₂, ...]`
    * `(rator rand)`                       → `Term.app rator rand`
    * `(f a₁ a₂ ... aₙ)` with n ≥ 2        → curried `App` (left-associative)
-/
partial def toTerm : Sexp → Option Term
  | .atom "top" => some .top
  | .atom s => some (.macroRef s)
  | .list [.atom "quote", .atom x] => some (.var x)
  | .list (.atom "FUN" :: .atom x :: t :: b :: []) => do
      let tT ← toTerm t
      let bT ← toTerm b
      pure (.fun_ x tT bT)
  | .list [.atom "y", body] => do
      let b ← toTerm body
      pure (.yfix b)
  | .list (.atom "OR" :: rest) => do
      let alts ← rest.mapM toTerm
      pure (.or alts)
  | .list [a, b] => do
      let aT ← toTerm a
      let bT ← toTerm b
      pure (.app aT bT)
  | .list xs =>
      -- General application: curry left-associatively.
      match xs with
      | [] => none
      | hd :: rest => do
        let h ← toTerm hd
        rest.foldlM (fun acc x => do
          let xT ← toTerm x
          pure (.app acc xT)) h

/-- Convert a parsed proof-script action to `Replay.Act`. -/
partial def toAct : Sexp → Option Replay.Act
  | .list [.atom "start-term", t] => do
      let tT ← toTerm t
      pure (.startTerm tT)
  | .list [.atom "start-goal", t] => do
      let tT ← toTerm t
      pure (.startGoal tT)
  | .list [.atom "qed"] => some .qed
  | .list [.atom "commit"] => some .commit
  | .list [.atom "focus", .atom n] => do
      let nN ← n.toNat?
      pure (.focus nN)
  | .list (.atom "rewrite" :: actSpec :: rest) => do
      let op ← parseOp actSpec
      let plist ← parsePlist rest
      let side := match plist.lookup "on-objectives" with
        | some (.atom "t") => Replay.Side.onGoal
        | _ => Replay.Side.onTerm
      let path : Term.Path :=
        match plist.lookup "path" with
        | some (.atom "nil") => []
        | some (.list ps) => ps.filterMap (fun p => match p with
            | .atom s => s.toNat?
            | _ => none)
        | _ => []
      pure (.rewrite op side path)
  | _ => none
where
  parseOp : Sexp → Option RewriteOp
    | .atom "beta-substitute" => some .betaSubstitute
    | .atom "beta-substitute-all" => some .betaSubstituteAll
    | .atom "macro-expand" => some .macroExpand
    | .atom "macro-collapse" => some .macroCollapse
    | .atom "promote" => some .promote
    | .atom "split-or-all" => some .splitOrAll
    | .list [.atom "objective-or-split", .atom n] => do
        let nN ← n.toNat?
        pure (.objectiveOrSplit nN)
    | _ => none
  parsePlist (rest : List Sexp) : Option (List (String × Sexp)) :=
    match rest with
    | [] => some []
    | .atom k :: v :: rest' =>
      if k.startsWith ":" then do
        let tail ← parsePlist rest'
        pure ((k.drop 1, v) :: tail)
      else
        none
    | _ => none

/-- Parse a complete proof script string into a list of actions. -/
partial def parseScript (s : String) : Option (List Replay.Act) := do
  let sexps ← Sexp.parseAll s
  sexps.mapM toAct

end Sexp
end Parser
end Pss.Checker
