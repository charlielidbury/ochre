import Pss.Checker.Term
import Pss.Checker.Replay
import Pss.Checker.Parser
import Pss.Checker.Encodings

/-! # `Pss.Checker.Examples` — Worked examples from PPDP 2025 §4

We replicate the proof scripts in
`pss/checker-artifact/examples/subtyping/proofs/*.txt` as Lean values,
then assert via `decide` that `Replay.runOk` succeeds.

The examples covered here:
* `1 ≤ int` (`leq-1-int.txt`, §4.1)
* extra: `1 ≤ OR(1, 2)` and `(OR 1 2) ≤ int` (from `or.el`)

Examples §4.2-4.5 (`plus-succint`, `factorial`, `safediv`, `syracuse`) require
multi-thousand-character proof traces and are deferred to a follow-up port.
-/

namespace Pss.Checker
namespace Examples

open Pss.Checker.Term
open Pss.Checker.Replay

/-! ### Example 4.1 — `*1* ≤ *int*`

Proof script faithfully transcribed from
`pss/checker-artifact/examples/subtyping/proofs/leq-1-int.txt`.
-/

/-- The expanded form of `*int*` after one Y-unfold:
```
(FUN self top
  (FUN zero-case top
    (FUN succ-case (FUN n top top)
      (OR 'zero-case ('succ-case 'self)))))
```
-/
def intYBody : Term :=
  .fun_ "self" .top
    (.fun_ "zero-case" .top
      (.fun_ "succ-case" (.fun_ "n" .top .top)
        (.or [.var "zero-case",
              .app (.var "succ-case") (.var "self")])))

/-- The "successor of zero" inner pattern that `*int*` reduces to under
    sufficient unfolding. -/
def zeroForm : Term :=
  .fun_ "zero-case" .top
    (.fun_ "succ-case" (.fun_ "n" .top .top) (.var "zero-case"))

/-- Variant where the inner Y-unfolded body has been simplified. -/
def intYUnit : Term :=
  .yfix
    (.fun_ "self" .top
      (.fun_ "zero-case" .top
        (.fun_ "succ-case" (.fun_ "n" .top .top)
          (.var "zero-case"))))

/-- Trace of `leq-1-int.txt`. -/
def leq1IntTrace : List Act :=
  [ .startTerm (.macroRef "*1*"),
    .startGoal (.macroRef "*int*"),
    .rewrite .macroExpand .onGoal [],
    .rewrite .betaSubstitute .onGoal [],
    .rewrite .betaSubstituteAll .onGoal [],
    .rewrite (.objectiveOrSplit 1) .onGoal [3, 3],
    .rewrite (.objectiveOrSplit 0) .onGoal [3, 3, 1, 1, 3, 3, 3],
    .rewrite .betaSubstitute .onGoal [3, 3, 1],
    .rewrite .betaSubstituteAll .onGoal [],
    .rewrite .macroExpand .onTerm [],
    .qed ]

/-- The `1 ≤ int` example terminates with all goals discharged. -/
def leq1IntOk : Bool := Replay.runOk Term.stdDefs leq1IntTrace

theorem leq1Int_passes : leq1IntOk = true := by native_decide

/-! ### Bonus example — `*1* ≤ OR(*1*, *2*)` (from `or.el`)

We pick the left alternative of the OR via `(objective-or-split 0)`. -/

def leq1Or12Trace : List Act :=
  [ .startTerm (.macroRef "*1*"),
    .startGoal (.or [.macroRef "*1*", .macroRef "*2*"]),
    .rewrite (.objectiveOrSplit 0) .onGoal [] ,
    .qed ]

def leq1Or12Ok : Bool := Replay.runOk Term.stdDefs leq1Or12Trace

theorem leq1Or12_passes : leq1Or12Ok = true := by native_decide

/-! ### Bonus example — `*2* ≤ OR(*1*, *2*)` -/

def leq2Or12Trace : List Act :=
  [ .startTerm (.macroRef "*2*"),
    .startGoal (.or [.macroRef "*1*", .macroRef "*2*"]),
    .rewrite (.objectiveOrSplit 1) .onGoal [],
    .qed ]

def leq2Or12Ok : Bool := Replay.runOk Term.stdDefs leq2Or12Trace

theorem leq2Or12_passes : leq2Or12Ok = true := by native_decide

/-! ### Bonus example — `OR(*1*, *2*) ≤ *int*` (from `or.el`)

Splits into two goals: `*1* ≤ *int*` and `*2* ≤ *int*`.  Each is closed by
unfolding `*int*` enough times.

For `*2* ≤ *int*` we need to unfold the y-fix twice (once to expose `*1*`'s
shape, once for the second `succ-case` layer). -/

def leqOr12IntTrace : List Act :=
  [ .startTerm (.or [.macroRef "*1*", .macroRef "*2*"]),
    .startGoal (.macroRef "*int*"),
    -- Split the term-side OR.  Current goal becomes `*1* ≤ *int*`;
    -- a new goal `*2* ≤ *int*` is appended.
    .rewrite .splitOrAll .onTerm [],
    -- ===== Goal 0: `*1* ≤ *int*` (identical to §4.1) =====
    .rewrite .macroExpand .onGoal [],
    .rewrite .betaSubstitute .onGoal [],
    .rewrite .betaSubstituteAll .onGoal [],
    .rewrite (.objectiveOrSplit 1) .onGoal [3, 3],
    .rewrite (.objectiveOrSplit 0) .onGoal [3, 3, 1, 1, 3, 3, 3],
    .rewrite .betaSubstitute .onGoal [3, 3, 1],
    .rewrite .betaSubstituteAll .onGoal [],
    .rewrite .macroExpand .onTerm [],
    .qed,
    -- ===== Goal 1: `*2* ≤ *int*` =====
    -- *2* = succ(succ(zero)).  We need TWO succ-case unfolds, then a zero.
    .rewrite .macroExpand .onGoal [],
    .rewrite .betaSubstitute .onGoal [],
    .rewrite .betaSubstituteAll .onGoal [],
    -- OR at [3,3]: pick succ-case alternative.
    .rewrite (.objectiveOrSplit 1) .onGoal [3, 3],
    -- Unfold the inner y at [3,3,1,1] → after replacement at [3,3,1].
    .rewrite .betaSubstitute .onGoal [3, 3, 1],
    .rewrite .betaSubstituteAll .onGoal [],
    -- New OR at [3,3,1,3,3]: pick succ-case again.
    .rewrite (.objectiveOrSplit 1) .onGoal [3, 3, 1, 3, 3],
    -- Unfold the inner y now at [3,3,1,3,3,1].
    .rewrite .betaSubstitute .onGoal [3, 3, 1, 3, 3, 1],
    .rewrite .betaSubstituteAll .onGoal [],
    -- New OR at [3,3,1,3,3,1,3,3]: pick zero-case.
    .rewrite (.objectiveOrSplit 0) .onGoal [3, 3, 1, 3, 3, 1, 3, 3],
    .rewrite .macroExpand .onTerm [],
    .qed ]

def leqOr12IntOk : Bool := Replay.runOk Term.stdDefs leqOr12IntTrace

theorem leqOr12Int_passes : leqOr12IntOk = true := by native_decide

/-! ### Example — `*0* ≤ *int*` (simpler base case) -/

def leq0IntTrace : List Act :=
  [ .startTerm (.macroRef "*0*"),
    .startGoal (.macroRef "*int*"),
    .rewrite .macroExpand .onGoal [],
    .rewrite .betaSubstitute .onGoal [],
    .rewrite .betaSubstituteAll .onGoal [],
    -- OR at [3,3]: pick zero-case (alternative 0).
    .rewrite (.objectiveOrSplit 0) .onGoal [3, 3],
    .rewrite .macroExpand .onTerm [],
    .qed ]

def leq0IntOk : Bool := Replay.runOk Term.stdDefs leq0IntTrace

theorem leq0Int_passes : leq0IntOk = true := by native_decide

/-! ### Example — `*0* ≤ OR(*1*, *0*)` (zero is in the union) -/

def leq0Or10Trace : List Act :=
  [ .startTerm (.macroRef "*0*"),
    .startGoal (.or [.macroRef "*1*", .macroRef "*0*"]),
    .rewrite (.objectiveOrSplit 1) .onGoal [],
    .qed ]

def leq0Or10Ok : Bool := Replay.runOk Term.stdDefs leq0Or10Trace

theorem leq0Or10_passes : leq0Or10Ok = true := by native_decide

/-! ### Reflexivity-style examples (sanity checks) -/

def reflTopTrace : List Act :=
  [ .startTerm .top, .startGoal .top, .qed ]

def reflTopOk : Bool := Replay.runOk Term.stdDefs reflTopTrace

theorem reflTop_passes : reflTopOk = true := by native_decide

def reflBoolTrace : List Act :=
  [ .startTerm (.macroRef "*bool*"),
    .startGoal (.macroRef "*bool*"),
    .qed ]

def reflBoolOk : Bool := Replay.runOk Term.stdDefs reflBoolTrace

theorem reflBool_passes : reflBoolOk = true := by native_decide

/-! ### Example — `*true* ≤ *bool*` -/

def trueIsBoolTrace : List Act :=
  [ .startTerm (.macroRef "*true*"),
    .startGoal (.macroRef "*bool*"),
    .rewrite .macroExpand .onGoal [],
    .rewrite (.objectiveOrSplit 0) .onGoal [],
    .qed ]

def trueIsBoolOk : Bool := Replay.runOk Term.stdDefs trueIsBoolTrace

theorem trueIsBool_passes : trueIsBoolOk = true := by native_decide

def falseIsBoolTrace : List Act :=
  [ .startTerm (.macroRef "*false*"),
    .startGoal (.macroRef "*bool*"),
    .rewrite .macroExpand .onGoal [],
    .rewrite (.objectiveOrSplit 1) .onGoal [],
    .qed ]

def falseIsBoolOk : Bool := Replay.runOk Term.stdDefs falseIsBoolTrace

theorem falseIsBool_passes : falseIsBoolOk = true := by native_decide

/-! ### Bool reflection: `*bool* ≤ OR(*true*, *false*)` -/

def boolEqOrTrace : List Act :=
  [ .startTerm (.macroRef "*bool*"),
    .startGoal (.or [.macroRef "*true*", .macroRef "*false*"]),
    .rewrite .macroExpand .onTerm [],
    .qed ]

def boolEqOrOk : Bool := Replay.runOk Term.stdDefs boolEqOrTrace

theorem boolEqOr_passes : boolEqOrOk = true := by native_decide

/-! ### Parser-driven examples — load proof scripts from the artifact

We can also parse the original Lisp proof traces directly from
`pss/checker-artifact/examples/subtyping/proofs/*.txt`. -/

/-- Cleaned text of `leq-1-int.txt`, without the explanatory `:desc`
    strings (the parser doesn't handle string literals). -/
def leq1IntScriptText : String :=
  "(start-term *1*)
   (start-goal *int*)
   (rewrite macro-expand :on-objectives t :path nil)
   (rewrite beta-substitute :on-objectives t :path nil)
   (rewrite beta-substitute-all :on-objectives t :path nil)
   (rewrite (objective-or-split 1) :on-objectives t :path (3 3))
   (rewrite (objective-or-split 0) :on-objectives t :path (3 3 1 1 3 3 3))
   (rewrite beta-substitute :on-objectives t :path (3 3 1))
   (rewrite beta-substitute-all :on-objectives t :path nil)
   (rewrite macro-expand :on-objectives nil :path nil)
   (qed)"

def leq1IntFromScript : Bool :=
  match Parser.Sexp.parseScript leq1IntScriptText with
  | some acts => Replay.runOk Term.stdDefs acts
  | none => false

theorem leq1IntFromScript_passes : leq1IntFromScript = true := by native_decide

/-! ### PPDP §4.2 — `plus(succ int)(succ int) ≤ succ int`

Cleaned text of `plus-succint-succint-leq-succint.txt`. -/

def plusSuccTrace : String :=
  "(start-term ((*plus* (*succ* *int*)) (*succ* *int*)))
   (start-goal (*succ* *int*))
   (rewrite macro-expand :on-objectives nil :path (0 0))
   (rewrite macro-expand :on-objectives nil :path (0 1 0))
   (rewrite beta-substitute :on-objectives nil :path (0 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (commit)
   (rewrite promote :on-objectives nil :path (1 0 0 1 3 3 3 1 3 1 0 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (rewrite beta-substitute :on-objectives nil :path (1 0 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (rewrite macro-expand :on-objectives nil :path (1 0 0))
   (rewrite beta-substitute :on-objectives nil :path (1 0 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (rewrite macro-expand :on-objectives t :path (1))
   (rewrite beta-substitute :on-objectives t :path (1))
   (rewrite beta-substitute-all :on-objectives t :path nil)
   (rewrite (objective-or-split 1) :on-objectives t :path (1 3 3))
   (rewrite macro-collapse :on-objectives t :path (1 3 3 1))
   (commit)
   (rewrite split-or-all :on-objectives nil :path (1))
   (rewrite macro-expand :on-objectives nil :path (1 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (qed)
   (commit)
   (rewrite macro-expand :on-objectives nil :path (1 0))
   (rewrite beta-substitute-all :on-objectives nil :path nil)
   (qed)
   (commit)"

def plusSuccOk : Bool :=
  match Parser.Sexp.parseScript plusSuccTrace with
  | some acts => Replay.runOk Term.stdDefs acts
  | none => false

theorem plusSucc_passes : plusSuccOk = true := by native_decide

/-! ### Summary of verified examples

| Test                                              | Section              | Status |
|---------------------------------------------------|----------------------|--------|
| `*1* ≤ *int*`                                     | PPDP §4.1            | OK     |
| `*1* ≤ *int*` (parser-driven)                     | PPDP §4.1            | OK     |
| `plus(*succ* *int*)(*succ* *int*) ≤ *succ* *int*` | PPDP §4.2            | OK     |
| `*0* ≤ *int*`                                     | (variant of §4.1)    | OK     |
| `*1* ≤ OR(*1*, *2*)`                              | from `or.el`         | OK     |
| `*2* ≤ OR(*1*, *2*)`                              | from `or.el`         | OK     |
| `*0* ≤ OR(*1*, *0*)`                              | (variant)            | OK     |
| `OR(*1*, *2*) ≤ *int*`                            | from `or.el`         | OK     |
| `*true* ≤ *bool*`                                 | (Bool encoding)      | OK     |
| `*false* ≤ *bool*`                                | (Bool encoding)      | OK     |
| `*bool* ≤ OR(*true*, *false*)`                    | (Bool encoding)      | OK     |
| `top ≤ top`                                       | sanity (reflexivity) | OK     |
| `*bool* ≤ *bool*`                                 | sanity (reflexivity) | OK     |

Examples §4.3 (factorial), §4.4 (safediv), §4.5 (Syracuse) all share a
common reduction step (action ≈22 of the factorial trace) where the
artifact's `:desc` annotations claim a result containing `*mult*` as a
literal macroRef.  Reproducing that step faithfully would require porting
an implicit macro-collapse heuristic that our verbatim port of
`beta-substitute-all-in-term` does not implement — ports of those
examples are deferred.
-/

end Examples
end Pss.Checker
