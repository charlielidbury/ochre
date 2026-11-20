import Ochr.Examples.Registry

/-!
# The rules trial: where values sit inside code, on every recorded state of the suite (compiled)

The question (the lead's point 2): can two convertible pieces of code whose embedded values the
decisions read differently arise, so that the model's runs of them differ? The decisions the run
reads at an embedded value are the reading of that value (`Decide.valueDecl`). This sweep records
every machine state of every example and case study (as `Sweep.lean` does: `located`,
`Config.recordStates`) and classifies every value written inside code anywhere in the state:

- in a sealed program's text: the text must have [Close]'s shape (`closeCall`, the only maker):
  cells `let c = u` or `let c = (u : T)`, then the head call `f(ā)` (head and non-borrow arguments
  embedded values, borrow arguments `&c`), alone, or followed by `peek(c)`, or bound to `r` with
  `*r := ℓ` / `peek(*r)` after it;
- in a closure's or Π-closure's code: only an inlined proof `(⋆ : T)` ([Capture]) or a domain or
  codomain of a stuck block's function (`closeBlock`'s `F_m`, types as values).

Anything else is reported with an example.

**Result** (2026-11-21, at e1af9662's checker): 76,568 states; 625,140 sealed programs, every one
[Close]-shaped; 68,500 closures and Π-closures, of which 72 (14 declarations) hold values in code
elsewhere, all in two more kinds of position: a stuck block function's binder type written with
its declared sort (`(h : (False : Prop))`), and a `J` block's statements (its type, endpoints and
motive: `J Nat σ0 0 MN (⋆ : …) t`). So values sit in code only at type and statement positions, and
in sealed programs at [Close]'s positions. Not built by default (about ten minutes).
-/

namespace Ochr.Meaning.Rules.ShapeSweep
open Ochr Ochr.Test Ochr.Registry

/-- A [Close] head call `f(ā)`: head and arguments embedded values or borrowed cells. -/
def isCloseCall : Term → Bool
  | .call (.val _) as true => as.all fun | .val _ | .borrow (.var _) => true | _ => false
  | _ => false

/-- What follows the cells in a [Close] text. -/
def isCloseBody : Term → Bool
  | t@(.call ..) => isCloseCall t
  | .seq c (.prim "peek" [.place (.var _)]) => isCloseCall c
  | .letIn _ c (.seq (.assign (.deref (.var 0)) (.val _)) (.prim "peek" [.place (.var _)])) => isCloseCall c
  | .letIn _ c (.prim "peek" [.place (.deref (.var 0))]) => isCloseCall c
  | _ => false

/-- A [Close] text: cells, then the body. -/
def isCloseText : Term → Bool
  | .letIn _ (.val _) rest | .letIn _ (.ascribe (.val _) (.val _)) rest =>
    isCloseText rest || isCloseBody (.letIn ⟨""⟩ (.val .unit) rest)
  | t => isCloseBody t

/-- Every `.val` written in closure code, classified: `true` when allowed. -/
partial def codeVals (allowed : Bool) : Term → List (Bool × Term)
  | t@(.val _) => [(allowed, t)]
  | .ascribe (.val .proof) (.val _) => []
  | .fix _ _ ds c _ b => (ds ++ [c]).flatMap dom ++ codeVals false b
  | .assign _ t | .succ t | .ref t => codeVals false t
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => codeVals false t ++ codeVals false u
  | .matchNat _ z s => codeVals false z ++ codeVals false s
  | .pi _ ds c => (ds ++ [c]).flatMap dom
  | .call f as _ => codeVals false f ++ as.flatMap (codeVals false)
  | .eq a b c | .id a b c => codeVals false a ++ codeVals false b ++ codeVals false c
  | .ctor _ _ _ ps as => ps.flatMap (codeVals false) ++ as.flatMap (codeVals false)
  | .prim _ as | .tind _ as => as.flatMap (codeVals false)
  | .matchInd _ _ as => as.flatMap (codeVals false ·.2)
  | _ => []
where
  /-- A domain or codomain: a type written as a value is allowed there (`F_m`). -/
  dom : Term → List (Bool × Term)
  | .val _ => []
  | t => codeVals false t

/-- All sub-values of a value, itself included, looking inside code at embedded values. -/
partial def subValues (v : Value) : List Value :=
  v :: match v with
  | .succ w | .tRef w | .borrow _ w | .gloan _ w => subValues w
  | .tEq A a b => subValues A ++ subValues a ++ subValues b
  | .clo cs t rd | .tPi cs t rd => cs.flatMap subValues ++ (termVals t).flatMap subValues ++ rd.flatMap (subValues ·.2)
  | .sealed t => (termVals t).flatMap subValues
  | .ind _ _ _ ps fs => ps.flatMap subValues ++ fs.flatMap subValues
  | .tInd _ fs => fs.flatMap subValues
  | _ => []
where
  termVals : Term → List Value
  | .val v => [v]
  | .assign _ t | .succ t | .ref t => termVals t
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => termVals t ++ termVals u
  | .matchNat _ z s => termVals z ++ termVals s
  | .pi _ ds c => ds.flatMap termVals ++ termVals c
  | .fix _ _ ds c _ b => ds.flatMap termVals ++ termVals c ++ termVals b
  | .call f as _ => termVals f ++ as.flatMap termVals
  | .eq a b c | .id a b c => termVals a ++ termVals b ++ termVals c
  | .ctor _ _ _ ps as => ps.flatMap termVals ++ as.flatMap termVals
  | .prim _ as | .tind _ as => as.flatMap termVals
  | .matchInd _ _ as => as.flatMap (termVals ·.2)
  | _ => []

/-- Every value of a state: Ω, stored types, the goal, the records. -/
def stateValues (st : MState) : List Value :=
  (st.env.toList.flatMap fun fr => fr.binds.toList.flatMap (fun b => b.val :: b.ty.toList) ++ fr.temps.toList)
    ++ st.absTy.toList ++ st.goal.toList ++ st.neutrals.map (·.1) ++ st.etaRefs.map (·.2) ++ st.refs.map (·.2)

structure Tally where
  states : Nat := 0
  sealed : Nat := 0
  badSealed : Nat := 0
  closures : Nat := 0
  badCode : Nat := 0
  examples : List String := []

def tally : Tally := Id.run do
  let cfg : Config := { recordStates := true }
  let mut t : Tally := {}
  for (bn, b) in programs ++ caseStudies do
    let r := runWith (some Prelude) bn b cfg 2000000 (located := true)
    for row in r.rows do
      for e in row.trace do
        match e with
        | .state _ _ _ st =>
          t := { t with states := t.states + 1 }
          for v in (stateValues st).flatMap subValues do
            match v with
            | .sealed tx =>
              t := { t with sealed := t.sealed + 1 }
              unless isCloseText tx do
                let ex := if t.examples.length < 6 then t.examples ++ [s!"{bn}.{row.name}: sealed {v}"] else t.examples
                t := { t with badSealed := t.badSealed + 1, examples := ex }
            | .clo _ tx _ | .tPi _ tx _ =>
              t := { t with closures := t.closures + 1 }
              let bad := (codeVals false tx).filter (!·.1)
              unless bad.isEmpty do
                let key := s!"{bn}.{row.name}"
                let ex := if t.examples.any (·.startsWith key) || t.examples.length ≥ 20 then t.examples
                  else t.examples ++ [s!"{key}: code {v} -- at {bad.map (fun (_, tm) => tm.pp [])}"]
                t := { t with badCode := t.badCode + 1, examples := ex }
            | _ => pure ()
        | _ => pure ()
  return t

#eval do
  let t := tally
  IO.println s!"states {t.states}; sealed {t.sealed} (not [Close]-shaped {t.badSealed}); closures {t.closures} (code with other values {t.badCode})\n{"\n".intercalate t.examples}"

end Ochr.Meaning.Rules.ShapeSweep
