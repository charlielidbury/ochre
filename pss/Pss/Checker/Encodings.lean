import Pss.Checker.Term
import Pss.Checker.MacroExpand

/-! # `Pss.Checker.Encodings` — Scott encodings of int / bool / arithmetic

Verbatim port of `pss/checker-artifact/terms/{int,bool}.el`.

We define the standard term-definition map used by the worked examples,
matching the artifact's `*term-definitions*` global state.

Loading order (mirrors the artifact's `(load "../terms/int.el")` after bool):
  bool  →  int  →  arithmetic  →  factorial / leq / syracuse
-/

namespace Pss.Checker
namespace Term

open Term

/-! ### Bool encoding -/

/-- `*true* := λ true-case ≤ top. λ false-case ≤ top. true-case` -/
def encTrue : Term :=
  .fun_ "true-case" .top
    (.fun_ "false-case" .top
      (.var "true-case"))

/-- `*false* := λ true-case ≤ top. λ false-case ≤ top. false-case` -/
def encFalse : Term :=
  .fun_ "true-case" .top
    (.fun_ "false-case" .top
      (.var "false-case"))

/-- `*bool* := OR(*true*, *false*)` -/
def encBool : Term :=
  .or [.macroRef "*true*", .macroRef "*false*"]

/-! ### Integers (Scott encoding) -/

/-- `*int* := y (λ self ≤ top. λ z ≤ top. λ s ≤ (λ n ≤ self. top). OR('z, 's 'self))` -/
def encInt : Term :=
  .yfix
    (.fun_ "self" .top
      (.fun_ "zero-case" .top
        (.fun_ "succ-case"
          (.fun_ "n" .top .top)
          (.or [.var "zero-case",
                .app (.var "succ-case") (.var "self")]))))

/-- `*0* := λ z ≤ top. λ s ≤ (λ n ≤ top. top). z` -/
def enc0 : Term :=
  .fun_ "zero-case" .top
    (.fun_ "succ-case" (.fun_ "n" .top .top)
      (.var "zero-case"))

/-- `*1* := successor of zero, fully unfolded` -/
def enc1 : Term :=
  .fun_ "zero-case" .top
    (.fun_ "succ-case" (.fun_ "n" .top .top)
      (.app (.var "succ-case") enc0))

/-- `*2* := successor of one, fully unfolded` -/
def enc2 : Term :=
  .fun_ "zero-case" .top
    (.fun_ "succ-case" (.fun_ "n" .top .top)
      (.app (.var "succ-case") enc1))

/-- `*succ* := λ n ≤ *int*. λ z ≤ top. λ s ≤ (λ n ≤ top. top). 's 'n` -/
def encSucc : Term :=
  .fun_ "n" (.macroRef "*int*")
    (.fun_ "zero-case" .top
      (.fun_ "succ-case" (.fun_ "n" .top .top)
        (.app (.var "succ-case") (.var "n"))))

/-! ### Arithmetic — `*plus*` (recursive, expanded) -/

/-- `*plus* := y (λ self ≤ (FUN a *int* (FUN b *int* *int*)).
                  λ m ≤ *int*. λ n ≤ *int*.
                    (m n) (λ a ≤ *int*. *succ* ((self a) n)))`

    This is the "expanded" form from `*plus-factory*` applied to its type
    argument; the artifact stores it pre-expanded under `*plus*`. -/
def encPlus : Term :=
  let plusType := .fun_ "a" (.macroRef "*int*")
                    (.fun_ "b" (.macroRef "*int*") (.macroRef "*int*"))
  .yfix
    (.fun_ "self" plusType
      (.fun_ "m" (.macroRef "*int*")
        (.fun_ "n" (.macroRef "*int*")
          (.app
            (.app (.var "m") (.var "n"))
            (.fun_ "a" (.macroRef "*int*")
              (.app (.macroRef "*succ*")
                (.app (.app (.var "self") (.var "a")) (.var "n"))))))))

/-! ### `*plus-factory*` — the abstract version of `*plus*` -/

def encPlusFactory : Term :=
  .fun_ "obj" .top
    (.yfix
      (.fun_ "self" (.var "obj")
        (.fun_ "m" (.macroRef "*int*")
          (.fun_ "n" (.macroRef "*int*")
            (.app
              (.app (.var "m") (.var "n"))
              (.fun_ "a" (.macroRef "*int*")
                (.app (.macroRef "*succ*")
                  (.app (.app (.var "self") (.var "a")) (.var "n")))))))))

/-! ### Multiplication — `*mult*` and `*mult-factory*` -/

def encMult : Term :=
  let multType := .fun_ "a" (.macroRef "*int*")
                    (.fun_ "b" (.macroRef "*int*") (.macroRef "*int*"))
  .yfix
    (.fun_ "self" multType
      (.fun_ "m" (.macroRef "*int*")
        (.fun_ "n" (.macroRef "*int*")
          (.app
            (.app (.var "m") (.macroRef "*0*"))
            (.fun_ "a" (.macroRef "*int*")
              (.app (.app (.macroRef "*plus*") (.var "n"))
                (.app (.app (.var "self") (.var "a")) (.var "n"))))))))

def encMultFactory : Term :=
  .fun_ "obj" .top
    (.yfix
      (.fun_ "self" (.var "obj")
        (.fun_ "m" (.macroRef "*int*")
          (.fun_ "n" (.macroRef "*int*")
            (.app
              (.app (.var "m") (.macroRef "*0*"))
              (.fun_ "a" (.macroRef "*int*")
                (.app (.app (.macroRef "*plus*") (.var "n"))
                  (.app (.app (.var "self") (.var "a")) (.var "n")))))))))

/-! ### Factorial -/

def encFactFactory : Term :=
  .fun_ "obj" .top
    (.yfix
      (.fun_ "self" (.var "obj")
        (.fun_ "n" (.macroRef "*int*")
          (.app
            (.app (.var "n") (.macroRef "*1*"))
            (.fun_ "a" (.macroRef "*int*")
              (.app (.app (.macroRef "*mult*") (.var "n"))
                (.app (.var "self") (.var "a"))))))))

def encFact : Term :=
  .app encFactFactory
    (.fun_ "a" (.macroRef "*int*") (.macroRef "*int*"))

/-! ### Syracuse (placeholder primitives) -/

def encIsOne : Term := .fun_ "n" (.macroRef "*int*") (.macroRef "*bool*")
def encIsEven : Term := .fun_ "n" (.macroRef "*int*") (.macroRef "*bool*")
def encDiv : Term :=
  .fun_ "n" (.macroRef "*int*")
    (.fun_ "m" (.macroRef "*int*") (.macroRef "*int*"))
def enc3 : Term :=
  .fun_ "zero-case" .top
    (.fun_ "succ-case" (.fun_ "n" .top .top)
      (.app (.var "succ-case") enc2))

def encSyracuseFactory : Term :=
  .fun_ "obj" .top
    (.yfix
      (.fun_ "self" (.var "obj")
        (.fun_ "n" (.macroRef "*int*")
          (.app
            (.app (.app (.macroRef "*isOne*") (.var "n")) (.macroRef "*1*"))
            (.app
              (.app (.app (.macroRef "*isEven*") (.var "n"))
                (.app (.var "self")
                  (.app (.app (.macroRef "*div*") (.var "n")) (.macroRef "*2*"))))
              (.app (.var "self")
                (.app (.macroRef "*succ*")
                  (.app (.app (.macroRef "*mult*") (.macroRef "*3*")) (.var "n")))))))))

/-! ### The standard definition map -/

/-- The full term-definitions alist used by the worked examples.

    Definitions are listed in **reverse** of the artifact's order so that
    `lookup` (which reads left-to-right) finds the most recent definition
    first — exactly what the Lisp `assoc` does on `push`-built alists. -/
def stdDefs : Defs :=
  -- Order matters for `Defs.reverseLookup`: earlier entries take priority.
  -- We mirror the artifact's defining order: bool first, then int, etc.
  -- The push-based alist ends up with the *last* defined first; we
  -- replicate that by listing in reverse-definition-order.
  [ ("*syracuse-factory*", encSyracuseFactory),
    ("*3*", enc3),
    ("*div*", encDiv),
    ("*isEven*", encIsEven),
    ("*isOne*", encIsOne),
    ("*fact*", encFact),
    ("*fact-factory*", encFactFactory),
    ("*mult*", encMult),
    ("*mult-factory*", encMultFactory),
    ("*plus*", encPlus),
    ("*plus-factory*", encPlusFactory),
    ("*succ*", encSucc),
    ("*2*", enc2),
    ("*1*", enc1),
    ("*0*", enc0),
    ("*int*", encInt),
    ("*bool*", encBool),
    ("*false*", encFalse),
    ("*true*", encTrue) ]

end Term
end Pss.Checker
