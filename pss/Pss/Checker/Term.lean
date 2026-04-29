/-! # `Pss.Checker.Term` — Extended PSS term language for the Pasquale & García-Pérez checker

This is the term grammar of the PPDP 2025 checker artifact, ported verbatim from
`pss/checker-artifact/`.  It is intentionally a **separate** datatype from
`Pss.Syntax.Term` so that the MPSS metatheory remains pristine.

The Lisp grammar from the artifact's `README.md`:
```
term ::= top
       | 'variable
       | (term term)
       | (FUN variable term term)
       | (OR term term)
       | (y term)
```

Plus an additional case for **macro references**: in the artifact, an unquoted
symbol such as `*int*` denotes a lookup into the global `*term-definitions*`
alist (see `macroexpand.el`).  We keep that as a separate constructor so the
replay interpreter can faithfully model `macro-expand-at-path` and
`macro-collapse-at-path`.

We also use a **named** representation (rather than locally-nameless) — this
matches the artifact's substitution algorithm in `reduction.el`, which is
shadowing-aware over named binders.
-/

namespace Pss.Checker

/-- Extended PSS term, mirroring the Emacs Lisp s-expression grammar. -/
inductive Term where
  /-- `top` — the universal type. -/
  | top : Term
  /-- `'x` — a quoted symbol, i.e. a variable reference. -/
  | var : String → Term
  /-- An unquoted symbol such as `*int*` — a macro reference resolved via the
      global term-definition map. -/
  | macroRef : String → Term
  /-- `(FUN x type body)` — lambda with bound variable `x`, type annotation
      `type`, and body `body`. -/
  | fun_ : (x : String) → (type : Term) → (body : Term) → Term
  /-- `(rator rand)` — application. -/
  | app : Term → Term → Term
  /-- `(y f)` — fixed point. -/
  | yfix : Term → Term
  /-- `(OR a₁ a₂ ...)` — variant with at least two alternatives in practice;
      we allow any non-empty list. -/
  | or : List Term → Term
  deriving Repr, Inhabited

namespace Term

/-- Decidable equality, defined manually so it can be `partial`-free. -/
def beq : Term → Term → Bool
  | .top, .top => true
  | .var x, .var y => x == y
  | .macroRef x, .macroRef y => x == y
  | .fun_ x t b, .fun_ y u c => x == y && beq t u && beq b c
  | .app a b, .app c d => beq a c && beq b d
  | .yfix a, .yfix b => beq a b
  | .or xs, .or ys => beqList xs ys
  | _, _ => false
where
  beqList : List Term → List Term → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _, _ => false

instance : BEq Term := ⟨beq⟩

/-- A path into a term is a list of zero-based indices, just as in
    `path-management.el`. -/
abbrev Path := List Nat

end Term

end Pss.Checker
