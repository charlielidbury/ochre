# `och{...}` Lean Macro for Expr Construction

## Problem

Building Och terms is extremely verbose and error-prone:

```lean
def dtrue : Expr := n
  (.mu "dtrue" dBool_n
    (.lam "P" (boolMotiveTy dBool_n)
      (.lam "t" (.app (.var "P") (.var "dtrue"))
        (.lam "f" .type
          (.var "t")))))
```

Tests are even worse:

```lean
example : concEval 100
  (.app (.app (.app (n dtrue) (.lam (n dBool) (n Nat_))) (n zero_)) (n one_))
  = some (n zero_) := by native_decide
```

This requires the intermediate `Named` type, manual `n` calls everywhere,
and the `indexOf` function silently returns 999 for unbound variables.

## Proposal

A Lean syntax macro `och{...}` that parses a human-readable term syntax and
expands directly to `Expr` (de Bruijn) at compile time.

### Syntax

```
term ::=
  | x                          -- variable (bound) or Lean-level splice (free)
  | $e                         -- explicit antiquotation: splice Lean Expr value
  | λx:term. term              -- lambda
  | μx:term. term              -- mu (self-reference)
  | (term : term)              -- ascription
  | term term                  -- application (left-associative)
  | Type                       -- universe
  | let x : term = term in term  -- let-binding (desugars to (λx:T. body) val)
  | (term)                     -- grouping
```

### Name Resolution

The macro maintains a binding context `ctx : List Name` tracking names
introduced by λ, μ, and let. When a bare name `x` is encountered:

1. **Bound variable**: If `x` is in `ctx`, emit `Expr.bvar i` where `i` is
   the de Bruijn index (position in `ctx`).
2. **Free reference**: If `x` is not in `ctx`, emit an antiquotation —
   resolve `x` as a Lean-level identifier of type `Expr` and splice it in.
   This is a compile-time error if `x` doesn't resolve to an `Expr`.

Step 2 means that `$` antiquotation is only needed when the Lean name
differs from what you'd write (e.g., qualified names, complex expressions).
Most of the time bare names just work:

```lean
-- dBool resolves to Std.dBool : Expr in scope
def not := och{ λb:dBool. b dBool dfalse dtrue }
```

If implicit resolution is too magical, a simpler design uses explicit `$`
for all free references:

```lean
def not := och{ λb:$dBool. b $dBool $dfalse $dtrue }
```

Either way, unbound variables that don't resolve are a **compile-time error**,
fixing the silent-999 bug in `indexOf`.

### Examples

**Definitions:**

```lean
def Bool := och{ λX:Type. λt:X. λf:X. X }
def true_ := och{ λX:Type. λt:X. λf:X. t }
def false_ := och{ λX:Type. λt:X. λf:X. f }

def not := och{ λb:$Bool. b $Bool $false_ $true_ }

def dBool := och{
  μ dBool:Type.
    let dtrue : dBool = μ dtrue:dBool. λP:(dBool → Type). λt:(P dtrue). λf:Type. t
    let dfalse : dBool = μ dfalse:dBool. λP:(dBool → Type). λt:Type. λf:(P dfalse). f
    λP:(dBool → Type). λt:(P dtrue). λf:(P dfalse). P dBool
}
```

**Tests:**

```lean
example : concEval 50 (och{ $dtrue $Bool $true_ $false_ }) = some true_ := by native_decide
example : subCheck 50 true_ Bool = true := by native_decide
```

### Arrow Syntax

For readability, `A → B` in type position could desugar to `λ_:A. B` (a
non-dependent function type). This is purely cosmetic:

```lean
-- These are equivalent:
och{ λP:(dBool → Type). ... }
och{ λP:(λ_:dBool. Type). ... }
```

### What This Eliminates

- **`Named` inductive type** — no longer needed
- **`toExpr` / `indexOf`** — de Bruijn indices computed by the macro
- **`n` function** — macro emits `Expr` directly
- **Silent 999 sentinel** — unbound names are compile errors
- **`_n` / `_e` naming conventions** — everything is just `Expr`

### Implementation

The macro is ~100-150 lines:

1. **Syntax declaration** (~20 lines): Register `och{...}` as a Lean syntax
   category with the grammar above.

2. **Macro expansion** (~80-100 lines): A recursive function
   `expand (ctx : List Name) (stx : Syntax) : MacroM Syntax` that pattern-matches
   on the syntax and emits `Expr` constructor calls. Lambda/mu/let extend
   `ctx`; variables look up their index in `ctx` or fall through to
   antiquotation.

3. **Arrow desugaring** (~10 lines): Rewrite `A → B` as `λ_:A. B` before
   the main expansion.

### Open Questions

- **Implicit vs explicit antiquotation**: Should free names automatically
  resolve against the Lean environment, or require explicit `$`? Implicit is
  more ergonomic but potentially surprising. Could start with explicit `$`
  and relax later.

- **Application parsing**: Left-associative application `f a b c` needs
  care in the syntax declaration to avoid ambiguity with Lean's own
  application syntax inside the `och{...}` block.

- **Notation for Std**: Once the macro exists, should Std definitions be
  rewritten to use it? Yes — that's the whole point. The definitions become
  readable and self-documenting.
