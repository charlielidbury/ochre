------------------------------------------------------------------
-- Och.Och.Syntax (Agda)
--
-- Untyped abstract syntax tree for Och.
--
-- This is the input to the type-checker — what a parser or surface
-- macro produces. Variables are de Bruijn indices (Nat). No
-- well-formedness invariants beyond "valid AST shape": bvars may
-- be out of scope, applications may be ill-typed, etc.
--
-- The intrinsically-typed counterpart is `Och.Typed`, which
-- builds Term + Ctx + (T ∈ Γ) via induction-induction. The
-- type-checker (later phase) is the function
-- `check : Syntax → Maybe (∃ Γ T. Term Γ T)`.
--
-- Mirrors `lean/Och/Syntax.lean`'s `Expr` constructor set, except:
--   * no `letE` (sugar for `(λ_. body) val`); add later if needed
--   * no `μ` yet
------------------------------------------------------------------

module Och.Syntax where

open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------
-- Untyped AST.
--
-- A `Syntax` value is just a tree of constructor applications
-- with bvars as natural numbers. There's no claim that bvars are
-- in scope or that applications are well-typed — that's checked
-- by the type-checker (a later phase) which produces a
-- `Och.Typed.Term Γ T` from a `Syntax`.
------------------------------------------------------------------

data Syntax : Set where

  -- Bound variable: a de Bruijn index. May be out of scope; the
  -- type-checker rejects if so.
  bvar : Nat → Syntax

  -- Top of the subtype lattice. Also serves as the Type universe
  -- (there's no separate type-of-types hierarchy in Och — `top : top`
  -- at the object level, which is what makes Och non-total).
  top : Syntax

  -- Bottom of the subtype lattice. Empty type; satisfies `bot ⊑ e`
  -- for every `e` (the [S-BotL] declarative rule from paper.md §3.1).
  bot : Syntax

  -- Lambda. Domain annotation, body. Body's bvar 0 refers to
  -- the parameter.
  lam  : (A : Syntax) → (b : Syntax) → Syntax

  -- Application.
  app  : Syntax → Syntax → Syntax

  -- Ascription / explicit type annotation.
  asc  : (e : Syntax) → (T : Syntax) → Syntax

  -- ι A. b — iota / self-type binder (Cedille-style).
  -- Bound occurrence (the "self") is bvar 0 in b.
  -- Annotation A states the weak (non-self) type the value
  -- inhabits.
  iota : (A : Syntax) → (b : Syntax) → Syntax

  -- fix A. b — recursive binder.
  -- Bound occurrence (the recursive reference) is bvar 0 in b.
  -- Annotation A states the (non-recursive) type that b's
  -- unfolding inhabits at each step.
  fix  : (A : Syntax) → (b : Syntax) → Syntax

------------------------------------------------------------------
-- Notes
--
-- This Phase-1 file does no work — just the data type. Operations
-- (free-var counting, alpha-equivalence, pretty-printing, etc.)
-- live in companion modules. The type-checker that promotes
-- Syntax → Typed.Term lives in `Och.Check` (Phase 2+).
--
-- Naming convention: this file uses `Syntax` rather than `Expr`
-- (Lean Och) to make it clear we mean "raw user-facing surface"
-- — distinct from `Och.Typed.Term`, which is the well-typed
-- semantic representation.
------------------------------------------------------------------
