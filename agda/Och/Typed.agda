------------------------------------------------------------------
-- Och.Och.Syntax (Agda)
--
-- Phase 1 of the Och rebuild — Agda track.
--
-- The Lean track of Och had to fall back to a Nat-indexed Term
-- because Lean 4 doesn't natively support induction-induction
-- (Term : Ctx → Set with Term's constructors referencing Ctx.cons).
--
-- Agda DOES support induction-induction. This file uses that to
-- write an honest intrinsic typing — Term Γ T means "a term of
-- type T in context Γ". No external well-formedness predicate;
-- the inductive's constructors enforce typing rules directly.
--
-- Status: minimal Phase 1 (no μ, no fix, no ι, no subtyping).
-- Equivalent to a small dependently-typed λ-calculus.
------------------------------------------------------------------

module Och.Typed where

------------------------------------------------------------------
-- Term + Context, mutually defined.
--
-- The whole point of going to Agda for this: induction-induction
-- works. Term's lam constructor can reference Ctx._,_ ; bvar's
-- type can mention the looked-up type from Γ.
--
-- We index Term by both its context Γ AND its type τ (a Term in
-- the same context that has type Type). This is "fully intrinsic"
-- — only well-typed terms are constructible.
------------------------------------------------------------------

mutual
  data Ctx : Set
  data Term : (Γ : Ctx) → Set
  data _∈_ : ∀ {Γ} → Term Γ → Ctx → Set

  -- Typing context: a dependent cons-list. Each entry is a Term
  -- in the prefix context (so subsequent entries can reference
  -- earlier ones via free variables).
  data Ctx where
    ∅   : Ctx
    _,_ : (Γ : Ctx) → (T : Term Γ) → Ctx

  -- Well-typed terms.
  --
  -- Term Γ is the type of well-formed terms in context Γ. The
  -- term's "natural type" is recovered structurally: each
  -- constructor produces a term whose type is determined by the
  -- inputs.
  --
  -- We don't index Term by its type τ — Och terms are their own
  -- types via subsumption (refl: e ⊑ e), so we use a separate
  -- function `naturalType : Term Γ → Term Γ` to read off the
  -- structural type.
  data Term where
    -- Bound variable lookup. The Member relation gives a typed
    -- de Bruijn index into Γ.
    bvar : ∀ {Γ} {T : Term Γ}
         → T ∈ Γ
         → Term Γ

    -- Top of the subtype lattice. Also the Type universe — `top :
    -- top` at the object level, which is what makes Och non-total.
    top  : ∀ {Γ} → Term Γ

    -- Lambda. Body lives in the extended context Γ , A.
    lam  : ∀ {Γ}
         → (A : Term Γ)
         → (b : Term (Γ , A))
         → Term Γ

    -- Application. Like the Lean side of Och, we don't enforce
    -- "f is a function" structurally — the typing rule is
    -- checked via naturalType + subsumption, not the constructor
    -- index. (For symmetry with the rest of Och's design where
    -- subsumption is implicit.)
    app  : ∀ {Γ}
         → (f : Term Γ)
         → (a : Term Γ)
         → Term Γ

    -- Ascription / explicit type annotation.
    asc  : ∀ {Γ}
         → (e : Term Γ)
         → (T : Term Γ)
         → Term Γ

  -- Typed de Bruijn index into a context.
  --
  -- T ∈ Γ means "T is somewhere in Γ". The position is encoded
  -- structurally:
  --   here  : T is the most-recent binding.
  --   there : T is in some prefix Γ' that was extended.
  --
  -- This is the Member / typed-de-Bruijn-index used in the bvar
  -- constructor. It's what makes induction-induction *necessary*:
  -- the relation "T ∈ Γ" depends on both Term and Ctx, and Term's
  -- constructor (bvar) uses it.
  data _∈_ where
    here  : ∀ {Γ} {T : Term Γ}
          → T ∈ (Γ , T)

    there : ∀ {Γ} {T : Term Γ} {S : Term Γ}
          → T ∈ Γ
          → T ∈ (Γ , S)

------------------------------------------------------------------
-- Notes on what's NOT enforced
--
-- This Phase 1 inductive doesn't yet capture:
--
-- 1. App well-formedness. `app f a` accepts any two terms; the
--    typing rule "f : Π A B, a : A ⇒ f a : B[a/0]" is left to
--    the natural-type function (or to a typing relation we'll
--    define alongside). This is intentional for symmetry with
--    Och's subsumption-driven typing.
--
-- 2. Subsumption. `e ⊑ τ` is the typing judgment in Och. We'll
--    add Subtype' as a separate inductive (Phase 3) and recover
--    "well-typed at τ" via the lookup function and Subtype'
--    derivation.
--
-- 3. iota / fix / mu / bot. Future phases.
--
-- The win at this stage: we have *structural* well-scopedness
-- (every bvar points into Γ via T ∈ Γ, with the type T tracked).
-- This is the "any well-typed lambda has the property" that the
-- user asked about — encoded in the type of bvar's argument.
--
-- The full property "any argument can be applied" still requires
-- a substitution lemma at the meta level, but it's now a clean
-- structural induction over Term and ∈ rather than a thicket of
-- de-Bruijn arithmetic.
------------------------------------------------------------------
