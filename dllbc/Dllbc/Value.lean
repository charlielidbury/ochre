import Dllbc.Syntax

/-!
# DLLBC Values and Environment (§2)

The runtime value tree and the environment Ω.

A `Val` is a constructor tree plus three ownership-tracking forms (doc §0):

  * `bot` (⊥) — the *vacant slot*: not a value of any type, the absence of
    one. Every read-shaped rule excludes it, so a second use of a moved
    variable is simply stuck.
  * `loanM ℓ` — a **loan marker**: "something is owed here". Parked where a
    borrowed value used to sit; excluded from every read rule until ended.
  * `borrowM ℓ payload` — a **mutable borrow**: ownership of the payload
    subtree, tagged with the loan id ℓ that ties it back to its marker.

The environment Ω maps variables to values. It is insertion-ordered and
slots are **overwritten in place, never removed** — matching the doc's
traces, where a moved-out slot becomes ⊥ and stays present.

We also provide, for the proof phase and for later milestones (σ's, joins):
a pretty-printer shaped like the doc's trace comments, and a canonical
renumbering of loan ids by deterministic traversal order so two environments
compare equal up to ℓ-renaming.
-/

namespace Dllbc

/-- Runtime value tree.

    `ctor` is a declared/anonymous constructor applied to argument values.
    `bot`/`loanM`/`borrowM` are the ownership machinery of §0. `sym σ` is a
    **symbolic value** (§3.2): an unknown value of the borrow-free
    (*unrestricted*) fragment — a snapshot the checker knows the type of but
    not the value of. Because snapshots are unrestricted, a `sym` never
    contains or hides borrows or loan markers: it is a leaf, it moves like any
    owned value, and `drop` discards it. (No σ-context/types yet — those
    arrive with the pure layer; here σ is just a fresh id.) -/
inductive Val where
  | ctor    : String → List Val → Val
  | bot     : Val
  | loanM   : Nat → Val
  | borrowM : Nat → Val → Val
  | sym     : Nat → Val
  -- Pure fragment (§4): types are terms of universe sort, and the borrow-free
  -- ("pure") fragment is an ordinary tiny type theory whose formers live in
  -- `Val` too, so a pure value (a type, a stuck neutral, a λ) is a first-class
  -- runtime value. Pure binders use de Bruijn indices (`pvar`), managed by the
  -- pure substitution in `Pure.lean`; runtime var ids, σ ids and ℓ ids are
  -- globally named and untouched by it.
  | pvar    : Nat → Val              -- pure de Bruijn variable (bound by lam/pi/sigmaT)
  | type    : Val                    -- the single universe (type-in-type)
  | pi      : Val → Val → Val        -- Π (dom) (cod); cod binds var 0
  | sigmaT  : Val → Val → Val        -- Σ (fst-type) (snd-type); snd binds var 0
  | lam     : Val → Val → Val        -- λ (dom) (body); body binds var 0
  | app     : Val → Val → Val        -- application (a redex, or a stuck neutral spine)
  | const   : String → Val           -- a built-in constant: a recursor or a type former
  -- The identity type `Id A a b` (§10): the v0 basis's one genuine indexed
  -- family. Its constructor is `Refl` (a nullary `ctor "Refl" []` whose type
  -- `Id A a a` determines the endpoints); eliminated by the constants `j`
  -- (Paulin-Mohring J) and `k` (Streicher K).
  | idT     : Val → Val → Val → Val  -- Id (type) (lhs) (rhs); no binders
  /-- `⇝τ` — the comptime binder-mode marker on a λ/Π domain (combining-fns §6;
      see `Term.cmpT`). Reflected from the term form so that ⇒'s application
      rules can read a *value* callee's binder modes; **invisible to `beq`**, and
      therefore to `convert` and every comptime judgment above it, because §6's
      "case is inert under ⇝" is a claim this calculus should not be able to
      violate by accident. -/
  | cmpT    : Val → Val
  /-- **A runtime function value** (combining-fns §7 cost 2, M26-C): the value a
      `Term.lamR` evaluates to — named binders and a suspended *body*.

      It carries a `Term`, which no other `Val` does, and the reason is the same
      one that forces `lamR`'s named binders: a body is not a value and cannot be
      reflected into one. So a transparent runtime function is a *suspension* —
      a body plus the names it will bind — and applying it is `readR` on that
      body under a fresh frame, not `substPure` into a `Val`.

      It is CLOSED (checked at formation), which is what lets it be a leaf for
      every traversal below: no loans, no σ's, no state markers, nothing to
      renumber. `ih` is exactly this shape (§7 cost 2's "the boring kind").

      **AND ITS BINDERS STAY UNTYPED, where `Term.lamR`'s became annotated (M27).**
      The asymmetry is ratified and is the erasure principle rather than an
      oversight: `readR` drops the domains at the moment it forms this value.
      Types exist here for one consumer, the seal, and a seal happens at FORMATION
      with the annotated term in hand — after that the executing machine binds and
      runs, and never converts. A value that carried its domains would be a second
      copy of a contract nothing downstream reads. The symmetric change would look
      tidier and would be wrong. -/
  | rfn     : List Var → Term → Val
deriving Inhabited

namespace Val

/-! Structural equality on values. Written by hand (mutually with the list
    case) because the `List Val` nesting defeats the `deriving BEq` handler;
    still total — `beq` recurses on subterms, `beqList` on the list tail. -/
mutual
  def beq : Val → Val → Bool
    | .ctor n1 a1, .ctor n2 a2 => n1 == n2 && beqList a1 a2
    | .bot,        .bot        => true
    | .loanM x,    .loanM y    => x == y
    | .borrowM x p, .borrowM y q => x == y && beq p q
    | .sym x,      .sym y       => x == y
    | .pvar x,     .pvar y      => x == y
    | .type,       .type        => true
    | .pi d1 c1,   .pi d2 c2    => beq d1 d2 && beq c1 c2
    | .sigmaT d1 c1, .sigmaT d2 c2 => beq d1 d2 && beq c1 c2
    | .lam d1 b1,  .lam d2 b2   => beq d1 d2 && beq b1 b2
    | .app f1 a1,  .app f2 a2   => beq f1 f2 && beq a1 a2
    | .const x,    .const y     => x == y
    | .idT a1 b1 c1, .idT a2 b2 c2 => beq a1 a2 && beq b1 b2 && beq c1 c2
    -- **Mode-blind, deliberately** (§6, "case is inert under ⇝"). `convert` is
    -- `nfV a == nfV b`, so unwrapping here is what makes the whole comptime layer
    -- unable to observe a binder's mode — congruence, `hasType`, the audit, the
    -- pure lift. Three arms rather than a traversal, so it costs nothing.
    --
    -- The alternative — modes part of type identity — was rejected on the
    -- calculus's own evidence: the machine builds recursor premise types
    -- (`natRec`'s `Π (k : Nat) → Π (ih : P k) → P (S k)`) in Lean with no modes,
    -- and `pure{}`'s motive binders are capitalized by long-standing convention
    -- (`λ (P : …)`, `λ (A : Type)`). Under a mode-sensitive equality every one of
    -- those would have to agree on a mode that ⇝ has no use for. Modes exist to
    -- route ⇒'s arguments and to fence its bodies; ⇝ is the room where the
    -- distinction was never meant to reach.
    | .cmpT a,     .cmpT b     => beq a b
    | .cmpT a,     b           => beq a b
    | a,           .cmpT b     => beq a b
    -- Syntactic, on binder names AND body: a runtime function value is a
    -- suspension, so there is no reduction to compare it up to. Two `lamR`s that
    -- differ only in binder ids are different values here — which is correct,
    -- because the ids are what their bodies reach Ω through.
    | .rfn xs a,   .rfn ys b   => xs == ys && a == b
    | _,           _           => false
  -- Both sides: the mode-blind arms peel a `cmpT` from one side only.
  termination_by v w => sizeOf v + sizeOf w
  def beqList : List Val → List Val → Bool
    | [],      []      => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _,       _       => false
  termination_by vs ws => sizeOf vs + sizeOf ws
end

instance : BEq Val := ⟨Val.beq⟩

/-- `Z`, the numeral zero. -/
def zero : Val := .ctor "Z" []
/-- Successor. -/
def succ (v : Val) : Val := .ctor "S" [v]
/-- Church-style `Nat` numeral abbreviation (doc: "Numerals abbreviate `Nat`"). -/
def nat : Nat → Val
  | 0 => zero
  | n + 1 => succ (nat n)
/-- The empty list. -/
def nil : Val := .ctor "Nil" []
/-- List cons. -/
def cons (h t : Val) : Val := .ctor "Cons" [h, t]

/-! ## Pretty-printing (doc-trace shaped) -/

/-! Render a value like the doc's trace comments: `loanₘ ℓ0`,
    `borrowₘ ℓ0 (S (S (S Z)))`, `Cons 3 Nil`, `⊥`. `prec` guards parens.
    Total (list helper `prettyArgs` handles the `List Val` nesting). -/
mutual
  def prettyPrec (prec : Nat) : Val → String
    | .bot => "⊥"
    | .sym σ => s!"σ{σ}"
    | .loanM ℓ => s!"loanₘ ℓ{ℓ}"
    | .borrowM ℓ p =>
      let s := "borrowₘ ℓ" ++ toString ℓ ++ " " ++ prettyPrec 1 p
      if prec > 0 then s!"({s})" else s
    -- ¶1.1's array forms, rendered the way the design note's traces read (the trace
    -- suite IS the test suite): an owned run as `[3, 1, 2]`, a carved node as
    -- `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ0⟩`.
    | .ctor "Arr" vs => "[" ++ prettyCommas vs ++ "]"
    | .ctor "§segs" segs => "Arr⟨" ++ prettySegs segs ++ "⟩"
    | .ctor "§seg" [c, b] => prettyPrec 1 c ++ " ▷ " ++ prettyPrec 0 b
    | .ctor name [] => name
    | .ctor name args =>
      let s := name ++ prettyArgs args
      if prec > 0 then s!"({s})" else s
    | .pvar k => s!"#{k}"
    | .type => "Type"
    | .const c => c
    | .cmpT τ => "⇝" ++ prettyPrec 1 τ
    | .pi d c =>
      let s := s!"Π{prettyPrec 1 d}. {prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    | .sigmaT d c =>
      let s := s!"Σ{prettyPrec 1 d}. {prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    | .lam d b =>
      let s := s!"λ{prettyPrec 1 d}. {prettyPrec 0 b}"
      if prec > 0 then s!"({s})" else s
    | .app f a =>
      let s := prettyPrec 0 f ++ " " ++ prettyPrec 1 a
      if prec > 0 then s!"({s})" else s
    | .idT _ a b =>
      let s := s!"Id {prettyPrec 1 a} {prettyPrec 1 b}"
      if prec > 0 then s!"({s})" else s
    | .rfn xs _ =>
      -- The binders, not the body: a rejection naming a function value wants to
      -- say WHICH function, and the body is a whole program.
      "λr(" ++ String.intercalate ", " (xs.map (·.name)) ++ "){…}"
  termination_by v => sizeOf v
  def prettyArgs : List Val → String
    | [] => ""
    | a :: as => " " ++ prettyPrec 1 a ++ prettyArgs as
  termination_by as => sizeOf as
  def prettyCommas : List Val → String
    | [] => ""
    | [a] => prettyPrec 0 a
    | a :: as => prettyPrec 0 a ++ ", " ++ prettyCommas as
  termination_by as => sizeOf as
  def prettySegs : List Val → String
    | [] => ""
    | [a] => prettyPrec 0 a
    | a :: as => prettyPrec 0 a ++ ", " ++ prettySegs as
  termination_by as => sizeOf as
end

/-- Doc-trace rendering of a value (top-level, no surrounding parens). -/
def pretty (v : Val) : String := prettyPrec 0 v

instance : ToString Val where
  toString v := pretty v

/-! ## Loan-id traversal, for canonical renumbering -/

/-! Loan ids occurring in `v`, in pre-order of first appearance
    (`borrowM ℓ` contributes ℓ before descending into its payload). The list
    helper keeps the recursion structural through the `List Val` nesting. -/
mutual
  def loanIds : Val → List Nat
    | .loanM ℓ => [ℓ]
    | .borrowM ℓ p => ℓ :: loanIds p
    | .ctor _ args => loanIdsList args
    | .bot => []
    | .sym _ => []
    | .pvar _ => []
    | .type => []
    | .const _ => []
    | .cmpT τ => loanIds τ
    | .rfn _ _ => []                                    -- closed: no loans to find
    | .pi d c => loanIds d ++ loanIds c
    | .sigmaT d c => loanIds d ++ loanIds c
    | .lam d c => loanIds d ++ loanIds c
    | .app d c => loanIds d ++ loanIds c
    | .idT a b c => loanIds a ++ loanIds b ++ loanIds c
  termination_by v => sizeOf v
  def loanIdsList : List Val → List Nat
    | [] => []
    | v :: vs => loanIds v ++ loanIdsList vs
  termination_by vs => sizeOf vs
end

/-! Replace each loan marker (`loanM ℓ` or `borrowM ℓ …`) whose ℓ is in `loans`
    with the pure de Bruijn `pvar` at ℓ's position in `loans` — the §6.2
    "suspension tree with holes": a captured borrow's payload rewritten as the
    backward function of the surrendered values. -/
mutual
  def loanToPvar (loans : List Nat) : Val → Val
    | .loanM ℓ => match loans.findIdx? (· == ℓ) with | some i => .pvar i | none => .loanM ℓ
    | .borrowM ℓ p =>
      match loans.findIdx? (· == ℓ) with | some i => .pvar i | none => .borrowM ℓ (loanToPvar loans p)
    | .ctor n args => .ctor n (loanToPvarList loans args)
    | v => v
  termination_by v => sizeOf v
  def loanToPvarList (loans : List Nat) : List Val → List Val
    | [] => []
    | v :: vs => loanToPvar loans v :: loanToPvarList loans vs
  termination_by vs => sizeOf vs
end

/-! Reflect a PURE `Term` into a `Val` (no monad, no Ω): the borrow-free fragment
    only — `var`/`deref`/runtime forms map to `⊥` (they never occur in a pure
    goal). Used by `Std.nfTerm` to normalize a §18 generalize goal so a computed
    subterm (an `eqb`-spine hidden in a `count`-unfolding) is exposed before
    `abstractOccurrences`. -/
mutual
  def Term.toValPure : Term → Val
    | .type => .type
    | .const c => .const c
    | .pvar k => .pvar k
    | .cmpT τ => .cmpT (Term.toValPure τ)
    | .pi d c => .pi (Term.toValPure d) (Term.toValPure c)
    | .sigmaT d c => .sigmaT (Term.toValPure d) (Term.toValPure c)
    | .lam d b => .lam (Term.toValPure d) (Term.toValPure b)
    | .app f a => .app (Term.toValPure f) (Term.toValPure a)
    | .idT a b c => .idT (Term.toValPure a) (Term.toValPure b) (Term.toValPure c)
    | .ctorApp n args => .ctor n (Term.toValPureList args)
    | .unit => .ctor "unit" []
    | _ => .bot                                          -- runtime forms: absent in pure goals
  termination_by t => sizeOf t
  def Term.toValPureList : List Term → List Val
    | [] => []
    | t :: ts => Term.toValPure t :: Term.toValPureList ts
  termination_by ts => sizeOf ts
end

/-! Does a value carry a STATE marker — a hole (`⊥`), a loan, or a borrow —
    anywhere in its tree? §3.2's knowledge/state invariant: a σ names ENTRY
    knowledge (a constructor shape true at entry, or an equation solution), never
    the present state of a slot. So a σ-substitution's replacement must be
    marker-free; a marker is state and belongs in an Ω tree, never substituted for
    a σ. Asserted at the substitution site (`refineSym`) so a regression that tries
    to substitute state is caught immediately, not layers downstream.

    It lives here rather than with `refineSym` because ¶1.1's array layer needs the
    same predicate for a second job: a segment body is **owned** exactly when it is
    marker-free, so a run with a hole or an element loan in it is not a carve
    candidate and does not merge with its neighbour. Both jobs are the same
    question — is this a value, or a record of who currently holds what. -/
mutual
  def hasStateMarker : Val → Bool
    | .bot => true
    | .loanM _ => true
    | .borrowM _ _ => true
    | .ctor _ args => hasStateMarkerList args
    | .pi d c | .sigmaT d c | .lam d c | .app d c => hasStateMarker d || hasStateMarker c
    | .idT a b c => hasStateMarker a || hasStateMarker b || hasStateMarker c
    | _ => false
  def hasStateMarkerList : List Val → Bool
    | [] => false
    | v :: vs => hasStateMarker v || hasStateMarkerList vs
end

/-! Symbolic ids occurring in `v`, in pre-order of first appearance. -/
mutual
  def symIds : Val → List Nat
    | .sym σ => [σ]
    | .borrowM _ p => symIds p
    | .ctor _ args => symIdsList args
    | .loanM _ => []
    | .bot => []
    | .pvar _ => []
    | .type => []
    | .const _ => []
    | .cmpT τ => symIds τ
    | .rfn _ _ => []                                    -- closed: no σ's to find
    | .pi d c => symIds d ++ symIds c
    | .sigmaT d c => symIds d ++ symIds c
    | .lam d c => symIds d ++ symIds c
    | .app d c => symIds d ++ symIds c
    | .idT a b c => symIds a ++ symIds b ++ symIds c
  termination_by v => sizeOf v
  def symIdsList : List Val → List Nat
    | [] => []
    | v :: vs => symIds v ++ symIdsList vs
  termination_by vs => sizeOf vs
end

/-! Rewrite every loan id `ℓ` to `fℓ ℓ` and every symbolic id `σ` to `fσ σ`
    (used by canonicalization, which renumbers both id spaces). -/
mutual
  def renumber (fℓ fσ : Nat → Nat) : Val → Val
    | .loanM ℓ => .loanM (fℓ ℓ)
    | .borrowM ℓ p => .borrowM (fℓ ℓ) (renumber fℓ fσ p)
    | .ctor n args => .ctor n (renumberList fℓ fσ args)
    | .bot => .bot
    | .sym σ => .sym (fσ σ)
    | .pvar k => .pvar k
    | .type => .type
    | .const c => .const c
    | .cmpT τ => .cmpT (renumber fℓ fσ τ)
    | .rfn xs b => .rfn xs b                            -- closed: nothing to renumber
    | .pi d c => .pi (renumber fℓ fσ d) (renumber fℓ fσ c)
    | .sigmaT d c => .sigmaT (renumber fℓ fσ d) (renumber fℓ fσ c)
    | .lam d b => .lam (renumber fℓ fσ d) (renumber fℓ fσ b)
    | .app f a => .app (renumber fℓ fσ f) (renumber fℓ fσ a)
    | .idT a b c => .idT (renumber fℓ fσ a) (renumber fℓ fσ b) (renumber fℓ fσ c)
  termination_by v => sizeOf v
  def renumberList (fℓ fσ : Nat → Nat) : List Val → List Val
    | [] => []
    | v :: vs => renumber fℓ fσ v :: renumberList fℓ fσ vs
  termination_by vs => sizeOf vs
end

end Val

/-! ## The environment Ω -/

/-- Ω: an insertion-ordered association list from variables to values. -/
abbrev Omega := List (Var × Val)

/-- A canonicalized environment for testing/comparison: display names paired
    with values whose loan ids have been renumbered to a canonical order. We
    keep the *name* (not the internal id) so expected environments can be
    written the way the doc's traces read. -/
abbrev Env := List (String × Val)

/-- First-occurrence-order dedup of a `Nat` list. `seen` accumulates the ids
    already emitted, so the recursion stays structural on the list. -/
def dedupNatGo (seen : List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if seen.contains x then dedupNatGo seen xs
    else x :: dedupNatGo (x :: seen) xs

/-- First-occurrence-order dedup of a `Nat` list. -/
def dedupNat (xs : List Nat) : List Nat := dedupNatGo [] xs

/-- Index of `x` in `xs` (0-based); `xs.length` if absent. -/
def natIndexOf (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if y == x then 0 else 1 + natIndexOf x ys

/-- Canonicalize Ω: renumber loan ids AND symbolic ids in first-appearance
    order across the whole environment (slot order, pre-order within each
    value), and project each variable to its display name. Two environments
    equal up to ℓ- and σ-renaming produce identical `Env`s. -/
def canonicalize (ω : Omega) : Env :=
  let ℓorder := dedupNat (ω.flatMap (fun kv => kv.2.loanIds))
  let σorder := dedupNat (ω.flatMap (fun kv => kv.2.symIds))
  ω.map (fun kv =>
    (kv.1.name, kv.2.renumber (fun ℓ => natIndexOf ℓ ℓorder) (fun σ => natIndexOf σ σorder)))

/-- Render Ω as a single doc-trace line, ℓ- and σ-canonicalized. -/
def prettyOmega (ω : Omega) : String :=
  let ℓorder := dedupNat (ω.flatMap (fun kv => kv.2.loanIds))
  let σorder := dedupNat (ω.flatMap (fun kv => kv.2.symIds))
  String.intercalate ", "
    (ω.map (fun kv =>
      s!"{kv.1.name} ↦ {(kv.2.renumber (fun ℓ => natIndexOf ℓ ℓorder) (fun σ => natIndexOf σ σorder)).pretty}"))

end Dllbc
