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
  -- runtime value. Pure binders carry their SOURCE NAME (M30 step 2) and are
  -- looked up in the comptime environment `Pure.lean`'s evaluator carries;
  -- runtime var ids, σ ids and ℓ ids are a different namespace entirely.
  | pvar    : String → Val           -- pure variable occurrence, by name
  | type    : Val                    -- the single universe (type-in-type)
  | pi      : String → Val → Val → Val    -- Π (x : dom) → cod
  | sigmaT  : String → Val → Val → Val    -- Σ (x : fst-type) → snd-type
  | lam     : String → Val → Val → Val    -- λ (x : dom). body
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
  /-- **A comptime closure** (M30/NbE, `docs/nbe.md` §2): a λ/Π/Σ body stored *as
      written*, together with the comptime environment it was born in. It sits in
      the BODY position of `lam`/`pi`/`sigmaT`, which is what keeps every consumer
      that matches those three formers matching them unchanged — opening the binder
      is the thing that changes, from `substPure 0 a b` to `instBody x b a`.

      The environment is the whole environment in scope (nbe.md §3.1, resolved to
      option (a)): capture is a pointer, and in an immutable fragment the retention
      of unmentioned bindings is unobservable.

      **What may be in it is the invariant** (§3.2): knowledge only — no hole (⊥),
      no loan marker, no borrow value, no runtime slot reference. Under substitution
      that held by construction, because there was no environment for state to sit
      in; here it is a rule someone maintains, which is why `capturedMarkers` below
      exists to be run over the corpus rather than trusted.

      **Keyed by NAME since M30 step 2**, and prepending is the whole of what
      shadowing is: `λ (x : τ). λ (x : υ). x` extends the same key twice and the
      lookup finds the inner binding, with no index anywhere to renumber. The
      `lvl` former that used to sit below this one is gone with the indices —
      `readback` now opens a binder at a fresh NAME (`readbackName`), and a name
      is already a `pvar`, so the second variable former earned its keep only
      while the two read back by different arithmetic. -/
  | closure : List (String × Val) → Val → Val
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
    -- Binder NAMES are compared. That is not up-to-α, and it does not need to be:
    -- `convert` is `nfV a == nfV b`, and readback renames every binder it opens to
    -- `readbackName ⟨its level⟩` — so two α-variant functions arrive here as the
    -- SAME tree and everything else that reaches this function is comparing values
    -- that came out of the same normalizer. An α-insensitive `beq` would be the
    -- wrong repair anyway: it would make `λ (x : τ). x` equal `λ (y : τ). x`.
    | .pi x d1 c1,   .pi y d2 c2    => x == y && beq d1 d2 && beq c1 c2
    | .sigmaT x d1 c1, .sigmaT y d2 c2 => x == y && beq d1 d2 && beq c1 c2
    | .lam x d1 b1,  .lam y d2 b2   => x == y && beq d1 d2 && beq b1 b2
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
    -- and `prog{}`'s motive binders are capitalized by long-standing convention
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
    -- STRUCTURAL, and the deviation from "equality never traverses a closure"
    -- (nbe.md Q5) is deliberate and unreachable. That policy is a claim about
    -- CONVERSION, and `convert` is `nfV a == nfV b` — it reads back first, so no
    -- closure ever arrives here through it. What is left is the incidental
    -- comparisons (Ω canonicalization, `abstractInto`'s target test), where a
    -- literal env-and-body match is a sound under-approximation: two structurally
    -- equal closures ARE equal, and the converse failure cannot be observed by a
    -- judgment, only by a comparison that should have gone through readback.
    | .closure ρ1 b1, .closure ρ2 b2 => beqEnv ρ1 ρ2 && beq b1 b2
    | _,           _           => false
  -- Both sides: the mode-blind arms peel a `cmpT` from one side only.
  termination_by v w => sizeOf v + sizeOf w
  def beqList : List Val → List Val → Bool
    | [],      []      => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _,       _       => false
  termination_by vs ws => sizeOf vs + sizeOf ws
  def beqEnv : List (String × Val) → List (String × Val) → Bool
    | [],      []      => true
    | (a, x) :: xs, (b, y) :: ys => a == b && beq x y && beqEnv xs ys
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
    -- A pure variable prints as its NAME (M30 step 2). `#` is kept as the sigil
    -- so a rejection still says at a glance which namespace a variable is from,
    -- which was the whole job `#0` was doing.
    | .pvar x => s!"#{x}"
    | .type => "Type"
    | .const c => c
    | .cmpT τ => "⇝" ++ prettyPrec 1 τ
    | .pi x d c =>
      let s := s!"Π({x} : {prettyPrec 1 d}). {prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    | .sigmaT x d c =>
      let s := s!"Σ({x} : {prettyPrec 1 d}). {prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    | .lam x d b =>
      let s := s!"λ({x} : {prettyPrec 1 d}). {prettyPrec 0 b}"
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
    -- The body, not the environment — the `.rfn` precedent read the other way
    -- round. A closure's body is what it MEANS; its captured environment is how it
    -- gets there, and printing every binding in scope at every λ would bury the
    -- one line a rejection is trying to say.
    | .closure _ b => "clo{" ++ prettyPrec 0 b ++ "}"
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
    | .closure _ _ => []                                -- §3.2: no loans in a captured env
    | .pi _ d c => loanIds d ++ loanIds c
    | .sigmaT _ d c => loanIds d ++ loanIds c
    | .lam _ d c => loanIds d ++ loanIds c
    | .app d c => loanIds d ++ loanIds c
    | .idT a b c => loanIds a ++ loanIds b ++ loanIds c
  termination_by v => sizeOf v
  def loanIdsList : List Val → List Nat
    | [] => []
    | v :: vs => loanIds v ++ loanIdsList vs
  termination_by vs => sizeOf vs
end

-- (`loanToPvar` — §6.2's "suspension tree with holes", a captured borrow's payload
-- rewritten as the backward function of the surrendered values, by mapping each
-- loan marker to the de Bruijn `pvar` at its position in a list — was deleted in
-- M30 step 2. It had no caller: declared `back`s went in M27-δ and took its only
-- one with them, and it was the last thing in this file that treated a `pvar` as a
-- POSITION. Under names its signature would have had to invent a name per loan id,
-- which is a design decision, and making one for a dead function is how a dead
-- function survives another five milestones.)

-- (`Term.toValPure` — the monad-free reflection of a pure `Term` — lives in
-- `Pure.lean` since M29 α. `let` is a form of the pure fragment now, and reading
-- one is β, which needs `shiftPure`; that is declared there, so the reflection
-- that uses it has to be below it.)

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
    | .app d c => hasStateMarker d || hasStateMarker c
    | .pi _ d c | .sigmaT _ d c | .lam _ d c => hasStateMarker d || hasStateMarker c
    | .idT a b c => hasStateMarker a || hasStateMarker b || hasStateMarker c
    | _ => false
  def hasStateMarkerList : List Val → Bool
    | [] => false
    | v :: vs => hasStateMarker v || hasStateMarkerList vs
end

/-- The §3.2 capture guard's question, asked of an ENVIRONMENT: does any binding
    hold state? Named separately from `hasStateMarkerList` because the environment
    is name-keyed and the values are what the invariant is about. -/
def hasStateMarkerEnv : List (String × Val) → Bool
  | [] => false
  | (_, v) :: ρ => hasStateMarker v || hasStateMarkerEnv ρ

/-! **The capture assertion of nbe.md §3.2, as instrumentation** (M30).

    §3.2 promotes "a mathematical λ closes over copyable knowledge" from accident
    to asserted invariant, and says to assert it at closure formation "the same way
    `refineSym` asserts it at substitution". The two sites are not equally
    affordable, and pretending otherwise would be the wrong reading:

      * `refineSym` fires once per solved σ and lives in `M`, so it throws.
      * closure formation fires at every λ *evaluation* — the innermost loop of the
        comptime fragment — and `eval` is a pure total function with no monad to
        throw into. A guard there is a marker traversal per β.

    So the assertion is carried out the way the FIRST site's zero-violations claim
    was actually established: as a whole-corpus instrumentation pass. This returns
    every offending captured environment in a value; the harness runs it over every
    state the corpus reaches and the answer is expected to be empty. What stays
    permanently is the assertion at the one site where a closure enters *persistent*
    state — the sealed contracts of §4.3 — which is rare, is in `M`, and is exactly
    parallel to `refineSym`.

    Descends through the body too, since a closure's body may itself contain λs. -/
mutual
  def capturedMarkers : Val → List Val
    | .closure ρ b =>
      (if hasStateMarkerEnv ρ then [Val.closure ρ b] else []) ++ capturedMarkersEnv ρ ++ capturedMarkers b
    | .ctor _ args => capturedMarkersList args
    | .borrowM _ p => capturedMarkers p
    | .cmpT τ => capturedMarkers τ
    | .app d c => capturedMarkers d ++ capturedMarkers c
    | .pi _ d c | .sigmaT _ d c | .lam _ d c => capturedMarkers d ++ capturedMarkers c
    | .idT a b c => capturedMarkers a ++ capturedMarkers b ++ capturedMarkers c
    | _ => []
  termination_by v => sizeOf v
  def capturedMarkersList : List Val → List Val
    | [] => []
    | v :: vs => capturedMarkers v ++ capturedMarkersList vs
  termination_by vs => sizeOf vs
  def capturedMarkersEnv : List (String × Val) → List Val
    | [] => []
    | (_, v) :: ρ => capturedMarkers v ++ capturedMarkersEnv ρ
  termination_by ρ => sizeOf ρ
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
    -- DESCENDS — the deviation §6.2 demands. σ's genuinely live inside captured
    -- environments (a sealed contract's entry snapshot is one), and both halves
    -- matter: the env holds the σ's the body was closed over, the body holds the
    -- ones written into it. Omitting either would leave a σ that refinement can
    -- reach (`substSym` descends) but canonicalization cannot see, and the two
    -- disagreeing is how an α-equal pair of states stops comparing equal.
    | .closure ρ b => symIdsEnv ρ ++ symIds b
    | .pi _ d c => symIds d ++ symIds c
    | .sigmaT _ d c => symIds d ++ symIds c
    | .lam _ d c => symIds d ++ symIds c
    | .app d c => symIds d ++ symIds c
    | .idT a b c => symIds a ++ symIds b ++ symIds c
  termination_by v => sizeOf v
  def symIdsList : List Val → List Nat
    | [] => []
    | v :: vs => symIds v ++ symIdsList vs
  termination_by vs => sizeOf vs
  def symIdsEnv : List (String × Val) → List Nat
    | [] => []
    | (_, v) :: ρ => symIds v ++ symIdsEnv ρ
  termination_by ρ => sizeOf ρ
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
    | .pvar x => .pvar x
    | .type => .type
    | .const c => .const c
    | .cmpT τ => .cmpT (renumber fℓ fσ τ)
    | .rfn xs b => .rfn xs b                            -- closed: nothing to renumber
    -- DESCENDS, paired with `symIds` above: canonicalization reads the σ order off
    -- one traversal and applies it with the other, so a σ visible to the first and
    -- untouched by the second would be renumbered out of existence.
    | .closure ρ b => .closure (renumberEnv fℓ fσ ρ) (renumber fℓ fσ b)
    | .pi x d c => .pi x (renumber fℓ fσ d) (renumber fℓ fσ c)
    | .sigmaT x d c => .sigmaT x (renumber fℓ fσ d) (renumber fℓ fσ c)
    | .lam x d b => .lam x (renumber fℓ fσ d) (renumber fℓ fσ b)
    | .app f a => .app (renumber fℓ fσ f) (renumber fℓ fσ a)
    | .idT a b c => .idT (renumber fℓ fσ a) (renumber fℓ fσ b) (renumber fℓ fσ c)
  termination_by v => sizeOf v
  def renumberList (fℓ fσ : Nat → Nat) : List Val → List Val
    | [] => []
    | v :: vs => renumber fℓ fσ v :: renumberList fℓ fσ vs
  termination_by vs => sizeOf vs
  def renumberEnv (fℓ fσ : Nat → Nat) : List (String × Val) → List (String × Val)
    | [] => []
    | (x, v) :: ρ => (x, renumber fℓ fσ v) :: renumberEnv fℓ fσ ρ
  termination_by ρ => sizeOf ρ
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
