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

/-- **The state skeleton** (M32 R1, suspensions.md §2.3): what a store slot holds.

    `Term` does not grow state formers — giving it one would make a marker
    grammatically writable, which is the objection that killed the union-tree
    horizon. So the split runs the other way: **knowledge at rest is a canonical
    `Term`, and the store holds a SKELETON whose leaves are knowledge.**

      * `know t` — marker-free knowledge, canonical. A σ is `Term.sym σ`, a
        constructor tree is a `ctorApp` spine, a type is a type.
      * `node n args` — constructor structure that HOLDS state somewhere inside.
      * `bot`/`loanM`/`borrowM` — the ownership machinery of §0, unchanged.
      * `rfn` — a runtime function value (R2 folds it into a closure `(ρ, Term)`).

    The skeleton is exactly as large as the live state: `Val.ctor` below collapses
    a node whose children are all knowledge back to one `know` leaf, and state
    intruding (a borrow-mode match pushing field loans in, a carve) re-splits it.

    **The invariant this buys is type-enforced rather than guarded**: knowledge
    cannot contain state, because a `Term` has nowhere to put a marker. nbe.md
    §3.2's capture assertion and `Val.capturedMarkers`, the whole-corpus
    instrumentation that policed it, are gone — not because the rule was dropped
    but because the representation now states it. State containing knowledge (the
    leaves) stays possible, which is the correct asymmetry.

    The environment Ω maps variables to these. It is insertion-ordered and slots
    are **overwritten in place, never removed** — matching the doc's traces, where
    a moved-out slot becomes ⊥ and stays present. -/
inductive Val where
  | know    : Term → Val
  | node    : String → List Val → Val
  | bot     : Val
  | loanM   : Nat → Val
  | borrowM : Nat → Val → Val
  /-- **A runtime function value** (combining-fns §7 cost 2, M26-C): the value a
      `Term.lamR` evaluates to — named binders and a suspended *body*.

      It is CLOSED (checked at formation), which is what lets it be a leaf for
      every traversal below: no loans, no σ's, no state markers, nothing to
      renumber. `ih` is exactly this shape (§7 cost 2's "the boring kind").

      **Its binders stay UNTYPED, where `Term.lamR`'s are annotated** (M27): the
      erasure principle — `readR` drops the domains at the moment it forms this
      value, because types exist here for one consumer (the seal) and a seal
      happens at FORMATION with the annotated term in hand.

      It is `(∅, body)` — a closure whose environment is empty — and R2 is where
      it says so, folding into the one suspension form with `ρ` filled in. -/
  | rfn     : List Var → Term → Val
deriving Inhabited

namespace Val

/-! ## Building and viewing a constructor node

    `Val.ctor` is a smart constructor, not a former, and that is the whole of
    §2.3's "a value with no live markers collapses to a bare `Term` leaf": a node
    whose children are all knowledge IS knowledge, and is stored as one leaf.
    Every site that used to write `.ctor n args` goes on writing it and gets the
    collapse for free, which is also what keeps the trace suite's expected
    environments spelled as they were.

    **Two names are exempt, and they are the array layer's** (¶1.1). A `§segs`
    node is STATE — it records a carve, i.e. who currently holds which stretch —
    even when every body in it happens to be owned, and `hasType`'s
    extent-consistency check is stated on that state form. Collapsing it would put
    a carve history inside a knowledge leaf, where the ⇝ bridge (`arrFoldDeep`) is
    what is supposed to turn a carve into knowledge. `§seg` follows its parent so
    that segment navigation has one shape to match. -/

/-- Is this one of the reserved names a node may never collapse under?

    `§segs`/`§seg` are the array layer's carve (state, even when every body in it
    is owned). `§rec` is the RECURSOR SPINE OVER RUNTIME ARMS (§7 cost 5) — a
    `natRec P z s` whose step arm is a runtime λ. It is a function value with
    non-knowledge children, so it cannot be a `Term`; and it must not collapse
    even when its children happen to be knowledge, because the collapsed form
    would be a `ctorApp "§rec"` where the evaluator expects an application spine.
    `recSpine` below is what builds one, and it collapses to the honest spine
    itself rather than to a node. -/
def stateCtorName (n : String) : Bool :=
  n == "§segs" || n == "§seg" || n == "§rec"

/-- All-knowledge children, as terms. -/
def knowArgs? : List Val → Option (List Term)
  | [] => some []
  | .know t :: rest => (knowArgs? rest).map (t :: ·)
  | _ => none

/-- Build a constructor node, collapsing to a knowledge leaf when nothing in it
    is state. -/
def ctor (n : String) (args : List Val) : Val :=
  if stateCtorName n then .node n args
  else match knowArgs? args with
    | some ts => .know (.ctorApp n ts)
    | none => .node n args

/-- View a value as a constructor application, seeing THROUGH a collapsed leaf.
    The two-layer principle at its smallest: walk the skeleton, and where the
    skeleton has bottomed out into knowledge, keep walking at `Term` level. -/
def asCtor? : Val → Option (String × List Val)
  | .node n args => some (n, args)
  | .know (.ctorApp n ts) => some (n, ts.map Val.know)
  | _ => none

/-- The knowledge a value is, if it is knowledge. -/
def know? : Val → Option Term
  | .know t => some t
  | _ => none

/-- **A recursor spine, at the store**. All-knowledge arguments give the ordinary
    application spine, which is what a pure recursor is; an argument that is a
    runtime function value (a `.lamR`'s value — §7 cost 5's arms-as-bodies) forces
    the skeleton form, because there is no `Term` that could hold it. -/
def recSpine (c : String) (args : List Val) : Val :=
  match knowArgs? args with
  | some ts => .know (ts.foldl (fun acc t => Term.app acc t) (Term.const c))
  | none => .node "§rec" (.know (.const c) :: args)

/-- View one, seeing through the knowledge form. -/
def asRecSpine? : Val → Option (String × List Val)
  | .node "§rec" (.know (.const c) :: args) => some (c, args)
  | .know t =>
    let rec go : Term → Option (String × List Term)
      | .const c => some (c, [])
      | .app f a => (go f).map (fun p => (p.1, p.2 ++ [a]))
      | _ => none
    (go t).map (fun p => (p.1, p.2.map Val.know))
  | _ => none

/-- The store value a σ is: a knowledge leaf holding the reserved name. A former
    until M32 R1, a smart constructor after it — which is the honest shape, since
    a σ is knowledge like any other and the store's business with it is only that
    it is a leaf. -/
def sym (σ : Nat) : Val := .know (Term.sym σ)

/-- The σ a value IS, if it is a bare one. -/
def symOf? : Val → Option Nat
  | .know (.pvar x) => symOfName? x
  | _ => none

/-! Structural equality on values. Written by hand (mutually with the list
    case) because the `List Val` nesting defeats the `deriving BEq` handler;
    still total — `beq` recurses on subterms, `beqList` on the list tail.

    Knowledge compares by `Term.beq`, which is MODE-SENSITIVE where the old
    `Val.beq` unwrapped `cmpT` on either side. Conversion — the judgment that
    unwrapping existed for — has its own equality now (`Term.convEq`, used by
    `Val.convert`), so mode-blindness lives at the site that needs it instead of
    in the equality every incidental comparison reaches for. -/
mutual
  def beq : Val → Val → Bool
    | .know a,     .know b     => Term.beq a b
    | .node n1 a1, .node n2 a2 => n1 == n2 && beqList a1 a2
    | .bot,        .bot        => true
    | .loanM x,    .loanM y    => x == y
    | .borrowM x p, .borrowM y q => x == y && beq p q
    -- Syntactic, on binder names AND body: a runtime function value is a
    -- suspension, so there is no reduction to compare it up to.
    | .rfn xs a,   .rfn ys b   => xs == ys && a == b
    | _,           _           => false
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

    The knowledge half is `Term.prettyPrec`, which reproduces what these cases
    used to print for the pure formers — including `Arr` as `[…]` and a σ as
    `σ0` — so a rejection quoting a value reads the way it always did. -/
mutual
  def prettyPrec (prec : Nat) : Val → String
    | .know t => Term.prettyPrec prec t
    | .bot => "⊥"
    | .loanM ℓ => s!"loanₘ ℓ{ℓ}"
    | .borrowM ℓ p =>
      let s := "borrowₘ ℓ" ++ toString ℓ ++ " " ++ prettyPrec 1 p
      if prec > 0 then s!"({s})" else s
    -- ¶1.1's array forms, rendered the way the design note's traces read (the trace
    -- suite IS the test suite): an owned run as `[3, 1, 2]`, a carved node as
    -- `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ0⟩`.
    -- A recursor spine over runtime arms prints as the SPINE it is; the `§rec`
    -- wrapper is where the skeleton keeps a function value whose arms are not
    -- knowledge, and it is not part of what the value means.
    | .node "§rec" (.know (.const c) :: args) =>
      let s := c ++ prettyArgs args
      if prec > 0 then s!"({s})" else s
    | .node "Arr" vs => "[" ++ prettyCommas vs ++ "]"
    | .node "§segs" segs => "Arr⟨" ++ prettyCommas segs ++ "⟩"
    | .node "§seg" [c, b] => prettyPrec 1 c ++ " ▷ " ++ prettyPrec 0 b
    | .node name [] => name
    | .node name args =>
      let s := name ++ prettyArgs args
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
end

/-- Doc-trace rendering of a value (top-level, no surrounding parens). -/
def pretty (v : Val) : String := prettyPrec 0 v

instance : ToString Val where
  toString v := pretty v

/-! ## Loan-id traversal, for canonical renumbering -/

/-! Loan ids occurring in `v`, in pre-order of first appearance
    (`borrowM ℓ` contributes ℓ before descending into its payload).

    A knowledge leaf is a LEAF here, and that is now a theorem of the
    representation rather than a licensed opacity: a `Term` cannot hold a loan. -/
mutual
  def loanIds : Val → List Nat
    | .loanM ℓ => [ℓ]
    | .borrowM ℓ p => ℓ :: loanIds p
    | .node _ args => loanIdsList args
    | .know _ => []                                     -- knowledge: no loans, by type
    | .bot => []
    | .rfn _ _ => []                                    -- closed: no loans to find
  termination_by v => sizeOf v
  def loanIdsList : List Val → List Nat
    | [] => []
    | v :: vs => loanIds v ++ loanIdsList vs
  termination_by vs => sizeOf vs
end

/-! Does a value carry a STATE marker — a hole (`⊥`), a loan, or a borrow —
    anywhere in its tree? §3.2's knowledge/state invariant: a σ names ENTRY
    knowledge, never the present state of a slot, so a σ-substitution's
    replacement must be marker-free.

    It survives the domain split as a two-line function, because the split
    answered most of it: knowledge cannot carry a marker, so the question is only
    ever about the skeleton above the leaves. ¶1.1's array layer uses it for its
    second job — a segment body is **owned** exactly when it is marker-free — and
    that job is now the same question as "is this body a knowledge leaf". -/
mutual
  def hasStateMarker : Val → Bool
    | .bot => true
    | .loanM _ => true
    | .borrowM _ _ => true
    | .node _ args => hasStateMarkerList args
    | .know _ => false
    | .rfn _ _ => false
  termination_by v => sizeOf v
  def hasStateMarkerList : List Val → Bool
    | [] => false
    | v :: vs => hasStateMarker v || hasStateMarkerList vs
  termination_by vs => sizeOf vs
end

/-! (`Val.capturedMarkers` and `Val.hasStateMarkerEnv` — nbe.md §3.2's capture
    assertion, carried as whole-corpus instrumentation and then as a live guard in
    `mkClosure` — are DELETED here, and not because the rule was dropped. A
    captured environment binds `Sem` values; `Sem` has no ⊥, no loan marker and no
    borrow; so "a captured environment contains knowledge only" is a fact about
    the types rather than a property to scan for. This is §2.3's stated
    consequence arriving: the capture filter and the knowledge-only environment
    invariant become theorems of the representation.) -/

/-! Symbolic ids occurring in `v`, in pre-order of first appearance. The σ's are
    inside the knowledge leaves now, which is where `Term.symIds` reads them. -/
mutual
  def symIds : Val → List Nat
    | .know t => Term.symIds t
    | .borrowM _ p => symIds p
    | .node _ args => symIdsList args
    | .loanM _ => []
    | .bot => []
    | .rfn _ _ => []                                    -- closed: no σ's to find
  termination_by v => sizeOf v
  def symIdsList : List Val → List Nat
    | [] => []
    | v :: vs => symIds v ++ symIdsList vs
  termination_by vs => sizeOf vs
end

/-! Rewrite every loan id `ℓ` to `fℓ ℓ` and every symbolic id `σ` to `fσ σ`
    (used by canonicalization, which renumbers both id spaces).

    Paired with `symIds` above: canonicalization reads the σ order off one
    traversal and applies it with the other, so a σ visible to the first and
    untouched by the second would be renumbered out of existence. -/
mutual
  def renumber (fℓ fσ : Nat → Nat) : Val → Val
    | .loanM ℓ => .loanM (fℓ ℓ)
    | .borrowM ℓ p => .borrowM (fℓ ℓ) (renumber fℓ fσ p)
    | .node n args => .node n (renumberList fℓ fσ args)
    | .know t => .know (Term.renumberSyms fσ t)
    | .bot => .bot
    | .rfn xs b => .rfn xs b                            -- closed: nothing to renumber
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
