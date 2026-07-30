/-!
# DLLBC Syntax (concrete runtime, §2)

One inductive `Term` for the whole grammar of the doc (§1.1), but we declare
only the forms the §2 concrete machine needs right now:

  * variable occurrence,
  * `let x = t ; rest`,
  * `t := t' ; rest` (assignment),
  * constructor application (constructor names as `String` for now —
    `inductive` declarations arrive in a later milestone),
  * `&mut t` (mutable borrow),
  * `*t` (dereference),
  * a unit / terminal form for statement sequences.

The λ / application / Π / `Type` / `match` forms of §1.1 join in later
milestones (§3 match, §5 boundaries, §7 inductives).

## Runtime variables carry globally-unique ids

A runtime variable is a `Nat` id (globally unique, minted by the `dllbc{…}`
macro at elaboration time) paired with a display `String`. There is **no**
de Bruijn indexing in the machine layer and **no** shifting anywhere — the
macro resolves names to ids while elaborating, and an unresolved name is an
elaboration-time error (mirroring `Och/Macro.lean`'s discipline that killed
the silent-999 sentinel bug). The environment Ω is then keyed by these ids,
so shadowing is a fresh id, never a name clash.
-/

namespace Dllbc

/-- A runtime variable: a globally-unique `id` plus a display `name`. -/
structure Var where
  id : Nat
  name : String
deriving DecidableEq, BEq, Repr, Inhabited

/-! Core term syntax of DLLBC's concrete fragment (§2 forms plus §3 `match`).

    Constructor names are `String`s (a placeholder until `inductive`
    declarations arrive). Numeric literals are macro-level sugar for
    `S (S (… Z))` and so need no dedicated term form.

    `Term` is mutual with `Branch` for the `match` case. The scrutinee of a
    match is a `Var` (grammar-enforced, §3: "the scrutinee must be a
    variable"); patterns are one constructor deep. -/
mutual
inductive Term where
  /-- Variable occurrence. Under ⇒ this is a *move*. -/
  | var    : Var → Term
  /-- `let x = rhs ; rest` — bind `x` to the ⇒-value of `rhs`, then run `rest`. -/
  | letIn  : Var → Term → Term → Term
  /-- `place := rhs ; rest` — ⇒-read `rhs`, ⇐-write it into `place`, then `rest`.
      `place` is syntactically an arbitrary `Term`; ⇐ is only *defined* on
      place shapes (a variable under zero or more `*` peels). -/
  | assign : Term → Term → Term → Term
  /-- Constructor application `C(a, b, …)`; nullary `C` is `ctorApp C []`. -/
  | ctorApp : String → List Term → Term
  /-- `&mut t` — mint a loan; `&mut *x` is reborrow. -/
  | borrow : Term → Term
  /-- `*t` — the peel. Arrow-generic in the doc; here used under ⇒ (take)
      and ⇐ (write-through / locate). -/
  | deref  : Term → Term
  /-- `t[i | ev]` — the **index step** (¶2.1), arrow-generic exactly as `*` is. The
      payload at an index place is the ELEMENT (type `T`), not an `Array 1 T`, which
      is what spares every element access a coercion. `ev` is the cited containment
      evidence, `none` when the bound computes (¶3.2's supply route 1). -/
  | index  : Term → Term → Option Term → Term
  /-- `t[lo ; cnt | ev]` — the **range step** (¶2.1). Offset-and-count, never
      lower-and-upper: `a[lo ; cnt]` has type `Array cnt T` read straight off the
      syntax, so no rule below ever produces a `sub`.

      The count is OPTIONAL: `a[lo ; ..]` means "to the end of the segment starting
      at `lo`". That is not sugar for a subtraction — it NAMES the residue the carve
      already minted (premise (3)'s `rest`, sitting in the extent map as a given)
      rather than computing `sub n lo`. ¶3.4 and ¶5 both write `rest` as if it were a
      surface name for that σ, and it is not one; this is how a program says it.

      The **residue** is optional too: `a[lo ; cnt ; rest | h]` SUPPLIES the extent of
      what is left over instead of letting premise (3) mint an unnameable σ for it.
      Same solution transition, same absence of `sub`; the equation is simply solved
      against a term the program wrote. Omit it and the checker mints, exactly as
      before. This is the third instance of a house pattern — an optional surface
      element reifying something the checker already knows, declared rather than
      inferred, free when absent — after §1.2's `[k]` naming the decreasing position
      and §3.2's `match h :` naming the branch equation. -/
  | range  : Term → Term → Option Term → Option Term → Option Term → Term
  /-- `match x { … }` — one-constructor-deep pattern match on a variable
      scrutinee (§3). Owned or borrow mode is chosen at runtime by what the
      scrutinee's slot holds.

      The `Option Var` is the **branch-equation binder** (M23), the surface
      `match h : x { … }`: when present, every branch additionally binds `h` to
      a proof of `Id τ ⟨the scrutinee's pre-split value⟩ ⟨this branch's
      constructor⟩`. One name for the whole match (its *type* is what varies per
      branch), exactly as in Lean's `match h : x with`. `none` is the plain
      form — nothing extra is bound and nothing is minted. -/
  | matchE : Var → Option Var → List Branch → Term
  /-- `e ; rest` — expression statement: ⇒-evaluate `e` for effect, discard
      its value, then run `rest`. Sequences a `match` (or any effectful term)
      used in statement position without binding a throwaway slot. -/
  | seq    : Term → Term → Term
  /-- `f(a, …)` — a call to a declared function (§5.3), checked against the
      signature alone. Unifying `fn` with λ is deferred (§10). -/
  | call   : String → List Term → Term
  /-- Terminal form, the value a statement sequence returns when it has no
      final expression. -/
  | unit   : Term
  -- Pure fragment (§4): the comptime type theory's formers. Pure binders use
  -- de Bruijn indices (`pvar`); `readC` (⇝) reflects these into the matching
  -- `Val` forms and reduces. Runtime `var`/`let` (named ids) are unaffected.
  | pvar   : Nat → Term              -- pure de Bruijn variable
  | type   : Term                    -- the universe
  | pi     : Term → Term → Term      -- Π (dom) (cod); cod binds var 0
  | sigmaT : Term → Term → Term      -- Σ (fst-type) (snd-type); snd binds var 0
  | lam    : Term → Term → Term      -- λ (dom) (body); body binds var 0
  | app    : Term → Term → Term      -- application
  | const  : String → Term           -- a built-in constant (recursor or type former)
  | idT    : Term → Term → Term → Term  -- Id A a b (§10): the identity type
  /-- The borrow type `&mut (s : τ ↝ S)` (§5.1): exclusive access to a `τ`,
      owing an `S` at the boundary. `S` is under one pure de Bruijn binder for
      the entry snapshot `s`. Plain `&mut τ` is `borrowT τ (weaken τ)`. Only
      valid at a telescope position — interpreted by `checkFn`'s seeding, never
      reflected as a value. -/
  | borrowT : Term → Term → Term
/-- A match branch: a constructor name, one-level-deep field binders (display
    names carrying fresh runtime ids), and a body term. -/
inductive Branch where
  | mk : (ctor : String) → (binders : List Var) → (body : Term) → Branch
end

-- Manual instances: `deriving` can't cross the `List Term`/`List Branch`
-- nesting, and nothing in the machine needs term equality (the macro produces
-- terms; tests compare *values*).
instance : Inhabited Term := ⟨.unit⟩
instance : Inhabited Branch := ⟨.mk "" [] .unit⟩

/-- The branch's constructor name. -/
def Branch.ctor : Branch → String | .mk c _ _ => c
/-- The branch's field binders. -/
def Branch.binders : Branch → List Var | .mk _ b _ => b
/-- The branch's body. -/
def Branch.body : Branch → Term | .mk _ _ t => t

/-! ## Structural term equality (manual; `deriving` can't cross the nesting) -/

mutual
  def Term.beq : Term → Term → Bool
    | .var x, .var y => x == y
    | .letIn x a b, .letIn y c d => x == y && Term.beq a c && Term.beq b d
    | .assign a b c, .assign d e f => Term.beq a d && Term.beq b e && Term.beq c f
    | .ctorApp n as, .ctorApp m bs => n == m && Term.beqList as bs
    | .borrow a, .borrow b => Term.beq a b
    | .deref a, .deref b => Term.beq a b
    | .index a i e, .index b j f => Term.beq a b && Term.beq i j && Term.beqOpt e f
    | .range a l c r e, .range b m d q f =>
      Term.beq a b && Term.beq l m && Term.beqOpt c d && Term.beqOpt r q && Term.beqOpt e f
    | .matchE x e as, .matchE y f bs => x == y && e == f && Term.beqBranches as bs
    | .seq a b, .seq c d => Term.beq a c && Term.beq b d
    | .call f as, .call g bs => f == g && Term.beqList as bs
    | .unit, .unit => true
    | .pvar k, .pvar j => k == j
    | .type, .type => true
    | .pi a b, .pi c d => Term.beq a c && Term.beq b d
    | .sigmaT a b, .sigmaT c d => Term.beq a c && Term.beq b d
    | .lam a b, .lam c d => Term.beq a c && Term.beq b d
    | .app a b, .app c d => Term.beq a c && Term.beq b d
    | .const n, .const m => n == m
    | .idT a b c, .idT d e f => Term.beq a d && Term.beq b e && Term.beq c f
    | .borrowT a b, .borrowT c d => Term.beq a c && Term.beq b d
    | _, _ => false
  termination_by t _ => sizeOf t
  def Term.beqList : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => Term.beq a b && Term.beqList as bs
    | _, _ => false
  termination_by ts _ => sizeOf ts
  def Term.beqOpt : Option Term → Option Term → Bool
    | none, none => true
    | some a, some b => Term.beq a b
    | _, _ => false
  termination_by ts _ => sizeOf ts
  def Term.beqBranches : List Branch → List Branch → Bool
    | [], [] => true
    | .mk c bs a :: r, .mk d es b :: s => c == d && bs == es && Term.beq a b && Term.beqBranches r s
    | _, _ => false
  termination_by ts _ => sizeOf ts
end

instance : BEq Term := ⟨Term.beq⟩

/-! ## Pure de Bruijn shift on `Term` (mirror of `Val.shiftPure`), and syntactic
    subterm abstraction — the §18 rewriting layer's mechanism. -/

mutual
  def Term.shiftPure (d c : Nat) : Term → Term
    | .pvar k => if k < c then .pvar k else .pvar (k + d)
    | .lam dom b => .lam (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) b)
    | .pi dom cod => .pi (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) cod)
    | .sigmaT dom cod => .sigmaT (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) cod)
    | .app f a => .app (Term.shiftPure d c f) (Term.shiftPure d c a)
    | .ctorApp n args => .ctorApp n (Term.shiftPureList d c args)
    | .idT a b b' => .idT (Term.shiftPure d c a) (Term.shiftPure d c b) (Term.shiftPure d c b')
    | t => t                                             -- runtime forms / leaves
  termination_by t => sizeOf t
  def Term.shiftPureList (d c : Nat) : List Term → List Term
    | [] => []
    | t :: ts => Term.shiftPure d c t :: Term.shiftPureList d c ts
  termination_by ts => sizeOf ts
end

/-! Abstract every occurrence of `e` at binder `depth` (mutual with the ctor-arg
    list helper). `e` is shifted under each binder crossed; a match replaces it
    with `pvar depth`; a free pure variable is lifted to make room. -/
mutual
  def absOcc (e : Term) (depth : Nat) : Term → Term
    | .lam dom b =>
      if Term.beq (.lam dom b) (Term.shiftPure depth 0 e) then .pvar depth
      else .lam (absOcc e depth dom) (absOcc e (depth + 1) b)
    | .pi dom cod =>
      if Term.beq (.pi dom cod) (Term.shiftPure depth 0 e) then .pvar depth
      else .pi (absOcc e depth dom) (absOcc e (depth + 1) cod)
    | .sigmaT dom cod =>
      if Term.beq (.sigmaT dom cod) (Term.shiftPure depth 0 e) then .pvar depth
      else .sigmaT (absOcc e depth dom) (absOcc e (depth + 1) cod)
    | .app f a =>
      if Term.beq (.app f a) (Term.shiftPure depth 0 e) then .pvar depth
      else .app (absOcc e depth f) (absOcc e depth a)
    | .idT a b c =>
      if Term.beq (.idT a b c) (Term.shiftPure depth 0 e) then .pvar depth
      else .idT (absOcc e depth a) (absOcc e depth b) (absOcc e depth c)
    | .ctorApp n args =>
      if Term.beq (.ctorApp n args) (Term.shiftPure depth 0 e) then .pvar depth
      else .ctorApp n (absOccList e depth args)
    | .pvar k =>
      if Term.beq (.pvar k) (Term.shiftPure depth 0 e) then .pvar depth
      else .pvar (if k < depth then k else k + 1)
    | s => if Term.beq s (Term.shiftPure depth 0 e) then .pvar depth else s   -- leaves
  termination_by s => sizeOf s
  def absOccList (e : Term) (depth : Nat) : List Term → List Term
    | [] => []
    | s :: ss => absOcc e depth s :: absOccList e depth ss
  termination_by ss => sizeOf ss
end

/-- Abstract every occurrence of `e` in `t` by a fresh de Bruijn binder.
    `Term.lam τ (abstractOccurrences e t)` applied to `e` β-reduces back to `t`.
    The §18 motive-generalization mechanism: no matching by eye, no missed
    occurrence. -/
def abstractOccurrences (e t : Term) : Term := absOcc e 0 t

end Dllbc
