import Dllbc.Value

/-!
# The pure fragment's reduction (§4)

The comptime fragment is a tiny standard type theory: one universe (type-in-
type), Π, Σ, λ, application, constructors, and a fixed basis of recursors as
built-in constants (`natRec`, `boolRec`, `botElim`). This module is the
substitution-based evaluator over `Val`, in the `lean/Och` playbook (Och's
`concEval` is the same shape): pure binders are de Bruijn (`pvar`), β and ι
fire by substitution, and a `sym` (or a `pvar`) at an application/recursor
head blocks reduction — the whole spine is then a legal (stuck neutral) value.

`readC` (⇝) and `hasType` (in `Machine.lean`) are built on top: `readC`
reflects a `Term` into a `Val` (resolving Ω snapshot reads) and normalizes it
here; `hasType` uses `convert` and the constructor signature table.

Everything is total: `shiftPure`/`substPure` recurse structurally (mutual with
a list helper for constructor arguments); `whnfV`/`nfV` take explicit fuel.
-/

namespace Dllbc.Val

/-! ## de Bruijn shift and substitution for pure binders

    Only `pvar` (pure de Bruijn) and the pure binders (`pi`/`sigmaT`/`lam`)
    participate. Constructor arguments are recursed into (a dependent type
    like `S #0` carries pure variables); `sym`/`const`/runtime forms are
    leaves — σ, ℓ and constant names are global, not de Bruijn. -/

/-! Shift pure de Bruijn indices ≥ `c` up by `d`. -/
mutual
  def shiftPure (d c : Nat) : Val → Val
    | .pvar k => if k < c then .pvar k else .pvar (k + d)
    | .cmpT τ => .cmpT (shiftPure d c τ)       -- a domain: same binder depth
    | .lam dom b => .lam (shiftPure d c dom) (shiftPure d (c + 1) b)
    | .pi dom cod => .pi (shiftPure d c dom) (shiftPure d (c + 1) cod)
    | .sigmaT dom cod => .sigmaT (shiftPure d c dom) (shiftPure d (c + 1) cod)
    | .app f a => .app (shiftPure d c f) (shiftPure d c a)
    | .ctor n args => .ctor n (shiftPureList d c args)
    | .idT a b b' => .idT (shiftPure d c a) (shiftPure d c b) (shiftPure d c b')
    | v => v                                   -- type, const, sym, ⊥, loanM, borrowM: leaves
  termination_by v => sizeOf v
  def shiftPureList (d c : Nat) : List Val → List Val
    | [] => []
    | v :: vs => shiftPure d c v :: shiftPureList d c vs
  termination_by vs => sizeOf vs
end

/-! Does the value mention any pure de Bruijn variable in a position the pure
    shift/substitution reaches (`borrowM` payloads are leaves there, so a pvar
    inside one does not count)? A pvar-free value is a fixed point of
    `shiftPure d c`, which is what lets `substPure` below never copy it. -/
mutual
  def pvarFree : Val → Bool
    | .pvar _ => false
    | .cmpT τ => pvarFree τ
    | .lam dom b => pvarFree dom && pvarFree b
    | .pi dom cod => pvarFree dom && pvarFree cod
    | .sigmaT dom cod => pvarFree dom && pvarFree cod
    | .app f a => pvarFree f && pvarFree a
    | .ctor _ args => pvarFreeList args
    | .idT a b b' => pvarFree a && pvarFree b && pvarFree b'
    | _ => true                                -- leaves (see shiftPure)
  termination_by v => sizeOf v
  def pvarFreeList : List Val → Bool
    | [] => true
    | v :: vs => pvarFree v && pvarFreeList vs
  termination_by vs => sizeOf vs
end

/-! Substitute `s` for pure de Bruijn variable `j` in a value; indices `> j`
    shift down by one (the binder at `j` is eliminated).

    **Delayed lifting** (the checker's measured hot spot — see the perf commit):
    the textbook recursion re-shifts `s` at *every* binder it goes under
    (`substPure (j+1) (shiftPure 1 0 s) b`), which structurally copies `s` once
    per binder crossed — O(binders × |s|). At quicksort scale the substituends
    are 10⁵-node proof values and this one line was ~93% of all checker CPU
    (62% `shiftPure` itself + ~30% allocator/refcount churn on the copies).
    Instead we carry the number of binders crossed, `d`, and lift only at an
    actual occurrence of the variable — and not even then when `s` is pvar-free
    (`sc`), since the shift is then the identity. Extensionally identical to the
    old recursion: `substGo j d sc s v = substPure_old (j+d) (shiftPure d 0 s) v`
    by induction on `v`, using `shiftPure 1 0 ∘ shiftPure d 0 = shiftPure (d+1) 0`
    (cutoff 0) at the binder cases and, for the `sc` fast path, that a pvar-free
    `s` is a fixed point of every shift. -/
mutual
  def substGo (j d : Nat) (sc : Bool) (s : Val) : Val → Val
    | .pvar k =>
      if k == j + d then (if sc || d == 0 then s else shiftPure d 0 s)
      else if k > j + d then .pvar (k - 1) else .pvar k
    | .cmpT τ => .cmpT (substGo j d sc s τ)    -- a domain: same binder depth
    | .lam dom b => .lam (substGo j d sc s dom) (substGo j (d + 1) sc s b)
    | .pi dom cod => .pi (substGo j d sc s dom) (substGo j (d + 1) sc s cod)
    | .sigmaT dom cod => .sigmaT (substGo j d sc s dom) (substGo j (d + 1) sc s cod)
    | .app f a => .app (substGo j d sc s f) (substGo j d sc s a)
    | .ctor n args => .ctor n (substGoList j d sc s args)
    | .idT a b b' => .idT (substGo j d sc s a) (substGo j d sc s b) (substGo j d sc s b')
    | v => v                                   -- leaves (see shiftPure)
  termination_by v => sizeOf v
  def substGoList (j d : Nat) (sc : Bool) (s : Val) : List Val → List Val
    | [] => []
    | v :: vs => substGo j d sc s v :: substGoList j d sc s vs
  termination_by vs => sizeOf vs
end

def substPure (j : Nat) (s : Val) (v : Val) : Val := substGo j 0 (pvarFree s) s v

def substPureList (j : Nat) (s : Val) (vs : List Val) : List Val := substGoList j 0 (pvarFree s) s vs

/-! ## `let`, and how the comptime fragment reads one (M29 α)

    **`let` is a form BOTH arrows read.** ⇒ binds an Ω slot; ⇝'s reading is β —
    `let x = e ; rest` is `rest` with `x`'s occurrences replaced by `e`'s value.
    The two reflections that implement ⇝ (`Term.toValPure` below, monad-free, and
    `reflectC` in `Machine.lean`, which additionally resolves Ω snapshots) share
    this context so that there is one statement of the rule rather than two.

    Doing β as a REWRITE — abstract `x` out of `rest`, then apply — would take
    both reflections off their structural recursion, since the abstracted body is
    not a subterm of anything. So the substitution is carried rather than applied:
    a binding is recorded here and consulted at the `.var` that needs it, which is
    the same reduction with the copies delayed.

    **The DEPTH is why this is a context and not a list.** A let-bound value may
    mention pure de Bruijn variables — `λ (n : Nat). let s = f n ; …` binds `s` to
    a value containing `#0` — and an occurrence of `s` under one more binder sits
    at a different level than the binding did. Each entry therefore records the
    depth it was made at, and a lookup lifts by the difference: exactly the
    `shiftPure` a β-rewrite performs on the way in. -/
structure LetCtx where
  /-- Pure binders crossed so far. -/
  dep : Nat := 0
  /-- `id ↦ (depth at binding, value)`, innermost first. -/
  lets : List (Nat × Nat × Val) := []
deriving Inhabited

/-- One pure binder deeper. -/
def LetCtx.under (c : LetCtx) : LetCtx := { c with dep := c.dep + 1 }

/-- Record a `let` binding at the current depth. PREPENDED, so an inner `let` on
    the same id shadows an outer one. -/
def LetCtx.bind (c : LetCtx) (id : Nat) (v : Val) : LetCtx :=
  { c with lets := (id, c.dep, v) :: c.lets }

/-- The value bound to a variable id, lifted from the depth it was bound at to
    the depth this occurrence sits at. The identity at equal depths — every
    occurrence not under a further pure binder, which is the common case — so the
    lift is guarded rather than unconditional. -/
def LetCtx.find? (c : LetCtx) (id : Nat) : Option Val :=
  match c.lets.find? (fun e => e.1 == id) with
  | some (_, bd, v) => some (if c.dep == bd then v else shiftPure (c.dep - bd) 0 v)
  | none => none

/-! Reflect a PURE `Term` into a `Val` (no monad, no Ω): the borrow-free fragment
    only — `var`/`deref`/runtime forms map to `⊥` (they never occur in a pure
    goal). Used by `Std.nfTerm` to normalize a §18 generalize goal so a computed
    subterm (an `eqb`-spine hidden in a `count`-unfolding) is exposed before
    `abstractOccurrences`.

    A `let` is read by β, through the context above. A `.var` that is NOT
    let-bound still maps to `⊥`: with no Ω there is nothing else it could be, and
    the distinction is exactly the one this reflection is for — a `let` is part of
    the pure term, an Ω snapshot is not. Moved here from `Value.lean` in M29 α,
    which is when it acquired the `let` case and with it a use for `shiftPure`. -/
mutual
  def Term.toValPureGo (c : LetCtx) : Term → Val
    | .type => .type
    | .const k => .const k
    | .pvar k => .pvar k
    | .var x => (c.find? x.id).getD .bot
    | .letIn x rhs rest => Term.toValPureGo (c.bind x.id (Term.toValPureGo c rhs)) rest
    | .cmpT τ => .cmpT (Term.toValPureGo c τ)
    | .pi d cod => .pi (Term.toValPureGo c d) (Term.toValPureGo c.under cod)
    | .sigmaT d cod => .sigmaT (Term.toValPureGo c d) (Term.toValPureGo c.under cod)
    | .lam d b => .lam (Term.toValPureGo c d) (Term.toValPureGo c.under b)
    | .app f a => .app (Term.toValPureGo c f) (Term.toValPureGo c a)
    | .idT a b b' => .idT (Term.toValPureGo c a) (Term.toValPureGo c b) (Term.toValPureGo c b')
    | .ctorApp n args => .ctor n (Term.toValPureListGo c args)
    | .unit => .ctor "unit" []
    | _ => .bot                                          -- runtime forms: absent in pure goals
  termination_by t => sizeOf t
  def Term.toValPureListGo (c : LetCtx) : List Term → List Val
    | [] => []
    | t :: ts => Term.toValPureGo c t :: Term.toValPureListGo c ts
  termination_by ts => sizeOf ts
end

def Term.toValPure (t : Term) : Val := Term.toValPureGo {} t

def Term.toValPureList (ts : List Term) : List Val := Term.toValPureListGo {} ts

/-! ## Kernel arithmetic, and the `Array` former's vocabulary

    `add` and `Le` are library terms (`Std`) in every other respect, but the CARVE
    rule's premises are *stated* against them: premise (2) is a `Le`, and premise
    (3) decomposes an extent with `add`. A kernel rule cannot cite a library it does
    not import, and two syntactically different `add`s would never convert — so the
    single source of truth for both moves here, and `Std` aliases these. (§9 already
    files "`Le` as a primitive former" as a pending recognition prerequisite; this is
    that pressure arriving from a second direction.) -/

def kNatTy : Val := .const "Nat"
def kUnitTy : Val := .const "Unit"
def kBotTy : Val := .const "Bot"
def kNatRecS (P z s n : Val) : Val := .app (.app (.app (.app (.const "natRec") P) z) s) n

/-- `add a b` by recursion on `a` (`add Z b = b`, `add (S a') b = S (add a' b)`). -/
def kAddFn : Val :=
  .lam kNatTy (.lam kNatTy (kNatRecS (.lam kNatTy kNatTy) (.pvar 0)
    (.lam kNatTy (.lam kNatTy (.ctor "S" [.pvar 0]))) (.pvar 1)))
def kAdd (a b : Val) : Val := .app (.app kAddFn a) b

/-- `Le : Nat → Nat → Type` as a computing predicate (`Z ≤ _ ↦ ⊤`, `S ≤ Z ↦ ⊥`,
    `S ≤ S ↦ recurse`). Premise (2)'s obligation type is built from this. -/
def kLeFn : Val :=
  .lam kNatTy (kNatRecS (.lam kNatTy (.pi kNatTy .type)) (.lam kNatTy kUnitTy)
    (.lam kNatTy (.lam (.pi kNatTy .type) (.lam kNatTy
      (kNatRecS (.lam kNatTy .type) kBotTy
        (.lam kNatTy (.lam .type (.app (.pvar 3) (.pvar 1)))) (.pvar 0)))))
    (.pvar 0))
def kLe (a b : Val) : Val := .app (.app kLeFn a) b

/-- `Array n T` — the ¶1.1 former, in the FIXED BASIS rather than §7's declaration
    scheme (the values are flat runs, which no CIC-scheme inductive has). -/
def arrayTy (n T : Val) : Val := .app (.app (.const "Array") n) T

/-- Recognize `Array n T`, returning `(n, T)`. -/
def asArrayTy? : Val → Option (Val × Val)
  | .app (.app (.const "Array") n) t => some (n, t)
  | _ => none

/-- Read a `Nat` value as a Lean numeral, if it is concrete. -/
def natOfVal? : Val → Option Nat
  | .ctor "Z" [] => some 0
  | .ctor "S" [n] => (natOfVal? n).map (· + 1)
  | _ => none

/-- The `Nat` value of a Lean numeral. -/
def valOfNat : Nat → Val
  | 0 => .ctor "Z" []
  | k + 1 => .ctor "S" [valOfNat k]

/-! An array's **owned run**: `Arr [v₁ … v_c]`, the flat literal, which is both the
    value form and the knowledge form (`ctorSig`'s field telescope is `T` repeated
    `c` times, so it is exactly what §7 would have generated). Element `i` is child
    `i` — a *subterm*, which is the whole reason ¶1.2 puts the former in the basis
    rather than deriving it from a right-nested spine. -/
def arrRun? : Val → Option (List Val)
  | .ctor "Arr" vs => some vs
  | _ => none

/-! ## Weak-head normalization (β and ι)

    An application spine is `head a₁ … aₙ`. β fires when the head is a `lam`;
    ι fires when the head is a recursor constant applied to enough arguments
    and its target (the last relevant one) is constructor-headed. A `sym`- or
    `pvar`-headed spine, or a recursor stuck on a neutral target, is a value. -/

/-- Collect an application spine into its head and argument list (in order). -/
def collectSpine : Val → Val × List Val
  | .app f a => let (h, as) := collectSpine f; (h, as ++ [a])
  | v => (v, [])

/-- Rebuild an application spine from a head and argument list. -/
def rebuildSpine : Val → List Val → Val
  | h, [] => h
  | h, a :: as => rebuildSpine (.app h a) as

/-- Weak-head-normalize: reduce the head redex (β / ι) only, fuel-bounded.
    Leaves (`pvar`, `sym`, `type`, `const`, `pi`, `sigmaT`, `lam`, `ctor`) and
    stuck neutral spines are returned as-is. -/
def whnfV : Nat → Val → Val
  | 0, v => v
  | fuel + 1, v =>
    let (head, args) := collectSpine v
    match head, args with
    | .lam _ b, a :: rest =>                        -- β
      whnfV fuel (rebuildSpine (substPure 0 a b) rest)
    | .const "natRec", motive :: z :: s :: n :: rest =>
      match whnfV fuel n with
      | .ctor "Z" [] => whnfV fuel (rebuildSpine z rest)
      | .ctor "S" [m] =>
        -- natRec P z s (S m) ↦ s m (natRec P z s m)
        let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
        whnfV fuel (rebuildSpine (.app (.app s m) recCall) rest)
      | n' => rebuildSpine (.const "natRec") (motive :: z :: s :: n' :: rest)  -- stuck
    | .const "boolRec", motive :: t :: f :: b :: rest =>
      match whnfV fuel b with
      | .ctor "True" [] => whnfV fuel (rebuildSpine t rest)
      | .ctor "False" [] => whnfV fuel (rebuildSpine f rest)
      | b' => rebuildSpine (.const "boolRec") (motive :: t :: f :: b' :: rest)  -- stuck
    -- listRec A P pn pc l : P l ; ι on Nil ↦ pn, on Cons h t ↦ pc h t (rec on t).
    | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
      match whnfV fuel l with
      | .ctor "Nil" [] => whnfV fuel (rebuildSpine pn rest)
      | .ctor "Cons" [h, t] =>
        let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
        whnfV fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)
      | l' => rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l' :: rest)  -- stuck
    -- sigmaRec A B P f p : P p (§9) — the dependent Σ eliminator, the basis's one
    -- missing recursor-per-former. ι on `Pair a b ↦ f a b`. Non-recursive (Σ is not
    -- inductive in its own right), so there is no `ih` argument, unlike natRec/listRec.
    | .const "sigmaRec", a :: b :: motive :: f :: p :: rest =>
      match whnfV fuel p with
      | .ctor "Pair" [x, y] => whnfV fuel (rebuildSpine (.app (.app f x) y) rest)
      | p' => rebuildSpine (.const "sigmaRec") (a :: b :: motive :: f :: p' :: rest)  -- stuck
    -- Paulin-Mohring J (§10): j A a P d b p ; ι fires on Refl (b = a there), → d.
    | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
      match whnfV fuel p with
      | .ctor "Refl" [] => whnfV fuel (rebuildSpine d rest)
      | p' => rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p' :: rest)  -- stuck
    -- Streicher K (§10): k A a P d p ; ι fires on Refl, → d.
    | .const "k", _A :: _a :: _P :: d :: p :: rest =>
      match whnfV fuel p with
      | .ctor "Refl" [] => whnfV fuel (rebuildSpine d rest)
      | p' => rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p' :: rest)  -- stuck
    -- ## The array basis's computing constants (¶1.3)
    --
    -- `arrCat T m k a b : Array (add m k) T` — the SPLIT view, and the comptime
    -- shadow of the segment structure. It computes on run-headed arguments
    -- (segment-list concatenation) and is a legitimate stuck neutral on σ's, which
    -- is exactly §3.2's knowledge/state line: the segment list is state, the
    -- `arrCat` spine is knowledge. Empty runs are absorbed — a zero-extent carve
    -- piece must vanish definitionally, or every degenerate carve's rejoin
    -- conversion would need a lemma.
    --
    -- DEVIATION from ¶1.3's signature, and the reason: the doc writes `arrCat : Π T
    -- (m k : Nat) → …`, but nothing needs the `T`. Its result type is checked, never
    -- synthesized (an `Array` is never applied), while the merge normalization and
    -- the ⇝ fold would both have to MANUFACTURE a `T` they cannot read off a value
    -- tree — Ω records extents, not element types. So `T` is dropped here and
    -- recovered from the expected type at the check. Same for `acons`; `aget` keeps
    -- its `T`, since its result type genuinely is `T` and must be synthesized.
    | .const "arrCat", m :: k :: a :: b :: rest =>
      match whnfV fuel a, whnfV fuel b with
      | .ctor "Arr" [], b' => whnfV fuel (rebuildSpine b' rest)
      | a', .ctor "Arr" [] => whnfV fuel (rebuildSpine a' rest)
      | .ctor "Arr" xs, .ctor "Arr" ys => whnfV fuel (rebuildSpine (.ctor "Arr" (xs ++ ys)) rest)
      -- CONS-VIEW compatibility: `arrCat (acons x xs) b ⇝ acons x (arrCat xs b)`, the
      -- array counterpart of `append (Cons h t) u ⇝ Cons h (append t u)`. Without it the
      -- library transfer ¶1.3 promises is not mechanical: `sorted_append_pivot`'s proof
      -- turns on `Sorted (append (Cons h t) …)` UNFOLDING definitionally, and the array
      -- restatement needs the same unfolding or every step wants a transport lemma.
      | .app (.app (.app (.const "acons") m') x) xs, b' =>
        whnfV fuel (rebuildSpine
          (.app (.app (.app (.const "acons") (kAdd m' k)) x)
            (.app (.app (.app (.app (.const "arrCat") m') k) xs) b')) rest)
      -- A nonempty RUN on the left with a non-run on the right peels its head into an
      -- `acons`, which is the same rule read through the other view: a literal is a
      -- cons spine that happens to be written flat. Without this `arrCat (asingle p) b`
      -- is stuck for symbolic `b` — and `asingle p` computes to a RUN, so ¶6's own
      -- spelling of the pivot splice would not reach the cons view it is meant to be.
      | .ctor "Arr" (x :: xs), b' =>
        let tlLen := valOfNat xs.length
        whnfV fuel (rebuildSpine
          (.app (.app (.app (.const "acons") (kAdd tlLen k)) x)
            (.app (.app (.app (.app (.const "arrCat") tlLen) k) (.ctor "Arr" xs)) b')) rest)
      | a', b' => rebuildSpine (.const "arrCat") (m :: k :: a' :: b' :: rest)
    -- `aget T n i a : T` — positional read of the snapshot (¶2.2's ⇝ column at an
    -- index place). Fires only at a concrete index into a run.
    | .const "aget", tt :: n :: i :: a :: rest =>
      match natOfVal? (whnfV fuel i), whnfV fuel a with
      | some j, .ctor "Arr" vs =>
        match vs.get? j with
        | some v => whnfV fuel (rebuildSpine v rest)
        | none => rebuildSpine (.const "aget") (tt :: n :: i :: .ctor "Arr" vs :: rest)
      | _, a' => rebuildSpine (.const "aget") (tt :: n :: i :: a' :: rest)
    -- `acons T n x xs : Array (S n) T` — the CONS view's constructor, so that the
    -- pure library over arrays can be written exactly like the one over lists.
    | .const "acons", n :: x :: xs :: rest =>
      match whnfV fuel xs with
      | .ctor "Arr" vs => whnfV fuel (rebuildSpine (.ctor "Arr" (x :: vs)) rest)
      | xs' => rebuildSpine (.const "acons") (n :: x :: xs' :: rest)
    -- `arrRec T P pn pc n a : P n a` — the cons-view recursor (¶1.3). ι on a run:
    -- empty ↦ pn, `Arr (x :: vs)` ↦ pc |vs| x (Arr vs) (rec on Arr vs).
    | .const "arrRec", tt :: motive :: pn :: pc :: n :: a :: rest =>
      match whnfV fuel a with
      | .ctor "Arr" [] => whnfV fuel (rebuildSpine pn rest)
      | .ctor "Arr" (x :: vs) =>
        let tl : Val := .ctor "Arr" vs
        let k : Val := valOfNat vs.length
        let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, k, tl]
        whnfV fuel (rebuildSpine (rebuildSpine pc [k, x, tl, recCall]) rest)
      -- …and ι on the CONS view, so a predicate over arrays unfolds on an `acons`
      -- exactly as its list counterpart unfolds on a `Cons`.
      | .app (.app (.app (.const "acons") m') x) xs =>
        let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, m', xs]
        whnfV fuel (rebuildSpine (rebuildSpine pc [m', x, xs, recCall]) rest)
      | a' => rebuildSpine (.const "arrRec") (tt :: motive :: pn :: pc :: n :: a' :: rest)
    -- botElim never fires (⊥ has no constructors); it is always a stuck value.
    | _, _ => rebuildSpine head args

/-! ## Environment-based evaluation — NbE (M30, `docs/nbe.md`)

    The replacement for everything above this line. A λ no longer reduces by
    copying its argument into its body; it evaluates to a **closure** — the body
    as written, plus the environment it was born in — and application extends
    that environment. There is no index arithmetic anywhere below, which is the
    point (§1.1: a hand-written index sat wrong for five milestones because
    nothing consulted it; environments have no index to get wrong).

    ### The one representation decision, and why it keeps the diff small

    A closure lives in the BODY position of `lam`/`pi`/`sigmaT` rather than
    replacing them. So every consumer that matches those three formers goes on
    matching them; what changes is the single act of *opening* a binder, from
    `substPure 0 a b` to `instBody b a`. That is why 18 substitution sites become
    18 one-word edits rather than a rewrite of the checker.

    It also means the domain is **mixed**: a `Val` may be syntax (a hand-built
    recursor premise type, a term just reflected from the surface) or semantics (a
    value `eval` produced), and the two differ only in whether binder bodies are
    closures. `instBody` accepts both — a closure carries its own environment, a
    syntactic body gets the singleton `[arg]` — and that is exactly right, because
    a syntactic binder reached this way is closed but for its own variable.

    ### The two variable conventions, which must not be conflated

      * `pvar k` with `k < |ρ|` is **bound**: look it up.
      * `pvar k` with `k ≥ |ρ|` is **free** — an index into the context *outside*
        ρ — and evaluates to `pvar (k - |ρ|)`, the same down-shift `substPure`
        performed when it eliminated a binder. Readback re-adds the depth.
      * `lvl j` is a **level**, minted by readback, counted from the outside.
        Readback turns it into `pvar (d - 1 - j)`.

    The two rules disagree (`+d` versus `d - 1 - j`), which is the whole reason
    `lvl` is a former of its own rather than a reuse of `pvar`.

    ### No η, structurally

    Readback is UNTYPED. It never expands a neutral at function type, so
    `λ (u : Nat). u` and `λ (u : Nat). Z` stay unequal and a stuck spine stays the
    spine it is — the property KernelFloor polices and the one an η-normalizing
    readback would silently destroy. -/

/-- Form a closure, unless the body already is one. A `.closure` in body position
    means the binder is ALREADY semantic — it was produced by an earlier `eval` and
    carries the environment it was born in — so re-capturing it against whatever
    environment happens to be current is the one way this machinery can go wrong.
    (It is also what makes `eval` idempotent on values, which the mixed domain
    needs: a value re-entering `eval` must come out unchanged.)

    **And this is §3.2's capture assertion**, live rather than instrumented. The
    plan had been a one-shot instrumentation run, on the reasoning that a marker
    scan at every λ evaluation is the innermost loop of the comptime fragment and
    `eval` is a pure function with no monad to throw into. The first half of that
    reasoning was refuted by measurement — the guard costs 2 s on a 124 s suite,
    inside the noise, because comptime environments are small and the scan
    short-circuits — so the honest thing is to keep it.

    The second half stands: there is no monad here, so a violation cannot be
    thrown. It is turned into a value no rule can use, which surfaces as the
    rejection of whatever asked. That is weaker than `refineSym`'s throw in the
    message it can give and exactly as strong in what it forbids. -/
def mkClosure (ρ : List Val) (body : Val) : Val :=
  match body with
  | .closure _ _ => body
  | b =>
    if hasStateMarkerList ρ then
      .const "@@capture: a λ/Π closed over a state marker (⊥/loan/borrow) — §3.2 knowledge/state"
    else .closure ρ b

mutual
  /-- Evaluate `v` (read as pure syntax) against the comptime environment `ρ`.
      Strong everywhere except under a binder, where the body is suspended.

      Runtime forms — `⊥`, `loanM`, `borrowM`, `rfn` — are LEAVES, exactly as they
      were for `shiftPure`/`substPure`. That is not an omission: a borrow payload
      is state, `eval` computes knowledge, and descending into one would be the
      first step of the door §3.3 is holding shut. -/
  def eval : Nat → List Val → Val → Val
    | 0, _, v => v
    | fuel + 1, ρ, v =>
      match v with
      | .pvar k =>
        match ρ.get? k with
        | some w => w
        | none => .pvar (k - ρ.length)          -- free: the binder-elimination down-shift
      | .lam dom body => .lam (eval (fuel + 1) ρ dom) (mkClosure ρ body)
      | .pi dom cod => .pi (eval (fuel + 1) ρ dom) (mkClosure ρ cod)
      | .sigmaT dom cod => .sigmaT (eval (fuel + 1) ρ dom) (mkClosure ρ cod)
      | .cmpT τ => .cmpT (eval (fuel + 1) ρ τ)
      | .app f a => whnfN (fuel + 1) (.app (eval (fuel + 1) ρ f) (eval (fuel + 1) ρ a))
      | .ctor n args => .ctor n (evalList (fuel + 1) ρ args)
      | .idT a b c => .idT (eval (fuel + 1) ρ a) (eval (fuel + 1) ρ b) (eval (fuel + 1) ρ c)
      | w => w        -- type, const, sym, lvl, closure, ⊥, loanM, borrowM, rfn
  termination_by fuel _ v => (fuel, 1, sizeOf v)
  def evalList : Nat → List Val → List Val → List Val
    | _, _, [] => []
    | fuel, ρ, v :: vs => eval fuel ρ v :: evalList fuel ρ vs
  termination_by fuel _ vs => (fuel, 1, sizeOf vs)
  /-- **Open a binder at `arg`** — the single operation that replaces
      `substPure 0 arg body` at all eighteen of its sites.

      Both shapes of body are legal, and the asymmetry is the mixed domain showing
      through rather than a special case: a `closure` was built by `eval` and knows
      the environment it needs, while a bare body is syntax whose only free variable
      is the binder's own, so the singleton environment is complete for it. -/
  def instBody : Nat → Val → Val → Val
    | fuel, .closure ρ b, arg => eval fuel (arg :: ρ) b
    | fuel, b, arg => eval fuel [arg] b
  termination_by fuel _ _ => (fuel, 2, 0)
  /-- Weak-head reduction over the mixed domain: β and ι, head redex only.

      Structurally the `whnfV` above it, with ONE line different — β opens the
      binder by environment extension instead of by substitution. Everything else
      (the recursor table, the array basis's computing constants, what counts as a
      stuck neutral) is the same calculus and is meant to read as the same rules. -/
  def whnfN : Nat → Val → Val
    | 0, v => v
    | fuel + 1, v =>
      let (head, args) := collectSpine v
      match head, args with
      | .lam _ b, a :: rest =>                        -- β, by capture
        whnfN fuel (rebuildSpine (instBody fuel b a) rest)
      | .const "natRec", motive :: z :: s :: n :: rest =>
        match whnfN fuel n with
        | .ctor "Z" [] => whnfN fuel (rebuildSpine z rest)
        | .ctor "S" [m] =>
          let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
          whnfN fuel (rebuildSpine (.app (.app s m) recCall) rest)
        | n' => rebuildSpine (.const "natRec") (motive :: z :: s :: n' :: rest)
      | .const "boolRec", motive :: t :: f :: b :: rest =>
        match whnfN fuel b with
        | .ctor "True" [] => whnfN fuel (rebuildSpine t rest)
        | .ctor "False" [] => whnfN fuel (rebuildSpine f rest)
        | b' => rebuildSpine (.const "boolRec") (motive :: t :: f :: b' :: rest)
      | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
        match whnfN fuel l with
        | .ctor "Nil" [] => whnfN fuel (rebuildSpine pn rest)
        | .ctor "Cons" [h, t] =>
          let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
          whnfN fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)
        | l' => rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l' :: rest)
      | .const "sigmaRec", a :: b :: motive :: f :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Pair" [x, y] => whnfN fuel (rebuildSpine (.app (.app f x) y) rest)
        | p' => rebuildSpine (.const "sigmaRec") (a :: b :: motive :: f :: p' :: rest)
      | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Refl" [] => whnfN fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p' :: rest)
      | .const "k", _A :: _a :: _P :: d :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Refl" [] => whnfN fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p' :: rest)
      | .const "arrCat", m :: k :: a :: b :: rest =>
        match whnfN fuel a, whnfN fuel b with
        | .ctor "Arr" [], b' => whnfN fuel (rebuildSpine b' rest)
        | a', .ctor "Arr" [] => whnfN fuel (rebuildSpine a' rest)
        | .ctor "Arr" xs, .ctor "Arr" ys => whnfN fuel (rebuildSpine (.ctor "Arr" (xs ++ ys)) rest)
        | .app (.app (.app (.const "acons") m') x) xs, b' =>
          whnfN fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (kAdd m' k)) x)
              (.app (.app (.app (.app (.const "arrCat") m') k) xs) b')) rest)
        | .ctor "Arr" (x :: xs), b' =>
          let tlLen := valOfNat xs.length
          whnfN fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (kAdd tlLen k)) x)
              (.app (.app (.app (.app (.const "arrCat") tlLen) k) (.ctor "Arr" xs)) b')) rest)
        | a', b' => rebuildSpine (.const "arrCat") (m :: k :: a' :: b' :: rest)
      | .const "aget", tt :: n :: i :: a :: rest =>
        match natOfVal? (whnfN fuel i), whnfN fuel a with
        | some j, .ctor "Arr" vs =>
          match vs.get? j with
          | some w => whnfN fuel (rebuildSpine w rest)
          | none => rebuildSpine (.const "aget") (tt :: n :: i :: .ctor "Arr" vs :: rest)
        | _, a' => rebuildSpine (.const "aget") (tt :: n :: i :: a' :: rest)
      | .const "acons", n :: x :: xs :: rest =>
        match whnfN fuel xs with
        | .ctor "Arr" vs => whnfN fuel (rebuildSpine (.ctor "Arr" (x :: vs)) rest)
        | xs' => rebuildSpine (.const "acons") (n :: x :: xs' :: rest)
      | .const "arrRec", tt :: motive :: pn :: pc :: n :: a :: rest =>
        match whnfN fuel a with
        | .ctor "Arr" [] => whnfN fuel (rebuildSpine pn rest)
        | .ctor "Arr" (x :: vs) =>
          let tl : Val := .ctor "Arr" vs
          let k : Val := valOfNat vs.length
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, k, tl]
          whnfN fuel (rebuildSpine (rebuildSpine pc [k, x, tl, recCall]) rest)
        | .app (.app (.app (.const "acons") m') x) xs =>
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, m', xs]
          whnfN fuel (rebuildSpine (rebuildSpine pc [m', x, xs, recCall]) rest)
        | a' => rebuildSpine (.const "arrRec") (tt :: motive :: pn :: pc :: n :: a' :: rest)
      | _, _ => rebuildSpine head args
  termination_by fuel _ => (fuel, 0, 0)
end

/-! **Readback**: a value back to closure-free de Bruijn syntax.

    It emits exactly the shapes `nfV` emits — classic indices, no levels, no
    closures — which is what makes the old and new evaluators comparable byte for
    byte over the whole corpus rather than merely "both plausible".

    `depth` counts the binders readback has re-created, and it is the ONLY thing
    the two variable rules need: a level is `depth - 1 - j` (levels count from the
    outside, indices from the inside), a free index is `k + depth` (every binder
    re-created around it is one more binder to skip).

    **It weak-heads each node on the way down**, which is `nfV`'s own shape and not
    a concession. `eval` is eager on the arguments it is *given* but leaves an ι
    reduct residual — `natRec P z s (S m)` steps to `s m (natRec P z s m)`, and the
    `S` node that wraps the recursive call is a constructor, where weak-head
    reduction is *supposed* to stop. Something has to force it, and forcing it here
    keeps the laziness that makes `hasType` linear in a value rather than quadratic:
    a constructor's arguments are reduced when someone looks at them, once. (Found
    by the smoke probe, not by reasoning: `add 2 3` normalized to
    `S (natRec … (S Z))` before this line existed.) -/
mutual
  def readback : Nat → Nat → Val → Val
    | 0, _, v => v
    | fuel + 1, depth, v =>
      match whnfN (fuel + 1) v with
      | .lvl j => .pvar (depth - 1 - j)
      | .pvar k => .pvar (k + depth)
      | .lam dom body =>
        .lam (readback fuel depth dom) (readback fuel (depth + 1) (instBody fuel body (.lvl depth)))
      | .pi dom cod =>
        .pi (readback fuel depth dom) (readback fuel (depth + 1) (instBody fuel cod (.lvl depth)))
      | .sigmaT dom cod =>
        .sigmaT (readback fuel depth dom) (readback fuel (depth + 1) (instBody fuel cod (.lvl depth)))
      | .cmpT τ => .cmpT (readback fuel depth τ)
      | .app f a => .app (readback fuel depth f) (readback fuel depth a)
      | .ctor n args => .ctor n (readbackList fuel depth args)
      | .idT a b c => .idT (readback fuel depth a) (readback fuel depth b) (readback fuel depth c)
      | w => w        -- type, const, sym, ⊥, loanM, borrowM, rfn: leaves, as in `nfV`
  termination_by fuel _ _ => (fuel, 0)
  def readbackList : Nat → Nat → List Val → List Val
    | _, _, [] => []
    | fuel, depth, v :: vs => readback fuel depth v :: readbackList fuel depth vs
  termination_by fuel _ vs => (fuel, vs.length + 1)
end

/-- Normal form by evaluation: evaluate against the empty environment, read back
    from depth zero. Intended to be **extensionally identical** to `nfV`, which is
    what the M30 differential asserts over the corpus rather than assumes. -/
def nfN (fuel : Nat) (v : Val) : Val := readback fuel 0 (eval fuel [] v)

/-! ## Full normalization and conversion -/

/-! Normalize to full normal form: whnf the head, then normalize subterms.
    Under a binder, de Bruijn `pvar 0` is naturally a neutral leaf, so no fresh
    variable is needed. Fuel-bounded.

    **The substitution normalizer, and for the duration of M30 it is no longer the
    one the checker calls.** `nfV` below runs this and `nfN` against each other on
    every normalization the corpus performs; this is the side that is going away. -/
mutual
  def nfSubst : Nat → Val → Val
    | 0, v => v
    | fuel + 1, v =>
      match whnfV (fuel + 1) v with
      | .pi d c => .pi (nfSubst fuel d) (nfSubst fuel c)
      | .sigmaT d c => .sigmaT (nfSubst fuel d) (nfSubst fuel c)
      -- The mode marker SURVIVES normalization — ⇒'s application rules read it
      -- off a normalized callee — and is invisible to `convert` anyway, because
      -- `beq` unwraps it (§6, "case is inert under ⇝").
      | .cmpT τ => .cmpT (nfSubst fuel τ)
      | .lam d b => .lam (nfSubst fuel d) (nfSubst fuel b)
      | .ctor n args => .ctor n (nfSubstList fuel args)
      | .app f a => .app (nfSubst fuel f) (nfSubst fuel a)
      | .idT a b b' => .idT (nfSubst fuel a) (nfSubst fuel b) (nfSubst fuel b')
      | w => w                                       -- pvar, sym, type, const, and runtime leaves
  termination_by fuel _ => (fuel, 0, 0)
  def nfSubstList : Nat → List Val → List Val
    | _, [] => []
    | fuel, v :: vs => nfSubst fuel v :: nfSubstList fuel vs
  termination_by fuel vs => (fuel, 1, vs.length)
end

/-! ## The M30 differential — SCAFFOLDING, deleted with the old evaluator

    Every normalization the corpus performs runs BOTH evaluators and compares the
    results byte for byte. A disagreement does not warn: it returns a value no rule
    can use, so the check that asked fails and the build goes red. Silent
    divergence is the only failure mode a refactor of the equality procedure really
    has, and this is the M28 playbook that caught the last one.

    The recursions above and below this line are careful to call `nfSubst`/`nfN`
    and NOT this wrapper: a differential at every node would run the new evaluator
    once per subterm and turn a linear normalization into a quadratic one.

    Deleted at step 4, with `substPure`, `shiftPure` and `nfSubst`. -/
def nfV (fuel : Nat) (v : Val) : Val :=
  let old := nfSubst fuel v
  let new := nfN fuel v
  if old == new then old
  else .const s!"@@M30-DIVERGENCE@@ old={old.pretty} new={new.pretty}"

/-- Definitional conversion: equal normal forms. For this fragment (β, ι, no
    eta, de Bruijn) normal forms are canonical, so normal-form equality *is*
    convertibility — simpler than a lazy whnf-and-compare recursion and, for a
    normalizing system, equivalent. -/
def convert (fuel : Nat) (a b : Val) : Bool := nfV fuel a == nfV fuel b

/-! ## Segments (¶1.1): the carved array's state form

    An array value at `Array n T` is one of
      * `Arr [v₁ … v_n]`   — an owned flat run (also the knowledge form),
      * `sym σ`            — opaque,
      * a stuck neutral    — an `arrCat` spine,
      * `§segs [seg₁ … seg_k]` (k ≥ 2) — CARVED, each `§seg [c, body]`.

    The last is **state only**: reserved names with no `ctorSig` entry, so no program
    can write or match one, and every generic `Val` walker (`loanIds`, `symIds`,
    `renumber`, `loanToPvar`, `hasStateMarker`, `beq`) traverses it unchanged — the
    load-bearing claim of Appendix A, and the reason the borrow machinery needed no
    edit. An UNCARVED array carries no wrapper at all: ¶1.1's "a single segment is
    abbreviated to its body, since the two are the same state". -/

def segNode (c body : Val) : Val := .ctor "§seg" [c, body]

/-- Rebuild a segment list into an array node, restoring the two invariants: drop
    zero-extent segments (¶1.1's *drop-empty*), and unwrap a single segment. -/
def segsNode (segs : List Val) : Val :=
  match segs with
  | [] => .ctor "Arr" []
  | [.ctor "§seg" [_, b]] => if hasStateMarker b then .ctor "§segs" segs else b
  | ss => .ctor "§segs" ss

def asSeg? : Val → Option (Val × Val)
  | .ctor "§seg" [c, b] => some (c, b)
  | _ => none

/-- Is a segment body **owned** — one of the three forms a carve is defined on
    (¶1.1: an owned run, a σ, a neutral) rather than the two ownership markers?

    The test is MARKER-FREEDOM, not "the body is not itself a marker", and the
    difference is load-bearing. An element cursor (`&mut a[i]`) parks its marker
    INSIDE the one-slot run — `§seg [1, Arr [loanₘ ℓ]]` — because ¶2.1 puts the
    element, not an `Array 1 T`, at an index place. A shallow test would call that
    body owned, let it merge into its neighbour's run, and then hand the MARKER out
    as an element on the next read: the silent-marker class §3.2 and §5.2 both
    warn about, reached by a new route. -/
def segOwned (b : Val) : Bool := !hasStateMarker b

/-- The total extent of a segment list: RIGHT-NESTED, with no trailing `Z`. `add`
    recurses on its first argument, so `add c Z` is stuck the moment `c` is symbolic,
    and every conversion the residue transition arranges would fail on the trailing
    zero alone. -/
partial def segsExtent? : List Val → Option Val
  | [] => some (.ctor "Z" [])
  | [s] => (asSeg? s).map (·.1)
  | s :: rest => do
    let (c, _) ← asSeg? s
    let tot ← segsExtent? rest
    some (kAdd c tot)

/-- The extent of an array-shaped value read off the value itself, where that is
    possible: a run knows its length, a segment list sums its extents, an `arrCat`
    spine carries both halves. A bare `σ` does NOT — its extent lives in its `sctx`
    type, which only the machine can reach (`arrExtent` there). -/
partial def arrExtentPure? : Val → Option Val
  | .ctor "Arr" vs => some (valOfNat vs.length)
  | .ctor "§segs" segs => segsExtent? segs
  | .app (.app (.app (.app (.const "arrCat") m) k) _) _ => some (kAdd m k)
  | _ => none

/-! **Merge** (¶1.1), the normalization that makes the carve history invisible: two
    adjacent segments with owned bodies collapse into one of the summed extent.

    Only *runs* are concatenated. Two adjacent σ's have `arrCat σ₁ σ₂` as their joint
    body in the doc, and building it here would be harmless but pointless: the pair of
    segments already types against `Array (add c₁ c₂) T` by the extent-consistency
    check, and `⇝` folds them to that very `arrCat` anyway. Leaving them apart keeps
    merge a pure function of the value tree — no element types, no fuel, no sctx. -/
partial def mergeSegList : List Val → List Val
  | s₁ :: s₂ :: rest =>
    match asSeg? s₁, asSeg? s₂ with
    | some (c₁, b₁), some (c₂, b₂) =>
      match b₁, b₂ with
      | .ctor "Arr" xs, .ctor "Arr" ys =>
        if segOwned b₁ && segOwned b₂ then
          mergeSegList (segNode (kAdd c₁ c₂) (.ctor "Arr" (xs ++ ys)) :: rest)
        else s₁ :: mergeSegList (s₂ :: rest)
      | _, _ => s₁ :: mergeSegList (s₂ :: rest)
    | _, _ => s₁ :: mergeSegList (s₂ :: rest)
  | ss => ss

/-- Merge-normalize an array node wherever one sits in `v`. Applied at every *read*
    of a place, which is what makes it robust to the §5.2 demand-end sites: a
    suspension collapsing mid-body turns markers back into values, and the read that
    follows is what re-merges them. Nothing has to remember to. -/
partial def mergeArrays : Val → Val
  | .ctor "§segs" segs =>
    segsNode (mergeSegList (segs.map (fun s => match asSeg? s with
      | some (c, b) => segNode c (mergeArrays b)
      | none => mergeArrays s)))
  | .ctor n args => .ctor n (args.map mergeArrays)
  | .borrowM ℓ p => .borrowM ℓ (mergeArrays p)
  | v => v

/-- `arrCat` applied to its four arguments. -/
def arrCatS (m k a b : Val) : Val := .app (.app (.app (.app (.const "arrCat") m) k) a) b

/-- **The ⇝ bridge** (¶1.3): fold one segment list into its `arrCat` spine — the
    knowledge form of what the array *is*, which never mentions a marker or a hole.
    `none` when some body is one: "a suspended array has no snapshot; only a
    collapsed one does", §5.2's proper-payload premise arriving at an array node. -/
partial def arrFoldSegs? : List Val → Option Val
  | [] => some (.ctor "Arr" [])
  | [s] => do
    let (_, b) ← asSeg? s
    if segOwned b then some b else none
  | s :: rest => do
    let (c, b) ← asSeg? s
    if !segOwned b then none
    else do
      let bt ← arrFoldSegs? rest
      let ct ← segsExtent? rest
      some (arrCatS c ct b bt)

/-- Fold every *foldable* segment list in `v`, leaving a suspended one in place.
    Total by design: an unfoldable node stays the state form it is and is rejected
    at the one place that judges (`hasType`, with a distinctive error), rather than
    turning every comptime read of a marker-bearing aggregate into a new error. -/
partial def arrFoldDeep : Val → Val
  | .ctor "§segs" segs =>
    let segs' := segs.map (fun s => match asSeg? s with
      | some (c, b) => segNode c (arrFoldDeep b)
      | none => arrFoldDeep s)
    match arrFoldSegs? segs' with
    | some v => v
    | none => .ctor "§segs" segs'
  | .ctor n args => .ctor n (args.map arrFoldDeep)
  | .borrowM ℓ p => .borrowM ℓ (arrFoldDeep p)
  | v => v

/-! ## Constructor signature table (§4)

    No inductive-declaration machinery: a small fixed table telling `hasType`,
    for a given whnf'd expected type, the constructor's field types as a
    telescope (dependent positions carry de Bruijn references to earlier
    fields — e.g. `Pair`'s second field). `none` means the constructor does
    not inhabit that type former. -/

/-- The field-type telescope of a constructor, given the whnf'd expected type. -/
structure CtorSig where
  fieldTypes : Val → Option (List Val)

/-- The fixed constructor basis: Unit, Bool, Nat, List (element parameter),
    and Σ's `Pair` (dependent second field). -/
def ctorSig : String → Option CtorSig
  | "unit"  => some { fieldTypes := fun ty => match ty with | .const "Unit" => some [] | _ => none }
  | "True"  => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "False" => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "Z"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [] | _ => none }
  | "S"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [.const "Nat"] | _ => none }
  | "Nil"   => some { fieldTypes := fun ty => match ty with | .app (.const "List") _ => some [] | _ => none }
  | "Cons"  => some { fieldTypes := fun ty =>
      match ty with | .app (.const "List") t => some [t, .app (.const "List") t] | _ => none }
  | "Pair"  => some { fieldTypes := fun ty => match ty with | .sigmaT a b => some [a, b] | _ => none }
  -- `Arr` — the array literal (¶1.4). Its field telescope for a CONCRETE `n` is `T`
  -- repeated `n` times; at a symbolic `n` there is no constructor signature, and
  -- correctly so — one cannot write an array literal of unknown length. This is
  -- hand-written rather than §7-generated, which is the concrete cost basis
  -- membership carries (¶9c): the fixed basis and the declaration scheme can drift,
  -- and this entry is where the drift would start.
  | "Arr"   => some { fieldTypes := fun ty =>
      match asArrayTy? ty with
      | some (n, t) => (natOfVal? (Val.whnfV 1000 n)).map (fun k => List.replicate k t)
      | none => none }
  -- Refl : Id A a a — a nullary constructor whose type demands equal endpoints.
  -- (Fixed fuel for the endpoint convert; construction sites are small.)
  | "Refl"  => some { fieldTypes := fun ty =>
      match ty with | .idT _ a b => if Val.convert 1000 a b then some [] else none | _ => none }
  | _ => none

/-- The names `ctorSig` answers for — **the fixed constructor basis, enumerated**.

    It exists because combining-fns §6 makes capitalisation the binder-mode
    marker, and the prescription that keeps that unambiguous is "constructor
    names are special-cased as keywords — the fixed basis makes the set closed
    and small". A surface binder may not take one of these names, and this list
    is what the check consults. Must track `ctorSig`; the two sit adjacent so
    that adding a constructor without reserving its name is a visible omission
    rather than a silent one. -/
def ctorNames : List String :=
  ["unit", "True", "False", "Z", "S", "Nil", "Cons", "Pair", "Arr", "Refl"]

/-! ## Binder modes on a value's domain (combining-fns §6)

    The `Val` mirror of `Term.domComptime`/`Term.stripCmp`. ⇒'s value-callee
    application rule reads a λ's or Π's binder modes through these; nothing under
    ⇝ ever asks, which is what "case is inert under ⇝" means operationally. -/

/-- Is this λ/Π domain a COMPTIME binder's? -/
def domComptime : Val → Bool
  | .cmpT _ => true
  | _ => false

/-- The domain proper, mode marker peeled. `⇝τ` is not a type: a value inhabits
    it exactly when it inhabits `τ`. -/
def stripCmp : Val → Val
  | .cmpT τ => τ
  | v => v

/-- The full constructor set of a whnf'd type (§9 exhaustiveness). `none` for a
    type whose constructors aren't known (nothing to check against). `Bot` has
    an EMPTY set — an empty match on a ⊥-typed scrutinee is vacuously
    exhaustive. -/
def typeCtors : Val → Option (List String)
  | .const "Nat"  => some ["Z", "S"]
  | .const "Bool" => some ["True", "False"]
  | .const "Unit" => some ["unit"]
  | .const "Bot"  => some []
  | .app (.const "List") _ => some ["Nil", "Cons"]
  | .sigmaT _ _   => some ["Pair"]
  | .idT _ _ _    => some ["Refl"]                 -- §10: Id's only constructor
  -- `Array n T` has the single constructor `Arr` at a concrete `n`, and NO known
  -- constructor set at a symbolic one. ¶1.4: arrays are never matched anyway — an
  -- array's information is positional, reached by the place grammar, not by a tag —
  -- so this entry exists for exhaustiveness's benefit and is never consulted.
  | ty => match asArrayTy? ty with
    | some (n, _) => if (natOfVal? (Val.whnfV 1000 n)).isSome then some ["Arr"] else none
    | none => none

end Dllbc.Val
