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

/-! ## Full normalization and conversion -/

/-! Normalize to full normal form: whnf the head, then normalize subterms.
    Under a binder, de Bruijn `pvar 0` is naturally a neutral leaf, so no fresh
    variable is needed. Fuel-bounded. -/
mutual
  def nfV : Nat → Val → Val
    | 0, v => v
    | fuel + 1, v =>
      match whnfV (fuel + 1) v with
      | .pi d c => .pi (nfV fuel d) (nfV fuel c)
      | .sigmaT d c => .sigmaT (nfV fuel d) (nfV fuel c)
      | .lam d b => .lam (nfV fuel d) (nfV fuel b)
      | .ctor n args => .ctor n (nfVList fuel args)
      | .app f a => .app (nfV fuel f) (nfV fuel a)
      | .idT a b b' => .idT (nfV fuel a) (nfV fuel b) (nfV fuel b')
      | w => w                                       -- pvar, sym, type, const, and runtime leaves
  termination_by fuel _ => (fuel, 0, 0)
  def nfVList : Nat → List Val → List Val
    | _, [] => []
    | fuel, v :: vs => nfV fuel v :: nfVList fuel vs
  termination_by fuel vs => (fuel, 1, vs.length)
end

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
