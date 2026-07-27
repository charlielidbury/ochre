import Std.Data.HashSet
import Std.Data.HashMap
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

/-! Shift pure de Bruijn indices ≥ `c` up by `d`. SHARING-PRESERVING: the
    primed helpers return a "changed" flag, and a node none of whose children
    changed is returned as the SAME object rather than rebuilt. The flag is
    sound in one direction only — `false` guarantees the result IS the input
    (so a conservative `true` is always allowed) — and behavior is pointwise
    identical to the naive rebuild: a `false` subtree is structurally equal to
    what the rebuild would have produced. Physical sharing is what pointer-
    fast equality and pointer-keyed memoization downstream feed on; a β-step
    that copies its argument into k occurrences now inserts k pointers to ONE
    object, and untouched proof-term regions survive substitution un-copied. -/
mutual
  def shiftPure' (d c : Nat) : Val → Val × Bool
    | v@(.pvar k) =>
      if k < c || d == 0 then (v, false) else (.pvar (k + d), true)
    | v@(.lam dom b) =>
      let (dom', bd) := shiftPure' d c dom
      let (b', bb) := shiftPure' d (c + 1) b
      if bd || bb then (.lam dom' b', true) else (v, false)
    | v@(.pi dom cod) =>
      let (dom', bd) := shiftPure' d c dom
      let (cod', bc) := shiftPure' d (c + 1) cod
      if bd || bc then (.pi dom' cod', true) else (v, false)
    | v@(.sigmaT dom cod) =>
      let (dom', bd) := shiftPure' d c dom
      let (cod', bc) := shiftPure' d (c + 1) cod
      if bd || bc then (.sigmaT dom' cod', true) else (v, false)
    | v@(.app f a) =>
      let (f', bf) := shiftPure' d c f
      let (a', ba) := shiftPure' d c a
      if bf || ba then (.app f' a', true) else (v, false)
    | v@(.ctor n args) =>
      let (args', bs) := shiftPureList' d c args
      if bs then (.ctor n args', true) else (v, false)
    | v@(.idT a b b') =>
      let (a', ba) := shiftPure' d c a
      let (b2, bb) := shiftPure' d c b
      let (b2', bb') := shiftPure' d c b'
      if ba || bb || bb' then (.idT a' b2 b2', true) else (v, false)
    | v => (v, false)                          -- type, const, sym, ⊥, loanM, borrowM: leaves
  termination_by v => sizeOf v
  def shiftPureList' (d c : Nat) : List Val → List Val × Bool
    | [] => ([], false)
    | vs@(v :: rest) =>
      let (v', bv) := shiftPure' d c v
      let (rest', br) := shiftPureList' d c rest
      if bv || br then (v' :: rest', true) else (vs, false)
  termination_by vs => sizeOf vs
end

/-- Shift pure de Bruijn indices ≥ `c` up by `d` (sharing-preserving). -/
def shiftPure (d c : Nat) (v : Val) : Val := (shiftPure' d c v).1
/-- List version of `shiftPure`. -/
def shiftPureList (d c : Nat) (vs : List Val) : List Val := (shiftPureList' d c vs).1

/-! Substitute `s` for pure de Bruijn variable `j` in a value; indices `> j`
    shift down by one (the binder at `j` is eliminated). `s` is shifted when
    going under a binder. Sharing-preserving like `shiftPure'` — a subtree
    without the variable comes back as the same object, and every occurrence
    of `s` in the result is the same physical `s`. -/
mutual
  def substPure' (j : Nat) (s : Val) : Val → Val × Bool
    | v@(.pvar k) =>
      if k == j then (s, true) else if k > j then (.pvar (k - 1), true) else (v, false)
    | v@(.lam dom b) =>
      let (dom', bd) := substPure' j s dom
      let (b', bb) := substPure' (j + 1) (shiftPure 1 0 s) b
      if bd || bb then (.lam dom' b', true) else (v, false)
    | v@(.pi dom cod) =>
      let (dom', bd) := substPure' j s dom
      let (cod', bc) := substPure' (j + 1) (shiftPure 1 0 s) cod
      if bd || bc then (.pi dom' cod', true) else (v, false)
    | v@(.sigmaT dom cod) =>
      let (dom', bd) := substPure' j s dom
      let (cod', bc) := substPure' (j + 1) (shiftPure 1 0 s) cod
      if bd || bc then (.sigmaT dom' cod', true) else (v, false)
    | v@(.app f a) =>
      let (f', bf) := substPure' j s f
      let (a', ba) := substPure' j s a
      if bf || ba then (.app f' a', true) else (v, false)
    | v@(.ctor n args) =>
      let (args', bs) := substPureList' j s args
      if bs then (.ctor n args', true) else (v, false)
    | v@(.idT a b b') =>
      let (a', ba) := substPure' j s a
      let (b2, bb) := substPure' j s b
      let (b2', bb') := substPure' j s b'
      if ba || bb || bb' then (.idT a' b2 b2', true) else (v, false)
    | v => (v, false)                          -- leaves (see shiftPure')
  termination_by v => sizeOf v
  def substPureList' (j : Nat) (s : Val) : List Val → List Val × Bool
    | [] => ([], false)
    | vs@(v :: rest) =>
      let (v', bv) := substPure' j s v
      let (rest', br) := substPureList' j s rest
      if bv || br then (v' :: rest', true) else (vs, false)
  termination_by vs => sizeOf vs
end

/-- Substitute `s` for pure de Bruijn `j` (sharing-preserving). -/
def substPure (j : Nat) (s : Val) (v : Val) : Val := (substPure' j s v).1
/-- List version of `substPure`. -/
def substPureList (j : Nat) (s : Val) (vs : List Val) : List Val := (substPureList' j s vs).1

/-! ## Weak-head normalization (β and ι)

    An application spine is `head a₁ … aₙ`. β fires when the head is a `lam`;
    ι fires when the head is a recursor constant applied to enough arguments
    and its target (the last relevant one) is constructor-headed. A `sym`- or
    `pvar`-headed spine, or a recursor stuck on a neutral target, is a value. -/

/-- Collect an application spine into its head and argument list (in order). -/
def collectSpine : Val → Val × List Val
  | .app f a => let (h, as) := collectSpine f; (h, as ++ [a])
  | v => (v, [])

/-! ## Interning (hash-consing)

    `intern` is LOGICALLY the identity — every use is semantically invisible —
    with an `implemented_by` runtime that returns a canonical representative
    for the node: a previously-interned node with the same constructor, the
    same leaf data, and POINTER-identical children (which entails structural
    equality). Keying on child pointers makes the probe O(arity), not
    O(subtree); effectiveness (not soundness) relies on building bottom-up so
    children are already canonical. Independently-constructed duplicates —
    each `readC` re-reflecting the same model term, each unfolding rebuilding
    the same spine — then become ONE object, so the rigid-table hits fire and
    `beqFast`'s pointer short-circuit decides equality without traversal. The
    table holds strong references, pinning addresses (no recycling) at the
    price of process-lifetime retention — acceptable for a checker run. -/

private unsafe def internTableRef : IO.Ref (Std.HashMap UInt64 (List Val)) :=
  unsafeBaseIO (IO.mkRef ∅)

/-- Child key hash: LEAVES by value (a fresh `.const "natRec"` is minted at
    every stuck rebuild — pointer identity would never unify spines),
    composites by address. -/
private unsafe def childHash (v : Val) : UInt64 :=
  match v with
  | .const s => mixHash 101 (hash s)
  | .pvar k => mixHash 103 (hash k)
  | .sym x => mixHash 107 (hash x)
  | .type => 109
  | .bot => 113
  | .loanM x => mixHash 127 (hash x)
  | _ => (ptrAddrUnsafe v).toUInt64

/-- Child equality matching `childHash`: leaf value, or same object. Either
    way the children are structurally equal. -/
private unsafe def childEq (a b : Val) : Bool :=
  match a, b with
  | .const x, .const y => x == y
  | .pvar x, .pvar y => x == y
  | .sym x, .sym y => x == y
  | .type, .type => true
  | .bot, .bot => true
  | .loanM x, .loanM y => x == y
  | _, _ => ptrEq a b

/-- O(arity) node hash: constructor tag + leaf data + child ADDRESSES. -/
private unsafe def nodeHashU : Val → UInt64
  | .ctor n args => mixHash 3 (mixHash (hash n) (args.foldl (fun h a => mixHash h (childHash a)) 47))
  | .bot => 5
  | .loanM x => mixHash 7 (hash x)
  | .borrowM x p => mixHash 11 (mixHash (hash x) (childHash p))
  | .sym x => mixHash 13 (hash x)
  | .pvar x => mixHash 17 (hash x)
  | .type => 19
  | .pi d c => mixHash 23 (mixHash (childHash d) (childHash c))
  | .sigmaT d c => mixHash 29 (mixHash (childHash d) (childHash c))
  | .lam d b => mixHash 31 (mixHash (childHash d) (childHash b))
  | .app f a => mixHash 37 (mixHash (childHash f) (childHash a))
  | .const s => mixHash 41 (hash s)
  | .idT a b c => mixHash 43 (mixHash (childHash a) (mixHash (childHash b) (childHash c)))

/-- O(arity) shallow equality: same tag and leaf data, children the SAME
    objects — which entails structural equality of the whole nodes. -/
private unsafe def nodeEqU : Val → Val → Bool
  | .ctor n1 a1, .ctor n2 a2 =>
    n1 == n2 && a1.length == a2.length && (List.zip a1 a2).all (fun p => childEq p.1 p.2)
  | .bot, .bot => true
  | .loanM x, .loanM y => x == y
  | .borrowM x p, .borrowM y q => x == y && childEq p q
  | .sym x, .sym y => x == y
  | .pvar x, .pvar y => x == y
  | .type, .type => true
  | .pi d1 c1, .pi d2 c2 => childEq d1 d2 && childEq c1 c2
  | .sigmaT d1 c1, .sigmaT d2 c2 => childEq d1 d2 && childEq c1 c2
  | .lam d1 b1, .lam d2 b2 => childEq d1 d2 && childEq b1 b2
  | .app f1 a1, .app f2 a2 => childEq f1 f2 && childEq a1 a2
  | .const x, .const y => x == y
  | .idT a1 b1 c1, .idT a2 b2 c2 => childEq a1 a2 && childEq b1 b2 && childEq c1 c2
  | _, _ => false

private unsafe def findBucket (v : Val) : List Val → Option Val
  | [] => none
  | w :: ws => if nodeEqU v w then some w else findBucket v ws

private unsafe def internU (v : Val) : Val :=
  unsafeBaseIO do
    let h := nodeHashU v
    let m ← internTableRef.get
    let bucket := m.getD h []
    match findBucket v bucket with
    | some w => pure w
    | none =>
      internTableRef.set (m.insert h (v :: bucket))
      pure v

/-- Canonicalize a node against the intern table. LOGICALLY THE IDENTITY. -/
@[implemented_by internU]
def intern (v : Val) : Val := v

/-- Rebuild an application spine from a head and argument list (interning each
    node, so every spine construction site — whnf reducts, resolved back
    compositions, audit specs — produces canonical objects). -/
def rebuildSpine : Val → List Val → Val
  | h, [] => h
  | h, a :: as => rebuildSpine (intern (.app h a)) as

/-- Weak-head-normalize: reduce the head redex (β / ι) only, fuel-bounded.
    Leaves (`pvar`, `sym`, `type`, `const`, `pi`, `sigmaT`, `lam`, `ctor`) and
    stuck neutral spines are returned as-is. SHARING-PRESERVING (`whnfV'`
    carries a "changed" flag): a spine on which no rule fires — including a
    recursor stuck on an already-whnf target — is returned as the ORIGINAL
    object, where the old code rebuilt a structurally identical fresh spine
    (`rebuildSpine (collectSpine v)` and the stuck-recursor rebuilds are the
    identity up to structure). Pointwise identical results, shared objects. -/
def whnfV' : Nat → Val → Val × Bool
  | 0, v => (v, false)
  | fuel + 1, v =>
    let (head, args) := collectSpine v
    match head, args with
    | .lam _ b, a :: rest =>                        -- β
      ((whnfV' fuel (rebuildSpine (substPure 0 a b) rest)).1, true)
    | .const "natRec", motive :: z :: s :: n :: rest =>
      let (n', bn) := whnfV' fuel n
      match n' with
      | .ctor "Z" [] => ((whnfV' fuel (rebuildSpine z rest)).1, true)
      | .ctor "S" [m] =>
        -- natRec P z s (S m) ↦ s m (natRec P z s m)
        let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
        ((whnfV' fuel (rebuildSpine (.app (.app s m) recCall) rest)).1, true)
      | n'' =>                                       -- stuck
        if bn then (rebuildSpine (.const "natRec") (motive :: z :: s :: n'' :: rest), true)
        else (v, false)
    | .const "boolRec", motive :: t :: f :: b :: rest =>
      let (b', bb) := whnfV' fuel b
      match b' with
      | .ctor "True" [] => ((whnfV' fuel (rebuildSpine t rest)).1, true)
      | .ctor "False" [] => ((whnfV' fuel (rebuildSpine f rest)).1, true)
      | b'' =>                                       -- stuck
        if bb then (rebuildSpine (.const "boolRec") (motive :: t :: f :: b'' :: rest), true)
        else (v, false)
    -- listRec A P pn pc l : P l ; ι on Nil ↦ pn, on Cons h t ↦ pc h t (rec on t).
    | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
      let (l', bl) := whnfV' fuel l
      match l' with
      | .ctor "Nil" [] => ((whnfV' fuel (rebuildSpine pn rest)).1, true)
      | .ctor "Cons" [h, t] =>
        let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
        ((whnfV' fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)).1, true)
      | l'' =>                                       -- stuck
        if bl then (rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l'' :: rest), true)
        else (v, false)
    -- Paulin-Mohring J (§10): j A a P d b p ; ι fires on Refl (b = a there), → d.
    | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
      let (p', bp) := whnfV' fuel p
      match p' with
      | .ctor "Refl" [] => ((whnfV' fuel (rebuildSpine d rest)).1, true)
      | p'' =>                                       -- stuck
        if bp then (rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p'' :: rest), true)
        else (v, false)
    -- Streicher K (§10): k A a P d p ; ι fires on Refl, → d.
    | .const "k", _A :: _a :: _P :: d :: p :: rest =>
      let (p', bp) := whnfV' fuel p
      match p' with
      | .ctor "Refl" [] => ((whnfV' fuel (rebuildSpine d rest)).1, true)
      | p'' =>                                       -- stuck
        if bp then (rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p'' :: rest), true)
        else (v, false)
    -- botElim never fires (⊥ has no constructors); it is always a stuck value.
    | _, _ => (v, false)

/-- Weak-head-normalize (sharing-preserving; see `whnfV'`). -/
def whnfV (fuel : Nat) (v : Val) : Val := (whnfV' fuel v).1

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

/-! Definitional conversion: equal normal forms. For this fragment (β, ι, no
    eta, de Bruijn) normal forms are canonical, so normal-form equality *is*
    convertibility. Computed INCREMENTALLY (the kernel algorithm): identical
    terms convert outright (`beq` is structural equality, and `nfV` is a
    function of structure, so `a == b` implies equal normal forms); otherwise
    whnf both sides, compare heads, recurse on subterms. This is *pointwise
    equal* to the specification `nfV fuel a == nfV fuel b`, by induction on
    fuel: `nfV (fuel+1)` is `whnfV (fuel+1)` followed by `nfV fuel` on each
    subterm, and `beq` on the two rebuilt results is the head comparison
    followed by `beq` on normalized subterm pairs — which is `convert fuel` on
    the un-normalized pairs, by the inductive hypothesis. The mixed-head and
    leaf cases land in the `w₁ == w₂` catch-all, exactly `beq` on what `nfV`
    returns unchanged. The fuel accounting is `nfV`'s own (decrement per
    structural level, whnf at the entry fuel), so even fuel-truncated behavior
    coincides. What changes is only the COST: two sides that agree
    syntactically — the overwhelmingly common case in `hasType`, measured at
    72% of all `convert` calls in a partition-range check — are decided by one
    structural pass with no normalization at all, and a genuine mismatch stops
    at the first differing head instead of building both full normal forms. -/
mutual
  def convert : Nat → Val → Val → Bool
    | 0, a, b => a == b
    | fuel + 1, a, b =>
      if a == b then true else
      match whnfV (fuel + 1) a, whnfV (fuel + 1) b with
      | .pi d1 c1, .pi d2 c2 => convert fuel d1 d2 && convert fuel c1 c2
      | .sigmaT d1 c1, .sigmaT d2 c2 => convert fuel d1 d2 && convert fuel c1 c2
      | .lam d1 b1, .lam d2 b2 => convert fuel d1 d2 && convert fuel b1 b2
      | .ctor n1 as1, .ctor n2 as2 => n1 == n2 && convertList fuel as1 as2
      | .app f1 a1, .app f2 a2 => convert fuel f1 f2 && convert fuel a1 a2
      | .idT a1 b1 c1, .idT a2 b2 c2 =>
        convert fuel a1 a2 && convert fuel b1 b2 && convert fuel c1 c2
      | w1, w2 => w1 == w2                 -- mixed heads, or two leaves: beq as-is
  termination_by fuel _ _ => (fuel, 0, 0)
  def convertList : Nat → List Val → List Val → Bool
    | _, [], [] => true
    | fuel, v :: vs, w :: ws => convert fuel v w && convertList fuel vs ws
    | _, _, _ => false
  termination_by fuel _ ws => (fuel, 1, ws.length)
end

/-! ## Shared normalization: the rigid-term cache

    `nfV` has no term sharing: a subterm embedded k times is re-normalized k
    times, and the conformance audit's trees embed the same model spines
    (`partIdxRangeL lo cnt *v`, a whole `partitionRangeL` unfolding) many times
    over. Measured on the partScanRange check: 94,930 `nfV` node visits over
    only 2,672 distinct terms — 35.5x visit redundancy, 65% of size-weighted
    normalization work spent on re-visits — and one recursion level up
    (quicksort) the repetition compounds multiplicatively.

    `nfS` is `nfV` plus a cache of terms *certified rigid*: hereditarily β/ι-
    irreducible, so `nfV f w = w` and `whnfV f w = w` for EVERY fuel f — fuel
    only gates reduction steps, and a rigid term admits none. That makes the
    cache sound to consult at any fuel and immune to the checker's state
    mutations (`refineSym`/`abstractInto` build NEW terms; rigidity is a
    property of the term itself, so no invalidation exists to miss).

    Certification is syntactic and bottom-up, never trusted from fuel: a leaf
    is rigid by definition (`nfV`/`whnfV` return `pvar`/`sym`/`type`/`const`/
    `⊥`/`loanM`/`borrowM` unchanged — `borrowM` payloads are runtime state the
    pure layer never enters); a composite is certified iff its children were
    (cache membership) AND its own head is not a β/ι-redex (`headRedexApp`,
    conservative: ANY constructor-headed scrutinee under a recursor blocks
    certification, a superset of the exact `Z`/`S`/… patterns `whnfV` fires
    on). Fuel-0 truncation returns uncertified, so a truncated (possibly still
    reducible) result never enters the cache.

    BEHAVIORAL IDENTITY: the value component of `nfS` is pointwise `nfV`, for
    any cache satisfying the invariant. The recursion mirrors `nfV`'s equations
    (same whnf at entry fuel, same decrement per level); the only new branch is
    the cache hit, which returns `v` where `nfV` computes `nfV f v` — equal
    because members are rigid. Any change to `nfV`/`whnfV` must be mirrored
    here (and `convert` above), or the mirror arguments break. -/

/-- The set of terms certified rigid (hereditarily β/ι-irreducible). -/
abbrev NormCache := Std.HashSet Val

/-- Constructor-headed? (the shapes ι could fire on — checked conservatively:
    arity/name mismatches still block certification, they never fire). -/
def isCtorV : Val → Bool
  | .ctor _ _ => true
  | _ => false

/-- Is this spine a head β/ι-redex (or possibly one)? Callers guarantee the
    spine's components are rigid, so the scrutinee IS its own whnf and a shape
    check suffices. Mirrors `whnfV`'s redex cases, conservatively. -/
def headRedexApp (v : Val) : Bool :=
  match collectSpine v with
  | (.lam _ _, _ :: _) => true
  | (.const "natRec", _ :: _ :: _ :: n :: _) => isCtorV n
  | (.const "boolRec", _ :: _ :: _ :: b :: _) => isCtorV b
  | (.const "listRec", _ :: _ :: _ :: _ :: l :: _) => isCtorV l
  | (.const "j", _ :: _ :: _ :: _ :: _ :: p :: _) => isCtorV p
  | (.const "k", _ :: _ :: _ :: _ :: p :: _) => isCtorV p
  | _ => false

/-! `nfS fuel v c` = `(nfV fuel v, certified?, changed?, updated cache)`.
    `certified` means the result is in the cache (hence rigid); `false` is
    always safe. `changed = false` guarantees the result IS the input object
    (sharing-preservation, like `substPure'`): an already-normal subterm comes
    back as itself, so re-normalizing a term yields physically the same
    objects and downstream equality gets pointer-fast. -/
mutual
  def nfS : Nat → Val → NormCache → Val × Bool × Bool × NormCache
    | 0, v, c => (v, false, false, c)
    | fuel + 1, v, c =>
      if c.contains v then (v, true, false, c) else
      let (w, cw) := whnfV' (fuel + 1) v
      match w with
      | .pi d k =>
        let (d', bd, chd, c) := nfS fuel d c
        let (k', bk, chk, c) := nfS fuel k c
        let w' := if chd || chk then intern (Val.pi d' k') else w
        if bd && bk then (w', true, cw || chd || chk, c.insert w')
        else (w', false, cw || chd || chk, c)
      | .sigmaT d k =>
        let (d', bd, chd, c) := nfS fuel d c
        let (k', bk, chk, c) := nfS fuel k c
        let w' := if chd || chk then intern (Val.sigmaT d' k') else w
        if bd && bk then (w', true, cw || chd || chk, c.insert w')
        else (w', false, cw || chd || chk, c)
      | .lam d b =>
        let (d', bd, chd, c) := nfS fuel d c
        let (b', bb, chb, c) := nfS fuel b c
        let w' := if chd || chb then intern (Val.lam d' b') else w
        if bd && bb then (w', true, cw || chd || chb, c.insert w')
        else (w', false, cw || chd || chb, c)
      | .ctor n args =>
        let (args', bs, chs, c) := nfSList fuel args c
        let w' := if chs then intern (Val.ctor n args') else w
        if bs then (w', true, cw || chs, c.insert w')
        else (w', false, cw || chs, c)
      | .app f a =>
        let (f', bf, chf, c) := nfS fuel f c
        let (a', ba, cha, c) := nfS fuel a c
        let w' := if chf || cha then intern (Val.app f' a') else w
        if bf && ba && !headRedexApp w' then (w', true, cw || chf || cha, c.insert w')
        else (w', false, cw || chf || cha, c)
      | .idT x y z =>
        let (x', bx, chx, c) := nfS fuel x c
        let (y', by', chy, c) := nfS fuel y c
        let (z', bz, chz, c) := nfS fuel z c
        let w' := if chx || chy || chz then intern (Val.idT x' y' z') else w
        if bx && by' && bz then (w', true, cw || chx || chy || chz, c.insert w')
        else (w', false, cw || chx || chy || chz, c)
      | w => (w, true, cw, c.insert w)   -- leaves: rigid by definition (see above)
  termination_by fuel _ _ => (fuel, 0, 0)
  def nfSList : Nat → List Val → NormCache → List Val × Bool × Bool × NormCache
    | _, [], c => ([], true, false, c)
    | fuel, vs@(v :: rest), c =>
      let (v', bv, chv, c) := nfS fuel v c
      let (rest', bs, chr, c) := nfSList fuel rest c
      if chv || chr then (v' :: rest', bv && bs, true, c)
      else (vs, bv && bs, false, c)
  termination_by fuel vs _ => (fuel, 1, vs.length)
end

/-! ## Runtime rigid-term table (pointer-keyed)

    The pure `nfS` above is the SPEC: its cache is a structural `HashSet`, and
    its value component is pointwise `nfV` for any cache satisfying the rigid
    invariant — including the empty one. The `implemented_by` mirror below
    keeps the recursion case-for-case identical but consults a GLOBAL
    pointer-keyed table instead of the threaded set, because structural
    hashing is O(subtree) per probe and re-introduces the quadratic that
    sharing is meant to remove (the M22 finding: any content-addressed lookup
    on unshared trees is as expensive as the work it saves). Soundness:

      * a table hit requires the probe object and the stored object to have
        the SAME address while both are live — the table holds a strong
        reference to every key, so addresses cannot be recycled — hence the
        probe IS a term previously certified rigid, and returning it
        unchanged is what `nfV` computes on it (rigid terms are nfV-fixed at
        every fuel);
      * a pointer miss on a structurally-cached term merely re-normalizes —
        the pure spec's value is cache-independent, so EVERY miss is safe;
      * the threaded `NormCache` passes through untouched (stays ∅ at
        runtime), so `St` forks copy nothing.

    The certified/changed flags may differ from the pure run (they reflect
    the table, not the set); the only consumer (`nfM`) discards them. -/

private unsafe def rigidTableRef : IO.Ref (Std.HashMap USize Val) :=
  unsafeBaseIO (IO.mkRef ∅)

/-- Runtime: is `v` (this very object) certified rigid? O(1). -/
private unsafe def rigidContains (v : Val) : Bool :=
  unsafeBaseIO do pure ((← rigidTableRef.get).contains (ptrAddrUnsafe v))

/-- Runtime: certify `v` rigid (keyed by its address, holding `v` alive so the
    address stays uniquely its own). Returns `c` through the IO so the call is
    not dead-code-eliminated. -/
private unsafe def rigidRemember (v : Val) (c : NormCache) : NormCache :=
  unsafeBaseIO do
    rigidTableRef.modify (fun m => m.insert (ptrAddrUnsafe v) v)
    pure c

mutual
  private unsafe def nfSU : Nat → Val → NormCache → Val × Bool × Bool × NormCache
    | 0, v, c => (v, false, false, c)
    | fuel + 1, v, c =>
      if rigidContains v then (v, true, false, c) else
      let (w, cw) := whnfV' (fuel + 1) v
      match w with
      | .pi d k =>
        let (d', bd, chd, c) := nfSU fuel d c
        let (k', bk, chk, c) := nfSU fuel k c
        let w' := if chd || chk then intern (Val.pi d' k') else w
        if bd && bk then (w', true, cw || chd || chk, rigidRemember w' c)
        else (w', false, cw || chd || chk, c)
      | .sigmaT d k =>
        let (d', bd, chd, c) := nfSU fuel d c
        let (k', bk, chk, c) := nfSU fuel k c
        let w' := if chd || chk then intern (Val.sigmaT d' k') else w
        if bd && bk then (w', true, cw || chd || chk, rigidRemember w' c)
        else (w', false, cw || chd || chk, c)
      | .lam d b =>
        let (d', bd, chd, c) := nfSU fuel d c
        let (b', bb, chb, c) := nfSU fuel b c
        let w' := if chd || chb then intern (Val.lam d' b') else w
        if bd && bb then (w', true, cw || chd || chb, rigidRemember w' c)
        else (w', false, cw || chd || chb, c)
      | .ctor n args =>
        let (args', bs, chs, c) := nfSListU fuel args c
        let w' := if chs then intern (Val.ctor n args') else w
        if bs then (w', true, cw || chs, rigidRemember w' c)
        else (w', false, cw || chs, c)
      | .app f a =>
        let (f', bf, chf, c) := nfSU fuel f c
        let (a', ba, cha, c) := nfSU fuel a c
        let w' := if chf || cha then intern (Val.app f' a') else w
        if bf && ba && !headRedexApp w' then (w', true, cw || chf || cha, rigidRemember w' c)
        else (w', false, cw || chf || cha, c)
      | .idT x y z =>
        let (x', bx, chx, c) := nfSU fuel x c
        let (y', by', chy, c) := nfSU fuel y c
        let (z', bz, chz, c) := nfSU fuel z c
        let w' := if chx || chy || chz then intern (Val.idT x' y' z') else w
        if bx && by' && bz then (w', true, cw || chx || chy || chz, rigidRemember w' c)
        else (w', false, cw || chx || chy || chz, c)
      | w => (w, true, cw, rigidRemember w c)   -- leaves: rigid by definition (see above)
  private unsafe def nfSListU : Nat → List Val → NormCache → List Val × Bool × Bool × NormCache
    | _, [], c => ([], true, false, c)
    | fuel, vs@(v :: rest), c =>
      let (v', bv, chv, c) := nfSU fuel v c
      let (rest', bs, chr, c) := nfSListU fuel rest c
      if chv || chr then (v' :: rest', bv && bs, true, c)
      else (vs, bv && bs, false, c)
end
attribute [implemented_by nfSU] nfS
attribute [implemented_by nfSListU] nfSList


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
  | _ => none

end Dllbc.Val
