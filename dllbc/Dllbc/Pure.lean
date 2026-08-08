import Dllbc.Value

/-!
# The pure fragment's reduction (§4)

The comptime fragment is a tiny standard type theory: one universe (type-in-
type), Π, Σ, λ, application, constructors, and a fixed basis of recursors as
built-in constants (`natRec`, `boolRec`, `botElim`). This module is the
evaluator over `Val`. Pure binders carry their source NAME (M30 step 2); β and ι
fire by **environment extension** (M30 — see the NbE section below, and
`docs/nbe.md`), and a `sym` (or a `pvar`) at an application/recursor head blocks
reduction — the whole spine is then a legal (stuck neutral) value.

`readC` (⇝) and `hasType` (in `Machine.lean`) are built on top: `readC`
reflects a `Term` into a `Val` (resolving Ω snapshot reads) and normalizes it
here; `hasType` uses `convert` and the constructor signature table.

Everything is total: `eval`/`whnfN`/`readback` take explicit fuel, and the
value traversals recurse structurally (mutual with a list helper for constructor
arguments). There is no substitution and no index arithmetic: `substPure`,
`shiftPure` and the delayed-lift machinery were deleted in M30 step 1, and the
indices themselves in step 2 — there is no arithmetic of ANY kind below.
-/

namespace Dllbc.Val

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
  .lam "a" kNatTy (.lam "b" kNatTy (kNatRecS (.lam "_" kNatTy kNatTy) (.pvar "b")
    (.lam "a'" kNatTy (.lam "r" kNatTy (.ctor "S" [.pvar "r"]))) (.pvar "a")))
def kAdd (a b : Val) : Val := .app (.app kAddFn a) b

/-- `Le : Nat → Nat → Type` as a computing predicate (`Z ≤ _ ↦ ⊤`, `S ≤ Z ↦ ⊥`,
    `S ≤ S ↦ recurse`). Premise (2)'s obligation type is built from this. -/
def kLeFn : Val :=
  .lam "a" kNatTy (kNatRecS (.lam "_" kNatTy (.pi "_" kNatTy .type)) (.lam "_" kNatTy kUnitTy)
    (.lam "a'" kNatTy (.lam "f" (.pi "_" kNatTy .type) (.lam "b" kNatTy
      (kNatRecS (.lam "_" kNatTy .type) kBotTy
        (.lam "b'" kNatTy (.lam "_" .type (.app (.pvar "f") (.pvar "b'")))) (.pvar "b")))))
    (.pvar "a"))
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

/-- The comptime environment: name ↦ value, innermost first. Prepending IS
    shadowing, and `List.lookup` finding the first match IS the scope rule. -/
abbrev PEnv := List (String × Val)

/-- Collect an application spine into its head and argument list (in order). -/
def collectSpine : Val → Val × List Val
  | .app f a => let (h, as) := collectSpine f; (h, as ++ [a])
  | v => (v, [])

/-- Rebuild an application spine from a head and argument list. -/
def rebuildSpine : Val → List Val → Val
  | h, [] => h
  | h, a :: as => rebuildSpine (.app h a) as

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
    `substPure 0 a b` to `instBody x b a`. That is why 18 substitution sites became
    18 one-word edits rather than a rewrite of the checker.

    It also means the domain is **mixed**: a `Val` may be syntax (a hand-built
    recursor premise type, a term just reflected from the surface) or semantics (a
    value `eval` produced), and the two differ only in whether binder bodies are
    closures. `instBody` accepts both — a closure carries its own environment, a
    syntactic body gets the singleton `[(x, arg)]` — and that is exactly right,
    because a syntactic binder reached this way is closed but for its own variable.

    ### One variable convention (M30 step 2)

    There used to be two, disagreeing about arithmetic: a bound index looked up,
    a free index down-shifted by `|ρ|`, and a `lvl` minted by readback converted
    back by `d - 1 - j`. Under names there is one rule and no arithmetic —

      * `pvar x` with `x` in `ρ` is **bound**: look it up.
      * `pvar x` otherwise is **free**, and evaluates to itself.

    — which is why the `lvl` former is gone: readback opens a binder at a fresh
    `pvar`, and a fresh `pvar` is already the neutral it needed `lvl` to express.

    ### Freshness, and why it is a LEVEL and not a counter

    `readback` renames every binder it opens to `readbackName ⟨its level⟩`. That
    is a reserved name (`§0`, `§1`, …) which no source program can write, so it
    cannot capture what it descends past; and it is a function of the level alone,
    so **readback output is canonical**: two α-variant functions read back to the
    same tree, which is what lets `convert` stay `nfV a == nfV b` on the nose.

    The invariant that makes it capture-free in the other direction, stated once
    because everything below depends on it: *`readback` at depth `d` is applied
    only to values whose free reserved names are all below `d`*. It holds at the
    three exported entry points (`nfN`, `whnfOut`, `instBodyOut`), which read back
    from depth 0 and are handed checker values, in which every reserved name is
    bound; and it is preserved by the recursion, which mints `§d` while descending
    into a body whose only new free name is that same `§d`.

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
def mkClosure (ρ : PEnv) (body : Val) : Val :=
  match body with
  | .closure _ _ => body
  | b =>
    if hasStateMarkerEnv ρ then
      .const "@@capture: a λ/Π closed over a state marker (⊥/loan/borrow) — §3.2 knowledge/state"
    else .closure ρ b

mutual
  /-- Evaluate `v` (read as pure syntax) against the comptime environment `ρ`.
      Strong everywhere except under a binder, where the body is suspended.

      Runtime forms — `⊥`, `loanM`, `borrowM`, `rfn` — are LEAVES, exactly as they
      were for `shiftPure`/`substPure`. That is not an omission: a borrow payload
      is state, `eval` computes knowledge, and descending into one would be the
      first step of the door §3.3 is holding shut. -/
  def eval : Nat → PEnv → Val → Val
    | 0, _, v => v
    | fuel + 1, ρ, v =>
      match v with
      | .pvar x =>
        match ρ.lookup x with
        | some w => w
        | none => .pvar x                       -- free: a name means itself
      | .lam x dom body => .lam x (eval (fuel + 1) ρ dom) (mkClosure ρ body)
      | .pi x dom cod => .pi x (eval (fuel + 1) ρ dom) (mkClosure ρ cod)
      | .sigmaT x dom cod => .sigmaT x (eval (fuel + 1) ρ dom) (mkClosure ρ cod)
      | .cmpT τ => .cmpT (eval (fuel + 1) ρ τ)
      | .app f a => whnfN false (fuel + 1) (.app (eval (fuel + 1) ρ f) (eval (fuel + 1) ρ a))
      | .ctor n args => .ctor n (evalList (fuel + 1) ρ args)
      | .idT a b c => .idT (eval (fuel + 1) ρ a) (eval (fuel + 1) ρ b) (eval (fuel + 1) ρ c)
      | w => w        -- type, const, sym, closure, ⊥, loanM, borrowM, rfn
  termination_by fuel _ v => (fuel, 1, sizeOf v)
  def evalList : Nat → PEnv → List Val → List Val
    | _, _, [] => []
    | fuel, ρ, v :: vs => eval fuel ρ v :: evalList fuel ρ vs
  termination_by fuel _ vs => (fuel, 1, sizeOf vs)
  /-- **Open the binder `x` at `arg`** — the single operation that replaces
      `substPure 0 arg body` at all eighteen of its sites.

      Both shapes of body are legal, and the asymmetry is the mixed domain showing
      through rather than a special case: a `closure` was built by `eval` and knows
      the environment it needs, while a bare body is syntax whose only free variable
      is the binder's own, so the singleton environment is complete for it. -/
  def instBody : Nat → String → Val → Val → Val
    | fuel, x, .closure ρ b, arg => eval fuel ((x, arg) :: ρ) b
    | fuel, x, b, arg => eval fuel [(x, arg)] b
  termination_by fuel _ _ _ => (fuel, 2, 0)
  /-- Weak-head reduction over the mixed domain: β and ι, head redex only.

      Structurally the `whnfV` above it, with ONE line different — β opens the
      binder by environment extension instead of by substitution. Everything else
      (the recursor table, the array basis's computing constants, what counts as a
      stuck neutral) is the same calculus and is meant to read as the same rules. -/
  def whnfN : Bool → Nat → Val → Val
    | _, 0, v => v
    | rb, fuel + 1, v =>
      let (head, args) := collectSpine v
      match head, args with
      | .lam x _ b, a :: rest =>                      -- β, by capture
        whnfN rb fuel (rebuildSpine
          (if rb then readback fuel 0 (instBody fuel x b a) else instBody fuel x b a) rest)
      | .const "natRec", motive :: z :: s :: n :: rest =>
        match whnfN rb fuel n with
        | .ctor "Z" [] => whnfN rb fuel (rebuildSpine z rest)
        | .ctor "S" [m] =>
          let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
          whnfN rb fuel (rebuildSpine (.app (.app s m) recCall) rest)
        | n' => rebuildSpine (.const "natRec") (motive :: z :: s :: n' :: rest)
      | .const "boolRec", motive :: t :: f :: b :: rest =>
        match whnfN rb fuel b with
        | .ctor "True" [] => whnfN rb fuel (rebuildSpine t rest)
        | .ctor "False" [] => whnfN rb fuel (rebuildSpine f rest)
        | b' => rebuildSpine (.const "boolRec") (motive :: t :: f :: b' :: rest)
      | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
        match whnfN rb fuel l with
        | .ctor "Nil" [] => whnfN rb fuel (rebuildSpine pn rest)
        | .ctor "Cons" [h, t] =>
          let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
          whnfN rb fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)
        | l' => rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l' :: rest)
      | .const "sigmaRec", a :: b :: motive :: f :: p :: rest =>
        match whnfN rb fuel p with
        | .ctor "Pair" [x, y] => whnfN rb fuel (rebuildSpine (.app (.app f x) y) rest)
        | p' => rebuildSpine (.const "sigmaRec") (a :: b :: motive :: f :: p' :: rest)
      | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
        match whnfN rb fuel p with
        | .ctor "Refl" [] => whnfN rb fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p' :: rest)
      | .const "k", _A :: _a :: _P :: d :: p :: rest =>
        match whnfN rb fuel p with
        | .ctor "Refl" [] => whnfN rb fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p' :: rest)
      | .const "arrCat", m :: k :: a :: b :: rest =>
        match whnfN rb fuel a, whnfN rb fuel b with
        | .ctor "Arr" [], b' => whnfN rb fuel (rebuildSpine b' rest)
        | a', .ctor "Arr" [] => whnfN rb fuel (rebuildSpine a' rest)
        | .ctor "Arr" xs, .ctor "Arr" ys => whnfN rb fuel (rebuildSpine (.ctor "Arr" (xs ++ ys)) rest)
        | .app (.app (.app (.const "acons") m') x) xs, b' =>
          whnfN rb fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (kAdd m' k)) x)
              (.app (.app (.app (.app (.const "arrCat") m') k) xs) b')) rest)
        | .ctor "Arr" (x :: xs), b' =>
          let tlLen := valOfNat xs.length
          whnfN rb fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (kAdd tlLen k)) x)
              (.app (.app (.app (.app (.const "arrCat") tlLen) k) (.ctor "Arr" xs)) b')) rest)
        | a', b' => rebuildSpine (.const "arrCat") (m :: k :: a' :: b' :: rest)
      | .const "aget", tt :: n :: i :: a :: rest =>
        match natOfVal? (whnfN rb fuel i), whnfN rb fuel a with
        | some j, .ctor "Arr" vs =>
          match vs.get? j with
          | some w => whnfN rb fuel (rebuildSpine w rest)
          | none => rebuildSpine (.const "aget") (tt :: n :: i :: .ctor "Arr" vs :: rest)
        | _, a' => rebuildSpine (.const "aget") (tt :: n :: i :: a' :: rest)
      | .const "acons", n :: x :: xs :: rest =>
        match whnfN rb fuel xs with
        | .ctor "Arr" vs => whnfN rb fuel (rebuildSpine (.ctor "Arr" (x :: vs)) rest)
        | xs' => rebuildSpine (.const "acons") (n :: x :: xs' :: rest)
      | .const "arrRec", tt :: motive :: pn :: pc :: n :: a :: rest =>
        match whnfN rb fuel a with
        | .ctor "Arr" [] => whnfN rb fuel (rebuildSpine pn rest)
        | .ctor "Arr" (x :: vs) =>
          let tl : Val := .ctor "Arr" vs
          let k : Val := valOfNat vs.length
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, k, tl]
          whnfN rb fuel (rebuildSpine (rebuildSpine pc [k, x, tl, recCall]) rest)
        | .app (.app (.app (.const "acons") m') x) xs =>
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, m', xs]
          whnfN rb fuel (rebuildSpine (rebuildSpine pc [m', x, xs, recCall]) rest)
        | a' => rebuildSpine (.const "arrRec") (tt :: motive :: pn :: pc :: n :: a' :: rest)
      | _, _ => rebuildSpine head args
  termination_by _ fuel _ => (fuel, 0, 0)
  /-- Read a value back to closure-free syntax, renaming every binder it opens to
      its LEVEL — see the note below the block for why this is in it, and the
      freshness paragraph above for why the renaming is what makes the output
      canonical rather than merely closure-free. -/
  def readback : Nat → Nat → Val → Val
    | 0, _, v => v
    | fuel + 1, depth, v =>
      match whnfN false (fuel + 1) v with
      -- The binder is opened at its OWN name (`nm`, which is what its body's
      -- occurrences say) and bound to the fresh `x`; the node that comes back
      -- carries `x`. Passing `x` on both sides would bind a name the body never
      -- mentions and leave every occurrence free — the one way this rewrite can be
      -- got wrong, and the only reason `nm` is still read at all.
      | .lam nm dom body =>
        let x := readbackName depth
        .lam x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm body (.pvar x)))
      | .pi nm dom cod =>
        let x := readbackName depth
        .pi x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm cod (.pvar x)))
      | .sigmaT nm dom cod =>
        let x := readbackName depth
        .sigmaT x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm cod (.pvar x)))
      | .cmpT τ => .cmpT (readback fuel depth τ)
      | .app f a => .app (readback fuel depth f) (readback fuel depth a)
      | .ctor n args => .ctor n (readbackList fuel depth args)
      | .idT a b c => .idT (readback fuel depth a) (readback fuel depth b) (readback fuel depth c)
      | w => w        -- pvar, type, const, sym, ⊥, loanM, borrowM, rfn: leaves
  termination_by fuel _ _ => (fuel, 3, 0)
  def readbackList : Nat → Nat → List Val → List Val
    | _, _, [] => []
    | fuel, depth, v :: vs => readback fuel depth v :: readbackList fuel depth vs
  termination_by fuel _ vs => (fuel, 3, vs.length + 1)
end

/-! **Readback lives INSIDE the block above**, and that placement is the M30
    correction that made the corpus green rather than a tidiness choice.

    The first draft let closures escape into checker state: `whnfN`'s β returned an
    evaluated body, whose binders are closures, and that value flowed into Ω,
    `sctx` and the obligations. Every conversion still agreed — the differentials
    over `nfV`, over binder-opening and over weak-head reduction all found ZERO
    divergence — and the corpus still failed, at quicksort's count equation.

    The reason is §19. `generalizeStuck` abstracts a stuck spine out of *all*
    σ-bearing state by STRUCTURAL IDENTITY (`abstractInto`'s `v == target`), with
    the target a normalized spine. A closure holds its body UNEVALUATED, so the
    same spine sits inside it in a different shape, `==` misses it, and the
    generalization silently leaves an occurrence behind — after which the branch
    equation that occurrence was supposed to become never fires. No conversion is
    wrong anywhere; a comparison simply stops seeing.

    So the rule, enforced by construction rather than by audit: **closures never
    leave this file.** `readback` is applied at the two places a value crosses out
    of normalization — β's reduct, and `instBody`'s exported form below — and the
    checker goes on seeing the first-order trees it compares, prints, canonicalizes
    and searches. What NbE deletes is unchanged: there is no index arithmetic left
    anywhere, `substPure`/`shiftPure` are gone, and binder opening is environment
    extension. What it does not buy, here, is closures as a value form — nbe.md
    §6.1 files that under attack surface rather than under motivation, and this is
    that item coming due.

    The named consequence for §4.3 (step 3): contracts-as-closures puts closures
    back into exactly the state `generalizeStuck` sweeps, so it must answer this
    same question rather than inherit an answer. -/

/-- Normal form by evaluation: evaluate against the empty environment, read back
    from depth zero. Intended to be **extensionally identical** to `nfV`, which is
    what the M30 differential asserts over the corpus rather than assumes. -/
def nfN (fuel : Nat) (v : Val) : Val := readback fuel 0 (eval fuel [] v)

/-- **Weak-head reduction, for callers outside this file.** Same rules; the
    difference is that a β reduct is read back, so no closure ever crosses out.
    Only this entry point may do that: `readback` itself calls `whnfN` at a
    NON-ZERO depth, on values carrying levels, and a depth-0 readback there would
    convert every level by the wrong offset. (Found the hard way — doing it inside
    `whnfN` unconditionally turned two failures into eighty.) -/
def whnfOut (fuel : Nat) (v : Val) : Val := whnfN true fuel v

/-- **Open a binder, for callers outside this file** — the replacement for
    `substPure 0 arg body` at all eighteen of its sites.

    It reads the result back, which is the rule stated above `readback`: the
    checker compares, prints, canonicalizes and searches its values, and every one
    of those operations is defined on first-order trees. The cost is a normalization
    of the opened body, which is what `substPure` followed by the caller's `nfV`
    already amounted to at eleven of the eighteen sites. -/
def instBodyOut (fuel : Nat) (x : String) (body arg : Val) : Val :=
  readback fuel 0 (instBody fuel x body arg)

/-! ## `let`, and how the comptime fragment reads one (M29 α; rebuilt in M30 step 2)

    **`let` is a form BOTH arrows read.** ⇒ binds an Ω slot; ⇝'s reading is β —
    `let x = e ; rest` is `rest` with `x`'s occurrences replaced by `e`'s value.
    The two reflections that implement ⇝ (`Term.toValPure` below, monad-free, and
    `reflectC` in `Machine.lean`, which additionally resolves Ω snapshots) share
    this vocabulary so that there is one statement of the rule rather than two.

    **And it is now the β-REDEX, built rather than carried.** M29 α carried the
    substitution instead — a `LetCtx` recording each binding with the pure-binder
    DEPTH it was made at, and a lookup that lifted the value by the difference
    (`shiftPure`, then `readback`) — because building the redex means abstracting
    `x` out of `rest`, which takes both reflections off their structural recursion.

    Under names there is nothing to abstract: a `let`'s occurrences are already
    `.var x` and mapping them to a pure name is a leaf rewrite the recursion does
    on the way past. So the reflection emits `(λ ⟨x's reserved name⟩ : Type. rest) e`
    and the evaluator does the rest, which is strictly better than what it
    replaces on the point that matters — **the transplant is gone.** Carrying a
    value from its binding site to an occurrence under further binders is exactly
    the move that captures under names (nbe.md §5's "NbE never transplants a body"
    was a claim about `eval`, and `LetCtx` was the one place in the tree that did
    it anyway); an environment extension cannot, because the argument is a VALUE
    before the inner binder is ever entered.

    The redex's binder is `letName x.id` — reserved, so no source binder can
    shadow it and no `let` can shadow another (runtime ids are globally unique).
    Its domain is `Type` and is never read: β discards the domain, and every
    consumer of these reflections normalizes. -/

/-- The pure binder a reflected `let` binds, for the runtime slot `id`. Reserved
    (`isReservedName`), which is what makes the redex capture-free. -/
def letName (id : Nat) : String := "§let" ++ toString id

/-- The reflected `let x = rhs ; rest`: the β-redex, with `x`'s occurrences in
    `rest` already rewritten to `letName x.id` by the caller's traversal. -/
def letRedex (id : Nat) (rhs rest : Val) : Val := .app (.lam (letName id) .type rest) rhs

/-! Reflect a PURE `Term` into a `Val` (no monad, no Ω): the borrow-free fragment
    only — `var`/`deref`/runtime forms map to `⊥` (they never occur in a pure
    goal). Used by `Std.nfTerm` to normalize a §18 generalize goal so a computed
    subterm (an `eqb`-spine hidden in a `count`-unfolding) is exposed before
    `abstractOccurrences`.

    A `let` is read by β, as the redex above. A `.var` that is NOT let-bound still
    maps to `⊥`: with no Ω there is nothing else it could be, and the distinction
    is exactly the one this reflection is for — a `let` is part of the pure term,
    an Ω snapshot is not. `lets` is the list of ids currently bound, innermost
    first, which is all the scope information a name-keyed reading needs. -/
mutual
  def Term.toValPureGo (lets : List Nat) : Term → Val
    | .type => .type
    | .const k => .const k
    | .pvar x => .pvar x
    | .var x => if lets.contains x.id then .pvar (letName x.id) else .bot
    | .letIn x rhs rest =>
      letRedex x.id (Term.toValPureGo lets rhs) (Term.toValPureGo (x.id :: lets) rest)
    | .cmpT τ => .cmpT (Term.toValPureGo lets τ)
    | .pi x d cod => .pi x (Term.toValPureGo lets d) (Term.toValPureGo lets cod)
    | .sigmaT x d cod => .sigmaT x (Term.toValPureGo lets d) (Term.toValPureGo lets cod)
    | .lam x d b => .lam x (Term.toValPureGo lets d) (Term.toValPureGo lets b)
    | .app f a => .app (Term.toValPureGo lets f) (Term.toValPureGo lets a)
    | .idT a b b' => .idT (Term.toValPureGo lets a) (Term.toValPureGo lets b) (Term.toValPureGo lets b')
    | .ctorApp n args => .ctor n (Term.toValPureListGo lets args)
    | .unit => .ctor "unit" []
    | _ => .bot                                          -- runtime forms: absent in pure goals
  termination_by t => sizeOf t
  def Term.toValPureListGo (lets : List Nat) : List Term → List Val
    | [] => []
    | t :: ts => Term.toValPureGo lets t :: Term.toValPureListGo lets ts
  termination_by ts => sizeOf ts
end

def Term.toValPure (t : Term) : Val := Term.toValPureGo [] t

def Term.toValPureList (ts : List Term) : List Val := Term.toValPureListGo [] ts

/-! ## Full normalization and conversion -/

/-- Normal form: `nfN`, and there is no longer a second one to compare it against.
    The substitution normalizer and the whole-corpus differential that ran the two
    against each other were deleted with `substPure` — the evidence they produced
    is in the M30 step-1b commit, and keeping a second evaluator alive to re-derive
    it on every build is exactly the two-evaluator era the milestone said must not
    reach main. -/
def nfV (fuel : Nat) (v : Val) : Val := nfN fuel v

/-- Definitional conversion: equal normal forms. For this fragment (β, ι, no eta)
    normal forms are canonical, so normal-form equality *is* convertibility —
    simpler than a lazy whnf-and-compare recursion and, for a normalizing system,
    equivalent.

    **Canonical up to binder names is what `readback` buys** (M30 step 2), and it
    is the whole reason this can stay a literal `==` now that binders have names:
    readback renames each one to its level, so `nfV` forgets what a binder was
    called. KernelFloor's readback-canonicality battery is where that is asserted
    rather than assumed. -/
def convert (fuel : Nat) (a b : Val) : Bool := nfV fuel a == nfV fuel b

/-! ## Segments (¶1.1): the carved array's state form

    An array value at `Array n T` is one of
      * `Arr [v₁ … v_n]`   — an owned flat run (also the knowledge form),
      * `sym σ`            — opaque,
      * a stuck neutral    — an `arrCat` spine,
      * `§segs [seg₁ … seg_k]` (k ≥ 2) — CARVED, each `§seg [c, body]`.

    The last is **state only**: reserved names with no `ctorSig` entry, so no program
    can write or match one, and every generic `Val` walker (`loanIds`, `symIds`,
    `renumber`, `hasStateMarker`, `beq`) traverses it unchanged — the
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
    telescope (dependent positions refer to earlier fields BY NAME — e.g.
    `Pair`'s second field, which is the Σ's codomain under the Σ's own binder).
    `none` means the constructor does not inhabit that type former. -/

/-- The field-type telescope of a constructor, given the whnf'd expected type.
    Each entry is `(the name later entries reach this field by, the field's
    type)`; `"_"` where nothing does. -/
structure CtorSig where
  fieldTypes : Val → Option (List (String × Val))

/-- The fixed constructor basis: Unit, Bool, Nat, List (element parameter),
    and Σ's `Pair` (dependent second field). -/
def ctorSig : String → Option CtorSig
  | "unit"  => some { fieldTypes := fun ty => match ty with | .const "Unit" => some [] | _ => none }
  | "True"  => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "False" => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "Z"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [] | _ => none }
  | "S"     => some { fieldTypes := fun ty =>
      match ty with | .const "Nat" => some [("_", .const "Nat")] | _ => none }
  | "Nil"   => some { fieldTypes := fun ty => match ty with | .app (.const "List") _ => some [] | _ => none }
  | "Cons"  => some { fieldTypes := fun ty =>
      match ty with
      | .app (.const "List") t => some [("_", t), ("_", .app (.const "List") t)]
      | _ => none }
  -- The one DEPENDENT entry in the table: `Pair`'s second field type is the Σ's
  -- codomain, a body under the Σ's own binder — so that binder is the name
  -- `checkFields` opens it at.
  | "Pair"  => some { fieldTypes := fun ty =>
      match ty with | .sigmaT x a b => some [(x, a), ("_", b)] | _ => none }
  -- `Arr` — the array literal (¶1.4). Its field telescope for a CONCRETE `n` is `T`
  -- repeated `n` times; at a symbolic `n` there is no constructor signature, and
  -- correctly so — one cannot write an array literal of unknown length. This is
  -- hand-written rather than §7-generated, which is the concrete cost basis
  -- membership carries (¶9c): the fixed basis and the declaration scheme can drift,
  -- and this entry is where the drift would start.
  | "Arr"   => some { fieldTypes := fun ty =>
      match asArrayTy? ty with
      | some (n, t) => (natOfVal? (Val.whnfOut 1000 n)).map (fun k => List.replicate k ("_", t))
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
  | .sigmaT _ _ _ => some ["Pair"]
  | .idT _ _ _    => some ["Refl"]                 -- §10: Id's only constructor
  -- `Array n T` has the single constructor `Arr` at a concrete `n`, and NO known
  -- constructor set at a symbolic one. ¶1.4: arrays are never matched anyway — an
  -- array's information is positional, reached by the place grammar, not by a tag —
  -- so this entry exists for exhaustiveness's benefit and is never consulted.
  | ty => match asArrayTy? ty with
    | some (n, _) => if (natOfVal? (Val.whnfOut 1000 n)).isSome then some ["Arr"] else none
    | none => none

end Dllbc.Val
