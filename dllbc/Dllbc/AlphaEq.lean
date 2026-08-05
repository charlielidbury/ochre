import Dllbc.Machine

/-!
# Alpha-equivalence of `FnDef`s up to runtime-var id renaming (§ point 4)

The corpus hand-numbers runtime binder ids ad-hoc and **reuses ids across
mutually-exclusive sibling branches** (partScan: `k2`=6 in one arm, `i2`=7 in the
other, id 7 reused for `c`). Any deterministic macro threads ids linearly, so its
bodies are only *alpha*-equivalent — same binding structure, different ids — to
those corpus Decls, and exact `BEq` cannot reach them.

`FnDef.alphaNorm` renumbers every runtime binding occurrence (telescope param,
`letIn`, `matchE` branch binder) to a fresh canonical id in pre-order traversal
order, with a **scoped** environment so sibling branches that reuse an id are
kept distinct. `FnDef.alphaEq a b := a.alphaNorm == b.alphaNorm` is then the
round-trip criterion for the multi-branch corpus bodies. Pure de Bruijn vars
(`pvar`) are untouched (they are not runtime ids); runtime vars embedded in types
(a `*v` under a `len`) renumber through the same traversal.
-/

namespace Dllbc

mutual
/-- Renumber runtime var ids under a scoped env (oldId → newId, innermost first)
    and a monotonic fresh-id counter. Returns the rewritten term and the counter. -/
partial def anTerm (env : List (Nat × Nat)) (ctr : Nat) : Term → (Term × Nat)
  | .var ⟨id, nm⟩ => (.var ⟨(env.lookup id).getD id, nm⟩, ctr)
  | .letIn ⟨id, nm⟩ rhs body =>
    let (rhs', c1) := anTerm env ctr rhs
    let newId := c1
    let (body', c2) := anTerm ((id, newId) :: env) (c1 + 1) body
    (.letIn ⟨newId, nm⟩ rhs' body', c2)
  | .matchE ⟨id, nm⟩ eqn branches =>
    let scrut : Var := ⟨(env.lookup id).getD id, nm⟩
    match eqn with
    | none =>
      let (branches', c') := anBranches env ctr branches
      (.matchE scrut none branches', c')
    | some ⟨eid, enm⟩ =>
      -- The branch-equation binder is one binder for the whole match, in scope
      -- in every branch — canonicalized once, before the branches.
      let (branches', c') := anBranches ((eid, ctr) :: env) (ctr + 1) branches
      (.matchE scrut (some ⟨ctr, enm⟩) branches', c')
  | .assign p e r =>
    let (p', c1) := anTerm env ctr p
    let (e', c2) := anTerm env c1 e
    let (r', c3) := anTerm env c2 r
    (.assign p' e' r', c3)
  | .seq a b => let (a', c1) := anTerm env ctr a; let (b', c2) := anTerm env c1 b; (.seq a' b', c2)
  | .ctorApp n args => let (args', c') := anList env ctr args; (.ctorApp n args', c')
  | .call n args => let (args', c') := anList env ctr args; (.call n args', c')
  | .borrow t => let (t', c') := anTerm env ctr t; (.borrow t', c')
  | .deref t => let (t', c') := anTerm env ctr t; (.deref t', c')
  | .app f a => let (f', c1) := anTerm env ctr f; let (a', c2) := anTerm env c1 a; (.app f' a', c2)
  | .pi d c => let (d', c1) := anTerm env ctr d; let (c', c2) := anTerm env c1 c; (.pi d' c', c2)
  | .sigmaT d c => let (d', c1) := anTerm env ctr d; let (c', c2) := anTerm env c1 c; (.sigmaT d' c', c2)
  | .lam d c => let (d', c1) := anTerm env ctr d; let (c', c2) := anTerm env c1 c; (.lam d' c', c2)
  | .idT a b c => let (a', c1) := anTerm env ctr a; let (b', c2) := anTerm env c1 b; let (c', c3) := anTerm env c2 c; (.idT a' b' c', c3)
  | .borrowT a b => let (a', c1) := anTerm env ctr a; let (b', c2) := anTerm env c1 b; (.borrowT a' b', c2)
  -- M26's three formers. Without these the criterion silently degrades to
  -- structural equality on any term containing one — which is what a `fn` macro's
  -- output is made of, and exactly the comparison phase D needs it for.
  | .seal t u => let (t', c1) := anTerm env ctr t; let (u', c2) := anTerm env c1 u; (.seal t' u', c2)
  | .callV ⟨id, nm⟩ args =>
    let callee : Var := ⟨(env.lookup id).getD id, nm⟩
    let (args', c') := anList env ctr args
    (.callV callee args', c')
  -- A runtime λ BINDS its binders, so they renumber like a branch's fields and are
  -- scoped to the body. Since M27 they also carry DOMAINS, which are types and so
  -- renumber through the same traversal every other type position does — under
  -- telescope scoping, because `ih`'s domain mentions the predecessor bound to its
  -- left. Leaving them un-normalized would make two α-equivalent arms compare
  -- unequal on their annotations alone, which is the criterion silently degrading
  -- to structural equality on exactly the terms it exists to compare.
  | .lamR xs body =>
    let (xs', ext, c1) := anLamBinders env xs ctr
    let (body', c2) := anTerm (ext ++ env) c1 body
    (.lamR xs' body', c2)
  -- A comptime domain can mention runtime vars (`λ (H : Le n m). …`), so it
  -- renumbers like any other type position rather than falling to the leaf case.
  | .cmpT τ => let (τ', c') := anTerm env ctr τ; (.cmpT τ', c')
  | t => (t, ctr)                                            -- pvar, type, const, unit — no runtime ids
partial def anList (env : List (Nat × Nat)) (ctr : Nat) : List Term → (List Term × Nat)
  | [] => ([], ctr)
  | t :: ts => let (t', c1) := anTerm env ctr t; let (ts', c2) := anList env c1 ts; (t' :: ts', c2)
partial def anBranches (env : List (Nat × Nat)) (ctr : Nat) : List Branch → (List Branch × Nat)
  | [] => ([], ctr)
  | .mk c binders body :: rest =>
    let (binders', ext, c1) := anBinders binders ctr
    let (body', c2) := anTerm (ext ++ env) c1 body              -- binders scoped to this branch only
    let (rest', c3) := anBranches env c2 rest                    -- siblings: base env, threaded ctr
    (.mk c binders' body' :: rest', c3)
partial def anBinders : List Var → Nat → (List Var × List (Nat × Nat) × Nat)
  | [], ctr => ([], [], ctr)
  | ⟨id, nm⟩ :: bs, ctr =>
    let newId := ctr
    let (bs', ext, c') := anBinders bs (ctr + 1)
    (⟨newId, nm⟩ :: bs', (id, newId) :: ext, c')
/-- A runtime λ's ANNOTATED binders (M27). Each domain is normalized under the
    binders to its left and none of its own, which is what makes it a telescope
    rather than a list. -/
partial def anLamBinders (env : List (Nat × Nat)) :
    List (Var × Term) → Nat → (List (Var × Term) × List (Nat × Nat) × Nat)
  | [], ctr => ([], [], ctr)
  | (⟨id, nm⟩, τ) :: bs, ctr =>
    let (τ', c1) := anTerm env ctr τ
    let newId := c1
    let (bs', ext, c2) := anLamBinders ((id, newId) :: env) bs (c1 + 1)
    ((⟨newId, nm⟩, τ') :: bs', (id, newId) :: ext, c2)
end

/-- Canonicalize a `FnDef`'s runtime var ids. Telescope params keep their positional
    ids `0 .. n-1` (identity-mapped — they are the same in any faithful surface);
    body binders are renumbered from `n` in pre-order. Types/back carry only param
    *uses*, so they are fixed points. -/
def FnDef.alphaNorm (d : FnDef) : FnDef :=
  let n := d.telescope.length
  let baseEnv := (List.range n).map (fun i => (i, i))
  { d with
    telescope := d.telescope.map (fun (nm, ty) => (nm, (anTerm baseEnv n ty).1)),
    retType := (anTerm baseEnv n d.retType).1,
    body := (anTerm baseEnv n d.body).1 }

-- Structural equality on `FnDef`. Relocated here in M27-P2 from
-- `Tests/SDeclMacro.lean`, which retired with the `decl{ … back = … }` surface it
-- round-tripped: the instance is not a property of that surface — it is what every
-- exact-equality assertion about a declaration needs — and it outlived its old home
-- by one phase, and it survives the kernel's own retirement of the name (M27-δ):
-- `FnDef` is a surface record now, and exact equality is still what every
-- assertion about one needs.
deriving instance BEq for Dllbc.FnDef

/-- Two `FnDef`s are equal up to runtime-var id renaming. Compared field-wise via
    the component `BEq`s (`Term`/`String`/`List`/`Option`) so no `BEq FnDef`
    instance is required here.

    ~~It compares neither `back` (gone with the mechanism in M27-P2) nor `dec`, and
    the `dec` blindness is a KNOWN LIMITATION: once the guard is deleted, `[k]` is
    purely a scrutinee-selection hint, and two definitions differing only in it
    elaborate to different recursors. Widening it is P5's, with the guard.~~

    **`dec` IS COMPARED NOW** (M27-δ), and the timing is the whole content: it
    became correct at exactly the moment the guard died. While `[k]` was a guard
    INPUT, two definitions differing only in it could still be the same function —
    the hint said which parameter to police, not what to build. Now it is purely
    the scrutinee-selection hint, so it decides which recursor `fnElab` emits, and
    two definitions differing in it are two different terms. A round-trip criterion
    blind to it would report equivalence for a pair that elaborates apart. -/
def FnDef.alphaEq (a b : FnDef) : Bool :=
  let a' := a.alphaNorm; let b' := b.alphaNorm
  a'.name == b'.name && a'.telescope == b'.telescope && a'.retType == b'.retType
    && a'.dec == b'.dec
    && a'.body == b'.body

end Dllbc
