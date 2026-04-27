# AppendVec investigation — why `Och.synth appendVec` fails

**Status**: investigation complete (2026-04-27). No fix shipped;
diagnostic test corpus pinned in `lean/Och/AppendVecPath.lean`.

## Question

`Och.synth Std.appendVec` returns `.error`. The original conjecture
(carried by the prior agent's commit message) was "engine
incompleteness on a dependent equation
`add_ (succ_ pred) n2 ≡ succ_ (add_ pred n2)`" — i.e. the
structural engine can't decide a finite β-reduction chain.

## Result

The conjecture is wrong. The engine handles the dependent
reductions just fine:

| Stage | Question | Engine verdict |
|------:|----------|---------------|
| A | `add_ (succ_ pred) n2 ⊑ succ_ (add_ pred n2)` (and reverse) | ✓ ok true |
| B | `Array_ (succ_ pred) T ⊑ Pair T (Array_ pred T)` (and reverse) | ✓ ok true |
| C | `Array_ (add_ (succ_ pred) n2) T ⊑ Pair T (Array_ (add_ pred n2) T)` | ✓ ok true |
| D | `?14 Type (λa. λb. a) ⊑ ?8` (the actual question synth asks) | ✗ ok false |
| E | `Och.synth Std.appendVec` | ✗ error |

A/B/C close because `succ_ pred` (with abstract `pred`) is *not*
considered `isNeutral` by `EvalSubst.lean`'s predicate (which only
flags an `.app` whose head is a level-var; `succ_`'s head is a
`.fix`, not a level-var). So `add_`'s and `Array_`'s outer fixes
both unfold past it, the cascade closes structurally, and Stage A's
β-equation drops out.

## The actual bail point

Localised by instrumenting `synth`'s `.app` arm to print the
failing `f`/`a`/`Γ` at the leaf error. At depth 15 (15 binders deep
into `appendVec`'s body, descending through every `.lam`/`.fix`/
`.iota` synth visits):

  - `raw a = (λp:(Pair Type Type). p Type (λa:Type. λb:Type. a)) ?14`
    — i.e. `fst_ ?14`.
  - After WHNF: `aV = ?14 Type (λa:Type. λb:Type. a)`.
  - `dom = ?8`.
  - `Γ[8] = Type` (the `λT:Type` binder of `appendArrays`'s
    inlined body).
  - `Γ[14] = Array_ (succ_ ?13) ?8` (the `λarr:(Array_ (succ_ pred) T)`
    of the succ branch).

The synth walk at this point is processing
`pair_ T (Array_ (add_ pred n2) T) (fst_ arr) …`. It checks
`fst_ arr ⊑ T`, where `T = ?8`. `fst_` is
`λp:(Pair Type Type). p Type (λa:Type. λb:Type. a)` — declared
return is `Type`, not the precise element type. Synth's question
to the engine is "does a `Type`-typed value belong to type `T`?".

The engine correctly answers `.ok false`:

  - `subCheckSubstMatch`'s `_, _` arm (`EvalSubst.lean` ~432–440)
    returns `.ok false` when LHS is canonical (lam, after the
    spine ascends `?14` to its declared type) and RHS is a free
    level-var.
  - There's no "RHS-ascend" rule. The declarative `bvar` rule
    only goes `bvar k ⊑ Γ[k]`, not the reverse, so adding such a
    rule would break soundness.

## Why the program "should" type-check operationally

`fst_ arr` operationally returns the head element of `arr`, which
*is* a `T` when `arr : Array_ (succ_ pred) T = Pair T (Array_ pred T)`.
But that precision is recoverable only by inlining the eliminator:
`arr T (λa:T. λb:(Array_ pred T). a)`. The Std-level `fst_` ascends
to `Pair Type Type → Type`, deliberately losing precision (see
`Std/Pair.lean`'s docstring: "fst_ p : Type, not : A. For precise
projections, write the eliminator inline").

`appendArrays` and `appendVec` use the loose `fst_` / `snd_` rather
than inline projections, and so the bidirectional check on
appendVec hits a precision-mismatch wall.

## Fixes considered, none shipped

### Program-level: inline projections

Rewrite `appendArrays`'s succ branch as
`pair_ T (Array_ (add_ pred n2) T) (arr T (λa:T. λb:(Array_ pred T). a)) (self T pred n2 (arr (Array_ pred T) (λa:T. λb:(Array_ pred T). b)) arr2)`.

This restores type precision and would let synth close. It was not
applied because:

- It mutates `Std.appendArrays`'s body, which is referenced by other
  pinned tests (`Std/Vec.lean`'s vecResult chain).
- The same precision loss exists in any other Std consumer that uses
  `fst_`/`snd_` on a typed Pair — fixing one consumer doesn't fix the
  pattern.

### Synth-level: β-spine fast-path

Mirror `TyCheck.tyInfer`'s β-fast-path: when synth sees a
`.app .lam .arg` chain, peel β-redexes by substituting one at a time
into the body, instead of walking the lambda body fresh under an
opaque level-var.

Implemented experimentally as a `synthAppSpine` helper alongside
`synthAppGeneric`. Result: doesn't fix this case. Even with the
fast-path, the failing question still surfaces because synth's
`.fix` and `.lam` arms still descend into `appendArrays`'s body
fresh (its outer `fix self : ... . λT. λn1. λn2. λarr1. λarr2. body`
gets walked binder-by-binder), where the inlined `fst_ arr` ends up
being processed under fresh-level-var typing regardless. The β-
spine optimization is real, but orthogonal to this bail.

The change was reverted before commit. Diff is preserved in this
commit's parent for reference but not landed.

### Engine-level: RHS-ascend rule

Add a structural rule "if `b` is a free level-var with `Γ[b] = ty`,
check `a ⊑ ty`". This is **unsound** under the current declarative
`Subtype'` rules — there's no `bvar_R` rule (the declarative `bvar`
goes one direction only). Adding it without a corresponding spec
extension breaks soundness. Out of scope.

## What this means for the engine-collapse refactor

The `synth + subCheck` API is structurally fine for forms whose
type-precision survives the bidirectional walk. The `appendVec`
case was the canonical one we couldn't pin pre-refactor (commented
out at `Std/Vec.lean` line 112), and we now have a precise
explanation: the program uses `fst_`/`snd_` whose declared types
lose precision, and the bidirectional walk asks correctly-false
questions as a consequence.

To make `appendVec` typecheck through `synth`, either:

  1. Rewrite Std consumers to use inline eliminators where
     precision matters.
  2. Extend the declarative spec with a sound RHS-ascent rule
     (likely as a `letE`-style binder elaboration rather than a
     subtyping rule), and update `Subtype'` accordingly.

Both are out of scope for the engine-collapse refactor.

## Test corpus

`lean/Och/AppendVecPath.lean` pins the staged investigation:

  - Stages A, B, C: `native_decide` `.ok true` pins on the engine's
    convertibility verdict at each step of the dependent reduction.
    These verify the engine's completeness is *not* the issue.
  - Stage D: `native_decide` `.ok false` pin on the synthetic
    version of synth's failing question. This pin is the
    well-typedness fact: the question synth asks is genuinely false
    by structural rules.
  - Stage E: `native_decide` `(Och.synth Std.appendVec).isError` —
    pinning the current behaviour so a future fix shows up as a
    test regression on this file.
