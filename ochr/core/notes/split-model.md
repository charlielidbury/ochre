# A model of case splitting on unknowns

Theory lane, 2026-10-29, branch `split-model` off main `4cc0beda`. Target: [Split],
[Split-gen], [T-Split-goal], refinement, generalisation records (D34/D37), the
re-normalisation of sealed programs under refinement, and `split f in t`. Method follows
the dependent-field model (D76): state principles and obligations, derive the rules, compare
with the checker, probe the gaps. Twice before, a fact leaked from one match arm into another
and gave a closed proof of `False` (paper §6.4, §7.2); this note is about ruling that class
out by construction.

## 1. The model

Checking a `match p { Cᵢ ⇒ tᵢ }` on a place `p` whose content is an unknown `σ` of an
inductive `D(ā)`:

- **Worlds.** Each arm `i` is a separate *world*: the one in which `σ` is `Cᵢ(σᵢ₁, …)`, with
  the fields fresh unknowns at their telescope types. The worlds are mutually exclusive and
  jointly exhaustive — `σ` is some constructor, and exactly one per arm.
- **Refinement is substitution.** Entering world `i` substitutes `σ := Cᵢ(σ̄)` everywhere `σ`
  can occur: the environment, every stored type, the types of other unknowns, the goal, and
  the sealed programs and closures that embed values. A world is the original state with that
  substitution applied, nothing more.
- **Generalisation.** A match on a *neutral that is not a bare unknown* (a sealed program `n`
  left by a stuck call) is first generalised: replace `n` everywhere by a fresh unknown `σ`,
  record `n ↦ σ`, then split `σ`. The record exists so that if the same text `n` is derived
  again on this path it is replaced by the same `σ` (finding G1/D34): one program, one meaning,
  within one world.
- **The block.** After the arms, the match is closed off (it was stuck on `σ`), as a call to
  an anonymous function of the places the arms use, and checking continues once from the
  *unrefined* state. The block stands for "whatever this match computes once `σ` is known".

A model where types are sets (docs/14 R1): `σ` of `D(ā)` denotes an element of the set
`⟦D(ā)⟧`, which is the disjoint union of its constructors' field tuples. "By cases on which
constructor" is the elimination principle of that disjoint union: to conclude something for
every element it suffices to conclude it for each `Cᵢ(σ̄)`. Each arm is one summand. A fact
proved in summand `i` is a fact about `Cᵢ(σ̄)` only; it is **not** a fact about the union, so
it cannot be used in summand `j`.

## 2. Principles and obligations

- **(X) Worlds are exclusive.** No fact established while checking arm `i` may be visible while
  checking arm `j`. A fact is anything the refinement produced or that was derived under it:
  a refinement `σ := Cᵢ(σ̄)`, a stored type refined by it, a generalisation record made in the
  arm, a captured value, an η-refinement made in the arm.
- **(S) Refinement is total substitution.** Entering a world substitutes `σ` in *every* place
  it can occur. A component the substitution skips keeps a pre-refinement value in a
  refined world: that value is stale, and reading it is reading a falsehood. The components
  are: Ω's values; the stored type of every binding; the type of every unknown; the goal; and
  the values embedded in sealed programs and closures (which re-normalise, since a stuck run
  may now make progress).
- **(G) One text, one meaning, one world.** A generalisation record `n ↦ σ` is in force for the
  world that made it and its sub-worlds (private copies, further splits within the arm), and
  nowhere else. Reusing it in a sibling arm violates (X): the same text `n` can denote values
  of different types in different arms, because `n` may mention the scrutinee (reviewer-6 A1).
- **(B) The block is checked from the unrefined state.** What follows the match is checked once,
  with `σ` still unknown, so it may not assume any arm's refinement. Its own sealed programs
  re-run and resolve as soon as a later split learns `σ` ([Seal-stuck]).

(X) is the heart: the other three are the ways a checker can break it by sharing the wrong
piece of state between arms.

## 3. Derived rules vs. the checker

| Derived | Checker | Verdict |
|---|---|---|
| (S) substitute `σ` in Ω, stored types, unknown types, goal | `refine` → `substEnv … types:=true` (Ω, bindings' types, `absTy`, goal) | matches |
| (S) re-normalise embedded sealed programs after refining a generalised neutral | `refine`: `if neutrals.any (·.2==σ) then renormAll`; `renormV`/`renormT` reach into sealed programs, closures and Π-types | matches |
| (X) drop an arm's refinements on exit | `exitWorld` (was `restoreArm`/`restoreKeep`): base is the snapshot, so `refs`, `env`, `goal`, bindings restored | matches |
| (G) drop an arm's generalisation records on exit | `exitWorld` (was `restoreArm`): `neutrals` not in its kept set | matches |
| (X) old unknowns' refined types do not leak | `restoreKeep`: `absTy` for old σ restored to `saved`; only new σ's kept | matches |
| fresh names never reused across worlds | `nextAbs`/`nextLoan` kept global | matches (a kept counter is not a kept *fact*) |
| (B) continue from the unrefined state | `splitArmsThenClose`: `closeOffMatch … ` runs from `saved` restored | matches |
| split a neutral's constructors from its **type**, never its patterns | `scrutType`/`natScrutinee` before splitting | matches (fuzz-port M2) |

Every current rule corresponds to a derived one; I found no derived obligation the checker
omits. The two historical holes are both closed and both are instances of (X): the closure
capture leak (D-era) and the generalisation-record reuse (reviewer-6 A1, closed by
`restoreArm` dropping `neutrals`).

### The one component kept across worlds that is not a counter

`etaRefs` (D68: `σ ↦ Cᵢ(σ̄)` for a *one-constructor* inductive) is kept global across arms
(`restoreKeep` keeps `cur.etaRefs`), and `movedPlace` actually *refines* `σ` by it. This looks
like it violates (X), since it is a refinement surviving across worlds. It is safe, and the
model says why: an η-refinement is **world-independent**. It is derived from `σ`'s type alone
(the type has one constructor, so `σ` must be it in *every* world), not from any sibling's
case split. It is a fact about the union, not about a summand, so (X) does not forbid sharing
it. The same argument licenses keeping `absTy` for *new* unknowns (never named in a sibling)
and the name counters. This is worth stating in the paper as the precise reason `etaRefs` and
`nextAbs` may be global while `refs` and `neutrals` may not.

## 4. Probes

All run through `lake env lean` on the built tree, verdicts printed explicitly, each with a
`def Control : False := refl` that is correctly rejected (so the harness is live, not a stale
olean). Programs in `/tmp` scratch, not committed (no finding to pin).

- **SPGen:** two sibling arms each generalise the same opaque call `Opaque(())` and match it.
  Accepted and benign — no type conflict, since `Opaque`'s result type does not depend on the
  scrutinee. Confirms generalisation per arm does not error spuriously.
- **SPLeak:** an opaque *definition* whose result type `TB(n)` is `Void` in one arm. Rejected
  at construction: a total function into a sometimes-empty type cannot be written
  (`match p {}` needs `p : Void`). So this shape cannot even produce the opaque call; the
  danger needs a function *parameter*.
- **SPParam:** a function parameter `g : Π(n:Word). TB(n)` with `TB(Zero)=One`, `TB(Succ _)=Void`;
  arm `Zero` matches `g(n)`, whose type refines to `One`. `Cross` is **accepted**, and this is
  sound: it is a function under the hypothesis that such a `g` exists, and none does
  (`TB(Succ 0)=Void`), so it can never be called to yield a contradiction. The arm-`Zero`
  generalisation `g(n) ↦ σ:One` is dropped on exit (G), and arm `Succ` never sees it.

No new hole found by hand. The construction that would test (X) hardest — the same
scrutinee-dependent text generalised at incompatible types in two arms — is reviewer-6 A1,
which `restoreArm` closes; I could not rebuild it into an acceptance.

## 5. Choke point: `enterWorld` / `inWorld` / `exitWorld` (landed)

The first version of this note left this as a proposal, because `restoreKeep` is shared with `onCopy` and `nfSealed`, where the kept set differs. The coordinator's answer: do not share it. Landed on this branch:

- `Env.lean`: `World` (the snapshot an arm starts from), `enterWorld`, `exitWorld`, `inWorld w x` (run `x`, then leave the world). `restoreArm` is deleted. `exitWorld` has its own body, not `restoreKeep`'s, and its docstring lists exactly what it keeps and why against (X): the name counters (`nextAbs`, `nextLoan`, `nextRecUid`), the types of abstract values created inside the arm, `etaRefs`, the [Rec] candidates and the pure caches. Everything else, `neutrals` included, is restored. A field added to `MState` is therefore restored by default, and keeping one is a claim that must be argued in that docstring.
- `Machine.lean`: every arm of [Split] (`splitArmsThenClose`), the by-type match on a proof (`evalMatchByType`, both its untyped and typed loops), the tail splits of `checkTailAt` on `Nat` and on inductives, the by-type tail match, and `split f in t` run inside `inWorld w do …`, with `w ← enterWorld` taken once before the first arm. What an arm hands back to the split (its type, its moves, its end state for D72's check, its proof flag) is returned from the `inWorld` block, read before the world is left.
- `onCopy`/`nfSealed`/`stuckScrutinee` keep `restoreKeep`, whose kept set is a private copy's (it keeps `neutrals`: a copy stays within its world, D37).
- Not converted: [T-J-stuck]'s transported-term check, which uses `restoreKeep` and so keeps the term's generalisation records. It makes no refinement, so it opens no world, and a record it keeps is a renaming within the current world, which (G) allows. That site is reworked by D75/D76 on the unmerged `depfields-model` branch, so it is left alone here to avoid a conflict.

Verdict-neutral: `lake build` green (97 jobs), every verdict assertion and the total guard unchanged. The only reorderings are a fresh name taken inside the second arm's world rather than between the arms, which the kept counter makes identical, and an arm's proof flag read into a local rather than straight into `allProof`.

## 5b. The original proposal

The components that must be restored per arm (`refs`, `neutrals`, `env`, `goal`, bindings'
types, old `absTy`) and those that may be kept (`etaRefs`, new `absTy`, counters) are split
across `restoreKeep` and `restoreArm` by hand, with the correctness of the split argued in two
code comments. (X) says the invariant exactly: **on arm exit, every component that a refinement
could have written is restored, and only world-independent facts and fresh-name counters are
kept.** A single `enterWorld`/`exitWorld` pair that takes the snapshot and restores exactly the
refinement-reachable components, with the kept set named and justified against (X) in one
place, would make a future "keep one more field for convenience" unable to silently leak a
world fact — the same move D76 made for producers with `closeBlock`. I did **not** implement
it: `restoreKeep` is also called by `onCopy` and `nfSealed`, where the kept set differs
(a private copy keeps more than a sibling arm), so unifying them needs care and a verdict-stable
refactor, which is more than a probe. Flagged for a dedicated lane.

## 6. Candidate simplification (not implemented)

`neutrals` (generalisation records, per world) and `etaRefs` (η-refinements, global) are two
record lists with the same shape `Value ↦ σ` but opposite scoping. The model explains the
difference (world-dependent vs world-independent), but a reader of the checker must know which
is which. Document them side by side with the (X) argument, or, if a measure ever shows it
pays, tag each record with the world depth at which it was made and let one restore routine
drop the too-deep ones. Describing only; removing or merging rules needs the user.

## 7. Open questions

- **Stability.** Everything here assumes the stability conjecture: that refinement commutes
  with conversion and with the telescope/sealed-program re-normalisation. (S)'s "substitute
  everywhere, then re-normalise" is exactly the operation whose commutation with the direct
  run is unproved (paper Conjecture 2). The model makes the obligation precise; it does not
  discharge it.
- **`split f in t`.** Not probed here; it is [Split-gen] with the scrutinee found in the goal
  rather than written. Its generalisation uses the same `neutrals` path, so (G) covers it, but
  a dedicated probe over goals whose stuck chain has several links is worthwhile.
- **Fuzzing.** The by-hand probes are weak evidence for (X). A generator aimed at
  scrutinee-dependent opaque calls generalised in sibling arms is the real test, and is the
  cheap falsifier docs/14 keeps testing for.
