# 23. Which route to consistency: a joint verdict

Agreed on 2026-11-06 by two Claude sessions at the user's request: `ochr-consistency-2`, which proposed the route after reading `docs/17`, `18` and `19` and the Aeneas paper, and the session that wrote `docs/18`. It compares that route with `docs/18`'s plan. It is a recommendation; nothing is dispatched from it until the user has reviewed it.

## Route

Prove consistency by **meaning preservation in the set model**, not by `docs/18`'s two-run walk (a generic run compared with a run at each instance). Give each symbolic state a meaning ⟦Ω⟧_ρ for every assignment ρ of set-theoretic values to its unknowns (ρ(σ) ∈ ⟦Δ(σ)⟧), and prove that each checker step keeps that meaning, or loses only information (⊑). An accepted definition then means an element of its type, and `False` means ∅.

## Why

1. **The model's Π is what gets checked.** Unknowns range over all set-theoretic values, non-computable functions included. A stuck call ⌈σ(…)⌉ means ρ(σ)(…), so the generic call never needs ρ(σ) to be computable. The referees' main gap (truth in the set model against a walk over machine closures, `docs/17`) closes by construction, and no bridge to machine values is needed.
2. **There is no second run.** There is no agreement relation, no renaming of fresh names, and no "equal only up to resolution". `Pick`'s problem (`docs/18`, (A2)) becomes local: a read fixes a live hole at the borrow's current content.
3. **Checks that only reject come free.** Conversion, [Rec], the whole-borrow checks and [Repack] need only their accepting direction. Comparing sealed programs by text is sound (same text, same meaning).
4. **No progress, termination of runs, or adequacy** is needed for consistency.
5. **The referees' cycle becomes ordinary induction.** Meaning preservation (a) and membership (b) are proved together, by induction on the run inside induction on definitions: earlier definitions by the induction hypothesis, recursive calls by well-founded induction on the [Rec] argument. (a) consults (b) at the steps that replace a value by a canonical one, `⋆` for a proof and `()` for η, since those keep meaning only for a value whose meaning lies in its type's. Every appeal is to an earlier step or to the outer hypothesis.

## Agreed costs

- **The set model.** It is stratified by universe as in Carneiro's model of Lean; Ochr's syntactic, non-cumulative sorts (D55) help. Each type is a set with its relation R, and `&` is read as forward and injective backward functions. This is shared with `docs/18` and is the main risk. `docs/18`'s Q9 (a well-founded definition of the model) is unchanged.
- **⟦Ω⟧ for symbolic states.**
  - Sealed fills with holes mean functions of the live holes, and inert loans are hole parameters.
  - Open dependent values are raw field tuples, and [Repack] restores membership.
  - Meanings are partial (an error value) for bodies that go wrong; no derivation reaches them.
  - Closures mean functions on their annotated domains.
  - ⊥ is a choice that test (2) settles. Either it means the old value (a deliberately non-affine model, in which ⊥ needs no ⊑), or it means "no information" (and ⊑ covers it).
- **A well-formedness invariant**, preserved by every step: preservation only, no progress.
  - No aliasing live borrows.
  - Loans only where closing off allows (A.5 condition 5, the paper's unproved Assumption 11).
  - Every closure and global in the state has passed [Rec], since a `fix` means a function only through well-founded recursion.
- **A smaller (Mono).** An information order ⊑ for steps that over-approximate: block captures and early ends, and ⊥ if it means "no information". Every step that computes on a state (`Eq`, `J`, match, [Close]'s rows) must be ⊑-monotone. `Eq` staying stuck over ⊥ is the existing instance.
- **The two-paths census re-run under a new criterion.** A decision is harmless when all its outcomes mean the same, or are ⊑-related; it no longer has to be identical on both paths. The known non-free decision is a binding's class (a private copy discards writes), which D77 already makes syntactic. η, copy vs move, and erasure are free given membership.
- **One one-sided step lemma per checker step, against the real checker.** Large but routine.
- **Not covered:** runtime safety at instances (`docs/18`'s clause (i)). It needs a separate argument if wanted.

## Tests, all on paper

0. **Model existence on a slice.** `Nat`; a type function defined by recursion (`Cells(E, n)`); a type variable `A : Type₀` with R at it; a function type returning a borrow, with injective backward functions; Π into `Prop` over `Type₀`. Check that the stratified definition is well-founded. If it fails, both routes fail.
1. **Historical bugs.** The step lemma fails at the buggy step behind each of `docs/18` §9's closed proofs of `False` (EtaBoom included) and MovedBothSides, and holds after each fix.
2. **A higher-order slice.** Function parameters ranging over all set functions, a closure built in the run and called later, [Conv-fun] (functions compared by their generic observation) and a function taking a function that returns a borrow. Do `Pick`, A3 after Drop and N3 through inert loans disappear, or move into ⟦Ω⟧? This also settles what ⊥ means. The user's caveat (2026-11-06): fragment F is first-order, so redoing its proof is at most a warm-up, and its results say little about the whole calculus.

Tests 0 and 1 are independent and can run in parallel; test 2 comes after.

Reviewed by the user on 2026-11-06, who asked for `docs/18` to be updated to this route and for the tests to be run.

## Still open

Nothing between the two sessions.

## Implication for current work

(P) is not on this route's path.
- **D80 and the η question** no longer matter for consistency. They matter for `docs/18`'s route, now secondary, and for programmer experience.
- **D82** (every binding carries its declared type, branch `typed-bodies`) is not needed for this route, but may make the membership invariant easier to state against the checker.
