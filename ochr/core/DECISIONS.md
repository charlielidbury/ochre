# Decision log

Newest last. Each entry: the decision, the alternatives, why, and what would make us revisit it. Entries marked **[overturns user]** reverse something the user had tentatively chosen in discussion; the user authorised overturning technical decisions but not the end goals in BRIEF.md.

## D1. Definitional equality is normalisation by a deterministic symbolic machine
Alternatives: rewriting with confluence (fails: effects make rewriting-anywhere non-confluent). Revisit if: never, this is structural.

## D2. Types read values; a formed type is a closed statement (snapshot)
Alternatives: types re-evaluated at every use (unsound: `let h : Id Nat x Z := refl; x := S Z; h` would change meaning). Revisit if: the snapshot makes some needed proof impossible.

## D3. Borrow-free data is copied on read; borrows are moved; reborrowing is explicit **[overturns user: "everything moves for now"]**
Why: with moves, a type like `Id Nat x 3` consumes `x` on one side only, so the two observations differ in whether `x` is dead, and `x + x = 2 * x` cannot be stated at all. Copy semantics for data removes both problems and needs no runtime/type-level mode split. Moves are recovered as an optimisation: an affine usage check (outside the core) licenses implementing a last-use copy as a move, so `AddM` still allocates nothing. `Id Nat (Add x x) x` is therefore well-formed (and false), which the user had wanted rejected; that preference was tentative and conflicts with stating `x + x = 2x`. Revisit if: the affine layer turns out not to be separable.

## D4. Close off at the innermost stuck call, into sealed source programs
Alternatives: freeze the stuck match (loses the frame; 01 §4); fresh abstract values shared between the two sides of an equation (un-Lean-like: a neutral that does not name itself); prophecy variables (mint abstracts at borrow creation, breaking "concrete in, concrete out"). Sealed programs are the backward functions written in source syntax, so the programmer never sees a second language. Returned borrows are handled by a sealed program with a loan hole. Revisit if: the loan-hole form breaks down for borrows stored in data.

## D5. `Id` is derived: it computes to `Eq` on observations over a syntactic footprint
Alternatives: primitive `Id` with its own intro/elim (more rules); observing all of Ω (shape depends on unrelated locals, so the IH and the goal stop matching once a `let` intervenes); observing only the result (loses effects, violates end goal 3); a semantic footprint (not stable under refinement). Revisit if: the footprint misses writes (e.g. through a function returning a borrow).

## D6. `Eq` computes observationally on pairs, Unit, Nat constructors
Why: makes `Id`'s product collapse to the single interesting equation, and makes `AddZero`'s proof bare recursion (no `cong S`). All rules identify props with equal truth values, so the proof-irrelevant set model validates them. Revisit if: the simplifier shows `cong` is cheaper than the extra conversion rules.

## D7. Imprecise join; rejection when loan shapes differ **[user's choice]**
The programmer duplicates the continuation when precision is needed; errors land on the arm that caused them.

## D8. Scope: no borrows inside data, no shared borrows, no loops, closures capture only borrow-free values
Why: keep the first core small. These are the known frontiers (see the three motivating examples in 00-idea follow-ups: returned borrows are IN scope, borrows in data and branch-dependent live borrows are OUT).
