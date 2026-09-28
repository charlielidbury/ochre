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

## Round 1 → v1 (reports in notes/: deriver-e1, deriver-e2, deriver-e346, breaker-frame, simplifier, meta-model)

## D9. [Seal] never closes off its own head call
v0's [Seal] re-ran the sealed call, which got stuck again and re-closed into itself (loop), or, if [Close] was disabled inside [Seal], never produced the `S` the successor arms need. Fix: the head call of a sealed program unfolds once and is not eligible for [Close]; calls inside its body are. This is exactly CIC's fixpoint guard (a fixpoint unfolds only when it can make progress). Found independently by deriver-e1 (F1), deriver-e2 (F1), deriver-e346 (F9).

## D10. Saturated n-ary calls; λ is a non-recursive `fix`
Curried application let `AddM(x)` build a closure capturing a borrow, which the scope forbids. (deriver-e1 F2, simplifier 8.)

## D11. Loans are variables bound by their borrow; ending substitutes, with no side condition
Supersedes v0's anonymous pending bindings and Aeneas's End-Mut side condition. A hole for a returned borrow is the same thing as a loan, may occur several times inside sealed programs, and is filled by substitution. Inside a [Seal] run, a loan whose borrow lives outside is inert. (deriver-e2 F2–F4, simplifier 3, meta-model C5.) Cost: accepts some programs Rust rejects once data has several fields; this is more permissive, not unsound.

## D12. No ghost owners: a definition is checked at its generic call site
Checking `f` = running `f(&c₁,…)` from `{cᵢ ↦ σᵢ}`. The goal is the [Call-type] of that call, the same rule that types an induction hypothesis. One rule instead of [Lam]'s snapshot plus [App]'s call-site evaluation plus ghosts. (simplifier 2.)

## D13. Π-types are closures over formation-time values; [Call-type] rebinds only the parameters
v0 re-read a Π-type's free variables at the call site: `Oops2 x h := x := S x; h()` with `h : Π(_:Unit). Id Nat x Z` proves ⊥. (deriver-e346 F5, meta-model C4.) This is D2 applied to Π-types, not a new principle.

## D14. Proofs are not run (P5) **[new principle]**
A call whose result type is a proposition is erased at runtime; the machine must therefore not run it either (borrow arguments come back unchanged). Without this: checker/runtime disagreement (deriver-e1 N2), lemma calls overwrite the borrowed place with an opaque sealed program (deriver-e1 N1, deriver-e2 F8, deriver-e346 F8), and proof irrelevance at a Π over a borrow parameter identifies `λx.⋆` with `λx.(*x := 7; ⋆)`, giving a closed proof of ⊥ (meta-model C1).

## D15. Stuck non-tail matches are closed off like calls; [Join] deleted **[overturns user's D7: imprecise join]**
deriver-e346 showed [Join] is a strictly weaker copy of [Close]: moving AddToOne's match into a helper function made it accepted, with exactly the right backward function in the loans. Closing off the stuck match instead (the arms are still checked by [Split]; the continuation runs once from the closed-off state) removes anti-unification and all of [Join]'s underspecification (F1–F4), and is precise. It keeps what the user wanted from the imprecise join: the continuation is checked once, so errors land on a line without "in the case where…" qualifiers. meta-model T5: [Join] is not natural (does not commute with refinement), closing off is. Consequence: branch-dependent live borrows (E3's AddToOne) are now accepted, so D8's exclusion of them is lifted.

## D16. `Eq` computation trimmed to pairs, reflexivity, and ⊤ units
Kept: `Eq (A×B)` splits, `Eq A a b ≡ ⊤` when `a ≡ b`, ⊤ is a unit for ∧; `refl : ⊤`. Dropped: Nat constructor injectivity and the ⊥ rule (only served the pure `AddZero`, which now uses `cong S`; the borrow examples are bare recursion without them: simplifier 1). Kept rather than deleting D6 wholesale because (a) Prop is needed anyway for D14, (b) the reflexivity rule removes `refl` padding for untouched owners in multi-borrow footprints (deriver-e346 F12), and (c) it makes `Id Unit (AddM x 0) ()` compute to the single interesting equation. The model needs `propext` (meta-model).

## D17. Recursion is structural on entry values
The recursive argument's content must be a σ' obtained by refining the parameter's entry σ. The v0 syntactic check accepted `*x := S *x; match *x {S p => f(&p)}` and so a proof of `Π(n:Nat). ⊥` (deriver-e346 F6, meta-model C3).

## D18. Owners are sets; the footprint observes all owners of a hole
A returned borrow from a two-borrow call leaves its hole in both owners; observing one lets [Call-type] prove `Id Nat (S Z) Z` (meta-model C2).

## D19. [Access] ends loans on the path and inside the content; the two sides of `Id` run on independent copies
Makes the exclusivity invariant that [Call-type]'s frame soundness rests on explicit, and closes a dangling-borrow adequacy bug (breaker-frame 1, 2, 10; meta-model C5).

## Round 2 → v1.2 (reports: deriver-e1-v1, deriver-e2-v1, breaker-close-v1; E1 and E2 derive under v1, all round-1 ⊥ attacks blocked)

## D20. P5 becomes a theorem: proofs have no effect outside themselves
breaker-close-v1 N1: v1's P5 was a stipulation about *calls*, and closing off a stuck block turns a non-call into a call, so a proposition-typed block that writes gave different answers sealed-and-refined vs run directly: a closed proof of `Id Nat (S Z) Z`. Fix: a term whose type is a proposition may not write, borrow or move a place that outlives it except by passing it to a call whose result type is a proposition. Skipping proofs is then a consequence (running and skipping agree), inlining vs outlining a proof cannot matter, and runtime erasure is justified. Runtime erasure keeps a proof call's argument evaluation (deriver-e1-v1 G2). This is a restriction on proofs, which are erased, not on programs: it introduces no pure/impure divide for the programmer.

## D21. [Call-type] is evaluated after the arguments, in a frame pushed on the caller's environment; arguments live in temporaries
deriver-e1-v1 G1: read literally, v1 evaluated the codomain before the argument's loan existed, making every effect goal `⊤` (end goal 3 emptied). deriver-e2-v1 H5: the IH's owner chain needs the caller's frames visible. breaker-close-v1 N7/G5: arguments in flight (`f(&x, &x)`) must be visible to [Access], so each is evaluated into a temporary.

## D22. Stuck blocks capture like Rust closures; generalise-then-split on sealed scrutinees
breaker-close-v1 N2–N5: a closed-off block moves a place it moves in any arm, passes by `&` a place it writes or borrows, copies a place it only reads; its codomain is the match's type. deriver-e2-v1 H7 / F10, breaker-close-v1 G4: [Split] on a sealed-program head first replaces every occurrence of it by a fresh σ (Lean's `generalize`), then splits.

## D23. `J` takes explicit endpoints; recursion declares its decreasing parameter
deriver-e1-v1 G3 (`Eq A a a ≡ ⊤` erases endpoints), G6 / deriver-e2-v1 H4 (several shrinking arguments).

## D24. All types are formed on a private copy of the environment
breaker-close-v1 N8: v1 said only `Id`'s sides ran on copies; a type formed elsewhere could run effectfully in the real environment. P2 now says every type is evaluated on a private copy.

## D25. The pure theorem is proved by the in-place lemma
deriver-e1-v1 G4: `AddZero := match x { Z => refl | S p => AddMZero(&p) }` checks with no `cong` and no Nat rule, because borrowing the predecessor field of the owned `x` makes the environment do the congruence even for the pure statement. §7 now uses it; `cong` is not in the core.

## Round 2 (cont.) → v1.3 (reports: deriver-e346-v1, breaker-frame-v1, meta-model-v1; no unsoundness against v1.2's text found; breaker-frame-v1: "v1 is the first version I could not break")

## D26. One principle for erased terms: they run on a private copy
Supersedes D20's static [Proof] check. meta-model-v1 (R1, §1.5) proposes the simpler fix for the Prop-typed stuck-block bug: whatever the runtime erases (types and proofs) the machine runs on a private copy of the environment, argument evaluation included. Then running and skipping a proof agree by construction, naturality holds (a Prop-typed block has no effect whether its scrutinee is abstract or refined), proofs may use local mutation freely, and deriver-e1-v1 G2 (runtime erasure of proof-call arguments) disappears because the checker also discards them. P2 and P5 become one principle. Also: a call with a neutral head closes off at once (meta-model-v1, deriver-e346-v1 N7); [Rec] applies inside nested functions (deriver-e346-v1 N1 residual); Π-types capture no borrows (breaker-frame-v1); stuck-block captures on maximal prefixes, any-arm, only for checked arms (deriver-e346-v1 N2–N6, meta-model-v1 R4).
