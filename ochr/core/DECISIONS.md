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

## D27. Proof parameters are ⋆ at the generic call (deriver-e5 Q1); small clarifications
E5 (a precondition proof about the current, mutated `*x` passed to `SubM`) derives under v1.3 with no new rule: in-place `AddM` and pure `Add` close off into the same sealed program, so a proof about `Add` of a snapshot is accepted where a proof about `*x` is required. One incompleteness: [Def] bound a proof parameter to an abstract σ_h while every other proof value is ⋆, so sealed programs embedding different proofs failed to compare. Fix: proof parameters are ⋆. Also: parameter types evaluated left to right and stored where [Split] refines them (Q4); a sealed program of sort Prop is a type (Q3); reading `p.1` needs a known `S` head (breaker-close A3/G2, deriver-e346-v1 N9). `False` is not needed: `Eq Nat Z (S Z)` is closed, irreducible and empty (Q2).

## Round 3 → v1.5 (reports: breaker-fresh, reviewer-1, lean-checker v1.4 139/139)

## D28. Erasure is decided per definition and per syntactic position, never from a normal form; universes are not cumulative
breaker-fresh F1: with `U(n) : Type_0 := match n {Z => Prop | S _ => Prop}` and `W(x : &Nat, n) : U(n) := *x := S Z; V(n)`, the call `W(&c, n)` ran for real at the generic `n` (its type `⌈U(σ)⌉` is not recognisably a sort) but was erased at `n = Z` (its type is `Prop`), so `Lie(n) : Id Nat (let c = Z; W(&c, n); c) (S Z) := refl` gave `Lie(Z) : Eq Nat Z (S Z)`. This is exactly the fire triangle's "desynchronisation between effects performed in the term and in the type". Fix: a call is erased iff the callee's declared codomain, at its generic call, is a sort or has sort Prop (decided once at [Def]); other terms by syntactic position or declared sort. Non-cumulativity is load-bearing (with `Prop ≤ Type_0` a Type-valued family could return a proposition).

## D29. Matching ends loans anywhere inside a neutral head; normalisation errors are type errors
breaker-fresh F2: a hole inside a sealed program at the head of a matched place was not ended, [Split] generalised the sealed program away with the only occurrence of the hole, and an accepted program wrote through an ended borrow at runtime. The paper already said "inside its content"; RULES had narrowed it.

## D30. A function value's normal form is the observation of its generic call
breaker-fresh F3: comparing closures by result only made `λx.(*x := S Z)` and `λx.()` convertible, and transport gave `Eq Nat (S Z) Z`. One notion of "what a computation is" for [Def], `Id` and conversion.

## D31. Without `by`, `f` is not in scope in its body; `f` is never in scope in its own signature
breaker-fresh F4.

## D32. Pattern variables are resolved to sub-places before captures and footprints
breaker-fresh F5: `p := Z` in a stuck block was not seen as a write to the scrutinee, so the block captured `*x` by copy and `Clear(&c) : Eq Nat (S Z) (S (S Z))`.

## D33. Type-level matches are type-checked like any other term
reviewer-1: whether the arms of a stuck match inside a type were checked was unspecified (v1.3 exempted them); unchecked arms can fail after refinement and break naturality. Types are terms; typing a type splits and checks its arms. A match's result type must agree across arms after refinement, or be annotated.

Common root of D28 and D32 (breaker-fresh): a statement is evaluated along two paths — through closing off at the generic call, and directly at each instance — and [Call-type] equates them. Any lossy or reclassifying step on the closing-off path is an inconsistency. The metatheory's "refinement commutes with closing off" must cover instantiation, stuck blocks, captures and the erasure decision.

## D34. Generalising a sealed program is a persistent refinement of that neutral (lean-checker G1); general inductive types
With trees, a proof splits on a comparison `b = Lt(k, v)` that is a sealed program on abstract values. v1.5 generalised only the occurrences present at split time; when the goal's sealed programs re-ran, they re-derived `⌈Lt(σk, σv)⌉` inside `InsertM`'s body, stayed stuck, and never met the induction hypothesis (InsertMEq rejected). Fix: record `⌈n⌉ := σ` as a refinement, applied to later derivations too. Sound because a sealed program is a closed deterministic computation (this is Lean's `split` with the equation `h : Lt k v = b` rewritten everywhere). It makes refinements uniformly "knowledge about neutrals". General inductive types (lists, binary trees) needed no other rule change: InsertMEq (in-place BST insert = pure insert) is bare recursion, the environment carrying both untouched fields.

## D35. Erasure is purely syntactic (formal-appendix BoomL, BoomB)
Writing the formal appendix exposed two more "two paths" inconsistencies, both accepted by the v1.5 checker and admitted by RULES read literally. BoomL: a *local* function's erasure class was computed from its codomain evaluated with captured values, so `h : Π(x:&Nat). U(n)` ran at the generic `n` (where `U(σ)` is stuck) but was erased at `n = Z` (where `U(Z) = Prop`), giving `Eq Nat Z (S Z)`. BoomB: a stuck block is a call whose codomain is the match's type, so a type-valued match was erased when closed off but not when run directly, giving `Eq Nat (S Z) Z`. Fix: erasure is read from syntax and declared sorts only — a function's class from its codomain *term* (a sort → returns types; declared sort Prop → returns proofs), for local and top-level functions alike; a stuck block is erased exactly when its match would be. [Close]'s row is also read from the declared codomain. After D28 and D35, every decision the two evaluation paths must agree on is syntactic, which is what the metatheory's stability lemma needs.

## D36. Inductive declarations are strictly positive (first-order fields)
formal-appendix: v1.6 checked only that field types were borrow-free, so `inductive Bad := Mk(f : Π(x : Bad). Empty)` was accepted, and with `L(b) := match b {Mk(f) => f(b)}` a proof `K(bad) : Eq Nat Z (S Z)` was typed by [Call-type] alone while the diverging `L(bad)` never ran (proofs are not run). Fix: fields are first-order data only. This is the standard positivity condition in its simplest form; lists, trees and Bool satisfy it.

## Round 5 → v1.8 (breaker-fresh-v16: X1–X5 against the v1.6 checker; X1/X2 = formal-appendix BoomL/BoomB, already fixed in v1.7's rules)

## D37. Generalisation records are global; fresh names are never reused (X3)
A generalisation made while forming a type on a private copy (D33 × D34) left its σ_g in the formed type but discarded the record with the copy, and the checker's restore also rewound the fresh-name counter, so a later split reissued the same σ_g for a different sealed program: a closed false proof. Records name closed computations, so they are global; abstract values are never reused.

## D38. Observing a borrow-typed result writes a fresh abstract value through it (X4)
D30 compares functions by their generic-call observation; for a function returning `&T`, the observation ended the returned borrow with its current content, so `PickX(x, y) := x` and `PickY(x, y) := y` observed identically when nothing was written, became convertible, and transport proved `Eq Nat 0 1 ∧ Eq Nat 1 0`. Fix: observe a borrow result `borrow_k u` as `u` together with the owners' contents after writing a fresh abstract value through it, which reveals where it points. This is the model's reading of `&T` results (a current value and a backward function of the final value).

## D39. [Seal]'s head guard covers neutral-headed calls (X5)
RULES said both "a neutral-headed call closes off at once" and "[Seal]'s head call is not eligible for [Close]"; the checker applied the former at the head, re-creating D9's loop for a neutral head with an `&T` codomain (stack overflow). The guard wins: a sealed program whose head is a neutral-headed call stays as it is.

## D40. A stuck block is erased exactly when each of its arms is (lean-checker P2)
v1.7 said a block is erased when its match would be; a match's type inferred from its arms is *computed*, so a block whose arms call a data-class function returning `V(Z)` (declared type `U(Z)`, computing to `⊤ : Prop`) was erased at the generic call but its match ran directly at the instance (`BoomG : Eq Nat (S Z) Z`). Erasing a block only when every arm is itself erased keeps the decision syntactic; a non-erased block is always safe because its sealed programs re-run the arms, which make their own decisions. An annotation of declared sort Prop erases the whole annotated term on both paths.

## D41. Fail-safe for erasure: erased terms may not affect places outside themselves (checked)
Six of the last eleven soundness bugs (breaker-fresh F1, X1, X2; formal-appendix BoomL, BoomB; lean-checker P1, P2) were disagreements between the generic path and an instance path about *whether a term is erased*, each fixed by making the classification more syntactic (D28, D35, D40). The classification is now syntactic, but the area has been fragile, so we add defence in depth: v1.2's static restriction (D20), reinstated alongside the private copy (D26). An erased term may not write, borrow or move a place that outlives it except by passing it to an erased call; the machine checks this on every path. Then a term that writes outside itself is never erased on any path that accepts it, so a misclassification on one path becomes a type error there instead of a desynchronisation. Proofs keep their local mutation (on the private copy) and may hand outer places to other proofs (as AddMZero's recursive call does). This is a restriction on erased terms only, not on programs.

## D42. "A proof" means declared, read from syntax (lean-checker P3 and the declared/computed disagreement)
The checker's P1 fix classified a variable as a proof by whether its value was ⋆, which is computed: `LieH(g : Π(y:Nat). V(Z))` erased `(c := S Z; h)` at an instance where `g(0)` evaluates to ⋆ but kept the write at the generic call where it is a sealed program (`BoomH`). Fixed by per-binding proof flags read from syntax. The appendix had meanwhile read "whose type has sort Prop" with the *computed* type; each reading is consistent alone, mixing them is BoomG. Decision: the declared reading everywhere — a `let`/`;`/`match` is a proof when its tail is, a call when its callee's codomain term has declared sort Prop, a variable when its declaration says so, a stuck block when every arm is. The machine then needs no types, only one flag per binding.

## D41 measured (lean-checker v1.9 round, notes/lean-checker.md §12)
With D41 on and one classification rule switched off at a time: D41 is a fail-safe for misclassified *inline* terms (let/seq/match/leaves: the leafRule switches flip nothing any more) and for dropping the private copy (P2's row then only guards completeness: TwoPhase, LemmaMoves, TypeErased). It is NOT a fail-safe for misclassified *calls or stuck blocks*: the discarded write happens inside a callee body through a borrow passed as an argument (D41's erased-call exception), and bodies are checked in tail position, not as erased occurrences. The extension `confineBodies` (proof- and type-valued functions may not write through their borrow parameters; every arm of an erased block confined) closes all block attacks and BoomL, not X1 with value-based classification, and costs proofs that run programs on outer places (TwiceMZero') and type-valued functions that write through borrows. Nested erased terms are judged by the outermost erased occurrence containing a step. Pending the user's decision on replacing the private copy by confinement (with confineBodies).

## D44. A function type returning a borrow must take a borrow (reviewer-2)
reviewer-2: with `M(n) := match n { Z => Unit | S _ => Empty }`, `P(x : &Nat, e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())` and `Q(g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)`: closing off `g(5)` returns a borrow whose hole is placed in no owner (no borrow arguments), so owners(k) = ∅, the footprint is empty, `e`'s type computes to ⊤, and Ochr proves `¬(Π(n : Nat). &Nat)`; an opaque `leak : Π(n : Nat). &Nat` (which safe Rust inhabits via `Box::leak`, a `'static` borrow) then gives a closed proof of `Empty`. lean-meta had already made "[Close] with a borrow result and no borrow argument" an error in the mechanisation (its model's injective subset is empty). Fix: such Π-types are ill-formed. Ochr has no `'static` borrows; a returned borrow always derives from a borrow argument, which is Rust's lifetime-elision rule for functions without explicit lifetimes.

## v2.0 (user, 2026-09-29): uniform inductive definitions over a small rule count
The user: "making the kernel/typing rules simple is not the same as making them small; if we have one consistent way of defining an arbitrary inductive definition and ⊥ is one of those, that's a nice consistent view instead of encoding things between other things." Until now `⊥` was encoded as `Eq Nat Z (S Z)` (a leftover of D16's minimality), `⊤`/`∧`/`⟨h, k⟩` were primitives, and user inductives were `Type₀`-only and monomorphic. Every mainstream calculus with inductives has `⊥` as the empty inductive (Lean `inductive False : Prop`, Coq `Inductive False : Prop := .`, Agda `data ⊥`); encodings (`Π(P : Prop). P`) belong to calculi without inductives (the pure Calculus of Constructions).

## D45. Prop inductives, zero constructors, matching on proofs by type, subsingleton elimination
Inductive declarations may be in `Prop` and have zero constructors; `False`, `True` and `And` become library declarations and `⊤`, `∧`, `⟨h, k⟩`, `refl` notation. A match on a proof cannot inspect it (its value is `⋆`, or `σ`, and D27 binds proof parameters to `⋆`), so it is driven by the scrutinee's declared type: zero arms for `False`, one arm with `⋆` fields for `True`/`And`. Large elimination from a Prop inductive is restricted to subsingletons (Lean's rule) — required for consistency with proof irrelevance once Prop inductives are general. Stability under the two evaluation paths: refinement never changes a declared type, so the by-type decision is the same on both paths; a zero-arm match is erased vacuously (D40) and has no effects (D41).

## D46. Uniform parameters on inductive declarations
Needed for `And (P : Prop) (Q : Prop)`; also gives polymorphic data (`List (A : Type₀)`). No indices, so `Eq` stays primitive. Positivity (D36) allows a parameter as a field type.

## D47. Distinct constructors are disjoint in `Eq`
`Eq D (C ā) (C' b̄) ≡ False` for `C ≠ C'`, completing the observational rules now that `False` is native (restores half of what D16 dropped). Sound in the model (both sides denote ∅; a propext instance). Injectivity is deliberately not added: the paper's point that the borrow structure performs the frame/congruence step for in-place proofs stands, and adding injectivity is a separate, optional extension.

## D48. Borrows only of data, only at the top of declared types; Π-types compared under binders (reviewer-3)
A cold review of d7e0be31 (notes/reviewer-3.md, score reject) found: (1) `&T : Type₀` for every `T`, including universes, so `Π(x : &Type)(a : *x). *x : Type` made Type₀ impredicative; with impredicative `Prop : Type₀` the typing rules then contain System U⁻ (Hurkens' paradox), and the set model's clause "types of sort s denote elements of s's universe" fails (Reynolds). The reviewer's Hurkens transcription was stopped only by a conversion incompleteness, which is no defence. Fix: `&A` only for data types `A`. (2) "`&` only at the top of a declared type" was not enforced: a codomain computing to `&Nat` let an accepted `G` read ⊥ at `n = 0`. Fix: `&` only syntactically at the top of a declared type. (3) Π-types were compared by captured values and unevaluated code, rejecting closures that capture variables, type abbreviations under binders, and lemmas whose statements differ only in unevaluated code. Fix: compare Π-types (and types under binders) by instantiating binders with fresh abstract values and comparing normal forms, as D30 does for function values. Also noted: Ochr's injectivity of backward functions for `&T`-returning functions holds because Ochr has no `'static` borrows (every returned borrow derives from a borrow argument); Rust's `Box::leak` shows this is a genuine restriction relative to Rust, to be stated as scope, and opaque/FFI borrow-returning functions are injectivity assumptions.
