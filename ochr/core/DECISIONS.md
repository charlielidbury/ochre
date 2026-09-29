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

## D49. Clarifications of D45 (prop-paper's v2.0 pass)
(1) A proof scrutinee's type is its stored type as refined by [Split]; it must normalise to an inductive head, and a still-neutral type is a type error. This consults a normal form, but only fail-safe: a less refined path sees a neutral and rejects, it never sees a different head. (2) A match on a several-constructor Prop inductive is erased and each arm must be a declared proof (D42's reading of subsingleton elimination). (3) Data fields of a proof are bound to fresh abstract values, as [Def] binds parameters (uniform; enables ∃-style witnesses without new machinery). (4) Constructors take their inductive's parameters as leading arguments in the core; surface syntax may omit inferable ones; values record them. (5) A zero-arm match is unreachable, erased, and yields ⋆ at any type. (6) The unit laws keep `True`/`And` kernel-known; stated as the one non-uniform point. (7) A proof's value is always ⋆ (D27), never an abstract value.

## D50. The unit laws are conversion, not normalisation (prop-checker F2)
Implemented as normalisation, `And(True, P) ≡ P` rewrote a stored type `True ∧ P` to `P`, so `match h { Intro(a, b) => … }` on `h : True ∧ P` could not be typed. As conversion rules (two types are equal if they agree after applying the unit laws), stored types keep their inductive head and `Id`'s observations still compute to the single interesting equation for comparison. Also recorded from the same report: in this machine, D42 (every proof is ⋆) alone already prevents a match from distinguishing `Inl` from `Inr`, so the `Or` attack's closed proof of False needs both D42 and D45 switched off; D45 remains necessary for the model (a large elimination from `Or` has no set-theoretic meaning), for canonicity (a closed Bool stuck on a proof), and for totality of several-constructor matches.

## D51. Captured values keep their declared types (reviewer-2; implemented by the previous checker agent, verified by prop-checker)
A closure or Π-type that read a captured proof or a captured sealed program could not be typed (no type for ⋆ or a sealed program in isolation), a "severe hidden restriction" per reviewer-2 (e.g. `let n = *x` after `AddM(&*x, 1)`, then `λ(y : Nat) : Nat => n`). Capture now records each captured value's declared type; whether a captured variable is a proof is read from its declaration, never its value (D42/P3).

## D52. Pairs are an ordinary inductive; `Eq` is injective on constructors (user, 2026-09-29)
The user, on the finding that a pair parameter could not be taken apart (`SwapPair`, notes/lean-checker.md §17): "it seems like pairs should be a regular inductive instead of a weird primitive". `Pair (A : Type₀) (B : Type₀) : Type₀ := Mk(fst : A, snd : B)` joins `Nat`, `Unit`, `False`, `True`, `And` as a library declaration; `A × B`, `(a, b)`, `t.1`, `t.2` are notation, and a pair is taken apart by `match p { Mk(a, b) => … }`, which [Split] refines like any inductive (no η rule).
v2.0's `Eq (A × B) (a, b) (a', b') ≡ And(…)` was a special rule for the primitive pair, and `Id` relied on it to compute to "the one interesting equation". Keeping it for one inductive would reintroduce the primitive by another name, so it is replaced by the uniform rule: `Eq` on two values built by the same constructor is the conjunction of the equations between their fields (injectivity), alongside D47's disjointness for different constructors. `Eq` then computes on constructor values by structure, as in observational type theory. Sound in the proof-irrelevant set model (constructors are injective; a propext instance, as for D47). `Id` is restated without pairs: it computes directly to a conjunction of equations over the result and the observed owners. An observation is a tuple of the machine, not a `Pair` value, so `Id` still applies at any borrow-free type, propositions and universes included, which a `Pair (A : Type₀) …` could not hold (universes are not cumulative).
Consequence, accepted: D47 and the paper said injectivity was left out deliberately, and the paper used its absence as a contrast ("a pure proof recursing on a copy needs a congruence step; the in-place proof does not"). With injectivity the pure `AddZero` needs no `cong` either. The user's thesis is about total program size (one program instead of spec + implementation + refinement proof), not about in-place proofs being simpler, so the contrast is a side observation and the uniform rule wins. Expected ledger effect: programs rejected only for want of injectivity (e.g. `Logic.Inj`) become accepted, as completeness.

## D53. Runtime reads move; erased reads and copy types copy; `clone` is built in (user, 2026-09-29) [spec accepted; not yet in RULES or the checker]
Overturns D3, restoring the user's original "everything moves". D3's reason (a type like `Id Nat (Add(x, x)) x` reads `x` twice) no longer needs copying at runtime: since D24/D26 every erased term runs on a private copy, so erased reads may copy freely, quantitative-type-theory style, while runtime reads follow Rust. The paper's §9 gap ("the checked machine copies where the compiled program moves; their agreement is an assumption") closes: the machine's moves are the compiled program's moves, and every deep copy is written `clone`.
- [Read] of a borrow-free content: in an erased position (P2), copy; at runtime, copy if its declared type is a copy type, else move (the place becomes ⊥). Borrows always move, as before.
- Copy types, read from declarations (never from values): an inductive in `Type₀` whose fields do not mention the type being declared and whose field types are all copy types (a parameter used as a field is a copy type at an instance `D(ā)` when its argument is). `Unit`, field-less enumerations, and pairs of copy types are copy types. `Nat` is recursive, so it is not (user: "if nat is made copy then AddM etc. must not use it because the whole point of those functions is they're doing moves"); a fixed-width integer primitive, if added, would be. A closure is a copy type when all its captured values' declared types are.
- Moving out through a borrow is allowed (the machine checks by running, not by Rust's static rule) provided the borrowed content is whole again when the borrow ends: ending a borrow whose content contains ⊥ is an error. `SubM`'s `*x := p` (moving the predecessor field out of `*x`, then overwriting `*x`) stays accepted.
- `clone(p)` is a built-in term: [Access] as for a read, then copy `content(p)` and leave `p` unchanged. Copying an abstract value gives the same abstract value, so every clone of `x ↦ σ` is `σ` (definitionally equal), which a user-defined recursive clone could not give (it would close off to a sealed program and leave a backward function in `x`).
- Captures are reads: a runtime closure moves the non-copy variables it captures; a Π-type, being a type, copies.
Copy/move is decided from syntax and declared types, so the generic call and every instance agree (the D28/D35 discipline).

## D54. The erasure class and [Close] row are part of the Π-type (reviewer-5)
A cold review (notes/reviewer-5.md) found a closed proof of False, accepted at 96d788a1:
```
def P0 : Type := Prop
def H (x : &Nat) : P0 := (*x := S Z; ⊤)
def RunG (f : Π(x : &Nat). Prop) : Nat := (let c = Z; let g = f; g(&c); c)
def RunGGen (f : Π(x : &Nat). Prop) : Id Nat (RunG(f)) Z := refl
def Boom : False := RunGGen(H)
```
D35 reads a call's class from the *callee value's* codomain term. At the generic call `g` is the abstract `f`, whose type's codomain is syntactically `Prop`, so `g(&c)` is erased and `c` stays `Z`. At the instance `g` is `H`, whose own codomain term `P0` is not syntactically a sort, so the call runs and writes. [Conv-pi] compares codomains by evaluation, so it lets `H : Π(x : &Nat). P0` stand where `Π(x : &Nat). Prop` is expected. Variants: through an identity function (`IdF(f)(&c)`), and the proof version (`f : Π(x : &Nat). ⊤` instantiated by a writing function whose codomain `V(Z)` computes to `⊤` but whose declared sort is not `Prop`). The same gap in [Close]'s row (`Unit` against `UU(Z)`, which computes to `Unit`) makes the paths disagree harmlessly, since `Unit` has one value. A direct call through the parameter was already safe, because the checker used the parameter's declared type there, which the rules did not say.
This is the two-path failure again, one level up. D35 made the class a property of a function's syntax, but conversion could still identify two function types whose functions the machine treats differently. The fix makes the class a property of the *type*, not only of the value. A Π-type records the class (returns types / returns proofs / other) and the [Close] row (`Unit` / `&T` / other) that its codomain term determines when it is formed. A function value's class and row are those of its declared type. [Conv-pi] additionally requires equal class and row. Every function value is then used only at a type of its own class, so the class the untyped machine reads from the value at a call equals the one the static type promised, whichever path runs.
Soundness of conversion is unaffected: D54 only removes identifications (types that denote the same set but differ in class stop being convertible), so the set model validates every remaining conversion. Cost: a program must write a function type's codomain in the same class as the functions it will hold, e.g. `Prop`, not a constant that evaluates to `Prop`; `RunGGen(H)` is rejected at the argument. The reviewer's suggestion was to "make the erasure class and the [Close] row part of the Π-type, respected by conversion, and prove stability rather than enumerate cases". The first half is this decision. The second half is the stability conjecture of the paper's §7, now tested by the v2 fuzzer (notes/fuzzer.md).

## D55. Sorts are syntactic: one notion of proposition (reviewer-4)
A second cold review (notes/reviewer-4.md, W1–W2) found closed proofs of False through the same seam as D54, approached from the proof side:
```
def P (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
def T (n : Nat) : P(n) := match n { Z => ⊤, S _ => ⊤ }
def W (u : Unit) : T(Z) := refl
def f (x : &Nat) : T(Z) := (*x := S Z; W(()))
def RunK (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
def Stmt (k : Π(x : &Nat). ⊤) (x : &Nat) : Id Unit (RunK(k, x)) () := refl
def Boom : False := (let c = 0; Stmt(f, &c))
```
There are variants through a generic statement (`Boom2`) and through an annotated `let` in a stuck match (`Boom4`, core syntax only). Its W2 is worse: `TT := Π(x : &Nat). T(Z)` is accepted as a `Prop`, yet `k(f) = 1` and `k(g2) = 0` are both provable for a data function `k`. So a proposition has two distinguishable inhabitants, which contradicts the model sketch ("Prop denotes subsingletons").
The diagnosis, in the reviewer's words: Ochr had two notions of "is a proposition". The *declared* sort (D28/D35) decided erasure, proof flags and [Close]'s row. The *computed* sort decided conversion, the sort of a Π-type, and the generic call's `⋆` binding. They disagree exactly on types whose sort is only known by computation, like `T(Z) : P(Z)`, and conversion moved values between the two readings. D54 puts the class into Π-types, which blocks `f` at a proof-class Π-type, but it does not remove the disagreement: `TT` is still a `Prop` with relevant inhabitants, and `Boom4`'s annotated `let` still reads the declared sort.
The fix removes the second notion instead of reconciling it at each use. Every term written where a type is expected must have a declared type that is syntactically a sort. Evaluation preserves declared types, and universes are not cumulative, so a well-formed type's declared sort then equals its computed sort. "Is a proof" has one meaning, every value of a proposition is `⋆`, and the sort of a Π-type is `Prop` exactly when its class is "returns proofs". `T(Z)` as an annotation is rejected, and with it `f`, `TT`, `Boom`, `Boom2` and `Boom4`. Still allowed: `U(n) : Type`, a family declared into `Prop` such as `W (n : Nat) : Prop`, `P0 : Type := Prop` used as a codomain (whose class is then "other", D54), and large eliminations like `Cells(T, n) : Type`. Excluded: sort-polymorphic type families. That includes the suite's own fixture `V (n : Nat) : U(n)` used as a type, `V(Z)`, whose declared type `U(Z)` is not a sort. The attacks written with it (LieG, BoomG, BoomH, EffInline, LieH) are now rejected at the root. (An earlier version of this entry wrongly listed `V(n)` as still allowed.) Measured with the ledger: with D55 on, D40's row flips nothing. "A stuck block is erased iff each of its arms is" follows from "a term is erased iff its type is a proposition", since a match's type is its arms' type. So D40 is deleted as a separate rule. The other erasure rows still flip.
This is the uniform endpoint the earlier erasure decisions (D28, D35, D40, D42, D49) were approaching one case at a time. With one notion of proposition, erasure is: a term is erased exactly when it is a proof (its declared type is a proposition) or when it forms a type (a type former, a call whose declared codomain is a sort, or anything in a type position). A `let`, sequence or match that computes a type in term position is not erased as a whole; its parts decide (`SeqT`). Several older clauses may be subsumed by this. The implementer should measure that with the ledger rather than assume it.

## D56. `J` computes only when its endpoints are convertible (reviewer-4 W4)
`J(A, a, b, P, h, t)` returned `t` unconditionally. That is equality reflection for open terms: under an absurd hypothesis, casts between `Nat → Nat` and `(Nat → Nat) → Nat` gave untyped λ-calculus inside the checker (`Om` diverged, "call depth exceeded"), and `J`-casting `5` to `Bool` put a `Nat` at type `Bool` ("[Match] on 5, which is not a value of Bool"), breaking well-formedness condition 6 in open contexts. Now `J` evaluates to `t` only when `a ≡ b`, as Lean's `Eq.rec` does, and is otherwise stuck. A `J` into a proposition is a proof and is never run, so proofs are unaffected. Data transport under a hypothesis becomes a stuck cast. The paper's decidability remark changes accordingly: equality reflection is gone, and what remains open is termination of normalisation.

## D57. Arrays are a library over a type-level model with a native runtime, not a kernel primitive (lead, after two design probes)
User constraints (2026-09-29):
- the length lives only in the type, and nothing stores it at runtime;
- growable arrays are a user-defined Σ;
- nothing recurses over an array, only over an index;
- runtime code never owns a sub-array (the objection to an earlier `SplitOff` sketch).

Two time-boxed probes designed each route against the same four benchmarks: B1, borrow a prefix, call anything, and the rest is unchanged; B2, quicksort; B3, a hashmap bucket insert; B4, a bounds proof from a runtime comparison.
- **Primitive route** (notes/arrays-primitive.md). Needs:
  - array values made of segments, with index places `p[i | h]` and `p[i..j | h]`;
  - a boundary normaliser;
  - `Le`, `Sub` and `Add` known to the kernel, with S-peeling rules;
  - an equality rule for arrays, a new well-formedness condition, and Ochr's first axiom (`SetGetOther`).

  Its benchmarks were not run. Its paper cost is about 1.2 pages of body and 2–2.5 pages of appendix.
- **Library route** (notes/arrays-library.md).
  - The model is `Cells(T, n) := match n { Z => Unit, S m => T × Cells(T, m) }`: exactly `n` elements by construction, with no dependent fields. `Array(T, n)` is owned and moves as a pointer; `Slice(T, n)` is borrow-only.
  - Sub-range borrows are scoped continuations (`WithSplit`).
  - Seven native functions plus drop glue are trusted, each with a simulation obligation that can be tested differentially. Everything else, including every lemma, is user code.
  - The kernel changes are static only: K1 a `Data` universe (D48's open item), K2 `unsized`, K3 `abstract` plus `implemented by`. No machine rule changes.
  - Its benchmarks were checked in today's checker (112 scratch declarations, all as expected; B1 holds by `refl` in its "joined back" form).
  - Its paper cost is about 0.5 page of body and 0.5 page of appendix.

The library route is chosen. Its costs are three facts that become one-induction lemmas (split-then-join, suffix-of-join, get-after-set), and continuation-scoped sub-range borrows. The primitive route would add a normaliser, arithmetic knowledge and an axiom to the part of the system that the reviews found most fragile. Both routes need strong recursion on Nat for quicksort ([Rec-<], K6, with `Lt` pinned like `True`/`And`); it is decided separately.

## D58. An impossible branch is stuck, never an ill-typed value (hashmap-port)
D49 (5) made a zero-arm match yield `⋆` "at any type", because it is unreachable. It is unreachable in closed runs, but it is reached in open ones. When a refinement makes a hypothesis false, re-normalising a sealed program runs into the `match h {}` arm and returns `⋆` at a data or borrow type. The next step (`*r` on a `⋆`) then errors, and D29 turns that into a type error, before the proof's own `match h {}` arm is even checked. Minimal (checker 96d788a1):
```
def IsZ (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
def G (x : &Nat) (h : IsZ(*x)) : &Nat := match *x { Z => x, S _ => match h {} }
def T (x : &Nat) (h : IsZ(*x)) : Id Nat (let q = G(&*x, h); *q) 0 := match *x { Z => refl, S _ => match h {} }   -- true, but rejected
```
This blocks every theorem about a function with a precondition-guarded impossible arm, such as the hashmap's `GetMut`. `GetMut` must take a presence proof, because `Option<&mut V>` is a borrow inside data (D48).
The fix follows the principle behind D56: an unreachable or unconvertible situation must stay *stuck* (a neutral) and never produce a value of the wrong type. That keeps well-formedness condition 6 ("values have their types") in open contexts. A zero-arm match in a proof position is erased as before (value `⋆`). Anywhere else, reaching it is stuck and the enclosing computation closes off. Sound: closed runs never reach it, and stuck terms are neutrals. D49 (5)'s "a zero-arm match is a declared proof, vacuously" now applies only where the match's own position is a proof.

## D53 amended after the viability study (checker lane, prototype at ochr-core-lean 5bfafa0a)
The literal rule caused 29 verdict flips across the suite. With the amendments below, 24 `clone`s in 21 declarations leave every verdict and message as before. Amendments:
(a) Re-runs of sealed programs, the two sides of `Id`, type formers and `clone`'s argument are erased and copy. A re-run is a computation of a value, not an execution.
(b) The body of a function whose declared result is a proposition or a sort is erased, since its calls always are (D28).
(c) A move leaves a *ghost* of the moved value that erased terms can still read. Erased uses do not count (quantitative-type-theory style), whatever the order of evaluation, so `SubM(x, old, LeAdd(old, y))` needs no runtime clone to feed its proof.
(d) Propositions are copy types. Borrows move even in erased reads.
(e) Function values follow Rust's `Fn` rule. A call does not consume the function it calls. A closure body may not move out of its captures, so a runtime read of a non-copy capture needs `clone`. A closure is a copy type exactly when its captures are.
(f) C5 extends: a stuck block moves in every variable that some arm moves.
(g) D48 (2) needs a new witness, because D53 now catches its old one (`BorrowTypes.G`) by itself.
(h) New ⊥ checks:
- reading or borrowing a place with ⊥ anywhere inside it;
- capturing a partly moved place;
- ending a borrow whose content holds ⊥ (the "whole again" rule).

The study also found that the checker decides several erasure classifications *after* evaluating the term: sequencing forms by their tail, calls by the class set after the arguments ran, ascriptions, λs, and leaves by their value. The rules say these are syntactic. D53 needs the answer before a read, and the two-path discipline needs it anyway, so erasure becomes a syntactic pre-pass, with the after-the-fact flags kept as an assertion that the two agree. This is done with D55, which makes the pre-pass simple ("the term's type is a proposition or a sort, by declared sort").
Ergonomic cost to watch: comparisons on `Nat` consume both sides (`Lt(clone(k), clone(v))`) until there are shared borrows or a copy index type.

## D54 refined: compare the class and the borrow part of the row, not Unit against other (checker lane)
As first implemented (4b8bdbd2), D54 compared whole rows. That broke the arrays library: `WithSplit(E, R, …, f : Π(l)(r). R)` instantiated at `R := Unit` with a `λ … : Unit => …` has the Unit row on the argument and the "other" row on the parameter (its codomain term is the variable `R`). The result was 11 rejected programs, the whole quicksort among them. In general, a higher-order function polymorphic in its continuation's result type could not be used with a `Unit`-returning function. The Unit and "other" rows produce identical loan fills and differ only in the result, `()` against a sealed program of type `Unit`. That is reviewer-5's harmless disagreement: `Unit` has one value, and a sealed program is not a constructor, so disjointness (D47) cannot turn the mismatch into `False`. Only the borrow part of the row is unsound to confuse, because a borrow returned as data is wrong. So conversion now requires equal classes and equal "returns a borrow" flags. `Functions.RunUH` (the Unit-row variant) is accepted, and D54's soundness witnesses are unchanged.

## D59 (planned). η for `Unit`: `Eq Unit a b ≡ True`
The uniform end of D54's refinement, and reviewer-4 W5's "a [Close] row special-cased for Unit because there is no η". `Eq` at `Unit` computes to `True` for any two values, since every value of `Unit` is `()` in the model. Then [Close] needs no `Unit` row: a stuck `Unit`-returning call returns its sealed program like any other, and every statement that relied on the `()` row still holds, by the new rule. [Close] is left with two rows, borrow and other. To be scheduled after D53.

## D53, second amendment: `Nat` stays non-copy; a declared-copy `Word` for indices, lengths and keys
The checker lane measured D53's `clone` noise. All 24 clones in the suite are on `Nat` values. The arrays library would need about 35, of which about 25 are on index or length `Nat`s and about 8 are in quicksort's partition. Its recommendation was to make `Nat` a copy type. The user's constraint rules that out for the running example: "if nat is made copy then AddM etc. must not use it because the whole point of those functions is they're doing moves". `AddM` on `Nat` is the paper's running example and the user's original requirement (`Id Unit (AddM(&x, 0)) ()`).
Resolution, in Rust's terms: `Nat` is the unary structure that in-place code walks and mutates. It is not a copy type, and reads of it move. Numbers that code only computes with are a separate type, `Word := Z | S(pred : Word)`. It is declared `copy`: unary in the logic, and a machine word in the cost model, as Rust's `usize` is `Copy`. The D53 copy criterion becomes: a type is copy if it is declared `copy`, or if it is non-recursive and all its fields are copy types. Declaring a recursive type `copy` is a cost-model statement, not a logical one: copying never affects soundness, since erased reads already copy. Array indices and lengths (D57), comparison keys (the tree example, the hashmap) and loop counters use `Word`, with its arithmetic and index lemmas in the library once, not duplicated over `Nat`. `Nat` keeps `AddM`, `Add`, `Le` and the examples that are about moving data.

## D60 (planned). `rewrite h in t`, and destructuring `let` (proof ergonomics, from the hashmap case study)
The case study (notes/hashmap-case-study.md §2, §6) measured Ochr's property proofs at 1.5 times Aeneas's in tokens. The single largest cause was rewriting: 35 `J`s, each with an explicit motive `λ(z : T) : Prop => …` restating the goal around the hole, plus 27 uses of `TransN`/`TransO`/`SymmN`, which exist only to orient `J`. The thesis is about total development size, so this matters.
- **`rewrite h in t`**, a typing rule and not new evaluation. For `h : Eq A a b`, checked against a goal `G` that is a proposition: generalise every occurrence of `b`'s normal form in `G` to a fresh `σ`, by the same replacement [Split] uses to generalise a sealed program (D34). Then substitute `a` for `σ`, and check `t` against the result. `rewrite ← h in t` swaps the roles of `a` and `b`. The term is a proof whose value is `⋆`. It is `J(A, a, b, λz. G[z/b], h, t)` with the motive read off the goal, so it adds nothing to the model. It never runs, so D56 is unaffected.
- **Destructuring `let`**, surface sugar. `let ⟨x, y, …⟩ = p; u` and `let (x, y) = p; u` mean `match p { C(x, y, …) => u }` for a single-constructor inductive (`And`, `Pair`, …). Nested patterns are allowed. On a place, the pattern variables are sub-places, as in any match. On a term, a temporary is bound first.
Both are elaboration or typing-local, so the paper presents them in a paragraph, with [Rewrite] in the appendix. The case study is then re-measured. That can move the result on the thesis, so both measurements are reported.

## D61 (planned). `split`: case-split on a sealed program found in the goal (hashmap case study)
After D60 the case study's largest remaining proof overhead is re-running part of the program on a copy just to name a sealed result and split on it: 31 sites, plus 33 splits on spec-side sealed values, together about 8.5% of the proof tokens. `split in t` / `split { C₁ => t₁, … }`: find the goal's first stuck match (in a fixed, stated traversal order) whose scrutinee is a sealed program, generalise that program (D34, recorded as for [Split]), and split. This is [Split] with the scrutinee found in the goal rather than written as a place, the analogue of Lean's `split`. A typing-level form: it never runs, and adds nothing to the model (it is [Split] on a generalised neutral). Estimated effect: the case study's proofs at about 1.26 times Aeneas's property proofs, down from 1.38.
