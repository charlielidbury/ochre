# lean-checker: an executable checker for RULES v2.0, and what running it found

**recCands fix (§20):** a closed proof of `False` from the fuzzer: typing a sealed program wiped the [Rec] state. The [Rec] frames now carry their candidates and merge by identity on every restore; four trigger paths are regressions; the audit of the other state kept outside Ω found no other mis-merge. 449 verdicts, all as expected.

**reviewer-3 round (§15):** D48 (borrows of data only, only at the top of declared types; Π-types compared under their binders), D49 and D50 are implemented with regression tests and switches, ∧-elimination is tested, and every ledger row is classified (23 soundness with named witnesses, 1 false lemma, 3 model, 3 policy, 16 completeness; none flips nothing). 427 verdicts, all as expected.

**v2.0 (§14):** False/True/And are library inductive declarations and the checker's primitives for them are gone; Prop inductives, zero constructors, uniform parameters, by-type matching on proofs, subsingleton elimination and D47 are implemented with switches and asserted ledger rows. 364 verdicts, all as expected. Findings: in this machine D42 (proofs are ⋆), not D45's subsingleton restriction, is what blocks the `Or` attack's closed `False` (D45 is still needed for the model and for canonicity); `And(True, P) ≡ P` as normalisation hides an `And` from a match; a v1.9 checker bug (a match's scrutinee type was assumed from its arms, a type-safety hole) is fixed. No closed proof of False found against v2.0.

**v1.9 (§12):** D41 (confinement) is implemented and checked. The fail-safe experiment finds that D41 as written catches misclassified inline terms but not misclassified calls or blocks: the erased-call exception lets their bodies' writes through. 247 verdicts, all as expected.
**v1.7–v1.8 (round 3, §10–§11):** D35–D39 implemented. The formal appendix's BoomL/BoomB, its positivity attack, and breaker-fresh-v16 X1–X5 are regressions. Three more closed proofs of false were found and fixed on the way: P1 against the v1.6 checker, P2 against a first v1.7 reading, and P3 against P1's first fix. 239 verdicts, all as expected. §11 lists where the checker, RULES and the appendix still differ.
**Verdict (as of v1.5, phase 2):** RULES v1.5 is implemented, extended to user-declared inductive types (lists, binary trees), and 185 verdict assertions all hold. Every §7 example (E1–E5) is accepted. Every must-fail program and every attack from rounds 1–2 is rejected: e346 `Bad`, `Oops2`, `Loop`/`Bot'`; meta-model C1, C2; breaker-close A1–A4 (and A5 terminates); breaker-close-v1 N1 and meta-model-v1 R1 (the closed proofs of false built from `T` and `Q`); breaker-frame attack 1; E5's three rejections. Each is caught by the rule meant to catch it: switching that one rule off flips exactly the verdicts it guards (§5).
**Most important finding:** **D18 (owners are sets) is load-bearing in v1.4.** An uncurried version of meta-model C2 (§4) uses v1.2's annotated block, which forms a type while a returned borrow's hole is in two owners and checks each arm against it after the split. Single-owner observation accepts it and yields the closed proof `ClosedD18 : Eq Nat 0 1`. Round 1's L1 (`f` escaping as a value) is fixed in v1.1 by exactly the rule this checker used.
**RULES.md must change:** nothing unsound remains that I can find. §3 lists what is still underspecified: a static reading of "moves out of in any arm", the sort of a sealed type, Unit η, universes, and J's motive sort. D18 should stay, with §4's program as its motivating example rather than the curried C2.
**Confidence:** high that the verdicts are what the implementation computes (all asserted in a green build; traces reproduce the round-1/2 hand derivations, including deriver-e5's rejection reasons symbol for symbol); medium that every clarification matches the intended reading.
**Not checked:** metatheory; universe levels beyond `Type_i : Type_{i+1}`; completeness beyond the examples. **Performance:** the compiled checker checks all 139 declarations in about 5 ms (median of 21 runs; the heaviest declaration, `BadD18`, takes about 0.2 ms). A clean build takes about 11 s, and `lake exe tests` about 20 s including compilation.

Code: `ochr/core/lean/` on branch `ochr-core-lean` (README: build, syntax, rule → function table). `lake build` checks every assertion. `lake exe tests` prints the verdict tables and the ledger. Trace any definition: `(run "E1" E1 { trace := true }).showTrace "AddMZero"`.

## 1. Rule bugs found by running the rules

| # | Found against | What | Status |
|---|---|---|---|
| L1 | v1 | `[Rec]` checked only recursive calls: `Knot x := Apply(Knot, x)` (f passed as a value) was accepted, and `Knot(0) : Eq Nat 0 1`. P5 meant nothing even looped. | Fixed in v1.1 ([Rec]: f only as the head of a call), the same rule this checker implemented (= breaker-close A4). Regression: `Attacks.Knot`, `KnotBoom`. |
| L2 | v1 | `f(&x, x)`: reading `x` ends the borrow already evaluated as argument 1, so the callee receives `⊥`. Without a check, `Dead(W7, 0)` is accepted and its concrete run writes through `⊥`. | v1.2 puts arguments in temporaries and moves them into the frame, so moving `⊥` is a [Read] error. The checker's value-level argument check is that consequence. Regression: `More.Dead`, `DeadTwice`. |
| L3 | v1 (this checker's first version) | A recursive call inside a nested λ, checked at the λ's own generic call, escaped [Rec]: `KnotL x := let g = (λ(y : Nat) : ⊥ => KnotL(y)); g(x)`. | Fixed in v1.3 ([Rec] covers nested functions and block arms). The checker keeps a stack of [Rec] contexts. Regression: `Attacks.KnotL`, `KnotLBoom`; a structural call through a closure (`AddZeroC`) is still accepted. |
| **L4** | **v1.2–v1.4** | **Single-owner observation is exploitable without currying**, through the annotated block (§4). | D18 already requires all owners. This is its first first-order regression test: `D18.BadD18`, `D18.ClosedD18`. |
| L5 | v1.4 (this checker's first v1.4 version) | P2 erases *types* as well as proofs. My first v1.4 version restored Ω only after proofs and in type positions, so a type-valued call in program position (`let T = F5(&*x)` with `F5 : … → Prop` writing `*x`) kept its write. | Fixed: Ω is restored after any term whose value is a proof or a type. v1.4 is right here. Regression: `Probes.TypeErased`. |
| **P1** | **this checker at v1.6** | A place holding a proof did not make a sequence erased, while a block of type `⊤` was: `BoomP : Eq Nat 1 0` accepted (§10). | Fixed: a place, constant or λ holding `⋆` is a proof. Regression: `V17.LieP`, `BoomP`. |
| **P3** | **P1's first fix** | A variable was a proof when its value was `⋆`. But `g(0)`, with `g : Π(y : Nat). V(Z)` data by syntax, is `⋆` at an instance and a sealed program at the generic call, so `BoomH : Eq Nat 0 1` was accepted (§11). | Fixed: a variable is a proof iff it is declared so (a flag on the binding, set from the syntax). Regression: `V18.LieH`, `BoomH`. |
| **P2** | **v1.7 read as "a block of computed sort Prop is erased"** | The block's computed type (`V(Z) = ⊤`) disagrees with the arms' syntactic classes: `BoomG : Eq Nat 1 0` accepted by my first v1.7 version (§10). | Fixed: a block is erased iff every arm is a proof. RULES wording suggested. Regression: `V17.LieG`, `BoomG`, `TruthG`. |
| **R1** | **this checker at 96d788a1 (fuzz-port)** | Typing a sealed program (`sealedType`, on a private copy outside the enclosing functions) wiped the [Rec] candidates: the restore merged them by position, so no later recursive call was checked. `Boom : False := Lie(0, ⟨refl, refl⟩)` accepted. | Fixed: the [Rec] frames carry their candidates and a `uid`, and restores merge by `uid` (§20). Regression: `Recursion.Lie`, `LieCap`, `LieRead`, `LieId` and their `Boom`s. |

## 2. Verdicts (expected vs actual: all 139 as expected)

| Program | Declarations (A = accept expected, R = reject expected) | Result |
|---|---|---|
| E1 | AddM, AddMZero, Add, **AddZero** (`S p => AddMZero(&p)`, no cong), AddZero' (`AddMZero(&x)`): all A | as expected |
| E2 | AddM, TailM, AddM', AddMEq, AddMEqOwned, AddM1, TailNoop: all A | as expected |
| E3 | AddM, AddMZero, **AddToOne** (inline, closed off), AddToOne', Pick, AddToOne'', AddToOneZero (about the inline AddToOne), AddToOneZero', AddToOneZero'': all A | as expected |
| E4 | AddM, AddMZero, Twice, TwiceNoop, TwiceM, TwiceMMove, TwiceMZero, Add, **TwiceMZero'** (modular, with `J(A, a, b, P, h, t)`): all A | as expected |
| E5 | AddM, Add, Le, LeAdd, SubM, AddSub, **AddSubId**, LeId, ProofIrr (deriver-e5 Q1), ExFalso, LeZero, TwoPhase (Q6): A; AddSubStale, AddSubWrong, AddSubIdReborrow, TwoPhaseMoved: R | as expected |
| E6 | UseMoved R, UseReborrowed A, **LemmaMoves A** (v1.3: a lemma's arguments run on a private copy; R under v1), WriteThenRefl R, WriteThenRefl' R, ZeroIsOne R, Add01 R, NotAdd01 A, Snapshot A, SnapshotLie R, DanglingLocal R, DanglingTail R, DanglingReborrow R (+ AddM, AddMZero, TailM A) | as expected |
| Attacks | e346 Bad R, Oops2 R, Loop R, Bot' R; breaker-close A3 Loop2 R, Spin R, A1 BadA1 R, A2 Boom R / BoomIsTrue A / Boom' R, seal variant TA2 A / TA2Z R; C1 FP2 A; C2 G R, BadC2 R; A4/L1 Knot R, KnotBoom R; L3 KnotL R, KnotLBoom R, AddZeroC A; **breaker-close-v1 N1: N1T A, N1Closed R; meta-model-v1 R1: Q A, QBoom R** (+ helpers A) | as expected |
| More | MatchAfterOpaque A, Dead R, DeadTwice R, NotDead A, g A, attack R, attack' R, NonTailRec A, StuckGoal A, StuckGoalSplit A, StuckGoalWrong R, AddMZeroLet A | as expected |
| Probes | T, UseT0, UseT, DepMatch A; DepMatchWrong R; Outer A; OuterBad R; Cap, CapMut, AliasRead A; AliasDangling R; Lemma, W5 A; **EffArg R** (v1.3); EffArgErased A; F5, **TypeErased** A; WriteInBlock A; AliasAfterBlock R; MovedByBlock R; ReborrowInBlock A (+ AddM) | as expected |
| D18 | Pick, Probe A, Use R (its expected parameter type has one conjunct per owner); Pick3, K A; **BadD18 R, ClosedD18 R** | as expected |

The rejection reasons are the intended ones (`lake exe tests` prints every reason). E5's rejections reproduce deriver-e5 §E5.6 exactly. For example, `AddSubStale` fails with "argument 3 (h) has type ⌈Le(σ0, ⌈let c1 = σ0; AddM(&c1, σ1); c1⌉)⌉, expected ⌈Le(σ0, 0)⌉", and `AddSubIdReborrow`'s IH carries the `S` that its goal lacks (Q5). E5.4's central claim holds: `LeAdd(old, y)`, a proof about the pure `Add` of a snapshot, is accepted where `SubM` requires `Le(y, *x)` about the mutated `*x`, because the in-place `AddM(&*x, y)` and the pure `Add(old, y)` close off into the same sealed program.

## 3. Clarifications: what the rules left open, the reading implemented, and its status in v1.4

Status "adopted" means a later rule set says what this checker already did. "Changed" means the rules chose differently and the checker followed. "Open" means v1.4 still does not say.

| # | Question | Reading implemented | v1.4 status |
|---|---|---|---|
| C1 | Which parameter decreases? | Declared with `by x` (`Term.fix`'s `dec`); without `by`, a recursive call is an error. [Rec] fails at the offending call, before running it (running a non-structural call first need not terminate). Inference is kept as `Config.inferRecPos`. | changed (v1.2 D23; the checker inferred it before) |
| C2 | Do all types form on a copy? | Every type former is evaluated on a private copy. | adopted (v1.2 D24) |
| C3 | May a Π-type capture a borrow? | No: capturing a borrow variable at formation is an error. | adopted (v1.3) |
| C4/C6 | What is a non-tail block's type? | The annotation `let x : T = match …` if present, with each arm checked against `T` refined by that arm's refinement (the refinement is substituted into `T`); otherwise the arms must agree. | adopted (v1.2 D22) |
| C5 | How does a stuck block take its free places? | Rust-style on maximal place prefixes (v1.3). Each used place gets a mode: moved (reading a borrow variable as a whole, or assigning one as a whole), `&` (under `&_` or left of `:=`), or copied (read). A captured place is a used place with no strict prefix among the used places, and takes the strongest mode below it. Body places under it are renamed to the parameter (with `*` for `&`). | adopted (v1.3); a static/dynamic detail is still open, see below |
| C7 | What is a proof value? | Every value of a proposition is `⋆`: Prop-typed globals, closures, parameters at the generic call, and results. | adopted (v1.4 D27 for parameters) |
| C8 | [Split] on a sealed program | Generalise every occurrence to a fresh `σ`, then split (the annotation of an annotated block too). | adopted (v1.2 D22) |
| C9 | Pattern variables after a write | `y` is `p.1`, re-read after writes; reading `p.1` without an `S` head is an error. | adopted (v1.4) |
| C10 | Do a proof call's arguments run for real? | v1 reading: yes, only the call was skipped. **v1.3 reverses this**: a proof, argument evaluation included, runs on a private copy. Implemented by restoring Ω after any term whose value is `⋆` (by C7, exactly the Prop-typed terms), in both modes. Consequences: `LemmaMoves` is now accepted, `EffArg` rejected, and Q6's `TwoPhase` accepted. | changed (v1.3 D26) |
| C11 | Values in flight | Temporaries in the current frame, visible to [End]; moving a `⊥` temporary into the callee frame is a [Read] error (L2). | adopted (v1.2 D21) |
| C12 | `J` after `Eq A a a ≡ ⊤` | Explicit endpoints `J(A, a, b, P, h, t)`: `h` must have type `Eq A a b` as computed (so `⊤` when `a ≡ b`), `t : P(a)`, result `P(b)`, value `t`'s. `cong`, `trans`, `symm` remain implemented as derivable conveniences but are used by no example. The motive may have any sort (a `Type`-valued motive transports data, keeping its value); deriver-e5 Q2 suggests Prop only. | adopted (v1.2 D23); the motive's sort is open |
| C13 | λ's result type | `λ(x : A) : B => t` (a `fix` without `by`). | as in v1.2's grammar |
| C14 | Unit η for abstract values | Not assumed: `σ : Unit` is not `()`. | open (no example needs it) |
| C15 | Universes | `Prop = sort 0`, `Type_i = sort (i+1)`, `sort l : sort (l+1)`, a Π at the `imax` level of its parts (computed at generic arguments); nothing else. | open |
| C16 | The sort of a sealed type | A sealed program in result form `L; C` whose head's codomain is (syntactically) a sort `l` has sort `l`. This is what makes `⌈Le(σ, …)⌉` a proposition, so `LeAdd`'s calls are proofs and `SubM`'s `h` is `⋆`. Other sealed programs have no known sort, and asking for one is an error. | v1.4 says "a sealed program of sort Prop is a type" but not how its sort is known |
| C17 | `Id` in untyped callee bodies | Sides are not re-checked; an owner with no stored type takes its value's type. | implementation detail |
| C18 | A call of a sealed *function* value in untyped code | Needs the function's type for [Close]'s row, and callee frames do not store types; an error ("the type of the sealed function … is not known here"). Never hit. | open (rare) |
| C19 | "Moves out of in any arm": static or dynamic? | A borrow variable read as a whole anywhere in the block is moved (static, like Rust), and so is one that an arm actually left `⊥` (dynamic). They differ only on reads in dead sub-branches of an arm. | open (wording) |

## 4. D18 is load-bearing: the uncurried C2

The lead asked whether any first-order program needs owner sets. It does, since v1.2:

```
def Pick3 (x : &Nat) (y : &Nat) (s : Nat) : &Nat := match s { Z => x | S _ => y }
def K (z : &Nat) (e : Id Unit (*z := 0) (*z := 1)) : Eq Nat 0 1 := e      // at K's generic call e's type is Eq Nat 0 1
def BadD18 (s : Nat) (hs : Eq Nat s 1) (a : Nat) (b : Nat) : Eq Nat 0 1 :=
  let r = Pick3(&a, &b, s);                                   // r ↦ borrow_k ⌈…⌉; a ↦ A[loan_k], b ↦ B[loan_k]: the hole is in both
  let e : Id Unit (*r := 0) (*r := 1) = match s { Z => hs | S _ => refl };
  K(r, e)
def ClosedD18 : Eq Nat 0 1 := BadD18(1, refl, 0, 0)
```

With `A[w] = ⌈let c1 = σa; let c2 = σb; let r = Pick3(&c1, &c2, σs); *r := w; c1⌉` and `B[w]` the same ending in `c2`:
- **Owner sets (v1.4):** the annotation forms as `Eq Nat A[0] A[1] ∧ Eq Nat B[0] B[1]`. In arm Z, `σs := 0` re-runs both: `A[w] ≡ w` and `B[w] ≡ σb`, giving `Eq Nat 0 1`, which is `hs`'s refined type ✓. In arm S, `A[w] ≡ σa` and `B[w] ≡ w`, giving `Eq Nat 0 1`, and `refl : ⊤` fails. **Rejected.**
- **Single owner (`multiOwner := false`, first owner `a`):** the annotation is `Eq Nat A[0] A[1]`. Arm Z gives `Eq Nat 0 1`, matched by `hs` ✓. Arm S gives `⊤`, matched by `refl` ✓. Then `K(r, e)`: `e`'s parameter type at the call point is `Eq Nat A[0] A[1]` ✓, so `BadD18 : Eq Nat 0 1`, and `ClosedD18` (`hs := refl` at `s := 1`) is a closed proof of `Eq Nat 0 1`. **Accepted: unsound.**

The ingredient v1 lacked is a type *formed before* a split and *checked in the arms*. Currying (the original C2) provided that, and so does v1.2's `let x : T = match …`. The model's T2c/Lemma Inj explains why all owners are needed, and this program is the first-order witness. For the paper: owner sets are needed by the metatheory's injectivity lemma, and are exercised by this annotated-block program (`D18.BadD18` in the suite).

## 5. The counterfactual ledger: which rule guards which test

Each `Config` switch turns off one rule. `Registry.lean` asserts that exactly these verdicts flip and nothing else (printed by `lake exe tests`):

| Switched off | Verdicts that flip |
|---|---|
| P2 (v1.3 D26): erased terms (proofs and types) run on a private copy, so v1's call-keyed P5 is what remains | Attacks.N1Closed, Attacks.QBoom → accepted (the closed proofs of false from breaker-close-v1 N1 and meta-model-v1 R1); Probes.EffArg → accepted; E6.LemmaMoves, E5.TwoPhase, Probes.EffArgErased, Probes.TypeErased → rejected |
| D18: owners are sets | D18.BadD18, D18.ClosedD18 → accepted (§4) |
| D17: [Rec] entry-value guard | Loop, Bot', Loop2, Spin, KnotL, KnotLBoom, Probes.OuterBad → accepted; since the recCands fix (§20) also Lie, LieCap, LieRead, LieId and their Booms |
| D19: [Access] ends loans inside the content | Attacks.BadA1 (breaker-close A1) → accepted |
| L1 (v1.1): self only as a call head | Knot, KnotBoom → accepted |
| L2 (v1.2 temporaries): no `⊥` argument | More.Dead, More.DeadTwice → accepted (and `Dead`'s concrete instance writes through `⊥`) |
| C8 (v1.2): generalise before splitting on a sealed program | More.MatchAfterOpaque → rejected |
| C5 (v1.3): a stuck block moves in what an arm moves | Probes.MovedByBlock → accepted (and its concrete run reads `⊥`) |
| D27 (v1.4): proof parameters are `⋆` at the generic call | E5.ProofIrr (deriver-e5 §E5.7) → rejected |
| L3 (v1.3): [Rec] covers nested functions | Attacks.KnotL, KnotLBoom → accepted |

v1's P5 switch (`p5 := false`: run proof calls instead of skipping them) is no longer in the ledger. Since v1.3, skipping is an optimisation of P2. In this checker, switching it off also switches off the `⋆` representation of proofs, because a run proof that gets stuck closes off into a sealed program rather than `⋆`. So its row would not isolate one rule. The [Close] precondition (v1.1) is asserted on every call that closes off and never fired on the suite. It is skipped only in the D19-off run, which models the rules without the invariant it states.

**On what "must be rejected" means for N1 and R1.** Under v1.3's P2, breaker-close-v1's `T` and meta-model-v1's `Q` are *true* statements: the write inside the proof-typed block is erased, so the observed place does not change. The checker accepts them. What must be rejected is the closed proof of false that v1.1 derived from them. `N1Closed : Id Nat 1 0 := N1T(0)` is rejected because `N1T(0) : ⊤`. `QBoom := J(Nat, S Z, Z, …, Q(0, 0), refl)` is rejected because `Q(0, 0) : ⊤`, not `Eq Nat 1 0`. Both flip to accepted with the P2 switch off (v1's call-keyed P5), which is the evidence the paper needs.

## 6. Timings and size

Median of 21 runs of the compiled checker (`lake exe tests`), per program:

| Program | Declarations | Check time |
|---|---|---|
| E1 | 5 | 0.2 ms |
| E2 | 7 | 0.5 ms |
| E3 | 9 | 0.8 ms |
| E4 | 9 | 0.5 ms |
| E5 | 16 | 0.9 ms |
| E6 | 16 | 0.4 ms |
| Attacks | 35 | 0.8 ms |
| More | 13 | 0.3 ms |
| Probes | 22 | 0.5 ms |
| D18 | 7 | 0.3 ms |
| **total** | **139** | **about 5 ms** |

The heaviest declarations take about 0.14–0.22 ms each: `BadD18`, `AddToOneZero''`, `TwiceMZero'`, `AddSubId`. Per-declaration times are printed by `lake exe tests`.

Lines per module (`wc -l`, including comments):

| Module | Lines | Contents |
|---|---|---|
| `Ochr/Syntax.lean` | 133 | terms, places, values, structural equality |
| `Ochr/Basic.lean` | 209 | `Eq`/`∧` smart constructors, traversals |
| `Ochr/Pretty.lean` | 133 | printer |
| `Ochr/Env.lean` | 210 | Ω, machine state, configuration |
| `Ochr/Obs.lean` | 127 | paths, owners, footprint |
| `Ochr/Machine.lean` | 1090 | machine, [Seal], [Close], stuck blocks, `Id`, [Call-type], [Rec], [Def] (one mutual block of about 960 lines) |
| `Ochr/Check.lean` | 98 | programs |
| `Ochr/Surface.lean`, `Ochr/Notation.lean` | 180 + 138 | surface syntax and the `ochr` command |
| `Ochr/Test.lean`, `Tests.lean` | 65 + 73 | runner |
| **checker total** | **about 2,450** | |
| `Ochr/Examples/*.lean` | 674 | the 139 assertions, unit tests, ledger |

## 7. Other observations

- **Normal forms need no α-renaming step.** With de Bruijn terms whose binder names `==` ignores, and [Close] building `⌈L; C…⌉` in one fixed shape, the goal's and the IH's sealed programs are structurally equal whenever the round-1/2 derivations say they are "equal up to renaming" (e1 F7).
- **"Discard the partial run" is exception semantics.** `stuck` is an exception carrying only the fuel spent. The innermost call catches it with the state it had at the call point, which is exactly [Close]'s restore. [Seal]'s head call rethrows instead.
- **Loans are variables.** [End] is one substitution over Ω followed by re-normalising the sealed programs it touched, and the same function implements refinement and generalisation.
- **P2 costs one line.** "A term whose value is `⋆` leaves Ω as it found it" is sufficient, because C7 makes `⋆` exactly the values of propositions. That one line closes breaker-close-v1 N1 and makes a proof's arguments behave like Rust's two-phase borrows (E5's `TwoPhase`).
- **Rust-style block captures fix a real failure.** deriver-e346-v1 N3's overlapping places (`*x` written in one arm, `(*x).1` in the other) close off as one `&*x` with `(*x).1` renamed inside (`Probes`/trace). A read-only block copies `*x` instead of turning it into a sealed program.
- **Dependent types through mutation work as deriver-e5 derived them**, including large elimination into `Prop` (`Le`), stored parameter types refined twice by [Split] (`SubM`'s `h`), and proof irrelevance at the value level (`ProofIrr`).
- **Paper syntax.** The `ochr { … }` block reads as RULES §7 does, with `by x`, calls `f(a, …)`, and `J(A, a, b, P, h, t)`.

## 8. Rules v1.5 (D28–D33): breaker-fresh F1–F5 and reviewer-1

Implemented, each with a `Config` switch. The ledger (asserted in `Registry.lean`) shows that switching each one off lets exactly its attack through:

| Rule | Implementation | Switch off → flips |
|---|---|---|
| D28 erasure by declared class | `fnClass` gives a function's class once from its declared codomain at the generic call (a sort: returns types; sort Prop: returns proofs; else data), cached per Π-type. `eval` erases a term by syntax: calls by the callee's class; `;`/`let`/`match` by their tail; proof formers; ascriptions at a proposition. Never by the value. | V15.Boom (F1's closed `Eq Nat 0 1`) → accepted; V15.MainW0 (`MainW(0) = 1`, what compiled code computes) → rejected |
| D29 matching ends loans inside a neutral head | `accessNeutralHead` before every match | V15.Bad, V15.Main → accepted (and the concrete `Main0` reads ⊥) |
| D30 closures by generic-call observation | `conv`/`convFn`: structural except at function values, which are compared by Π-type, captures, and the result plus final cell contents of one shared generic call. A comparison that needs itself (a recursive function stuck at its own generic call) answers "no", which is sound and incomplete. Also gives completeness: `Conv`, `ConvW` (same effects, different code) are convertible. | V15.Boom3 (F3) → accepted under "result only" |
| D31 no `f` without `by` | An occurrence of the self variable in a `by`-less body is an error. | V15.Loop, Boom4 (F4) → accepted under the v1.3 literal reading |
| D32 pattern variables as sub-places | Already so: the resolver substitutes `p ↦ (*x).1`. The switch emulates the literal capture rule. | V15.Clear, Boom5 (F5) → accepted |
| D33 type-level matches checked | Already so: type-level stuck matches are split and their arms checked (C6). | (no switch) |

**Correction to §4 and to round 1.** Round 1 said D18 protects nothing v1 lets you write. That was wrong. Reviewer-1's C1 (`D18.GR`/`BadR`) needs no annotated block and no currying. A hypothesis parameter's type recomputes, with local copies, the very sealed program that owner `a1` holds after `Pick`, and single-owner observation turns `Neq`'s parameter type into that one equation. It is expressible in v1. The missing ingredient in my round-1 search was a parameter type that *writes* (`*r := Z` in a local program), not only one that reads. D18's ledger row now lists both `BadD18`/`ClosedD18` and `GR`/`BadR`.

**D30's normal form is circular for recursive functions.** A recursive function stuck at its own generic call observes only a sealed call of itself (`⌈…f(…)…⌉`). Comparing two such functions therefore needs the comparison itself. Assuming the pair equal (coinductively) would equate *any* two recursive functions of the same type, which is unsound. The checker answers "not convertible" instead, which is sound and incomplete. RULES should say which.

## 9. Phase 2: general inductive types

**What was added.** User-declared inductive types with several constructors and several fields: `inductive List := Nil | Cons(h : Nat, t : List)`, `inductive Tree := Leaf | Node(l : Tree, v : Nat, r : Tree)`, `inductive Bool := False | True`.
- Constructor values are `C(v₁ … vₖ)`, and field places are `p.f`.
- In `match p { C₁(x̄) => … | … }` the pattern variables are the field places (D32).
- [Split] refines `σ` to `C(σ₁ … σₖ)` with fresh `σᵢ` of the field types. [Rec]'s strict subterms range over all fields, and the decreasing parameter may have any inductive type.
- Every rule of §3–§5 applies unchanged: [Access], [Close], stuck blocks (captures on maximal prefixes through field places), owners and footprints.
- `Nat` stays builtin, not rebuilt on the general mechanism. That is a non-uniformity in the implementation, not in the rules.

**Examples** (`Ochr/Examples/Inductives.lean`, 24 assertions, all as expected):
- **(a)** `AppendM(xs : &List, ys)` in place, and `AppendMNil : Id Unit (AppendM(xs, Nil)) ()` by bare recursion. The trace shows the environment doing a two-field congruence: goal and IH are both `Eq List Cons(σ1, ⌈AppendM on σ2⌉) Cons(σ1, σ2)`, with the untouched `h` carried. `AppendMOne` (appending `Cons(0, Nil)`) is rejected.
- **(b)** `LastM(xs) : &List` (a borrow of the final `Nil`), `AppendM'` through it, and `AppendMEq` by bare recursion, as `AddMEq` was.
- **(c)** Binary search trees. `Lt(a, b) : Bool`; in-place `InsertM(t : &Tree, k) by t`, which recurses into `&l` or `&r` depending on `Lt(k, v)`; the pure `Insert`; and **`InsertMEq : Id Unit (InsertM(t, k)) (*t := Insert(*t, k))` by bare recursion**. Its arms' goals and IHs are `Eq Tree Node(σl, σv, ⌈InsertM on σr⌉) Node(σl, σv, ⌈Insert(σr, k)⌉)` (False: the right field is rewritten) and the mirror image (True: the left field). The environment carries the other two fields. A variant that inserts on the wrong side (`InsertMSwapEq`) and a recursion on the node itself (`InsertLoop`) are rejected.
- **The measure: inserting grows the size by one**, `SizeInsert : Id Nat (S (Size(t))) (Size(Insert(t, k)))` with `Size(Node(l, v, r)) = S (Add(Size(l), Size(r)))`. Accepted. The proof needs:
  - `J(A, a, b, P, h, t)` to rewrite with the IH under the context `S (Add(…, □))`;
  - in the True arm, nothing else: `Add` recurses on its first argument, so `Add(S a, b) ≡ S (Add(a, b))`;
  - in the False arm, the lemma `x + S y = S (x + y)`. It is proved in place by bare recursion (`AddMS(x : &Nat, y) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x)`) and transferred to the pure `Add` by one call (`AddS := AddMS(&x, y)`), exactly as `AddZero` comes from `AddMZero`.
  - Without the lemma the arm is rejected with the precise missing step (`SizeInsertNoLemma`: `S (S (x + y))` against `S (x + S y)`). `SizeInsertTwo` (grows by two) is rejected.
- (d) In-place reverse is skipped: it needs a loop or an accumulator that moves nodes out of a borrowed list. The by-value reverse is an ordinary pure function.

**Finding G1 (rule change needed): [Split]'s generalisation must be consistent under later normalisation.** In `InsertMEq` the proof splits on `b = Lt(k, v)`, whose value is the sealed `⌈Lt(σk, σv)⌉`. v1.5 generalises "every occurrence" to a fresh `σg` and splits. But the goal holds `⌈let c1 = Node(σl, σv, σr); InsertM(&c1, σk); c1⌉`, whose *re-run* derives `⌈Lt(σk, σv)⌉` again inside `InsertM`'s own body. It is not an occurrence at the time of the split, so it stays stuck, the goal never meets the IH, and `InsertMEq` is rejected. (This is the first example whose stuck point is a computed neutral inside a function's own body rather than a parameter.) The fix implemented (`Config.genConsistent`) is:
- remember each generalisation `⌈n⌉ ↦ σg`;
- whenever normalisation derives `⌈n⌉` again (a [Close] result or fill, or a stuck [Seal] run), replace it by `σg`'s current refinement;
- after refining a generalised `σg`, re-normalise every sealed program in Ω, the goal and the stored types.

It is sound: a sealed program is a closed, deterministic computation, so every derivation of it denotes the same value, and the split is case analysis on that one value (in Lean terms, `split` together with rewriting by `h : Lt k v = b`). RULES should say it: *generalising a sealed program replaces it wherever it occurs or is later derived*. The ledger row G1 shows `InsertMEq` and `SizeInsert` rejected without it. The generalise-then-split row shows the whole BST group rejected without generalisation at all.

**Also:** a call-depth bound (2000) now complements fuel. Switching [Rec] off makes a node-recursion run until fuel runs out, and the threaded environment then copies quadratically (9.7 GB).

**Timings** (compiled, median of 21 runs): all 185 declarations check in about 9 ms. Inductives take 2.6 ms, of which `SizeInsert` is 0.8 ms, `InsertMEq` 0.3 ms and `AppendMEq` 0.16 ms. **Size:** about 3,900 lines in all; `Machine.lean` is 1,480.

## 10. Rules v1.7 (D35): erasure is purely syntactic

**Implemented**, each part with a `Config` switch whose ledger row is asserted in `Registry.lean`. Regressions are in `Ochr/Examples/V17.lean` (20 assertions).

| Rule | Implementation | Switch off → flips |
|---|---|---|
| A function's class is read from its codomain *term*, top-level and local alike | `fnClass` no longer evaluates anything. A codomain that is syntactically a sort returns types. `propDecl` decides "declared sort Prop": `Id`, `Eq`, `⊤`, `∧`; a Π into one of these; a variable declared `: Prop`; a call whose head is declared `→ Prop` (a global, a parameter of Π-type, a `λ`); the tail of `let`, `;` and `match`; an ascription at `Prop`. Anything else returns data. Parameters are read from their domain terms (`declOfDom`), captured values from their constructor or declared type (`declOfVal`). | `classBySyntax`: V17.BoomL → accepted (note 1); V17.TruthG → rejected |
| A stuck block is erased exactly when its match would be | The block is erased iff **every arm is a proof**: `splitArmsThenClose` collects each arm's flag as it checks the arm, and `closeOffMatch` hands the class to the block's call (see P2 for why the block's computed type cannot be used) | `blockRule := 0` (the v1.6 call rule on the computed codomain): V17.LieB, BoomB (note 2), LieG, BoomG → accepted; TruthB, TruthG → rejected |
| `let`, `;` and `match` are erased iff they are proofs | `eval` keeps two flags, *erased* and *proof*. A call returning types is erased itself (it runs on a private copy) but does not make its context a proof, so `let T = (c := S Z; F(&c)); …` keeps the write, as clause 4 of the appendix does. This removes the appendix's deviation (b). | `seqByProof`: V17.SeqT → rejected (v1.6 discarded the write) |
| [Close]'s row is read from the declared codomain | `declKind`: syntactically `Unit`, `&T`, or anything else; a block's codomain is its match's type | `rowByDecl`: V17.RowI → accepted |

**Finding P1 (against the v1.6 checker): a closed proof of false through a proof-typed tail.**
```
LieP(n : Nat) : Id Nat (let c = Z; let h : ⊤ = refl; let T = match n { Z => (c := S Z; h) | S _ => (c := S Z; h) }; c) Z := refl
BoomP : Eq Nat (S Z) Z := LieP(Z)
```
The checker at 6e8e05bc accepts `BoomP` (checked in a scratch worktree, along with BoomL and BoomB). At the generic call, the block has type `⊤` and is erased, so `c` stays `Z`. At `n = Z` the match runs directly. The checker erased a sequence only when its tail was erased, and a place holding a proof (`h`) was not, so the write happened. RULES is right (the sequence's declared type `⊤` has sort Prop); the checker's tail reading was not. The appendix's note 3 says that reading "is stable too", which holds only if every proof-typed tail is erased. **Fix:** a place, constant, value or `λ` whose value is `⋆` is a proof. §11's P3 shows that reading the value is itself unstable. It is now a variable's declared flag (`leafRule := 2`). With the P2 block rule, `BoomP` is rejected even without P1's fix. P1 is then a completeness fix: without it (`leafRule := 0`) `LieP` is rejected, where RULES erases the write. The combined ledger row (`blockRule := 1, leafRule := 0`) shows `BoomP` accepted again.

**Finding P2 (against my first v1.7 reading): a block must not be erased by its computed type.** My first implementation erased a block when its computed type has sort Prop. That is a normal form, and it disagrees with the arms, whose calls are classed by syntax:
```
LieG(m : Nat) (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let f = (λ(x : &Nat) : V(Z) => (*x := S Z; g(0))); let T = match m { Z => f(&c) | S _ => f(&c) }; c) Z := refl
BoomG : Eq Nat (S Z) Z := LieG(Z, (λ(y : Nat) : V(Z) => refl))
```
`f`'s codomain `V(Z)` has declared type `U(Z)`, which is not syntactically `Prop`, so `f` returns data, and `f(&c)` runs on the direct path at `m = Z`. But the block's type, inferred from the arms, is the computed `V(Z) = ⊤`, of sort Prop, so the block was erased at the generic call. Result: `BoomG` accepted. **Fix:** a block is erased iff each arm, as checked by [Split], is a proof by the same syntactic judgement. So it is erased at the generic call only when it would be erased whichever arm runs at an instance. A block that is not erased is always safe, because its sealed programs re-run the arms, which decide for themselves (the appendix's argument). With this rule, `LieG` is rejected and the true statement (`c` becomes `S Z`) is proved by splitting on `m` (`TruthG`). **For RULES:** "erased exactly when the match would be" needs the match's *declared* type, i.e. its arms' declared types. §3 says a block's "result type is the match's type (… inferred from the arms)", and that inferred type is computed. Suggested wording: *a stuck block is erased exactly when each of its arms would be.* An annotation `let x : T = match …` with `T` of declared sort Prop erases the whole annotated term on both paths, since the ascription is outside the block.

**Observation: the declared row costs Unit results.** `G(x : &Nat, n : Nat) : UU(n)`, with `UU(Z) = Unit`, gets the data row even at `n = Z`. So `RowI : Id Unit (let c = *x; G(&c, Z)) ()` is no longer provable by `refl`: `⌈let c1 = σ; G(&c1, 0)⌉` is not `()`, since there is no η for Unit. It is provable by induction on `*x` (`RowIInd`). v1.6 accepted `RowI` at this instance but took the data row at the generic `n`, which is the instability D35 removes.

**Residuals.**
- `declOfVal` reads a captured value, not the captured variable's declared type *term*, which a Π-closure no longer has. The two differ only for a captured variable whose declared type becomes a sort at an instance but is not one at the generic call (`A : U(n)`). Such a variable cannot be used as a type at the generic call (`evalType` rejects it), so it cannot appear as a codomain.
- `propDecl` is incomplete. For example, a codomain `q.1` (a projection of a captured pair holding a proposition) is classed as data. Since P2 this is consistent on both paths, because blocks follow the arms. It is not the appendix's reading, where such a function returns proofs.
- The appendix (lead-owned; not edited here) is now behind in four places:
  - "Recursion requires the declared decreasing parameter to have type `Nat` or `&Nat`": since phase 2 it may have any inductive type, or be a borrow of one.
  - Note 3 and deviation (b): the tail reading is gone for types, and for proofs it now agrees with clause 4.
  - The top-level class: the appendix reads "the goal of its [Def]" (the codomain evaluated), while RULES v1.7 and the checker read the codomain term.
  - Clause 4 for a block should say "each arm" (P2).

**Timings and size.** 205 verdicts, all as expected, in about 9.5 ms (V17: 0.8 ms). A clean build takes about 22 s: each of the 23 ledger rows re-runs the suite twice in the interpreter. `Machine.lean` is 1,608 lines; the checker is about 3,180 lines and the examples 973.

## 11. Rules v1.8 (D36–D39) and the formal appendix

**Implemented**, each part with a switch and an asserted ledger row. The regressions are in `Ochr/Examples/V18.lean`: breaker-fresh-v16's block (`V18`, 23 assertions), the positivity attack (`Positivity`, 8), and a typed-generalisation check (`GenTy`, 3, plus two trace assertions).

| Rule | Implementation | Switch off → flips |
|---|---|---|
| D36: fields are first-order data | `firstOrder` in `checkInd`: declared inductive types, `Nat`, `Unit`, `×` of these | `positivity`: Positivity.Bad, L, K, bad, Boom → accepted (the appendix's closed `Eq Nat 0 1`); `Empty` and `absurd` are accepted either way |
| D37: records are global, names never reused | `restoreKeep` keeps `nextAbs`, `absTy`, `nextLoan` and the generalisation records (`neutrals`) | `globalRecords`: V18.Esc, BoomE (X3) → accepted |
| D38: a borrow result is observed through a fresh value | `convFn`: for a codomain `&T`, one shared fresh `σ_w : T` is written through the returned borrow before every borrow ends, and the result is its content | `obsBorrow`: V18.ConvPick, TY, BoomX4 (X4) → accepted |
| D39: the head guard covers neutral heads | `callFn`: a neutral-headed head call is stuck, not closed off | `headGuardNeutral`: V18.P1 (X5) → rejected (a new bound on normalisation depth turns the old stack overflow into an error, so the ledger can run it) |
| A generalised σ has the matched place's type | `generalizeNeutral` uses `placeType p` | `genPlaceType` flips no verdict. `V18.lean` asserts through the trace that a generalised `List` fill gets `List`, and got `Nat` in v1.6. |

X1 and X2 are forms of BoomL and BoomB, and D35 rejects them: `classBySyntax` flips Boom8 and Direct8, and `blockRule := 0` flips Lie7 and Boom7. Under v1.7, X2's `Lie7` is *rejected*, where breaker's comment expected acceptance "iff inline is erased too". Neither the block nor the inline match is a proof (their type `Prop` has sort `Type₀`), so the write is kept on both paths.

**Finding P3: P1's first fix was itself unstable.**
```
LieH(g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
BoomH : Eq Nat Z (S Z) := LieH((λ(y : Nat) : V(Z) => refl))
```
My v1.7 checker (bc7c6285) accepted `BoomH`:
- P1's fix called a variable a proof when its value was `⋆`.
- `g`'s codomain `V(Z)` is not declared of sort Prop, so `g(0)` is data.
- At the instance, `g(0)` runs and returns `⋆`, so `h` counted as a proof and the write was erased.
- At the generic call, `g(0)` is a sealed program, so the write was kept.

Fix: a binding carries a flag, set from syntax: a `let` from its right-hand side's flag, a parameter from `propDecl` on its declared type (`paramFlags`, the same in the body, in [Def] and in [Call-type]). A stuck block's parameter keeps the captured variable's flag. A variable is a proof iff its flag is set. Captured values are never proofs (see below). The ledger row `leafRule := 1` shows `BoomH` accepted again.

**Also changed, to agree with the appendix:**
- [T-And] now requires both conjuncts to be propositions.
- A `Π` in term position is a type former, so its captures run on a private copy. The appendix's deviation (c) is gone.
- Neither change flipped a verdict.

**Where the checker, RULES and the appendix still differ.**
1. **"Declared" or computed sort Prop (clause 4 of the appendix's erasure).** RULES P2 erases a non-call term iff "its *declared* type has sort Prop", and "declared" means read without normalising. The checker implements exactly that:
   - A `let`, `;` or `match` is a proof iff its tail is.
   - A call is a proof iff its callee returns proofs (`propDecl` on the codomain term).
   - A variable is a proof iff it is declared so.
   - A stuck block is erased iff every arm is a proof.

   The appendix's clause 4 erases "any other term whose type has sort Prop", with the type computed by the typing judgement, and [T-Erase] and [Split] use the computed type too. The two readings differ when a term's computed type has sort Prop but its declared type's sort cannot be read without normalising. Examples: `g(0)` with `g : Π(y : Nat). V(Z)`, and a parameter `(h : V(Z))`, where `V(Z) : U(Z)` computes to `⊤`. Each reading is stable on its own:
   - **The appendix:** `f`'s body `*x := S Z; g(0)` is a proof, so it is erased. `LieG` is then *true*, `TruthG` false, and `LieH` false.
   - **RULES and the checker:** the write happens. `TruthG` and `LieH` are true, `LieG` false.
   - **Mixing them is unsound:** a block read by the computed type with calls read by syntax is exactly P2's `BoomG`.

   RULES' reading needs no types in the machine: the checker's untyped machine carries one flag per variable. The appendix's reading needs erasure decisions recorded by the typing of the enclosing definition, which the appendix does say ("the machine reads that decision"). **Recommendation:** clause 4 should say "declared", with a declared type read as the checker reads it (the tail's; the callee's codomain term; a variable's declaration). Then calls, variables, sequencing forms and blocks share one judgement. If the appendix's reading is preferred instead, the checker must record erasure per occurrence at [Def]. That is a larger change, and I have not made it.
2. **Captured values have no type in either.** The appendix's $"typeof"$ has no case for `⋆` or a sealed program, and the checker's `valType` has none either. So a `λ` or `Π` that reads a captured proof or captured neutral data in a typed position cannot be checked. For example, `let n = *x` after `AddM(&*x, 1)`, followed by `λ(y : Nat) : Nat => n`, is rejected with "cannot infer the type of the value ⌈…⌉". The fix in both is to record the captured values' types when a closure or Π-closure is formed. It is not done, because it changes the value representation. The same gap is why captured values are never proofs in the checker. A body that reads one fails its typed check at formation, so the flag is never consulted.
3. **Small readings.** `J` is a proof when its motive is syntactically a function into `Prop`, or when `t` is a proof: syntactic, in line with 1. `propDecl` is incomplete for codomains such as `q.1`, which are classed as data. That is consistent on both paths.
4. **The appendix's text about the checker is out of date** everywhere it says "the checker … v1.6" or "does not yet". The checker now implements the following, all as the appendix describes them apart from 1:
   - the syntactic class, deviations (a) and (b) gone and (c) gone as above;
   - [Obs-borrow];
   - D36 in [Ind];
   - D37;
   - D39;
   - [Split-gen]'s place type;
   - [Close]'s declared row (note 9);
   - [T-And]'s premise.

**Timings and size.**
- 239 verdicts, all as expected, in about 10.5 ms. V18 takes 0.7 ms, Positivity and GenTy under 0.1 ms.
- A clean build takes about 27 s, most of it the 30 ledger rows, each of which re-runs the suite twice.

## 12. Rules v1.9 (D41): erased terms are confined, and whether that is a fail-safe

**Implemented**, with the switch `confine`.
- **The effect log.** Every assignment, borrow and move is logged by the position of its place's root (`logEffect` in `assignPlace`, `borrowPlace`, `readPlace`).
- **Settling an erased run.** When an erased occurrence ends, `settleErased` looks at each step it logged:
  - a step on a place created inside the run is local, and is dropped;
  - a step on a place of the run's start state is marked *pending*.
- **Who resolves a pending step.** An enclosing erased term in which the place is local resolves it. Any other context rejects it (`flushPending`). The contexts that reject are: a non-erased term, the tail judgement (`checkTail`), a side of `Id`, and the context of a stuck block (whose arms' pending steps are carried past the split).
- **The exception.** The borrows and moves that evaluate the arguments of an erased call are exempt (`evalCall`).
- **Type positions** are confined runs on a private copy (`confinedCopy`: `evalType`, and `J`'s endpoints).
- **Regressions:** `Ochr/Examples/V19.lean` (8):
  - a proof mutating its own locals (`Local`) and handing an outer place to another proof (`Pass`) are accepted;
  - `Write`, `Borrow` and `Move` are rejected;
  - a proof whose steps are in tail position (`TailSteps`) is accepted.
- **Four earlier tests are now type errors**, as D41 intends. Each relied on P2 silently discarding a proof's outer write: `Attacks.N1T`, `Attacks.Q`, `Probes.EffArgErased` and `V17.LieP`.
- **Nothing else changed**: E1–E6 (including `AddMZero`'s `&p` into a proof call, `LemmaMoves`, `TwoPhase` and all of E5), the inductives and the v1.5–v1.8 regressions keep their verdicts.
- **Ledger:** `confine` off flips those 4 plus `Write`, `Borrow` and `Move`.

**One reading differs from the appendix's letter.** The appendix says that "steps inside an erased subterm are judged by that subterm's own confinement", and also that "a proof may still mutate its own locals". The two conflict. In `let h : ⊤ = (let y = 0; y := 1; refl); …`, the sequence `y := 1; refl` is itself erased (a proof), and `y` is in its start state, so under the letter that write is a violation. The checker instead judges each step against the *outermost* erased term containing it: steps on places local to that term are fine. Suggested wording: *a step inside an erased occurrence is judged by the outermost erased occurrence containing it.* The fail-safe argument only needs that one: an inner misclassification whose effects stay inside a consistently erased outer term cannot desynchronise anything.

**The experiment.** The question: with D41 on, switch off each classification rule in turn. Do the erasure attacks become *rejections*? The comparison is D41 off, D41 on, and D41 on plus the extension described below (switch `confineBodies`). The script was run on the whole suite; each column lists the closed false proofs and false statements accepted.

| Rule switched off | D41 off | D41 on | D41 + extension |
|---|---|---|---|
| D28 (value-based erasure) | F1 `V15.Boom`, `BoomL`, X1 `Boom8`/`Direct8`, X2 `Lie7`, `LieB`, `LieG` | **none** (`LieG` is accepted, but `BoomG` is rejected) | none |
| `classBySyntax` (evaluated class) | `BoomL`, X1 `Boom8`/`Direct8` | `BoomL`, `Boom8`, `Direct8` | `Boom8`, `Direct8` |
| `blockRule 0` (v1.6 block rule) | `LieB`/`BoomB`, `LieG`/`BoomG`, X2 `Lie7`/`Boom7` | the same | **none** |
| `blockRule 1` (computed block type) | `LieG`/`BoomG` | the same | **none** |
| `blockRule 1` + `leafRule 0` | `LieP`/`BoomP`, `LieG`/`BoomG` | the same | **none** |
| `leafRule 1` (P3's value reading) | `BoomH` | **none** | none |
| P2 (the private copy) | `N1Closed`, `QBoom`, `EffArg`, `BoomP` | **none** | none |
| `seqByProof`, `leafRule 0` | none | none | none |

**Where D41 as written is a fail-safe:** misclassified *inline* terms, that is, sequencing forms, leaves and the private copy itself. In each case the outer write is a step of the erased run. With D41 on, the ledger rows `leafRule 0` and `leafRule 1` flip nothing. The P2 row shrinks to completeness: `TwoPhase`, `LemmaMoves` and `TypeErased` are rejected without the copy, and the four closed proofs of false it used to guard are rejected by D41 alone. The ledger asserts the rows "P1 without D41", "P3 without D41" and "P2 without D41" to keep those attacks documented.

**Where it is not: misclassified calls and blocks.** Their outer writes happen inside a callee's body, through borrows that were passed as arguments, which is exactly D41's exception. D41 relies on the callee's body having been checked confined when it was defined. But neither RULES nor the appendix confines a *body*: a function body is checked in tail position, which is not an erased occurrence (this is how `E4.TwiceMZero'` and `V19.TailSteps` stay legal). A block's arms are confined only when they are erased themselves, and under D40 that is exactly when the block is.

**The extension (`confineBodies`, off by default, not in RULES)** closes most of the gap:
- **The two checks.** The body of a function whose calls are erased is confined through its borrow parameters. A by-value parameter, a capture or a local counts as the body's own, which keeps `E6.Snapshot` legal. And every arm of an erased block is confined.
- **What it catches.** Every block attack, and `BoomL`, whose λ is formed again, and checked again, at the instance.
- **What it misses.** It cannot catch X1 (`Boom8`, `Direct8`). There, `Mk(0)` builds its closure in untyped code at the instance, so the closure is never checked again, and its evaluated class differs from the one at `Mk`'s [Def]. With `classBySyntax` on, the class is syntactic and cannot differ.
- **Closing X1 too.** D41 would have to judge the steps of an erased call's body *when it runs*, by ownership rather than by root: a write through a borrow whose loan is owned by a place of the call's start state. That is possible because calls returning types do run (on the private copy). Calls returning proofs are skipped, so they cannot be judged at run time. But their class reads a sort, and sorts are stable (§10), so it cannot differ between paths.
- **What it costs.** It rejects proofs and type-valued functions that write through their borrow parameters:
  - `E4.TwiceMZero'`, the modular proof that runs `AddM(&*x, 0)` between two lemma citations;
  - `Attacks.P2`, `FP2`, `BoomIsTrue`, `p2`, `TA2` (`P2 (x : &Nat) : ⊤ := *x := 7; refl`);
  - `Probes.F5`, `TypeErased` and `V17.F`, `SeqT` (`F (x : &Nat) : Prop := *x := S Z; ⊤`);
  - `V19.TailSteps`.

**Timings.**
- 247 verdicts in about 12.4 ms. It was 10.5 ms before this round; the effect log and V19 account for most of the difference.
- A clean build takes about 42 s, most of it the 36 ledger rows, each of which re-runs the suite twice in the interpreter.
- `Machine.lean` is 1,790 lines. The checker is about 3,410 lines and the examples about 1,150.

**Where the checker, RULES v1.9 and the appendix still differ (final; this supersedes §11's list).**
- **Resolved since §11.** The appendix's clause 4 is now the syntactic proof judgement, and the checker agrees with it. That includes `J`, which is now a proof only when its motive is syntactically a function into `Prop`; the checker no longer also counts it a proof when `t` is.
- **Differences in substance:**
  1. **Confinement of nested erased terms:** the outermost-term reading above, against the appendix's "own confinement".
  2. **Captured values have no type in either.** The appendix's `typeof` has no case for `⋆` or a sealed program, and neither does the checker's `valType`. So a closure or Π-type that reads a captured proof or captured neutral data in a typed position cannot be checked, and captured variables are never proofs in the checker.
  3. **`propDecl` is incomplete** (appendix (a); consistent on both paths).
  4. **D41's erased-call exception** is not a fail-safe for calls and blocks (the experiment above). This is a property of RULES that the appendix states the same way, not a disagreement between them.
- **Appendix sentences about the checker that are now out of date:**
  - "implements v1.7 with D40 … not yet D36–D39 or D41";
  - "does not yet implement [Obs-borrow]";
  - (b) "a Π-type in a term position captures in the real environment": it now captures on a copy;
  - "the checker gives σ the head call's declared codomain … and `Nat` otherwise": it now uses the matched place's type;
  - "requires only that field types be borrow-free … and accepts that proof", and note 3's "still accepts `Bad`": D36 is implemented;
  - "does not yet check confinement";
  - "still closes off a neutral-headed call": D39 is implemented;
  - "[T-And] … the checker omits that premise": the premise is now checked.

## 13. Not done

A proof that the implementation matches the rules (the traces and the ledger are the evidence); universe checking beyond C15; `Nat` and `Unit` as ordinary declarations (they stay builtin); indexed families (`Eq` stays primitive); loops, shared borrows, borrows in data (D8); the separate meta-lean development (`ochr/core/meta-lean/`, another agent's).

## 14. Rules v2.0 (D45–D47): the connectives are inductive definitions

### 14.1 Rescued v1.9 work (D44, captured-value types)

The previous checker agent's uncommitted work was verified (261/261, green) and committed as 3c887eb3: D44 (a Π-type or `fix` whose codomain is syntactically `&T` needs a borrow parameter; `borrowParam`, ledger row D44.Q/Boom/LeakT) and captured values that keep their types (`capTypes`: a captured sealed program is typed by running its term on a private copy; a read of a captured proof is inlined as `(⋆ : T)`). One fix on top (2071ac58): capture decided "a captured proof" by the value `⋆`, the reading finding P3 removed; it now uses the binding's declared flag. The examples moved to `Examples/D44.lean` (program `D44`), and the asserted ledger rows to `Examples/Ledger.lean`.

### 14.2 What changed in the checker

- **No primitive connectives.** `Term.top/and/andI/refl` and `Value.tTop/tAnd` are deleted. `Check.prelude` declares `inductive False : Prop`, `inductive True : Prop := I`, `inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)`, checked by the same `checkInd` as user declarations; every program starts from it. `⊤`, `P ∧ Q`, `⟨h, k⟩`, `refl` are resolved to `True`, `And(P, Q)`, `Intro(h, k)`, `I` (`Surface.lean`), and printed back as notation. No internal alias remains. The `Eq` rules still name the library's `True`, `False` and `And` (`mkEqM`, `mkAnd`), as RULES §4 does. `Nat` and `Unit` stay builtin, as before.
- **`D(ā)`.** `Term.tind n args`, `Value.tInd n args`. A declaration stores its parameters (a telescope of type terms), its sort and its field types as *terms* in the scope of the parameters; `fieldTypes` instantiates them. Runtime values do not carry parameters, and neither does a constructor term (`C(t̄)`, as in RULES §1).
- **Field places know their constructor** (`Place.field` carries a `FieldRef`: type, constructor, index). A proof's field is typed without inspecting its content (`⋆`), and reading a field of a value built by another constructor or type is an error.

| Rule | Implementation | Switch → ledger row |
|---|---|---|
| D42 for constructors: a `Prop` inductive's constructor application is a proof, `⋆`, erased | `ctorIsProof` (flags), `evalCtor` | `propValues`: OrComm, SqTrue, EffL, EffLNoop rejected (completeness) |
| D45 by type | `byTypeMatch` (syntactic), `evalMatchByType`, `checkTail`'s by-type branch; `⋆`'s fields are `⋆` (`stepV`) | `byType`: 20 completeness losses (Logic, ByType, OrAttack) |
| D45 subsingleton elimination | `largeElim`, `fieldTermIsProp`; the check is on the arms' declared proof flags | `subsingleton`: OrAttack.IsL, Irr, OrLie, Get, SqIrr accepted (no closed False: finding F1) |
| D45 + D42 both off | | adds OrAttack.Boom : False and SqBoom : False (the closed proofs) |
| D46 parameters | `evalTInd`, `evalCtor` (`unifyParams`, the `hint` argument of `eval`), `fieldTypes`, `ctorRefinement`, `scrutType` | no switch (a representation) |
| D47 disjointness | `mkEqM`, `distinctCtors` | `disjoint`: E6.NotAdd01 and six Logic tests rejected |
| D36 with parameters | `firstOrderTerm` on field type terms | `positivity` gains PosParam.Bad, L, K, bad, Boom, Neg |
| scrutinee typing (finding F3) | `scrutType` reads the place's type | `scrutTyped`: Scrut.f, Scrut.g accepted |

Existing rows only gain entries from the new programs: D27 off loses the by-type tests (a proof parameter is `σ`, whose fields do not exist); D28 off and P3's value reading (`leafRule 1`) accept Get/SqIrr (a `⋆` read from Sq's data field passes as a proof by its value), so the subsingleton check depends on the declared proof judgement; P1's `leafRule 0` rejects OrLet; D41 off and its combinations accept EffInline. Every v1.9 verdict is unchanged, and so is every v1.9 ledger entry.

### 14.3 Readings where RULES v2.0 left a choice

All decisions are read from syntax and declarations, never from normal forms, so both evaluation paths make them the same way.

- **R1. When a match is by type.** When the arms' constructors (resolved by name: names are now unique per program) belong to a `Prop` inductive, or there are no arms. The scrutinee's type is still *checked* to be `D(ā)`; that is typing, not an erasure decision.
- **R2. Several constructors (`Or`).** §8 says what happens with zero and one. Implemented: every arm is checked with its fields as `⋆` places and no refinement, every arm must be a proof, and the match is a proof, `⋆`, erased. An untyped run does not run it (it cannot pick an arm); it runs one arm on a discarded copy to read its proof flag.
- **R3. "A result whose type is not a proposition"** is read as "an arm that is not a proof by the declared judgement" (D42's flags), the reading consistent with D28/D35/D42. The computed-type reading would disagree across paths; the ledger's D28 and P3 rows show the value reading letting `Get` through.
- **R4. No arms.** Any inductive with no constructors (`False`, or a data `Void`). The match is erased (vacuously a proof), its value is `⋆`; outside tail position it needs an annotation; in tail position it has no paths.
- **R5. Parameters.** Inferred from the fields' types, else from a *hint*: the type the context requires (an ascription or `let x : T`, the goal at a tail, a parameter type at a call argument, a field type in an enclosing constructor, `Id`'s type). A hint only chooses parameters no field fixes, and the result is checked in context, so it cannot make anything typecheck that should not. `D(ā)`'s arguments are type positions (confined private copies), checked against the parameter telescope; a parameter may not be a borrow type (`List(&Nat)`, no borrows in data); universes are not cumulative (`Box(Eq Nat 0 1)` is rejected).
- **R6. Proof fields in data** (`Sig(P) := MkSig(n : Nat, h : P)`): a field declared of a proposition (a parameter declared `: Prop`, or a `Prop` inductive) is a proof by declaration (`leafProof`), [Split] gives it `⋆`, and a stuck block that captures it keeps the flag.
- **R7. [Close] rows, footprints, stuck-block captures.** Unchanged. A codomain `D(ā)` takes the data row; a codomain that is a `Prop` inductive makes the function return proofs (erased, never closed off). A by-type match is never stuck, so it is never closed off as a block.

### 14.4 Tests (`Ochr/Examples/Logic.lean`, 104 assertions; existing examples restated)

| Program | What it checks |
|---|---|
| `Logic` (26) | ex falso (`absurd(h : False) : Nat := match h {}`, into any `P`, into an effect-sensitive `Id`, annotated in a `let`); `False` is empty (four closed attempts rejected); no arms need a type with no constructors; D47 (`Eq Nat Z (S Z) ≡ False`, with an abstract predecessor, at a user `Bool`, and for `Id Unit (*x := 0) (*x := 1)`); no injectivity (`Inj` rejected); the notation is the library; large elimination from `True` |
| `ByType` (19) | `Swap`/`Fst` on `And`; `Two` (data from a proof) and `WriteIf` (a data function that matches a proof, then writes); the two-path tests `WriteIfAt`/`TwoAt` instantiate lemmas checked at `h = ⋆` with propositions about a mutated place, and their false instances `WriteIfAtLie`/`TwoAtLie` are rejected; a by-type match outside tail position; `Id` over two owners taken apart as the library's `And` (`SplitId`); `AndTrue` (finding F2) |
| `OrAttack` (20) | `Or` into `Prop` accepted; `IsL` rejected, so `Irr` and the closed `Boom : False` are; `OrLie`; the one-constructor variant `Sq` with a `Nat` field; `EffL` (finding F4) |
| `PList` (15) | `inductive List (A : Type)`; in-place `AppendM` and `AppendMNil` by bare recursion; `AppendMOne` rejected; the pure `AppendNil` from the in-place lemma; instances at `List(Nat)` and `List(List(Nat))`; parameter inference and its errors; `List(&Nat)` rejected |
| `PosParam` (16) | D36 through a parameter (`Mk(f : Box(Π(x : Bad). Void))` rejected; without D36 its closed `False` goes through); a `Π` field of a parameterised type rejected; nested (`Rose(A)` with `List(Rose(A))`) and proof fields (`Sig(P)`) accepted; `Box(Eq Nat 0 1)` rejected (non-cumulative) |
| `Scrut` (7) | finding F3; unique constructor names |

Existing examples: E5's `Le` has `False` as its base case; E6's `NotAdd01` and `SnapshotLie`, most `Attacks` targets and `Positivity`'s are restated as `False`; `TA2Z` and `Boom'` keep `Eq Nat 0 1` (convertible with `False` by D47), as do the v1.5–v1.8 regressions. `Inductives`' `Bool` constructors are renamed `ff | tt`. No verdict changed.

### 14.5 Findings

**F1. In this machine D42, not the subsingleton restriction, blocks the `Or` attack's closed `False`.**
```
inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => tt | Inr(q) => ff }
def Irr (h : Or(True, True)) (k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
def Boom : False := Irr(Inl(refl), Inr(refl))
```
With D45's restriction switched off, `IsL` and `Irr` are accepted (at the generic call `h = k = ⋆`, so both sides are the stuck `⌈IsL(⋆)⌉`), but `Boom` is still rejected: `Inl(refl)` is a proof, so its value is `⋆`, and `Irr(Inl(refl), Inr(refl))` has type `Eq Bool ⌈IsL(⋆)⌉ ⌈IsL(⋆)⌉ ≡ True`. No match can see which constructor built a proof. `Boom` (and the `Sq` variant `SqBoom`) is accepted only when constructor applications of `Prop` inductives also keep their constructor (`propValues` off). What D45 is still needed for:
- **the model:** `IsL` and `Get(h : Sq) : Nat := match h { Mk(n) => n }` have no interpretation once proofs are irrelevant, and `OrLie : Eq Bool (IsL(Inl(refl))) (IsL(Inr(refl))) := refl`, accepted without D45, reads `Eq Bool tt ff` in the model;
- **canonicity and adequacy:** `IsL(Inl(refl))` is a closed `Bool` that is stuck forever, and `Get(Mk(0))` returns `⋆` as a `Nat`;
- **making D45's by-type rule total:** with two constructors there is no arm to pick, and only "every arm is a proof" makes the match's value `⋆`.

For the paper: subsingleton elimination is a requirement of the model and of canonicity. The machine's own consistency comes from D42. The ledger has both rows.

**F2. `And(True, P) ≡ P`, implemented as normalisation, hides an `And` from a match.**
```
def AndTrue (P : Prop) (h : ⊤ ∧ P) : P := match h { Intro(a, b) => b }     -- rejected
```
`h`'s stored type is the normal form `P`, so the by-type match has no `And(ā)` to read its field types from. Since `mkAnd` has done this since v1.x, `⊤ ∧ P` and `P` are the same value and the lost information cannot be recovered. Options: implement the unit laws as a conversion rule (`conv` identifies `And(True, P)` with `P`; stored types keep the `And`), or accept it (match on the conjunct directly). Matching on `Id` over two owners works when no conjunct is `True` (`SplitId`). **For RULES §4:** say whether the unit laws are normalisation or conversion.

**F3. v1.9 checker bug: a match's scrutinee type was assumed from its arms.** Reproduced against 2071ac58:
```
inductive L := LNil | LCons(h : Nat, t : L)
def T (n : Nat) : Type := match n { Z => L | S _ => Nat }
def f (n : Nat) (x : T(n)) : Nat := match x { LNil => 0 | LCons(h, t) => 0 }
def g (x : Nat) : Nat := f(1, x)
```
Both `f` and `g` were accepted. [Split] refined the abstract `x : ⌈T(σ)⌉` with `L`'s constructors, and `g`'s generic call closed `f(1, σ)` off, so at run time `g(5)` runs `L`'s arms on the number 5. This is a type-safety hole, not a closed `False`. RULES is right (the match typing rule needs the scrutinee's type to be `D`); the checker had never checked it for data. It is now read by `scrutType`, which v2.0 needs anyway for the parameters. Constructor names are also required to be unique: the resolver picks the first declaration with a name. Switch `scrutTyped`.

**F4. A by-type match that cannot pick an arm is erased wherever it runs: `EffL`.**
```
def EffL (x : &Nat) (h : Or(⊤, ⊤)) : V(Z) := match h { Inl(p) => (*x := 1; refl) | Inr(q) => (*x := 2; refl) }
```
`V(Z)` computes to `⊤` but is not declared of sort `Prop`, so `EffL`'s calls run its body. The body is a proof, so each run erases it: `EffLNoop` (a call writes nothing) is accepted and `EffLOne` rejected. The typed check of `EffL` runs each arm's write in tail position, which is §12's tail-position gap of D41; outside tail position `EffInline` is rejected by D41. No claim depends on the typed run's effects: a goal is a snapshot formed before the body. But an effect that depends on the constructor (1 or 2) is exactly what subsingleton elimination forbids for results. So if the tail-position gap were ever closed by *running* erased tails rather than confining them, D45 would have to cover effects as well as results. With the machine as it is, erasing is what keeps it consistent.

**F5. Disjointness is head-only.** Without injectivity, `Eq Nat 7 8` stays irreducible (`WriteIfAtLie`'s goal): empty in the model, not `False` by conversion. That is D47 as decided.

**No closed proof of `False` found against v2.0.** Checked: the `Or` and `Sq` attacks; D36 through a parameter; borrows through a parameter; non-cumulativity at a parameter; ex falso never reaching a closed term; and the by-type decision on both paths (`WriteIfAt`, `TwoAt`).

### 14.6 Timings and size

- 364 verdicts, all as expected, in about 16 ms (compiled, median of 21 runs; it was 12.4 ms at v1.9 with 247). The v2.0 programs take about 3 ms, mostly `ByType` (1.3 ms) and `PList` (0.9 ms).
- A clean build takes about 35 s. `lake exe tests` takes about 38 s, including compilation.
- `Machine.lean` is 2,096 lines (1,823 before). The checker is about 3,860 lines and the examples about 1,460.

## 15. reviewer-3 (D48–D50) and the ledger's classes

**Probes.** The reviewer's S1–S10 now give the following. S1's `Q(g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)` is rejected by D44, and so is its v2.0 form `QF … : False := PF(g(5), refl)`, where `PF(x : &Nat, e : Id Unit (*x := 0) (*x := 1)) : False := e` holds by D47 (the rescued v1.9 work; the reviewer ran d7e0be31, before it). S2/S8's impredicative `Type₀` is rejected, and so are S10's `&Prop` and S7's `F`/`G` (D48 (1), (2)). S3's and S9's programs are accepted (D48 (3)). S6's `h.1` stays rejected: there is no projection from a proof, and ∧-elimination is a `match` on `And` (`AndElim`). S5's `LetZ` is rejected correctly: its `Id` borrows `x`, so `x` is in the footprint and the write is observed; `let z = …; (refl : Id Nat z 2)` is accepted.

| Item | Implementation | Switch → row class |
|---|---|---|
| D48 (1) `&A` only for data | `isDataType` when `&A` is formed: `Nat`, `Unit`, `×` of data, an inductive in `Type₀` at any parameters. A neutral type or a type variable is not known to be data, so the generic path rejects (fail-safe). | `refData`, model: `Impred`, `PolyId`, `SelfApp`, `SelfAppEq` (System U⁻ inside the rules), `PIref`, `RefTrue`, `RefFun`, `SwapT` |
| D48 (2) `&` only at the top | `Term.refsOk`/`refTopOk` over the whole definition in `checkDef`: a parameter's domain, a declared result, an annotation, a Π's parts | `refTop`, soundness: `D48.G` (reads `⊥` at `n = 0`) |
| D48 (3) Π under binders | `convPi`: the binders get shared fresh generic values (an owned place behind a borrow, `⋆` for a proof); domains and codomains are compared by normal form. Captures and code are no longer compared; they remain a fast path. | `piUnder`, completeness: S3's `Cap`, `P1`, `P3`, S9's `PassZeroAdd`, `PassA` |
| D49 (1) | already so (`scrutType`); `SubM`'s `Z => match h {}` with `h : Le(S q, Z) ≡ False` is accepted; a neutral type is an error (`Neutral`) | — |
| D49 (2) | an untyped run of a non-subsingleton match is `⋆`, decided from the declaration (replaces §14's probe of one arm) | — |
| D49 (3) | `bindDataFields`: a data field of a matched proof is a fresh abstract value, bound by a `let` that replaces the field's place in the arm | `proofDataFields`, completeness: `SqSplit` |
| D49 (4) | `Term.ctor`/`Value.ind` carry parameters; surface `C[ā](t̄)` (core `C(ā; t̄)`); inferred parameters are recorded when typed; `==` ignores them | — (a representation) |
| D50 | the unit laws in `conv` (`unitTop`); `mkEqM` still builds the single equation; stored types keep `And(True, P)` | `unitNorm` (on), completeness: `AndTrue` |
| ∧-elimination | `match h { Intro(l, r) => … }` on `Id` over two and three owners (`AndElim`) | — |

**What D48 costs.** There is no generic borrow `&A` for a type variable `A : Type` (`SwapT` is rejected), because `A` may be instantiated at `Prop` or at a Π-type. A `Data` kind (`Type₀` restricted to data types) would bring it back. Borrows of data holding propositions (`&Box(Prop)`) stay legal: quantifying over `Prop` in `Type₀` is predicative.

**What D49 (4) does not do.** The checker has no elaborator, and the resolver has no types. So an omitted parameter that no field determines (`Nil`'s `A`) is known only when the constructor is evaluated in checked code, from a hint. A value built by an untyped run from `Nil` does not record `A`, and its `typeof` is unknown unless the parameter was written (`Nil[A]`). Conversion ignores recorded parameters (a type determines them), so typed-built and untyped-built values agree.

**The ledger's classes** (`Registry.rowClass`, checked in `Ledger.lean` together with each row, printed by `lake exe tests`):

| Class | Rows |
|---|---|
| soundness (closed false proof, or an accepted program that goes wrong when run; witness in brackets) | P2 without D41 [N1Closed, QBoom, BoomP], D18 [ClosedD18, BadR], D17 [KnotLBoom], D19 [BadA1], L1 [KnotBoom], L2 [Dead], C5 [MovedByBlock], L3 [KnotLBoom], D29 [V15.Main], D30 [Boom3], D31 [Boom4], D32 [Boom5], D35 class [BoomL, Boom8], D35/D40 block [BoomB, BoomG, Boom7], D40 [BoomG], P3 without D41 [BoomH], P1 + computed block type [BoomP, BoomG], D36 [Positivity.Boom, PosParam.Boom], D37 [BoomE], D38 [BoomX4], D45 + D42 [OrAttack.Boom, SqBoom], scrutinee type [Scrut.g], D48 (2) [D48.G] |
| false lemma | D28 [LieG; its closed instance BoomG is caught by D41 since v1.9] |
| model | D44 [Boom: refutes a type Rust inhabits], D45 alone [IsL, Get], D48 (1) [Impred, SelfApp] |
| policy | D35's [Close] row [RowI, a true statement: stability, no witness], D41 and P1 without D41 [programs true under P2, which D41 forbids] |
| completeness | P2, C8, D27, G1, D35 sequencing, P1, P3, D39, captured types, D45 by type, D42, D47, D48 (3), D49 (3), D50, the confineBodies extension |

- **No row flips nothing.** The reviewer's P1 and P3, which were empty at 247 verdicts, now flip completeness tests (captured proofs, `OrLet`). Their soundness witnesses appear only with D41 off.
- **D41 backs up three rules.** The witnesses of P2 (the private copy: N1Closed, QBoom, BoomP) and of P3 (BoomH) appear only with D41 off as well. P1 without D41 flips only programs D41 forbids by policy; its original witness, BoomP, also needs the computed-type block rule.
- **D28's closed witness (V15.Boom) is now rejected by D41** even with D28 off, so D28 is a *false lemma* row.
- **Rows whose witness is an open program that goes wrong when run** (adequacy, not a closed proof): D19, L2, C5, D29, the scrutinee type, and D48 (2).

**Timings.** 427 verdicts in about 18 ms. A clean build takes about 40 s: 46 ledger rows, each re-running the suite twice in the interpreter, with each row's class checked in the same guard. `Machine.lean` is 2,210 lines, the checker about 4,050, and the examples about 1,690.

## 16. Every program the paper prints, and its test

Checked against the paper at a0bca0fe (body sections and appendix). An "=" means the same program up to surface syntax:
- the checker's examples use a multi-line layout with parenthesised bodies;
- a `λ` in the bound position of a `let`, or a `Π` as a result type, needs parentheses;
- `Type₀` is written `Type`.

The body's programs were also run verbatim, one-line layout and subscripts included, and each gave the verdict in this table. 467 verdicts since the merge with the recCands fix, all as expected.

| Paper location | Program | Test | Verdict |
|---|---|---|---|
| §1, §2 | `AddM`, `AddMZero` | Std.AddM, Std.AddMZero | accepted |
| §2 | `Add` | Std.Add | accepted |
| §2 | `Id Nat (Add(2, 3)) 5` by `refl` | Numbers.Add23 | accepted |
| §2.2 (5a3e47c9) | `{ x ↦ loan₀ } ⊢ AddM(borrow₀ σ, 0) ⟶ { x ↦ ⌈let c = σ; AddM(&c, 0); c⌉ } ⊢ ⌈let c = σ; AddM(&c, 0)⌉` | the fill: Std.AddMZero's traced goal is `Eq Nat ⌈let c1 = σ0; AddM(&c1, 0); c1⌉ σ0`. The result: ClosingOff.StuckResult (a stuck call's result is its sealed program, built from argument values; with D59 off it is `()`), and the rejection of `P(()) ⊢ P(let c = *x; AddM(&c, 0))` prints it: "the goal is ⌈σ2(⌈let c1 = σ0; AddM(&c1, 0)⌉)⌉" (Scratch/D59ConvGap.lean) | accepted |
| §2.3 (5a3e47c9) | `⟦AddM(x, 0)⟧ = (⌈…⌉, N(σ))`; `Id Unit (AddM(x, 0)) () ≡ Eq Unit ⌈…⌉ () ∧ Eq Nat N(σ) σ ≡ Eq Nat N(σ) σ` | Equality.IdIsConjSealed (the Unit conjunct's left side written `let c = *x; AddM(&c, 0)`), IdIsConj (`Eq Unit () ()`, equal by η), IdIsEq, EqIsId (`N(σ)` is `Add(*x, 0)`); IdIsWrong | accepted ×4; rejected |
| §2 | the `S` arm's goal `Eq Nat N(S σ') (S σ') ≡ Eq Nat (S N(σ')) (S σ') ≡ Eq Nat N(σ') σ'` | Recursion.SuccGoal, InjStep | accepted |
| §2.4 (5a3e47c9) | the recursive call at the call site: `⟦AddM(x', 0)⟧ = (⌈…⌉, S N(σ'))`, `AddMZero(&p) : Eq Nat (S N(σ')) (S σ') ≡ Eq Nat N(σ') σ'` | Recursion.CallSite; CallSiteWrong; the trace line `[Call-type] AddMZero(borrow_4 σ1) : Eq Nat ⌈let c1 = σ1; AddM(&c1, 0); c1⌉ σ1` (the normal form, the Unit conjunct gone) | accepted; rejected |
| §2 | `AddZero(x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)` | Numbers.AddZero' (Numbers.AddZero is the older proof by a match) | accepted |
| §2 | `TailM`, `AddM'` | Std.TailM, ReturnedBorrows.AddM' | accepted |
| §2 | `AddMEq`, `AddMEqOwned` | ReturnedBorrows.AddMEq, AddMEqOwned | accepted |
| §2 | `Le`, `SubM` (`Z => match h {}`), `LeAdd`, `AddSub` | CurrentState.Le, SubM, LeAdd, AddSub | accepted |
| §2 | `…; *x := Z; SubM(x, old, LeAdd(old, y))` | CurrentState.AddSubStale | rejected |
| §2 | `InsertM`; `Insert(t, k) := InsertM(&t, k); t` | InPlaceTrees.InsertM, Insert (the paper's text and layout); InsertMIsInsert (in-place is pure, by `refl`) | accepted |
| §2 | `SizeInsert` with its three `J` steps; `Size(Node(l, v, r)) = S(Add(Size(l), Size(r)))` | InPlaceTrees.SizeInsert (verbatim), Size; SizeInsertTwo | accepted; rejected |
| §2 | `AddS : x + S y = S (x + y)`, in place by bare recursion, transferred by lending | InPlaceTrees.AddMS, AddS | accepted |
| §2 (proposed) | `SizeInsert` with D60's `rewrite`: `true => rewrite SizeInsert(l, k) in refl`, `false => rewrite SizeInsert(r, k) in rewrite AddS(Size(l), Size(r)) in refl` | InPlaceTrees.SizeInsertRw (the recursive calls name `SizeInsertRw`); control SizeInsertRwNoLemma (no `AddS`) | accepted; rejected |
| §2 | `AddToOne(b, x₁, x₂, y) := let r = match b { Z => x₁, S _ => x₂ }; AddM(r, y)` | ClosingOff.AddToOne | accepted |
| §3 | `Nat`, `Unit` (built in), `False`, `True`, `Pair`, `And` | Prelude (checked by `checkInd`) | accepted |
| §3, §5 | `match h {}`; `match h { Intro(l, r) => … }` on a multi-place `Id` | Propositions.absurd…; Propositions.TwoOwners, TwoOwnersR, ThreeOwners | accepted |
| §4 | `N(S σ') = S N(σ')` | Recursion.SuccGoal | accepted |
| §5 | owned locals are observed: `x := 6` vs `()` | Equality.OwnedLocal / OwnedLocalNeq | rejected / accepted |
| §5 | `Id Unit (*x := 0) (*x := 1)` is `False`, eliminated by `match e {}` | Equality.WriteNeq, WriteDisj | accepted |
| §6 | `let z = (let y = &x; *y := 2; x)`, then `Id Nat z 2` by `refl` | Borrows.LetZ | accepted |
| §6 | `λ(x : &Nat). (*x := 5; refl)` is not a `Π(x : &Nat). Id Nat (*x) 5` | Snapshots.LamWrite | rejected |
| §6, note 10 | `Or`; `IsL`, `Irr`, `Boom` | Subsingletons.Or; IsL, Irr, Boom | accepted; rejected ×3 |
| Fig. 7 | Π-types capture values | Snapshots.Oops2 | rejected |
| Fig. 7 | recursion on entry values; `f` as a value; `f` without `by` | Recursion.Loop, Bot'; Knot, KnotBoom; LoopNoBy, LoopNoByBoom | rejected |
| Fig. 7 | `λx. ⋆` vs `λx. (*x := 7; ⋆)`; proof blocks inline vs closed off | Erasure.Boom; N1T/N1Closed, Q/QBoom | rejected |
| Fig. 7 | `W(&c, n) : U(n)`; local function; type-valued match; non-cumulativity | ErasureBySyntax.Boom, BoomL, BoomB; Universes.NonCumul, PositivityParams.PropBox | rejected |
| Fig. 7 | functions by observation; borrow results | Functions.Boom3; ConvPick, TY, BoomX4 | rejected |
| Fig. 7 | pattern variables are places | ClosingOff.Clear, Boom5 | rejected |
| Fig. 7 | all owners observed | Owners.BadD18, ClosedD18, GR, BadR | rejected |
| Fig. 7 | exclusive access; matches end loans in neutral heads | Borrows.BadA1; ReturnedBorrows.Bad, Main | rejected |
| Fig. 7, note 5 | generalisations global: `Box`, `Double`, `Esc`, `Bad5` | GlobalRecords.* (constructor `MkBox`, see gaps) | accepted ×2, rejected ×2 |
| Fig. 7, note 11 | `Impred`, `PolyId`, `SelfApp`; `F`, `G`; `SwapT` | Universes.Impred, PolyId, SelfApp; BorrowTypes.F, G, UseG, SwapT | rejected |
| Fig. 7, note 7 | `PF`, `QF` | ReturnedBorrows.PF / QF | accepted / rejected |
| Fig. 7, note 4 | `inductive Bad := Mk(…)`, `L`, `Bad4` | PositivityPaper.Bad, L, Bad4 (constructor `MkBad`, see gaps) | rejected |
| §7 | `Pick`; `let r = Pick(n, &a, &b); let z = b; match n { … }` | Fixtures.Pick; Naturality.PickEarly / PickEarly0, PickEarly1 | rejected / accepted |
| §8 | the `ochr Numbers { … }` excerpt | Std.AddM, Std.AddMZero, Numbers.WriteThenRefl | accepted, accepted, rejected |
| §9 | every `Π(x : &Nat). &Nat` has an injective backward function | ReturnedBorrows.L, Inj | accepted |
| §9 | `IterM : &(List Nat) → List (&Nat)`; no generic in-place swap | BorrowTypes.IterM; SwapT | rejected |
| §9 | `⌈let c = σ; AddM(&c, 0); c⌉` is `Add(x, 0)` | Equality.IdIsEq | accepted |
| note 1 | `U`, `V`, `LieL`, `BoomL` | ErasureBySyntax.U, V, LieL, BoomL (Fixtures.U, V) | accepted ×3, rejected |
| note 2 | `LieB`, `BoomB`; the `g`/`f` block | ErasureBySyntax.LieB, BoomB; LieG, BoomG | rejected |
| note 3 | `LieH`, `BoomH` | ErasureBySyntax.LieH, BoomH | accepted, rejected |
| note 6 | `PickX`, `PickY`, transport | Functions.PickX, PickY, ConvPick, TX, TY, BoomX4 | accepted ×2, rejected, accepted, rejected ×2 |
| App. note on [Close]'s row (5a3e47c9) | with η for `Unit`, `Id Unit (let c = *x; G(&c, Z)) ()` holds by `refl` (it needed induction before D59) | ClosingOff.RowI / RowIInd; the D59 ledger row flips RowI | accepted / accepted |
| App. conversion (5a3e47c9) | "no η rule, except that `eq` identifies any two values of `Unit` and [Conv-fun] any two results at a codomain written `Unit` … an abstract `σ : Unit` is still not convertible with `()`"; "no η rule other than for `Unit`" | ClosingOff.UnitEta, UnitEtaUU (`eq` goes by the evaluated type), ConvUnitRes; UnitNotConv, ConvUnitWritten (codomain `UU(Z)`, not written `Unit`) | accepted ×3; rejected ×2 |
| note 25 | `SubM`'s `match h {}` by the stored type; a neutral type rejected | CurrentState.SubM; Neutral | accepted; rejected |
| note 26 | injectivity and disjointness | Equality.Inj, InjWrong, PairInj, NoConf… | as asserted |
| note 27 | `let n = *x` after `AddM(&*x, 1)`, then `λ(y : Nat) : Nat => n` | Snapshots.CapS | accepted |
| App. A [T-Ref] | `&Box(Prop)` | BorrowTypes.RefBoxProp | accepted |
| App. D [Conv-fun] | the two stuck closures are not convertible | Functions.CoInd | rejected |
| §8.2 (0652e4bc) | `QSCorrect(n, s, q) : (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧ (let old = *s; Eq Nat (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩` | Quicksort.QSCorrect. The printed text, with `def` and curried binders put back, is token-for-token the test once the test's outer parentheses are dropped (120 tokens each), and the transliteration checks on its own | accepted |
| §8.2 | the untouched rest, by definition: the view after `WithSplit` is `JoinS(E, n, k, (let c = TakeS(E, n, k, *s, h); g(&c); c), DropS(E, n, k, *s))`, by `refl` | ArrayBench.B1Join | accepted |
| §8.2 | about the rest alone, one lemma (dropping `k` elements from a join) | ArrayBench.B1 (by DropJoin); B1Refl (by `refl`: what a built-in array would give) | accepted; rejected |
| §8.2 | `Cells(E, n)`, `Slice(E, n)`, `Array(E, n)`; the eight functions primitive at runtime (the view of an array, `Read`, `Set`, `GetMut`, `WithSplit`, the empty array, push, pop); `l : &Slice(E, k)`, `r : &Slice(E, Sub(n, k))` | Arrays.Cells, Slice, Array; AsSlice, Read, Set, GetMut, WithSplit, ArrEmpty, ArrPush, ArrPop; `WithSplit`'s continuation parameters | accepted |
| §8.2 (b62282c9) | `InsertFindOther(hm : &HashMap, k, v, k2 : Nat, h : Eq Bool (EqB(k, k2)) false) : Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2)) (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) := match *hm { HM(n, len, slots) => split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }` | HashMapLookup.InsertFindOther (17HashMap.lean:563). The printed text, with `def` and curried binders put back, is token-for-token the test, apart from the test's optional trailing comma after the one arm, and it checks on its own | accepted |
| §8.2 | "`Find(m, k)` is `Get(&m, k)`, the in-place lookup run on a copy" | HashMap.Find, defined as exactly that (17HashMap.lean:255) | accepted |
| App. [T-Split-goal] | `split f in t`, `split f { C₁ => t₁, … }` | Splitting.PickNotZero, PickNotZeroCopy, Pick22NotZero (a link that an earlier split generalised), PickTwo, DoubleVal (arms bind fields); rejected: PickNotZeroNoSplit, NothingToSplit, WrongHead, WrongArm, WrongCtors, SplitLie, NotTail; HashMapLookup.InsertFind, InsertFindOther, with InsertFindNoSplit rejected | as asserted |

**Printed programs that failed as printed** (fixed in the paper since, 2223fd4f: note 4 and Fig. 7 now print `MkBad`, note 5 `MkBox`, matching the tests; and a0f40123 prints `SizeInsert` with `rewrite`, exactly InPlaceTrees.SizeInsertRw):
- **Note 4 and Fig. 7 (strict positivity).** They print `inductive Bad : Type₀ := Mk(f : Π(x : Bad). False)`, with `L(b : Bad) : False := match b { Mk(f) => f(b) }` and `Bad4 : False := L(Mk(λ(x : Bad) : False => L(x)))`. Since D52, `Mk` is `Pair`'s constructor in the Prelude, so the block is an error before positivity is reached: "N4 declares Mk, which Prelude (used by N4) already declares", and per declaration "Bad: the constructor name Mk is already used"; `L`'s pattern and `Bad4`'s application are then read as `Pair`'s `Mk` ("pattern Mk needs 2 variables"). Corrected text: `inductive Bad : Type₀ := MkBad(f : Π(x : Bad). False)`, with `match b { MkBad(f) => f(b) }` and `L(MkBad(λ(x : Bad) : False => L(x)))`, as PositivityPaper tests.
- **Note 5.** It prints `inductive Box := Mk(x : Nat)` and `Esc(… m : Box) … match m { Mk(x) => … }`, `Bad5 : Eq Nat 1 0 := Esc(1, Mk(0))`: the same clash, so `Box`, `Esc` and `Bad5` are rejected for the name, not for what the note explains. Corrected text: `MkBox` for `Mk` throughout, as GlobalRecords tests.

**Gaps, not closed by a test:**
- **[T-Split-goal]'s rule line (b62282c9) is looser than the checker and RULES D61.** It says "n is the first sealed program, among the goal's in order, each followed down the chain of neutrals its run is stuck on, whose head call is a call of f", which can be read as including the goal's own sealed programs. The checker, like D61 ("take the first link") and the rule's own prose ("a result … on which the goal's sealed programs are stuck"), considers only the links: the neutrals the runs are stuck on. So `split IsZ { false => match h {}, true => refl }` against the goal `Eq Bool (IsZ(n)) true`, whose one sealed program `⌈IsZ(σ)⌉` is headed by `IsZ` but stuck only on `σ`, is rejected ("the goal … is not stuck on the result of a call of IsZ"). The inclusive reading would accept it. The rule line also omits D61's second kind of link, an abstract value that a sibling arm's split already generalised (Pick22NotZero needs it). Suggested wording: "n is the first link, in pre-order over the goal's sealed programs, of the chain of neutrals each one's run is stuck on (a sealed program, or an abstract value a recorded generalisation stands for), whose head call is a call of f".
- §4's `(λy. (x := 2; y))(x := 1)` illustrates why rewriting is not confluent. It is not an Ochr program: the `λ` is untyped, and an Ochr closure copies `x`.
- Note 1 prints `let h = λ(x : &Nat) : U(n) => (…); …`. The checker's surface needs `let h = (λ(x : &Nat) : U(n) => (…)); …`, with the same verdict once parenthesised.
- The `J` note describes D56 (`J` stuck unless its endpoints are convertible; the casts between `Nat → Nat` and `(Nat → Nat) → Nat`, and of `5` to `Bool`), and note 25 describes D58 (a zero-arm match is stuck outside proofs). Neither prints a program, and neither rule is in this checker branch yet (task #13), so there is no test.
- **D59 is not only a gain in completeness.** Its ledger row is classed completeness (switching it off only rejects good programs), which holds of the suite. But conversion has no η for `Unit` (as the appendix says), and a stuck `Unit` call's result used to be `()` and is now a sealed program, so true statements that compare such a result by conversion are rejected with D59 and were accepted without it: `P(()) ⊢ P(let c = *x; AddM(&c, 0))`, `P(let c = *x; AddM(&c, 0)) ⊢ P(let c = *x; AddM(&c, 1))` for `P : Unit → Prop`, and `Eq (Π(x : &Nat). UU(Z)) (λ… => ()) (λ… => let c = *x; AddM(&c, 0))`. They are in Scratch/D59ConvGap.lean rather than the suite, because each would flip to accepted in the D59 row and break its class.
- §2 names the one-line proof `AddZero`; the test is Numbers.AddZero', because Numbers.AddZero is the match proof the paper no longer prints.
- The `Trees` block still has the pure recursive `Insert`, with `InsertMEq` and its size theorem. The paper no longer prints these; InPlaceTrees is the printed version.

## 17. The examples as a tour of the language: old names → new names

The example files were named after rule versions and reviewers (E1–E6, V15–V19, D44, Review3, Attacks, More, Probes, Logic, Inductives, Paper). They are now 15 files named and ordered by language feature, `Ochr/Examples/01Numbers.lean` … `15BorrowTypes.lean` (the checker README lists them), and every program is reformatted: a multi-line body in parentheses under the signature, one match arm per line with a trailing comma (arms are separated by commas since 90cd2c96), one statement per line, no alignment. The historical sections above keep the old names (`V17.LieL`, `Attacks.Knot`, …); this table says where each declaration went. A program (`ochr` block) is its own namespace, so a helper such as `AddM` exists once per program that needs it.

Checked mechanically against the suite just before the reorganisation (459 declarations, comma syntax):
- every old declaration has, under its new name, the same expectation, the same verdict and the same rejection message (up to the renames below);
- every new declaration parses to the same surface term as the old one, up to the renames, so the reformatting changed only layout;
- the ledger has the same 46 rows and classes, and each row flips the same programs, as sets, through this table. Three rows list fewer programs because a deleted duplicate maps to the declaration it duplicated: the D27 row (16 → 15) and the D45-by-type row (27 → 26) because `AndElim.AndL` is `ByType.Fst`, and the D37 row (4 → 2) because V18's `Esc`/`BoomE` are Note 5's `Esc`/`Bad5`. No added program flips in any row.

Since the next change (§18) the definitions the tour shared are in one block, `Std`, which the other blocks use; the table gives that final place. 432 declarations: 459 − 57 deleted duplicates + 30 added. A *duplicate* is a declaration whose text equals another one's up to layout and the renames; each is listed below as "(duplicate)" and maps to the declaration of the same (new) name in the program it went to. 48 of them are copies of the helpers now in `Std` (`AddM`, `Add`, `AddMZero`, `TailM`, `Pick`, `Bool`, `List(A)`, `Box(A)`, `Empty`, `U`, `V`); one of those, E3's `Pick`, differs from `Std.Pick` in the names of its bound variables only ("duplicate up to bound names"), and its users keep their verdicts and messages. The other nine are `D49.Le`, `D49.SubM`, `D49.Sq`, `E6.WriteThenRefl` (= E1's), `AndElim.AndL` (= `ByType.Fst`), and V18's X3 group `Box`, `Double`, `Esc`, `BoomE` (= Note 5's, with the constructor `MkBox` renamed `Mk` and `BoomE` renamed `Bad5`). Renamed to avoid a clash in the merged programs: `V15.Loop`, `Boom4` (now `Recursion.LoopNoBy`, `LoopNoByBoom`: `Recursion.Loop` is the D17 attack) and `AndElim.Two`, `TwoR`, `TwoWrong`, `Three` (now `Propositions.TwoOwners`, `TwoOwnersR`, `TwoOwnersWrong`, `ThreeOwners`: `Propositions.Two` is `ByType.Two`). Every other declaration keeps its name.

Added where RULES had a construct or side condition with no readable example (21): `Numbers.MissingArm`, `Pred`, `PredOfAbstract`, `PairLocal`, `PairLocalIs`, `PairWrite`, `PairWriteIs`, `PairBorrow`, `PairBorrowIs`, `ProjNat`, `SwapPair`, `Unsaturated`, `AscribeWrong`; `ClosingOff.ArmTypes`, `ArmAnnot`; `Equality.Transport`, `TransportBack`; `Recursion.SelfType`; `Functions.ApplyArrow`; `Universes.TypeInType`; `BorrowTypes.RefCell`. One is a finding: `SwapPair` is rejected because a pair parameter cannot be projected (an abstract pair has no components, and the rules have no match on pairs and no η rule for them), so pairs are usable only when their components are known. `ProofIrrelevance (P : Prop) (h1 h2 : P) : Eq P h1 h2 := refl` was considered and left out: it is accepted, but it flips in the D27 row, which would change the ledger.

Added for the rejections of `capture` (Machine.lean), which no test covered (9, in `Snapshots`, next to the accepted `CapS`, `CapSId`, `CapPi`, `CapP`, `CapP2`, `Cap`, `CapMut`): `CapBorrow` (rejected: "a closure or Π-type captures the borrow x"), `CapCopy` (accepted: copy `*x` first), `PiBorrow` / `PiCopy` (the same for a Π-type), `CapEndsBorrow` (rejected: capturing `a` reads it and ends the borrow `r`, so `*r := 1` finds no place), `CapAfterBorrow` (accepted: the write through `r` before the capture is seen, the closure returns 1), `CapSnap` (accepted: a closure formed before `a := 1` returns 0) and `CapSnapNew` (rejected: it does not return 1), `CapMoved` (rejected: "a closure or Π-type captures a moved place"). Every verdict was the expected one on the first run; none flips in the ledger.

| Old file | Old program | Its declarations, and the program they are in now |
|---|---|---|
| `E1.lean` | E1 | AddM, AddMZero, Add → Std; AddZero, AddZero', WriteThenRefl → Numbers |
| `E2.lean` | E2 | AddM (duplicate), TailM → Std; AddM', AddMEq, AddMEqOwned, AddM1, TailNoop → ReturnedBorrows |
| `E3.lean` | E3 | AddM (duplicate), AddMZero (duplicate) → Std; AddToOne, AddToOne' → ClosingOff; Pick (duplicate up to bound names) → Std; AddToOne'', AddToOneZero', AddToOneZero'', AddToOneZero → ClosingOff |
| `E4.lean` | E4 | AddM (duplicate), AddMZero (duplicate) → Std; Twice, TwiceNoop, TwiceM, TwiceMMove, TwiceMZero → Functions; Add (duplicate) → Std; TwiceMZero' → Functions |
| `E5.lean` | E5 | AddM (duplicate), Add (duplicate) → Std; Le, LeAdd, SubM, AddSub, AddSubId, AddSubStale, AddSubWrong, AddSubIdReborrow, LeId, ProofIrr → CurrentState; ExFalso → Propositions; LeZero, TwoPhase, TwoPhaseMoved → CurrentState |
| `E6.lean` | E6 | AddM (duplicate) → Std; UseMoved, UseReborrowed → Borrows; AddMZero (duplicate) → Std; LemmaMoves → Erasure; WriteThenRefl (duplicate) → Numbers; WriteThenRefl' → Snapshots; ZeroIsOne, Add01, NotAdd01 → Equality; Snapshot, SnapshotLie → Snapshots; DanglingLocal → Borrows; TailM (duplicate) → Std; DanglingTail → ReturnedBorrows; DanglingReborrow → Borrows |
| `Attacks.lean` | Attacks | AddM (duplicate) → Std; Bad → ClosingOff; Oops2 → Snapshots; Loop, Bot', Loop2, Spin → Recursion; P1, P2, F, FP2, Boom, BoomIsTrue, p1, p2, UseP, TA2, TA2Z, N1T, N1Closed, Q, QBoom, Boom' → Erasure; Pick (duplicate) → Std; G, BadC2 → Owners; G1, BadA1 → Borrows; Apply, Knot, KnotBoom, KnotL, KnotLBoom → Recursion; Add (duplicate) → Std; AddZeroC → Recursion |
| `More.lean` | More | AddM (duplicate) → Std; MatchAfterOpaque → CaseSplits; Dead, DeadTwice, NotDead, g, attack, attack' → Borrows; NonTailRec, StuckGoal, StuckGoalSplit, StuckGoalWrong → ClosingOff; AddMZeroLet → Equality |
| `Probes.lean` | Probes | AddM (duplicate) → Std; T, UseT0, UseT, DepMatch, DepMatchWrong → CaseSplits; Outer, OuterBad → Recursion; Cap, CapMut → Snapshots; AliasRead, AliasDangling → Numbers; Lemma, W5, EffArg, EffArgErased, F5, TypeErased → Erasure; WriteInBlock, AliasAfterBlock, MovedByBlock, ReborrowInBlock → ClosingOff |
| `V15.lean` | V15 | U, V → Std; W, Lie, Boom, MainW, MainW0 → ErasureBySyntax; TailM (duplicate) → Std; Bad, Main, Main0 → ReturnedBorrows; P, Boom3, Conv, ConvW → Functions; Loop (as LoopNoBy), Boom4 (as LoopNoByBoom) → Recursion; Clear, Boom5 → ClosingOff |
| `V17.lean` | V17 | U (duplicate), V (duplicate) → Std; LieL, BoomL, LieB, BoomB, TruthB, LieP, BoomP, LieG, BoomG, TruthG, F, SeqT → ErasureBySyntax; UU, AddU, G, RowUnit, RowI, RowIInd → ClosingOff |
| `V18.lean` | V18 | U (duplicate), V (duplicate) → Std; Mk, Lie8, Boom8, Direct8, Lie7, Boom7, P3d → ErasureBySyntax; Box (duplicate), Double (duplicate), Esc (duplicate), BoomE (duplicate, as Bad5) → GlobalRecords; PickX, PickY, ConvPick, Q, TX, TY, BoomX4 → Functions; P1 → ClosingOff; LieH, BoomH → ErasureBySyntax |
| `V18.lean` | Positivity | Empty (duplicate) → Std; absurd, Bad, L, K, bad, Boom, Pairs → Positivity |
| `V18.lean` | GenTy | List, AppendM, GenL → GenType |
| `V19.lean` | V19 | AddM (duplicate), AddMZero (duplicate) → Std; Local, Pass, Write, Borrow, Move, TailSteps → Erasure |
| `D44.lean` | D44 | Empty → Std; M, P, Q, Boom, LeakT, PF, QF, Keep, KeepT → ReturnedBorrows; AddM (duplicate) → Std; CapS, CapSId, CapPi, CapP, CapP2 → Snapshots |
| `Inductives.lean` | Inductives | List, AppendM, AppendMNil, AppendMOne, LastM, AppendM', AppendMEq → Lists; Bool (duplicate) → Std; Tree, Lt, InsertM, Insert, InsertMEq, InsertMSwap, InsertMSwapEq, InsertLoop → Trees; AddM (duplicate), Add (duplicate) → Std; AddMS, AddS, Size, SizeInsert, SizeInsertNoLemma, SizeInsertTwo → Trees |
| `Logic.lean` | Logic | absurd, absurdP, absurdId, absurdLet, Bot1, Bot2, Bot3, Bot4, NotEmpty, NotEmptyNat → Propositions; NoConf, NoConfS, NoConfMatch, NoConfBack, Inj → Equality; Bool → Std; BoolDisj, WriteDisj, WriteSame → Equality; Pair, PairI, ReflI, TopUnit, AndWrong, FromTrue, FromTrueIs → Propositions |
| `Logic.lean` | ByType | AddM (duplicate), AddMZero (duplicate) → Std; Swap, Fst, FstWrong, FstSwap, Two, TwoIs, WriteIf, WriteIfId, WriteIfLie, WriteIfAt, WriteIfAtLie, TwoAt, TwoAtLie, Snd, Twice, SplitId, AndTrue, AndTrueConv → Propositions |
| `Logic.lean` | OrAttack | Bool (duplicate) → Std; Or, OrComm, OrElim, OrLet, IsL, Irr, Boom, OrLie, Sq, Get, SqIrr, SqBoom, SqTrue → Subsingletons; U (duplicate), V (duplicate) → Std; EffL, EffLNoop, EffLOne, EffInline → Subsingletons |
| `Logic.lean` | PList | List → Std; AppendM, AppendMNil, AppendMOne, Append, AppendNil, AppendNilL, Closed, ClosedWrong, Ann, NoParam, WrongParam, Arity, BorrowList, BorrowCons → PolyLists |
| `Logic.lean` | PosParam | Void → PositivityParams; Box → Std; unbox, absurdV, Bad, L, K, bad, Boom, Neg → PositivityParams; List (duplicate) → Std; Rose, Sig, SigProof, SigAt, PropBox → PositivityParams |
| `Logic.lean` | Scrut | L, T, f, g, f0 → ScrutineeTypes; A, B → Lists |
| `Review3.lean` | D48 | AddM (duplicate) → Std; Impred, PolyId, SelfApp, SelfAppEq, PolyTy → Universes; PIref, RefTrue, RefFun, SwapT → BorrowTypes; List (duplicate) → Std; RefList, RefPair, F, G, UseG, InPair, InId → BorrowTypes; TailM (duplicate) → Std; Ann, HO → BorrowTypes |
| `Review3.lean` | D49 | AddM (duplicate) → Std; Le (duplicate), SubM (duplicate), Neutral → CurrentState; Sq (duplicate), SqSplit, SqZero → Subsingletons; List (duplicate) → Std; Explicit, ExplicitWrong, PairP, CapNil, CapNilAnn → PolyLists |
| `Review3.lean` | PiConv | AddM (duplicate), Add (duplicate) → Std; Apply, Cap, CapEq, Pow, P1, UseP, P3, ZeroAdd, UseRefl, PassZeroAdd, UseA, PassA, PassStuck, PassWrong, UseW, PassW, PassDom → Functions |
| `Review3.lean` | AndElim | AndL (duplicate, as Fst), AndL2, Two (as TwoOwners), TwoR (as TwoOwnersR), TwoWrong (as TwoOwnersWrong), Three (as ThreeOwners), Proj → Propositions |
| `Paper.lean` | Paper | AddM (duplicate), AddMZero (duplicate), Add (duplicate) → Std; Add23 → Numbers; AddZeroCopy → Recursion; AddXX → Borrows; NonCumul, PropInType → Universes; LetZ → Borrows; LamWrite → Snapshots; OwnedLocal, OwnedLocalNeq, WriteNeq → Equality; Pick → Std; PickEarly, PickEarly0, PickEarly1 → Naturality; List (duplicate) → Std; IterM → BorrowTypes; L, Inj → ReturnedBorrows; Box (duplicate) → Std; RefBoxProp → BorrowTypes; CoInd → Functions |
| `Paper.lean` | Note4 | Bad, L, Bad4 → PositivityPaper |
| `Paper.lean` | Note5 | Box, Double, Esc, Bad5 → GlobalRecords |
| `Units.lean` | D18 | Pick (duplicate) → Std; Probe, Use, Pick3, K, BadD18, ClosedD18, Neq, GR, BadR → Owners |

## 18. Blocks that use other blocks, and `Std`

An `ochr` block may use other blocks: `ochr Numbers uses Std { … }` (`uses A, B`, optional; a non-reserved keyword). Built as agreed with the user:
- *What a block is.* The command defines a Lean constant `Name : Ochr.Surface.Block` holding the block's name, the blocks it uses (their Lean constants) and its declarations. A block in another file is used by importing that file.
- *Checking.* A block is checked after its library: for each block it uses, transitively and each block once (by name, a block after the blocks it uses), that block's own declarations that are `def`s and are accepted, themselves checked after their own library. A `reject` declaration, and a declaration the checker rejects, is never visible to users. Nothing is cached: the library is checked again, under the same configuration, wherever it is used, so switching a rule off re-decides it there too (the whole suite still checks in about 18 ms; a clean build, most of it the ledger, is about 55 s, up from about 40 s). A block's report, its verdict assertions and its exact count cover its own declarations only, so each declaration is asserted once, in its home block.
- *Names.* A block and the blocks it uses share one flat namespace. Declaring a name that a used block declares (other than by `reject`, constructors included), two used blocks declaring the same name, or a block declaring a name twice is an error when the block is elaborated, e.g. "ochr Clash: Clash declares AddM, which LibA (used by Clash) already declares; the declarations of a block and the blocks it uses share one namespace".
- *Ledger attribution.* When a rule is switched off and a library declaration flips, the flip is counted once, in its home block's rows. A declaration of a using block that flips and mentions a library declaration whose visibility changed (or another such declaration of its block) is reported as "<Block>.<decl> blocked by <Home>.<decl>" instead of as a flip. `rowOk` asserts the blocked list of every row; it is empty in all 46, since no declaration of `Std` flips under any switch, and the flip lists are exactly those of the tour before `Std`. `Units.lean` tests the attribution on two small blocks (`AttrLib.Swap` flips under `byType := false`; `AttrUser.UseSwap` is blocked by it), the clash check and the closure.

`Std` (`Ochr/Examples/00Std.lean`) holds `AddM`, `Add`, `AddMZero`, `TailM`, `Pick`, `Bool`, `List(A)`, `Box(A)`, `Empty`, `U`, `V`: every definition the tour repeated. `Le` and `Lt` stay where they are, each used by one block. Twenty blocks use `Std`; `Lists`, `GenType` and `GlobalRecords` do not, since they declare a different `List` or `Box` of their own, and four others need nothing from it. The built-in prelude (`False`, `True`, `And`) is still part of the checker. Checked as before: every declaration's verdict and rejection message unchanged (against the original suite and against the tour), every declaration in `Std` equal to the copies it replaces (up to bound names for E3's `Pick`), the ledger's flip lists byte-identical, and 432 declarations (464 − 43 copies + 11 in `Std`).

## 19. D52 in the checker: pairs are the library's `Pair`, `Eq` is injective, the library is Ochr code

RULES v2.1 / DECISIONS D52, as built:
- *The library is an Ochr block.* `Ochr/Prelude.lean` declares `Prelude { Pair (A B : Type) := Mk(fst : A, snd : B); False : Prop; True : Prop := I; And (P Q : Prop) : Prop := Intro(l : P, r : Q) }`, checked like any block and asserted in `00Std.lean`. Every block uses it implicitly (`libOf` puts its accepted declarations first; the clash check counts its names), replacing the hard-coded `Check.prelude`. The kernel knows these names: `Pair`/`Mk` for the notation `A × B`, `(a, b)`, `t.1`, `t.2` (resolution, the places `.1`/`.2`, printing, and the syntactic "a codomain `A × B` is data"), `True`/`I` for `refl` and `⊤`, `False`, `True` and `And` because `Eq` computes to them, and `True`/`And` for the unit laws (D50). The file's doc comment lists each function.
- *Pairs.* The checker's pair type, value and term forms (`prod`, `pair`, `tProd`, the pair value) are gone. `A × B` resolves to `Pair(A, B)` and `(a, b)` to `Mk(a, b)`; `t.1`/`t.2` stay, as places (`.fst`/`.snd`) or terms, and denote field 1 or 2 of a `Pair` value (field 1 of `S v` for `.1` on a number, as before). A pair parameter is taken apart by `match p { Mk(a, b) => … }` via ordinary [Split]; projecting an abstract pair fails as reading a field of any abstract inductive value does ("no such place p.2: its path does not exist in σ0"); there is no η rule.
- *Injectivity.* `mkEqM`: after reflexivity, two values built by the same constructor give `And` of the equations between their fields at the field types instantiated at the parameters (from the equation's type `D(ā)`, else the values' recorded parameters; `S` counts as `Nat`'s constructor with one field), right-nested, with the unit laws: no fields is `True`, one field the one equation. D47's disjointness is unchanged. The switch is `injective`.
- *`Id`.* `observe` returns the result and the owners' contents; `idType` builds `And(Eq A r r', And(Eq T₁ w₁ w'₁, …))` directly (`andList`), no longer an `Eq` at a pair type. The shape is the old one exactly (the old pair rule produced the same nesting), so every message printing an `Id` is unchanged.
- *Names.* `Prelude`'s names are in every block's namespace, and `Mk` is `Pair`'s constructor, so the tests that used `Mk` were renamed: `Sq := MkSq(n)` (Subsingletons), `Bad := MkBad(f)` (Positivity, PositivityParams, PositivityPaper), `Box := MkBox(x)` (GlobalRecords, as V18 had it), `A := Make(x)`, `B := Make(y)` (Lists), the function `Mk` of ErasureBySyntax → `MkClosure`, and Propositions' `Pair` (a proof of `P ∧ Q`) → `AndPair`.
- *Fixtures.* `Std` keeps the library definitions (`AddM`, `Add`, `AddMZero`, `TailM`, `Bool`, `List`, `Box`); `Pick`, `Empty`, `U`, `V`, which only tests need, moved to a block `Fixtures` in the same file.
- *Not done.* `Nat` and `Unit` stay built in. `Nat` is deep: numerals and `S t` are its syntax, `S y` in a match is the sub-place `p.1` (the same place as a written `x.1`), the machine has its own [Match] (arms `Z` then `S`, with its own surface error), [Split] and [Rec] paths for it, and every message prints numbers as numerals; rebuilding it as `Z | S(pred : Nat)` would change every one of those and most messages. `Unit` is shallower but touches [Close]: its `Unit` row is read from a codomain written `Unit` and returns `()`, and the machine makes `()` in several places ([Assign], [Close], drops). Both are left for a separate change.

Checked mechanically against the suite before D52 (0127f58b, 432 declarations):
- *Verdicts.* Exactly three flip, all rejected → accepted, all by injectivity, and their expectations changed: `Equality.Inj` (`Eq Nat (S a) (S b)` is `Eq Nat a b`), `Recursion.AddZeroCopy` (the pure `AddZero` recursing on a copy, no `cong`: the goal `Eq Nat (S ⌈Add(σ, 0)⌉) (S σ)` computes to the induction hypothesis's `Eq Nat ⌈Add(σ, 0)⌉ σ`) and `CurrentState.AddSubIdReborrow` (the induction hypothesis about the predecessor in place is an equation between successors, which now computes to the goal). None flips for pair-as-inductive.
- *Messages.* Ten rejection messages change, none because of pairs (pairs print as before, `A × B` and `(a, b)`). Six by injectivity, an equation between constructor values now computed: StuckGoalWrong (`Eq Nat 1 (S σ2)` → `Eq Nat 0 σ2`), InsertMSwapEq (`Eq Tree Node(…) Node(…)` → the conjunction of the field equations), SizeInsertNoLemma (one `S` fewer on each side), SizeInsertTwo (`Eq Nat 2 1` → `False`), WriteIfAtLie (`Eq Nat 7 8` → `False`), TwoAtLie (`Eq Nat 2 3` → `False`). Four by the constructor renames: Lists.B ("the constructor name Make is already used"), Positivity.Bad, PositivityParams.Bad and PositivityPaper.Bad ("field f of MkBad : …").
- *Parsed programs.* Identical except the renames above and SwapPair (see additions).
- *Ledger.* 47 rows. The 46 old rows keep their classes and their flipped programs, except D48 (2), which no longer flips `BorrowTypes.InPair`: `Nat × &Nat` is now `Pair(Nat, &Nat)`, whose parameters may not be borrow types whatever the switch says (the row keeps its class, soundness, witness `BorrowTypes.G`). New row "D52 (v2.1): Eq is injective on constructors", class completeness: switching injectivity off rejects Equality.Inj, Equality.PairInj, Recursion.AddZeroCopy and CurrentState.AddSubIdReborrow. No blocked declarations in any row.
- *Additions* (8, all as expected): `Prelude`'s 4 declarations; `Numbers.SwapPair` (a pair parameter taken apart by `match p { Mk(a, b) => (b, a) }`, accepted; the projection version, `(p.2, p.1)`, is kept as `SwapPairProj`, still rejected: "no such place p.2: its path does not exist in σ0"); `Equality.InjWrong` (rejected); `Equality.PairInj` (`Eq (Nat × Nat) (a, b) (1, 2)` is `Eq Nat a 1 ∧ Eq Nat b 2`, accepted) and `PairInjWrong` (the swapped conjunction, rejected). The pure `AddZero` without `cong` is `Recursion.AddZeroCopy`, now accepted.
- 440 declarations = 432 + 4 (`Prelude`) + 4 (SwapPair, InjWrong, PairInj, PairInjWrong).

## 20. The recCands fix: the [Rec] state survives every restore

*The bug* (fuzz-port, 2026-09-29; accepted on 96d788a1): `Boom : False := Lie(0, ⟨refl, refl⟩)` with `Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }`. `sealedType` types a sealed program by running it on a private copy outside the enclosing functions (`recStack := []`, `recCands := []`). `restoreKeep` restored `recStack` whole but merged `recCands` by position (`cur.recCands.drop (cur.len - saved.len)`), which from the emptied list kept `[]`; `recCheck` zipped the two lists, so no later recursive call of any enclosing function was checked.

*The fix.* The two lists are one: a `RecCtx` frame carries its candidates and a `uid` (from `nextRecUid`, never reused, kept by every restore). `restoreKeep` gives each saved frame the candidates of the current frame with the same `uid`, if there is one, so a computation that replaces the stack (`sealedType`) or starts a fresh one (the L3 counterfactual, whose special case at the end of `checkFix` is gone) cannot wipe or shift them. `recCheck` narrows the frames of the called function in place. An implementation bug, not a rule: no switch and no ledger row.

*Paths.* Found by tracing every `valType` call site; each program below was accepted before the fix (checked on 329482c6) and is rejected by [Rec] after it. The value typed is a sealed program, reached through `placeType` of a place with no stored type: a pattern variable (`Lie`: the conjunction's parameter `⌈Le(σ, 1)⌉`), or a closure's capture read in its codomain (`LieCap`) or in its body (`LieRead`); or through `Id`'s footprint over a capture (`LieId`). `indValType` and a borrow's content reach `valType` only below these; the `.val` case of `eval` meets a sealed program only inside `sealedType` itself, where the stack is already empty. Tests in `07Recursion`, each with its `Boom`. The ledger and every other verdict and message are unchanged.

*Audit* of the state kept outside Ω (`MState`) and how restores treat it (all restores go through `restoreKeep`, including `onCopy`'s):
- Scoped, restored whole: `env`, `refs` (refinements), `goal`, `depth`, `effects` (D41; a stuck block re-adds its arms' pending steps by hand), `convStack` (D30; a cycle answers false, never true), the flags `lastErased`/`lastProof` (re-derived for each term by `eval`).
- Kept whole: `fuel` (also carried by `.stuck`), `classCache` (keyed by the Π value itself), `nextRecUid`; `nextAbs`/`absTy`/`nextLoan`/`neutrals` when `globalRecords` (D37; switching it off restores them, which is what the D37 row shows).
- Merged: only the [Rec] candidates, now by `uid`.
- Nested runs that replace per-definition state: `sealedType` (env, [Rec] stack, goal), `nfSealed` (env, depth; it keeps the [Rec] stack but runs untyped, so it never checks a recursive call), `checkFix` (env, goal; pushes a frame), function conversion (env, `convStack`), a constant's check. Only `sealedType` touched the [Rec] state.
- Exceptions discard the state back to the handler's entry (`StateT` over `ExceptT`), except the fuel a `.stuck` carries. The handlers that recover are closing off a call (`runBody` runs untyped: no `recCheck` inside), `nfSealed` (untyped), the hints `fieldTypeAt` and `argHint` (recomputed where they matter), and conversion (answers false). None of them can lose a narrowing made by a typed recursive call that is not checked again elsewhere.
- 449 declarations = 440 + 9 (`Le`, and `Lie`, `LieCap`, `LieRead`, `LieId` with their `Boom`s).

## 21. D54, D56, D58 in the checker; D55 built, switched off pending the fixture decision

- *D54 (reviewer-5): a Π-type's erasure class and [Close] row are part of it.* `convPi` first requires equal `fnClass` and `declKind` (switch `classInType`). The class and row are those the D35 classification reads off the codomain term, as before. At a call, `callFn` reads the class and row from the function value's own declared Π-type (`funType fv none`), not from the static type. Conversion now guarantees that the two agree, so the typed and untyped paths use one source.
  - *The partial mechanism it replaces:* `funType fv fT` preferred the static type `fT` whenever the call was typed. That is why a direct call through a parameter was safe and a call after `let g = f` or through `IdF(f)` was not. In untyped runs `fT` is absent and the value's own codomain decided.
  - *Tests (Functions, 14 declarations):* reviewer-5's program verbatim (`P0`, `H`, `RunG`, `RunGGen`, `Boom`, and `RunGH`, now rejected at the argument); the identity-function variant (`IdF`, `RunI`, `RunIGen`, `BoomI`); and the [Close]-row variant (`UU`, `H2`, `RunU`, `RunUH`). The proof-class variant writes `V(Z)` as a codomain, so it waits for the D55 fixture decision.
  - *Ledger row, soundness:* witnesses `Boom` and `BoomI`; it also flips `RunGH` and `RunUH`.
  - *Completeness:* no existing verdict or message changes.
- *D56 (reviewer-4 W4): `J` computes only on convertible endpoints* (switch `jStuck`). `t` always runs, so its effects happen once, as in a closed run. `jValue` then returns its value when `a ≡ b`, and otherwise the stuck cast `⌈J(A, a, b, P, (⋆ : Eq A a b), v)⌉`, which re-normalises to `v` once a refinement makes the endpoints convertible. A `J` whose motive returns `Prop` is unchanged.
  - A call whose head is a stuck cast takes its type from the cast's program (`funType` on a sealed head now tries `valType`). This is needed for `Om`.
  - *Tests (Equality):* `CastRefl` (computes); reviewer-4's `C1`, `C2`, `Om` (was "call depth exceeded", now accepted) and `CastMatch` (was "[Match] on 5, which is not a value of Bool", now accepted).
  - *Ledger row, completeness:* `Om` and `CastMatch` are rejected without it.
- *D58 (hashmap-port): a zero-arm match outside a proof position is stuck* (switch `zeroArmStuck`). An untyped run that reaches one is stuck, and the enclosing call closes off. A typed one at a type that is not a proposition is closed off like a stuck match (`closeOffMatch`). At a proposition it is `⋆`, as before.
  - *Tests (Propositions):* `IsZ`, `GetZ`, `GetZIs` (hashmap-port's minimal program, renamed to fit the block's names).
  - *Ledger row, completeness:* `GetZIs` is rejected without it.
  - No existing test depended on `⋆` from a zero-arm match at a data type.
- *Existing rows that also flip the new tests:*
  - P2 and P2 without D41: `RunGGen`, `RunIGen`.
  - C8: `CastMatch`.
  - D28: `RunG`, `RunGGen`, `RunI`, `RunIGen`.
  - P1, P1 without D41, P3, P3 without D41, P1 with the computed block rule, captured types, and D48 (3): `Om`, whose stuck casts exercise all of them.
  - All of these are rejections. No row's class changes.
- *D55 (reviewer-4 W1/W2), built but off.* `Check.declOf` is a static pass run over each definition, and over an inductive's parameter and field types (switch `sortsSyntactic`, default off for now).
  - It computes each term's *declared* type as a `DeclInfo`: a sort, a Π with what its codomain says, `&A`, or other. It reads the heads' declarations without normalising.
  - It requires a sort at every type position: binder types, codomains, `let` annotations and ascriptions, Π components, the type slots of `Eq`/`Id`/`J`/`&`, inductive and constructor parameters, and field types.
  - Unknown names are left to the machine, so its messages keep their order.
  - Switched on, it rejects every reviewer-4 program (W, f, TT, g2, k, and with them Boom, Boom2, RunIs, Lie4, Boom4, K1, K2).
  - In the suite it rejects only programs that write `V(Z)` as a type, because `V (n : Nat) : U(n)` makes `V(Z)`'s declared type `U(Z)`, which is not a sort:
    - accepted before, rejected now: `EffL`, `EffLNoop`, `TruthG`, `LieH`;
    - rejected before, with a D55 message now: `EffInline`, `LieG`, `BoomG`, `BoomH`, `EffLOne`.
  - Measured against the D55-on default: the D40 row flips nothing (its witnesses all write `V(Z)`), and ten rows lose witnesses but keep flips.
  - Reported to the lead; the fixture decision is pending.
- 471 declarations = 449 + 14 (Functions) + 5 (Equality) + 3 (Propositions). Ledger: 50 rows.

## 22. Typing a sealed program: embedded values are typed by their position

Two incompleteness reports hit the same gap: `valType` had no type for a value that has none of its own.
- *arrays-library:* "cannot infer the type of the value ⋆". `H (x : Nat) (h : ⊤) : Nat by x` is stuck at an abstract `x`, so `let y = H(x, refl)` holds the sealed `H(σ, ⋆)`. Typing that program (`sealedType`, reached from a split on `LeDec(y, x)` or from a closure capturing `y`) typed the argument `⋆` on its own.
- *fuzz-port (49 cases):* "cannot infer the type of the value loan_ℓ". Re-running a stuck match's sealed block at `*x0 := 0` meets `Id Unit () (*x0 := 0)`, whose footprint owner is the block's cell for `*x0`. That cell has no stored type in the untyped re-run, and it is lent out.

Neither value is ill-typed. It is typed by where it sits, as D51 already did for captured proofs:
- *A proof argument, and an inert loan,* take the type of their position. `evalCall` and `evalCtor` now pass the parameter's or field's declared type as a hint for an embedded value (`.val`) too, not only for a constructor argument. `eval` types `.val ⋆` by that hint when it is a proposition, and an inert loan by the hint when its borrow is not in the run.
- *A live loan* has the type of its borrow's content: `valType (.loan ℓ)` finds `borrow_ℓ c` in Ω and types `c`.

Tests (ClosingOff, "Typing a sealed program"): `Le`, `Lt`, `Dec`, `LeDec`, `H`, `UseDec`, `Apply`, `UseApply` (arrays-library's repros), and `IdInBlock` (fuzz-port's shape, `Id Prop (match *x0 { Z => Id Unit () (*x0 := 0), S _ => ⊤ }) ⊤` proved by splitting). All accepted; all were rejected before. Every earlier verdict and message is unchanged.

The ledger's rows are unchanged apart from rejections of the new tests:
- C8: `UseDec`;
- D28: `IdInBlock`;
- captured types: `UseApply`, `UseDec`;
- D48 (3): `UseApply`.

480 declarations.

### 21.1 D55 on; D54 refined; D40 deleted (merged with ochr-core at 384f4762, 498 → 519 verdicts)

- *D54 refined* (lead, 2026-09-29): `convPi` compares the class and whether the codomain is a borrow (`&T`). The `Unit` and data rows of [Close] stay convertible, since `Unit` has one value; η for `Unit` (D59, planned) would delete the `Unit` row altogether. The strict version rejected every higher-order function that is polymorphic in its continuation's result type and instantiated at `Unit`: the arrays library's `WithSplit(E, R, …, f : Π(…). R)` at `R := Unit`, taking out ArrayBench's B1Join, B1, SplitNoop and ZeroFirst2, and Quicksort.Recurse, with 6 dependents. All 11 are accepted again on this head; arrays' `GetMutSet` (expected rejected there) is now accepted, by §22. `Functions.RunUH` is accepted, and the D54 row keeps its witnesses `Boom` and `BoomI`.
- *D55 on by default.* The V(Z) programs:
  - The attacks are kept verbatim and now rejected by D55, each with a one-line comment: `ErasureBySyntax.LieG`, `BoomG`, `LieH`, `BoomH`, `Subsingletons.EffInline`. Their point, the seam between declared and computed sorts, can no longer be written.
  - `EffL`, `EffLNoop` and `TruthG` only made sense across that seam, so they are rejected by D55 too. `EffLOne` is still rejected, now because it uses `EffL`.
  - D54's proof-class variant (`Functions.RunP`, `RunPGen`, `WV`, `BoomP`) is in, with `WV` and `BoomP` rejected by D55. D54 alone rejects `BoomP` at the argument.
  - reviewer-4's programs are block `Sorts` in `14Universes`, verbatim (17 declarations).
  - The D55 row is class model, witnesses `Sorts.K1`, `Sorts.K2`: `TT` would be a proposition with two inhabitants a data function tells apart. With D54 on, the closed proofs of W1 are still caught at their arguments.
  - The new `InPlaceTrees` and `SizeInsert` tests are unaffected.
- *D40 deleted.* With D55 on its row flipped nothing: its witnesses all wrote `V(Z)` as a type. "A stuck block is erased iff each arm is" follows from "a term is erased iff its type is a proposition", since a match's type is its arms' type. Its switch and row are gone. `blockRule` stays in `Config` for the D35/D40 row (`blockRule := 0`) and the P1-with-computed-block row.
- *Rows whose witnesses D55 removed* are reclassified by what they flip now:
  - D28 (erasure by declared class): false lemma [LieG] → policy [ClosingOff.RowI], the true `Unit` statement.
  - D35/D40: soundness [BoomB, BoomG, Boom7] → [BoomB, Boom7].
  - P3 without D41: soundness [BoomH] → false lemma [LieP].
  - P1 with the computed block rule: [BoomP, BoomG] → [BoomP].
- *Ledger with D55 on*: 50 rows, and every row flips something. Soundness 22 (16 with a closed proof of `False`), false lemma 1, model 4, policy 4, completeness 19.
- *Rows that no longer guard anything of their own.* Among the "without D41" combination rows, P1 and P3 add over D41 alone only rejections of good programs (`Om`, `CapP`, `CapP2`, and `OrLet` for P1): their accepting flips are all D41's.

## 23. The erasure pre-pass: erasure is decided before a term runs, from declared types

*What changed.*
- `eval` asks `preFlags` whether a term is erased and whether it is a proof before it runs, and uses the answer. `preFlags` reads the term's declared type with `declOf`, the same reading as D55's static pass (moved into the machine).
  - A term is a proof iff its declared type is a proposition, or a Π-type into propositions.
  - It is erased iff it is a proof, or it is a call returning types, other than a stuck block's call.
  - A stuck block's call is a match, and a sequence, `let` or match is erased iff it is a proof (D35).
  - The declared-type readings live in `DeclInfo`: a sort, a proposition, a Π with its codomain, `&A`, other, and `any` (a zero-arm match).
- Every binding in Ω now records what its declared type says:
  - parameters from their domain terms (`paramDecls`, in the scope of the captures and the earlier parameters);
  - a `let` from its bound term;
  - captures from their values (`valueDecl`: ⋆ is a proof, a type has its sort, a function has its own Π-type's codomain);
  - `self` as its Π-type.
- A binding whose declared type is a Π-type only after computing it, such as `p : Pow(Nat)`, or which holds a function value, takes the value's own declared Π-type (`refineDecl`). D54 makes that the static one.

*The assertion.* The after-the-fact classification (D28/D35/D42, the leaf and block rules) still runs, as an assertion. Under the default rules, a disagreement is an INTERNAL error.
- Across the whole suite (519 verdicts, every sealed-program re-run and conversion) the two agree, once three things are in place:
  - `self`, read as a call's head, is not classified: a call's flags are its own, and the after-the-fact rule deliberately does not treat `self` as a proof, so that a closure never inlines it as `⋆`, which would escape [Rec];
  - a stuck block's call is classified as a match;
  - a function-valued binding takes its value's declared Π-type.
- A counterfactual run, with one rule switched off, does not assert, so the ledger measures the rule alone.

*The ledger with the pre-pass deciding.* Verdicts and messages are unchanged. Rows that now flip nothing, with the new class `subsumed` (asserted to flip nothing):
- *D35: a function's class is read from its codomain term* (classBySyntax). Its witnesses BoomL, Boom8 and Direct8 stay rejected with the v1.6 rule switched on. The class that decides erasure is read from the declared type whatever that switch says.
- *D35/D40: a stuck block is erased iff each arm is* (blockRule := 0): LieB, BoomB, Lie7, Boom7 and TruthB keep their verdicts.
- *D35: a let, sequence or match is erased iff it is a proof* (seqByProof): SeqT keeps its verdict.
- *D54: the class and borrow row in the Π-type* (classInType).
  - Boom, BoomI and RunGH are now rejected with D54 off, by confinement (D41): "[D41] an erased term borrows c". `g(&c)` is erased by its declared type on both paths, so `H`'s write is an erased term's effect on an outer place.
  - D54 still makes a function value's class, which `callFn` uses to decide whether a call runs, equal to its static type's. But in the suite nothing depends on it once erasure is static and D55 holds.

Rows that shrink:
- D28 (erasure by declared class): 10 → 7 flips. It keeps RowI accepted, because `erasureByDecl` also sets [Close]'s row.
- P1: 4 → 3, all rejections. P1 without D41: its accepted flips are all D41's.
- P1 with the computed block rule: 6 → 3, all rejections, so completeness now; BoomP is no longer accepted.
- D55: loses TruthG.

Nothing else changes. Ledger classes now: soundness 18 (12 with a closed proof of `False`), false lemma 1, model 4, policy 4, subsumed 4, completeness 19.

*Cost.* A full suite run takes about 0.8–1.1 s with the pre-pass and about 0.7 s without it; the machine was under load. Three things keep it cheap:
- the frame's bindings are read in place (`withLive`);
- a sequence or `let` hands its reading to its tail;
- globals' readings are cached.

A first version formatted `Config` to decide whether to assert, and was 4× slower; perf showed it.

## 24. P2 is a soundness row (fuzz-port)

With P2 off (`eraseOnCopy := false`) and D41 on, a closed proof of `False` is accepted. Confinement lets an erased term pass an outer place to an erased call. Without the private copy, that call's writes persist on the direct path, while the closed-off block, being erased, skips them. fuzz-port's `P2Alone` is in `Erasure`, in a new section "What goes wrong without the private copy": `LieP2` (accepted), and `BoomP2Pair` and `BoomP2` (rejected). The P2 row is now class soundness with witness `BoomP2`; it was completeness. `LieP2` also shows up as a rejection in the D28, D42, D45 + D42 and confined-bodies rows. Classes: soundness 19 (13 with a closed proof of `False`), false lemma 1, model 4, policy 4, subsumed 4, completeness 18. 522 verdicts.

## 25. fuzz-port's fail-safe classes R2, R3, R4, R7

Each is a true statement that the checker rejected. Each is now accepted, and each has a regression: `ClosingOff.LamWriteInBlock`, `LamReadInWrittenBlock` and `ConvBlocks`, and `Equality.SymmUnreachable`. All four were rejected on 6d90f016.

- **R2 (i): a closure's write inside a stuck block.** The block's capture analysis counted a nested λ's write to its own captured copy as a write by the block. So it took the place by `&`, and when the block re-ran, the λ captured a borrow. The fix: occurrences inside a nested function or Π-type count as reads (`Term.blockOccs`).
- **R2 (ii): a closure reading a place the block writes.** When an arm really writes a place, the block takes it by `&`. A λ in that arm that only reads the place then captured the block's borrow parameter. The fix:
  - A stuck block's borrow parameter is marked on its binding (`blockRef`; its declared type is the block's `.val (&T)`).
  - `capture` captures the value behind such a parameter, `(*c).1` by value, when the λ only reads through it. This is how the λ captures the place itself on the direct path.
  - A user's `&` parameter is unaffected: `CapBorrow` is still rejected.
- **E** (an arm-local σ in a block's inferred type) came only with R2 (ii); it no longer shows up in the regressions.
- **R3: an error while comparing two blocks' functions.** `convFn` observed the functions at a generic argument where a pattern's sub-place does not exist, and the error escaped. It now answers "not convertible", as `convPi` does.
- **R4: a call of a sealed function in untyped code.** Fixed since 4b8bdbd2: `funType` on a sealed head types its program. fuzz-port saw it drop from 23 cases in 10⁶ to 0. `V2Classes.R4s` is still rejected, because the proof splits the wrong place (§27).
- **R7: `symm` in an unreachable branch.** `symm` (and `trans`) of a proof of `False` is a proof of `False`. An equation that a refinement made impossible computes to `False`, and so does its symmetric one.

Not taken up here:
- **R5**, one case in 10⁶. Two arms' Π-types capture a place holding a sealed program that the arms' refinements made different. It is the same root as E: types read under arm refinements.
- **R6.** `Id`'s conjunction order is not stable under closing off; it needs a canonical footprint order.
- **R1's residual**, one case in 10⁶. An `Id` owner reached through a returned borrow is an inert loan in a re-run. It needs the cells a closed-off call creates to carry their declared types.

Draft RULES wording for the stuck-block capture rule (§3 "Stuck blocks"), after "otherwise a place it reads is passed by value (copied)":

> An occurrence inside a nested `λ` or Π-type counts as a read, whatever that function does with it: a closure captures a copy, so its writes and borrows are to that copy. A closure formed inside the block that reads, through one of the block's `&` parameters, a place the block writes captures the value behind that parameter, as it captures the place itself when the match is not closed off.

526 declarations.

## 26. D53 in the checker: moves, copy types, `clone`, ghosts, the Fn rule

This follows DECISIONS D53, its amendments (a)–(h), the second amendment (`Word`), and fuzz-port's shapes (a)–(c). Switches: `moves` (the rule), `ghosts` (c), `fnRule` (e).

- **Reads.** A runtime read of data whose type is not a copy type moves it: the place holds a *ghost* (`Value.ghost v`, a real form in Ω) and is dead for runtime code. A borrow is always moved (`⊥`). Copy types (`isCopyType`) are:
  - `Unit`, sorts and propositions;
  - an inductive declared `copy` (its fields must be copies, checked in `checkInd`);
  - a non-recursive `Type₀` inductive with copy fields.

  A closure is a copy exactly when its captures are (`isCopyValue`). `Nat` is not a copy type.
- **Erased reads copy (a).** An erased term's reads copy, and it sees a ghost's value (c: a proof may mention what runtime code moved, in any order). What is erased comes from the pre-pass (§23), decided before the term runs:
  - types and statements;
  - `Id`'s sides;
  - `clone(p)`;
  - a sealed program's final read (`peek`: the `K` of [Close]);
  - the bodies of functions whose calls are erased (b).
- **Sealed programs.** A sealed program's `L; C` re-runs as the code it came from, and only its final read is an observation (shape (b)). Function bodies and sealed re-runs inherit erasure from where they run: a closure written in a statement is not runtime code. Conversion compares functions as code (`convFn` observes under `withRuntime`), so a function that moves out through a borrow is not identified with one that does not (shape (c)).
- **The ⊥ checks (h)** apply to a place partly moved out: reading it, borrowing it, capturing it, ending a borrow of it, and returning a borrow of it (shape (c): `wholeReturned`).
- **The Fn rule (e).** A call's head is read in place and not consumed (`inPlace`). A runtime read of a non-copy captured value (`Binding.cap`) is an error, because a closure may run again: clone it. Forming a runtime closure moves the non-copy variables it captures.
- **Stuck blocks mirror the direct path (shape (a), amendment (f)).**
  - A place a block only reads is read in place (`inplace`), not consumed.
  - A part that some arm moves out is moved in on its own, at the move's granularity (`newHoles`: `q1.1`, not `q1`), while the rest of the place is still read in place.
- **`clone(p)`** is built in: an erased read of a place, so the clone of `σ` is `σ`.
- **`Word`.** `copy inductive Word := Zero | Succ(pred : Word)` is in `Std`. The names avoid `Nat`'s `Z`/`S`, which are syntax; there are no `Word` numerals. The trees' keys are words, with each tree block's own `Lt` on words. `Std` does not export an order, because the arrays library's and the hash map's blocks already declare `Lt` as a proposition about indices.

*Clones.* The suite's existing programs use 25 `clone`s, down from the study's 24 plus 8 new ones for the Fn rule, since `Word` removes the trees' six and `NotDead`'s one. They fall into three groups:
- data used twice (7): `(clone(n), n)` twice, `UseDec`, `PickEarly` ×3, `Om`'s function value;
- a copy taken out of a borrow (10): `CapCopy`, `CapS`, `CapSId`, `Local`, `Pass`, `Write`, `Borrow`, `AddSub` ×3;
- a closure body returning what it captured (8): `UseApply`, `CapCopy`, `CapS`, `CapEndsBorrow`, `Functions.Cap`, `CapNil`, `CapNilAnn`, `MkClosure`.

`PickEarly`'s `n` is a selector that `Fixtures.Pick` takes as a `Nat`; as a `Word` it would need no clone.

*Tests.*
- `Borrows` gets a section "Moves and copies (D53)" (18 declarations): moves, `clone`, `Word`, `copy` declarations, the ghost, the borrow rules, the Fn rule, and shape (b) (`MoveInArm`).
- `ClosingOff.BlockReads` and `BlockMovesField` cover shape (a); `Functions.RetMoved` covers shape (c).
- D48 (2) has a new witness: `G` now reads `a` while `r` may borrow it, since D53 catches the old double read by itself.

*Ledger.* Three new rows:
- D53: class `cost` (new), witnesses `TwiceNat` and `ClosureMovesCapture`.
- (c): completeness (`GhostRead`, `AddSub`…).
- (e): completeness (`CallTwice`, `Twice`…, `Size`).

53 rows: soundness 19, false lemma 1, model 4, policy 4, subsumed 4, cost 1, completeness 20. 548 verdicts.

## 27. D59: η for `Unit`

`mkEqM` makes `Eq Unit a b` equal to `True` for any two values (switch `unitEta`). [Close] loses its `Unit` row: a stuck call whose declared result is `Unit` returns its sealed program, like any other data. `convFn` treats two functions' results at a codomain written `Unit` as equal.

- *Verdicts:* `ClosingOff.RowI` (a call through `UU(Z)`, which is `Unit` only by computation) goes from rejected to accepted, by `refl`. Nothing else changes.
- *Ledger, new row:* D59, completeness (`RowI`).
- *Ledger, rows that change:*
  - The D35 row "[Close]'s row is read from the declared codomain" flips nothing: the only rows left are a borrow's, read off a declared `&T` anyway (D48 (2)), and data's. It is now `subsumed`.
  - D28 loses `RowI` and is now completeness.
  - D19 flips nothing. Its witness `BadA1` passes a live loan into a stuck `Unit` call (with D19 off, [Close]'s precondition is unchecked). The call's result is now its sealed program, not `()`, so it carries the loan, and discarding it is a [Drop] error. `BadA1` is rejected with or without D19, so the row is `subsumed` too. D19 is still what establishes [Close]'s precondition, which the checker asserts; it has no witness in the suite now. This is worth a new witness if one exists.
- *Classes, 54 rows:* soundness 18 (13 with a closed proof of `False`, 5 going wrong when run), false lemma 1, model 4, policy 2, subsumed 6, cost 1, completeness 22.
- `V2Classes.R4s` (fuzz-port's R4) is still rejected. Its remaining goal is about `x1`'s content, `Eq Nat ⌈…(&c1); c1⌉ 0`, because the called function is stuck on `*x0`. The proof splits `*x1` instead of `*x0`, so that proof cannot close it, with or without η. Earlier notes called this a matter of η; that was wrong.

## 28. Merging ochr-core (the case studies, D60, D61): what the pre-pass needed

*The case studies stay pre-D53 for now.* With moves on, 231 case-study verdicts fail (Arrays and Quicksort 84, HashMap 145) and two tour ones (`Splitting.Double`, which now clones, and `InPlaceTrees.SizeInsertRw`, whose keys are now `Word`s). The case-study blocks are checked with moves off (`Ochr.Test.preD53`, applied by `run` and by `lake exe tests`): reads there copy, as before D53. The tour, the ledger and the fuzzer run D53 as the default. A lane removes its block from `preD53` once the block checks with moves on. The pre-pass assertion ignores D53's switches, so it covers the case studies too.

*Pre-pass fixes found on the merged suite and by fuzz-port's R8.* Each was a place where the old after-the-fact reading and the declared-type reading disagreed, so the INTERNAL assertion fired (always fail-safe):
- A parameter bound to evaluate a Π-type's codomain or to observe a closure (`convPi`, `convFnRun`, `fnClass`, `argHint`, `sortOf`, inductive parameters) had its proof flag hard-wired to false. It is now what its declared type says (P1). This fixed 13 `Quicksort` lemmas that pass a hypothesis `ht : Lt(t, n)` into a type (`Nth(…, ht)`).
- A proof applied is a proof: `declOf`'s `.call` reads a `.prop` head as `.prop`. Before, a called proof field (a field of `And` whose type is a Π into proofs) read as data. This was hashmap-port's `Destructuring.DCallField` and `HashMapResize.ResizeFind`, adopted from fd024cb2. Giving `placeDecl` the field's Π shape is not needed: a Π into proofs is itself a proposition, so `.prop` is exact.
- R8 (fuzz-port, 2,235 cases in 10⁶), which had three shapes:
  - A stuck block's parameter declared by an embedded type (`(Π(z0 : &Nat). ⊤ : Prop)`, or `.val T`): `propDecl` reads an embedded type's sort, which was syntactic where it was captured (D55).
  - A sealed program's `let c = ⋆`: the binding is a proof when its declared type is a proposition (`letIn`, P1).
  - Arms that are proofs of different shapes (a proof variable, a λ into proofs) agree on a proof (`agreeDecl`).
- A proof is never captured by `&` (D48 (1)). A stuck block whose arm writes a field of a matched proof, inside a proof, once took the proof by borrow (`h3 : &ExN`). It now takes it by value: a proof is `⋆`, and the field is a fresh value (D49 (3)) local to the match, which D45 allows only in a proof position.

*Regressions.* `Destructuring.DCallField`, and in `ErasureBySyntax` the four programs `R8Param`, `R8Lam`, `R8Field` and `R8Arms` (plus `ExN` and `RunP`). The fuzzer, on 3 × 10⁵ cases with moves off and 10⁵ with them on, finds no INTERNAL case; what remains is E (arm-local values, about 6 in 10⁵) and R6 (conjunction order, 2 in 10⁵). The fuzz harness now records parameter declarations as `checkFix` does. Without that, the harness's own direct path tripped the assertion.

957 verdicts: the tour 604, the case studies 353.

## 29. The arm leak (arrays-library): a refinement belongs to its arm

`restoreKeep` kept the whole table of abstract values' types (`absTy`) under D37. [Split] substitutes a refinement into every stored type, those included, so one arm's refinement of an OLDER value's type survived into its sibling arms. For example, after `n := Z`, a parameter `r : Slice(n)` had type `Slice(0)` in the arm `n := S m` wherever it was typed through its value: a closure capturing it (captures are typed by `valType`), or an inferred conjunct. Binding types were restored correctly, so a direct use of `r` saw the right type.

*It was unsound.* `ArmLocalBoom.T7` states that every slice is the empty one. In the arm `n := S m` it applies a closure that captures `r` and sees `r : Slice(0)`, and `EmptyEq` proves any `Slice(0)` equal to `MkSlice(N0)`. At `T7(1, MkSlice(S0(9)))` the statement computes, by injectivity and disjointness, to `False`, and before the fix `BoomLeak : False` was accepted. fuzz-port's reading, that the leak could only reject, missed the closure route.

*Fix.* `restoreKeep` keeps only the types of abstract values created by the nested run: `saved.absTy ++` the new suffix. D37 is about fresh names and generalisation records, not about refinements of existing types.

*The re-audit of the rest of what `restoreKeep` keeps.* The question for each field: can a nested run refine an existing entry, not just add one?
- `nextAbs`, `nextLoan`, `fuel`: counters.
- `neutrals`: only grows, and no entry is rewritten in place (substitution does not reach it).
- `recStack` candidates: merged by uid (§20); substitution does not reach them.
- `classCache`: keyed by the Π-type value. Its reading is syntactic and depends on a captured abstract value only through whether its type is a sort, which no substitution changes.
- `constDecls`: keyed by global name, over fixed declared types.
None needs changing.

*Regressions (08CaseSplits).* `ArmLocal` is arrays-library's repro; `Leak` there is a true lemma the stale type rejected, now accepted. `ArmLocalBoom` has `T6`, `T7` and `BoomLeak`, now rejected: `T6`'s closure body says `Eq (Slice(0)) r …` with `r : Slice(S m)`. The fix has no switch: it is the implementation of [Split] as RULES states it (each arm from the same Ω, stored types included), not a new rule.

978 verdicts.

## 30. D35's four after-the-fact switches deleted

These are the lead's decision on §23, and I extended it to the fourth clause. D35's clauses were:
- a function's class read from its codomain term (`classBySyntax`);
- a stuck block erased iff each arm is (`blockRule`);
- `let`, `;` and `match` erased iff they are proofs (`seqByProof`);
- [Close]'s row read from the declared codomain (`rowByDecl`).
Each flipped nothing: the first three since the erasure pre-pass, and the fourth since D59. Their switches and ledger rows are gone.

The row "P1 together with the computed-type block rule of P2" (`blockRule := 1, leafRule := 0`) is gone too. It flipped exactly what P1 alone flips, so without `blockRule` it would be P1's row twice.

The code keeps each clause's default reading:
- `fnClass` reads the codomain term;
- a stuck block's class is given at its call;
- the old classification reads a sequencing form as a proof iff it is one;
- `callFn` reads [Close]'s row off the declared codomain.

The witnesses (BoomL, Boom8, Direct8, LieB, BoomB, Lie7, Boom7, TruthB, SeqT) stay as regressions. The panic under `seqByProof := false` (arrays-library's note, item 6) went with the switch.

*Rows that still flip nothing (class `subsumed`, pending decisions):*
- D19: its witness falls to [Drop] since D59;
- D54: the D54 Pow test (§31) decides it.

49 rows: soundness 18, false lemma 1, model 4, policy 2, subsumed 2, cost 1, completeness 21.

## 31. D54 stays: the Pow test finds its witness

The lead asked whether the pre-pass subsumes D54. The pre-pass reads a call's class from the declared type of its head. A variable whose declared type is a Π-type *as written* (`f : Π(x : &Nat). Prop`, reviewer-5's `Boom`/`BoomI`) reads the same on both paths, and that is why the row flipped nothing. A variable whose type is a Π-type *only by computation* is different. For `p : RefPred(0)` with `RefPred(n) := Π(x : &Nat). Prop` (the existing `Functions.Pow(X)` has the same shape without the borrow), the declared term says nothing. In a typed run the binding's stored, evaluated type is read (`refineDecl` on `A`), but an untyped run (a body called to compute a value: `runBody`) has no stored type. There the reading falls back to the value the variable holds:
- at the generic call, an abstract value of type `Π(x : &Nat). Prop`, which returns types, so `p(&c)` is erased;
- at the instance, `H`, which returns data (`P0`), so `p(&c)` runs.

With D54 off, `H` is accepted at `RefPred(0)`, and `RunPowGen(H)` has type `Id Nat (RunPow(H)) 0`, which computes to `False`: `Functions.BoomPow : False` is accepted. D54 is soundness again, with witness `BoomPow`.

*Why not read the stored type in untyped runs instead?* That would erase `H`'s write whenever it is called through a `RefPred(0)`. Compiled code runs it, so the checker's value of `RunPow(H)` (0) would differ from the program's (1). The class belongs to the value's type, and D54 makes conversion respect it. That is the right fix, not a different reading.

`subsumed` is now only D19's row. 49 rows: soundness 19, false lemma 1, model 4, policy 2, subsumed 1, cost 1, completeness 21. 982 verdicts.

## 32. R6: `Id`'s owners in a canonical order

`footprint` sorted the owners by their position in Ω. Closing off a match changes that order in two ways:
- a sealed program binds its captures in its own order, and a borrow parameter's cell is not where the caller's is;
- a captured place that an arm writes becomes a borrow parameter, so its plain reads become reads through a borrow, which the footprint counts.

The same `Id` then computed to conjunctions in different orders on the two paths, and `And` is not commutative by conversion.

The order is now canonical, by syntax: first the owners of the places the two sides write or borrow, in the order they first occur; then those reached only through a borrow-typed variable. Duplicates are dropped.

- *Regressions* (`Owners`):
  - `IdOrder`, fuzz-port's `R6Order.Direct`, a true statement that was rejected; it is now accepted;
  - `OrderSwapped`, the opposite order, which was accepted and is now rejected;
  - `OrderAtZero`;
  - `IdOrderRead`, the fuzzer's shape where a read of a written place came first once closed off.
- *Fuzzer:* 3 × 10⁵ cases with moves off show no conjunction-order finding. Before, there were 2 in 10⁵.
- `Scratch/R6Order.lean` still carries its old expectations: `Direct` is marked as a rejection and `Swapped` as an acceptance.

986 verdicts.

## 33. arrays-library's two completeness findings

These are items 1 and 4 of `notes/arrays-library.md` §10's list of checker findings.

*A Π-type whose body uses a proof captured from outside it.* The case is a Π formed by a function's body, e.g. `CapOf(n, h) := Π(u : Nat). Eq Nat (Get(n, h)) n`. At a use `c : CapOf(n, h)`, the type is computed by running `CapOf`'s body untyped (`runBody`). There `h` is `⋆` with no stored type, so `capture` could not record it (D51 inlines a captured proof as `(⋆ : T)` only when it knows `T`). Calling `c(0)` evaluates `Get(n, h)` in the codomain, typed, and failed with "cannot infer the type of the value ⋆". A Π written in a signature was fine, since its captures come from typed bindings.

Fix: when a body forms a function or Π-type (`Term.formsFn`), `runBody` evaluates the declared types of its proof parameters, at the arguments, on a private copy, and binds them with those types. The types are evaluated when the parameters are bound, as types are formed once (P2). Only proof parameters are typed, and only when something may capture them, so the case studies' check times are unchanged (Quicksort 283 ms against 271 ms).

A `let`-bound proof in an untyped run is still untyped. No program here needs it.

*Re-normalisation inside Π-types.* `renormV` handles sealed programs, constructors and inductive types, but it returned closures and Π-types unchanged, while `substV` reaches into both. After a split generalises a sealed program, another sealed program that re-derives it (`⌈G(σ)⌉`, where `G` computes `F(n)` inside) is re-normalised (G1). As a capture of a Π in the goal, it stayed stale: `RenormPi.InPi`'s goal kept `κ1 = ⌈G(σ0)⌉` after `F(n) := 0`.

Fix: `renormV` re-normalises the captures and embedded values of closures and Π-types, and also `&T` and inductive values' parameters. `renormT` walks every term form, as `substT` does. RULES already says re-normalisation reaches inside closures and types; the checker now matches it.

*Regressions:*
- `Snapshots.Get`, `CapOf`, `UseCapOf`;
- a new block `RenormPi` (08CaseSplits): `F`, `G`, `Plain`, `InPi`, `InConj`. `Plain` was already accepted.

Both fixes were confirmed by reverting them: `UseCapOf` and `InPi` are rejected without them.

994 verdicts.

## 34. R1's residual: an `Id` owner reached through a returned borrow

This was fuzz-port's last R1 case (1 in 10⁶; `Scratch/R1Residual.lean`). A sealed program's re-run forms `Id Unit (*x0 := *a6) ()`, where `a6 = RetSub(x1)` is a borrow returned by a stuck call. The owner of `*a6` is the re-run's cell `c2`, bound by an untyped `let`, which at that point holds `loan_ℓ`. The loan's borrow sits inside the stuck call's sealed arguments, where `findBorrow` does not look, so `valType` could not type the cell.

`idType` now observes first, then types each owner:
1. by its binding's type;
2. else by its content;
3. else by what the observation read from it, after every borrow had ended.

A place keeps its type across writes, so any of the three readings is the owner's type.

Regression: `Owners.RetSub` and `IdThroughRet`, the true statement once rejected.

996 verdicts.

## 35. D53 off by default until acceptance (the lead's inversion)

fuzz-port's execution oracle runs accepted data functions at ground inputs, with reads moving. It found programs that the checker accepts with D53 on and that go wrong when run: 15,567 in 10⁶ on 55977f8e. The causes are M1, M2 and M2b (stuck blocks hide their arms' moves) and M3 (erased code read at runtime depth). So ochr-core's default must not have D53 on.

`Config.d53` (default false) gates D53: `movesOn`, `ghostsOn` and `fnRuleOn` are `d53 && …`. `moves`, `ghosts` and `fnRule` still switch its parts, for the ledger. `Ochr.Test.d53Blocks = ["Moves"]` is checked with `d53 := true`.

`Moves` is the Borrows file's D53 section, split into its own block. It also holds `Functions.RetMoved` (shape (c)) and `ClosingOff.BlockReads`/`BlockMovesField` (shape (a)), since those regressions mean nothing with D53 off.

Everything else, the case studies included, reads by copying. The tour's `clone`s and `Word`s are harmless there. With D53 off, no verdict outside `Moves` changes.

The D53 rows are measured on `Moves`:
- `moves`: the same 8 programs, now `Moves.*`;
- `ghosts`: `GhostRead` only (the `CurrentState` programs are no longer checked with D53);
- `fnRule`: `CallTwice`, `ClosureClones`, `ClosureCopy`.

The unit tests' expected sealed programs no longer end in `peek`.

The fuzzer defaults to D53 off, and `--switch +D53` turns it on.

When M1, M2, M2b, M3 and RN are fixed and the execution oracle shows no findings in at least 10⁵ cases, `d53` becomes true by default. The tour flips first, then the case studies as their lanes adapt.

`preD53` is gone.

## 36. D19 is soundness again; the `subsumed` class is gone

fuzz-port found two D19 witnesses without a `Unit` call (`Scratch/D19Witness.lean` on ochr-fuzz-v2, `--diff --switch D19`). Both are now in `Borrows`, next to `BadA1`:
- **`V`**, the primary witness, makes no call: `let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0`. The stuck block returns a borrow of `n0`, so `n0` holds a sealed program with that borrow's loan inside. Reading `n0` must end the borrow, which is D19's "loans inside the content". Without D19, `V` is accepted, and `V(0)` writes through an ended borrow.
- **`W`** (with `G2`) is [Close]'s precondition. It passes `&a`, holding `r`'s loan inside, to a stuck `Nat` call. The result goes to `out`, which is declared before `r`, so `r` dies first and [Drop] never sees the loan. Without D19, `W` is accepted and `W(1)` overwrites `a` while `r` borrows inside it.

The D19 row is soundness (going wrong when run), with witnesses `V` and `W`.

With it, no row flips nothing, and the `subsumed` class is removed. `classOk` now requires every row to flip something, and every non-completeness row to name a witness. These are the ledger's invariants: every rule is needed, and a rule that flips nothing is deleted.

49 rows:
- soundness 20;
- false lemma 1;
- model 4;
- policy 2;
- cost 1;
- completeness 21.

1001 verdicts.

*RULES numbering:* the D53 draft's "P3 Reads move…" replaces the old P3 ("Data is copied, borrows are moved"). D53 is that principle's change, so there is no collision. RULES states D53 as the rule; the checker applies it only in `Moves` until acceptance.

## 37. The D53 acceptance mechanisms (fuzz-port's execution oracle)

fuzz-port's execution oracle runs accepted data functions at ground inputs, with reads moving. It found 15,567 programs in 10⁶ that the checker accepts and that go wrong when run. The principle behind every fix below is that a closed-off block's effect on its captured places equals the direct path's, moves included, and that whether a computation is a runtime one depends on where it runs, never on the code path the machine takes to run it.

- **M1: a move of a field the arm's pattern exposed was lost.** `splitArmsThenClose` took `before` from the unrefined `σ`, which has no fields, so `newHoles` found nothing.
  - `before` is now taken per arm, after the refinement.
  - A moved place that does not exist in the closed-off (unrefined) state is mapped into it (`movedPlace`). If it runs through an abstract value of a single-constructor type, that value is refined to its constructor, which is total, like a split with one arm. So `q0.1` is moved in and `q0.2` stays. Otherwise the longest existing prefix is moved in: `n0`, since its predecessor exists only in one arm.
  - `A1` and `A2` are now rejected; `A3` stays accepted.
- **M2: a moved capture that is not a whole variable** (`*x0`, `*x1`) stayed a read-in-place capture. A capture that some arm moves out whole is now moved in (mode 2). `B1`, `B2`, `B3` are rejected.
- **M2b: one arm moves a borrow into the block whole and another moves out through it.** The block's frame ends that borrow partly moved. `splitArmsThenClose` records, per borrow variable, which arms moved it whole and which left it holed inside, and rejects the block if both happen. `B4` is rejected.
- **M3 (i): the untyped `J` read its endpoints at runtime depth.** `J`'s type, endpoints and motive are now evaluated erased on both paths. `J1` and `J1Run` are accepted.
- **M3 (ii): an `Id` side writing a moved place.** It was already fixed by §34 (owners are typed by what the observation reads). `I1` and `I1Run` are accepted.
- **RN: a split in a data function re-ran a type's sealed program as code**, so the program's reads moved. `substEnv`'s stored types, `absTy` and goal, and `renormAll`'s goal and stored types, are now re-normalised erased. `DataSplit` is accepted.

*Regressions.* All twelve are in `Moves`: `A1`, `A2`, `A3`, `B1`–`B4`, `J1`, `J1Run`, `I1`, `I1Run`, `DataSplit`.

*Ledger.* The `moves` row gains `A1`, `A2` and `B1`–`B4`. The `ghosts` row gains `J1` and `J1Run`: without ghosts, the erased endpoint reads `⊥`.

*Cost with D53 off.* The per-arm comparison of captured values runs in full only with D53 on. Without D53 only a whole move can happen, and `newHoles` returns early on a value with no hole. Check times match the previous head up to machine load: with a load average of 16, every block was about 1.4× slower, uniformly.

*With D53 on everywhere:* the tour has no failures. The case studies have 225, all of them missing clones or `Word`s, as before; Quicksort's count is 48, down from 52.

1013 verdicts.

## 38. The D53 flip (branch `ochr-d53-on`, pending acceptance)

This branch is prepared to be merged once fuzz-port's acceptance run passes: the execution oracle with D53 on, zero findings over at least 10⁵ cases. It changes three things:
- `Config.d53` defaults to true;
- `Test.d53Blocks` is replaced by `Test.preD53`, the case-study blocks, which are checked with `d53 := false` until their lanes adapt them;
- the unit tests' expected sealed programs end in `peek` again.

The tour has no failures with D53 on.

The ledger's D53 rows now range over the whole tour:
- `ghosts` gains the three `CurrentState.AddSub*` proofs;
- `fnRule` gains `Equality.Om`, the `Functions.Twice*` family, and the trees' `Size`/`SizeInsert`, which call a closure twice.
## 39. A block's moves as effects by place (N1, N2, N3)

After §37, fuzz-port's acceptance run on 10a7861a fell from 1,608 execution findings to 104 (seed 1). Three shapes remained, and they share one cause: a block's moves were recovered by diffing values before and after each arm, and that fails whenever the values are abstract or sealed.
- **N1:** an inner block's move was invisible one level up, because the outer arm's `x0` was still abstract.
- **N2:** a borrow moved in whole, but only by the syntax of a dead inner arm.
- **N3:** the owner `q1` had mixed modes: `q1.1` moved and `q1.2` lent. [Close] sealed `q1` whole and hid the move.

*The mechanism now (one, replacing the diff):*
- **Every move and assignment is logged by place** (`placeLog`, at the root binding's position; `logEffect`), in any configuration. A step through a local borrow (`let r = &q0; *r…`) is logged as the owner's too (`throughLocalBorrow`); that is needed only with D53 on.
- **An arm's effect on the block's captures** is its log replayed in order (`armMoves`). A move adds its place. An assignment restores every moved place it covers, so a move the arm undoes is not a move.
- **Nested blocks compose** because an inner block's effect on its captures happens through its arguments, which the outer arm's log records like any other move.
- **Captures take modes per sub-place.** A capture part of which some arm moves out is split into its fields. Each field is captured by its own mode: move, `&`, or read in place; fields the block never uses are left out. The block's matches on the split place take the arm of its constructor (`Term.selectArms`). If the place is used whole other than as a scrutinee, or its content is not a constructor value, it is moved in whole.
- **M2b is read from the capture modes.** A borrow variable the block moves in whole is ended by the block's frame. If any arm moves out through it and does not restore it, that is an error. The capture's mode comes from syntax as well as from the log, which covers N2's dead inner arm.

*Regressions (`Moves`):*
- rejected: `N1`, `N2`, `N3`, `ThroughLocal`;
- accepted: `N3Other` (the same block without reading `q1` afterwards) and `MoveRestore`.

*Unchanged:* the suite's other verdicts, with D53 off by default and with it on everywhere. With D53 off the log costs nothing measurable: interleaved runs against 10a7861a give Quicksort 288 ms against 286 ms.

1019 verdicts.

## 40. The last residue at 10⁶ (P, Q, K)

fuzz-port ran 10⁶ cases on 0b8a68f0 with D53 on. Ten cases remained, down from 950 on 10a7861a, with no value disagreements. They fall into three shapes (`Scratch/D53Residual2.lean` on ochr-fuzz-d53acc2).

- **P (7 cases): a borrow whose content is already partly moved out, passed to a call that closes off or to an erased call.** [Close] seals the borrowed content, which hides the hole. An erased call's writes vanish at runtime. So neither kind of call can make the content whole before the borrow ends.
  - [Close]'s precondition now includes it: a borrowed argument's content must be whole.
  - A call of class ≠ 0 checks the same (`wholeBorrowArgs`), at runtime depth only.
  - A call that runs may still refill the borrow (`TakeRefill`: `let v = *x; Refill(x, v)` is accepted).
  - Regressions: `P1` (a stuck `G1`) and `P2` (an erased `F5` in an arm).
- **Q (2 cases): a closure in an arm moves `q0` whole, to capture `q0`'s field `q0.1`.** Closures capture variables. The block had captured `q0.1` alone, so the move of `q0.2` was lost. A place that some arm moved out whole and that is a strict prefix of captures now replaces those captures, and is moved in. Regression: `Q1`.
- **K (1 case): the same field written two ways.** One arm moves `a4.2`; another inspects `a4`, whose pattern fields are `fst`/`snd`. The split of `a4` into its fields did not recognise `.2` as `snd`. Places are now compared up to `stepEq` (`placePrefix`, `placeEq`): a pair's `.1`/`.2` are its constructor's fields. A Nat's `.1` is never a pair's field, so the two readings cannot meet. Regression: `K1`.

1028 verdicts. With D53 on everywhere the tour still has no failures, and check times are unchanged (Quicksort 280 ms).

## 41. The flip's pre-pass assertion; R9 (arms of different classes)

*The assertion was off on `ochr-d53-on` (found by fuzz-port).* `Config.prePassAssert` normalised `d53 := false` and compared the result with `{}`. On the flip branch `{}` has `d53 = true`, so no configuration asserted. The normalisation now uses the default's own value (`d53 := ({} : Config).d53`), so the same code is right on both branches.

*R9 (fuzz-port; it is also on `b2ce75b5`, with and without D53).* Take `match 0 { Z => refl, S _ => 0 }`: a match whose arms differ in class, a proof in one arm and data in another. `agreeDecl` read it as data, but the run took the proof arm, so the INTERNAL assertion fired. That is fail-safe. On the flip, with the assertion off, it surfaced as a D41 error on a refined generic path.
- Such a match runs only on a known scrutinee. A stuck match's arms must have one type.
- A known scrutinee is the same on every path, so the arm it takes is too.
- Arms that disagree on being a proof therefore say nothing (`.any`), and the match's erasure is that of the arm it runs.

I also tried rejecting such matches statically. That is a D55-style check that arms agree on being a proof. It rejected no program in the suite. But with D42 off, `refl` is not a proof, so every proof by recursion with a `refl` arm has arms that disagree, and the D42 rows would have gained dozens of flips that belong to the check, not to D42. So I chose deferral.

*Regressions:* `ErasureBySyntax.R9Arms` and `R9Nested` are accepted. fuzz-port's `R9PrePassArms` (`B`, `B6`) is accepted with and without D53.

1030 verdicts.
