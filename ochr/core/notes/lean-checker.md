# lean-checker: an executable checker for RULES v1.5, and what running it found

**Verdict:** RULES v1.5 is implemented, extended to user-declared inductive types (lists, binary trees), and 185 verdict assertions all hold. Every §7 example (E1–E5) is accepted. Every must-fail program and every attack from rounds 1–2 is rejected: e346 `Bad`, `Oops2`, `Loop`/`Bot'`; meta-model C1, C2; breaker-close A1–A4 (and A5 terminates); breaker-close-v1 N1 and meta-model-v1 R1 (the closed proofs of false built from `T` and `Q`); breaker-frame attack 1; E5's three rejections. Each is caught by the rule meant to catch it: switching that one rule off flips exactly the verdicts it guards (§5).
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

## 2. Verdicts (expected vs actual: all 139 as expected)

| Program | Declarations (A = accept expected, R = reject expected) | Result |
|---|---|---|
| E1 | AddM, AddMZero, Add, **AddZero** (`S p => AddMZero(&p)`, no cong), AddZero' (`AddMZero(&x)`): all A | as expected |
| E2 | AddM, TailM, AddM', AddMEq, AddMEqOwned, AddM1, TailNoop: all A | as expected |
| E3 | AddM, AddMZero, **AddToOne** (inline, closed off), AddToOne', Pick, AddToOne'', AddToOneZero, AddToOneZero'', AddToOneZeroInline: all A | as expected |
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
| D17: [Rec] entry-value guard | Loop, Bot', Loop2, Spin, KnotL, KnotLBoom, Probes.OuterBad → accepted |
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

## 10. Not done

A proof that the implementation matches the rules (the traces and the ledger are the evidence); universe checking beyond C15; `Bool` (Nat stands in); loops, shared borrows, borrows in data (D8); the separate meta-lean development (`ochr/core/meta-lean/`, another agent's).
