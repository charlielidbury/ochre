# lean-checker: an executable checker for RULES v1, and what running it found

**Verdict:** RULES v1 can be implemented as written, given seventeen clarifications and three fixes (§1, §3). Every §7 example (E1–E4) is accepted. Every round-1 attack is rejected: e346 `Bad`, `Oops2`, `Loop`/`Bot'`; meta-model C1 and C2; breaker-close A1, A2, A3a, A3b; breaker-frame attack 1. Each attack is caught by the rule meant to catch it, as the counterfactual ledger (§5) shows.
**Most important finding:** v1 is unsound as written (L1). [Rec] inspects only recursive *calls*, so a function that passes *itself as a value* to a helper (`Knot x := Apply(Knot, x)`) never makes one. It is accepted at any type, and `Knot(0) : Eq Nat 0 1` is a closed proof of ⊥. Because of P5, nothing even loops.
**RULES.md must change:** [Rec] needs the head-only clause (L1) and must cover nested closures (L3). The argument check must be read on values: an argument that is `⊥` at the call point is an error (L2). §3 lists seventeen clarifications, two of which change verdicts (C5, C8). D18 (owners are sets) protects nothing that v1 lets you write (§4).
**Confidence:** high that the verdicts are what the implementation computes: each is an assertion in a green build, and the traces reproduce the round-1 hand derivations symbol for symbol. Medium that every clarification in §3 matches the intended reading.
**Not checked:** metatheory; universe levels beyond `Type_i : Type_{i+1}`; completeness beyond the examples; performance beyond the examples (the whole suite, including the ledger's runs of 9 programs under 9 configurations, takes seconds).

Code: `ochr/core/lean/` on branch `ochr-core-lean` (README: build, rule → function table). Build: `lake build`. Table and ledger: `lake exe tests`. Trace any definition: `(run "E1" E1 { trace := true }).showTrace "AddMZero"`.

## 1. Bugs in RULES v1 (concrete failing runs)

### L1. [Rec] misses a function that uses itself as a value (closed proof of ⊥)

breaker-close's summary lists this as A4, but its note was cut off before A4 was written up, and v1's [Rec] does not cover it.

```
def Apply (f : Π(x : Nat). Eq Nat 0 1) (x : Nat) : Eq Nat 0 1 := f(x)
def Knot (x : Nat) : Eq Nat 0 1 := Apply(Knot, x)
def KnotBoom : Eq Nat 0 1 := Knot(0)
```

With fix L1 switched off (`Config.selfHeadOnly := false`), the checker accepts all three (ledger row L1):

```
[Def] Knot: generic call x ↦ σ0; goal Eq Nat 0 1
  Apply(Knot, x)        // [Call-type]: Knot : Π(x : Nat). Eq Nat 0 1 is Apply's parameter type; the result type is Eq Nat 0 1
                        // [Rec]: the call's head is Apply, so there is no recursive call to check
                        // P5: Apply's result is a proposition, so the call is not run and nothing loops
  Eq Nat 0 1 ≡ goal ✓
[Def] KnotBoom: Knot(0) : Eq Nat 0 1 ✓      // closed proof of ⊥
```

Before v1, the checker would loop instead (as with e346's `Bot'`). P5 turns this into a clean closed proof. **Fix (implemented):** in the body of `fix f`, `f` occurs only as the head of a call, so every use of `f` is a call that [Rec] sees. With the fix, Knot is rejected with `[Rec] Knot occurs in its own body other than as the head of a call`.

### L2. An argument can be `⊥` at the call point (a borrow-checker hole)

In `f(&x, x)`, reading `x` for the second argument ends the borrow already evaluated as the first ([Access]), so argument 1 is `⊥` when the call is made. v1 lists "an argument not of the parameter's type" as an error, but a checker that compares *inferred* types (`&x : &Nat`) lets it through. With the check switched off (`argNotBot := false`):

```
def Dead (f : Π(a : &Nat) (b : Nat). Unit) (x : Nat) : Unit := f(&x, x)   // accepted: f is abstract, so [Close] builds ⌈σ_f(⊥, x)⌉
def W7 (a : &Nat) (b : Nat) : Unit := *a := 7
def RunDead : Unit := Dead(W7, 0)                                         // its concrete run goes wrong: "no such place *a: its path does not exist in ⊥"
```

A well-typed program goes wrong. **Fix (implemented):** read the argument check on values, so an argument that is `⊥` at the call point is an error. `f(&x, &x)` is caught the same way. `f(x, &x)` is fine.

### L3. [Rec] must cover recursive calls inside nested closures (clarification; an early version of this checker was unsound here)

```
def KnotL (x : Nat) : Eq Nat 0 1 := let g = (λ(y : Nat) : Eq Nat 0 1 => KnotL(y)); g(x)
```

The recursive call sits inside a λ, and [Def] checks that λ at its own generic call. If that check starts with an empty [Rec] context, which is what my first version did, `KnotL(y)` is not recognised as recursive, `KnotL` is accepted, and `KnotL(0) : Eq Nat 0 1`. v1 read literally forbids this ("in the body of fix f, each recursive call…"), and the nested λ's body is inside the body of `fix KnotL`. Still, an implementer who takes [Def]'s "fresh environment" to mean a fresh check will get it wrong, so RULES should say it. **Implemented:** the checker keeps a stack of [Rec] contexts, one per enclosing function being checked, plus the refinements made so far. A recursive call anywhere is checked against its own function's entry values. `y` is the λ's fresh parameter, not a subterm of `x`'s entry value, so `KnotL` is rejected. A structural call through a closure (`AddZeroC` in `Attacks.lean`, which captures the predecessor `q` of the split parameter) is accepted.

## 2. Verdicts (expected vs actual; all 105 as expected)

| Program | Declarations (A = accept expected, R = reject expected) | Result |
|---|---|---|
| E1 | AddM A, AddMZero A, Add A, AddZero A (`cong S`) | all as expected |
| E2 | AddM, TailM, AddM', AddMEq, AddMEqOwned, AddM1, TailNoop: all A | all as expected |
| E3 | AddM, AddMZero, **AddToOne A** (inline, closed off), AddToOne' A, Pick A, AddToOne'' A, AddToOneZero A (natural proof, no refl padding), AddToOneZero'' A, AddToOneZeroInline A | all as expected |
| E4 | AddM, AddMZero, Twice, TwiceNoop, TwiceM, TwiceMMove, TwiceMZero, TwiceMZero' (modular proof with `trans`): all A | all as expected |
| E6 | UseMoved R, UseReborrowed A, LemmaMoves R, WriteThenRefl R, WriteThenRefl' R, ZeroIsOne R, Add01 R, NotAdd01 A (its negation), Snapshot A, SnapshotLie R, DanglingLocal R, DanglingTail R, DanglingReborrow R (+ AddM, AddMZero, TailM A) | all as expected |
| Attacks | e346 Bad R, Oops2 R, Loop R, Bot' R; breaker-close Loop2 (A3a) R, Spin (A3b) R, BadA1 (A1) R; meta-model C1: FP2 A, Boom R, BoomIsTrue A, Boom' R; C2: G R, BadC2 R (+ P1, P2, F, Pick, G1 A); L1: Knot R, KnotBoom R; L3: KnotL R, KnotLBoom R, AddZeroC A (+ Apply, Add A) | all as expected |
| More | MatchAfterOpaque A (E4.3), Dead R, DeadTwice R, NotDead A, g A, attack R, attack' R (breaker-frame 1), NonTailRec A, StuckGoal A, StuckGoalSplit A, StuckGoalWrong R, AddMZeroLet A | all as expected |
| Probes | T, UseT0, UseT, DepMatch A, DepMatchWrong R, Outer A, OuterBad R, Cap A, CapMut A, AliasRead A, AliasDangling R, Lemma, W5, EffArg A, WriteInBlock A, AliasAfterBlock R, MovedByBlock R, ReborrowInBlock A | all as expected |
| D18 | Pick A, Probe A, Use R (checks that the error message's expected type has one conjunct per owner) | all as expected |

The rejection reasons are the intended ones: e.g. `Bad` has type `Eq Nat σ0 0` (pre-split, D15), `Oops2` has type `Eq Nat σ0 0` (captured at formation, D13), `Loop` fails `[Rec] … at Loop(borrow_1 σ0, σ0)` (entry value, D17), `BadA1` fails at `*r := S Z` because moving `b` ended the reborrow `r` (D19), C2's `G` is rejected because its result type is a Π that captures the borrow `z`. `lake exe tests` prints every reason.

The traces reproduce the round-1 derivations symbol for symbol. For example, AddMZero's goal is `Eq Nat ⌈let c1 = σ0; AddM(&c1, 0); c1⌉ σ0`, the Z arm reduces to `⊤`, and the S arm's goal and the induction hypothesis are both `Eq Nat (S ⌈let c1 = σ1; AddM(&c1, 0); c1⌉) (S σ1)`. AddMEq's are both `Eq Nat (S ⌈let c1 = σ2; AddM(&c1, σ1); c1⌉) (S ⌈let c1 = σ2; let r = TailM(&c1); *r := σ1; c1⌉)`, which is deriver-e2's `S A(σ',τ)` against `S B(σ')[τ]`. E3's inline `AddToOne` closes off into exactly e346's `Pick` backward function in source syntax: `⌈let c1 = σ1; let c2 = σ2; let r = (fix _ (b : Nat) (x1 : &Nat) (x2 : &Nat) : &Nat := match b {…})(σ0, &c1, &c2); *r := loan_k; c1⌉`.

## 3. Clarifications: where v1 is ambiguous, and the reading implemented

For each: the rule, the ambiguity, the choice, and whether another choice changes a verdict.

- **C1 [Rec] "the recursive position".** v1 never says which parameter it is. *Choice:* inferred. The candidates are the parameters whose entry value is an abstract `Nat` (through the borrow for `&Nat`), and a candidate survives a recursive call if that call's argument is a strict subterm of its entry value as refined so far. The check fails at the first call that leaves no candidate, before that call is run. Failing late gives the same verdicts but is not safe: with P5 off, running a non-structural recursive call to find out first does not terminate (breaker-close A3a/b did that). *Verdicts:* none change, as long as the position is not declared wrongly by hand.
- **C2 Type formation effects.** v1's P2 says a type is evaluated once, against the current Ω, but only `Id` says "on its own copy". *Choice:* every type former (`Eq`, `Id`, `Π`, `&`, `×`, `∧`, binder and result types, [Call-type]'s `B`) is evaluated on a private copy of Ω, as v0's P2 said. *Verdicts:* none in the suite. Otherwise `let T = Eq Nat (AddM(x, 0); 0) 0; AddM(x, 1)` would be rejected, because forming `T` moves `x`.
- **C3 Closures and Π-types capture by value, never a borrow.** Following D13 and RULES §1. A Π-type (or λ) whose body mentions a borrow variable is an error, even when only `*x` is read. *Consequence:* meta-model C2 cannot be stated (its `G` has result type `Π(e : Id Unit (*z := 0) (*z := 1)). ⊥`, which captures `z`), and hypotheses such as `h : Π(_ : Unit). Id Nat (*x) 0` about a borrow parameter cannot be written. Capturing the *content* of a read-only `*x` instead would make C2 statable, and then D18 would matter (§4).
- **C4 The type of a non-tail match.** v1's stuck-block rule needs a result type for the anonymous function, and v1 does not say where it comes from. *Choice:* check the arms under their refinements; they must have the same type, which becomes the anonymous function's result type. Otherwise reject, with a message saying v1 leaves this open. *Verdicts:* none in the suite. A match whose arm types differ only through the refined `σ` (e.g. `Z => AddZero(n) | S _ => AddZero(n)`) is rejected, and would need an annotation (e346 F1's proposal).
- **C5 How a stuck block takes a borrow variable.** "Borrow variables it uses … become borrow arguments" could mean *move* `x` or *reborrow* `&*x`. *Choice:* move if some arm moves it, reborrow otherwise. Written owned variables are passed as `&x` (and the body's places `x…` become `*x…`); read-only ones by value; parameters in frame order. **Verdicts change.** Always reborrowing accepts `let r = match b { Z => x1 | S _ => x2 }; AddM(r, 1); AddM(x1, 2)`, and its concrete run `RunIt` reads `⊥` (x1 was moved into `r` in arm Z). Ledger row C5 shows the flip. Always moving rejects `(match b { Z => AddM(&*x, 1) | S _ => () }); AddM(x, 2)` (Probes.ReborrowInBlock), which is fine in both arms.
- **C6 Stuck matches in type-level terms.** v1 closes them off, but the anonymous function needs a result type. *Choice:* same as C4 (arms checked under refinements, which also type-checks them).
- **C7 Proof irrelevance and P5 are one mechanism here.** Every value of a proposition is the single value `⋆`. That includes functions whose type is a proposition (`P2 : Π(x : &Nat). ⊤`) and Prop-typed globals and parameters. Calling `⋆` is always P5, since it has no body to run. *Consequence:* the C1 counterfactual cannot be run. Switching P5 off also switches irrelevance off (P1 and P2 become distinct closures), so `Boom` stays rejected, for a different reason. That is why the ledger shows P5 guarding `FP2`/`BoomIsTrue` rather than a closed ⊥. In the paper, "a proof carries no code" is the one-line reason both hold.
- **C8 [Split] on a neutral that is not `σ`.** After an opaque call, `*x` holds a sealed program. v1's [Split] only covers `σ`, and a match in checked code cannot be closed off with unchecked arms. *Choice:* generalise first: replace that sealed program everywhere (Ω, stored types, goal) by a fresh `σ`, then split. This is dependent elimination with a generalised motive, sound by meta-model §3.5, and possibly incomplete. **Verdicts change:** e346's E4.3 `f(&*x); match *x {…}` is accepted, and without this it is rejected (ledger row C8).
- **C9 Pattern variables are places.** `S y` makes `y` the sub-place `p.1` (the resolver substitutes it), so after a write to `p`, `y` names the *new* tail (Probes.AliasRead), and after `p := 0` it names nothing: "no such place" is an error (AliasDangling). This is what breaker-close A3b exploited; entry-value [Rec] (D17) is what stops it. It is surprising enough that the paper should state it.
- **C10 P5 erases the call, not its arguments.** `Lemma(W5(&*x))` evaluates `W5(&*x)`, which writes `*x := 5`, then does not run `Lemma` (Probes.EffArg proves `Id Unit (Lemma(W5(&*x)); ()) (*x := 5)`). The runtime must match this: erase the call, keep the argument computations. Erasing the whole application, as a pure language may, would disagree with the checker (e1 N2's failure mode).
- **C11 Values in flight are in Ω.** Evaluated arguments waiting for the next one, the right-hand side of an assignment, and a result while its frame is popped are all temporaries in the current frame, so [End] finds and substitutes into them. L2 is the case where this matters.
- **C12 `J`, `trans`, `symm`, `cong`.** `J A P h t` takes the endpoints `a, b` from `h`'s type `Eq A a b` and types the result `P(b)`, checking `t : P(a)`. If `h`'s type has already computed to `⊤` (reflexive, D16), the endpoints are gone. Then `a ≡ b`, so the result keeps `t`'s type (sound, since `⊤` only arises from equal normal forms). `trans` and `symm` are primitives, derivable from `J`. `cong f h` applies `f` to both endpoints by calling it.
- **C13 `λ` carries its result type** (`λ(x : A) : B => t`), because v1's λ is a non-recursive `fix` and `fix` carries `B`. (E4's `TwiceMZero` becomes `TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x)`.)
- **C14 No η for Unit.** An abstract `σ : Unit` is not `()`. [Close]'s Unit row makes stuck Unit *results* `()`, and nothing in the suite needs more.
- **C15 Universes.** `Prop = sort 0`, `Type_i = sort (i+1)`, `sort l : sort (l+1)`, and a Π's level is the `imax` of its parts, computed by evaluating the parts at generic arguments. Nothing else is checked (e.g. a product with a proposition component). `Type : Type` cannot be written.
- **C16 [Def] details.** A parameter whose type is a proposition gets the generic value `⋆`. A borrow parameter `x : &T` gets a cell `x° : T ↦ σ` in frame 0 and the argument `&x°`. The body runs in `[self, x̄]` over it. The function is not in scope in its own type.
- **C17 `Id` inside a callee's body.** Callee bodies run on the untyped machine, since they were checked when defined. An `Id` there observes without re-checking its sides' types, and an owner with no stored type takes its value's type. Example: `F (h : Π(x : &Nat). ⊤) : Prop := Id Nat (let a = 0; h(&a); a) 0` is called as a type-level function.

## 4. D18 (owners are sets) protects nothing that v1 lets you write

`multiOwner := false` (the single-owner reading) flips no verdict in the suite. D18 itself is implemented and tested directly. In `Units.lean`, `owners` of a hole that occurs in two owned places returns both. End to end, after `let r = Pick(n, &a, &b)`, the parameter type of `Probe(z : &Nat) (e : Id Unit (*z := 0) (*z := 1))` at the call `Probe(r, …)` is the two-conjunct equation over `a` and `b`, exactly meta-model C2's type, and it has one conjunct under the single-owner reading.

The only known attack (meta-model C2) cannot be written in v1. It needs the caller to *form* an `Id` type while the hole is in two owners and to *use* it after a split has removed the hole from one of them. In v1:
- the type must be formed as a hypothesis, i.e. as a parameter type of something applied later; with saturated n-ary calls (D10) there is no partial application;
- the only way to hold a hypothesis across a split is a Π-typed value, and a Π-type or λ that mentions the returned borrow `r` captures a borrow, which RULES §1 forbids (C3);
- a positive use of the single-owner type is harmless: it is *weaker* than the all-owner statement, so it is implied.

So in v1, D18 is needed by the model (T2c: [Call-type] is only an equivalence when the context is injective), but no checked program depends on it. If C3 is relaxed (Π-types that capture the content of a read-only `*x`) or currying comes back, C2 becomes statable and D18 is load-bearing again. Recommendation: keep D18, and cite C2 in the paper as the reason it exists, noting that v1's other restrictions currently block it.

## 5. The counterfactual ledger: which rule guards which test

Each `Config` switch turns off one rule. `Registry.lean` asserts that exactly these verdicts flip and nothing else (`lake exe tests` prints the ledger):

| Switched off | Verdicts that flip |
|---|---|
| P5 (D14): calls at a proposition are not run | E4.TwiceMZero' → rejected (e346 F8: the lemma rewrites `*x`); Attacks.FP2 → rejected (`P2`'s write becomes visible: `Eq Nat 7 0`); Attacks.BoomIsTrue → rejected (P1, P2 no longer identified; C7) |
| D18: owners are sets | nothing (§4) |
| D17: [Rec] entry-value guard | Loop, Bot', Loop2, Spin, KnotL, KnotLBoom, Probes.OuterBad → accepted |
| D19: [Access] ends loans inside the content | Attacks.BadA1 (breaker-close A1) → accepted |
| L1: self only as a call head | Knot, KnotBoom → accepted |
| L2: no ⊥ argument | More.Dead, More.DeadTwice → accepted |
| C8: generalise before splitting on a sealed program | More.MatchAfterOpaque (E4.3) → rejected |
| C5: move a borrow variable an arm moves into a stuck block | Probes.MovedByBlock → accepted (and its concrete run reads ⊥) |

Breaker-frame's attack 1 (a lemma for disjoint borrows applied to aliased ones) is blocked twice: by D19 at argument evaluation, and, with D19 off, by the path part of [Access] when the observation writes `*x`. No single switch flips it.

## 6. Other observations

- **Normal forms need no α-renaming step.** With de Bruijn terms whose binder names are ignored by `==`, and [Close] building `⌈L; C…⌉` in one fixed shape, the goal's and the IH's sealed programs are structurally equal whenever the round-1 derivations say they are "equal up to renaming" (e1 F7).
- **"Discard the partial run" is exception semantics.** `stuck` is an exception carrying only the fuel spent. The innermost call catches it with the state it had at the call point (arguments evaluated, not yet pushed), which is exactly [Close]'s restore. [Seal]'s head call rethrows instead of closing.
- **Loans are variables:** [End] is one substitution over Ω followed by re-normalising the sealed programs it touched. The same function implements refinement (`σ := S σ'`) and [Split] (then also over stored types and the goal). No pending bindings, no side conditions.
- **P5 makes the modular proof work** (TwiceMZero', e346 F8), and **generalisation (C8) makes matching after an opaque call work** (E4.3). Both were open in round 1.
- **Dependent pattern matching through a type computed by a program works** (Probes.DepMatch: `x : T(b)` with `T(b) := match b { Z => Nat | S _ => Unit }`; the split refines `x`'s stored type to `T(0) ≡ Nat`).
- **The syntax the paper can quote** is the `ochr { … }` block (README). E1 reads exactly as in BRIEF.md, with calls written `f(a, …)`.

## 7. Not done

J with a motive depending on the proof (irrelevant here: every proof is `⋆`); `Bool` (Nat stands in, e346 E3.0); universe checking beyond C15; a proof that the implementation matches the rules (the traces are the evidence); anything about loops, shared borrows or borrows in data (D8).
