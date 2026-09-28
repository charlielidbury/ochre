# breaker-fresh, round 2: attacks on RULES v1.6 and the v1.6 checker

**Verdict:** v1.6 is still inconsistent. I have four new closed proofs of a false proposition, and the executable checker (`ochr/core/lean` at `49f9108a`) accepts all four. X1 and X2 are two further forms of D28's two-path problem (erasure re-decided). X3 is a generalisation that escapes the private copy it was made in (D33 × D34). X4 is D30 identifying functions that return borrows into different arguments. There is also a checker non-termination (X5).
**Most important finding:** D28 fixed erasure for *top-level* calls only.
- A closure's class is computed from its Π-type *value*, including its captured values, so `Mk(n)`'s closure is data at the generic `n` and a type at `n = Z` (X1).
- A stuck block becomes a call to an anonymous function whose codomain is `Prop`, so it is erased. The same match run inline is a non-call term, so it is not erased (X2).
- The general rule: every classification must be a property of *syntax*, fixed when the enclosing top-level definition is checked.
**What must change:**
- (1) Erasure: decide it from the codomain or declared-type *term* (syntactically a sort → types; typed `Prop` → proofs; otherwise data), with no evaluation, and with one criterion for calls, closures, stuck blocks and inline terms.
- (2) Generalisation is a naming equation `σ_g ≡ ⌈n⌉`, so its record must be global, and fresh names must never be reissued (X3).
- (3) D30 must observe `&T` results through a hole (X4).
- (4) A neutral-headed head call inside [Seal] must stay sealed (X5).
- D34 itself, general inductive types and D30's circularity clause survived every attack I tried (§4–§6).
**Confidence:** high. Every derivation below is accepted by the checker: `Boom8 : Eq Nat 0 1`, `Boom7 : Eq Nat 1 0`, `BoomE : Eq Nat 1 0`, `Boom : Eq Nat 0 1 ∧ Eq Nat 1 0`. X2 follows from D28's text. X1, X3 and X4 exploit gaps in the text (closure identity, generalisations inside private copies, borrow codomains in D30) where the checker took an unsound reading.
**Not checked:** the paper's metatheory; mutual or nested inductive types; performance beyond X5.

Labels: X1–X5 are the findings of this round (named to avoid clashing with lean-checker's G1 and round 1's F1–F5).

Method: I read RULES v1.6 and D28–D34, and tested every candidate attack with the checker on a scratch copy of `ochr/core/lean` (in my scratchpad; nothing in the worktree was edited). The scratch files are reproduced verbatim below; each runs with `lake env lean <file>` in about 0.5 s.

---

## X1. A closure's erasure class depends on its captured values (closed `Eq Nat 0 1`, accepted by the checker)

D28: "a call `f(ā)` is erased iff `f`'s declared codomain, evaluated at `f`'s generic call, is a sort or has sort Prop, recorded at [Def] and reused at every call". For a top-level `f`, the record is keyed by its name. For a closure the rules do not say what the record is keyed by, and a closure's "generic call" binds its captured values, which differ from instance to instance. The checker keys the record by the Π-type *value*: `fnClass` evaluates the codomain of `tPi cs …`, with `cs` the captured values, and caches per value. So a λ whose codomain mentions a captured variable is classified differently in different contexts.

```
def U (n : Nat) : Type := match n { Z => Prop | S _ => Prop }
def V (n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }
def Mk (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
def Lie8 (n : Nat) : Id Nat (let c = Z; let g = Mk(n); g(&c); c) (S Z) := refl
def Boom8 : Eq Nat Z (S Z) := Lie8(Z)                       -- ACCEPTED
```
Trace (checker, `trace := true`):
```
generic Lie8, n ↦ σ0:  [Call-type] (λ … : U(κ1) …) where κ1 = σ0 (borrow_0 0) : ⌈U(σ0)⌉
                          → class "data": g(&c) runs, c ↦ 1, goal Eq Nat 1 1 ≡ ⊤, refl ✓
instance Lie8(Z):       [Call-type] (λ … : U(κ1) …) where κ1 = 0 (borrow_0 0) : Prop
                          → class "returns types": g(&c) is erased, c stays 0, type Eq Nat 0 1
```
The check `Direct : Id Nat (let c = Z; let g = Mk(0); g(&c); c) Z := refl` is also accepted: the checker says Mk(0)'s closure does not write.

**Principle.** This is F1 exactly, carried by a closure's environment instead of a call's arguments. D28 fixed the decision "once per definition", but a λ is not a top-level definition: it is re-created, with different captured values, at every instance.

**Fix.** Decide the class from the codomain *term*, with no evaluation:
- class 1 (returns types) iff the codomain is syntactically a sort;
- class 2 (returns proofs) iff the codomain's type, as given by typing, is `Prop`;
- class 0 (data) otherwise.

For `λ … : U(n)` this gives class 0 at every capture, because `U(n)`'s type is `Type`, not a sort term. That is sound: `V(Z)` then returns the type `⊤` as a runtime value, which is fine because types are values. Equivalently: record the class on the λ's *syntax* during the generic check of the enclosing top-level definition, and never recompute it for a closure value.

---

## X2. Closing off turns a non-erased term into an erased call (closed `Eq Nat 1 0`, accepted)

D28 has two criteria:
- a *call* is erased iff its codomain "is a sort, or has sort Prop";
- *any other term* is erased iff it is in a type position, or "its declared type has sort Prop".

A term whose type *is* `Prop` (it computes a proposition) is erased as a call but not as an inline term. A stuck match is closed off as a *call* to an anonymous function whose codomain is the match's type. So the generic path (stuck block) and the instance path (direct match) classify the same code differently. The checker implements both halves: `closeOffMatch` goes through `callFn`/`fnClass`, while inline `seq`/`match` inherit their tail's class, and a type former such as `⊤` has class 0.

```
def Lie7 (n : Nat) : Id Nat (let c = Z; let T : Prop = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; c) Z := refl
def Boom7 : Eq Nat (S Z) Z := Lie7(Z)                       -- ACCEPTED
```
- Generic `n = σ`: the match is stuck inside a type, so it becomes the block `fix _ (n : Nat) (c : &Nat) : Prop := …(σ, &c)`. Its codomain `Prop` is a sort, so it is erased and `c` stays 0. The goal is `Eq Nat 0 0 ≡ ⊤`.
- Instance `n = Z`: the match runs directly. The arm `c := S Z; ⊤` is a `seq` whose tail `⊤` is not erased, so `c ↦ 1`, and `Lie7(Z) : Eq Nat 1 0`.

The same split exists in checked programs (target 3). Both of the following are accepted: inside `P3d` the checker proves `c = 0` after the block, while `P3dRun` shows that `P3d(0)` returns 1.
```
def P3d (n : Nat) : Nat := let c = Z; let T : Prop = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; let h : Id Nat c Z = refl; c
def P3dRun : Id Nat (P3d(0)) 1 := refl
```
With a data annotation (`let T : Nat = …`) the block is not erased and `h` is correctly rejected. So the difference really is the class.

**Fix.** One criterion for every term, and it must be the criterion used for calls: a term is erased iff its declared type is a sort term, or has sort Prop. A `let` or `match` takes its class from its *declared type* (its annotation, or the type the checker infers *before* refinement), never from its tail's class. [Close] of a stuck block then preserves erasure, because the anonymous function's codomain is that same declared type. Inheritance "by tail" is the second classification path and should go.

---

## X3. A generalisation made inside a private copy escapes it and captures a later σ (closed `Eq Nat 1 0`, accepted)

D33 made type-level matches type-checked, so a match inside a type whose scrutinee is a sealed program is *generalised* ([Split] → D34 records `⌈n⌉ := σ_g`) inside the type's private copy. The arms are checked, and the match is closed off as a stuck block *over σ_g*. The formed type therefore mentions σ_g. When the private copy is discarded, two things go wrong:
- **Rule level.** The record `⌈n⌉ := σ_g` is discarded with the copy, but σ_g survives in the formed type as an ill-scoped abstract value, unrelated to `⌈n⌉`.
- **Checker level.** `onCopy` restores the fresh-name counter (`restoreKeep` keeps only fuel, classCache and recCands), so the next `freshAbs` re-issues σ_g's index.

```
inductive Box := Mk(x : Nat)
def Double (n : Nat) : Nat by n := match n { Z => Z | S p => S (S (Double(p))) }
def Esc (n : Nat) (m : Box) : Id Nat (let b = Double(n); match b { Z => 0 | S _ => 1 })
                                      (match m { Mk(x) => match x { Z => 0 | S _ => 1 } }) :=
  match m { Mk(x) => match x { Z => refl | S _ => refl } }
def BoomE : Eq Nat 1 0 := Esc(1, Mk(0))                      -- ACCEPTED
```
Trace:
```
[Call-type] Double(σ0) : Nat
[Split] generalise ⌈Double(σ0)⌉ to σ2                         -- inside the goal's private copy
[Def] Esc: goal Eq Nat ⌈F(σ2)⌉ ⌈G(σ1)⌉                        -- σ2 escaped; the counter is back at 2
[Split] σ1 := Mk(σ2)                                           -- the body's field is issued σ2 again
[Split] σ2 := 0    → goal ⌈F(0)⌉ vs ⌈G(Mk 0)⌉ = Eq Nat 0 0 ≡ ⊤   refl ✓
[Split] σ2 := S σ3 → Eq Nat 1 1 ≡ ⊤                             refl ✓
```
The statement proved is "`Double(n) ≥ 1` iff `m.x ≥ 1`", for all `n` and `m`. It is false, and its instance at `(1, Mk(0))` is `Eq Nat 1 0`. The single-constructor `Box` makes the collision happen in *every* arm, because each arm's first fresh σ is issued index 2 from the restored counter.

It does not have to be the definition's own goal. Any lemma call whose statement contains such a match leaks σ_g into the call's type ([Call-type] also evaluates on a private copy). A caller can then refine the lemma's σ_g by splitting its own variable, and derive a false fact from a *true* lemma.

**What part is the rule, what part the checker.** With globally fresh names, σ_g would be a free variable of the goal, unrelated to anything the body can split. The goal would then be unprovable, and the checker incomplete but sound. So the collision is an implementation bug. But the rules produce the ill-scoped σ_g in the first place. RULES says nothing about generalisations made inside a private copy, and D34's "every occurrence later re-derived" presupposes that the record lives as long as σ_g does.

**Fix.**
- (a) Rules: a generalisation is not an assumption. It *names* a closed deterministic computation, `σ_g ≡ ⌈n⌉`, which is true everywhere. So its record is global (it survives private copies and arms); only the *split refinements* of σ_g are arm-scoped. The formed type then says `⌈F(σ_g)⌉` with `σ_g ≡ ⌈Double(σ0)⌉` known, which is the true statement, and later derivations of `⌈Double(σ0)⌉` in the body meet it. An alternative is to substitute `σ_g := ⌈n⌉` back into anything that leaves the private copy.
- (b) Checker: `restoreKeep` must keep `nextAbs` and `nextLoan`. Fresh names must never be reissued, the same discipline as Lean's name generator.
- (c) Regression test: `BoomE`.

---

## X4. D30 identifies functions that return borrows into different arguments (closed `Eq Nat 0 1 ∧ Eq Nat 1 0`, accepted)

D30 defines the normal form of a function as "the observation of its generic call: its result together with the final contents of the generic owned places `cᵢ`". For a codomain `&T`, the observation ends every borrow, including the returned one. So the result is `⊥` for every such function, and the owners get their contents back *unchanged*: which argument the result pointed into is forgotten. `Id` avoids exactly this with "A must be borrow-free". D30 has no such guard. The checker's `convFn` does `pushTemp r; endAll; popTemp`, so `rf = rg = ⊥`.

```
def PickX (x : &Nat) (y : &Nat) : &Nat := x
def PickY (x : &Nat) (y : &Nat) : &Nat := y
def ConvPick : Eq (Π(x : &Nat) (y : &Nat). &Nat) PickX PickY := refl                    -- ACCEPTED
def Q (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Π(x : &Nat) (y : &Nat). Id Unit (let r = h(x, y); *r := S Z) (*x := S Z)
def TX : Q(PickX) := let h = PickX; (λ(x : &Nat) (y : &Nat) : Id Unit (let r = h(x, y); *r := S Z) (*x := S Z) => refl)
def TY : Q(PickY) := J(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickY, Q, refl, TX)         -- ACCEPTED
def Boom : (Eq Nat 0 1) ∧ (Eq Nat 1 0) := let c = Z; let d = Z; TY(&c, &d)                -- ACCEPTED
```
`TY` says: writing `1` through `PickY(x, y)` is the same as writing `1` to `*x`. Its instance at two fresh zeros observes `(c, d) = (0, 1)` against `(1, 0)`. The conjunction is `Eq (Nat × Nat) (0, 1) (1, 0)` by the pair rule, which is empty.

TX is written with `let h = PickX; λ…` so that its Π-type captures `PickX` exactly as `Q(PickX)` does. The checker compares Π-types structurally, captured values included, so `λ… : …PickX(x,y)…` without the capture is not convertible. That incompleteness is worth recording separately (§6).

**Fix.** For a function with codomain `&T`, observe the result *through the hole*: run `let r = f(ā); *r := σ_new` with `σ_new` fresh, and compare the final contents of the `cᵢ`. Equivalently, compare the [Close] `&T`-row sealed programs, treating `loan_k` as a free variable. `PickX` then leaves `(σ_new, σ_y)` and `PickY` leaves `(σ_x, σ_new)`. State this in P1 next to D30. More generally, D30's "observation" must be the same observation that `Id` and [Call-type] use for every codomain `Id` supports, and must say what it does for the codomains `Id` rejects.

---

## X5. Checker non-termination: a neutral-headed call in a sealed program's head position re-closes forever

```
def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Id Nat (let a = Z; let b = Z; (let r = h(&a, &b); ()); a) Z
```
The checker overflows its stack (deep recursion `nfSealed → eval → readPlace → accessInside → endBorrow → substEnv → substV → nfSealed …`). Any function that calls an *abstract* function returning a borrow, with two or more borrow arguments, and then reads an owner does the same. So do `Q` above with an owned local in place of `y`, and the motive `P(h) := Id Nat (let c = Z; let d = Z; (let r = h(&c, &d); *r := S Z); c) Z`, which is the natural way to write X4's transport.

Cause, at the rule level: two rules conflict. [Call] says "a call whose head is a neutral … is stuck at once and closed off". [Seal] (D9) says the head call `C` of a sealed program is not eligible for [Close]. `callFn` takes the first reading for neutral heads (`| .abs _ | .sealed _ => closeCall`) and never consults the head flag. Normalising `⌈L; let r = σ_h(&c₁,&c₂); *r := X; c₁⌉` therefore closes `σ_h(&c₁,&c₂)` off *again*, which makes a new hole. Reading `c₁` ends that hole's borrow, the substitution re-normalises a sealed program of the same shape, and so on without end. This is D9's loop, reopened for neutral heads. With a Unit or data codomain the re-closing is harmless, since it reproduces the same syntax, which is presumably why no test caught it.

**Fix.** Rules: "a neutral-headed call is stuck at once; it is closed off unless it is the head call of the sealed program being normalised, in which case the program stays sealed". Checker: honour the `head` flag in the neutral-head branch of `callFn`.

---

## §4. D34 (persistent generalisation): what I tried, and why it holds apart from X3

Soundness argument. A generalisation `⌈n⌉ := σ_g` is Lean's `generalize`: it names a closed, deterministic computation. Applying the name to later derivations of the same syntax is sound as long as three things hold:
- (i) the syntax is closed, so no live loan binds inside it;
- (ii) evaluation is deterministic, so the same syntax gives the same value;
- (iii) the *split* refinements of σ_g stay scoped to their arms.

(i) holds because D29 ends every loan inside a neutral at a matched head *before* [Split] generalises it, so the recorded key is loan-free. A later derivation with a fresh hole is different syntax until the hole is filled, and after filling it is the same closed program. (ii) holds in the checker, with a caveat: fuel exhaustion counts as "stuck". That only makes the checker incomplete. The re-derivation that later completes gives the true value, and a clash with an arm's split value only makes that arm unreachable. (iii) holds for arms and nested functions, as the tests below show. It fails only for private copies (X3), where the record is discarded but the name escapes.

Tests (scratch file `D34.lean`, 14/14 as expected):
- `LeakA`/`LeakB`: a generalisation in a non-tail proof, or in a data match, followed by `refl` on `Id Bool (Lt(k,v)) False`. Rejected. After the block the goal is `Eq Bool σ2 False`, with σ2 unrefined.
- `LeakC`: the same inside a nested `λ`'s check. Rejected, and the goal still holds `⌈Lt(σ0, σ1)⌉`.
- `LeakD`: the same inside a type on a private copy. Rejected. X3's leak needs the collision with a later fresh σ to do harm.
- `SplitOK` accepted, `SplitBad` rejected: the split itself is right.
- `Re`: generalise `⌈IsZ(n)⌉`, take arm False, then split `n := Z`. The re-derived `IsZ(Z)` *computes* True, which contradicts the arm, and the goal is correctly left as `Eq Bool False True`. The arm is unreachable, and the checker proves nothing there.
- `Loop2`: recursing on a field of a generalised sealed tree is rejected by [Rec]. σ_g's fields are not subterms of the entry value.
- `TwoCopies`: two derivations of `⌈Lt(k,v)⌉` in the goal are both reached by one split.

Other cases the lead asked about:
- *Erroring sealed program:* a normalisation error is a type error (D29), so it cannot be generalised.
- *Refinement after generalisation that changes the value:* see `Re`. It gives an inconsistent, unreachable arm, never a false conclusion in a reachable one.
- *Leak into an enclosing definition's goal:* every top-level item starts from a fresh state (`checkDefs`), and `checkFix` restores everything except fuel, `classCache` and `recCands`.

One checker detail, not an attack. `generalizeNeutral` types σ_g by `sealedResultType?`, which returns a type only when the head's declared codomain is closed. Otherwise it falls back to `Nat`, including for every loan fill `⌈L; C; cᵢ⌉`. So a generalised `List`- or `Tree`-valued fill is typed `Nat`. Refinement uses the match's constructors, so I found no consequence, but `absType` feeds `typeClass` and `erasedValue`. Type it from the place's stored type instead.

---

## §5. D30's "circular comparison ⇒ not convertible"

"Not convertible" can only make the checker reject. No rule branches positively on non-convertibility: Eq-reflexivity, [Split] occurrence replacement (syntactic `==`), `canonNeutral` lookup (syntactic) and arm-type agreement all use conversion positively, and `conv` is a conjunction of positive checks. So the clause is sound, and incomplete exactly where the lead says. `convStack` is per comparison pair, and a nested unrelated comparison of the same pair inside an observation also answers false. That is incompleteness only.

What *does* break D30 is not circularity but the definition of the observation for `&T` codomains (X4).

---

## §6. General inductive types (several fields)

Scratch files `A4.lean` and `A5.lean`, all as expected, where each case's expectation is my own judgement of soundness:
- `Swap` (recurse on `Node(r, v, l)`), `Regrow` (`l := *t; Regrow(&l)`, where `l`'s content equals the entry): both rejected by [Rec].
- `SwapFields` (swap the fields, then recurse on `l`): accepted, and it terminates.
- Sibling sub-borrows: `LeftmostM(&l)` gives a live returned borrow into `l`'s subtree while `r := Leaf` runs. `SibEq` (a split proof) is accepted, `SibWrong` rejected. The owner receives `Node(⌈…*r := Node(Leaf,7,Leaf); c1⌉, σ2, Leaf)`, which is right.
- Re-matching `*t` while the hole into `l` is live, then writing `r2` and the hole (`Sib2`): accepted, and the concrete run `Sib2Run` gives the right tree.
- `Two(&l, &r)` with both sibling borrows passed to one call: `TwoEq` accepted, `TwoWrong` rejected. Owners and footprints across fields come out right.

I found nothing wrong here. The one design point worth recording: a pattern variable is a *path*, so after `*t := Node(X, …)` the name `l` denotes the *new* node's field (the Probes file says the same for Nat). [Rec] measures the content at call time, so this cannot be abused for recursion, but it is not Rust's semantics and the paper should say so.

Incompleteness met on the way (not soundness): Π-types are compared structurally, captured values included. So `Π(x y : &Nat). Id … (PickX(x,y)) …` is not convertible to `Q(PickX)`, which captures `PickX` as `κ1`. X4 had to build its proof with `let h = PickX; λ…` for that reason. The paper should say that Π-types are compared structurally, with captured values.

---

## Attack list (distinct attacks and outcomes)

| # | Attack | Outcome (checker at 49f9108a) |
|---|---|---|
| X1 | closure with codomain `U(n)` over a captured `n` (D28 for λ) | **closed `Eq Nat 0 1`, accepted** |
| X2 | stuck block erased as a call vs the same match not erased inline (D28 non-call rule) | **closed `Eq Nat 1 0`, accepted**; also a false in-program `Id` (target 3) |
| X3 | generalisation inside a type's private copy; the name escapes and collides (D33 × D34) | **closed `Eq Nat 1 0`, accepted** |
| X4 | D30 on `&T` codomains: `PickX ≡ PickY`, then J | **closed `Eq Nat 0 1 ∧ Eq Nat 1 0`, accepted** |
| X5 | abstract borrow-returning call with ≥ 2 borrow args, then read an owner | checker stack overflow (the head guard is ignored for neutral heads) |
| D34a | generalisation in a non-tail proof or data match leaking to the continuation | blocked (arm refinements restored) |
| D34b | leak from a nested λ's check | blocked (checkFix restores) |
| D34c | refine an embedded σ after generalising | unreachable arm, nothing provable (correct) |
| D34d | [Rec] on a generalised neutral's field | blocked by entry values |
| D34e | live hole or erroring program as the generalised key | blocked by D29 (loans ended first; errors are type errors) |
| D28a | Π-typed parameter with codomain `Prop`, instantiated with an effectful closure | consistent (class 1 on both paths) |
| D28b | J endpoint with an effect | consistent (type slot, private copy on both paths) |
| D28c | `Type`-valued family returning `⊤` (cumulativity) | rejected, correctly |
| D30a | circular comparison answering "not convertible" | sound (§5) |
| I1 | [Rec] on rebuilt or regrown trees | rejected, correctly; field-swap recursion accepted and terminating |
| I2 | sibling sub-borrows, a hole in one field while the other is written, re-matching the node | computes the right trees and effects |

---

## Regression block (for `ochr/core/lean`; the expectations are those of the fixed rules)

```
ochr V17 {
  def U (n : Nat) : Type := match n { Z => Prop | S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }
  -- X1
  def Mk (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
  def Lie8 (n : Nat) : Id Nat (let c = Z; let g = Mk(n); g(&c); c) (S Z) := refl
  reject def Boom8 : Eq Nat Z (S Z) := Lie8(Z)
  reject def Direct8 : Id Nat (let c = Z; let g = Mk(0); g(&c); c) Z := refl
  -- X2
  def Lie7 (n : Nat) : Id Nat (let c = Z; let T : Prop = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; c) Z := refl  -- accepted iff inline is erased too
  reject def Boom7 : Eq Nat (S Z) Z := Lie7(Z)
  reject def P3d (n : Nat) : Nat := let c = Z; let T : Nat = match n { Z => (c := S Z; 0) | S _ => (c := S Z; 0) }; let h : Id Nat c Z = refl; c
  -- X3
  inductive Box := Mk(x : Nat)
  def Double (n : Nat) : Nat by n := match n { Z => Z | S p => S (S (Double(p))) }
  reject def Esc (n : Nat) (m : Box) : Id Nat (let b = Double(n); match b { Z => 0 | S _ => 1 }) (match m { Mk(x) => match x { Z => 0 | S _ => 1 } }) :=
    match m { Mk(x) => match x { Z => refl | S _ => refl } }
  -- X4
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  reject def ConvPick : Eq (Π(x : &Nat) (y : &Nat). &Nat) PickX PickY := refl
  -- X5 (must terminate; the verdict is accepted)
  def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Id Nat (let a = Z; let b = Z; (let r = h(&a, &b); ()); a) Z
}
```
The `inductive Box := Mk(…)` constructor name clashes with the function `Mk` in X1. Rename one of them if the checker's namespace is shared (in my runs the two lived in separate files). All scratch files are in my scratchpad copy of the checker (`Scratch/A1.lean`, `A3.lean`, `A5.lean`, `A6*.lean`, `A8.lean`, `D28.lean`, `D34.lean`). Nothing in the worktree was modified except this note.
