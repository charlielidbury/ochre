# breaker-fresh, round 2: attacks on RULES v1.6 and the v1.6 checker

**Verdict:** v1.6 is still inconsistent. I have three new closed proofs of False, and the executable checker (`ochr/core/lean` at `49f9108a`) accepts all three. G1 and G2 are two further forms of D28's two-path problem (erasure re-decided). G3 is a new hole: a generalisation made inside a private copy escapes it, and the leaked σ collides with a later fresh σ.
**Most important finding:** D28 fixed erasure for *top-level* calls only.
- A closure's erasure class is computed from its Π-type *value*, which includes its captured values. A closure made by `Mk(n)` is therefore data at the generic `n` and a type at `n = Z` (G1).
- A stuck block becomes a call to an anonymous function whose codomain is a sort, so it is erased. The same match run directly is a non-call term of type `Prop`, so it is not erased (G2).
- The general rule: every classification must be a property of *syntax*, fixed when the enclosing *top-level* definition is checked.
**What must change:** (1) decide erasure from the codomain *term* (literally a sort → returns types; its declared type is `Prop` → returns proofs; otherwise data), with no evaluation, for top-level functions, closures and stuck blocks alike. Also use one criterion for calls and non-call terms, so that closing off preserves erasure. (2) A generalisation is a naming equation (`σ_g ≡ ⌈n⌉`), not an assumption, so it must outlive the private copy it was made in. At minimum, a σ created inside a private copy must never be re-issued (G3). D34 is otherwise sound (§4).
**Confidence:** high. All three are accepted by the checker: `Boom8 : Eq Nat 0 1`, `Boom7 : Eq Nat 1 0`, `BoomE : Eq Nat 1 0`. G1 and G2 follow from the rule text of D28 as written. G3 has a rule-level half (an ill-scoped σ in a formed type) and an implementation half (fresh-name reuse), which together give False.
**Not checked:** the metatheory sections of the paper; mutual or nested inductive types; performance. D30's circularity clause I checked only by argument (§5).

Method: I read RULES v1.6 and D28–D34, and tested every candidate attack with the checker on a scratch copy of `ochr/core/lean` (in my scratchpad; nothing in the worktree was edited). The scratch files are reproduced verbatim below; each runs with `lake env lean <file>` in about 0.5 s.

---

## G1. A closure's erasure class depends on its captured values (closed `Eq Nat 0 1`, accepted by the checker)

D28: "a call `f(ā)` is erased iff `f`'s declared codomain, evaluated at `f`'s generic call, is a sort or has sort Prop". For a closure, "its generic call" binds its captured values. So a λ whose codomain mentions a captured variable is classified differently in different contexts. The checker implements the rule faithfully: `fnClass` evaluates the codomain of the Π-type *value*, `tPi cs …`, and `cs` holds the captured values.

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

## G2. Closing off turns a non-erased term into an erased call (closed `Eq Nat 1 0`, accepted)

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

The same split exists in checked programs. In a non-tail stuck match annotated `Prop` with writes in its arms, the continuation believes the writes did not happen, and `let h : Id Nat c Z = refl` is accepted where the program has `c = 1` (target 3).

**Fix.** One criterion for every term, and it must be the criterion used for calls: a term is erased iff its declared type is a sort term, or has sort Prop. A `let` or `match` takes its class from its *declared type* (its annotation, or the type the checker infers *before* refinement), never from its tail's class. [Close] of a stuck block then preserves erasure, because the anonymous function's codomain is that same declared type. Inheritance "by tail" is the second classification path and should go.

---

## G3. A generalisation made inside a private copy escapes it and captures a later σ (closed `Eq Nat 1 0`, accepted)

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
