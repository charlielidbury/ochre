# Referee report on docs/18: the structure of the argument and its targets

Attack on the consistency proof plan `ochr/docs/18-consistency-proof-plan.typ`, as it stood on 2026-11-02: the first, 26-page draft, before the set-theory background, the explainer boxes and the notation changes were added. The referee was a fresh, read-only Opus agent (`attack-structure`), asked to produce a statement of the form "this plan for consistency will never lead to a final proof of consistency because X", where X is a real obstruction rather than a difficulty. Its angle: whether the Lean target says what is claimed, the gap between the paper's rules and the checker, cycles in the dependency graph, the bridge between the heap design and the real checker, and whether the "proved" claims prove what they say. The report arrived in two parts; both are given here, lightly edited.

**Coordinator's note.** Finding 5.3, that the Lean statement `Conjecture2` is false as stated and so `theorem stability` is a `sorry` proof of a false proposition, is recorded in `ochr/docs/17-consistency-status.md`.

## 1. The statement

I found no strict impossibility. I did find one place where the plan, as written, cannot be completed: its notion of truth and its soundness theorem do not meet. Fixing it means changing the model, not just doing more work.

- **Truth is set-theoretic.** A proposition is true when its meaning is `{•}`, and `Type_i` means `V_κi`.
- **Soundness covers only ground instances made of machine values.** These are countably many: the closed values the checker can build.
- **Accepted programs prove propositions that quantify over `Type₀` and over functions.** Their truth is a claim about every element of an uncountable set, almost none of which is the meaning of any machine value.
- **Nothing in the plan's lemma graph gives truth at such an element.** The meaning of a function value, or of a codomain at such an element, is never defined.

So the claim "proof terms have true types" cannot be discharged, and the corollary that derives consistency from soundness does not go through. This is a failure of the pieces to compose, not a proof that Ochr is inconsistent.

## 2. The argument

1. **Function types denote full set-theoretic products.** The plan's meaning of a function type is a subset of `Π(d̄ : D̄). Out_B(d̄)`, where the codomain's meaning is a function of *set-theoretic* arguments, and `Type_i` means `V_κi`.
2. **Truth is set-theoretic.** A proposition is true when its meaning is `{•}`, and the plan says outright that truth must be semantic.
3. **Soundness quantifies over machine values only.** Clause (ii) of the soundness target ranges over ground instances β, which are valuations into the checker's `Value`s, a countable Lean inductive type.
4. **The claim needs the uncountable case.** "Proof terms have true types" has an unargued case, marked "new beyond F": proofs that are function values. For a lemma used as a value, its Π-type must be true for every `A ∈ V_κ₀` and every `a ∈ A`. Soundness of the lemma itself gives this only for machine-valued `A` and `a`, and no lemma in the graph says anything about truth at an element that is not the meaning of a value.
5. **Q1 does not address this.** Its requirement (c), "a good function value's meaning lies in R", quantifies over all set arguments. Both of Q1's candidate notions of "good" (a logical relation, or definability) are defined by runs at definable arguments, so neither can deliver (c).
6. **The model presupposes a semantics it never builds.** The meaning of a codomain at set arguments, the conversion principle that a function value is fixed by the observation of its generic call, and `Eq` at function types all assume a meaning for Ochr code (borrows, closing off, observation) at arbitrary set arguments. The plan's sketch of the model covers only inductive types, so the model is not actually defined for these Π-types.

## 3. Evidence

```
def L (A : Type) (a : A) : Eq(A, a, a) := refl
def M : (Π(A : Type) (a : A). Eq(A, a, a)) := L
def H (h : Π(A : Type) (a : A). Eq(A, a, a)) : ⊤ := refl
def K : ⊤ := H(L)
def LF (f : Π(n : Nat). Nat) : Eq(Nat, f(0), f(0)) := refl
def MF : (Π(f : Π(n : Nat). Nat). Eq(Nat, f(0), f(0))) := LF
def ML : (Π(A : Type) (a : A). Eq(A, a, a)) := λ(A : Type) (a : A) : Eq(A, a, a) => refl
```

Printed verdicts: `L`, `M`, `H`, `K`, `LF`, `MF` and `ML` are all ACCEPTED; the control `Bad : False := refl` is rejected ("the body of Bad has type ⊤, but the goal is False"). To check `K = H(L)`, the walk must show that `H`'s hypothesis is true at its instance, which means true for every set `A`: exactly what step 4 cannot supply.

## 4. Confidence, and what would rescue it

- That the gap is real in the plan as written: **high**. It is reached by the accepted `M`, `K`, `MF` and `ML`.
- That it cannot be rescued: **low**. Both repairs below rewrite the plan's definitions of meaning and truth, its model lemma, conversion soundness and Q1.

**Repair A: relativise truth to good, definable values** (a term or realizability model).
- **What changes.** The truth of a Π-type over `Type_i` or over functions becomes "for every good closed argument"; `⟦Type₀⟧` becomes the meanings of good closed type values, and `⟦A → B⟧` the meanings of good closures. The soundness walk stays as it is: the claim's universal case then follows from soundness clause (ii) at good instances.
- **Cost 1, impredicative `Prop`.** The truth of `Π(P : Prop). Q(P)` cannot be defined by recursion over closed propositions, since `Q(P)` is not smaller than the Π-type. `Prop` binders must range over the two truth values, which means proving that `Q`'s truth depends only on `P`'s truth value. Ochr's conversion-sensitive `J` and `Eq` make that a real lemma.
- **Cost 2, well-definedness.** A function's meaning must be extensional: arguments with the same meaning must give results with the same meaning. A `J` at endpoints that are semantically equal but not convertible gets stuck on one argument and computes on the other, so sealed programs at ground states need meanings. That turns Q3 from an option into a hard requirement.
- **Cost 3, conversion soundness** must be re-proved against the term model.
- **Estimate:** a redesign of the semantics section plus a new extensionality lemma. The walk survives.

**Repair B: a denotational semantics of Ochr code in the set model, with an adequacy theorem.**
- **What changes.** Give a meaning, under a semantic environment ρ, to every closed value, closure and sealed program. That must cover borrows (forward and backward functions), closing off, stuck blocks and observation. Then prove that it agrees with the machine on definable arguments (adequacy).
- **Cost.** Either the walk's ground side becomes semantic states (symbolic against denotational, instead of symbolic against a ground run), or the walk is kept and adequacy plus a separate denotational soundness theorem handle non-definable arguments. That is roughly a second soundness proof of comparable size. It is also the object that the plan's meaning of codomains, its conversion principle for function values, and `Eq` at function types already silently presuppose.
- **A middle route.** Treat non-definable elements as never-refined unknowns interpreted by ρ, and define the meaning of a sealed program by repeatedly refining the unknown it is stuck on to its semantic value. Plausible, but a new construction with its own termination argument.

## 5. Secondary weaknesses

**5.1 The target statement holds up.** No vacuity or trivial falsity:
- `checkProgram` gives exactly one verdict per declaration, filling in "not checked" if verdicts run short (`Run.lean`);
- the hole check is total over surface terms, and covers every term-valued field of a declaration;
- a second `False` is rejected by the duplicate-name check;
- the opaque `termAddr` is used only for location-table lookups and their relocation, which are the identity on empty tables, provably without unfolding it;
- running out of fuel cannot be caught below the verdict, and the depth limits exhaust.

One obligation is missing from the plan: about 80 unchecked array accesses `xs[i]!` in the checker (51 in `Machine.lean`, 17 in `Env.lean`, 7 in `Check.lean`). In Lean's logic an out-of-range access silently returns `default`, which for `Value` is `.zero`. A proof must show each is in range on every run it reasons about, or harmless. Neither the well-formedness list nor invariant T1 covers this.

**5.2 Restricting stability to reachable states creates a cycle.** `checkDef` adds the definition to the globals before checking its body, and refinement re-runs its unchecked code:

```
copy inductive N := Su(p : N) | Zr
def Fok (n : N) : Nat by n := match n {
  Su(m) => (let r : Nat = Fok(m); match m { Su(k) => 0, Zr => match r { Z => 0, S k => clone(k) } }),
  Zr => 0 }
reject def Fbad (n : N) : Nat by n := match n {
  Su(m) => (let r : Nat = Fbad(m); match m { Su(k) => 0, Zr => match r { Z => 0, S k => clone(k) } }),
  Zr => Nat }
```

- `Fbad` (whose `Zr` arm returns the type `Nat`) is rejected with "[Match] on a non-Nat value Nat". That error is raised in the `Su` arm, where `r : Nat` holds the type `Nat` produced by running the unchecked `Zr` arm; the `Zr` arm's own error ("body has type Type, but the goal is Nat", seen on a variant with only that arm) is never reached. `Fok` is accepted.
- So Q7's conjunct "the signature is checked" is false at every state of every definition check. Any invariant that holds at `Fok`'s states but not `Fbad`'s must refer to the eventual acceptance of the definition being checked.
- Consequence: stability cannot be a lemma below soundness. The graph has a back-edge: soundness's induction hypothesis → Q7 → preservation of declared readings → decisions commute → naturality → runs agree → soundness.
- The cycle is well founded if fused: re-runs are at strict subterms by the recursion principle (R1), so the induction hypothesis at a smaller pair covers them. That requires two changes: prove stability inside the walk, relative to the instance β, rather than "for every reachable state and every α"; and add type preservation to soundness clause (i), which currently says only "runs to completion without error".
- Step 7 of the plan's order, "declared readings are preserved, under the typing invariant of Q7", as a standalone machine invariant, cannot be done as written.

**5.3 The Lean `Conjecture2` (cited for the stability lemma) is false as stated, and has a `sorry` proof.**
- `RunsCorrespond` quantifies over all machine states, and demands that the contents agree after resolution and renaming.
- Counterexample: a state with `n ↦ σ0` and `x ↦ 1`, the term `(match n { Z => (let y = x; ()), S _ => () }); ()` and the refinement `σ0 ↦ 1`, which respects the state (borrow-free, of type `Nat`). Refining the generic result gives contents `[[1, ⊥]]`; running directly gives `[[1, 1]]`. No renaming of fresh unknowns turns `⊥` into `1`.
- This is the generic state of the accepted `def G (n : Nat) (x : Nat) : Unit := ((match n { Z => (let y = x; ()), S _ => () }); ())`. The variant that ends by reading `x` is rejected with "[Read] x was moved out … (reading ⊥)", so the over-approximation is real at reachable states.
- Separately, `ValueDeclCommutes`, on which the erasure field rests, fails at states with unchecked globals; the existing `probe_d55_*` theorems show it, and 5.2 shows such states are reached.
- So `theorem stability : Conjecture2 := ⟨…, sorry⟩` is a `sorry` proof of a false proposition, and anything downstream that used it would be vacuous.
- The plan's stability lemma's "runs" half ("agree once every borrow is ended", as equality) also contradicts the plan's own ordering clause (A2⊑) and capture principle (K1). It is off the critical path in the dependency figure, but the status table lists it as the Lean form.

**5.4 The heap-slice "proved" tags put the substance in the hypotheses.**
- `frame` and `call_effect` assume that the run never touched a handle it did not hold. That is locality itself, and it is measured on 1,166 runs, not proved.
- `exec_agree` and `P_evalH` are non-interference for any program of the reified computation type, so they say nothing about the checker until the checker is written as one.
- `P_evalH` compares a heap with the same heap after filling σ, at the same allocation counter. A refinement to a compound value with fresh field handles, or a ground instance whose values are not already in the heap, changes the counter. Then renaming invariance is needed for (P) too, contradicting the claim that no renaming is needed for runs (P) covers.
- The slice excludes stuck calls. `force_is_direct`, on the heap-closing branch, assumes renaming invariance and no thunk inputs. Returned borrows with holes have no heap counterpart described: with no [End], nothing marks when the hole is supplied.

**5.5 Two machines, with no bridge.** The agreement clauses, naturality's resolution step, the order-of-ends invariant and the `Pick` example are all about moving borrows, loans, owners and resolution. (P), the frame property and (C) are discharged on the heap design, where borrows are references and resolution does not exist. No step re-derives the conditional theorem for the heap machine, and none proves the two equivalent: their equivalence is measured on 1,166 runs, not proved. After the port the checker no longer implements the paper's appendix rules, so the plan's claim that "a completed plan would prove both" fails: a Lean proof would be about the heap checker, the paper's theorem about the moving-borrow rules.

**5.6 The recommended order never produces a Lean proof of `Ochr.Consistency.consistency`.**
- No step mechanises the model, conversion soundness or the walk; the last step "states the Lean form", which already exists.
- The walk follows case trees, but `Stability.lean` itself says the checker "builds no derivation tree", and no lemma links `checkProgram`'s acceptance to the existence of one.
- The walk's per-construct naturality steps are the per-function induction over the 116-function evaluator that the plan rules out as prohibitive for (P) (10,000–20,000 lines). The heap port's reified-computation trick does not cover steps that inspect σ.

**5.7 Universes (Q8).** A uniform Lean statement cannot use one inaccessible cardinal per level, which needs ω many at once; the plan acknowledges this. My addition, unverified: inaccessibles look unnecessary, because Ochr has no W-types (no function-typed fields, and nesting only at nestable parameters). A model with `Type_i ↦ V_λi` for suitable limit ordinals λi inside ZFC may suffice, which would make Q8 moot rather than fatal. I did not verify that Π over arbitrary definable families stays bounded below λ.
