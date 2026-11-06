# 25. The historical bugs, read as failed step lemmas (docs/23, test 1)

Written on 2026-11-06 by a fork of the session that wrote `docs/18`, at the user's request ("run any tests you think will be useful"), as test 1 of `docs/23`. It is a paper analysis: nothing here is mechanised, and the pre-fix behaviour of each step is taken from the fix's commit and its DECISIONS entry, not re-run.

**The question.** `docs/23` proposes proving consistency by meaning preservation: each symbolic state Ω has a meaning ⟦Ω⟧_ρ for every assignment ρ of set-theoretic values to its unknowns, and each checker step keeps it. If that route is right, every known way the checker went wrong should show up as a step whose lemma fails before the fix and holds after it. If a bug escapes the lemmas, or is caught only by something the route treats as an afterthought, that is evidence against the route.

## Just enough of the framework

- **Assignments.** ρ maps each unknown σ to ρ(σ) ∈ ⟦Δ(σ)⟧_ρ, in the order Δ was built. A [Split] arm restricts ρ by its refinement; generalisation records and η-refinements are further constraints on ρ (path conditions).
- **States.** ⟦Ω⟧_ρ maps places to meanings. A state with live borrows means a *function of the final contents κ of its live holes*: ⟦Ω⟧_{ρ,κ}. A sealed program means what its text means, ⟦⌈t⌉⟧_ρ := ⟦t⟧_ρ.
- **(a) Meaning preservation.** A step Ω, t → Ω′, t′ keeps meaning: for every ρ′ admitted by Ω′ (restricted to Ω's unknowns, ρ), running t′ from ⟦Ω′⟧_{ρ′} means what running t from ⟦Ω⟧_ρ means. Its **coverage** part: the arms of a split, together, admit every ρ the state before the split admits.
- **(b) Membership.** Every stored value's meaning lies in its stored type's meaning, *for every completion κ of the live holes*: ⟦v⟧_{ρ,κ} ∈ ⟦T⟧_ρ.
- **The well-formedness invariant.** The borrow discipline. (This analysis first also put "every closure and global passed [Rec]" here. Test 0, `docs/24`, showed a `fix` means a function by guarded recursion whether or not it passed [Rec], a non-decreasing call meaning the error value; so [Rec] belongs to membership, (b): the guard never fires. Case 3 is re-classified accordingly.)
- **Checks.** A check that rejects produces no derivation, so only its accepting direction carries an obligation: whatever (b) or the invariant it is there to establish.
- **⊥.** Two readings are open (`docs/23`): (i) ⊥ means the value the place held when it was moved (a non-affine model); (ii) ⊥ means "no information", with an order ⊑ and every computing step ⊑-monotone.

## The five cases

### 1. A returned borrow of an index field (D73; `LentIndex`, closed `False` `BoomI2`)

**Program.** `GetN (v : &V) : &Word := match *v { MkV(n, x) => &n }` with `V := MkV(n : Word, x : Fin1(n))`. The caller writes `Zero` through the result.

**Step at fault.** [Repack] at `GetN`'s return (a whole-again point), `repackCheck`. Before `6bcb347a` it read the lent `n` as the content its borrow held at that moment, so `MkV(n_now, x)` checked.

**Lemma.** The accepting direction of [Repack] owes (b) for the owner: after the return, `*v`'s meaning is a function of the hole κ of the returned borrow, and its stored type is `V`, so it must hold that ∀κ. MkV(κ, ⟦x⟧) ∈ ⟦V⟧.
- *Buggy:* the check establishes membership at κ = n_now only. At κ = Zero (what `A2e` writes) and x = O : Fin1(One), MkV(Zero, O) ∉ ⟦V⟧. **Fails.**
- *Fixed:* `lentUnknown` checks against a fresh unknown of the lent content's type, i.e. for all κ. `GetN` is then rejected. **Holds.**

**Caught by:** (b), at a check's accepting direction. It is visible only because a state with live borrows means a function of its holes. (a) is not involved.

### 2. A stuck `J` closed off unchecked (D75; `JBlocks`, closed `False` `BoomJ`)

**Program.** `JLie (a b : Word) (h : Eq(Word, a, b)) (v : &V) := match *v { MkV(n0, x0) => J(Word, a, b, λz. Unit, h, match *v { MkV(n, x) => (n := Zero; ()) }) }`.

**Step at fault.** Closing off the stuck `J` as a block ([T-J-stuck] through `closeOffMatch`). Before `58a889a3` no end state was passed, so the places it borrowed were never checked whole. `*v` received a sealed fill with stored type `V`.

**Lemma.** (a) *holds* even before the fix: the fill means exactly what running the `J` means, which at ρ(a) = ρ(b) and ρ(h) = refl is running the transported term. (b) for the fill is the obligation: ∀ρ. ⟦fill⟧_ρ ∈ ⟦V⟧.
- *Buggy:* at ρ(a) = ρ(b) = Zero the fill means MkV(Zero, x0) with x0 typed at n0 = One, which is ∉ ⟦V⟧. **Fails.**
- *Fixed:* the block's one arm ends with the whole-again check, which rejects `JLie`, so no state is produced. **Holds.**

**Caught by:** (b) at a producer step. D76's "producer obligation" (every producer of a neutral of dependent type checks the value whole) is precisely (b) at producers.

### 3. A recursive closure capturing a value it splits on (D78; `Recursion`, closed `False` `BoomCapSplit`)

**Program.** `CapSplit (n x : Nat) : False := (fix go (y : Nat) : False by y := match n { Z => go(y), S q => go(y) })(x)`.

**Step at fault.** `recCheck`, which before `c7b31b65` identified a recursive call by comparing function values (`ctx.fn == fv`). The [Split] on the captured `n` substituted inside the closure's captures, its binding of itself included, but not inside the [Rec] entry. So after the split `go(y)` was not recognised as recursive and was never checked.

**Lemma.** The split itself keeps meaning: the refined closure means the same function, which is (a), and it **holds**. What fails is the accepting direction of [Rec], which membership needs (first written here as part of the well-formedness invariant; see the amendment above): "every call whose head *means* the function being defined is at a strict subterm of the entry, for every ρ".
- *Buggy:* the identification was by representation, which the split changed without changing the meaning, so a call meaning `go` went unchecked. **Fails.** And it has to fail: under guarded recursion (`docs/24`) the call `go(y)` does not decrease, so the guard fires and ⟦go⟧ is the error value there, which is in no type, so membership of `go(y)` in `False` cannot be proved.
- *Fixed:* recognition by name, which is syntax and is invariant under refinement. **Holds.**

**Caught by:** membership (b), through the guard: under guarded recursion (`docs/24`) the missed call's decreasing argument does not drop, so the closure's meaning at that call is the error value, which lies in no type. This analysis first classified it under the well-formedness invariant; test 0 moved [Rec] to membership. It is also exactly what `docs/23`'s re-audit criterion flags: a decision read from representation whose two outcomes ("check the call" or "skip it") do not mean the same.

### 4. EtaBoom (D79; `ArmEta`, closed `False` `Boom`)

**Program.** `DP (n : Nat) := MkDP(x : Bool, y : G(n, x), z : Nat)` with `G(Z, _) = Void`, `G(S _, _) = Nat`. `Bad1` matches on `n`, and in each arm moves `d.z` in a block and then matches `d.y`.

**Step at fault.** `exitWorld` leaving the arm `n := Z`. Before `9b0f36ff` it kept the η-refinement σ_d ↦ MkDP(σx, σy, σz), whose fields were typed in that arm's world, so Δ(σy) = Void (an evaluated type, not `G(n, x)`).

**Lemma.** The coverage part of (a): the sibling arm `n := S m` must admit every ρ the state before the split admits with ρ(n) = S(…).
- *Buggy:* the kept record forces ρ(σ_d) = MkDP(ρσx, ρσy, ρσz) with ρσy ∈ ⟦Void⟧ = ∅, so the sibling admits *no* ρ. Coverage **fails**, and the arm is vacuous, which is how `match y {}` proved `False`.
- *Fixed:* the record dies with its arm, and the sibling re-derives σy′ : Nat. **Holds.**

**Caught by:** (a), its path-condition part. This is the case `docs/23` predicted.

### 5. MovedBothSides (fuzz case 11014; fixed in `54fa605e`, made a switch with its witness in `b8941db2`)

**Program.** `Id(Unit, (let r = &x; match n { Z => (let y = x; ()), S _ => () }), (let r = &x; match n { Z => (), S _ => (let y = x; ()) }))`, closed by `refl`.

**Step at fault.** `mkEqM` on moved-out places. At the generic call each stuck block captures `x` by move (K1(e): some arm moves it), so both sides leave x = ⊥, and conversion's reflexivity gave Eq(⊥, ⊥) = ⊤. At n = 0 only the left side moves it, and the equation came out `False`: "⊤ generically, False at n0 = 0", in the commit's words.

**Lemma.** This depends on the reading of ⊥:
- *Under (i), ⊥ is the old value.*
  - The block's over-approximated move keeps meaning, since moving is invisible.
  - Eq(⊥, ⊥) ↦ ⊤ keeps meaning only when the two old values are equal. In this program they happen to be, but in general they are not: `(x := 1; let y = x; ())` against `(x := 2; let y = x; ())` leaves ⊥ on both sides with old values 1 and 2. So (a) for the buggy `Eq` step **fails**.
  - The instance's `False` over (⊥, x0) fails it too, since both mean x0.
- *Under (ii), ⊥ is no information.* ⊤ at (⊥, ⊥) is not ⊑-monotone, because refining the two sides differently makes it false. **Fails.**
- *Fixed:* an equation with ⊥ on either side stays stuck, which keeps meaning and is monotone. **Holds** under both readings.

**Caught by:** (a) under (i), or (Mono) under (ii).

**A cost for test 2.** Under (i), ⟦Ω⟧ is not a function of Ω: the checker's ⊥ does not record the old value, so the model would need ghost data per ⊥. Reading (ii) needs nothing extra beyond monotonicity of every computing step over ⊥. This favours (ii).

## Other soundness guards, treated cheaply (from `ochr/core/notes/machine-ablation.md`)

| Guard (row) | Witnesses | Lemma that fails without it | Caught by |
|---|---|---|---|
| a `Z`/`S` match needs a scrutinee of type `Nat` (#19) | `NatT`, `M2` | splitting σ : TG(σ′) into Z / S covers ρ only where ⟦TG(ρσ′)⟧ = ℕ; at ρσ′ = 1 it is `B2` | (a), coverage |
| a whole read repacks (#26) | `ReadBroken`, `PassBrokenVar`, `LiePass` | an open raw tuple is stored at its declared type | (b) |
| a proof field assigned while part of its value is lent (#25) | `LieLent`, `BoomLent`, … | as case 1, for a proof (`⋆`, which [Repack] cannot re-check): membership only at the current lent part, not for all κ | (b), for all holes |
| each arm's end checked as a return (#33) | 23, among them `JBlocks`, `Producers` | case 2 in general: a block's sealed result is stored at a type it may not inhabit | (b) at producers |
| `&p` needs `p : Type₀` (#21) | `BorrowType`, `BorrowProp`, … | for a type: overwriting a type variable while values typed by it live breaks (b). For a proposition: ⟦P⟧ ⊆ {•}, so a write is semantically harmless; that half is a runtime and erasure guard | (b), for types; not a consistency guard, for propositions |
| borrows whole when returned or closed off (#14, #15); K1(d), K1(e) (#10, #11) | `ReturnMovedBorrow`, `P1`, …, `B1`–`B3` | depends on the reading of ⊥. Under (i) a hole means its old value and these look like runtime-safety guards; under (ii) they would be ⊑ obligations | not analysed |

## Summary

| Bug | Step at fault | Lemma | Buggy | Fixed | Caught by |
|---|---|---|---|---|---|
| D73 `BoomI2` | [Repack] at a return (`repackCheck`) | (b) for all holes κ | fails | holds | (b), check's accepting direction |
| D75 `BoomJ` | closing off a stuck `J` | (b) at the producer; (a) holds even when buggy | fails | holds | (b) at a producer |
| D78 `BoomCapSplit` | `recCheck`'s identification of recursive calls | [Rec]'s accepting direction, part of membership (the guard never fires); (a) holds | fails | holds | (b), through the guard (first classified under the invariant) |
| D79 EtaBoom | `exitWorld` keeping an η-refinement | (a), coverage | fails | holds | (a), path conditions |
| fuzz 11014 MovedBothSides | `mkEqM` on ⊥ | (a) under (i), (Mono) under (ii) | fails | holds | (a) or (Mono), depending on ⊥ |

## Verdict

The route explains all five: in each case a lemma of the route fails at the buggy step and holds at the fixed one, and no bug escapes. But the explanation is spread across the route's parts. Meaning preservation (a) alone catches only EtaBoom, and MovedBothSides under reading (i). All three October bugs are caught by membership (b): two quantified over the live holes, the third through the guard of a recursive function ([Rec] is membership's, since test 0; this analysis first put it in the well-formedness invariant). In all three, the step's (a) holds even before the fix. So the route stands or falls with (b) as much as with (a), which agrees with `docs/23`'s point 5 that they must be proved together. It would be wrong to present the route as "each step keeps meaning" alone.

In the two-run walk each bug was a disagreement between two runs. Here each is local to one step and one lemma, with no instance run, which is the simplification `docs/23` claimed. The ⊥ question leans to reading (ii): reading (i) needs ghost old values that the checker's ⊥ does not carry. And the guards that protect holes and moves (#10, #11, #14, #15) are the ones still unexplained until that choice is made.
