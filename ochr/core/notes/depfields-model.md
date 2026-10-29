# A model of dependent fields, and the rules it forces

Lane `depfields-model`, 2026-10-29, toward docs/14's goal: derive the dependent-field rules ([Open], [Repack], whole-again points, lent parts) from a model instead of listing them one counterexample at a time. Branch `depfields-model`, off main `4cc0beda`.

**Result.** The model accounts for every current rule, and it pointed at one rule that was missing: a `J` closed off by [T-J-stuck] never checked the places it takes by borrow where its transported term ends. That was a closed proof of `False` on main (`BoomJ`), fixed here as D75. Three candidate simplifications follow from the model; none is implemented.

## 1. The model

**Values with a telescope.** A dependent constructor `C(ā; g₁ : A₁, …, gₖ : Aₖ)`, where `Aⱼ` may mention `g₁ … gⱼ₋₁` (its *index fields*), denotes a Σ-type: the tuples `(v₁, …, vₖ)` with each `vⱼ ∈ Aⱼ(v₁, …, vⱼ₋₁)`. A proof field denotes the truth of its proposition at the earlier fields (a singleton or empty).

**Open values.** Between two points where the program relies on a value's type, mutation may break a dependency. An *open* value is a tuple whose fields each have *some* type, not necessarily the one the telescope computes from the current earlier fields. So the honest type of a field of an open value is the type of what it holds, not its telescope type.

**Borrows** are as in Aeneas: a borrow of a place of type `T` hands out the place's current content and receives back, when it ends, a final content that may be *any* value of `T`. The lender knows nothing more about the final content until the borrow ends.

**The invariant (W).** At every point where code other than the code that opened a value relies on its type, the value is in its Σ-type. Those are exactly the points where a value crosses an ownership boundary:
- it is read, moved, copied or borrowed *whole*, since the receiver assumes its type;
- a borrow of it ends, since the owner gets it back and assumes its type; this includes a borrow parameter at its function's return;
- it is a function's or constant's result, or one of `Id`'s observed results and owners;
- it is captured whole by a closure, a Π-type or a stuck block.

**Neutrals.** On the generic path the checker holds *neutrals* in place of values: abstract values `σ` and sealed programs `⌈t⌉`. A neutral of a dependent type is **treated as whole**: [Repack] does not look into it, and [Split-gen] generalises it to a fresh `σ` of the place's type and then splits that `σ` by the telescope, with each field's type computed from the earlier fields. That is sound only if every way a neutral of a dependent type can be produced guarantees that what it stands for is whole at every instance. Call this the **producer obligation**.

## 2. The rules the model forces, against the current ones

| Derived rule | Why the model forces it | Current rule | Status |
|---|---|---|---|
| A field of an open value is typed by what it holds | an open tuple's fields have their own types, not the telescope's | [Open]: a dependent data field "takes its content's type whenever the content does not have its telescope type" | present (see S3 for a simpler equivalent) |
| Writing a dependent data field is untyped against the telescope (a strong update) | the field may be written before the index it depends on | [Open]: strong update | present |
| A proof field can't outlive a change to what its proposition mentions | a proof is ⋆ and carries no record of the values it was about | [Open]: a write or borrow through an index field sets the dependent proof fields to ⊥ | present (see S1) |
| (W) at every ownership boundary | receivers rely on the type | [Repack] at: read, moved or borrowed whole; end of a borrow (including borrow parameters); result; `Id`; captures; a stuck block's arm ends (D72) | present (see S2) |
| A part still lent at a boundary is any value of its borrow's type | a borrow's final content is unknown until it ends | D73: lent parts are checked as fresh unknowns; [Open]'s lent-proof assignment, the same for proofs | present |
| **Producer obligation** for every source of a neutral of dependent type | [Split-gen] and [Repack] trust neutrals | see the producer table below | **one producer was unchecked: D75** |
| No ⊥ inside a value at a boundary | a moved-out or invalidated field is not a value of its type | [Repack]: no ⊥ inside | present |

**The producers of neutrals, and what checks each one:**

| Producer | Stands for | Checked by |
|---|---|---|
| a parameter's abstract value | the caller's argument | the caller: passing a value whole, or borrowing it whole, is a boundary |
| the result of a stuck call, `⌈L; f(ā)⌉` | `f`'s result | `f`'s own [Def]: its result is a boundary |
| a borrowed argument's fill, `⌈L; f(ā); cⱼ⌉` | the final content `f` leaves | `f`'s [Def]: a borrow parameter's end is a boundary |
| a fill with a hole, `⌈…; *r := loan_k; cⱼ⌉` | the content after the caller writes any value through the returned borrow | `f`'s [Def] with the lent part unknown (D73) |
| a stuck match's block | each arm's effect | the arm ends (D72) |
| **a `J` closed off by [T-J-stuck]** | **the effect of the transported term `t`** | **nothing, before D75**; now `t`'s end, as a stuck match's arm |
| a zero-arm match closed off | nothing runs | nothing to check |
| a closure or Π-type | its captures | capture is a boundary |
| generalisation records ([Split-gen], `split f in t`) | a neutral already produced above | inherited |

## 3. The finding: a closed proof of `False` through a closed-off `J` (D75)

[T-J-stuck] types `t` on a private copy, discards its effects, and closes the `J` off with the same machinery as a stuck match. That machinery checks the places a block takes by borrow at the end of each arm, but [T-J-stuck] passed it no end state, so for a `J` block nothing was checked. On the direct path, at an instance where the endpoints are convertible, `J` *is* `t` and runs its writes.

```
JLie (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit :=
  match *v { MkV(n0, x0) => J(Word, a, b, λ(z : Word) : Type => Unit, h,
                               match *v { MkV(n, x) => (n := Zero; ()) }) }
LenStmt (c0 : V) : Prop := (let c = c0; JLie(Zero, Zero, refl, &c); match c { MkV(n, x) => IsSucc(clone(n)) })
LenPf (c0 : V) : LenStmt(c0) := (let c = c0; JLie(Zero, Zero, refl, &c);
                                 match c { MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl } })
BoomJ : False := LenPf(One1)
```

What happens, step by step:
- **In `JLie`**, the endpoints are abstract, so the `J` closes off. Its transported term writes through a pattern variable of `*v`, so the block takes `*v` by `&`. `*v` becomes a sealed program of type `V`, and `JLie`'s return check sees a neutral.
- **`LenPf` is checked at its generic call.** There `JLie` is stuck and closes off, `c` is a neutral of type `V`, and the match splits it as a whole `V`. In the arm `Zero`, `x : Fin1(Zero)` is `Void`, so `match x {}` proves anything.
- **At the instance `One1`**, `JLie` runs, the endpoints are equal, and `t` writes the length: `c = MkV(Zero, O)`. So `LenStmt(One1)` computes to `IsSucc(Zero)`, which is `False`.

All four declarations were accepted on main `4cc0beda`.

**The fix (D75):** the block's one arm is `t`, so the places it takes by borrow are checked whole in the state `t` ends in, with `t`'s result held as a temporary, as D72 does for arms. `JLie` is now rejected with "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open". The twin `JSame`, which writes the length back unchanged, is accepted, and so is its chain, which proves a true statement. Every other caller of `closeOffMatch` was audited: [Split]'s arms already pass their end states, and a zero-arm match runs no body.

## 4. Other shapes checked against the model

All are fail-safe: rejected, or accepted and sound. Each is argued here from the checker's rules and code; only the `J` chain was run.
- **Changing the index while a dependent data field is lent**, e.g. `let r = &x; n := Succ(Zero)`. Rejected at the next boundary: by D73 the lent `x` is an unknown of its borrow's type `Fin1(σₙ)`, against `Fin1(S Z)`. This is incomplete when every reachable index gives the same type, which the generic path cannot see.
- **A call that borrows two fields of one value and changes only the index**, e.g. `Touch(&n, &x)`, whose `x` parameter has type `&Fin1(*k)`, formed once. Rejected at the caller's boundary by telescope mismatch. If the call is stuck, the index is a fill, and `Fin1(⌈fill⌉)` is not convertible with `Fin1(σₙ)`, so it fails safe.
- **A live loan inside a sealed program inside a value at a boundary.** `lentUnknown` does not look inside sealed programs, but a type that mentions such a sealed program is stuck. It is convertible only with a type mentioning the same sealed program, and an [End] substitutes into both consistently. So it fails safe; this is a model argument, not a check.
- **Writing an index after the instance path kept a returned borrow alive.** At an instance [Access] ends fewer loans than on the generic path, never more, since a neutral head forces ending everything inside it. Any later use of the borrow is therefore rejected on the generic path.
- **Proof staleness.** A proof copied out before an index write keeps its declared type, which mentions the old index, so re-assigning it is checked against the new contents (`StaleProof`).

## 5. Candidate simplifications (not implemented)

- **S1. Proofs carry the type they were checked at.** Today a proof is ⋆, so [Open] must set dependent proof fields to ⊥ on every write or borrow of an index, and [Open] has a separate rule for assigning a proof while part of the value is lent. If a proof field's content recorded the proposition it was checked against, [Repack] could check proof fields like data fields: the recorded proposition must be convertible with the telescope's, with lent parts unknown (D73). That replaces the ⊥ invalidation and the lent-proof rule with the one [Repack] mechanism. It costs a recorded type per proof field in the checked program only; runtime proofs stay erased.
- **S2. One principle for the whole-again points.** The paper's list (read, moved or borrowed whole; end of a borrow; result; `Id`; captures; stuck-block arm ends; now `J`'s end) is the set of ownership boundaries in §1. Stating (W) and the producer obligation, and deriving the list from them, would have made D72 and D75 corollaries rather than counterexample-driven additions. This is a change to how the rules are presented, not to the rules.
- **S3. Always type a dependent data field by what it holds.** The [Open] rule compares the content's type with the telescope type and uses the content's when they differ. When they agree the two are convertible, so typing by content always is equivalent and drops a value-dependent decision site (`depFieldType`'s `packedErr` test), which docs/14's two-paths work would welcome. Check before adopting: [Split-gen] and refinement read field types, so their behaviour on open values must be unchanged.

## 6. Open questions

- **Stability.** Every argument here assumes that conversion and the telescope's type computation commute with refinement, i.e. the stability conjecture. The model shows what must be checked, not that the generic check implies the instance's.
- **Incompleteness worth fixing.** A stuck block that captures an index and its dependent field as separate places (both by `&`) and updates them consistently is rejected: each place is checked against its type at capture. Capturing their common parent instead, when an arm writes an index together with a field that depends on it, would accept it. This is a completeness improvement, not a soundness one.
