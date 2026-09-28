# Hashmap flagship: implementation log (agent: hashmap implementer)

Spec: `notes/hashmap-design.md`. Code: `ochr/core/lean/Ochr/Examples/HashMap.lean` (one `ochr HashMap { … }` block, registered in `Registry.lean`). Checker: RULES v1.8 + D42 (the checker on `ochr-hashmap` at 861a6a40); no rule or `Machine.lean` change.

(5-line summary goes here at the end.)

## Phase 1: data types and operations (all accepted)

Data exactly as the spec: `Bool`, `Opt`, `Bucket` (association list), `Slots` (non-empty list of buckets), `HashMap := HM(n, len, slots)`.

| Operation | Shape | Check time (compiled) |
|---|---|---|
| `EqB`, `Lt` | structural on the first argument | 52, 27 µs |
| `ModGo(k, n, r)`, `Idx(k, n) := ModGo(k, n, 0)` | k mod (S n), structural on k with a running remainder; dispatches on `EqB(r, n)` | 62, 13 µs |
| `NthM(s : &Slots, i) : &Bucket by s` | the index borrow; saturates at the last slot | 45 µs |
| `Nth(s, i)` | pure read | 27 µs |
| `BGet(b : &Bucket, k) : Opt by b` | lookup through the borrow | 55 µs |
| `BInsertM(b, k, v) : Bool by b` | overwrite in place, or append at the end; `True` iff added | 65 µs |
| `BRemoveM(b, k) : Bool by b` | `*b := t` at the key; `True` iff removed | 51 µs |
| `InsertNoResize(hm, k, v)` | `r = NthM(&slots, Idx(k, n)); added = BInsertM(r, k, v); if added then len := S len` | 142 µs |
| `Get(hm, k)`, `Remove(hm, k)` | through `NthM` | 53, 122 µs |
| `BLen`, `Count` | pure sizes (`Count` sums with `Add`) | 19, 42 µs |
| `EmptySlots(n)`, `New(n)` | `S n` empty buckets | 19, 13 µs |
| `MoveBucket(b, hm)`, `MoveSlots(s, hm)` | re-insert every entry with `InsertNoResize`, structural on the moved-out data | 40, 40 µs |
| `Resize(hm)` | `old = slots; *hm := New(S (n + n)); MoveSlots(old, hm)` (doubles the slot count) | 60 µs |
| `Insert(hm, k, v)` | `InsertNoResize`, then `Resize` if `Lt(n, len)` (load factor 1) | 110 µs |

Everything was accepted as first written. Things worth noting:
- `NthM` returns `&b`, a borrow of a field of the borrowed slot list (a reborrow), in both arms; the recursion `NthM(&t, i')` is the TailM pattern. No bounds proof anywhere.
- `Resize` assigns `*hm` inside the arm of a `match *hm` whose pattern variables alias `(*hm).slots` (the copy `old = slots` is taken first). Fine: pattern variables are places, not borrows.
- `Insert` matches on `*hm` again after `InsertNoResize(&*hm, …)` and reborrows `&*hm` inside that arm for `Resize`.

Concrete runs (12, as `Id … := refl` over closed programs; 1 rejected on purpose): three inserts into a 2-slot table, the second reaching the load factor and resizing to 4 slots (`RunLayout` checks the exact final table `HM(3, 3, [∅, [1↦10], [2↦20], [3↦30]])`); each key is found (`RunGet1..3`), an absent one is not, a wrong value is rejected (`RunGetWrong`: "the goal is Eq Opt Some(10) Some(20)"); overwrite keeps `len`; a colliding key shares a bucket (`RunCollide`); remove (present and absent) and get-after-remove; and `len = Count(slots)` after a mixed run of five operations (`RunCount`). The runs take 0.4–0.9 ms each; `RunCount` 4.8 ms (two full runs plus `Count`).

Ledger: switching off generalise-then-split (C8) rejects every definition that dispatches on `EqB`/`Lt` (their results are sealed at the generic call) and every run built on them: 23 flips, asserted in `Registry.lean` as `hashMapGeneralize`. No other ledger row flips on the hashmap.

## Phase 2: bucket-level theorems (all accepted)

| Theorem | Statement (`b : &Bucket`) | Verdict | Proof shape | Time |
|---|---|---|---|---|
| H1 `BInsertGet` | `Id Opt (BInsertM(&*b,k,v); BGet(&*b,k)) (BInsertM(&*b,k,v); Some(v))` | accepted | recursion on `*b`; BNil: split on `EqB(k,k)`, the False arm by `ExFalsoFT(goal, EqBRefl(k))`; BCons: split on `EqB(k',k)`, False = IH, True = `refl`. 0 J steps (1 inside `ExFalsoFT`) | 1.6 ms |
| H2 `BInsertGetOther` | given `h : Id Bool (EqB(k,k2)) False`: `Id Opt (BInsertM(&*b,k,v); BGet(&*b,k2)) (let r = BGet(&*b,k2); BInsertM(&*b,k,v); r)` | accepted | recursion; 2 nested `EqB` splits per cons cell; IH in one arm, `refl` in two, ex falso in two (`BoolAbsurd`, and `EqBTrans` for "k' = k and k' = k2 but k ≠ k2") | 3.5 ms |
| H1' `BRemoveGet` | given `h : AtMostOnce(*b, k)`: `Id Opt (BRemoveM(&*b,k); BGet(&*b,k)) (BRemoveM(&*b,k); None)` | accepted | recursion; found arm = `let c = t; BGetAbsent(&c, k, h)` (a lemma on a copy of the tail) | 1.2 ms |
| H2' `BRemoveGetOther` | given `k ≠ k2`: as H2 with `BRemoveM` | accepted | as H2 | 2.6 ms |

Helpers (all accepted): `ExFalso` (E5's), `ExFalsoFT(G, h : Eq Bool False True) : G` and `BoolAbsurd(x, x = False, x = True)` by one J each; `EqBRefl` by bare recursion; `EqBSound : EqB(a,b) = True → a = b` by recursion with one J (congruence under `S`: D16 removed Nat injectivity, so `Eq Nat (S a) (S b)` does not reduce); `EqBTrans` by one J; `BAbsent(b, k)`, `AtMostOnce(b, k) : Prop` (Le-style Prop-valued recursion that dispatches on `EqB`); `BGetAbsent : BAbsent(*b,k) → Id Opt (BGet(&*b,k)) None` by recursion.

Negative tests (rejected, reasons checked): `BInsertGetNoLemma` (BNil arm by `refl`: the goal still holds `⌈…BGet(&c1, σ1)⌉` stuck on `EqB(σ1, σ1)`), `BInsertGetWrongValue` (`Some(k)`: goal `Eq Opt Some(σ2) Some(σ1)`), `BInsertGetOtherNoHyp` (goal `Eq Opt Some(σ2) None` in the k = k2 arm), `BRemoveGetNoHyp` (duplicate keys: `⌈BGet(σ4, σ1)⌉` vs `None`).

**Finding F1 (a read through `&T` is only propositionally the identity).** `BGet(b : &Bucket, k)` reads through a mutable borrow (the core has no shared borrows). When it gets stuck on an abstract tail, [Close] fills the borrowed place with the backward program `⌈let c1 = u; BGet(&c1, k); c1⌉`, which is semantically `u` but not definitionally. So every statement whose one side reads with `BGet` and whose other does not has a second conjunct about the bucket, e.g. H1's goal is `Eq Opt ⌈…BGet…⌉ Some(v) ∧ Eq Bucket ⌈…BGet(&c1, k); c1⌉ ⌈…⌉` (the trace of `BInsertGet`). The theorems as stated are therefore *stronger* than Aeneas's (they also say that the lookup leaves the bucket as it was), and this is harmless for H1–H2' because the proofs are bare recursion: the IH carries the same conjunct and the base cases compute it away. It costs where lemmas are composed: the core has no ∧-elimination (a proof of `P ∧ Q` cannot be projected: no neutral projections, and J cannot do it), so a lemma whose type carries the residue conjunct can only be used where the goal carries the same conjunct. Two techniques keep it usable, both used below: (a) call the lemma on a *copy* the proof owns (`let c = t; BGetAbsent(&c, k, h)`), so its footprint is exactly the place the goal observes, not the enclosing cell; (b) lift the lemma by recursion through the enclosing structure, so the environment performs the congruence (next phases).

**Ledger.** Switching G1 off (a generalised sealed program stays generalised when re-derived) rejects all five bucket theorems (`hashMapG1` in Registry.lean): the proofs split on `EqB(k', k)` in the proof body, and the goal's sealed programs re-derive that comparison inside `BInsertM`/`BGet`/`BRemoveM`. Switching generalise-then-split (C8) off rejects every hashmap declaration that dispatches on `EqB` (30).

Build: the full `lake build` went from 26 s to 68 s, because each of the 30 ledger rows re-checks the hashmap twice in the interpreter (about 0.3 s per check).

## Phase 3: the index borrow (all accepted)

| Theorem | Statement (`s : &Slots`) | Verdict | Proof shape | Time |
|---|---|---|---|---|
| H3a `NthWriteSame` | `Id Bucket (let r = NthM(&*s,i); *r := x; Nth(*s,i)) (let r = NthM(&*s,i); *r := x; x)` | accepted | bare recursion on `*s` and `i`; 0 J | 0.26 ms |
| H3b `NthWriteOther` | given `EqB(i,j) = False`, `Le(i, Last(*s))`, `Le(j, Last(*s))`: `Id Bucket (let r = NthM(&*s,i); *r := x; Nth(*s,j)) (let v = Nth(*s,j); let r = NthM(&*s,i); *r := x; v)` | accepted | recursion on `*s`, split `i`, `j`; `refl` in the two mixed arms, IH in (S, S), ex falso in (0, 0) and the out-of-range arms | 1.0 ms |

`NthWriteOtherNoRange` (H3b without the range hypotheses) is rejected: two different indices past the end both hit the last slot (goal `Eq Bucket σ3 σ4`). The map-level proofs turned out not to need H3 at all (next section).

## Phase 4: map level, for InsertNoResize (all accepted)

The route the spec suggested (H4 = H1 + H3, rewriting with J at the map level) runs into F1 and the missing ∧-elimination: H1 carries a bucket conjunct, and a J at the map level needs a motive that rebuilds the whole map from the rewritten bucket. Instead each bucket lemma is **lifted through the index borrow by recursion on the slots**, mirroring `NthM`'s own recursion: in each cons cell the recursive call borrows the tail field, so the environment carries the untouched slots, exactly as in `AddZero`/`AppendMNil`. Then the map-level theorem is a case split plus one call of the lifted lemma on a copy of the map. No congruence lemma and no J anywhere in H4/H5.

| Theorem | Verdict | Proof shape | Time |
|---|---|---|---|
| `NthInsertGet(s, i, k, v)`: H1 through `NthM` | accepted | bare recursion on `*s`, `i`; leaves are `BInsertGet(&b, k, v)` | 1.0 ms |
| H4 `InsertGet(hm, k, v)`: `Id Opt (InsertNoResize(&*hm,k,v); Get(&*hm,k)) (InsertNoResize(&*hm,k,v); Some(v))` | accepted | `match *hm`; reproduce the sealed `added` on a copy of the slots and split on it; in each arm build `d = HM(n, len', slots)` with the arm's length and call `NthInsertGet(&d.slots, Idx(k,n), k, v)` (its footprint is the whole `d`, so its type is the goal's) | 1.0 ms |
| `NthInsertGetOther`: H2 through `NthM` (write at i, read at j) | accepted | recursion; same bucket = H2, different buckets = `refl` (they commute by computation) | 2.1 ms |
| `BInsertAfterGet`, `NthInsertAfterGet`: an insert's result does not see an earlier lookup | accepted | recursion (bucket), then lifted (slots); both on copies so their type is a single `Eq Bool` | 0.4, 0.8 ms |
| H5 `InsertGetOther(hm, k, v, k2, k ≠ k2)`: `Id Opt (InsertNoResize(&*hm,k,v); Get(&*hm,k2)) (let r = Get(&*hm,k2); InsertNoResize(&*hm,k,v); r)` | accepted | split on *two* `added` programs (see F1'), 2 arms by `NthInsertGetOther` on a copy, 2 arms ex falso from `NthInsertAfterGet` | 3.9 ms |

Negative tests: `InsertGetSwapLen` (lengths swapped between the arms: rejected, `HM(σ3, S σ4, …)` vs `HM(σ3, σ4, …)`), `InsertGetOtherNoIndep` (mixed arms by `refl`: rejected).

**F1' (F1 at the map level).** In H5's right side the lookup runs first, so the insert that follows computes its `added` from the bucket's read-residue: a different sealed program from the left side's `added` (`⌈BInsertM(NthRead(σs, i))⌉` vs `⌈BInsertM(NthRead(⌈Get-back σs⌉, i))⌉`). The proof must split on both and refute the two mixed arms with an extra lemma pair ("an insert's result does not see an earlier lookup"). With shared borrows (or a lookup that does not leave a backward program) this lemma pair and two of the four arms would disappear.

## Phase 5: the length invariant (all accepted)

| Theorem | Verdict | Proof shape | Time |
|---|---|---|---|
| `BInsertLen(b, k, v)`: `Bump(added, BLen(*b)) = BLen(after)` | accepted | recursion, split on `EqB` and on the tail's `added`; 1 J per arm (congruence under `S`) | 0.73 ms |
| `NthInsertCount(s, i, k, v)`: lifted to `Count` | accepted | recursion; SOne leaf = `BInsertLen` directly; other leaves 1 J (congruence under `Add`), the (S, True) arm also `AddS` (x + S y = S (x + y), in place by bare recursion) | 2.0 ms |
| H6 `InsertLen(hm, k, v, h : Len(*hm) = CountHM(*hm))`: `Id Nat (InsertNoResize(&*hm,k,v); Len(*hm)) (InsertNoResize(&*hm,k,v); CountHM(*hm))` | accepted | split `*hm`, `added`; the slot lemma on a copy of the slots; 1 J (not added) or 2 J (added) against `h` | 1.0 ms |
| `BRemoveLen`, `NthRemoveCount`: `Bump(removed, count after) = count before` | accepted | as above, through small lemmas `CongS`, `CongAddL/R`, `TransN`, `SymmN` (1 J each) | 0.55, 1.6 ms |
| H6 `RemoveLen(hm, k, h)`: the same for `Remove` (`len := Pred(len)`) | accepted | split, then `TransN`/`SymmN`/`CongPred` | 1.0 ms |

`InsertLenNoHyp` (no invariant hypothesis) is rejected.

**Finding F2 (rules gap: a generalisation is never refined).** The natural statement of `BInsertLen` puts the case distinction inline: `… match a { False => BLen(*b) | True => S (BLen(*b)) }` with `a = BInsertM(&c, k, v)`. Forming this type at the generic call type-checks the inline match (D33), which splits on `a`, whose value is the sealed `⌈let c1 = σ0; BInsertM(&c1, σ1, σ2)⌉`, so [Split] first generalises it to a fresh `σ3` (D22/D34) — for good: the record is global (D37) and the stuck block that the type closes off captures `σ3`, not the sealed program. When the proof then splits `σ0 := BNil`, the sealed program would compute `True`, but nothing links it to `σ3`: [Split] applies refinements to "Ω, the goal and all stored types", not to the generalisation records, so the goal keeps `⌈block(BNil, σ3)⌉` and is unprovable (`BInsertLenInline`, rejected: goal `Eq Nat ⌈block(BNil, σ3)⌉ 1`). Minimal program (`InlineLost`, rejected; true):
```
IsZ(x : Nat) : Bool := match x { Z => True | S _ => False }
InlineLost(x : Nat) : Id Nat (let a = IsZ(x); match a { False => 0 | True => 1 }) (match x { Z => 1 | S _ => 0 }) := match x { Z => refl | S _ => refl }
```
RULES v1.9 as written rejects it too (the checker follows the rules here). It is incompleteness, not unsoundness (an unrefined `σ3` only makes goals harder). Workaround used throughout: put the case distinction in a helper function (`Bump(a, n)`, `B2N(a)`): a call is not split while the type is formed, so it stays a sealed call of the sealed `a` and is re-derived after the refinement (`HelperKept`, accepted). Suggested fix for RULES: a [Split] refinement also applies to the generalisation records — refining `σ0` in a record's key `⌈n⌉ := σ3` re-normalises the key, and if it computes to a value `v` this refines `σ3 := v` (Lean's `generalize h : f x = y` keeps `h`, which `cases x` rewrites). Alternatively, generalise only while checking a stuck block's arms and close the block off over the original sealed program.

**Finding F3 (checker gap, known: lean-checker §11.2).** A λ that captures a computed local holding a sealed value and uses it in a typed position is rejected at formation ("cannot infer the type of the value ⌈…⌉"): captured values carry no type in the checker. `CaptureSealed` (rejected) is `let L = Add(x, y); J(Nat, L, y, λ(z : Nat) : Prop => Id Nat (S L) (S z), h, refl)`; RULES v1.9 accepts it (the captured `L : Nat` has a type in Ω). Workaround: make the motive a top-level lemma over parameters (`CongS(x, y, h)`, `CongAddL/R`, `CongPred`, `TransN`, `SymmN`), which is also what Lean's library does (`congrArg`, `Eq.trans`). It forced four small lemmas; no statement changed.
