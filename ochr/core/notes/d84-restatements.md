# D84: the statements restated

D84 went through two versions (`DECISIONS.md`, D84). The first made `Id` observe every owned, non-proof place a side reads, since a read may move it and moves are definite: a statement whose sides consume different places became false (`F(x)` against `F(y)`). The revision drops that and makes `Id(A, t, u)` well formed only where `t` and `u` leave the same type-state ([Id-typestate]): the same places moved, the same borrow bindings consumed, re-pointed and left open, and no borrow held outside a side ended inside it. The first version's restatements are kept (the first table below): each was restated because one side consumed a place the other left, which is a type-state difference too. The revision's own restatements follow it.

## The first version (kept)

The suite had 43 such statements, plus 2 whose own statement read a place on one side only and that failed with their lemma (`InstPow`, `AtIdTySealed`). Each is restated in one of two ways, so that it says what it was there to say:

- **On a copy** (`clone`): the side that consumed an argument consumes a copy of it instead. A clone denotes the same value, so the results and the effects on written places are the old statement's, and the statement now also says that the argument is left alone (trivially). The proof is unchanged in every case.
- **The same consumption on both sides**: where the tested side's text is the point of the test, the other side consumes the same place (`let m = n; …`).

None was weakened: every restated statement proves what it proved before about results and written places, and no proof changed. In none of them was the consumption itself the point of the statement.

**Case studies** (marked ★ below; Charlie may want to review them before the merge): `ArrayBench.B1Join` and nine `HashMap` lemmas. Their restatements are of the first kind: the statement runs `MoveBucket`, `MoveFrom`, `Insert` or `InsertNoResize` on `clone(m)`, or inserts `clone(v)`, `clone(b)`, `clone(s)`, where it consumed `m`, `v`, `b`, `s` on one side only. `Quicksort` and `Array` are unaffected by this version.

| Statement | Old | New | Meaning |
|---|---|---|---|
| Numbers.AliasRead | `Id(Nat, (let m = x; match m {…}), (match x {…}))` | `let m = clone(x)` | same: the pattern variable aliases `m.0` |
| Numbers.PairBorrowIs | `Id(Nat, PairBorrow(n), 7)` | `PairBorrow(clone(n))` | same |
| Numbers.CallProj | `Id(Nat, PairWrite(n).1, 5)` | `PairWrite(clone(n)).1` | same |
| Numbers.TripWriteIs | `Id(Trip, TripWrite(n), MkTrip(7, (), 5))` | `TripWrite(clone(n))` | same |
| Erasure.Lie | `…; W(&c, n); c, S(Z))` | `W(&c, clone(n))` | same; `Boom := Lie(Z)` still rejected |
| Erasure.LieL | `…; h(&c); c, S(Z))` (the closure captures `n`) | right side `(let m = n; S(Z))` | same; the tested closure is unchanged |
| Erasure.Lie8 | `let g = MkClosure(n)` | `MkClosure(clone(n))` | same |
| Borrows.LetZ | `let h : Id(Nat, z, 2) = refl` | `Id(Nat, clone(z), 2)` | same |
| Equality.RwSplit | `Id(Nat, Add(y, 0), x)` | `Id(Nat, Add(clone(y), 0), clone(x))` | same (the old one is the `F(x)`/`F(y)` shape, `Moves84.FxFy`) |
| BorrowTypes.UseSetIfS | `Id(Nat, UseSetIf(S(n)), 4)` | `UseSetIf(S(clone(n)))` | same |
| Functions.TwiceNoop | `Id(Unit, Twice(f), ())` | `Twice(clone(f))` | same: `Twice` does nothing |
| Functions.TwiceMMove | `Id(Unit, TwiceM(f, x), f(&*x); f(x))` | `TwiceM(clone(f), x)` | same: moving `x` into the second call makes no difference |
| Functions.TwiceMZero' | motive `Id(Nat, Add(Add(s, 0), 0), z)` | `Id(Nat, Add(Add(clone(s), 0), 0), clone(z))` | same |
| Functions.RunGGen | `Id(Nat, RunG(f), Z)` | `RunG(clone(f))` | same; `Boom := RunGGen(H)` still rejected |
| Functions.RunIGen | `RunI(f)` | `RunI(clone(f))` | same |
| Functions.RunPowGen | `RunPow(p)` | `RunPow(clone(p))` | same; `BoomPow` still rejected, `BoomPowOk` accepted |
| Functions.InstPow | `Id(Nat, RunPow(PickP(n)), Z)` | `PickP(clone(n))` | same (its own statement read `n` on one side) |
| Functions.DirectPow | `RunPow(PickP(n))` | `RunPow(PickP(clone(n)))` | same |
| Functions.RunT0Gen | `RunT0(p)` | `RunT0(clone(p))` | same |
| Functions.RunRecGen | `RunRec(n, p)` | `RunRec(clone(n), clone(p))` | same |
| Functions.RunIdTyGen | `RunIdTy(p)` | `RunIdTy(clone(p))` | same |
| Functions.AtIdTySealed | `Id(Nat, RunIdTy(PickP(n)), Z)` | `PickP(clone(n))` | same (its own statement read `n` on one side) |
| Functions.RunU | `Id(Unit, let c = n; f(&c), ())` | `let c = clone(n)` | same |
| Functions.SndOfGen | `Id(Nat, SndOf((a, clone(b))), b)` | `Id(Nat, SndOf((clone(a), clone(b))), clone(b))` | same: a capture projected in a closure's body |
| Inductives.SizeInsert (×2, both `Trees` versions) | three `J` motives, e.g. `Id(Nat, S(z), S(Add(Size(l), Size(Insert(r, k)))))` | every variable a motive reads cloned, e.g. `Id(Nat, S(clone(z)), S(Add(Size(clone(l)), Size(Insert(clone(r), k)))))` | same: the motives compare numbers |
| ClosingOff.AddToOneZero, ', '' | `Id(Unit, AddToOne(b, x1, x2, 0), ())` | `AddToOne(clone(b), …)` | same: adding zero through the chosen borrow does nothing |
| ClosingOff.LamReadInWrittenBlock | right side `match q2 { Mk(p5, p6) => p5 }` | `(let d = q2; match d { Mk(p5, p6) => p5 })` | same; the tested left side is unchanged (it consumes `q2` whole) |
| CloseOffModel.CoPick | `let r = Pick(n, a, b)` | `Pick(clone(n), a, b)` | same |
| ClosingOff.CoGen | `Id(Nat, Add(clone(x), 0), S(q))` | `S(clone(q))` | same |
| ClosingOff.CoGenTwice | `Id(Nat, Add(clone(x), 1), S(S(r)))` | `S(S(clone(r)))` | same |
| DeclaredReadings.ExUAt | `ExU((), n)` | `ExU((), clone(n))` | same |
| DeclaredReadings.ExUGen | `ExU(x, n)` | `ExU(x, clone(n))` | same |
| ★ ArrayBench.B1Join | `WithSplit(E, Unit, n, k, s, h, λ(l)(r) => g(l))` (the closure captures `g` by move; the right side calls `g` in place) | `(let g2 = clone(g); WithSplit(…, λ(l)(r) => g2(l)))` | same: for any `g`, the view after the split is `g`'s result on the first `k` elements joined to the rest |
| ★ HashMap.MoveBucketLen | `let c = m; MoveBucket(V, b, &c); Len(V, c)` | `let c = clone(m)` | same: moving a bucket of fresh keys adds its length |
| ★ HashMap.MoveFromLen | `let c = m; let o = s; MoveFrom(…, &c); Len(V, c)` | `let c = clone(m)` | same |
| ★ HashMap.InsertFindR | `let c = m; Insert(V, &c, k, v); Find(V, c, k)` | `let c = clone(m)` | same: after inserting `(k, v)`, finding `k` gives `v` |
| ★ HashMap.InsertFindOtherR | `Insert(V, &c, k, v); Find(V, c, k2)` (only the left side consumed `v`) | `Insert(V, &c, k, clone(v))` | same: the found value does not depend on `v` |
| ★ HashMap.InsertResultR | `Insert(V, &c, k, v)` | `Insert(V, &c, k, clone(v))` | same |
| ★ HashMap.InsertLenR | `Insert(V, &c, k, v); Len(V, c)` | `Insert(V, &c, k, clone(v))` | same |
| ★ HashMap.InsertN | `InsertNoResize(V, &c, k, v); NOf(V, c)` | `InsertNoResize(V, &c, k, clone(v))` | same |
| ★ HashMap.MoveBucketN | `MoveBucket(V, b, &c); NOf(V, c)` | `MoveBucket(V, clone(b), &c)` | same |
| ★ HashMap.MoveFromN | `let o = s; MoveFrom(…)` | `let o = clone(s)` | same |

The cascades (`BoomPowOk`, `InstPowZ`, `AtRec`, `AtIdTy`, `RunUH`, `ResizeLen`, `ResizeN`, `InsertNotOver`) needed no change: their statements consume the same places on both sides, and they failed only through the lemmas above.

### Rejected tests restated to keep their reason

Fifteen `reject def`s stayed rejected, but for a new reason: one side consumed a place the other left, so their goal gained a `False` conjunct, which masked the failure each was written for (`StuckGoalWrong` was meant to fail at `b ≥ 2`, and now failed at `b = 0` on `b`'s consumption). Each is restated the same way, on a copy, and each is again rejected with its message on main, verbatim:

| Test | Old | New |
|---|---|---|
| FrameModel.ReassignLie | `let c = c0` | `let c = clone(c0)` |
| ClosingOff.StuckGoalWrong | `Id(Nat, (match b {…}), b)` | `…, clone(b))` |
| ClosingOff.Bad | `(h : Id(Nat, b, 0))` | `(h : Id(Nat, clone(b), 0))` |
| CloseOffModel.CoPickOnlyA, CoPickBoth, CoPickRefl | `Pick(n, a, b)` | `Pick(clone(n), a, b)` |
| DeclaredReadings.ExAAt | `ExA(Unit, (), n)` | `ExA(Unit, (), clone(n))` |
| Equality.JT | `JF(a, b, h, &c)` | `JF(clone(a), clone(b), h, &c)` |
| Snapshots.Oops2 | `(h : Π(_ : Unit). Id(Nat, x, 0))` | `Id(Nat, clone(x), 0)` |
| GlobalRecords.Esc | `let b = Double(n)` | `let b = Double(clone(n))` |
| Trees.SizeInsertNoLemma | the `J` motives, as in `SizeInsert` | every variable they read cloned |
| PolyLists.AppendMOne | `Cons(a, Nil)` | `Cons(clone(a), Nil)` |
| Subsingletons.SqZero | `(refl : Id(Nat, n, 0))` | `Id(Nat, clone(n), 0)` |
| ErasureBySyntax.P3d | `let h : Id(Nat, c, Z) = refl` | `Id(Nat, clone(c), Z)` |
| FnBorrows.UseSetIfWrong | `Id(Nat, UseSetIf(n), 3)` | `UseSetIf(clone(n))` |

## The revision: borrows passed whole become explicit reborrows

A borrow binding passed whole to a call is consumed: the call takes the borrow, and the binding is `⊥` after it. So `Id(Unit, AddM(x, 0), ())` relates a side that consumes `x` to one that leaves it, and is ill-formed (`Moves84.Consumes`). In every statement below the call was meant to act on `*x`, not to take `x`, and the restatement passes an explicit reborrow, `&*x`: the call borrows `*x` for its duration and `x` holds its borrow again afterwards, on both sides. The statement says what it said about `*x` (the owner of `x`'s loan is observed as before), and also that `x` is still a borrow afterwards. No proof changed: a proof that cites the lemma at `x` (`AddMZero(x)`) still does. `Moves84.Reborrows` is the restated `Consumes`.

| Statement | Old | New |
|---|---|---|
| Nats.AddMZero (the paper's first lemma) | `Id(Unit, AddM(x, 0), ())` | `AddM(&*x, 0)` |
| Nats.AddMS | `AddM(x, S(y))` | `AddM(&*x, S(y))` |
| Equality.AddMZeroLet | `let n = 0; AddM(x, n)` | `AddM(&*x, n)` |
| Equality.IdIsConjSealed, IdIsConj, IdIsEq, EqIsId (and the reject twin IdIsWrong) | `h : Id(Unit, AddM(x, 0), ())` | `AddM(&*x, 0)` |
| Sorts.Stmt | `RunK(k, x)` | `RunK(k, &*x)` |
| CurrentState.AddSubId, AddSubIdReborrow | `AddSub(x, y)` | `AddSub(&*x, y)` |
| Propositions.SndProj, Snd | `Id(Unit, AddM(x, 0), ())` | `AddM(&*x, 0)` |
| Propositions.WriteIfId, WriteIfAt (and the reject twin WriteIfAtLie) | `WriteIf(x, P, Q, h)`; `AddM(y, 0)` | `WriteIf(&*x, …)`; `AddM(&*y, 0)` |
| Propositions.TwoAt (and the reject twin TwoAtLie) | `Id(Unit, AddM(y, 0), ())` | `AddM(&*y, 0)` |
| Subsingletons.EffLNoopOk | `EffLOk(x, h)` | `EffLOk(&*x, h)` (the twin of `EffLNoop`, restated below; `EffLOk`'s call is a proof, so `x` was not consumed either way) |
| ReturnedBorrows.TailNoop | `let t = TailM(x); ()` | `TailM(&*x)` |
| Functions.TwiceMZero, TwiceMZero' | `TwiceM(λ(z) => AddM(z, 0), x)` | `…, &*x)` |
| Functions.UseA, PassA | `Π(x : &Nat). Id(Unit, AddM(x, 0), ())` | `AddM(&*x, 0)` (`PassA`: `AddM(&*y, t)`) |
| Functions.Q, TX | `let r = h(x, y); *r := S(Z)` | `h(&*x, &*y)` |
| Sugar.BumpIsMatch | `Id(Unit, Bump(&*m), BumpMatch(m))` | `BumpMatch(&*m)`: both sides now reborrow, as the left side already did |
| Abstraction.GetIs | `Get(s)` | `Get(&*s)` |
| NatLists.AppendMNil, PolyLists.AppendMNil | `AppendM(xs, Nil)` | `AppendM(&*xs, Nil)` |
| Trees.InsertMEq, InPlaceTrees.InsertMIsInsert | `InsertM(t, k)` | `InsertM(&*t, k)` |
| ClosingOff.AddToOneZero, ', '' | `AddToOne(clone(b), x1, x2, 0)` | `AddToOne(clone(b), &*x1, &*x2, 0)` |
| CloseOffModel.CoPick (and the reject twins CoPickOnlyA, CoPickBoth, CoPickRefl) | `Pick(clone(n), a, b)` | `Pick(clone(n), &*a, &*b)` |
| ★ ArrayLemmas.GetMutSet | `*GetMut(E, n, s, i, h) := w` | `GetMut(E, n, &*s, i, h)` |
| ★ ArrayLemmas.GetMutRead | `clone(*GetMut(E, n, s, i, h))` | `GetMut(E, n, &*s, i, h)` |
| ★ ArrayLemmas.SwapLtIsSwapS | `SwapLt(E, n, s, i, j, …)` | `SwapLt(E, n, &*s, …)` |
| ★ ArrayLemmas.SwapIsSwapS | `Swap(E, n, s, i, j, …)` | `Swap(E, n, &*s, …)` |
| ★ ArrayBench.B1Join | `WithSplit(E, Unit, n, k, s, h, …)` | `WithSplit(…, &*s, h, …)` (on top of the first version's `clone(g)`) |
| ★ ArrayBench.ReadIsNth | `*GetMut(Word, n, s, i, h)` | `GetMut(Word, n, &*s, i, h)` |
| ★ ArrayBench.SwapIsSwapSRefl (reject) | `Swap(E, n, s, …)` | `Swap(E, n, &*s, …)` |

**Case studies.** `Quicksort`'s `QSCorrect` cites `SwapIsSwapS` and `GetMutRead` (by `rewrite`), whose statements changed. `Quicksort`'s own text is unchanged and still accepted: the rewrites find the restated equations' sides in its goals as before. `HashMap` needed nothing beyond the first version, since its statements already pass `&*hm`.

## The revision: owned places moved on one side

| Statement | Old | New | Intent |
|---|---|---|---|
| Snapshots.PiCopy | `Π(n : Nat). Id(Nat, n, m)` | `Id(Nat, clone(n), clone(m))` | kept: the Π-type captures `m`, a copy of `*x`, not the borrow |
| Snapshots.CapPi | `Π(y : Nat). Id(Nat, n, y)` | `Id(Nat, clone(n), clone(y))` | kept: the Π-type captures `n`, the copy made after the write |
| FordAttack.CastRefl | `Id(VecF(Word, Zero), CastV(…, clone(v)), v)` | right side `clone(v)` | kept: the cast of a copy is the copy |
| ClosingOff.LamReadOtherArm | right side `0` | `(let m = n0; 0)` | kept: the tested left side (its block takes `n0` by move) is unchanged |
| ClosingOff.MoveBorrowBlk | right side `()` | `(let m = n1; ())` | kept: the tested left side is unchanged, and `MoveBorrowSplit` still fails on it with the [Join] reason |
| StuckBlocks.LieDroppedOk (and the reject twin LieDropped) | right side `()` | `(let w = v; ())` | kept: the left side moves `v` into `w` |

## The revision: a borrow ended before the `Id`, not inside it

`CloseOffModel.CoInert`, `CoWrittenFirst`, `CoPerArm` and `CoBlockBorrow`, and their reject twins `…Off`, form `Id(Nat, clone(c), 7)` (or similar) in a body while `t = TailM(&c)` (in `CoBlockBorrow`, `r`) holds a borrow into `c`. The side `clone(c)` reads `c`, which ends `t`'s borrow, and the side `7` does not: the no-ending clause rejects it (docs/30 measured these four as F4's cost). Each now ends the borrow first, `(let u = t; ());` before the `Id`. Intent kept: the statement is about `c`'s content after the write through `t`, and nothing uses `t` afterwards. The twins are again rejected with their messages on main.

## The revision: rejected tests restated to keep their reason

Fifteen `reject def`s would otherwise have been rejected by [Id-typestate] before reaching the failure each was written for. Each is restated the same way as the statements above, and each is again rejected with its message on main, verbatim (`PassWrong`'s message prints its statement, now with `clone(n)`):

| Test | Old | New |
|---|---|---|
| Numbers.WriteThenRefl | `Id(Nat, *x, 5)` | `Id(Nat, clone(*x), 5)` |
| Snapshots.WriteThenRefl', LamWrite | `Id(Nat, *x, 5)` | `Id(Nat, clone(*x), 5)` |
| Snapshots.SnapshotLie | `Id(Nat, x, 0)` | `Id(Nat, clone(x), 0)` |
| Moves.GhostRead | `Id(Nat, n, m)` | `Id(Nat, clone(n), clone(m))`: the statement still reads the moved `n` (`[Read]`) |
| Owners.BadC2 | `Id(Nat, n, 0)` | `Id(Nat, clone(n), 0)`: still rejected because `G` is |
| Functions.PassWrong | `Π(n : Nat). Id(Nat, n, 0)` | `Id(Nat, clone(n), 0)` |
| NatLists.AppendMOne, PolyLists.AppendMOne | `AppendM(xs, …)` | `AppendM(&*xs, …)` |
| Trees.InsertMSwapEq | `InsertMSwap(t, k)` | `InsertMSwap(&*t, k)` |
| Propositions.WriteIfLie | `WriteIf(x, P, Q, h)` | `WriteIf(&*x, …)` |
| Subsingletons.EffLNoop, EffLOne | `EffL(x, h)` | `EffL(&*x, h)`: still rejected because `EffL` is |
| ArrayBench.SplitNoopRefl | `WithSplit(…, s, h, …)` | `WithSplit(…, &*s, h, …)` |
| ArrayBench.ReadNoopRefl | `GetMut(E, n, s, i, h)` | `GetMut(E, n, &*s, i, h)` |

The twelve reject twins restated with their statements above (`IdIsWrong`, `WriteIfAtLie`, `TwoAtLie`, `CoPickOnlyA`, `CoPickBoth`, `CoPickRefl`, `SwapIsSwapSRefl`, `LieDropped` and the four `…Off`) keep their messages on main too.

## The paper's body

`intro.typ` and `overview.typ` §2 state `AddMZero(x : &Nat) : Id(Unit, AddM(x, 0), ())`, which is now ill-formed (the checked `Nats.AddMZero` says `AddM(&*x, 0)`). `obs.typ`'s "Unobserved moves are harmless" says the two sides may consume different borrow variables, and that `Id(Nat, let z = a; Z, Z)` holds; both are now ill-formed. Not changed in this landing: they are paper claims.
