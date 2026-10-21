import Ochr.Examples.Array

/-! # Quicksort: in-place quicksort, proved sorted and a permutation (B2)

In place, over a view, recursing over indices only. The partition is Lomuto's scan with index
bounds proved from its invariant; the recursive calls get the two sides of the pivot as
borrowed pieces. What is proved (`QSCorrect`): quicksort's result is sorted and is a permutation
of its input, with fuel equal to the length.
* `QSPerm`: quicksort permutes its view (every count is unchanged), for any fuel.
* `QSSorted`: quicksort sorts its view, for fuel at least the length, given the partition's
  contract: four facts about `Partition` (`PartLe`, `PartLeft`, `PartPivot`, `PartRight`).
* `PartLeProof` … `PartRightProof`: the partition meets that contract, for every input. This is
  Lomuto's invariant: the pivot stays at 0, cells `1 … i` are at most it, cells
  `i + 1 … j - 1` are greater (`ScanLt`, `ScanPivot`, `ScanLeft`, `ScanRight`, by recursion on
  the countdown). It is bridged to the contract's pieces by `AllLeTakeOf`, `TakeOneDrop` and
  `AllGeDropOf`.
-/

open Ochr.Test

ochr Quicksort uses ArrayLemmas {
  -- Lomuto's partition around the pivot `p`, which sits at index 0. Elements `1 … i` are at
  -- most `p` and `i + 1 … j - 1` are greater; `rem` elements are still to scan (`rem + j = n`).
  -- The recursion is on `rem`, never on the view. Every bound is a lemma about indices.
  def Scan (n : Word) (s : &Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word)
      (hij : Lt(i, j)) (hr : Eq(Word, WAdd(rem, j), n)) : Word by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        Swap(Word, n, s, Zero, i, LeTrans(Succ(Zero), Succ(i), n, refl, hin), hin);
        i
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        let x = *GetMut(Word, n, &*s, j, hjn);
        let b = LeB(x, p);
        match b {
          true => (
            Swap(Word, n, &*s, Succ(i), j, LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn), hjn);
            Scan(n, s, p, Succ(i), Succ(j), r, hij, hr2)
          ),
          false => Scan(n, s, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2),
        }
      ),
    }
  )

  -- The pivot's final index.
  def Partition (m : Word) (s : &Slice(Word, Succ(m))) : Word := (
    let p = *GetMut(Word, Succ(m), &*s, Zero, refl);
    Scan(Succ(m), s, p, Zero, Succ(Zero), m, refl, AddOneR(m))
  )

  -- Sort both sides of the pivot at `k`, with `rec`. The pieces are borrowed by continuations
  -- (`WithSplit`), so each recursive call sees only its own piece. Written once for any `rec`,
  -- which is also what its lemmas are about. The first closure calls `rec` and hands it on to
  -- the second, which would move it out of the first closure's captures, so the second gets a
  -- clone (a closure may run again, D53).
  def Recurse (rec : Π(n : Word) (s : &Slice(Word, n)). Unit) (m : Word) (k : Word) (s : &Slice(Word, Succ(m))) : Unit := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => WithSplit(Word, Unit, Succ(m), k, s, LeStep(k, m, hk),
        λ(l : &Slice(Word, k)) (r : &Slice(Word, Sub(Succ(m), k))) : Unit => (
          rec(k, l);
          let rec2 = clone(rec);
          WithSplit(Word, Unit, Sub(Succ(m), k), Succ(Zero), r, SubPos(m, k, hk),
            λ(p : &Slice(Word, Succ(Zero))) (rr : &Slice(Word, Sub(Sub(Succ(m), k), Succ(Zero)))) : Unit => rec2(Sub(Sub(Succ(m), k), Succ(Zero)), rr))
        )),
      No(nk) => (),
    }
  )

  -- [K6] The recursion is on the length, but the lengths `k` and `m - k` of the pieces are not
  -- structural subterms of `Succ(m)`; until recursion on a measure exists, fuel bounds the depth
  -- (`QS(n, n, s)` sorts).
  def QS (fuel : Word) (n : Word) (s : &Slice(Word, n)) : Unit by fuel := (
    match fuel {
      Zero => (),
      Succ(f) => match n {
        Zero => (),
        Succ(m) => (
          let k = Partition(m, &*s);
          Recurse(λ(n' : Word) (s' : &Slice(Word, n')) : Unit => QS(f, n', s'), m, k, s)
        ),
      },
    }
  )

  def SortArray (n : Word) (a : &Array(Word, n)) : Unit := QS(n, n, AsSlice(Word, n, a))

  def SortRun : Id(Array(Word, W(5)),
      (let a : Array(Word, W(5)) = [W(3), W(1), W(4), W(1), W(2)]; SortArray(W(5), &a); a),
      ([W(1), W(1), W(2), W(3), W(4)] : Array(Word, W(5)))) := refl

  reject def SortRunWrong : Id(Array(Word, W(5)),
      (let a : Array(Word, W(5)) = [W(3), W(1), W(4), W(1), W(2)]; SortArray(W(5), &a); a),
      ([W(1), W(1), W(2), W(4), W(3)] : Array(Word, W(5)))) := refl

  -- ## Quicksort permutes: every count is unchanged
  -- The scan only swaps.
  def ScanPerm (n : Word) (s : &Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word)
      (hij : Lt(i, j)) (hr : Eq(Word, WAdd(rem, j), n)) (q : Word) :
      (let old = clone(*s); Eq(Word, Count(q, n, (Scan(n, &*s, p, i, j, rem, hij, hr); clone(*s))), Count(q, n, old))) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapS(Word, n, s, Zero, i, h0, hin) in CountSwap(q, n, clone(*s), Zero, i, h0, hin)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        -- the scan reads element `j` through its borrow: the value `x`, and the view `v`
        -- afterwards, a put-back program with the same counts by `GetMutRead`
        let x = (let c = clone(*s); *GetMut(Word, n, &c, j, hjn));
        let v = (let c = clone(*s); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hx, hv⟩ = GetMutRead(Word, n, s, j, hjn);
        let hc : Eq(Word, Count(q, n, v), Count(q, n, clone(*s))) = (rewrite ← hv in refl);
        let b = LeB(x, p);
        rewrite hc in
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c = (let c1 = clone(v); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            rewrite CountSwap(q, n, v, Succ(i), j, hsi, hjn) in
            rewrite SwapIsSwapSV(Word, n, v, Succ(i), j, hsi, hjn) in
              ScanPerm(n, &c, p, Succ(i), Succ(j), r, hij, hr2, q)
          ),
          false => ScanPerm(n, &v, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, q),
        }
      ),
    }
  )
  def PartitionPerm (m : Word) (s : &Slice(Word, Succ(m))) (q : Word) :
      (let old = clone(*s); Eq(Word, Count(q, Succ(m), (Partition(m, &*s); clone(*s))), Count(q, Succ(m), old))) := (
    -- the pivot is read at 0: once the view's first cell is split off, the read computes
    match *s {
      MkSlice(c) => match c {
        MkC(y, t) => (
          let p = y;
          ScanPerm(Succ(m), s, p, Zero, Succ(Zero), m, refl, AddOneR(m), q)
        ),
      },
    }
  )

  -- The recursive step permutes, for any `rec` that does.
  def RecursePerm (rec : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (ih : Π(n : Word) (s : &Slice(Word, n)) (q : Word). (let old = clone(*s); Eq(Word, Count(q, n, (rec(n, &*s); clone(*s))), Count(q, n, old))))
      (m : Word) (k : Word) (s : &Slice(Word, Succ(m))) (q : Word) :
      (let old = clone(*s); Eq(Word, Count(q, Succ(m), (Recurse(rec, m, k, &*s); clone(*s))), Count(q, Succ(m), old))) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        -- the pieces before, and after the two recursive calls
        let tk = TakeS(Word, Succ(m), k, clone(*s), hk2);
        let r0 = DropS(Word, Succ(m), k, clone(*s));
        let pv = TakeS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0), h1);
        let rr = DropS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0));
        let l2 = (let c = clone(tk); rec(k, &c); c);
        let rr2 = (let c = clone(rr); rec(Sub(Sub(Succ(m), k), Succ(Zero)), &c); c);
        let x2 = JoinS(Word, Sub(Succ(m), k), Succ(Zero), clone(pv), clone(rr2));
        -- the left part: the recursive call permutes it
        rewrite ← CountJoin(q, Succ(m), k, l2, x2, hk2) in
        rewrite ← (let c = clone(tk); ih(k, &c, q)) in
        -- the right part: the pivot is untouched and the recursive call permutes the rest
        rewrite ← CountJoin(q, Sub(Succ(m), k), Succ(Zero), pv, rr2, h1) in
        rewrite ← (let c = clone(rr); ih(Sub(Sub(Succ(m), k), Succ(Zero)), &c, q)) in
        rewrite CountJoin(q, Sub(Succ(m), k), Succ(Zero), pv, rr, h1) in
        rewrite ← JoinTakeDrop(Word, Sub(Succ(m), k), Succ(Zero), r0, h1) in
        -- and the two parts are the view, split
        rewrite CountJoin(q, Succ(m), k, tk, r0, hk2) in
        rewrite ← JoinTakeDrop(Word, Succ(m), k, clone(*s), hk2) in refl
      ),
      No(nk) => refl,
    }
  )

  -- The closure `QS` passes to `Recurse`, built outside `QS`: it captures the sort and the fuel,
  -- as the one inside `QS` captures `QS` itself and its fuel, so the two are the same value.
  def RecWith (qs : Π(fuel : Word) (n : Word) (s : &Slice(Word, n)). Unit) (fuel : Word) : (Π(n : Word) (s : &Slice(Word, n)). Unit) := (
    match fuel {
      Zero => (λ(n : Word) (s : &Slice(Word, n)) : Unit => ()),
      Succ(f) => (λ(n : Word) (s : &Slice(Word, n)) : Unit => qs(f, n, s)),
    }
  )

  -- Quicksort permutes its view: every count is unchanged.
  def QSPerm (fuel : Word) (n : Word) (s : &Slice(Word, n)) (q : Word) :
      (let old = clone(*s); Eq(Word, Count(q, n, (QS(fuel, n, &*s); clone(*s))), Count(q, n, old))) by fuel := (
    match fuel {
      Zero => refl,
      Succ(f) => match n {
        Zero => refl,
        Succ(m) => (
          let rec = RecWith(QS, fuel);
          let c = clone(*s);
          let k = Partition(m, &c);
          let e1 = RecursePerm(rec,
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (q2 : Word) :
                (let old = clone(*s2); Eq(Word, Count(q2, n2, (QS(f, n2, &*s2); clone(*s2))), Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            m, k, &c, q);
          rewrite PartitionPerm(m, s, q) in e1
        ),
      },
    }
  )
  -- ## Quicksort sorts, given the partition's contract
  -- Every element is at most `p`; at least `p`; and the view is sorted. Each is a
  -- proposition computed by recursion on the length.
  def AllLe (n : Word) (s : Slice(Word, n)) (p : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(x, p) ∧ AllLe(m, t, p),
        },
      },
    }
  )

  def AllGe (n : Word) (s : Slice(Word, n)) (p : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(p, x) ∧ AllGe(m, t, p),
        },
      },
    }
  )

  def Sorted (n : Word) (s : Slice(Word, n)) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => AllGe(m, t, x) ∧ Sorted(m, t),
        },
      },
    }
  )

  -- A lower bound can be lowered.
  def AllGeWeaken (n : Word) (s : Slice(Word, n)) (x : Word) (a : Word) (h : AllGe(n, s, x)) (hax : Le(a, x)) :
      AllGe(n, s, a) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => (
            let ⟨hy, ht⟩ = h;
            ⟨LeTrans(a, x, y, hax, hy), AllGeWeaken(m, t, x, a, ht, hax)⟩
          ),
        },
      },
    }
  )

  def AllGeJoin (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) (a : Word)
      (hl : AllGe(k, l, a)) (hr : AllGe(Sub(n, k), r, a)) : AllGe(n, JoinS(Word, n, k, l, r), a) by k := (
    match k {
      Zero => hr,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(y, t) => (
              let ⟨hy, ht⟩ = hl;
              ⟨hy, AllGeJoin(m, k', t, r, h, a, ht, hr)⟩
            ),
          },
        },
      },
    }
  )

  -- Two sorted views joined, everything on the left at most `x` and on the right at least
  -- `x`, are sorted.
  def SortedJoin (n : Word) (k : Word) (l : Slice(Word, k)) (r : Slice(Word, Sub(n, k))) (h : Le(k, n)) (x : Word)
      (hl : Sorted(k, l)) (hlx : AllLe(k, l, x)) (hr : Sorted(Sub(n, k), r)) (hrx : AllGe(Sub(n, k), r, x)) :
      Sorted(n, JoinS(Word, n, k, l, r)) by k := (
    match k {
      Zero => hr,
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => match l {
          MkSlice(c) => match c {
            MkC(a, t) => (
              let ⟨hla, hlt⟩ = hl;
              let ⟨hax, htx⟩ = hlx;
              ⟨AllGeJoin(m, k', t, r, h, a, hla, AllGeWeaken(Sub(m, k'), r, x, a, hrx, hax)),
                SortedJoin(m, k', t, r, h, x, hlt, htx, hr, hrx)⟩
            ),
          },
        },
      },
    }
  )

  -- ## Bounds survive a permutation, by counting (with `EqBRefl` from `Words`)
  -- If q = x (by EqB), x <= p and p < q is impossible; and the mirror image.
  def EqBLeLt (q : Word) (x : Word) (p : Word) (e : Eq(Bool, EqB(q, x), true)) (h1 : Le(x, p)) (h2 : Lt(p, q)) : False by q := (
    match q {
      Zero => match h2 {},
      Succ(q') => match x {
        Zero => match e {},
        Succ(x') => match p {
          Zero => match h1 {},
          Succ(p') => EqBLeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  def EqBGeLt (q : Word) (x : Word) (p : Word) (e : Eq(Bool, EqB(q, x), true)) (h1 : Le(p, x)) (h2 : Lt(q, p)) : False by q := (
    match q {
      Zero => match x {
        Zero => match p {
          Zero => match h2 {},
          Succ(p') => match h1 {},
        },
        Succ(x') => match e {},
      },
      Succ(q') => match x {
        Zero => match e {},
        Succ(x') => match p {
          Zero => match h2 {},
          Succ(p') => EqBGeLt(q', x', p', e, h1, h2),
        },
      },
    }
  )

  -- Every element at most `p`: no value above `p` occurs.
  def CountAboveZero (n : Word) (s : Slice(Word, n)) (p : Word) (h : AllLe(n, s, p)) (q : Word) (hq : Lt(p, q)) :
      Eq(Word, Count(q, n, s), Zero) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let ⟨hx, ht⟩ = h;
            let e = EqB(q, x);
            match e {
              true => (
                let no = EqBLeLt(q, x, p, refl, hx, hq);
                match no {}
              ),
              false => CountAboveZero(m, t, p, ht, q, hq),
            }
          ),
        },
      },
    }
  )

  def CountBelowZero (n : Word) (s : Slice(Word, n)) (p : Word) (h : AllGe(n, s, p)) (q : Word) (hq : Lt(q, p)) :
      Eq(Word, Count(q, n, s), Zero) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let ⟨hx, ht⟩ = h;
            let e = EqB(q, x);
            match e {
              true => (
                let no = EqBGeLt(q, x, p, refl, hx, hq);
                match no {}
              ),
              false => CountBelowZero(m, t, p, ht, q, hq),
            }
          ),
        },
      },
    }
  )

  -- A count of zero for the whole is a count of zero for the rest.
  def CountTailZero (q : Word) (m : Word) (x : Word) (t : Slice(Word, m)) (e0 : Eq(Word, Count(q, Succ(m), MkSlice(MkC(x, t))), Zero)) :
      Eq(Word, Count(q, m, t), Zero) := (
    let e = EqB(q, x);
    match e {
      true => match e0 {},
      false => e0,
    }
  )

  -- Conversely: if no value above `p` occurs, every element is at most `p`.
  def AllLeOfCounts (n : Word) (s : Slice(Word, n)) (p : Word)
      (hz : Π(q : Word) (hq : Lt(p, q)). Eq(Word, Count(q, n, s), Zero)) : AllLe(n, s, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(x, p);
            match d {
              Yes(hle) => ⟨hle, AllLeOfCounts(m, t, p, λ(q : Word) (hq : Lt(p, q)) : Eq(Word, Count(q, m, t), Zero) => CountTailZero(q, m, x, t, hz(q, hq)))⟩,
              No(nk) => (
                let e1 = hz(x, nk);
                let r1 = EqBRefl(x);
                let e = EqB(x, x);
                match e {
                  true => match e1 {},
                  false => match r1 {},
                }
              ),
            }
          ),
        },
      },
    }
  )

  def AllGeOfCounts (n : Word) (s : Slice(Word, n)) (p : Word)
      (hz : Π(q : Word) (hq : Lt(q, p)). Eq(Word, Count(q, n, s), Zero)) : AllGe(n, s, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => (
            let d = LeDec(p, x);
            match d {
              Yes(hle) => ⟨hle, AllGeOfCounts(m, t, p, λ(q : Word) (hq : Lt(q, p)) : Eq(Word, Count(q, m, t), Zero) => CountTailZero(q, m, x, t, hz(q, hq)))⟩,
              No(nk) => (
                let e1 = hz(x, nk);
                let r1 = EqBRefl(x);
                let e = EqB(x, x);
                match e {
                  true => match e1 {},
                  false => match r1 {},
                }
              ),
            }
          ),
        },
      },
    }
  )

  -- So a bound on every element survives any permutation.
  def AllLePerm (n : Word) (s : Slice(Word, n)) (s2 : Slice(Word, n)) (p : Word) (h : AllLe(n, s, p))
      (perm : Π(q : Word). Eq(Word, Count(q, n, s2), Count(q, n, s))) : AllLe(n, s2, p) := (
    AllLeOfCounts(n, s2, p, λ(q : Word) (hq : Lt(p, q)) : Eq(Word, Count(q, n, s2), Zero) =>
      rewrite ← perm(q) in CountAboveZero(n, s, p, h, q, hq))
  )

  def AllGePerm (n : Word) (s : Slice(Word, n)) (s2 : Slice(Word, n)) (p : Word) (h : AllGe(n, s, p))
      (perm : Π(q : Word). Eq(Word, Count(q, n, s2), Count(q, n, s))) : AllGe(n, s2, p) := (
    AllGeOfCounts(n, s2, p, λ(q : Word) (hq : Lt(q, p)) : Eq(Word, Count(q, n, s2), Zero) =>
      rewrite ← perm(q) in CountBelowZero(n, s, p, h, q, hq))
  )

  def LeSuccFalse (m : Word) (h : Le(Succ(m), m)) : False by m := (
    match m {
      Zero => match h {},
      Succ(m') => LeSuccFalse(m', h),
    }
  )

  -- ## Sorting
  -- The recursive step sorts the view, given the partition's facts about it (the pivot `x`
  -- ends at `k`; everything before is at most `x`, everything after at least `x`) and a
  -- `rec` that sorts and permutes views no longer than `m`.
  def RecurseSorted (m : Word) (rec : Π(n : Word) (s : &Slice(Word, n)). Unit)
      (ihS : Π(n : Word) (s : &Slice(Word, n)) (hn : Le(n, m)). (let c = clone(*s); rec(n, &c); Sorted(n, c)))
      (ihP : Π(n : Word) (s : &Slice(Word, n)) (q : Word). (let old = clone(*s); Eq(Word, Count(q, n, (rec(n, &*s); clone(*s))), Count(q, n, old))))
      (k : Word) (hk : Le(k, m)) (x : Word) (s : &Slice(Word, Succ(m)))
      (hL : AllLe(k, TakeS(Word, Succ(m), k, clone(*s), LeStep(k, m, hk)), x))
      (hP : Eq(Slice(Word, Succ(Zero)), MkSlice(MkC(x, MkSlice(End))), TakeS(Word, Sub(Succ(m), k), Succ(Zero), DropS(Word, Succ(m), k, clone(*s)), SubPos(m, k, hk))))
      (hR : AllGe(Sub(Sub(Succ(m), k), Succ(Zero)), DropS(Word, Sub(Succ(m), k), Succ(Zero), DropS(Word, Succ(m), k, clone(*s))), x)) :
      (let c = clone(*s); Recurse(rec, m, k, &c); Sorted(Succ(m), c)) := (
    let d = LeDec(k, m);
    match d {
      Yes(hk3) => (
        let hk2 = LeStep(k, m, hk);
        let h1 = SubPos(m, k, hk);
        let tk = TakeS(Word, Succ(m), k, clone(*s), hk2);
        let r0 = DropS(Word, Succ(m), k, clone(*s));
        let pv = TakeS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0), h1);
        let rr = DropS(Word, Sub(Succ(m), k), Succ(Zero), clone(r0));
        let l2 = (let c = clone(tk); rec(k, &c); c);
        let rr2 = (let c = clone(rr); rec(Sub(Sub(Succ(m), k), Succ(Zero)), &c); c);
        let x2 = JoinS(Word, Sub(Succ(m), k), Succ(Zero), clone(pv), clone(rr2));
        -- the left part: sorted by `rec`, and still at most `x` because `rec` permutes
        let sl2 : Sorted(k, l2) = (let c = clone(tk); ihS(k, &c, hk));
        let bl2 : AllLe(k, l2, x) = AllLePerm(k, tk, l2, x, hL,
          λ(q : Word) : Eq(Word, Count(q, k, l2), Count(q, k, tk)) => (let c = clone(tk); ihP(k, &c, q)));
        -- the right part: likewise, at least `x`
        let srr2 : Sorted(Sub(Sub(Succ(m), k), Succ(Zero)), rr2) = (let c = clone(rr); ihS(Sub(Sub(Succ(m), k), Succ(Zero)), &c, SubOneLe(m, k)));
        let brr2 : AllGe(Sub(Sub(Succ(m), k), Succ(Zero)), rr2, x) = AllGePerm(Sub(Sub(Succ(m), k), Succ(Zero)), rr, rr2, x, hR,
          λ(q : Word) : Eq(Word, Count(q, Sub(Sub(Succ(m), k), Succ(Zero)), rr2), Count(q, Sub(Sub(Succ(m), k), Succ(Zero)), rr)) =>
            (let c = clone(rr); ihP(Sub(Sub(Succ(m), k), Succ(Zero)), &c, q)));
        -- the pivot piece is `[x]`
        let spv : Sorted(Succ(Zero), pv) = (rewrite hP in refl);
        let lpv : AllLe(Succ(Zero), pv, x) = (rewrite hP in ⟨LeRefl(x), refl⟩);
        let gpv : AllGe(Succ(Zero), pv, x) = (rewrite hP in ⟨LeRefl(x), refl⟩);
        -- glue: pivot and right part, then left part and the rest
        let sx2 : Sorted(Sub(Succ(m), k), x2) = SortedJoin(Sub(Succ(m), k), Succ(Zero), pv, rr2, h1, x, spv, lpv, srr2, brr2);
        let gx2 : AllGe(Sub(Succ(m), k), x2, x) = AllGeJoin(Sub(Succ(m), k), Succ(Zero), pv, rr2, h1, x, gpv, brr2);
        SortedJoin(Succ(m), k, l2, x2, hk2, x, sl2, bl2, sx2, gx2)
      ),
      No(nk) => (
        let no = LeSuccFalse(m, LeTrans(Succ(m), k, m, nk, hk));
        match no {}
      ),
    }
  )

  -- ## The partition's contract
  -- Run on a copy of its input `v`, the partition returns `k` and leaves `PartV(m, v)`. Its
  -- contract: the pivot `x` (the first element of `v`) ends at `k <= m`, everything before
  -- it is at most `x`, and everything after it at least `x`.
  def PartK (m : Word) (v : Slice(Word, Succ(m))) : Word := (
    let c = v;
    Partition(m, &c)
  )

  def PartV (m : Word) (v : Slice(Word, Succ(m))) : Slice(Word, Succ(m)) := (
    let c = v;
    Partition(m, &c);
    c
  )

  def PartLe (m : Word) (v : Slice(Word, Succ(m))) : Prop := Le(PartK(m, v), m)

  def PartLeft (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    AllLe(PartK(m, v), TakeS(Word, Succ(m), PartK(m, clone(v)), PartV(m, clone(v)), LeStep(PartK(m, v), m, hk)), Nth(Word, Succ(m), v, Zero, refl))
  )

  def PartPivot (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    Eq(Slice(Word, Succ(Zero)), MkSlice(MkC(Nth(Word, Succ(m), v, Zero, refl), MkSlice(End))), TakeS(Word, Sub(Succ(m), PartK(m, clone(v))), Succ(Zero), DropS(Word, Succ(m), PartK(m, clone(v)), PartV(m, clone(v))), SubPos(m, PartK(m, v), hk)))
  )

  def PartRight (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : Prop := (
    AllGe(Sub(Sub(Succ(m), PartK(m, v)), Succ(Zero)), DropS(Word, Sub(Succ(m), PartK(m, clone(v))), Succ(Zero), DropS(Word, Succ(m), PartK(m, clone(v)), PartV(m, v))),
      Nth(Word, Succ(m), v, Zero, refl))
  )

  -- Quicksort sorts, for fuel at least the length, given the partition's contract.
  def QSSorted (specLe : Π(m : Word) (v : Slice(Word, Succ(m))). PartLe(m, v))
      (specL : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartLeft(m, v, hk))
      (specP : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartPivot(m, v, hk))
      (specR : Π(m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)). PartRight(m, v, hk))
      (fuel : Word) (n : Word) (s : &Slice(Word, n)) (hf : Le(n, fuel)) :
      (let c = clone(*s); QS(fuel, n, &c); Sorted(n, c)) by fuel := (
    match fuel {
      Zero => match n {
        Zero => refl,
        Succ(m) => match hf {},
      },
      Succ(f) => match n {
        Zero => refl,
        Succ(m) => (
          let rec = RecWith(QS, fuel);
          let v = clone(*s);
          let hk = specLe(m, v);
          let c = clone(*s);
          let k = Partition(m, &c);
          RecurseSorted(m, rec,
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (hn : Le(n2, m)) : (let c2 = clone(*s2); QS(f, n2, &c2); Sorted(n2, c2)) =>
              QSSorted(specLe, specL, specP, specR, f, n2, s2, LeTrans(n2, m, f, hn, hf)),
            λ(n2 : Word) (s2 : &Slice(Word, n2)) (q2 : Word) :
                (let old = clone(*s2); Eq(Word, Count(q2, n2, (QS(f, n2, &*s2); clone(*s2))), Count(q2, n2, old))) =>
              QSPerm(f, n2, s2, q2),
            k, hk, Nth(Word, Succ(m), v, Zero, refl), &c, specL(m, v, hk), specP(m, v, hk), specR(m, v, hk))
        ),
      },
    }
  )

  -- The contract on examples (proved for every input below).
  def ContractRun1 : PartLe(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End)))))))))))) ∧ PartLeft(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ PartPivot(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ PartRight(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) := refl
  def ContractRun2 : PartLe(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End)))))))))))))) ∧ PartLeft(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) ∧ PartPivot(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) ∧ PartRight(W(5), MkSlice(MkC(W(2), MkSlice(MkC(W(5), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(5), MkSlice(MkC(Zero, MkSlice(MkC(W(2), MkSlice(End))))))))))))), refl) := refl
  -- A wrong pivot position is not.
  reject def ContractWrong : PartPivot(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End))))))))))), refl) ∧ Eq(Word, PartK(W(4), MkSlice(MkC(W(3), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(4), MkSlice(MkC(Succ(Zero), MkSlice(MkC(W(2), MkSlice(End)))))))))))), W(2)) := refl
  -- ## The partition meets its contract: Lomuto's invariant
  -- More order facts (with `LeOfLt` from `Words`).
  def LtTrans (a : Word) (b : Word) (c : Word) (h1 : Lt(a, b)) (h2 : Lt(b, c)) : Lt(a, c) := (
    LeTrans(Succ(a), b, c, h1, LeOfLt(b, c, h2))
  )

  def LtLeTrans (a : Word) (b : Word) (c : Word) (h1 : Lt(a, b)) (h2 : Le(b, c)) : Lt(a, c) := LeTrans(Succ(a), b, c, h1, h2)

  -- What a comparison said, as a proof.
  def LeBLe (a : Word) (b : Word) (e : Eq(Bool, LeB(a, b), true)) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match e {},
        Succ(b') => LeBLe(a', b', e),
      },
    }
  )

  def LeBGt (a : Word) (b : Word) (e : Eq(Bool, LeB(a, b), false)) : Lt(b, a) by a := (
    match a {
      Zero => match e {},
      Succ(a') => match b {
        Zero => refl,
        Succ(b') => LeBGt(a', b', e),
      },
    }
  )

  -- ## Reading a swapped view
  def NthSwapB (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (ha : Lt(a, n)) (hb : Lt(b, n)) :
      Eq(Word, Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), b, hb), Nth(Word, n, c, a, ha)) := (
    NthSetSame(Word, n, SetS(Word, n, clone(c), a, Nth(Word, n, c, b, hb)), b, Nth(Word, n, c, a, ha), hb)
  )

  def NthSwapA (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (ha : Lt(a, n)) (hb : Lt(b, n)) :
      Eq(Word, Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), a, ha), Nth(Word, n, c, b, hb)) by a := (
    match n {
      Zero => match ha {},
      Succ(m) => match c {
        MkSlice(cc) => match cc {
          MkC(y, t) => match a {
            Zero => match b {
              Zero => refl,
              Succ(b') => refl,
            },
            Succ(a') => match b {
              Zero => NthSetSame(Word, m, t, a', y, ha),
              Succ(b') => NthSwapA(m, t, a', b', ha, hb),
            },
          },
        },
      },
    }
  )

  def NthSwapOther (n : Word) (c : Slice(Word, n)) (a : Word) (b : Word) (t : Word) (ha : Lt(a, n)) (hb : Lt(b, n))
      (ht : Lt(t, n)) (na : Π(e : Eq(Word, a, t)). False) (nb : Π(e : Eq(Word, b, t)). False) :
      Eq(Word, Nth(Word, n, SwapS(Word, n, c, a, b, ha, hb), t, ht), Nth(Word, n, c, t, ht)) := (
    rewrite ← NthSetOther(Word, n, SetS(Word, n, clone(c), a, Nth(Word, n, c, b, hb)), b, t, Nth(Word, n, c, a, ha), hb, ht, nb) in
      NthSetOther(Word, n, c, a, t, Nth(Word, n, c, b, hb), ha, ht, na)
  )

  -- ## From facts about positions to facts about pieces
  def AllLeTakeOf (n : Word) (k : Word) (c : Slice(Word, n)) (p : Word) (hk : Le(k, n))
      (h : Π(t : Word) (ht : Lt(t, k)) (htn : Lt(t, n)). Le(Nth(Word, n, c, t, htn), p)) :
      AllLe(k, TakeS(Word, n, k, c, hk), p) by k := (
    match k {
      Zero => refl,
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => ⟨h(Zero, refl, refl),
              AllLeTakeOf(m, k', t0, p, hk,
                λ(t : Word) (ht : Lt(t, k')) (htn : Lt(t, m)) : Le(Nth(Word, m, t0, t, htn), p) => h(Succ(t), ht, htn))⟩,
          },
        },
      },
    }
  )

  def AllGeAllOf (n : Word) (c : Slice(Word, n)) (p : Word)
      (h : Π(t : Word) (ht : Lt(t, n)). Le(p, Nth(Word, n, c, t, ht))) : AllGe(n, c, p) by n := (
    match n {
      Zero => refl,
      Succ(m) => match c {
        MkSlice(cc) => match cc {
          MkC(x, t0) => ⟨h(Zero, refl),
            AllGeAllOf(m, t0, p, λ(t : Word) (ht : Lt(t, m)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht))⟩,
        },
      },
    }
  )

  def AllGeDropOf (n : Word) (k : Word) (c : Slice(Word, n)) (p : Word)
      (h : Π(t : Word) (ht : Lt(t, n)) (hkt : Lt(k, t)). Le(p, Nth(Word, n, c, t, ht))) :
      AllGe(Sub(Sub(n, k), Succ(Zero)), DropS(Word, Sub(n, k), Succ(Zero), DropS(Word, n, k, c)), p) by k := (
    match k {
      Zero => match n {
        Zero => refl,
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => AllGeAllOf(m, t0, p, λ(t : Word) (ht : Lt(t, m)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht, refl)),
          },
        },
      },
      Succ(k') => match n {
        Zero => refl,
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => AllGeDropOf(m, k', t0, p,
              λ(t : Word) (ht : Lt(t, m)) (hkt : Lt(k', t)) : Le(p, Nth(Word, m, t0, t, ht)) => h(Succ(t), ht, hkt)),
          },
        },
      },
    }
  )

  def TakeOneDrop (n : Word) (k : Word) (c : Slice(Word, n)) (hk : Lt(k, n)) :
      Eq(Slice(Word, Succ(Zero)), MkSlice(MkC(Nth(Word, n, c, k, hk), MkSlice(End))), TakeS(Word, Sub(n, k), Succ(Zero), DropS(Word, n, k, c), SubPosLt(n, k, hk))) by k := (
    match k {
      Zero => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => refl,
          },
        },
      },
      Succ(k') => match n {
        Zero => match hk {},
        Succ(m) => match c {
          MkSlice(cc) => match cc {
            MkC(x, t0) => TakeOneDrop(m, k', t0, hk),
          },
        },
      },
    }
  )

  -- ## The scan's last step: the pivot is swapped to `i`
  def EndLeft (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (hin : Lt(i, n)) (h0 : Lt(Zero, n))
      (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, s0, t, ht), p))
      (t : Word) (ht : Lt(t, i)) (htn : Lt(t, n)) : Le(Nth(Word, n, SwapS(Word, n, s0, Zero, i, h0, hin), t, htn), p) := (
    match t {
      Zero => rewrite ← NthSwapA(n, s0, Zero, i, h0, hin) in j1(i, hin, ht, LeRefl(i)),
      Succ(t') => rewrite ← NthSwapOther(n, s0, Zero, i, Succ(t'), h0, hin, htn, λ(e : Eq(Word, Zero, Succ(t'))) : False => match e {},
          λ(e : Eq(Word, i, Succ(t'))) : False => LtNe(Succ(t'), i, ht, rewrite e in refl)) in
        j1(Succ(t'), htn, refl, LeOfLt(Succ(t'), i, ht)),
    }
  )

  def EndRight (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hin : Lt(i, n)) (h0 : Lt(Zero, n))
      (hjn : Eq(Word, j, n))
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (t : Word) (ht : Lt(t, n)) (hkt : Lt(i, t)) : Lt(p, Nth(Word, n, SwapS(Word, n, s0, Zero, i, h0, hin), t, ht)) := (
    rewrite ← NthSwapOther(n, s0, Zero, i, t, h0, hin, ht, λ(e : Eq(Word, Zero, t)) : False => LtNe(Zero, t, LeTrans(Succ(Zero), Succ(i), t, refl, hkt), e),
        λ(e : Eq(Word, i, t)) : False => LtNe(i, t, hkt, e)) in
      j2(t, ht, hkt, rewrite ← hjn in ht)
  )

  -- ## One step of the scan keeps the invariant
  -- After swapping `i + 1` with `j` (the element at `j` was at most `p`): the pivot is still at
  -- 0, cells `1 … i + 1` are at most `p`, cells `i + 2 … j` are greater.
  def StepJ0 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j0 : Π(h0 : Lt(Zero, n)). Eq(Word, Nth(Word, n, s0, Zero, h0), p)) (h0 : Lt(Zero, n)) :
      Eq(Word, Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), Zero, h0), p) := (
    rewrite ← NthSwapOther(n, s0, Succ(i), j, Zero, hsi, hjn, h0, λ(e : Eq(Word, Succ(i), Zero)) : False => match e {},
        λ(e : Eq(Word, j, Zero)) : False => LtNe(Zero, j, LeTrans(Succ(Zero), Succ(i), j, refl, hij), rewrite e in refl)) in
      j0(h0)
  )

  def StepJ1 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, s0, t, ht), p))
      (hx : Le(Nth(Word, n, s0, j, hjn), p)) (t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, Succ(i))) :
      Le(Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), t, ht), p) := (
    let d = LeDec(t, i);
    match d {
      Yes(hti) => rewrite ← NthSwapOther(n, s0, Succ(i), j, t, hsi, hjn, ht,
          λ(e : Eq(Word, Succ(i), t)) : False => LtNe(t, Succ(i), hti, rewrite e in refl),
          λ(e : Eq(Word, j, t)) : False => LtNe(t, j, LeTrans(Succ(t), Succ(i), j, hti, hij), rewrite e in refl)) in
        j1(t, ht, a, hti),
      No(nti) => rewrite ← LeAntisym(t, Succ(i), b, nti) in rewrite ← NthSwapA(n, s0, Succ(i), j, hsi, hjn) in hx,
    }
  )

  def StepJ2 (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hsi : Lt(Succ(i), n)) (hjn : Lt(j, n))
      (hij : Lt(i, j)) (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (t : Word) (ht : Lt(t, n)) (a : Lt(Succ(i), t)) (b : Lt(t, Succ(j))) : Lt(p, Nth(Word, n, SwapS(Word, n, s0, Succ(i), j, hsi, hjn), t, ht)) := (
    let d = LeDec(Succ(t), j);
    match d {
      Yes(htj) => rewrite ← NthSwapOther(n, s0, Succ(i), j, t, hsi, hjn, ht, λ(e : Eq(Word, Succ(i), t)) : False => LtNe(Succ(i), t, a, e),
          λ(e : Eq(Word, j, t)) : False => LtNe(t, j, htj, rewrite e in refl)) in
        j2(t, ht, LtTrans(i, Succ(i), t, LeRefl(Succ(i)), a), htj),
      No(ntj) => (
        let e = LeAntisym(t, j, b, ntj);
        rewrite ← e in rewrite ← NthSwapB(n, s0, Succ(i), j, hsi, hjn) in j2(Succ(i), hsi, LeRefl(Succ(i)), rewrite e in a)
      ),
    }
  )

  -- Without a swap (the element at `j` was greater than `p`): cells `i + 1 … j` are greater.
  def StepJ2F (n : Word) (s0 : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (hjn : Lt(j, n))
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, s0, t, ht)))
      (hx : Lt(p, Nth(Word, n, s0, j, hjn))) (t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, Succ(j))) :
      Lt(p, Nth(Word, n, s0, t, ht)) := (
    let d = LeDec(Succ(t), j);
    match d {
      Yes(htj) => j2(t, ht, a, htj),
      No(ntj) => rewrite ← LeAntisym(t, j, b, ntj) in hx,
    }
  )

  -- ## What the scan leaves, fact by fact
  -- [checker] Stated pointwise, one lemma per fact, rather than as one proposition with
  -- `Π`s inside: a `Π`-type's captured values are not re-normalised after a case split, so a
  -- goal holding the scan's result inside a `Π` stays stale.
  -- The scan's result and final view, run on a copy of `v`.
  def ScanK (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n)) : Word := (
    let c = v;
    Scan(n, &c, p, i, j, rem, hij, hr)
  )

  def ScanV (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n)) : Slice(Word, n) := (
    let c = v;
    Scan(n, &c, p, i, j, rem, hij, hr);
    c
  )

  def ScanLt (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n)) : Lt(ScanK(n, v, p, i, j, rem, hij, hr), n) by rem := (
    match rem {
      Zero => rewrite hr in hij,
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let b = LeB(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            ScanLt(n, (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1), p, Succ(i), Succ(j), r, hij, hr2)
          ),
          false => ScanLt(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2),
        }
      ),
    }
  )

  def ScanPivot (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n)) (j0 : Π(h0 : Lt(Zero, n)). Eq(Word, Nth(Word, n, v, Zero, h0), p))
      (hk : Lt(ScanK(n, v, p, i, j, rem, hij, hr), n)) :
      Eq(Word, Nth(Word, n, ScanV(n, clone(v), p, i, j, rem, hij, hr), ScanK(n, v, p, i, j, rem, hij, hr), hk), p) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in rewrite ← NthSwapB(n, v, Zero, i, h0, hk) in j0(h0)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j0w : Π(h0 : Lt(Zero, n)). Eq(Word, Nth(Word, n, w, Zero, h0), p) = (
          λ(h0 : Lt(Zero, n)) : Eq(Word, Nth(Word, n, w, Zero, h0), p) => rewrite ← hw in j0(h0));
        let b = LeB(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanPivot(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(h0 : Lt(Zero, n)) : Eq(Word, Nth(Word, n, c2, Zero, h0), p) =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ0(n, w, p, i, j, hsi, hjn, hij, j0w, h0), hk)
          ),
          false => ScanPivot(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, j0w, hk),
        }
      ),
    }
  )

  def ScanLeft (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n))
      (j1 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(Zero, t)) (b : Le(t, i)). Le(Nth(Word, n, v, t, ht), p))
      (t : Word) (ht : Lt(t, ScanK(n, v, p, i, j, rem, hij, hr))) (htn : Lt(t, n)) :
      Le(Nth(Word, n, ScanV(n, v, p, i, j, rem, hij, hr), t, htn), p) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in EndLeft(n, v, p, i, hin, h0, j1, t, ht, htn)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j1w : Π(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, i)). Le(Nth(Word, n, w, t2, ht2), p) = (
          λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, i)) : Le(Nth(Word, n, w, t2, ht2), p) =>
          rewrite ← hw in j1(t2, ht2, a, b2));
        let b = LeB(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let hx : Le(Nth(Word, n, w, j, hjn), p) = (rewrite ← hw in rewrite hxv in LeBLe(x, p, refl));
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanLeft(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Zero, t2)) (b2 : Le(t2, Succ(i))) : Le(Nth(Word, n, c2, t2, ht2), p) =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ1(n, w, p, i, j, hsi, hjn, hij, j1w, hx, t2, ht2, a, b2),
              t, ht, htn)
          ),
          false => ScanLeft(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2, j1w, t, ht, htn),
        }
      ),
    }
  )

  def ScanRight (n : Word) (v : Slice(Word, n)) (p : Word) (i : Word) (j : Word) (rem : Word) (hij : Lt(i, j))
      (hr : Eq(Word, WAdd(rem, j), n))
      (j2 : Π(t : Word) (ht : Lt(t, n)) (a : Lt(i, t)) (b : Lt(t, j)). Lt(p, Nth(Word, n, v, t, ht)))
      (t : Word) (ht : Lt(t, n)) (hkt : Lt(ScanK(n, v, p, i, j, rem, hij, hr), t)) :
      Lt(p, Nth(Word, n, ScanV(n, v, p, i, j, rem, hij, hr), t, ht)) by rem := (
    match rem {
      Zero => (
        let hin : Lt(i, n) = (rewrite hr in hij);
        let h0 : Lt(Zero, n) = LeTrans(Succ(Zero), Succ(i), n, refl, hin);
        rewrite ← SwapIsSwapSV(Word, n, v, Zero, i, h0, hin) in EndRight(n, v, p, i, j, hin, h0, hr, j2, t, ht, hkt)
      ),
      Succ(r) => (
        let hjn : Lt(j, n) = (rewrite hr in LeAddL(r, j));
        let hr2 : Eq(Word, WAdd(r, Succ(j)), n) = (rewrite AddRS(r, j) in hr);
        -- element `j`, read through its borrow, and the view `w` the read leaves
        let x = (let c = clone(v); *GetMut(Word, n, &c, j, hjn));
        let w = (let c = clone(v); let y = *GetMut(Word, n, &c, j, hjn); c);
        let ⟨hxv, hw0⟩ = GetMutReadV(Word, n, v, j, hjn);
        let hw : Eq(Slice(Word, n), w, v) = hw0;
        let j2w : Π(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, j)). Lt(p, Nth(Word, n, w, t2, ht2)) = (
          λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, j)) : Lt(p, Nth(Word, n, w, t2, ht2)) =>
          rewrite ← hw in j2(t2, ht2, a, b2));
        let b = LeB(x, p);
        match b {
          true => (
            let hsi : Lt(Succ(i), n) = LeTrans(Succ(Succ(i)), Succ(j), n, hij, hjn);
            let c2 = (let c1 = clone(w); Swap(Word, n, &c1, Succ(i), j, hsi, hjn); c1);
            ScanRight(n, c2, p, Succ(i), Succ(j), r, hij, hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(Succ(i), t2)) (b2 : Lt(t2, Succ(j))) : Lt(p, Nth(Word, n, c2, t2, ht2)) =>
                rewrite ← SwapIsSwapSV(Word, n, w, Succ(i), j, hsi, hjn) in StepJ2(n, w, p, i, j, hsi, hjn, hij, j2w, t2, ht2, a, b2),
              t, ht, hkt)
          ),
          false => (
            let hx : Lt(p, Nth(Word, n, w, j, hjn)) = (rewrite ← hw in rewrite hxv in LeBGt(x, p, refl));
            ScanRight(n, w, p, i, Succ(j), r, LeStep(Succ(i), j, hij), hr2,
              λ(t2 : Word) (ht2 : Lt(t2, n)) (a : Lt(i, t2)) (b2 : Lt(t2, Succ(j))) : Lt(p, Nth(Word, n, w, t2, ht2)) =>
                StepJ2F(n, w, p, i, j, hjn, j2w, hx, t2, ht2, a, b2),
              t, ht, hkt)
          ),
        }
      ),
    }
  )

  -- ## The partition meets its contract
  -- At the start (`i = 0`, `j = 1`) the invariant holds trivially: the pivot is the first
  -- element, and the two ranges are empty.
  def Start0 (m : Word) (v : Slice(Word, Succ(m))) (h0 : Lt(Zero, Succ(m))) :
      Eq(Word, Nth(Word, Succ(m), v, Zero, h0), Nth(Word, Succ(m), v, Zero, refl)) := refl

  def Start1 (m : Word) (v : Slice(Word, Succ(m))) (t : Word) (ht : Lt(t, Succ(m))) (a : Lt(Zero, t)) (b : Le(t, Zero)) :
      Le(Nth(Word, Succ(m), v, t, ht), Nth(Word, Succ(m), v, Zero, refl)) := (
    let no = LeSuccFalse(Zero, LeTrans(Succ(Zero), t, Zero, a, b));
    match no {}
  )

  def Start2 (m : Word) (v : Slice(Word, Succ(m))) (t : Word) (ht : Lt(t, Succ(m))) (a : Lt(Zero, t)) (b : Lt(t, Succ(Zero))) :
      Lt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), v, t, ht)) := (
    let no = LeSuccFalse(Zero, LeTrans(Succ(Zero), t, Zero, a, b));
    match no {}
  )

  def PartLeProof (m : Word) (v : Slice(Word, Succ(m))) : PartLe(m, v) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          ScanLt(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m))
        ),
      },
    }
  )

  def PartLeftProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartLeft(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          AllLeTakeOf(Succ(m), PartK(m, v), PartV(m, v), Nth(Word, Succ(m), v, Zero, refl), LeStep(PartK(m, v), m, hk),
            λ(t : Word) (ht : Lt(t, PartK(m, v))) (htn : Lt(t, Succ(m))) : Le(Nth(Word, Succ(m), PartV(m, v), t, htn), Nth(Word, Succ(m), v, Zero, refl)) =>
              ScanLeft(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
                λ(t2 : Word) (ht2 : Lt(t2, Succ(m))) (a : Lt(Zero, t2)) (b : Le(t2, Zero)) : Le(Nth(Word, Succ(m), v, t2, ht2), Nth(Word, Succ(m), v, Zero, refl)) =>
                  Start1(m, v, t2, ht2, a, b),
                t, ht, htn))
        ),
      },
    }
  )

  def PartPivotProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartPivot(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          rewrite TakeOneDrop(Succ(m), PartK(m, v), PartV(m, v), hk) in
          rewrite ← ScanPivot(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
              λ(h0 : Lt(Zero, Succ(m))) : Eq(Word, Nth(Word, Succ(m), v, Zero, h0), Nth(Word, Succ(m), v, Zero, refl)) => Start0(m, v, h0), hk) in
            refl
        ),
      },
    }
  )

  def PartRightProof (m : Word) (v : Slice(Word, Succ(m))) (hk : PartLe(m, v)) : PartRight(m, v, hk) := (
    -- the pivot is read at 0: once the first cell is split off, the read computes
    match v {
      MkSlice(c0) => match c0 {
        MkC(y0, t0) => (
          AllGeDropOf(Succ(m), PartK(m, v), PartV(m, v), Nth(Word, Succ(m), v, Zero, refl),
            λ(t : Word) (ht : Lt(t, Succ(m))) (hkt : Lt(PartK(m, v), t)) : Le(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), PartV(m, v), t, ht)) =>
              LeOfLt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), PartV(m, v), t, ht),
                ScanRight(Succ(m), v, Nth(Word, Succ(m), v, Zero, refl), Zero, Succ(Zero), m, refl, AddOneR(m),
                  λ(t2 : Word) (ht2 : Lt(t2, Succ(m))) (a : Lt(Zero, t2)) (b : Lt(t2, Succ(Zero))) : Lt(Nth(Word, Succ(m), v, Zero, refl), Nth(Word, Succ(m), v, t2, ht2)) =>
                    Start2(m, v, t2, ht2, a, b),
                  t, ht, hkt)))
        ),
      },
    }
  )

  -- Quicksort sorts, for fuel at least the length, with no hypotheses.
  def QSSortedFull (fuel : Word) (n : Word) (s : &Slice(Word, n)) (hf : Le(n, fuel)) :
      (let c = *s; QS(fuel, n, &c); Sorted(n, c)) := (
    QSSorted(PartLeProof, PartLeftProof, PartPivotProof, PartRightProof, fuel, n, s, hf)
  )

  -- Quicksort is correct: its result is sorted and a permutation of its input.
  def QSCorrect (n : Word) (s : &Slice(Word, n)) (q : Word) :
      (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧
        (let old = clone(*s); Eq(Word, Count(q, n, (QS(n, n, &*s); *s)), Count(q, n, old))) := (
    ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
  )
}
