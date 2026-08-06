import Dllbc.ProgMacro
import Dllbc.Machine
import Dllbc.Macro
import Dllbc.Tests.S2
import Dllbc.Tests.S3
import Dllbc.Tests.S3Sym
import Dllbc.Boundary
import Dllbc.Migrate
import Dllbc.Tests.S7Group
import Dllbc.Tests.S9Diff
import Dllbc.Std
import Dllbc.DeclMacro
import Dllbc.Tests.S14Bounds
import Dllbc.StdLemmas
import Dllbc.Tests.S17Spec
import Dllbc.PureMacro
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S25ArrSort
open Dllbc
open Dllbc.Val (nat nil cons)
open Dllbc.Tests.S2
open Dllbc.Tests.S3
open Dllbc.Tests.S3Sym
open Dllbc.Tests.S7Group
open Dllbc.Tests.S9Diff
open Dllbc.Tests.S14Bounds
open Dllbc.StdLemmas (set swapL)
open Dllbc.Tests.S17Spec
open Dllbc.StdLemmas (le_refl le_add)
open Dllbc.StdLemmas (countA SortedA UbA LbA BoundA asingle
  sorted_headA sorted_headA_ty sorted_tailA sorted_tailA_ty
  ub_headA ub_headA_ty ub_tailA ub_tailA_ty lb_boundA lb_boundA_ty
  bound_arrCat bound_arrCat_ty sorted_arrCat sorted_arrCat_ty
  count_arrCat count_arrCat_ty
  count_acons_hit count_acons_hit_ty count_acons_miss count_acons_miss_ty
  noAbove_of_ubA noAbove_of_ubA_ty ub_of_noAboveA ub_of_noAboveA_ty
  ub_permA ub_permA_ty noBelow_of_lbA noBelow_of_lbA_ty
  lb_of_noBelowA lb_of_noBelowA_ty lb_permA lb_permA_ty
  count_swap2 count_swap2_ty leb_true_le leb_false_gt le_pred_l)
open Dllbc.Tests.S24Arrays
open Dllbc.StdLemmas (le_refl le_add le_add_l le_add_succ le_trans le_up_r le_pred_l
  leb_true_le leb_false_gt add_succ add_zero id_trans id_congr id_sym znots
  SortedA UbA LbA countA asingle sorted_arrCat count_arrCat ub_permA lb_permA
  nat_rw nat_rw_ty le_zero_eq le_zero_eq_ty sortedA_nil sortedA_nil_ty
  SplitA PartA splitA_nil splitA_nil_ty
  splitA0_lb splitA0_lb_ty splitA_cat_e1 splitA_cat_e1_ty
  splitA_cat_i0 splitA_cat_i0_ty partA_cat_i0 partA_cat_i0_ty
  partA_cat_e0 partA_cat_e0_ty
  bumpN count_acons_congr count_acons_congr_ty bump_comm bump_comm_ty
  count_swapA count_swapA_ty
  splitA_cat_ub splitA_cat_ub_ty splitA_cat_rest splitA_cat_rest_ty
  splitA1_head splitA1_head_ty splitA1_tail splitA1_tail_ty
  partA_cat_ub partA_cat_ub_ty partA_cat_rest partA_cat_rest_ty
  partA0_eq partA0_eq_ty partA0_lb partA0_lb_ty s_inj)
open Dllbc.Tests.S25ArrSort

/-!
# The migration's safety net — legacy grammar ≡ unified grammar, by `rfl`

**This module is TEMPORARY and dies with the legacy grammar.** It exists for
exactly as long as both grammars do: one `example … := rfl` per legacy site in
the suite, asserting that the `dllbc{ }` / `dllbcWith [..]{ }` block and the
`prog{ }` / `progSeed [..]{ }` block written from the *same source text*
elaborate to the *same* `Term`.

Why `rfl` and not the golden traces: the traces are the migration's outer net,
but they only catch a changed `Term` that also changes an observable final
environment, and they say nothing about the sites that are `FnDef` bodies never
run in isolation. `rfl` compares the elaborated values themselves, which is the
property the migration actually needs — Uni.lean's header claims "the runtime
subset produces byte-identical `Term`s to the `dllbc` block", and this is that
claim, checked, at every site that relies on it.

The three known semantic differences between the grammars (head resolution keyed
on `ctorSet` rather than case; bare uppercase names resolving through the basis;
unbound lowercase names falling through to Lean identifier resolution) would each
show up here as a type mismatch. None do — so the migration is a rename.

Generated mechanically from the legacy sites; do not edit by hand.
-/

-- Dllbc/Tests/S2.lean site 1
example : (dllbc{
  let x = 3;
  let y = x;
  x := 7;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let y = x;
  x := 7;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 2
example : (dllbc{
  let x = 3;
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 3
example : (dllbc{
  let x = 3;
  let b = &mut x;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 4
example : (dllbc{
  let x = 3;
  let b = &mut x;
  *b := 7;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  *b := 7;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 5
example : (dllbc{
  let x = 3;
  let b = &mut x;
  *b := 7;
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  *b := 7;
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 6
example : (dllbc{
  let x = 3;
  let b = &mut x;
  b := 9;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  b := 9;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 7
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 8
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  *b := Cons(7, tail);
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  *b := Cons(7, tail);
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 9
example : (dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 10
example : (dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  let z = x;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  let z = x;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 11
example : (dllbc{
  let x = 3;
  let y = x;
  let z = x;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let y = x;
  let z = x;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 12
example : (dllbc{
  Pair(1) := 7;
  ()
} : Dllbc.Term) = (prog{
  Pair(1) := 7;
  ()
}) := rfl

-- Dllbc/Tests/S2.lean site 13
example : (dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  b := c;
  ()
} : Dllbc.Term) = (prog{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  b := c;
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 14
example : (dllbc{
  let p = Pair(3, 7);
  let q = match p { Pair(a, b) => Pair(a, b) };
  ()
} : Dllbc.Term) = (prog{
  let p = Pair(3, 7);
  let q = match p { Pair(a, b) => Pair(a, b) };
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 15
example : (dllbc{
  let p = Pair(1, Cons(2, Nil));
  let r = match p {
    Pair(a, rest) => match rest { Cons(h, t) => Pair(a, h), Nil => Pair(a, a) }
  };
  ()
} : Dllbc.Term) = (prog{
  let p = Pair(1, Cons(2, Nil));
  let r = match p {
    Pair(a, rest) => match rest { Cons(h, t) => Pair(a, h), Nil => Pair(a, a) }
  };
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 16
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 17
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 18
example : (dllbc{
  let x = Nil;
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = Nil;
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 19
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *b := Nil; () },
    Nil => ()
  };
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *b := Nil; () },
    Nil => ()
  };
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 20
example : (dllbc{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  match b {
    Cons(hd, tl) => match tl {
      Cons(h2, t2) => { *h2 := 0; () },
      Nil => ()
    },
    Nil => ()
  };
  let y = x;
  ()
} : Dllbc.Term) = (prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  match b {
    Cons(hd, tl) => match tl {
      Cons(h2, t2) => { *h2 := 0; () },
      Nil => ()
    },
    Nil => ()
  };
  let y = x;
  ()
}) := rfl

-- Dllbc/Tests/S3.lean site 21
example : (dllbc{
  let p = Nil;
  let q = p;
  match p { Nil => () }
} : Dllbc.Term) = (prog{
  let p = Nil;
  let q = p;
  match p { Nil => () }
}) := rfl

-- Dllbc/Tests/S3.lean site 22
example : (dllbc{
  let p = Nil;
  match p { Cons(h, t) => () }
} : Dllbc.Term) = (prog{
  let p = Nil;
  match p { Cons(h, t) => () }
}) := rfl

-- Dllbc/Tests/S3.lean site 23
example : (dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  match b { Cons(hd, tl) => (), Nil => () }
} : Dllbc.Term) = (prog{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  match b { Cons(hd, tl) => (), Nil => () }
}) := rfl

-- Dllbc/Tests/S3Sym.lean site 24
example : (dllbcWith [n]{ match n { Z => (), S(m) => () } } : Dllbc.Term) = (progSeed [n]{ match n { Z => (), S(m) => () } }) := rfl

-- Dllbc/Tests/S3Sym.lean site 25
example : (dllbcWith [x, b]{
    match b { Cons(hd, tl) => { *hd := 0; () }, Nil => () };
    let y = x;
    ()
  } : Dllbc.Term) = (progSeed [x, b]{
    match b { Cons(hd, tl) => { *hd := 0; () }, Nil => () };
    let y = x;
    ()
  }) := rfl

-- Dllbc/Tests/S3Sym.lean site 26
example : (dllbcWith [x, b]{
    match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
    let y = x;
    ()
  } : Dllbc.Term) = (progSeed [x, b]{
    match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
    let y = x;
    ()
  }) := rfl

-- Dllbc/Tests/S3Sym.lean site 27
example : (dllbcWith [x, b]{
    match b {
      Cons(hd, tl) => match tl {
        Cons(h2, t2) => { *h2 := 0; let y = x; () },
        Nil => { let y = x; () }
      },
      Nil => { let y = x; () }
    }
  } : Dllbc.Term) = (progSeed [x, b]{
    match b {
      Cons(hd, tl) => match tl {
        Cons(h2, t2) => { *h2 := 0; let y = x; () },
        Nil => { let y = x; () }
      },
      Nil => { let y = x; () }
    }
  }) := rfl

-- Dllbc/Tests/S3Sym.lean site 28
example : (dllbcWith [z]{
    let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
    ()
  } : Dllbc.Term) = (progSeed [z]{
    let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
    ()
  }) := rfl

-- Dllbc/Tests/S7Group.lean site 29
example : (dllbcWith [c, x, y]{ match c { True => x, False => y } } : Dllbc.Term) = (progSeed [c, x, y]{ match c { True => x, False => y } }) := rfl

-- Dllbc/Tests/S7Group.lean site 30
example : (dllbcWith []{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      *r := 7;
      let z = a;
      () } : Dllbc.Term) = (prog{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      *r := 7;
      let z = a;
      () }) := rfl

-- Dllbc/Tests/S7Group.lean site 31
example : (dllbcWith [b]{ b } : Dllbc.Term) = (progSeed [b]{ b }) := rfl

-- Dllbc/Tests/S7Group.lean site 32
example : (dllbcWith []{
      let x = Cons(1, Nil); let b = &mut x;
      let r = through(b);
      *r := Cons(9, Nil);
      let y = x;
      () } : Dllbc.Term) = (prog{
      let x = Cons(1, Nil); let b = &mut x;
      let r = through(b);
      *r := Cons(9, Nil);
      let y = x;
      () }) := rfl

-- Dllbc/Tests/S7Group.lean site 33
example : (dllbcWith []{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      let tk = *r;
      let z = a;
      () } : Dllbc.Term) = (prog{
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      let tk = *r;
      let z = a;
      () }) := rfl

-- Dllbc/Tests/S7Group.lean site 34
example : (dllbcWith [b]{ b } : Dllbc.Term) = (progSeed [b]{ b }) := rfl

-- Dllbc/Tests/S9Diff.lean site 35
example : (dllbcWith [b]{ b } : Dllbc.Term) = (progSeed [b]{ b }) := rfl

-- Dllbc/Tests/S9Diff.lean site 36
example : (dllbcWith [b]{ match b { Nil => b, Cons(hd, tl) => tl } } : Dllbc.Term) = (progSeed [b]{ match b { Nil => b, Cons(hd, tl) => tl } }) := rfl

-- Dllbc/Tests/S9Diff.lean site 37
example : (dllbcWith [c, x, y]{ match c { True => x, False => y } } : Dllbc.Term) = (progSeed [c, x, y]{ match c { True => x, False => y } }) := rfl

-- Dllbc/Tests/S9Diff.lean site 38
example : (dllbcWith [e, v]{ let tail = *v; *v := Cons(e, tail); () } : Dllbc.Term) = (progSeed [e, v]{ let tail = *v; *v := Cons(e, tail); () }) := rfl

-- Dllbc/Tests/S9Diff.lean site 39
example : (dllbcWith []{
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  *r := 7;
  let za = a; let zb = b;
  () } : Dllbc.Term) = (prog{
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  *r := 7;
  let za = a; let zb = b;
  () }) := rfl

-- Dllbc/Tests/S9Diff.lean site 40
example : (dllbcWith []{
  let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () } : Dllbc.Term) = (prog{
  let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () }) := rfl

-- Dllbc/Tests/S9Diff.lean site 41
example : (dllbcWith []{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = through(b); *r := Cons(9, Nil); let y = x; () } : Dllbc.Term) = (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = through(b); *r := Cons(9, Nil); let y = x; () }) := rfl

-- Dllbc/Tests/S9Diff.lean site 42
example : (dllbcWith []{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () } : Dllbc.Term) = (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () }) := rfl

-- Dllbc/Tests/S9Diff.lean site 43
example : (dllbcWith []{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () } : Dllbc.Term) = (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () }) := rfl

-- Dllbc/Tests/S14Bounds.lean site 44
example : (dllbcWith []{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 2, (), ());
  let y = x;
  () } : Dllbc.Term) = (prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 2, (), ());
  let y = x;
  () }) := rfl

-- Dllbc/Tests/S14Bounds.lean site 45
example : (dllbcWith []{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 4, (), ());
  let y = x;
  () } : Dllbc.Term) = (prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 4, (), ());
  let y = x;
  () }) := rfl

-- Dllbc/Tests/S14Bounds.lean site 46
example : (dllbcWith []{
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { *ei := 9; *ej := 8; let y = x; () } } } : Dllbc.Term) = (prog{
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { *ei := 9; *ej := 8; let y = x; () } } }) := rfl

-- Dllbc/Tests/S14Bounds.lean site 47
example : (dllbcWith []{
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { let taken = *ei; let y = x; () } } } : Dllbc.Term) = (prog{
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { let taken = *ei; let y = x; () } } }) := rfl

-- Dllbc/Tests/S17Spec.lean site 48
example : (dllbcWith []{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &mut x;
  swapS(b, 0, 2, (), ());
  let y = x;
  () } : Dllbc.Term) = (prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &mut x;
  swapS(b, 0, 2, (), ());
  let y = x;
  () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 49
example : (dllbc{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 50
example : (dllbc{
  let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; () } : Dllbc.Term) = (prog{
  let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 51
example : (dllbc{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let b = a; () } : Dllbc.Term) = (prog{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let b = a; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 52
example : (dllbc{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let x = a[0]; () } : Dllbc.Term) = (prog{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let x = a[0]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 53
example : (dllbc{ let a = Arr(3, 1, 2); a[0] := 9; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); a[0] := 9; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 54
example : (dllbc{ let a = Arr(3, 1, 2); let x = a[2]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); let x = a[2]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 55
example : (dllbc{ let a = Arr(3, 1, 2); let e = &mut a[1]; *e := 8; let y = a[1]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); let e = &mut a[1]; *e := 8; let y = a[1]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 56
example : (dllbc{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           a[1 ; 2] := run;
                           let w = a[0]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           a[1 ; 2] := run;
                           let w = a[0]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 57
example : (dllbc{ let a = Arr(3, 1, 2, 7, 5);
           let m = &mut a[1 ; 3];
           let inner = &mut (*m)[1 ; 2];
           (*inner)[0] := 9;
           let b = a;
           () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2, 7, 5);
           let m = &mut a[1 ; 3];
           let inner = &mut (*m)[1 ; 2];
           (*inner)[0] := 9;
           let b = a;
           () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 58
example : (dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[2 ; 3];
                           () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[2 ; 3];
                           () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 59
example : (dllbc{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 3]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 3]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 60
example : (dllbc{ let a = Arr(3, 1, 2); let x = a[3]; () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2); let x = a[3]; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 61
example : (dllbc{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           let x = a[1];
                           () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           let x = a[1];
                           () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 62
example : (dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           *q := 6;
                           let b = a;
                           () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           *q := 6;
                           let b = a;
                           () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 63
example : (dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           (*p)[0] := 4;
                           () } : Dllbc.Term) = (prog{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           (*p)[0] := 4;
                           () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 64
example : (dllbc{
    let a = Arr(3, 1, 2);
    let p = &mut a[0 ; 1]; let q = &mut a[1 ; 1]; let r = &mut a[2 ; 1];
    (*p)[0] := 7; (*q)[0] := 8; (*r)[0] := 9;
    let b = a; () } : Dllbc.Term) = (prog{
    let a = Arr(3, 1, 2);
    let p = &mut a[0 ; 1]; let q = &mut a[1 ; 1]; let r = &mut a[2 ; 1];
    (*p)[0] := 7; (*q)[0] := 8; (*r)[0] := 9;
    let b = a; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 65
example : (dllbc{
    let a = Arr(3, 1, 2);
    let p = &mut a[0]; let q = &mut a[1]; let r = &mut a[2];
    *p := 7; *q := 8; *r := 9;
    let b = a; () } : Dllbc.Term) = (prog{
    let a = Arr(3, 1, 2);
    let p = &mut a[0]; let q = &mut a[1]; let r = &mut a[2];
    *p := 7; *q := 8; *r := 9;
    let b = a; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 66
example : (dllbcWith []{
  let a = Arr(3, 1, 2); let s = &mut a[1 ; 1]; fill1(s); let b = a; () } : Dllbc.Term) = (prog{
  let a = Arr(3, 1, 2); let s = &mut a[1 ; 1]; fill1(s); let b = a; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 67
example : (dllbcWith []{
  let a = Arr(3, 1, 2, 7);
  let s = &mut a[0 ; 2]; let t = &mut a[2 ; 2];
  bump(s); bump(t);
  let b = a; () } : Dllbc.Term) = (prog{
  let a = Arr(3, 1, 2, 7);
  let s = &mut a[0 ; 2]; let t = &mut a[2 ; 2];
  bump(s); bump(t);
  let b = a; () }) := rfl

-- Dllbc/Tests/S24Arrays.lean site 68
example : (dllbcWith []{
  let a = Arr(3, 1, 2);
  let p = &mut a[0 ; 1]; let q = &mut a[1 ; 2];
  (*p)[0] := 5; (*q)[1] := 6;
  let b = a; () } : Dllbc.Term) = (prog{
  let a = Arr(3, 1, 2);
  let p = &mut a[0 ; 1]; let q = &mut a[1 ; 2];
  (*p)[0] := 5; (*q)[1] := 6;
  let b = a; () }) := rfl

-- Dllbc/Tests/S25ArrSort.lean site 69
example : (dllbcWith []{
  let z = Arr(1, 2, 3); let b = &mut z; citedCarve(3, 1, 1, Refl, b); let y = z; () } : Dllbc.Term) = (prog{
  let z = Arr(1, 2, 3); let b = &mut z; citedCarve(3, 1, 1, Refl, b); let y = z; () }) := rfl

-- Dllbc/Tests/S25ArrSort.lean site 70
example : (dllbcWith []{
  let z = Arr(1, 2); let b = &mut z; citedCarve(2, 5, 5, Refl, b); let y = z; () } : Dllbc.Term) = (prog{
  let z = Arr(1, 2); let b = &mut z; citedCarve(2, 5, 5, Refl, b); let y = z; () }) := rfl
