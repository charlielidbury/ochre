#include <stdlib.h>

// Commutativity of Peano addition, relational, with NO pure model of the
// number. Two copies of x and y; add(x, y) runs on one, add(y2, x2) on the
// other; the two results are proved same(_, _), where same(p, p2) is a binary
// heap predicate "p and p2 are the same number" (lockstep walk to the two
// Zs) with no sequence and no length. The final heaps are different objects,
// so unlike concat-nospec-1.c no single contract pins both; the content of
// commutativity is the lemma cross, and the "n + S m = S (n + m)" step is the
// lemma rot1. Both are inductions on a heap predicate, sameseg.
//
// The first half of the file (seg, num, addM, add) is add-nospec-1.c verbatim.

struct nat { struct nat *pred; };

/*@
predicate seg(struct nat *p, struct nat *last) =
  p == last ? true : [1/2]p->pred |-> ?q &*& q != 0 &*& seg(q, last);

predicate num(struct nat *p, struct nat *last, struct nat *v) =
  p == 0 ? last == 0 : last != 0 &*& seg(p, last) &*& last->pred |-> v;
@*/

void addM(struct nat **x, struct nat *y)
//@ requires [?f]*x |-> ?px &*& num(px, ?last, 0) &*& (px == 0 ? f == 1 : true);
//@ ensures  [f]*x |-> (px == 0 ? y : px) &*& num(px, last, y);
{
  //@ open num(px, last, 0);
  if (*x == 0) {
    *x = y;
    //@ close num(0, 0, y);
  } else {
    struct nat *p = *x;
    //@ open seg(p, last);
    /*@ if (p == last) { close num(0, 0, 0); } else { assert [1/2]p->pred |-> ?q; close num(q, last, 0); } @*/
    addM(&p->pred, y);
    /*@ if (p == last) { open num(0, 0, y); } else { assert [1/2]p->pred |-> ?q; open num(q, last, y); } @*/
    //@ close seg(p, last);
    //@ close num(p, last, y);
  }
}

struct nat *add(struct nat *x, struct nat *y)
//@ requires num(x, ?lx, 0);
//@ ensures  result == (x == 0 ? y : x) &*& num(x, lx, y);
{
  addM(&x, y);
  return x;
}

/*@
// same(p, p2): p and p2 are the same number. Lockstep walk to the two Zs.
predicate same(struct nat *p, struct nat *p2) =
  p == 0 ? p2 == 0
         : p2 != 0 &*& malloc_block_nat(p) &*& malloc_block_nat(p2)
           &*& p->pred |-> ?q &*& p2->pred |-> ?q2 &*& same(q, q2);

// sameseg(p, p2, q, q2): lockstep segment from (p, p2) up to but not including (q, q2).
predicate sameseg(struct nat *p, struct nat *p2, struct nat *q, struct nat *q2) =
  p == q ? p2 == q2
         : p != 0 &*& p2 != 0 &*& p2 != q2 &*& malloc_block_nat(p) &*& malloc_block_nat(p2)
           &*& p->pred |-> ?n &*& p2->pred |-> ?n2 &*& sameseg(n, n2, q, q2);

// rest(p, p2, la, la2): what same(p, p2) keeps back when it lends its pred
// cells to num(p, la, 0) and num(p2, la2, 0): malloc blocks, the other half
// of every pred cell before the last nodes, and the last nodes' malloc blocks.
predicate rest(struct nat *p, struct nat *p2, struct nat *la, struct nat *la2) =
  p != 0 &*& p2 != 0 &*& malloc_block_nat(p) &*& malloc_block_nat(p2)
  &*& (p == la ? p2 == la2
              : p2 != la2 &*& [1/2]p->pred |-> ?q &*& [1/2]p2->pred |-> ?q2 &*& rest(q, q2, la, la2));

predicate restv(struct nat *p, struct nat *p2, struct nat *la, struct nat *la2) =
  p == 0 ? p2 == 0 &*& la == 0 &*& la2 == 0 : rest(p, p2, la, la2);

lemma void rest_nonnull(struct nat *p, struct nat *p2, struct nat *la, struct nat *la2)
  requires rest(p, p2, la, la2);
  ensures  rest(p, p2, la, la2) &*& p != 0 &*& p2 != 0 &*& la != 0 &*& la2 != 0;
{
  open rest(p, p2, la, la2);
  if (p == la) {
  } else {
    assert [1/2]p->pred |-> ?q &*& [1/2]p2->pred |-> ?q2;
    rest_nonnull(q, q2, la, la2);
  }
  close rest(p, p2, la, la2);
}

// Lend the pred cells out.
lemma void split(struct nat *p, struct nat *p2)
  requires same(p, p2);
  ensures  num(p, ?la, 0) &*& num(p2, ?la2, 0) &*& restv(p, p2, la, la2);
{
  open same(p, p2);
  if (p == 0) {
    close num(p, 0, 0); close num(p2, 0, 0); close restv(p, p2, 0, 0);
  } else {
    assert p->pred |-> ?q &*& p2->pred |-> ?q2;
    split(q, q2);
    assert num(q, ?lq, 0) &*& num(q2, ?lq2, 0);
    open restv(q, q2, lq, lq2);
    if (q == 0) {
      open num(q, lq, 0); open num(q2, lq2, 0);
      close seg(p, p); close num(p, p, 0);
      close seg(p2, p2); close num(p2, p2, 0);
      close rest(p, p2, p, p2); close restv(p, p2, p, p2);
    } else {
      rest_nonnull(q, q2, lq, lq2);
      open num(q, lq, 0); open num(q2, lq2, 0);
      close seg(p, lq); close num(p, lq, 0);
      close seg(p2, lq2); close num(p2, lq2, 0);
      close rest(p, p2, lq, lq2); close restv(p, p2, lq, lq2);
    }
  }
}

// Take the pred cells back, in lockstep, up to the last nodes.
lemma void peel(struct nat *x, struct nat *x2, struct nat *lx, struct nat *lx2)
  requires rest(x, x2, lx, lx2) &*& seg(x, lx) &*& seg(x2, lx2);
  ensures  sameseg(x, x2, lx, lx2) &*& lx != 0 &*& lx2 != 0 &*& malloc_block_nat(lx) &*& malloc_block_nat(lx2);
{
  open rest(x, x2, lx, lx2);
  open seg(x, lx); open seg(x2, lx2);
  if (x == lx) {
    close sameseg(x, x2, lx, lx2);
  } else {
    assert x->pred |-> ?q &*& x2->pred |-> ?q2;
    peel(q, q2, lx, lx2);
    close sameseg(x, x2, lx, lx2);
  }
}

// A lockstep segment, its last nodes, and a same() continuation make a same().
lemma void same_of_sameseg(struct nat *x, struct nat *x2, struct nat *lx, struct nat *lx2)
  requires sameseg(x, x2, lx, lx2) &*& lx != 0 &*& lx2 != 0 &*& malloc_block_nat(lx) &*& malloc_block_nat(lx2)
       &*& lx->pred |-> ?n &*& lx2->pred |-> ?n2 &*& same(n, n2);
  ensures  same(x, x2);
{
  open sameseg(x, x2, lx, lx2);
  if (x == lx) {
    close same(x, x2);
  } else {
    assert x->pred |-> ?q &*& x2->pred |-> ?q2;
    same_of_sameseg(q, q2, lx, lx2);
    close same(x, x2);
  }
}

// rot1: the heap form of  n + S m = S (n + m).  Given lockstep segments
// (c1..lc) ~ (c21..lc2), a node c in front on the first side (c->pred = c1)
// and a node m behind on the second side (lc2->pred = m), the segments
// (c, c1..lc) ~ (c21..lc2, m) are lockstep too. Induction on the heap
// predicate sameseg; nothing sequence-shaped.
lemma void rot1(struct nat *c, struct nat *c1, struct nat *c21, struct nat *lc, struct nat *lc2, struct nat *m)
  requires sameseg(c1, c21, lc, lc2) &*& c != 0 &*& malloc_block_nat(c) &*& c->pred |-> c1
       &*& lc2 != 0 &*& malloc_block_nat(lc2) &*& lc2->pred |-> m
       &*& m != 0 &*& malloc_block_nat(m) &*& m->pred |-> ?mv &*& lc->pred |-> ?v;
  ensures  sameseg(c, c21, lc, m) &*& malloc_block_nat(m) &*& m->pred |-> mv &*& lc->pred |-> v;
{
  open sameseg(c1, c21, lc, lc2);
  if (c1 == lc) {
    close sameseg(lc, m, lc, m);
    close sameseg(c, c21, lc, m);
  } else {
    assert c1->pred |-> ?c11 &*& c21->pred |-> ?c211;
    rot1(c1, c11, c211, lc, lc2, m);
    close sameseg(c, c21, lc, m);
  }
}

lemma void sameseg_sym(struct nat *p, struct nat *p2, struct nat *q, struct nat *q2)
  requires sameseg(p, p2, q, q2);
  ensures  sameseg(p2, p, q2, q);
{
  open sameseg(p, p2, q, q2);
  if (p == q) {
    close sameseg(p2, p, q2, q);
  } else {
    assert p->pred |-> ?n &*& p2->pred |-> ?n2;
    sameseg_sym(n, n2, q, q2);
    close sameseg(p2, p, q2, q);
  }
}

// cross: the heap form of  x + y = y + x.  Copy 1 is the chain a..la, then
// c..lc, then d; copy 2 is c2..lc2, then a2..la2, then d2. With (a..la) ~
// (a2..la2), (c..lc) ~ (c2..lc2) and same(d, d2), the whole chains are the
// same number. Induction on the heap predicate sameseg(a, a2, la, la2); the
// step pairs a with c2 and rotates one node with rot1.
lemma void cross(struct nat *a, struct nat *a2, struct nat *la, struct nat *la2,
                 struct nat *c, struct nat *c2, struct nat *lc, struct nat *lc2,
                 struct nat *d, struct nat *d2)
  requires sameseg(a, a2, la, la2) &*& la != 0 &*& la2 != 0 &*& malloc_block_nat(la) &*& malloc_block_nat(la2)
       &*& la->pred |-> c &*& la2->pred |-> d2
       &*& sameseg(c, c2, lc, lc2) &*& lc != 0 &*& lc2 != 0 &*& malloc_block_nat(lc) &*& malloc_block_nat(lc2)
       &*& lc->pred |-> d &*& lc2->pred |-> a2
       &*& same(d, d2);
  ensures  same(a, c2);
{
  open sameseg(a, a2, la, la2);
  open sameseg(c, c2, lc, lc2);
  if (a == la) {
    if (c == lc) {
      close same(c, a2);
      close same(a, c2);
    } else {
      assert c->pred |-> ?c1 &*& c2->pred |-> ?c21;
      rot1(c, c1, c21, lc, lc2, la2);
      same_of_sameseg(c, c21, lc, la2);
      close same(a, c2);
    }
  } else {
    assert a->pred |-> ?a1 &*& a2->pred |-> ?a21;
    if (c == lc) {
      close sameseg(lc, a2, lc, a2);
      cross(a1, a21, la, la2, lc, a2, lc, a2, d, d2);
      close same(a, c2);
    } else {
      assert c->pred |-> ?c1 &*& c2->pred |-> ?c21;
      rot1(c, c1, c21, lc, lc2, a2);
      cross(a1, a21, la, la2, c, c21, lc, a2, d, d2);
      close same(a, c2);
    }
  }
}
@*/

// The theorem. Two copies of the same two numbers; x + y on one copy, y + x
// on the other; the two results are the same number.
void comm_two_runs(struct nat *x, struct nat *y, struct nat *x2, struct nat *y2,
                   struct nat **r1, struct nat **r2)
//@ requires same(x, x2) &*& same(y, y2) &*& *r1 |-> _ &*& *r2 |-> _;
//@ ensures  *r1 |-> ?a &*& *r2 |-> ?b &*& same(a, b);
{
  //@ split(x, x2);
  //@ split(y, y2);
  //@ assert num(x, ?lx, 0) &*& num(x2, ?lx2, 0) &*& num(y, ?ly, 0) &*& num(y2, ?ly2, 0);
  struct nat *r = add(x, y);
  struct nat *s = add(y2, x2);
  *r1 = r;
  *r2 = s;
  /*@ {
  open restv(x, x2, lx, lx2);
  open restv(y, y2, ly, ly2);
  if (x != 0) { rest_nonnull(x, x2, lx, lx2); }
  if (y != 0) { rest_nonnull(y, y2, ly, ly2); }
  open num(x, lx, y);
  open num(y2, ly2, x2);
  open num(x2, lx2, 0);
  open num(y, ly, 0);
  if (x == 0) {
    if (y == 0) {
      close same(0, 0);
    } else {
      peel(y, y2, ly, ly2);
      close same(0, 0);
      same_of_sameseg(y, y2, ly, ly2);
    }
  } else if (y == 0) {
    peel(x, x2, lx, lx2);
    close same(0, 0);
    same_of_sameseg(x, x2, lx, lx2);
  } else {
    peel(x, x2, lx, lx2);
    peel(y, y2, ly, ly2);
    close same(0, 0);
    cross(x, x2, lx, lx2, y, y2, ly, ly2, 0, 0);
  }
  } @*/
}

// The step on its own:  x + S y  and  S (x + y)  are the same number. Copy 1
// has a node n with pred y (S y) and runs add(x, n); copy 2 runs add(x2, y2)
// and moves the result into a node m (S (x2 + y2)). The proof is rot1 once.
void succ_two_runs(struct nat *x, struct nat *y, struct nat *n,
                   struct nat *x2, struct nat *y2, struct nat *m,
                   struct nat **r1, struct nat **r2)
/*@ requires same(x, x2) &*& same(y, y2)
         &*& n != 0 &*& malloc_block_nat(n) &*& n->pred |-> y
         &*& m != 0 &*& malloc_block_nat(m) &*& m->pred |-> _
         &*& *r1 |-> _ &*& *r2 |-> _; @*/
//@ ensures  *r1 |-> ?a &*& *r2 |-> ?b &*& same(a, b);
{
  //@ split(x, x2);
  //@ assert num(x, ?lx, 0) &*& num(x2, ?lx2, 0);
  struct nat *r = add(x, n);
  struct nat *t = add(x2, y2);
  m->pred = t;
  *r1 = r;
  *r2 = m;
  /*@ {
  open restv(x, x2, lx, lx2);
  open num(x, lx, n);
  open num(x2, lx2, y2);
  if (x == 0) {
    close same(n, m);
  } else {
    rest_nonnull(x, x2, lx, lx2);
    peel(x, x2, lx, lx2);
    open sameseg(x, x2, lx, lx2);
    if (x == lx) {
      close same(n, lx2);
      close same(x, m);
    } else {
      assert x->pred |-> ?x1 &*& x2->pred |-> ?x21;
      sameseg_sym(x1, x21, lx, lx2);
      rot1(x2, x21, x1, lx2, lx, n);
      sameseg_sym(x2, x1, lx2, n);
      same_of_sameseg(x1, x2, n, lx2);
      close same(x, m);
    }
  }
  } @*/
}
