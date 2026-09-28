#include <stdlib.h>

// Peano nats on the heap, NULL is Z, a node is S(pred): the programs of addm.c
// with NO pure model of the number. No ghost N, no length, no fixpoint. The
// ghost arguments are node pointers only. As in concat-nospec-1.c, the walk
// is handed the pred cells at half permission (read-only) and the final Z's
// cell in full; so the contract of addM says exactly which cell it writes.

struct nat { struct nat *pred; };

/*@
// seg(p, last): the nodes from p up to but not including last, pred cells read-only.
predicate seg(struct nat *p, struct nat *last) =
  p == last ? true : [1/2]p->pred |-> ?q &*& q != 0 &*& seg(q, last);

// num(p, last, v): the number p. Its final node is last, whose pred cell is
// owned in full and holds v. A proper Peano nat is num(p, last, 0).
predicate num(struct nat *p, struct nat *last, struct nat *v) =
  p == 0 ? last == 0 : last != 0 &*& seg(p, last) &*& last->pred |-> v;
@*/

// addM: walk x to its final Z and replace it with y, by move. Program unchanged.
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

// add: the by-value wrapper. Program unchanged.
struct nat *add(struct nat *x, struct nat *y)
//@ requires num(x, ?lx, 0);
//@ ensures  result == (x == 0 ? y : x) &*& num(x, lx, y);
{
  addM(&x, y);
  return x;
}

// x + 0 = x, for the record. Zero ghost statements: the postcondition is the
// precondition. Not "represents the same number": the heap is unchanged cell
// for cell, because the one cell addM may write is written with its old value.
struct nat *add_zero(struct nat *x)
//@ requires num(x, ?lx, 0);
//@ ensures  result == x &*& num(x, lx, 0);
{
  return add(x, 0);
}

// x + y and y + x, single runs. Each has a contract that pins its final heap.
// The two heaps are different objects (x's nodes then y's, versus y's nodes
// then x's), so there is no single-run contract in this vocabulary that says
// "the same number" of both. That statement needs two heaps side by side:
// see add-nospec-2.c.
struct nat *add_xy(struct nat *x, struct nat *y)
//@ requires num(x, ?lx, 0) &*& num(y, ?ly, 0);
//@ ensures  result == (x == 0 ? y : x) &*& num(x, lx, y) &*& num(y, ly, 0);
{
  return add(x, y);
}

struct nat *add_yx(struct nat *x, struct nat *y)
//@ requires num(x, ?lx, 0) &*& num(y, ?ly, 0);
//@ ensures  result == (y == 0 ? x : y) &*& num(y, ly, x) &*& num(x, lx, 0);
{
  return add(y, x);
}
