#include <stdlib.h>

// Peano naturals on the heap: NULL is Z, a node is S(pred).
struct nat { struct nat *pred; };

/*@
// The pure specification separation logic cannot do without.
inductive N = Z | S(N);

fixpoint N plus(N a, N b) {
  switch (a) { case Z: return b; case S(pa): return S(plus(pa, b)); }
}

// Representation predicate: the heap reachable from p represents the math nat n.
predicate nat(struct nat *p; N n) =
  p == 0 ? n == Z
         : p->pred |-> ?q &*& malloc_block_nat(p) &*& nat(q, ?m) &*& n == S(m);
@*/

// AddM: walk x to its final Z and replace it with y, by move.
void addM(struct nat **x, struct nat *y)
//@ requires *x |-> ?px &*& nat(px, ?n) &*& nat(y, ?m);
//@ ensures  *x |-> ?rx &*& nat(rx, plus(n, m));
{
  //@ open nat(px, n);
  if (*x == 0) {
    *x = y;
  } else {
    struct nat *p = *x;
    addM(&p->pred, y);
    //@ close nat(p, plus(n, m));
  }
}

// Add: the pure interface.
struct nat *add(struct nat *x, struct nat *y)
//@ requires nat(x, ?n) &*& nat(y, ?m);
//@ ensures  nat(result, plus(n, m));
{
  addM(&x, y);
  return x;
}

/*@
// AddZero: a lemma about N, not about add. Induction on n, not on the heap.
lemma void plus_zero(N n)
  requires true;
  ensures plus(n, Z) == n;
{
  switch (n) { case Z: case S(pn): plus_zero(pn); }
}
@*/

// The doc's  assert AddZero : Πx: Nat. Id Nat (Add x 0) x  becomes this triple.
struct nat *add_zero(struct nat *x)
//@ requires nat(x, ?n);
//@ ensures  nat(result, n);
{
  //@ close nat(0, Z);
  struct nat *r = add(x, 0);
  //@ plus_zero(n);
  return r;
}
