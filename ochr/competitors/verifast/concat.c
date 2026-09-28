#include <stdlib.h>

// Cons lists on the heap: NULL is Nil, a node is Cons(head, tail).
struct list { int head; struct list *tail; };

/*@
// The pure specification separation logic cannot do without.
inductive L = Nil | Cons(int, L);

fixpoint L app(L xs, L ys) {
  switch (xs) { case Nil: return ys; case Cons(x, xs0): return Cons(x, app(xs0, ys)); }
}

// Representation predicate: the heap reachable from p represents the list l.
predicate list(struct list *p; L l) =
  p == 0 ? l == Nil
         : p->head |-> ?x &*& p->tail |-> ?q &*& malloc_block_list(p)
           &*& list(q, ?l0) &*& l == Cons(x, l0);
@*/

// concatM: walk a to its final Nil and replace it with b, by move. No allocation.
void concatM(struct list **a, struct list *b)
//@ requires *a |-> ?pa &*& list(pa, ?xs) &*& list(b, ?ys);
//@ ensures  *a |-> ?ra &*& list(ra, app(xs, ys));
{
  //@ open list(pa, xs);
  if (*a == 0) {
    *a = b;
  } else {
    struct list *p = *a;
    concatM(&p->tail, b);
    //@ close list(p, app(xs, ys));
  }
}

// concat: the pure interface.
struct list *concat(struct list *a, struct list *b)
//@ requires list(a, ?xs) &*& list(b, ?ys);
//@ ensures  list(result, app(xs, ys));
{
  concatM(&a, b);
  return a;
}

/*@
// Associativity: a lemma about L, not about concat. Induction on xs, not on the heap.
lemma void app_assoc(L xs, L ys, L zs)
  requires true;
  ensures app(app(xs, ys), zs) == app(xs, app(ys, zs));
{
  switch (xs) { case Nil: case Cons(x, xs0): app_assoc(xs0, ys, zs); }
}
@*/

// (a ++ b) ++ c  and  a ++ (b ++ c)  are two different programs: the first walks a,
// then walks a and b again; the second walks b, then a. Separation logic has no
// equality between them. The most it can say is that both meet the same contract,
// and the left-nested one only does so via the lemma.

struct list *concat_left(struct list *a, struct list *b, struct list *c)
//@ requires list(a, ?xs) &*& list(b, ?ys) &*& list(c, ?zs);
//@ ensures  list(result, app(xs, app(ys, zs)));
{
  struct list *r = concat(concat(a, b), c);
  //@ app_assoc(xs, ys, zs);
  return r;
}

struct list *concat_right(struct list *a, struct list *b, struct list *c)
//@ requires list(a, ?xs) &*& list(b, ?ys) &*& list(c, ?zs);
//@ ensures  list(result, app(xs, app(ys, zs)));
{
  return concat(a, concat(b, c));
}
