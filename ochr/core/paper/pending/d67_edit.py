# D67 (reborrow-and-replace accepted): meta-order's d2a1b498 (proof, sections/tf.typ; owned-part reading) and the lead's [Access] wording (appendix).
# Apply ONLY once D67 is in the checker on ochr-core (same gate as D65), and cite Trav
# only if it lands in the suite. Usage: python3 d67_tf.py <paper dir>
import sys
P = sys.argv[1]
f = P + 'sections/tf.typ'
s = open(f).read()
PAIRS = [("  - An assignment's new value can be ended by the assignment's own [Access] on the symbolic path only: `x := Pick(n, &*x, &b)` ends the new borrow symbolically, while at `n = 1` the ground one survives. This is harmless for the drop clause. While the new value is in flight, the only drop is of the assigned place's old content. That content is a borrow, since the place has borrow type, so the drop ends it and never fails. After the assignment the value is a binding.", "  - An assignment's new value is never ended by the assignment's own [Access], on either path. That [Access] ends only the loans in the part of the place's content that the place owns. A place that receives a borrow has borrow type, and what it owns is its old borrow, not the data behind it. A place of data type receives loan-free data. While the new value is in flight, the only drop is of the old content, a borrow, so the drop ends it and never fails. After the assignment the value is a binding."), ("A [Match]'s [Access] ends only loans on the path and loans inside a neutral at the head, not loans deeper in a value. That is why the argument goes through the fill staying stuck. A program that reborrows through `Pick`'s result and then assigns `x := &c` is rejected on the symbolic path for this reason.", "A [Match]'s [Access] ends only loans on the path and loans inside a neutral at the head, not loans deeper in a value. An assignment's [Access] ends only the loans in the part of the place's content that the place owns, including loans inside neutrals in that part ($L^A$, @app-aux). A loan behind a borrow the place holds, even one inside a neutral, is left alone on both paths, and the drop of that borrow carries it back to its owner. In each case, an early end that the [Access] makes is made inside a neutral, so the argument goes through the fill staying stuck. A program that reborrows through `Pick`'s result and then assigns `x := &c` is rejected on the symbolic path for this reason."), ("The theorem does not cover the reborrow-and-replace idiom `x := &(*x).1`, because the rules reject it: the assignment's [Access] on `x` ends the new borrow, whose loan sits inside `x`'s content.", "The reborrow-and-replace idiom is in F, and it is accepted. `Trav(x : &Nat) : Unit := match *x { Z => (), S p => (x := &p; *x := 0) }` satisfies F1–F6. The new borrow's loan sits behind the borrow that `x` held, which the assignment's [Access] leaves alone. The drop of the old borrow carries the loan back to its owner, where it stays live. So @tf-thm covers it.")]
for o, n in PAIRS:
    assert s.count(o) == 1, o[:80]
    s = s.replace(o, n)
open(f, 'w').write(s)

# Appendix: assignment's [Access] (lead's wording, to be RULES [Access] at landing; DECISIONS e50a754a:
# neutrals are ended only in the owned part). LEAN_TAGS_ASSIGN: fill from the checker at landing.
LEAN_TAGS_ASSIGN = '"TODO"'
f = P + 'sections/appendix.typ'
s = open(f).read()
APP = [
  ("+ *Loans an access must end* ([Access]). For reading, borrowing and assigning,",
   "+ *Loans an access must end* ([Access]). For reading and borrowing,"),
  ("""and for matching, $L^M_Omega (p) = {ell mid(|) cont_Omega (q) = "loan"_ell, q in "pre"(p)} union "hl"(cont_Omega (p))$,""",
   """for assigning, $L^A_Omega (p) = {ell mid(|) cont_Omega (q) = "loan"_ell, q in "pre"(p)} union "ol"(cont_Omega (p))$, where $"ol"$ is $"loans"$ except that it does not look inside a borrow, $"ol"("borrow"_m w) = emptyset$; and for matching, $L^M_Omega (p) = {ell mid(|) cont_Omega (q) = "loan"_ell, q in "pre"(p)} union "hl"(cont_Omega (p))$,"""),
  ("""*[Access]*. $acc^R_p (Omega)$ and $acc^M_p (Omega)$ end, one at a time and in the order of item 2 of @app-aux, the borrow of the first label of $L^R_Omega (p)$, respectively $L^M_Omega (p)$, until that set is empty:""",
   """*[Access]*. $acc^R_p (Omega)$, $acc^A_p (Omega)$ and $acc^M_p (Omega)$ end, one at a time and in the order of item 2 of @app-aux, the borrow of the first label of $L^R_Omega (p)$, $L^A_Omega (p)$ or $L^M_Omega (p)$, until that set is empty:"""),
  ("""acc^X_p (Omega') & "if" ell "is the first label of" L^X_Omega (p) "and" Omega arrow.squiggly_ell Omega') quad (X in {R, M}). $""",
   """acc^X_p (Omega') & "if" ell "is the first label of" L^X_Omega (p) "and" Omega arrow.squiggly_ell Omega') quad (X in {R, A, M}). $"""),
  ("Every rule that reads, borrows or assigns a place `p` first computes $acc^R_p$, and a match on `p` computes $acc^M_p$.",
   "Every rule that reads or borrows a place `p` first computes $acc^R_p$, an assignment to `p` computes $acc^A_p$, and a match on `p` computes $acc^M_p$. Before assigning `p`, [Access] ends every borrow whose loan lies in the part of `content(p)` that `p` owns: on the path to `p`, in its owned content, or inside a neutral there, since a loan's position inside a neutral is unknown. A loan behind a borrow held in `content(p)`, including one inside a neutral behind that borrow, is not ended: the [Drop] of the old content ends that borrow ([End]), which carries the loan back to its owner, where it stays live. This is Rust's rule that a reborrow `&mut (*x).f` lasts as long as the reference `x` held, not the variable `x`. Reads, moves and borrows of `p` still end every loan inside `content(p)`."),
  ('#lean("endBorrow", "accessPath", "accessInside", "accessNeutralHead")',
   '#lean("endBorrow", "accessPath", "accessInside", "accessNeutralHead", ' + LEAN_TAGS_ASSIGN + ')'),
  ("""ir(name: "Assign", pv($cfg(Omega, t) ev cfg(Omega_1, v) quad acc^R_p (Omega_1 dot v) = Omega_2 dot v'$""",
   """ir(name: "Assign", pv($cfg(Omega, t) ev cfg(Omega_1, v) quad acc^A_p (Omega_1 dot v) = Omega_2 dot v'$"""),
  ("""$acc^R_p (Omega_1 dot v) = Omega_2 dot v' quad "drop"(Omega_2, cont_(Omega_2)(p)) = Omega_3$), $Omega tack.r p := t""",
   """$acc^A_p (Omega_1 dot v) = Omega_2 dot v' quad "drop"(Omega_2, cont_(Omega_2)(p)) = Omega_3$), $Omega tack.r p := t"""),
]
for o, n in APP:
    assert s.count(o) == 1, o[:80]
    s = s.replace(o, n)
open(f, 'w').write(s)
print('ok')
