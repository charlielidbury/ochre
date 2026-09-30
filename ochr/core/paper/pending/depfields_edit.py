# Dependent fields (D64, RULES §9 at 6060c8e5): paper edits. Apply once the checker lands on ochr-core.
# LEAN_TAGS below must be filled from the checker's function names before applying.
import sys
P = sys.argv[1] if len(sys.argv) > 1 else '/home/charlielidbury/repos/ochre-ochr-core/ochr/core/paper/'
LEAN_TAGS = '#lean("TODO")'

def edit(f, pairs):
    s = open(P + f).read()
    for o, n in pairs:
        assert s.count(o) == 1, (f, o[:80], s.count(o))
        s = s.replace(o, n)
    open(P + f, 'w').write(s)

# --- appendix ---
edit('sections/appendix.typ', [
  # copy types
  ("or a non-recursive inductive type in `Type₀` whose field types are copy types;",
   "or a non-recursive inductive type in `Type₀` whose field types are copy types and which has no dependent constructor (@app-dep) unless it is declared `copy`;"),
  # [Ind-decl] field premise
  ("""$"for every field" g_(i j) : A_(i j): quad A_(i j) "is a parameter, or is built from" ty("D")(overline(x)) ", declared inductive types and" times$, $Sigma + ty("D") ";" (overline(x) : overline(T) |-> overline(sigma)) tack.r A_(i j) ev T_(i j) : s_(i j) quad s_(i j) in {ty("Prop"), ty("Type")_0}$)""",
   """$"for every field" g_(i j) : A_(i j): quad A_(i j) "is a parameter, or is built from" ty("D")(overline(x)) ", declared inductive types," times "and type functions (@app-dep)"$, $Sigma + ty("D") ";" (overline(x) : overline(T) |-> overline(sigma), g_(i 1) : T_(i 1) |-> tau_1, dots, g_(i (j-1)) : T_(i (j-1)) |-> tau_(j-1)) tack.r A_(i j) ev T_(i j) : s_(i j) quad s_(i j) in {ty("Prop"), ty("Type")_0}$)"""),
  ("Field types are first-order data or parameters: they may mention the type being declared, but contain no `Π` and no `&`, which is strict positivity in its simplest form (note 4 of @app-notes).",
   "Field types are first-order data, parameters or calls of type functions (@app-dep): they may mention the type being declared, but contain no `Π` and no `&`, which is strict positivity in its simplest form (note 4 of @app-notes); a field's type may mention the fields before it, each bound to a fresh generic value $tau$ (⋆ for a proof field)."),
])

DEP = r'''
=== Dependent fields <app-dep>

A field's type may mention the constructor's earlier fields, as in the growable vector `Vec(E) := MkVec(n : Word, items : Array(E, n))`. [Ind-decl] checks field `j`'s type with the parameters and the fields before it bound to fresh generic values, and rejects a type that mentions field `j` or a later one; an earlier field occurs only as an argument inside a later field's type. A field that a later field's type mentions is an _index field_, and a constructor with one is _dependent_. A field type may be a call $F(overline(a))$ of an earlier definition whose declared codomain is a sort (`Array(E, n)`, or a proof field `Sorted(xs)`), with arguments that are parameters, fields, numerals or first-order types not mentioning `D`, and which at the generic fields computes to no Π-type, borrow type, sort or equation. `D` may occur inside another inductive $ty("D'")(dots)$ only at a _nestable_ parameter of $ty("D'")$, one that occurs in its field types only as a whole field type or at a nestable parameter of an inductive; otherwise `MkNBox(f : Neg(A))`, with `Neg(A) := Π(x : A). Void`, would let `MkBad(b : NBox(Bad))` bring back the non-positive `Bad` of note 4.

*Typing by position.* The type of a field place $p.g_j$ of a dependent constructor is its declared type with the parameters taken from `p`'s type and each earlier field bound to the current content of `p`'s field, so $"type"(p."items") = ty("Array")(E, cont(p.n))$ ([Field]). [Split] refines $sigma := ty("C")(overline(a); sigma_1, dots, sigma_k)$ with each $sigma_i$ fresh at the type computed from $sigma_1, dots, sigma_(i-1)$, [T-Ctor] checks each argument against the type computed from the earlier arguments, and [Assign] types the value it writes by the target place's type.

*Open and repack.* A dependency may be broken while a value is mutated, and is re-checked where the value must be whole again. Writing, borrowing or moving out a field of a dependent constructor _opens_ the value ([Open]). While it is open, a data field whose declared type mentions earlier fields takes its content's type whenever the content does not have its telescope type, and assigning it is a strong update, typed by the value; a write or borrow through an index field sets every proof field whose type mentions it to ⊥, which is an error to read until it is assigned, against its type at the current contents. At every _whole-again_ point, each value of a dependent constructor inside the value must have its type by its telescope, with no ⊥ or ghost inside ([Repack]); a failure is a type error there. The points are a place read, moved or borrowed whole (so a borrow variable passed on), the end of a borrow of the value (a borrow parameter's when the function returns), a function's or constant's result, `Id`'s observed result and owners, and the captures of a stuck block, closure or Π-type. So `*v.n := 2; *v.items := a` is accepted in either order: `v` is open between the writes and whole at the return. The machine's own runs, the concrete calls a checked program makes and the re-runs of sealed programs, do not check [Repack], because they are instances of generically checked code.

*Injectivity, restricted.* For a dependent constructor, [Eq-inj] applies only when every index field is convertible on both sides, and the field types are then computed from the left side; otherwise the equation stays as it is. This fails safe and is incomplete: the full rule of observational type theory needs a dependent conjunction. Proof fields are ⋆ on both sides and never block. [Close], sealed programs, observation and the model are unchanged; in the model a dependent constructor denotes a Σ-type. ''' + LEAN_TAGS + '\n'

s = open(P + 'sections/appendix.typ').read()
anchor = '== Well-formed environments <app-wf>'
assert s.count(anchor) == 1
s = s.replace(anchor, DEP.lstrip('\n') + '\n' + anchor)
open(P + 'sections/appendix.typ', 'w').write(s)

# --- body ---
edit('sections/intro.typ', [
  ("[Peano numbers only; arrays as a library, borrowed in parts only through a continuation (@sec-eval-qs).]",
   "[Peano numbers only; arrays as a library, borrowed in parts only through a continuation, and growable vectors as a user type with a dependent field (@sec-eval-qs).]"),
])
edit('sections/impl.typ', [
  ("so the length lives only in the type.",
   "so the length lives only in the type. A growable vector is a user type whose second field's type depends on the first, `Vec(E) := MkVec(n : Word, items : Array(E, n))`, with `Push` and `Pop` written in place; the dependency may be broken while the vector is mutated, and is re-checked wherever the value must be whole again (@app-dep)."),
])
print('ok')
