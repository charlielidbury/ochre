import Ochr.Consistency

/-!
# The checker accepted a closed proof of `False` (a positivity hole), checked natively

**Closed by main's D107** (the nesting condition covers the type being declared; nestable
parameters are a greatest fixed point): `Q` is now rejected, and with it `Delta`, `Lem` and `Boom`,
so the block below is marked `reject` there and the guard that the program is accepted is negated.
The rest of this text describes the checker before D107.

`Q (A : Type) (b : Bit) := MkQ(y : FB(A, b), z : OptB(Q(Q(A, b), B1), b))` is accepted. Positivity
(`Check.firstOrderTerm`, K4) lets it through on three counts, each allowed on its own:
* `FB(A, b)` is a call of a type function whose result is a function type only at `b := B1`; at
  the generic `b` the call is stuck, so "computes to a Π" (D36) does not fire;
* the self occurrence `Q(Q(A, b), B1)` puts `Q` itself at `Q`'s own parameter `A`, which `Q` passes
  to a type function (`FB`); the nesting condition (K4, `nestViolation`) is skipped for the
  declaration's own occurrences (`m != n`);
* `OptB`'s value parameter `b` makes `OptB(·, B0)` have no "none" case (`NoneB(h : FF(B0))`,
  `FF(B0)` empty), so `Q(Unit, B0) ≅ Q(Q(Unit, B0), B1) ≅ (Q(Unit, B0) → Void) × (1 + …)`.

That is Curry's paradox: `X ≅ (X → Void) × (nonempty)`, so `X` is inhabited iff it is empty. No set
model has such a type, so no data model can be faithful to `Q`, and `Delta : Q(Unit, B0) → Void`,
which the checker accepts, cannot be a member of its type in any model. A closed proof of `False`
follows without running the loop: `Lem` takes the diagonal function as an argument (its body runs
at an unknown `g`, so the self-application is a stuck call), and `Boom := Lem(Delta)` is a proof,
so the checker never runs `Lem`'s body at `Delta` (`Delta(ι(Delta))` itself is `undecided`: it
diverges).

The program is hole-free and every declaration is accepted after the library at the default fuel
(`#guard` below, natively: the kernel cannot run `checkProgram`), so it refutes
`Ochr.Consistency.consistency` as stated.
-/

open Ochr Ochr.Test Ochr.Surface Ochr.Consistency

namespace Ochr.Meaning.DataModel.Exists.ConsistencyCE

ochr Curry {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def FB (X : Type) (b : Bit) : Type := (match b { B1 => (Π(x : X). Void), B0 => Unit })
  reject inductive Q (A : Type) (b : Bit) := MkQ(y : FB(A, b), z : OptB(Q(Q(A, b), B1), b))
  reject def Delta (x : Q(Unit, B0)) : Void := (
    match x {
      MkQ(y, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQ(f, z2) => f(MkQ[Unit, B0](y, SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  reject def Lem (g : Π(x : Q(Unit, B0)). Void) : False :=
    VF(g(MkQ[Unit, B0]((), SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](g, NoneB[Q(Q(Q(Unit, B0), B1), B1), B1](()))))))
  reject def Boom : False := Lem(Delta)
}

/-- The user's declarations (after the library). -/
def q : Program := Curry.decls

-- the hypotheses of `Ochr.Consistency.consistency` hold of `q` (no holes; every declaration of
-- `Prelude.decls ++ q` accepted at fuel 2000000), and `q` has a parameterless definition of type
-- `False`
#guard !q.any (·.hasHole)
-- rejected since main's D107: the declaration of `Q` fails the nesting condition
#guard !accepts {} 2000000 (Prelude.decls ++ q)
#guard q.any fun d => d.ind?.isNone && d.params.isEmpty && d.name == "Boom" &&
  (match d.ret.unloc with | .ident "False" => true | _ => false)

end Ochr.Meaning.DataModel.Exists.ConsistencyCE
