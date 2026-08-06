import Dllbc.Uni

open Lean

namespace Dllbc

/-! ## `prog{ … }` — the program surface (§8)

    A program is a term, so its surface is the term surface: `ublk` in RUNTIME
    mode, elaborated in the empty context. There is no declaration form to write
    and nothing for this macro to assemble — which is the point, and which is why
    it is three lines. A declaration is a STATEMENT of the block (`fn`, M28 θ),
    since §8 says a declaration is a `let` and §7 says what its right-hand side is;
    so this is the whole of the language's surface, with `pure{ }` beside it.

    `pure{ … }` is the same grammar in ⇝ mode (a `let` there is a β-redex, not a
    slot); the two differ by exactly the `isTy` flag, which is this calculus's
    "one grammar, four arrows" showing up at the surface.

    **The empty context is not a limitation, and the three `…With`-style forms
    that thought it was are gone** (M28 η). Each pre-bound a list of names to ids
    some harness had seeded — at `0, 1, …` for a telescope or a hand-seeded Ω, at
    `progBase, …` for an assembled program's callee slots — and each turned out to
    be writing by hand something the calculus already does:

      * a **seeded symbolic slot** is what an opaque call returns (§6.1 hands the
        caller a fresh existential at the callee's return type), so
        `let n = anyNat()` needs no seeding;
      * a **seeded telescope parameter** is what `fn f (x : τ) …` declares, and
        `seedTelescope` puts it at exactly the id the `…With` list was reproducing;
      * a **seeded callee slot** is what `FnMacro.progOf` binds, and it RETARGETS
        the tail's `.call`s into those bindings — so a tail naming its callees as
        ordinary out-of-scope calls assembles to the same term.

    What is left is one entry point with no parameters, which is what "a program is
    an arbitrary term" should have looked like from the start. -/

syntax "prog{" ublk "}" : term

macro_rules
  | `(prog{ $b:ublk }) => do let (t, _) ← Dllbc.Surface.elabUBlk false [] [] 0 b; pure t

end Dllbc
