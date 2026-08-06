import Dllbc.Uni

open Lean

namespace Dllbc

/-! ## `prog{ … }` — THE surface (§8)

    A program is a term, so its surface is the term surface: `ublk`, elaborated in
    the empty context. There is no declaration form to write and nothing for this
    macro to assemble — which is the point, and which is why it is one line. A
    declaration is a STATEMENT of the block (`fn`, M28 θ), since §8 says a
    declaration is a `let` and §7 says what its right-hand side is.

    ## **THERE IS ONE MACRO** (M29 γ)

    There were two, `prog{ }` and `pure{ }`, and they were the same call to the
    same elaborator differing by one boolean — "is this position consumed by ⇒ or
    ⇝". That flag had two readers, `let` and `&mut`, and M29 α and β removed both:
    `let` emits one `.letIn` that the kernel reads under both arrows, and the
    borrow operation and the borrow type are spelled `&m` and `&mut`. With no
    readers the flag deleted, and with the flag gone the two macros were the same
    function of the same argument.

    **`prog{ }` is the survivor, and the choice cost churn to buy meaning.**
    Measured before deciding: 675 `pure{ }` sites against 447 `prog{ }`, so keeping
    `pure{ }` would have been the smaller rename by a wide margin. It is the wrong
    name for what the block now is. A `pure{ }` may contain a `fn`, an assignment,
    a borrow and a runtime match — nothing excludes them any more — so the name
    would be a claim about the contents that the grammar no longer makes, which is
    the one kind of comment this project treats as a defect. `prog{ }` is §8's own
    sentence, "**a program is an arbitrary term**", and an arbitrary term is
    exactly what this brace delimits. A proof term is one of those.

    ## What the name no longer promises, and where the promise lives instead

    Reading `prog{ … }` tells you nothing about which fragment the term is in,
    and that is correct rather than a loss: a term's fragment is not a property of
    where it was WRITTEN, it is a property of which arrow CONSUMES it. The same
    term can be both — `len *v` is a legal body and a legal type — and under two
    macros that fact was unsayable at the surface even though the kernel had
    always known it.

    The exclusions are where they were always enforced. A form with no comptime
    reading is refused by `reflectC`, whose refusal list IS this calculus's
    definition of the pure sub-grammar (§1.3): `.seal`, `.borrow`, `.assign`,
    `.seq`, `.matchE`, `.call`, `.callV`, `.lamR`. A form with no runtime reading
    is refused by `readR`: `.borrowT`, `.cmpT`. Each refusal names the form and
    gives the reason, which a mode flag could not do — it could only say that the
    brace was the other kind.

    ## The empty context is not a limitation

    The three `…With`-style forms that thought it was are gone (M28 η). Each
    pre-bound a list of names to ids some harness had seeded, and each turned out
    to be writing by hand something the calculus already does:

      * a **seeded symbolic slot** is what an opaque call returns (§6.1 hands the
        caller a fresh existential at the callee's return type), so
        `let n = anyNat()` needs no seeding;
      * a **seeded telescope parameter** is what `fn f (x : τ) …` declares, and
        `seedTelescope` puts it at exactly the id the `…With` list was reproducing;
      * a **seeded callee slot** is what a `fn` statement binds, and it RETARGETS
        the tail's `.call`s into those bindings — so a tail naming its callees as
        ordinary out-of-scope calls assembles to the same term.

    ## Authoring pure terms (what `pure{ }`'s header used to say, §15)

    The M11 wall was mis-indexed de Bruijn failing silently across ~15 binder
    contexts. The fix was not a unifier or case trees — it was *names and explicit
    structure*, elaborated to the existing de Bruijn kernel `Term` by the macro
    layer, in a resolve-or-error discipline. That is what this grammar is, and
    `StdLemmas` is written in it. Name resolution for a bare identifier `x`
    (`Surface.resolveName`):

      * a **bound** name → its de Bruijn `pvar` (index = binders since it was bound);
      * an earlier telescope parameter → its absolute runtime `var`;
      * a known **constructor** (`Z`, `S`, `Cons`, `Refl`, `unit`, …) → `ctorApp`;
      * a kernel **constant** (`Nat`, `List`, `natRec`, `j`, …) → `const`;
      * a reified-function alias (`Le`, `len`, `add`, …) → its `…FnT` Term constant;
      * anything else → the **Lean identifier** of that name, which must denote a
        `Dllbc.Term` in scope (a library definition like `swapL`); an unbound name
        is a Lean elaboration error, never a silent fallback.

    `%e` splices a Lean-level `Term` expression `e` directly (an escape hatch), and
    the recursor sugar `elim … return …` / `elim … generalizing …` (§15b, §18) is
    part of the grammar. -/

syntax "prog{" ublk "}" : term

macro_rules
  | `(prog{ $b:ublk }) => do let (t, _) ← Dllbc.Surface.elabUBlk [] [] 0 b; pure t

end Dllbc
