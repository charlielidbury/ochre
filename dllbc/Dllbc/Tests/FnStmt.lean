import Dllbc.Program
import Dllbc.ProgMacro

/-!
# The `fn` statement's own hazards — what the grammar can get wrong

`fn` is a statement of the one grammar (Uni.lean): §8 says a declaration is a
`let`, §7 says its right-hand side is a seal over a recursor or a runtime λ, and
`fn f (…) -> R { … } ; rest` is that `let` written where a `let` is written.

## What this file used to be, and why it is a third of its old size

It was **the sweep's safety net** (M28 θ). While `decl{ … }` still produced an
`FnDef` value, the statement form could be held to it exactly:

    prog{ fn a …; fn b …; TAIL }   ==   progOf [declA, declB] (prog{ TAIL })

as `Term`s, by `==` — literal equality, not α-equivalence, because the statement
binds its slot at `progBase + next` and `progOf` binds the `i`-th declaration at
`progBase + i`, and those agree exactly when the statements are consecutive and
start a block. Four cases covered the shapes the lowering treats differently: a
non-recursive function and a caller, `[k]` on parameter 0, `[k]` NOT on parameter
0 (the permutation case the design exists for), and a dependent return type.

**The net's job was to police a migration, and the migration is over** (M28 D9).
`decl{ }` is deleted, so there is no second construction of the same term to
compare against — `fn` is the only way to write a function, and its output is
checked by the kernel from scratch at the seal (constraint 7). Each case's
underlying claim outlived it, in the language rather than in a comparison:

  * **the permutation** is `S23Direct.setSwap` (`swap_at` calls `set_at [i]`,
    whose decreasing parameter is second) and `S23Direct.pick` (`pick` calls
    `insert_at [k]`), both `progOk`, both with a negative twin at the same
    position;
  * **the dependent return type** is every flagship in the corpus;
  * **`[k]` on parameter 0** is most of the corpus;
  * **the refusal path** is `S6Call.zeroAll` — the same `[v]` function, rejected
    on `FnMacro.fnRefusedNeedle`, on "§12 decision 8" by name, and with
    `progOk = false` to say the sentinel fires at the BINDING rather than at a
    call. `S23Direct.borrowDecrease` says it again where the flagship's own `[v]`
    class is discussed.

What is left here is the two hazards that belong to the STATEMENT rather than to
any function written with it.
-/

open Dllbc

namespace Dllbc.Tests.FnStmt

/-! ## §A. Two `fn` chains composed through a `%` splice

    Sharing a prefix is ordinary let-chain composition — a Lean function taking the
    rest of the block and splicing it — and half the corpus is written that way.
    But each chain numbers its slots from `progBase`, so NESTING two of them makes
    the inner chain shadow the outer, and left alone that is not an error:
    measured before the check existed, `withA (withB …)` ACCEPTED with both names
    resolving to whichever function landed second. `bindFn` refuses it instead. -/

def withA (rest : Term) : Term := prog{ fn a (n : Nat) -> Nat { n }; %rest }
def withB (rest : Term) : Term := prog{ fn b (n : Nat) -> Nat { n }; %rest }

-- Nested: refused, by the same needle a refused lowering uses, naming the slot
-- and the fix.
example : progRejects (withA (withB (prog{ let r = a(1); let s = b(2); () })))
  FnMacro.fnRefusedNeedle = true := by native_decide
example : progOk (withA (withB (prog{ let r = a(1); let s = b(2); () }))) = false := by
  native_decide

-- The two shapes that are FINE, so the check above is not simply banning
-- composition: one chain declaring both, and a prefix whose tail declares nothing.
example : progOk (prog{
  fn a (n : Nat) -> Nat { n };
  fn b (n : Nat) -> Nat { n };
  let r = a(1); let s = b(2); () }) = true := by native_decide
example : progOk (withA (prog{ let r = a(1); () })) = true := by native_decide

/-! ## §B. The seal is ASCRIPTION, and its one confusable neighbour (M28 ξ)

    `seal(t, T)` is spelled `(t : T)`. The parenthesised-node property that made
    the old row unmistakable for an application is unchanged — an ascription closes
    at its own paren, so `(f : T) x` is the ascribed `f` APPLIED to `x`, not an
    ascription at a function type. What the spelling adds is that §5's definition of
    a declaration — a λ with its signature ascribed — is now the grammar rather
    than a comment beside it.

    The neighbour is `&mut`. `&mut (s : τ ~> S)` is the borrow type with a snapshot
    binder; drop the `~> S` and the ascription row would take it, making
    `&mut (v : List Nat)` a borrow of a SEAL. Measured before deciding: it parsed,
    silently, and failed downstream as an unrelated unbound-identifier error. It is
    refused at elaboration instead, which is not assertable as a test (it fails the
    build by design) and so is recorded here with its message:

        &mut (v : τ) is not a borrow type — the snapshot-binder spelling is
        `&mut (v : τ ~> S)`, where `S` is what the borrow OWES back … If you meant
        a plain borrow of the type, write `&mut τ`.
-/

-- The two spellings the refusal is between, both still working.
example : progOk (prog{
  fn f (v : &mut (s : List Nat ~> List Nat)) -> Unit { *v := Nil; () };
  () }) = true := by native_decide
example : progOk (prog{
  fn f (v : &mut List Nat) -> Unit { *v := Nil; () };
  () }) = true := by native_decide

-- An ascription CLOSES at its own paren, so a following term is an application
-- argument rather than part of the ascribed type. Stated by splicing the
-- ascription in as an opaque head: if the paren did not close, the two would
-- differ.
def ascribed : Term := prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) }
example : ((prog{ let r = (λ (x : Nat). x : Π (x : Nat) → Nat) 3; () })
        == (prog{ let r = %ascribed 3; () })) = true := by native_decide

/-! ## §C. `[k]` naming a non-parameter is a LEAN error

    The one refusal that is cheap syntactically is the one the surface makes
    syntactically — the macro has to resolve `[k]` to an index anyway, so it says so
    at elaboration. Everything `fnElab` refuses is SEMANTIC (it needs the elaborated
    telescope type to see that `[v]` decreases through a borrow's payload, or that a
    scrutinee is neither `Nat` nor `List A`) and is deliberately NOT duplicated as a
    syntactic check: two implementations of one rule is one too many, and the copy
    would be the one that drifts.

    Not assertable as a test (it fails the build by design); recorded here so a
    reader knows which errors appear when. Writing
    `fn f [zzz] (n : Nat) -> Unit { () }` gives:

        fn: decreasing argument 'zzz' is not a parameter of 'f'
-/

end Dllbc.Tests.FnStmt
