import Dllbc.Uni

open Lean

namespace Dllbc

/-! # `dllbc{ … }` — the one surface (§8)

A program is a term, so its surface is the term surface: `ublk` in RUNTIME mode.
There is no declaration form to write and nothing for this macro to assemble —
which is the point.

**One macro, because there is one thing to write.** This replaces four spellings
that had all become the same thing:

| was | now |
|---|---|
| `dllbc{ … }` over the old `dllb` grammar | `dllbc{ … }` over `ublk` |
| `dllbcWith [x, y] { … }` | `dllbc [x, y] { … }` |
| `prog{ … }` | `dllbc{ … }` |
| `progWith [f] { … }` | `dllbc [f] from 900 { … }` |

The old `dllb`/`dlle` grammar was the runtime-only ancestor of `ublk`; `ublk`
spans both fragments under the `isTy` flag and produces byte-identical `Term`s on
the runtime subset, so the older grammar had nothing left to say. `pure{ … }` is
this same grammar with `isTy := true` — a `let` there is a β-redex rather than a
slot — and stays a separate spelling only because the arrow it elaborates under
is the other one.

## Pre-bound names, and why the base is sometimes written

`dllbc [x, y] { … }` binds the listed names to runtime ids `0, 1, …` before the
block starts, for programs that reference slots seeded directly into Ω (symbolic
entries have no surface syntax, so a test seeds them and names them here). Fresh
binders mint ids from `n` onward and never collide.

`from k` moves that base. Its one client is a hand-written caller for a program
`FnMacro.progOf` assembled: `progOf` binds its callees at `progBase` (900) to
stay clear of the ids the assembled bodies already carry, and a caller that wants
to call one has to agree with it. The base is written at the call site rather
than inferred because the two conventions answer to different things — a seeded Ω
on one side, `progBase` on the other — and a surface that silently picked one
would be wrong half the time.
-/

syntax "dllbc{" ublk "}" : term
syntax "dllbc" "[" ident,* "]" ("from" num)? "{" ublk "}" : term

macro_rules
  | `(dllbc{ $b:ublk }) => do
    let (t, _) ← Dllbc.DeclMacro.elabUBlk false [] [] 0 b
    pure t
  | `(dllbc [ $xs,* ] $[from $base]? { $b:ublk }) => do
    let k := (base.map (·.getNat)).getD 0
    let rctx := xs.getElems.toList.enum.map (fun p => (p.2.getId.toString, k + p.1))
    let (t, _) ← Dllbc.DeclMacro.elabUBlk false rctx [] (k + xs.getElems.size) b
    pure t

end Dllbc
