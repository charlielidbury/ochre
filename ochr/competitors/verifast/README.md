# The AddM example in separation logic (VeriFast)

`addm.c` is the motivating example from `ochr/docs/00-idea.md`, written in C and verified with VeriFast, a separation-logic checker for C whose contracts live in `/*@ ... @*/` comments. It exists to make one claim concrete: separation logic handles the example by keeping a pure specification (`plus` on a ghost type `N`) apart from the heap, and the proof of "x + 0 = x" is a proof about `N`, not about the program.

## Running

```
nix run            # verify addm.c and print the report
nix flake check    # the same, plus the counterfactual below
nix develop        # a shell with `verifast` on PATH
```

Expected report:

```
addm.c
0 errors found (12 statements verified)
Linking...
Program linked successfully.
```

## What the file shows

- **The pure spec is mandatory.** VeriFast is modular, so `addM` needs a contract before it can be called, and the only thing the contract can say is `plus(n, m)` on the ghost type `N`. There is no way to write "`addM` does whatever `addM` does".
- **Induction is on `n`, not on the heap.** The lemma `plus_zero` is the whole of AddZero. It never mentions a pointer. The C function `add_zero` only transfers it through `add`'s postcondition.
- **The frame rule is invisible.** Across the recursive call, the node `p`, its `malloc_block`, and the fact `n == S(m)` are framed off automatically. `open nat(px, n)` and `close nat(p, ...)` are the doc's `x ↦ S σ_px, px ↦ σ_px` and back.
- **"Add x 0 = x" means "represents the same n".** `add_zero`'s postcondition is `nat(result, n)`. Pointer identity `result == x` is a separate, stronger claim that `add`'s contract does not carry.

## The counterfactual

`checks.without-lemma` deletes the single call `//@ plus_zero(n);` from `add_zero` and asserts that VeriFast then rejects the file with

```
addm.c(57,14-17): Cannot prove plus(n, Z) == n
```

Nothing about the program changed. The obligation that remains is a fact about `N`.

## VeriFast

Source and manual: https://github.com/verifast/verifast

The nixpkgs package (`pkgs.verifast`, 25.08 in the pinned nixpkgs) is Linux only.
