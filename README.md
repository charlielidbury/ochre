# Ochre
_A systems theorem prover_

Watch this space.

## Building

This repo is built with [Nix](https://nixos.org) (flakes enabled).

```bash
# Build the Rust compiler
nix build .#compiler

# Build / type-check the Och Lean formalisation
nix build .#och-lean

# Build everything and run checks
nix flake check
```

## Development

Drop into a shell with every toolchain pinned (Rust nightly, Lean 4
matching `lean/lean-toolchain`, Agda + stdlib, OCaml/dune):

```bash
nix develop
```

Inside the shell the usual tools work directly:

```bash
cd lean && lake build       # Lean
cd compiler && cargo build  # Rust
```

If you don't have flakes enabled, add
`--extra-experimental-features 'nix-command flakes'` to each `nix` invocation.
