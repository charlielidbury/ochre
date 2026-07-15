# Mechanized LLBC
Formalization in the Rocq proof assistant of LLBC model for the Rust programming language. The reference is the 2024 article [Sound Borrow-Checking for Rust via Symbolic Semantics](https://dl.acm.org/doi/10.1145/3674640) by Son Ho, Aymeric Fromherz and Jonathan Protzenko.

## Requirements
The development uses Rocq >= 9.0 and the library rocq-std++. You can install the dependencies using the following commands:
```
opam repo add rocq-released https://rocq-prover.github.io/opam/released
opam install . --deps-only
```
