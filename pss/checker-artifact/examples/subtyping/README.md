# Subtyping Examples

This directory contains examples demonstrating some subtyping relations.

## Key Examples

- **int.el**: Examples of integer-related subtyping properties, including:
  - Basic integer subtyping (1 ≤ int)
  - Successor type operations ([1, +inf[ + [1, +inf[ ≤ [1, +inf[)
  - Factorial function typing (factorial returns a successor)
  - Syracuse function typing (always returns 1)

## Subdirectories

- **proofs/**: Contains the proof traces for the examples:
  - `leq-1-int.txt`: Proof that 1 is a subtype of int
  - `plus-succint-succint-leq-succint.txt`: Proof of successor type addition
  - `leq-fact-succint.int`: Proof of factorial function typing
  - `syracuse-leq-1.txt`: Proof that Syracuse function returns 1


## Usage

To study these examples:

1. Open an example file (like `int.el`)
2. Position cursor on a subtyping proposition (`<=p` form)
3. Use `proof-mode-start-subtype-proof` (C-c s) to start an interactive proof
4. Do the proof

## Proof Structure

Each proof file contains a detailed trace of the subtyping proof, showing:
- Initial subtyping proposition
- Step-by-step transformations