# Compilation Examples

This directory contains examples that demonstrate the compilation process of lambda calculus terms in the type system.
Still somewhat in todo.

## Key Examples

- **div-by-fact.el**: Example of division by factorial - showcases compilation of arithmetic operations
- **int.el**: Some example with integers

## Compilation Process

The compilation process in this system:

1. Transforms lambda calculus terms into a list proof obligations
2. Can raise an error for unsopported terms/ill-formed terms

## Usage

These examples can be loaded and executed to understand how the compilation mechanism works. You can also use them as templates for creating your own compilable terms in the system.

To work with these examples:
1. Open the desired example file
2. Use `proof-mode-compile` (C-c S) on a compilable term
3. Examine the generated proof obligations in the resulting buffer
4. Prove them using the interactive proof system