# An experimental interactive typechecker

This project is an interactive typechecker based on the PSS theory.
The typechecker is implemented in Emacs Lisp and provides an interactive proof system.

## Project Structure

- **src/**: Core implementation of the type system and the user UI with emacs
- **terms/**: Definition of some terms
- **examples/**: Example proofs and demonstrations

## Getting Started

First, add the following to your `.emacs` file:
```
(require 'cl-lib)
(add-to-list 'load-path "~/emacs/src/")

(load "interactive/all-binds.el")
(load "../terms/int.el")
(load "../terms/bool.el")
```

### Compiling a term

1. Open the desired example file, for instance `examples/compilation/int.el`
2. Use `proof-mode-compile` (C-c S) on a compilable term: `(<=-compile term)`
3. Examine the generated proof obligations in the resulting buffer
4. Choose a proof obligation, and follow the next section

### Proving a proof obligation

1. Open the desired example file, for instance `examples/subtyping/int.el`
2. Use `proof-mode-start-subtype-proof` (C-c s) on a proof obligation: `(<=p term-a term-b)`
3. Apply tactics using the defined keybindings (see `src/interactive/all-binds.el`)

For more details on specific components, see the README files in each subdirectory.

### Terms of our calculus

variable ::= <<any lisp symbol, not in reserved-symbols>>
reserved-symbols ::= 'OR | 'y

term ::= top | 'variable | (term term) | (FUN variable term term) | (OR term term) | (y term)