# Interactive Components

This directory contains modules that handle user interaction with the proof system, providing a rich UI for proof development and automation.

## Components

- **action-command.el**: Core operations for performing actions on terms (beta substitution, macro expansion, etc.)
- **all-binds.el**: Keybindings for all interactive features and commands
- **helper-command.el**: Utility commands that assist with proof development but don't affect proofs directly
- **logging.el**: Functions for logging proof steps and maintaining proof history
- **proof-mode-command.el**: The main proof mode interface with commands for starting/managing proofs

## Key Features

- Interactive proof development environment with buffer management
- Command system for term manipulation and reduction
- Proof logging and replay functionality
- Multi-window interface for simultaneous term/goal viewing

## Keyboard Shortcuts

See `all-binds.el` for the same list of keybindings.

### Action Commands
- `C-c b`: Beta substitution
- `C-c B`: Beta substitute all
- `C-c e`: Macro expand
- `C-c E`: Macro collapse
- `C-c p`: Promote term
- `C-c o`: Split or all
- `C-c C-o 0`: Objective or split (0)
- `C-c C-o 1`: Objective or split (1)

### Proof Mode Commands
- `C-c s`: Start a subtyping proof
- `C-c m`: Commit temporary proof
- `C-c q`: QED and close proof
- `C-c r`: Replay proof
- `C-c S`: Compile proof

### Helper Commands
- `C-c c`: Copy super sexp at point