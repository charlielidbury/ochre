# Source Code

This directory contains the core implementation of the lambda calculus type system and proof environment. The code is organized into modules that handle different aspects of the system.

## Core Modules

- **compile.el**: Compiles a term and generate the related proof obligations
- **reduction.el**: Term reduction operations (beta reduction)
- **subtype.el**: Subtyping operations
- **macroexpand.el**: Support for term macros and definitions
- **or-split.el**: Handling of union types and splitting operations
- **path-management.el**: Utilities for navigating S-expression paths
- **refl.el**: Reflexivity/Alpha-equivalence operations
- **replay.el**: Replay system for proof scripts

## Subdirectories

- **algorithms/**: Automatic algorithms for proof automation (still in todo)
- **interactive/**: Uses all the functions of the core module to create the interactive system used by the programmer

## Usage

Most functionality is accessed through the interactive commands defined in the `interactive` directory.
See the keybindings defined in `interactive/README.md` for available commands.