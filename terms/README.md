# Terms

This directory contains the definitions of core lambda calculus terms and type constructors used throughout the project.

## Core Components

- **bool.el**: Boolean type definitions and operations using Scott encoding
- **int.el**: Integer type definitions and arithmetic operations using Scott encoding
- **lisp.el**: List type definitions and operations using Scott encoding

## Scott Encoding

The project uses Scott encodings to represent data and operations. For example:

Scott encoding is a method for representing data types in lambda calculus. In this system:
- Each data value is represented as a function.
- This function acts as its own "case" or "match" statement. It takes one argument for each constructor of the data type.
- When this function is applied to these arguments (which are typically continuations or functions to handle each case), it selects and executes the argument corresponding to its actual constructor. If the constructor has data (like the head and tail of a cons cell, or the predecessor of a number), these are passed to the selected function.

For instance, consider booleans (as in `terms/bool.el`):
- `true` is conceptually encoded as `λt.λf. t`. It's a function that takes two arguments, a "true-case" `t` and a "false-case" `f`, and returns `t`.
- `false` is conceptually encoded as `λt.λf. f`. It's a function that takes `t` and `f`, and returns `f`.

For integers (as in `terms/int.el`):
- Each integer is represented as a function that takes two arguments:
  1. A `zero-case` function (for handling zero)
  2. A `succ-case` function (for handling successor cases)
- For example, `1` is represented as a function that applies the `succ-case` to the representation of `0`
- This encoding enables natural number arithmetic operations like addition, multiplication, and factorial, tho with a fixpoint each time
- The integer type `*int*` is however defined using a fixed-point combinator in order to capture precisly the integers, instead of capturing too many terms which doesn't the behaviors of integers (eg. we want to reject terms who aren't integers anyway and on which the addition isn't commutative)

## Usage

Terms defined here can be referenced in proofs and are accessible through the `define-term` macro system. They can be manipulated with the standard operations available in the interactive proof environment.