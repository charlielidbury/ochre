# Notation Conventions

## Derivation Trees

Standard notation places premises above and conclusion below:

```
A   B
-----
  C
```

We invert this, using indentation — conclusion first, then premises indented below:

```
C
  A
  B
```

Benefits:
1. Leaves space for comments after each line
2. Reads top-down like code
3. Scales better for large trees (deep nesting stays readable)

Nested example — standard:

```
    D
    -
E   A   B
---------
    C
```

Becomes:

```
C
  E
  A
    D
  B
```

## Comments

Comments use `//` and go immediately after the line with a single space —
never column-aligned with whitespace padding:

```
C // some comment
  A // another comment
  B
```

## Inference Rule Definitions

Use the same indented format for defining rules (not horizontal lines):

```
[RuleName]
conclusion
  premise1
  premise2
```
