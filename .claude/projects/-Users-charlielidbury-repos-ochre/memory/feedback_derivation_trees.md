---
name: Indented derivation tree notation
description: Use indented top-down derivation trees instead of standard bottom-up notation. Conclusion first, premises indented below.
type: feedback
---

Use indented derivation tree format: conclusion on top, premises indented below (not the standard premises-above-line-below format).

**Why:** Standard notation gets messy with large trees. Indented format leaves space for inline comments, reads like code, and scales better.

**How to apply:** In all proof/derivation work in this project, write trees as:
```
C
  A
  B
```
not:
```
A   B
-----
  C
```

Full conventions documented in docs/notation.md.
