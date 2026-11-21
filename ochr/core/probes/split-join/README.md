# A split in tail position ends with the join (D119)

- `Hunt.lean`: the hunt run before the fix, four blocks of differential twins of a match at the end of a body, each row printing its verdict and the [Join] lines of its derivation. Run with `lake env lean -DmaxErrors=100000 ../probes/split-join/Hunt.lean` from `ochr/core/lean`.
- `gen.py`: the generator of the asserted table `ReturnedBorrows.SplitJoin` / `SplitJoinInd` and of its guard's `splitJoinTable`.
