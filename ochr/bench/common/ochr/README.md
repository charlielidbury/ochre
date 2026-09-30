# Shared tooling for the Ochr packages

Used by `hashmap/ochr`, `hashmap/ochr-2p`, `quicksort/ochr` and `quicksort/ochr-2p`.

- `sandbox.py`: what each package's `make-sandbox.sh` runs. It copies the package, the checker (`ochr/core/lean`: its sources, the examples tour `00`–`15`, and the arrays library blocks `Index`, `Arrays`, `ArrayLemmas` extracted from `16Arrays.lean` without the case studies), `RULES.md`, `GUIDE.md` and the grader's tools into a fresh directory, searches it for case-study names, and builds it once. Everything comes from a git commit (`--rev`, default `HEAD`, recorded in the sandbox's `SANDBOX_REV`), never from uncommitted edits in the shared checkout; `--worktree` takes the working files instead, for development.
- `grade_ochr.py`: the grader, run by each package's `grade.sh` inside a sandbox (FIXED regions, the forbidden constructs outside them, the build, and the checker's verdict on every declaration).
- `GUIDE.md`: the language guide every Ochr sandbox gets as `docs/GUIDE.md`.
- `gen_tests.py SKELETON [--check]`: transcribes `../tests.json` into a skeleton's generated tests (`--check` verifies them).
- `gen_hashmap_2p.py [--check]` and `hashmap_compose.py`: build `hashmap/ochr-2p/HashMap.lean` from `hashmap/ochr/HashMap.lean`, so that the representation, signatures, statements of H1–H18 and tests are byte-identical in the two conditions, and add the model, the agreement and the generic lemmas (`HashMapCompose`) that derive H4–H15 from them.

After changing a `hashmap/ochr` skeleton or a `tests.json`, run `gen_tests.py` on each skeleton and then `gen_hashmap_2p.py`. `quicksort/ochr-2p/Quicksort.lean` shares its header and tests with `quicksort/ochr/Quicksort.lean` by hand; `gen_tests.py --check` verifies the tests of both.
