#!/usr/bin/env bash
# make-sandbox.sh DEST: build the directory an assessed agent works in.
#
# DEST gets this package (minus maint/ and the maintainer NOTES.md), the grader's pristine copies (.grader/), and the
# offline docs (docs/): the Verus guide with its code samples inlined, and the vstd
# source. Nothing else from this repository and nothing from Verus's examples/ directory
# (which has a hash table and a merge sort). The toolchain is the flake; its inputs must
# already be in the nix store, since the agent has no network.
#
# `make-sandbox.sh --check DEST` re-runs only the exclusion check on an existing DEST.
set -euo pipefail

NAME=quicksort
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

check() {
  local d="$1" bad=0
  # Only the expected top-level entries (a solver's target/ is allowed).
  for f in "$d"/* "$d"/.[!.]*; do
    [ -e "$f" ] || continue
    case "$(basename "$f")" in
      ASSIGNMENT.md|SOLUTION_FILES|flake.nix|flake.lock|grade.sh|.gitignore|src|docs|.grader|target) ;;
      *) echo "exclusion: unexpected entry $(basename "$f")"; bad=1 ;;
    esac
  done
  # No known solution or other repo material: Ochr case studies and paper, competitors/,
  # the benchmark's references, Aeneas's hashmap, Verus's hashmap and sorting examples.
  local hits
  hits="$(grep -rIlE --exclude-dir=vstd 'cuckoo|hash_?table|merge_?sort|quick_?sort|insertion_?sort|bubble_?sort|17HashMap|16Arrays|competitors/|_reference/|ochr/core' "$d" \
    | grep -vE "^$d/(ASSIGNMENT\.md|SOLUTION_FILES|grade\.sh|src/[a-z]+\.rs|\.grader/skeleton/[a-z]+\.rs)$" || true)"
  if [ -n "$hits" ]; then echo "exclusion: matches in"; echo "$hits"; bad=1; fi
  # docs/vstd is the library itself: it must be the pinned vstd, unmodified.
  if ! diff -rq "$vsrc/source/vstd" "$d/docs/vstd" >/dev/null; then
    echo "exclusion: docs/vstd differs from the pinned vstd source"; bad=1
  fi
  if find "$d" \( -name '*.lean' -o -name '*.typ' -o -name '*.pdf' -o -name 'SPEC.md' -o -name 'tests.json' \) | grep -q .; then
    echo "exclusion: Lean/paper/spec files present"; bad=1
  fi
  local docs_rs
  docs_rs="$(cd "$d/docs" && find . -name '*.rs' | grep -v '^\./vstd/' || true)"
  if [ -n "$docs_rs" ]; then echo "exclusion: Rust files in docs outside vstd:"; echo "$docs_rs"; bad=1; fi
  [ $bad -eq 0 ] && echo "exclusion check: OK ($d)"
  return $bad
}

vsrc="$(nix build --no-link --print-out-paths "path:$here#verusSrc")"
if [ "${1:-}" = "--check" ]; then check "${2:?usage: make-sandbox.sh --check DEST}"; exit; fi
dest="${1:?usage: make-sandbox.sh DEST}"
[ -e "$dest" ] && { echo "make-sandbox.sh: $dest already exists"; exit 2; }
mkdir -p "$dest/src" "$dest/.grader/skeleton" "$dest/docs"
dest="$(cd "$dest" && pwd)"

cp "$here/ASSIGNMENT.md" "$here/SOLUTION_FILES" "$here/flake.nix" "$here/flake.lock" "$here/grade.sh" "$here/.gitignore" "$dest/"
cp "$here/src/$NAME.rs" "$dest/src/"
cp "$here/src/$NAME.rs" "$dest/.grader/skeleton/"
cp "$here/../../common/check_fixed.py" "$dest/.grader/"

python3 "$here/maint/expand_guide.py" "$vsrc" "$dest/docs/verus-guide"
cp -r "$vsrc/source/vstd" "$dest/docs/vstd"
chmod -R u+w "$dest"
cat > "$dest/docs/README.md" <<'EOF'
# Offline documentation

- `verus-guide/`: the Verus guide ("Verus Tutorial and Reference") at the pinned release,
  as markdown. Start from `verus-guide/SUMMARY.md`. Code samples that the online guide
  pulls in from example files are inlined.
- `vstd/`: the source of `vstd`, Verus's standard library (specs and lemmas for `Seq`,
  `Multiset`, `Map`, `Vec`, slices, arithmetic, ...). `vstd/std_specs/` holds the specs
  Verus assumes for Rust's standard library.
EOF

check "$dest"
echo "sandbox ready: $dest (run ./grade.sh there)"
