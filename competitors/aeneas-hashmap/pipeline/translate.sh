#!/usr/bin/env bash
# Translate both hashmap variants through the real Aeneas toolchain.
#
#   ./translate.sh [OUTDIR]     (default: ./out)
#
# Builds Charon and Aeneas from the pinned revisions below with nix, runs
# Charon (Rust -> LLBC) and then Aeneas (LLBC -> Lean and Rocq) on
# `../current/hashmap.rs` and `../splice/hashmap.rs`, and diffs the results.
#
# The pinned revisions are the ones this was verified against on 2026-08-20.
# CHARON_REV is the revision Aeneas itself pins in its flake.lock, NOT Charon's
# main: main was 0.1.237 at the time and Aeneas wants 0.1.236, and Aeneas
# rejects an LLBC file whose format it does not expect. If you re-pin Aeneas,
# re-read its flake.lock and re-pin Charon to match.
#
# Neither flake advertises a binary cache, so the first run compiles a rustc
# driver from source and takes a while.

set -euo pipefail

CHARON_REV=f5a61c8f2cb695213b427ab696f8088f357b5dea   # charon 0.1.236
AENEAS_REF=github:AeneasVerif/aeneas                  # aeneas 937ff0d

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
out=$(cd "$(dirname "${1:-$here/out}")" 2>/dev/null && pwd)/$(basename "${1:-out}")
mkdir -p "$out"

echo "==> building charon $CHARON_REV"
nix build "github:aeneasverif/charon/$CHARON_REV" -o "$out/charon"
echo "==> building aeneas"
nix build "$AENEAS_REF" -o "$out/aeneas"

charon="$out/charon/bin/charon"
aeneas="$out/aeneas/bin/aeneas"
"$charon" version
"$aeneas" -version

for variant in baseline splice; do
  case $variant in
    baseline) src="$here/../current/hashmap.rs" ;;
    splice)   src="$here/../splice/hashmap.rs" ;;
  esac

  echo "==> charon: $variant"
  # --preset=aeneas is required; without it Aeneas refuses the file. Both
  # crates are named `hashmap` so the generated definitions line up for a diff.
  "$charon" rustc --preset=aeneas --dest-file "$out/hashmap_$variant.llbc" \
    -- --edition 2021 --crate-type=rlib --crate-name hashmap "$src"
  "$charon" pretty-print "$out/hashmap_$variant.llbc" > "$out/$variant.llbc.txt"

  echo "==> aeneas: $variant"
  # -split-files -loops-to-rec are the arguments the vendored file's own `//@`
  # header asks for.
  "$aeneas" -backend lean -split-files -loops-to-rec \
    -dest "$out/lean/$variant" "$out/hashmap_$variant.llbc"
  "$aeneas" -backend rocq -split-files -loops-to-rec \
    -dest "$out/rocq/$variant" "$out/hashmap_$variant.llbc"
done

echo
echo "==> generated Lean, baseline vs splice (ignoring source-location comments)"
diff -u \
  <(grep -v "Source: '" "$out/lean/baseline/Funs.lean") \
  <(grep -v "Source: '" "$out/lean/splice/Funs.lean") \
  || true

echo
echo "==> generated Lean types, baseline vs splice"
diff -u \
  <(grep -v "Source: '" "$out/lean/baseline/Types.lean") \
  <(grep -v "Source: '" "$out/lean/splice/Types.lean") \
  && echo "(identical)"
