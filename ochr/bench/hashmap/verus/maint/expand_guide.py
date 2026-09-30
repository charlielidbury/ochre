#!/usr/bin/env python3
"""Build the offline Verus guide for a sandbox.

Usage: expand_guide.py VERUS_SRC DEST

VERUS_SRC is the pinned Verus source tree (the flake's `verusSrc` output). The guide's
markdown lives in source/docs/guide/src and pulls its code samples out of
examples/guide/*.rs with mdbook `{{#include path[:anchor|:from:to]}}` directives. This
script inlines every directive, so DEST holds self-contained markdown and no copy of the
examples directory is needed (Verus's examples/ includes a hash table and a merge sort,
which the sandbox must not contain).
"""
import pathlib
import re
import shutil
import sys

INCLUDE = re.compile(r"\{\{#include\s+([^}\s]+)\s*\}\}")
ANCHOR_LINE = re.compile(r"ANCHOR(_END)?:\s*\w+")


def read_include(base, spec):
    path, _, sel = spec.partition(":")
    target = (base / path).resolve()
    if not target.is_file():  # likewise a few dangling file includes
        return f"// (file `{path}` is missing upstream)"
    lines = target.read_text().splitlines()
    if sel == "":
        chosen = lines
    elif re.fullmatch(r"\d*:?\d*", sel):
        lo, _, hi = sel.partition(":")
        if ":" not in sel:  # `file:N` is line N to the end
            hi = ""
        chosen = lines[(int(lo) - 1 if lo else 0) : (int(hi) if hi else None)]
    else:
        start = [i for i, l in enumerate(lines) if re.search(rf"ANCHOR:\s*{re.escape(sel)}\b", l)]
        end = [i for i, l in enumerate(lines) if re.search(rf"ANCHOR_END:\s*{re.escape(sel)}\b", l)]
        if not start or not end:  # upstream has a few dangling anchors; mdbook only warns
            return f"// (snippet `{sel}` is missing upstream)"
        chosen = lines[start[0] + 1 : end[0]]
    # mdbook drops every anchor marker line from included text
    chosen = [l for l in chosen if not ANCHOR_LINE.search(l)]
    text = "\n".join(chosen)
    if target.suffix == ".md":
        text = expand(target.parent, text)
    return text


def expand(base, text):
    return INCLUDE.sub(lambda m: read_include(base, m.group(1)), text)


def main():
    src, dest = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    guide = src / "source" / "docs" / "guide" / "src"
    dest.mkdir(parents=True, exist_ok=True)
    for md in sorted(guide.glob("*.md")):
        (dest / md.name).write_text(expand(guide, md.read_text()))
    if (guide / "graphics").is_dir():
        shutil.copytree(guide / "graphics", dest / "graphics", dirs_exist_ok=True)
    left = [p.name for p in dest.glob("*.md") if "{{#include" in p.read_text()]
    if left:
        raise SystemExit(f"unexpanded includes remain in {left}")


if __name__ == "__main__":
    main()
