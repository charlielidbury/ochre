#!/usr/bin/env python3
"""Build a sandbox for one Ochr benchmark package (conditions `ochr` and `ochr-2p`).

    sandbox.py --package PKG --checker CHECKER --rules RULES.md DEST [--no-build]

PKG is the package directory (for example ochr/bench/quicksort/ochr), CHECKER the Ochr
checker's Lean project (ochr/core/lean) and RULES.md the language's rule set
(ochr/core/RULES.md). DEST must not exist, or be an empty directory.

The sandbox holds:
  - the package's own files (ASSIGNMENT.md, the skeleton, Check.lean, lakefile.lean,
    grade.sh, SOLUTION_FILES, flake.nix, ...), minus the files only the repository needs;
  - checker/: the checker's sources, the examples tour (Ochr/Examples/00*..15*), and the
    library blocks the skeleton uses (the arrays library), extracted block by block from
    the file that holds them, so that the case studies kept in the same file stay out;
  - docs/RULES.md and docs/GUIDE.md;
  - tools/: check_fixed.py, grade_ochr.py, and tools/original/, the pristine skeleton
    files that check_fixed.py compares the solution against.

Everything else in the repository is left out: the case studies (17HashMap, the Quicksort
block and ArrayBench), the paper, the notes, the ledger and registry (which import the
case studies), the fuzzer and the scratch files. After copying, every file of the sandbox
is searched for distinctive names from the case studies, and the build fails if one is
found. Unless --no-build is given, the sandbox is then built once (checker, skeleton and
the verdict driver), so that a trial starts from a warm build.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
COMMON = os.path.dirname(HERE)

# Package files that stay in the repository.
PACKAGE_EXCLUDE = {"make-sandbox.sh", "gen_tests.py", ".lake", "lake-manifest.json", "result", "__pycache__"}

# Top-level checker modules that are not part of the checker proper.
CORE_EXCLUDE = set()
# Directories of the checker that never go into a sandbox.
# (Ochr/Fuzz is the fuzzer, Scratch holds probes; neither is needed to check a program.)

# The examples tour: numbered files below this number. Numbered files from it on are case
# studies, and only the library blocks a skeleton uses are extracted from them.
TOUR_LIMIT = 16

# Distinctive names from the case studies (17HashMap, the Quicksort block, ArrayBench's
# hashmap sketch). None may appear anywhere in a sandbox.
FORBIDDEN = [
    r"\bQS\(", r"\bQSCorrect\b", r"\bQSPerm\b", r"\bQSSorted\b", r"\bQSSortedFull\b",
    r"\bPartitionPerm\b", r"\bScanPerm\b", r"\bScanLt\b", r"\bScanPivot\b", r"\bRecursePerm\b",
    r"\bRecurseSorted\b", r"\bRecWith\b", r"\bSortArray\b", r"\bSortRun\b", r"\bPartLeProof\b",
    r"\bPartLe\b", r"\bAllLeTakeOf\b", r"\bTakeOneDrop\b",
    r"\bHMSlot\b", r"\bHashMapOf\b", r"\bBInsert\b", r"\bInsertB\b", r"\bGetMutB\b",
    r"\bBGetMut\b", r"\bBGet\b", r"\bBRemove\b", r"\bBFind\b", r"\bMoveBucket\b",
    r"\bMoveSlots\b", r"\bEmptySlots\b", r"\bSlotInsertFind\b", r"\bInsertFind\b",
    r"\bBRemoveFind\b", r"\bGetMutIsInsert\b", r"\bInsertCount\b",
    r"17HashMap", r"CaseStudyLedger", r"hashmap-case-study", r"arrays-library\.md",
    r"^ochr Quicksort\b", r"^ochr ArrayBench\b", r"^ochr HashMap\b", r"^ochr HashMapLookup\b",
]


def die(msg):
    print(f"make-sandbox: {msg}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------
# Blocks in example files

BLOCK_HEAD = re.compile(r"^ochr ([A-Za-z_][A-Za-z0-9_']*)(?: uses ([^{]*))?\{", re.M)


def blocks_of(text):
    """{name: (start, end, uses)} for the `ochr NAME uses A, B { ... }` blocks of a file.
    A block runs from its header line to the next line that is exactly `}`."""
    out = {}
    lines = text.splitlines(keepends=True)
    offsets, pos = [], 0
    for line in lines:
        offsets.append(pos)
        pos += len(line)
    i = 0
    while i < len(lines):
        m = BLOCK_HEAD.match(lines[i])
        if m:
            name = m.group(1)
            uses = [u.strip() for u in (m.group(2) or "").split(",") if u.strip()]
            j = i + 1
            while j < len(lines) and lines[j].rstrip("\r\n") != "}":
                j += 1
            if j == len(lines):
                die(f"block {name} has no closing line")
            out[name] = (i, j, uses)
            i = j + 1
        else:
            i += 1
    return out, lines


def preceding_doc(lines, start):
    """The `/-! ... -/` comment directly above line `start` (blank lines allowed between),
    as (first line, last line), or None."""
    k = start - 1
    while k >= 0 and not lines[k].strip():
        k -= 1
    if k < 0 or not lines[k].rstrip().endswith("-/"):
        return None
    end = k
    while k >= 0 and not lines[k].lstrip().startswith("/-"):
        k -= 1
    if k < 0 or not lines[k].lstrip().startswith("/-!"):
        return None
    return (k, end)


def run_lines(lines, name, after):
    """The `#eval`/`#guard` lines about block `name` that follow its closing line."""
    out = []
    k = after + 1
    while k < len(lines) and (not lines[k].strip() or lines[k].startswith("#") or lines[k].startswith("--")):
        if lines[k].startswith("#") and f'"{name}"' in lines[k]:
            out.append(lines[k])
        k += 1
    return out


LIBRARY_HEADER = """/-! # 16. Arrays: a library over a type-level model

Arrays are not built into Ochr. An array of `n` elements is modelled by `Cells(E, n)`, a type
computed by recursion on the length `n`: `CellsEnd` at zero, and a `Cell` holding an element
and the rest at `Succ(m)`. So the length lives only in the type, and a value of `Cells(E, n)`
has exactly `n` elements. A view `Slice(E, n)` wraps the cells, and an owned array
`Array(E, n)` wraps a view. Proofs reason about this model directly (`Nth`, `SetS`, `TakeS`,
`DropS`, `JoinS`, `Count`, ...). Compiled code uses a flat buffer instead, through eight native
functions whose models are the Ochr bodies given here (`implemented by`): `AsSlice`, `Read`,
`Set`, `GetMut`, `WithSplit`, `ArrEmpty`, `ArrPush`, `ArrPop`.

The rules: nothing recurses over an array, only over an index; runtime code never owns part
of an array; a borrow of part of an array is scoped by a continuation (`WithSplit`).

The representation is enforced. `SliceOf` is `unsized abstract`, and `Cell`, `CellsEnd` and
`ArrayOf` are `abstract`. Outside model code (the `implemented by` bodies, and the model
functions, which take or return a view by value and so never run at runtime), runtime code
only borrows a view: it never reads, moves, assigns or matches one, and never builds or takes
apart the representation. Statements and proofs (erased code) are unrestricted.

`&E` is not yet well formed for a type variable `E`, so the one native that returns a borrow
of an element, `GetMut`, is written for `Word` elements. Reads move (D53); indices, lengths
and `Word` elements are copies.

This file holds the library blocks: `Index` (the order on `Word` and facts about it),
`Arrays` (the model and the natives) and `ArrayLemmas` (the lemma library). -/
"""


def extract_library(example_files, wanted):
    """Find the blocks in `wanted` (and every block they use, transitively, that lives in the
    same files) among the numbered example files from TOUR_LIMIT on. Return
    {module file name: text} for the files that hold them, each rewritten to hold only those
    blocks, with their doc comments and their #eval/#guard lines."""
    found = {}   # block name -> (file, start, end, uses, lines)
    for path in example_files:
        text = open(path, encoding="utf-8").read()
        bl, lines = blocks_of(text)
        for name, (s, e, uses) in bl.items():
            found[name] = (path, s, e, uses, lines)
    keep, todo = set(), list(wanted)
    while todo:
        b = todo.pop()
        if b in keep:
            continue
        if b not in found:
            continue  # a tour block (Std) or the Prelude: not in these files
        keep.add(b)
        todo.extend(found[b][3])
    missing = [w for w in wanted if w not in keep]
    if missing:
        die(f"library blocks not found in the case-study files: {', '.join(missing)}")
    out = {}
    by_file = {}
    for b in keep:
        by_file.setdefault(found[b][0], []).append(b)
    for path, names in by_file.items():
        lines = found[names[0]][4]
        imports = [l for l in lines if l.startswith("import ")]
        parts = ["".join(imports), "\n", LIBRARY_HEADER, "\nopen Ochr.Test\n"]
        for name in sorted(names, key=lambda n: found[n][1]):
            _, s, e, _, _ = found[name]
            doc = preceding_doc(lines, s)
            parts.append("\n")
            if doc:
                parts.append("".join(lines[doc[0]:doc[1] + 1]) + "\n")
            parts.append("".join(lines[s:e + 1]))
            runs = run_lines(lines, name, e)
            if runs:
                parts.append("\n" + "".join(runs))
        out[os.path.basename(path)] = "".join(parts)
    return out


# ---------------------------------------------------------------------------

def skeleton_files(pkg):
    path = os.path.join(pkg, "SOLUTION_FILES")
    if not os.path.exists(path):
        die(f"{path} is missing")
    return [l.strip() for l in open(path) if l.strip() and not l.startswith("#")]


def library_blocks_used(pkg, files):
    """Blocks that a skeleton `uses` but does not define: the library it needs."""
    defined, used = set(), set()
    for f in files:
        text = open(os.path.join(pkg, f), encoding="utf-8").read()
        for m in BLOCK_HEAD.finditer(text):
            defined.add(m.group(1))
            used.update(u.strip() for u in (m.group(2) or "").split(",") if u.strip())
    return sorted(used - defined)


def copy_checker(checker, dest, wanted):
    ex_src = os.path.join(checker, "Ochr", "Examples")
    core_dst = os.path.join(dest, "Ochr")
    ex_dst = os.path.join(core_dst, "Examples")
    os.makedirs(ex_dst)
    modules = []
    for f in sorted(os.listdir(os.path.join(checker, "Ochr"))):
        if f.endswith(".lean") and f not in CORE_EXCLUDE:
            shutil.copy2(os.path.join(checker, "Ochr", f), core_dst)
            modules.append("Ochr." + f[:-5])
    numbered = sorted(f for f in os.listdir(ex_src) if re.match(r"^\d\d.*\.lean$", f))
    tour = [f for f in numbered if int(f[:2]) < TOUR_LIMIT]
    later = [os.path.join(ex_src, f) for f in numbered if int(f[:2]) >= TOUR_LIMIT]
    for f in tour:
        shutil.copy2(os.path.join(ex_src, f), ex_dst)
    lib = extract_library(later, wanted) if wanted else {}
    for f, text in lib.items():
        with open(os.path.join(ex_dst, f), "w", encoding="utf-8") as h:
            h.write(text)
    for f in tour + sorted(lib):
        modules.append("Ochr.Examples.«" + f[:-5] + "»")
    shutil.copy2(os.path.join(checker, "lean-toolchain"), dest)
    with open(os.path.join(dest, "lakefile.lean"), "w") as h:
        h.write("import Lake\nopen Lake DSL\n\n"
                "-- The Ochr checker, as distributed with a benchmark sandbox: the checker's sources,\n"
                "-- the examples tour and the arrays library. `lake build` checks every example.\n"
                "package «ochr» where\n  leanOptions := #[\n    ⟨`autoImplicit, false⟩,\n"
                "    -- no linter warnings: the checker's own are replayed on every build\n"
                "    ⟨`linter.all, false⟩\n  ]\n\n"
                "@[default_target]\nlean_lib «Ochr» where\n  srcDir := \".\"\n")
    with open(os.path.join(dest, "Ochr.lean"), "w") as h:
        h.write("".join(f"import {m}\n" for m in modules))
    # every import of a copied file must resolve to a copied module
    have = set(modules) | {"Lean", "Lean.Elab.Command", "Lake"}
    for root, _, files in os.walk(dest):
        for f in files:
            if not f.endswith(".lean") or f == "lakefile.lean":
                continue
            for line in open(os.path.join(root, f), encoding="utf-8"):
                m = re.match(r"^import (\S+)", line)
                if m and m.group(1) not in have and not m.group(1).startswith("Lean"):
                    die(f"checker/{os.path.relpath(os.path.join(root, f), dest)} imports {m.group(1)}, which is not in the sandbox")


def scan_forbidden(dest):
    pats = [re.compile(p, re.M) for p in FORBIDDEN]
    hits = []
    for root, dirs, files in os.walk(dest):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in files:
            path = os.path.join(root, f)
            try:
                text = open(path, encoding="utf-8").read()
            except (UnicodeDecodeError, OSError):
                continue
            for p in pats:
                for m in p.finditer(text):
                    line = text.count("\n", 0, m.start()) + 1
                    hits.append(f"{os.path.relpath(path, dest)}:{line}: {p.pattern}")
    return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--package", required=True)
    ap.add_argument("--checker", required=True)
    ap.add_argument("--rules", required=True)
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("dest")
    a = ap.parse_args()

    pkg, dest = os.path.abspath(a.package), os.path.abspath(a.dest)
    if os.path.exists(dest) and os.listdir(dest):
        die(f"{dest} exists and is not empty")
    os.makedirs(dest, exist_ok=True)

    files = skeleton_files(pkg)
    for f in sorted(os.listdir(pkg)):
        if f in PACKAGE_EXCLUDE:
            continue
        src = os.path.join(pkg, f)
        if os.path.isdir(src):
            shutil.copytree(src, os.path.join(dest, f))
        else:
            shutil.copy2(src, dest)

    tools = os.path.join(dest, "tools")
    os.makedirs(os.path.join(tools, "original"))
    shutil.copy2(os.path.join(COMMON, "check_fixed.py"), tools)
    shutil.copy2(os.path.join(HERE, "grade_ochr.py"), tools)
    for f in files:
        os.makedirs(os.path.dirname(os.path.join(tools, "original", f)), exist_ok=True)
        shutil.copy2(os.path.join(pkg, f), os.path.join(tools, "original", f))

    docs = os.path.join(dest, "docs")
    os.makedirs(docs)
    shutil.copy2(a.rules, os.path.join(docs, "RULES.md"))
    shutil.copy2(os.path.join(HERE, "GUIDE.md"), os.path.join(docs, "GUIDE.md"))

    copy_checker(os.path.abspath(a.checker), os.path.join(dest, "checker"), library_blocks_used(pkg, files))

    hits = scan_forbidden(dest)
    if hits:
        print("make-sandbox: case-study material found in the sandbox:", file=sys.stderr)
        for h in hits:
            print("  " + h, file=sys.stderr)
        sys.exit(1)

    if not a.no_build:
        print(f"make-sandbox: building {dest} (checker, skeleton, verdict driver) ...", flush=True)
        r = subprocess.run(["lake", "build"], cwd=dest, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if r.returncode != 0:
            print(r.stdout[-4000:])
            die("the sandbox does not build")
    print(f"make-sandbox: ready: {dest}")


if __name__ == "__main__":
    main()
