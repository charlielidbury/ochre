#!/usr/bin/env python3
"""Scan Rust sources for holes and forbidden constructs (used by grade.sh).

    grade_scan.py PROFILE FILE...

FIXED regions are skipped (the skeleton owns them). Comments, string literals
and character literals are removed first, so a word in a comment or a string is
never reported. What is left is split into
identifier tokens, and each token is looked up in the lists below. PROFILE
(`hashmap` or `quicksort`) picks the extra list for the package.

Prints one line per finding: `HOLE file:line: todo!()` or
`FORBIDDEN file:line: <token>: <reason>`. Exit status: 0 if nothing was found,
1 if only holes were found, 2 if anything forbidden was found.
"""
import re
import sys

HOLES = {"todo", "unimplemented"}

COMMON = {
    "unsafe": "unsafe code",
    "extern": "foreign code",
    "asm": "inline assembly",
    "global_asm": "inline assembly",
    "include": "including outside files",
    "include_str": "including outside files",
    "include_bytes": "including outside files",
    "transmute": "unsafe conversion",
    "cfg": "conditional compilation",
    "cfg_attr": "conditional compilation",
    "collections": "std::collections (library maps, sets and lists)",
    "HashSet": "library set",
    "BTreeMap": "library map",
    "BTreeSet": "library set",
    "LinkedList": "library list",
    "VecDeque": "library queue",
    "BinaryHeap": "library heap",
    "Rc": "shared ownership",
    "Arc": "shared ownership",
    "Cell": "interior mutability",
    "RefCell": "interior mutability",
    "UnsafeCell": "interior mutability",
    "OnceCell": "interior mutability",
    "Mutex": "interior mutability",
    "RwLock": "interior mutability",
    "Clone": "copying (no Clone impls)",
    "clone": "copying",
    "cloned": "copying",
    "to_owned": "copying",
    "to_vec": "copying",
}

PROFILES = {
    "hashmap": {},
    "quicksort": {
        "Vec": "a heap allocation (auxiliary space must be O(1))",
        "vec": "a heap allocation (auxiliary space must be O(1))",
        "Box": "a heap allocation (auxiliary space must be O(1))",
        "String": "a heap allocation (auxiliary space must be O(1))",
        "collect": "building a collection (auxiliary space must be O(1))",
        "alloc": "a heap allocation (auxiliary space must be O(1))",
        "concat": "building a collection (auxiliary space must be O(1))",
        "join": "building a collection (auxiliary space must be O(1))",
        "copy_from_slice": "copying a range",
        "clone_from_slice": "copying a range",
        "copy_within": "copying a range",
        "swap_with_slice": "library permutation routine",
        "reverse": "library permutation routine",
        "rotate_left": "library permutation routine",
        "rotate_right": "library permutation routine",
        "sort": "library sort",
        "sort_unstable": "library sort",
        "sort_by": "library sort",
        "sort_by_key": "library sort",
        "sort_unstable_by": "library sort",
        "sort_unstable_by_key": "library sort",
        "sort_by_cached_key": "library sort",
        "sort_floats": "library sort",
        "select_nth_unstable": "library selection",
        "select_nth_unstable_by": "library selection",
        "select_nth_unstable_by_key": "library selection",
        "partition_point": "library search",
        "partition_dedup": "library partition",
        "partition_dedup_by": "library partition",
        "partition_dedup_by_key": "library partition",
        "partition_in_place": "library partition",
        "binary_search": "library search",
        "binary_search_by": "library search",
        "binary_search_by_key": "library search",
    },
}

CHAR_LIT = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.)|[^\\'\n])'")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def strip(src):
    """Replace comments and string/char literals with spaces, keeping newlines."""
    out, i, n = [], 0, len(src)

    def blank(s):
        return re.sub(r"[^\n]", " ", s)

    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(src[i:j]))
            i = j
        elif (m := re.compile(r'b?r(#*)"').match(src, i)) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")):
            close = '"' + m.group(1)
            j = src.find(close, m.end())
            j = n if j < 0 else j + len(close)
            out.append(blank(src[i:j]))
            i = j
        elif c == '"' or (c == "b" and src.startswith('b"', i) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_"))):
            j = i + (2 if c == "b" else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
        elif c == "'" and (m := CHAR_LIT.match(src, i)):
            out.append(blank(m.group(0)))
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


MARKER = re.compile(r"(?<![\w-])FIXED-(BEGIN|END)(?![\w-])")


def drop_fixed(src):
    """Blank out the FIXED regions (marker lines included): the skeleton owns them."""
    out, inside = [], False
    for line in src.splitlines(keepends=True):
        m = MARKER.search(line)
        if m or inside:
            out.append("\n" if line.endswith("\n") else "")
            if m:
                inside = m.group(1) == "BEGIN"
        else:
            out.append(line)
    return "".join(out)


def main(argv):
    if len(argv) < 2 or argv[0] not in PROFILES:
        print("usage: grade_scan.py hashmap|quicksort FILE...")
        return 2
    forbidden = dict(COMMON, **PROFILES[argv[0]])
    holes = bad = 0
    for path in argv[1:]:
        with open(path, encoding="utf-8") as f:
            text = strip(drop_fixed(f.read()))
        for lineno, line in enumerate(text.splitlines(), 1):
            for m in IDENT.finditer(line):
                tok = m.group(0)
                is_macro = line[m.end():m.end() + 1] == "!"
                if tok in HOLES and is_macro:
                    print(f"HOLE {path}:{lineno}: {tok}!()")
                    holes += 1
                elif tok in forbidden:
                    print(f"FORBIDDEN {path}:{lineno}: {tok}{'!' if is_macro else ''}: {forbidden[tok]}")
                    bad += 1
            if re.search(r"#!?\[\s*path\b", line):
                print(f"FORBIDDEN {path}:{lineno}: #[path]: including outside files")
                bad += 1
    return 2 if bad else (1 if holes else 0)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
