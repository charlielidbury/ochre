#!/usr/bin/env python3
"""Scan Lean sources for holes and forbidden constructs (used by grade.sh).

    grade_scan.py PROFILE FILE...

FIXED regions are skipped (the skeleton owns them). Comments and string
literals are removed first, so a word in a comment or a string is never
reported. What is left is split into identifier tokens; each
component of a dotted name (`Lean.ofReduceBool` has two) is looked up in the
lists below. PROFILE (`hashmap` or `quicksort`) picks the extra list for the
package.

Prints one line per finding: `HOLE file:line: sorry` or
`FORBIDDEN file:line: <token>: <reason>`. Exit status: 0 if nothing was found,
1 if only holes were found, 2 if anything forbidden was found.
"""
import re
import sys

HOLES = {"sorry"}

COMMON = {
    # Escape hatches: unproved facts, and code the kernel does not check.
    "admit": "an unproved goal",
    "axiom": "a new axiom",
    "opaque": "an opaque constant",
    "partial": "a partial function (opaque to proofs)",
    "native_decide": "trusting compiled code",
    "ofReduceBool": "trusting compiled code",
    "ofReduceNat": "trusting compiled code",
    "trustCompiler": "trusting compiled code",
    "implemented_by": "code that differs from its definition",
    "extern": "foreign code",
    # Metaprogramming. New syntax, notation or instances could change what a
    # FIXED statement means; running meta code could add unchecked constants.
    "macro": "new syntax",
    "macro_rules": "new syntax",
    "syntax": "new syntax",
    "elab": "a new elaborator",
    "elab_rules": "a new elaborator",
    "notation": "new notation",
    "infix": "new notation",
    "infixl": "new notation",
    "infixr": "new notation",
    "prefix": "new notation",
    "postfix": "new notation",
    "instance": "a new instance",
    "default_instance": "a new instance",
    "unif_hint": "a new unification hint",
    "export": "a new alias (it would leak into the grader's files)",
    "run_cmd": "running meta code",
    "run_elab": "running meta code",
    "run_meta": "running meta code",
    "initialize": "running code at import",
    "builtin_initialize": "running code at import",
    "addDecl": "adding a declaration from meta code",
    "addDeclCore": "adding a declaration from meta code",
    "addDeclWithoutChecking": "adding a declaration from meta code",
    "modifyEnv": "changing the environment from meta code",
    "setEnv": "changing the environment from meta code",
    "getEnv": "reading the environment from meta code",
    # Attributes that register meta code, and the meta-level types themselves.
    "command_elab": "a new elaborator",
    "term_elab": "a new elaborator",
    "builtin_command_elab": "a new elaborator",
    "builtin_term_elab": "a new elaborator",
    "builtin_tactic": "a new tactic",
    "builtin_macro": "new syntax",
    "init": "running code at import",
    "builtin_init": "running code at import",
    "env_extension": "an environment extension",
    "CommandElab": "meta code",
    "CommandElabM": "meta code",
    "TermElab": "meta code",
    "TermElabM": "meta code",
    "TacticM": "meta code",
    "MetaM": "meta code",
    "CoreM": "meta code",
    "Environment": "meta code",
    "Declaration": "meta code",
    "ConstantInfo": "meta code",
    "IO": "running code",
    "EIO": "running code",
    "BaseIO": "running code",
}

# Operations that can panic at run time (by the `!` convention). Every property
# is total, so the code must not be able to panic: use `xs[i]` with a proof,
# `xs[i]?`, `getD`, `swapIfInBounds` and the like instead.
PANICKING = {"panic", "unreachable", "assert", "get", "getElem", "head", "tail", "back", "last",
             "getLast", "pop", "max", "min", "find", "fst", "snd", "set", "swap", "modify", "insertAt",
             "eraseIdx", "extract", "toNat", "ofNat"}

COMMANDS = {
    "#eval": "running code (it can change the environment)",
    "#exit": "skipping the rest of the file",
}

PROFILES = {
    "hashmap": {
        # Library maps and sets (SPEC A3): the map is the FIXED representation.
        "Std": "the Std library's maps and sets",
        "Batteries": "the Batteries library's maps and sets",
        "DHashMap": "library map",
        "HashSet": "library set",
        "RBMap": "library map",
        "RBSet": "library set",
        "TreeMap": "library map",
        "DTreeMap": "library map",
        "TreeSet": "library set",
        "AssocList": "library association list",
        "PersistentHashMap": "library map",
        "AList": "library association list",
        "Finmap": "library map",
    },
    "quicksort": {
        "qsort": "library sort",
        "qsortOrd": "library sort",
        "insertionSort": "library sort",
        "mergeSort": "library sort",
        "heapSort": "library sort",
        "sort": "library sort",
        "sortDedup": "library sort",
        "orderedInsert": "library sort",
        "binInsert": "library sort",
        "binInsertM": "library sort",
    },
}

# `set_option NAME` is allowed only for these options (or under these prefixes).
OPTIONS_ALLOWED = ("maxHeartbeats", "maxRecDepth", "synthInstance.", "linter.", "pp.", "trace.",
                   "profiler", "diagnostics", "exponentiation.", "autoImplicit", "relaxedAutoImplicit")

IDENT = re.compile(r"#?[A-Za-z_À-ɏͰ-Ͽἀ-῿][A-Za-z0-9_'!?.À-ɏͰ-Ͽἀ-῿₀-ₜ]*")


def strip(src):
    """Replace comments and string literals with spaces, keeping newlines."""
    out, i, n = [], 0, len(src)

    def blank(s):
        return re.sub(r"[^\n]", " ", s)

    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(src[i:j]))
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
        else:
            out.append(src[i])
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

    def report(path, lineno, tok, why):
        nonlocal bad
        print(f"FORBIDDEN {path}:{lineno}: {tok}: {why}")
        bad += 1

    for path in argv[1:]:
        with open(path, encoding="utf-8") as f:
            text = strip(drop_fixed(f.read()))
        for lineno, line in enumerate(text.splitlines(), 1):
            for m in IDENT.finditer(line):
                tok = m.group(0)
                if tok.startswith("#"):
                    if tok in COMMANDS:
                        report(path, lineno, tok, COMMANDS[tok])
                    continue
                if tok.startswith("Lean.HashMap"):
                    report(path, lineno, tok, "library map")
                for part in tok.rstrip(".").split("."):
                    if part.endswith("!") and part[:-1] in PANICKING:
                        report(path, lineno, tok, "can panic (every operation must be total)")
                    part = part.rstrip("!?")
                    if part in HOLES:
                        print(f"HOLE {path}:{lineno}: sorry")
                        holes += 1
                    elif part in forbidden:
                        report(path, lineno, tok, forbidden[part])
                    elif "unsafe" in part.lower():
                        report(path, lineno, tok, "unsafe code")
            if re.search(r"\]\s*!", line):
                report(path, lineno, "xs[i]!", "can panic (every operation must be total)")
            if re.search(r"(^|[^\w])decide\s*\+\s*native", line):
                report(path, lineno, "decide +native", "trusting compiled code")
            for m in re.finditer(r"\bset_option\s+([\w.]+)", line):
                if not m.group(1).startswith(OPTIONS_ALLOWED):
                    report(path, lineno, f"set_option {m.group(1)}",
                           "only " + ", ".join(OPTIONS_ALLOWED) + " may be set")
    return 2 if bad else (1 if holes else 0)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
