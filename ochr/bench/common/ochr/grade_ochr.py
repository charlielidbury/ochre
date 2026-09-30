#!/usr/bin/env python3
"""The grader for the Ochr benchmark packages (conditions `ochr` and `ochr-2p`).

    grade_ochr.py --root SANDBOX

Run by the sandbox's grade.sh. It passes (exit 0, last line `GRADE: PASS ...`) if and only if:

 1. every FIXED region of every file in SOLUTION_FILES is byte-identical to the original
    (tools/check_fixed.py against tools/original/);
 2. the code outside the FIXED regions is well formed and allowed: it sits inside the
    skeleton's editable `ochr` block, does not close that block or open a comment or string
    that runs into a FIXED region, and uses none of the forbidden constructs (the hole markers
    TODO, `?` and `sorry`; `reject`; `implemented by`, `abstract`, `unsized` and `copy` declarations; Lean
    commands, attributes or options; a new `ochr` block; declaring a built-in, library or FIXED
    name again, such as `Unit`, `Word`, `Lt` or `Sorted`); in a block whose name ends in `Model`
    (condition ochr-2p) it also has no borrows (`&`) and no assignment (`p := t`);
 3. by Lean's own parser (`lake exe check --outline`), each solution file is made of the
    skeleton's imports and the skeleton's `ochr` blocks, in order, and nothing else at Lean
    level (doc comments aside): no command, initializer, macro, elaborator, option or
    attribute can reach the checker from a solution file;
 4. the solution builds (`lake build`; since the `ochr` command checks each block when it is
    elaborated, a rejected declaration is a build error), and the checker's verdicts
    (`lake exe check --machine`) show every declaration of every block of the skeleton as
    expected: each FIXED declaration is present in its block, the FIXED `reject def`s are
    rejected, and everything else, the tests and every helper the solver added included, is
    accepted.
"""
import argparse
import os
import re
import subprocess
import sys

# ---------------------------------------------------------------------------
# A small lexer for the parts of Lean syntax the Ochr surface uses.

OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = {v: k for k, v in OPEN.items()}
IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿][A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-₉]*")


class Lex:
    """Tokens of a text, skipping comments. `state` after lexing tells whether the text ended
    inside a comment or a string."""

    def __init__(self, text, base=0):
        self.tokens = []  # (token, offset)
        self.state = None
        i, n = 0, len(text)
        depth = 0  # block comment nesting
        while i < n:
            if depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            c = text[i]
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j + 1
            elif text.startswith("/-", i):
                depth = 1
                i += 2
            elif c == '"':
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
                if j >= n:
                    self.state = "string"
                    return
                self.tokens.append(("<string>", base + i))
                i = j + 1
            elif c.isspace():
                i += 1
            elif text.startswith(":=", i):
                self.tokens.append((":=", base + i))
                i += 2
            elif text.startswith("@[", i):
                self.tokens.append(("@[", base + i))
                i += 2
            else:
                m = IDENT.match(text, i)
                if m:
                    self.tokens.append((m.group(0), base + i))
                    i = m.end()
                else:
                    self.tokens.append((c, base + i))
                    i += 1
        if depth:
            self.state = "comment"


# ---------------------------------------------------------------------------
# FIXED regions and the gaps between them

MARKER = re.compile(r"(?<![\w-])FIXED-(BEGIN|END)(?![\w-])[ \t]*([A-Za-z0-9_.:/-]*)")


def split_regions(text):
    """[(kind, id, start, end)]: alternating gaps ('gap', id of the region before it, or
    '<start>') and regions ('fixed', id), as character offsets; None if markers are broken."""
    parts, pos, open_id, open_at = [], 0, None, 0
    gap_key = "<start>"
    offset = 0
    for line in text.splitlines(keepends=True):
        m = MARKER.search(line)
        if m:
            kind, rid = m.group(1), m.group(2)
            if kind == "BEGIN" and open_id is None:
                parts.append(("gap", gap_key, pos, offset))
                open_id, open_at = rid, offset
            elif kind == "END" and open_id == rid:
                parts.append(("fixed", rid, open_at, offset + len(line)))
                pos = offset + len(line)
                gap_key, open_id = rid, None
            else:
                return None
        offset += len(line)
    if open_id is not None:
        return None
    parts.append(("gap", gap_key, pos, len(text)))
    return parts


def contexts(text, parts):
    """For each gap key: the name of the `ochr` block it sits in, or None at top level.
    And for each FIXED region: the declarations it states, as (block, name, is_reject)."""
    lex = Lex(text)
    toks = lex.tokens
    # offset -> (block, brace depth) just before that offset
    gap_ctx, decls = {}, []
    block, depth, stack = None, 0, []
    ti = 0
    bounds = [(p[2], p) for p in parts]
    for start, p in bounds:
        while ti < len(toks) and toks[ti][1] < start:
            t, _ = toks[ti]
            if t == "ochr" and depth == 0 and ti + 1 < len(toks):
                block = toks[ti + 1][0]
            if t in OPEN:
                depth += 1
            elif t in CLOSE:
                depth -= 1
                if depth == 0:
                    block = None
            ti += 1
        if p[0] == "gap":
            gap_ctx[p[1]] = block if depth >= 1 else None
    # declarations inside FIXED regions
    for kind, rid, s, e in parts:
        if kind != "fixed":
            continue
        region_toks = [(t, o) for t, o in toks if s <= o < e]
        for k, (t, o) in enumerate(region_toks):
            if t in ("def", "inductive") and k + 1 < len(region_toks):
                prev = [region_toks[j][0] for j in range(max(0, k - 3), k)]
                is_reject = "reject" in prev
                decls.append((block_at(toks, o), region_toks[k + 1][0], is_reject, rid))
    return gap_ctx, decls


def block_at(toks, offset):
    block, depth = None, 0
    for i, (t, o) in enumerate(toks):
        if o >= offset:
            break
        if t == "ochr" and depth == 0 and i + 1 < len(toks):
            block = toks[i + 1][0]
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
            if depth == 0:
                block = None
    return block if depth >= 1 else None


LEAN_COMMANDS = {"import", "open", "set_option", "macro", "macro_rules", "syntax", "elab", "elab_rules",
                 "notation", "infix", "infixl", "infixr", "prefix", "postfix", "attribute", "axiom",
                 "theorem", "lemma", "instance", "namespace", "section", "end", "variable", "universe",
                 "admit", "example", "noncomputable", "unsafe", "partial", "private",
                 "protected", "initialize", "builtin_initialize", "declare_syntax_cat"}


# Hole markers: the skeletons' `TODO` (an unbound name the checker rejects), and the checker's
# own holes `?` and `sorry`, which take the type their context requires and show its goal.
HOLES = {"TODO", "?", "sorry"}


# Names the checker knows without a declaration. A block may redeclare some of them (`Nat`,
# `Unit`), and later declarations would then mean the solver's type: a FIXED statement could
# silently change meaning, so the grader forbids it.
BUILTIN_NAMES = {"Nat", "Unit", "Z", "S", "Type", "Prop", "Eq", "Id", "J", "refl", "clone", "Pair", "Mk",
                 "True", "False", "And", "Intro", "I", "Word", "Zero", "Succ"}

# The library files a skeleton's blocks use (relative to the sandbox): their names are reserved.
LIBRARY_FILES = ["checker/Ochr/Prelude.lean", "checker/Ochr/Examples/00Std.lean",
                 "checker/Ochr/Examples/16Arrays.lean"]


def declared_names(toks):
    """(name, offset) for every name the declarations among `toks` introduce: the name after
    `def` or `inductive`, and an inductive's constructors (the identifier after its `:=` and
    after each `|`)."""
    out, depth, pending, ctors = [], 0, None, None
    for k, (t, o) in enumerate(toks):
        nxt = toks[k + 1][0] if k + 1 < len(toks) else None
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
            if ctors is not None and depth < ctors:
                ctors = None
        if t in ("def", "inductive") and nxt:
            out.append((nxt, o))
            pending, ctors = (depth if t == "inductive" else None), None
        elif t == ":=" and pending is not None and depth == pending:
            pending, ctors = None, depth
            if nxt:
                out.append((nxt, o))
        elif t == "|" and ctors is not None and depth == ctors and nxt:
            out.append((nxt, o))
    return out


def blocks_in(toks):
    """{block name: (uses, tokens of its body)} for the `ochr NAME uses A, B { … }` blocks."""
    out, i = {}, 0
    while i < len(toks):
        if toks[i][0] == "ochr" and i + 1 < len(toks):
            name, j, uses = toks[i + 1][0], i + 2, []
            while j < len(toks) and toks[j][0] != "{":
                if toks[j][0] not in ("uses", ","):
                    uses.append(toks[j][0])
                j += 1
            depth, k = 0, j
            while k < len(toks):
                depth += toks[k][0] in OPEN
                depth -= toks[k][0] in CLOSE
                if depth == 0:
                    break
                k += 1
            out[name] = (uses, toks[j + 1:k])
            i = k + 1
        else:
            i += 1
    return out


def reserved_names(root, originals):
    """Names a solution may not declare: the built-ins, the names of the library blocks the
    skeleton uses (transitively, and the Prelude), and every name the skeleton declares inside
    a FIXED region."""
    names = set(BUILTIN_NAMES)
    lib = {}
    for f in LIBRARY_FILES:
        p = os.path.join(root, f)
        if os.path.exists(p):
            lib.update(blocks_in(Lex(open(p, encoding="utf-8").read()).tokens))
    todo = ["Prelude"]
    for text in originals:
        for uses, _ in blocks_in(Lex(text).tokens).values():
            todo += uses
    seen = set()
    while todo:
        b = todo.pop()
        if b in seen or b not in lib:
            continue
        seen.add(b)
        todo += lib[b][0]
        names.update(n for n, _ in declared_names(lib[b][1]))
    for text in originals:
        parts = split_regions(text) or []
        toks = Lex(text).tokens
        for kind, _, s, e in parts:
            if kind == "fixed":
                names.update(n for n, _ in declared_names([(t, o) for t, o in toks if s <= o < e]))
    return names


def scan_gap(text, s, e, block, gap_name, problems, holes, info, reserved=frozenset()):
    """Check the code the solver wrote between two FIXED regions."""
    body = text[s:e]
    lex = Lex(body, s)
    line_of = lambda off: text.count("\n", 0, off) + 1
    if lex.state:
        problems.append(f"line {line_of(s)}: the text after FIXED region {gap_name} ends inside a {lex.state}; "
                        f"it would hide the FIXED region that follows")
    toks = lex.tokens
    for name, o in declared_names(toks):
        if name in reserved:
            problems.append(f"line {line_of(o)}: `{name}` is already a built-in, library or FIXED name; "
                            f"declaring it again is forbidden (it could change what a FIXED statement means)")
    if block is None:
        if toks:
            problems.append(f"line {line_of(toks[0][1])}: code outside the editable ochr block "
                            f"(only comments are allowed there): `{toks[0][0]}`")
        return
    stack, pending = [], []
    model = block.endswith("Model")
    for k, (t, o) in enumerate(toks):
        nxt = toks[k + 1][0] if k + 1 < len(toks) else None
        if t in OPEN:
            stack.append(t)
        elif t in CLOSE:
            if not stack or stack[-1] != CLOSE[t]:
                problems.append(f"line {line_of(o)}: unbalanced `{t}`: code between FIXED regions must be "
                                f"whole declarations, and may not close the ochr block")
                return
            stack.pop()
        if t in HOLES:
            holes.append(o)
        elif t == "reject":
            problems.append(f"line {line_of(o)}: `reject` is forbidden (a reject def counts as correct when it fails)")
        elif t in ("implemented", "abstract", "unsized"):
            problems.append(f"line {line_of(o)}: `{t}` is forbidden (no new native functions or abstract types)")
        elif t == "copy" and nxt == "inductive":
            problems.append(f"line {line_of(o)}: `copy inductive` is forbidden (it changes the cost model)")
        elif t == "ochr":
            problems.append(f"line {line_of(o)}: a new `ochr` block is forbidden; add declarations to {block}")
        elif t in LEAN_COMMANDS or t in ("#", "@["):
            problems.append(f"line {line_of(o)}: Lean command or attribute `{t}` is forbidden")
        elif t == "clone":
            info["clone"] = info.get("clone", 0) + 1
        if model:
            depth = len(stack)
            if t in ("def", "fix", "inductive"):
                pending.append(depth)
            elif t == ":=":
                if pending and pending[-1] == depth:
                    pending.pop()
                else:
                    problems.append(f"line {line_of(o)}: assignment `:=` in the pure model ({block}) is forbidden")
            elif t == "&":
                problems.append(f"line {line_of(o)}: a borrow `&` in the pure model ({block}) is forbidden")
    if stack:
        problems.append(f"line {line_of(s)}: unclosed `{stack[-1]}` in the code after FIXED region {gap_name}")


def enclosing_decl(text, offset):
    """The name of the declaration a hole belongs to: the last `def NAME` before it."""
    names = re.findall(r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)", text[:offset])
    return names[-1] if names else "?"


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--skip-build", action="store_true", help="scan only (for testing the grader)")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.chdir(root)

    files = [l.strip() for l in open("SOLUTION_FILES") if l.strip() and not l.startswith("#")]
    reasons, notes = [], []

    # 1. FIXED regions
    args = []
    for f in files:
        args += [os.path.join("tools", "original", f), f]
    r = subprocess.run([sys.executable, os.path.join("tools", "check_fixed.py")] + args,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    fixed_out = r.stdout.strip()
    print("== FIXED regions (check_fixed.py)")
    print(fixed_out)
    if r.returncode != 0:
        reasons.append("FIXED regions changed")
    line_counts = ""
    m = re.search(r"non-blank lines outside FIXED regions: skeleton (\d+), solution (\d+)", fixed_out)
    if m:
        line_counts = f"lines outside FIXED regions: skeleton {m.group(1)}, solution {m.group(2)}"

    # 2. The code outside the FIXED regions
    problems, required, hole_names, info = [], [], [], {}
    reserved = reserved_names(root, [open(os.path.join("tools", "original", f), encoding="utf-8").read() for f in files])
    for f in files:
        orig = open(os.path.join("tools", "original", f), encoding="utf-8").read()
        sol = open(f, encoding="utf-8").read()
        po, ps = split_regions(orig), split_regions(sol)
        if po is None:
            reasons.append(f"{f}: the original's FIXED markers are broken (a packaging error)")
            continue
        gap_ctx, decls = contexts(orig, po)
        required += decls
        if ps is None:
            problems.append(f"{f}: FIXED markers broken")
            continue
        holes = []
        for kind, key, s, e in ps:
            if kind != "gap":
                continue
            if key not in gap_ctx:
                problems.append(f"{f}: code after FIXED region {key}, which the original does not have")
                continue
            before = len(problems)
            scan_gap(sol, s, e, gap_ctx[key], key, problems, holes, info, reserved)
            for i in range(before, len(problems)):
                problems[i] = f"{f}: " + problems[i]
        hole_names += [enclosing_decl(sol, o) for o in holes]
    print("\n== Code outside the FIXED regions")
    if problems:
        for p in problems:
            print("  " + p)
        reasons.append(f"{len(problems)} forbidden or malformed construct(s)")
    else:
        print("  ok")
    holes_u = list(dict.fromkeys(hole_names))
    if holes_u:
        print(f"  holes (TODO) remain in: {', '.join(holes_u)}")
        reasons.append(f"holes remain in {', '.join(holes_u)}")
    if info.get("clone"):
        print(f"  note: {info['clone']} use(s) of clone(...) (allowed, but runtime code may not copy an array or a bucket)")

    if a.skip_build:
        verdict(reasons, line_counts)
        return

    # 3. The driver, then the file's structure by Lean's own parser
    print("\n== Build the verdict driver (lake build check)", flush=True)
    b = subprocess.run(["lake", "-q", "build", "check"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if b.returncode != 0:
        print(b.stdout[-3000:])
        reasons.append("the verdict driver does not build (a packaging error)")
        verdict(reasons, line_counts)
        return
    print("  ok")
    print("\n== Structure (Lean's parser: only the skeleton's imports and ochr blocks)", flush=True)
    bad_structure = []
    for f in files:
        want, got = outline(os.path.join("tools", "original", f)), outline(f)
        if want is None or got is None:
            bad_structure.append(f"{f}: the outline driver failed")
            continue
        (wi, wc, _), (gi, gc, ge) = want, got
        if gi != wi:
            bad_structure.append(f"{f}: the imports are {gi}, not the skeleton's {wi}")
        others = [(k, n, l) for k, n, l in gc if k != "Ochr.Notation.ochrProgram"]
        for k, n, l in others:
            bad_structure.append(f"{f}: line {l}: a top-level `{k.split('.')[-1]}` command; a solution file may hold only the skeleton's ochr blocks")
        blocks_w = [n for k, n, l in wc if k == "Ochr.Notation.ochrProgram"]
        blocks_g = [n for k, n, l in gc if k == "Ochr.Notation.ochrProgram"]
        if blocks_g != blocks_w:
            bad_structure.append(f"{f}: the ochr blocks are {blocks_g}, not the skeleton's {blocks_w}")
        for e in ge[:10]:
            bad_structure.append(f"{f}: parse error: {e}")
    if bad_structure:
        for l in bad_structure:
            print("  " + l)
        reasons.append("the file's structure is not the skeleton's")
        # Lean code outside the ochr blocks could run when the file is elaborated (an `#eval`,
        # an elaborator), so a file of the wrong shape is never built or elaborated
        print("\n  (not built: a file of the wrong shape is never elaborated)")
        verdict(reasons, line_counts)
        return
    print("  ok")

    # 4. Build the solution: the checker runs when each block is elaborated (a rejected
    # declaration is then a build error), and the build must succeed
    libs = [os.path.splitext(f)[0] for f in files]
    print(f"\n== Build the solution (lake build {' '.join(libs)})", flush=True)
    b = subprocess.run(["lake", "-q", "build"] + libs, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    build_errors = [l for l in b.stdout.splitlines() if l.startswith("error:") and "Lean exited" not in l
                    and "build failed" not in l and not l.startswith("error: Some required")]
    # the declarations each error is about; a rejected declaration's error is `NAME: reason`
    decl_names = set()
    for f in files:
        decl_names.update(n for n, _ in declared_names(Lex(open(f, encoding="utf-8").read()).tokens))
    about = lambda l: (re.match(r"error: [^:]+:\d+:\d+: ([^:\s]+):", l) or [None, None])[1]
    other_errors = [l for l in build_errors if about(l) not in decl_names]
    if b.returncode != 0:
        n_decl = len(build_errors) - len(other_errors)
        if n_decl:
            print(f"  {n_decl} declaration(s) rejected by the checker (listed under Verdicts)")
        for l in other_errors[:25]:
            print("  " + l[:400])
        if len(other_errors) > 25:
            print(f"  ... and {len(other_errors) - 25} more errors")
        reasons.append(f"the build reports {len(build_errors) or 'some'} error(s)")
    else:
        print("  ok")

    # 5. Every declaration's verdict, from the driver
    print("\n== Verdicts (lake exe check --machine)", flush=True)
    c = subprocess.run(["lake", "-q", "exe", "check", "--machine"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    rows = []
    for l in c.stdout.splitlines():
        if l.startswith("ROW\t"):
            _, blk, name, expect, got, msg = (l.split("\t") + [""] * 6)[:6]
            rows.append((blk, name, expect, got, msg))
    for l in c.stderr.splitlines():
        if "is missing from" in l:
            print("  " + l)
    if c.returncode != 0 or not rows:
        print((c.stdout + c.stderr)[-3000:])
        reasons.append("the verdict driver failed")
        verdict(reasons, line_counts)
        return
    by_block = {}
    for blk, name, expect, got, msg in rows:
        by_block.setdefault(blk, {})[name] = (expect, got, msg)
    req_reject = {(blk, name) for blk, name, rej, _ in required if rej}
    bad, missing = [], []
    for blk, name, rej, rid in required:
        if name not in by_block.get(blk, {}):
            missing.append(f"{blk}.{name} (FIXED region {rid})")
    n_ok = 0
    for blk, name, expect, got, msg in rows:
        want_reject = (blk, name) in req_reject
        if want_reject:
            ok = expect == "reject" and got == "rejected"
        else:
            ok = expect == "accept" and got == "accepted"
        if ok:
            n_ok += 1
        else:
            what = "rejected" if got == "rejected" else "accepted"
            should = "be rejected" if want_reject else "be accepted"
            bad.append(f"{blk}.{name}: {what}, should {should}" + (f": {msg[:300]}" if msg else ""))
    tests = [r for r in rows if r[1].startswith("Test")]
    tests_ok = sum(1 for r in tests if (r[0], r[1]) in req_reject and r[3] == "rejected" or (r[0], r[1]) not in req_reject and r[3] == "accepted")
    print(f"  {n_ok}/{len(rows)} declarations as required; tests {tests_ok}/{len(tests)}")
    bad_tests = [l for l in bad if l.split(".", 1)[1].startswith("Test")]
    bad_other = [l for l in bad if l not in bad_tests]
    for l in bad_other[:60]:
        print("  FAIL " + l)
    if len(bad_other) > 60:
        print(f"  ... and {len(bad_other) - 60} more")
    for l in bad_tests[:5]:
        print("  FAIL " + l)
    if len(bad_tests) > 5:
        print(f"  ... and {len(bad_tests) - 5} more tests fail (`lake -q exe check` shows them all)")
    for l in missing:
        print("  MISSING " + l)
    if bad:
        reasons.append(f"{len(bad)} declaration(s) not as required")
    if missing:
        reasons.append(f"{len(missing)} FIXED declaration(s) not checked")
    verdict(reasons, line_counts)


def outline(path):
    """(imports, [(command kind, block name, line)], parse errors) of a file, by Lean's parser
    (`lake exe check --outline`), or None if the driver failed."""
    r = subprocess.run(["lake", "-q", "exe", "check", "--outline", path], stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0:
        return None
    imports, cmds, errors = [], [], []
    for l in r.stdout.splitlines():
        parts = l.split("\t")
        if parts[0] == "IMPORT":
            imports.append(parts[1])
        elif parts[0] == "CMD" and len(parts) >= 4:
            if parts[1] != "Lean.Parser.Command.moduleDoc":
                cmds.append((parts[1], parts[2], parts[3]))
        elif parts[0] == "ERROR":
            errors.append(parts[1])
    return imports, cmds, errors


def verdict(reasons, line_counts):
    tail = f" ({line_counts})" if line_counts else ""
    if reasons:
        print(f"\nGRADE: FAIL: {'; '.join(reasons)}{tail}")
        sys.exit(1)
    print(f"\nGRADE: PASS{tail}")
    sys.exit(0)


if __name__ == "__main__":
    main()
