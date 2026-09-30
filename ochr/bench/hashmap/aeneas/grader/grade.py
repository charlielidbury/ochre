#!/usr/bin/env python3
"""The grader behind ./grade.sh. Run it through grade.sh (which sets up PATH).

    grader/grade.py [SOLUTION_DIR]

SOLUTION_DIR defaults to this package. The grader never builds in SOLUTION_DIR:
it lays the solution's files (those listed in SOLUTION_FILES) over a pristine
copy of the skeleton in .grade/work, regenerates the Lean translation there from
the Rust, and checks that copy. So edits anywhere else (the lakefile, Cargo.toml,
the vendored Aeneas library, a stale generated model) cannot affect the verdict.

Exit status 0 iff every check passes. The last line printed is the verdict.
"""
import json
import os
import re
import shutil
import subprocess
import sys

GRADER = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(GRADER)
CFG = json.load(open(os.path.join(GRADER, "package.json")))
# Pristine originals: a sandbox carries them in grader/orig; in the repo the
# package itself is the original.
ORIG = os.path.join(GRADER, "orig") if os.path.isdir(os.path.join(GRADER, "orig")) else PKG
SOL = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else PKG
WORK = os.path.join(PKG, ".grade", "work")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

problems = []  # (kind, message)


def problem(kind, msg):
    problems.append((kind, msg))
    print(f"  {kind}: {msg}")


def section(title):
    print(f"== {title}")


def run(cmd, cwd, log=None, env=None):
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
    if log:
        with open(log, "w") as f:
            f.write(p.stdout)
    return p.returncode, p.stdout


def editable_files(root):
    """The solution files (the pristine SOLUTION_FILES list) that exist under root."""
    listed = [l.strip() for l in open(os.path.join(ORIG, "SOLUTION_FILES")) if l.strip()]
    return [rel for rel in listed if os.path.isfile(os.path.join(root, rel))]


# ---------------------------------------------------------------- FIXED regions
def check_fixed():
    section("FIXED regions")
    checker = next((c for c in [os.path.join(GRADER, "check_fixed.py"),
                                os.path.join(PKG, "..", "..", "common", "check_fixed.py")] if os.path.isfile(c)), None)
    if checker is None:
        problem("grader", "check_fixed.py not found")
        return None
    args = []
    for f in CFG["fixed_files"]:
        args += [os.path.join(ORIG, f), os.path.join(SOL, f)]
    code, out = run([sys.executable, checker] + args, cwd=PKG)
    counts = None
    for line in out.splitlines():
        if code == 0:
            print(f"  {line}")
            m = re.search(r"skeleton (\d+), solution (\d+)", line)
            if m:
                counts = (int(m.group(1)), int(m.group(2)))
        else:
            problem("fixed", line.replace(SOL + "/", ""))
    return counts


# ------------------------------------------------------------ the work copy
def build_work():
    section("work copy (pristine skeleton + your solution files)")
    if os.path.exists(WORK):
        shutil.rmtree(WORK)
    skip = {".lake", "target", ".grade", ".tools", ".elan", "vendor", "build", "orig", "Code"}
    def ignore(d, names):
        return [n for n in names if n in skip or n.endswith(".llbc")]
    shutil.copytree(ORIG, WORK, ignore=ignore, symlinks=True)
    for rel in editable_files(SOL):
        dst = os.path.join(WORK, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(os.path.join(SOL, rel), dst)
    # Pre-built, read-only inputs come from this package, never from the solution.
    for d in ["vendor", ".tools", ".elan"]:
        if os.path.exists(os.path.join(PKG, d)):
            os.symlink(os.path.join(PKG, d), os.path.join(WORK, d))
    os.makedirs(os.path.join(WORK, "lean", ".lake"), exist_ok=True)
    os.symlink(os.path.join(PKG, "lean", ".lake", "packages"), os.path.join(WORK, "lean", ".lake", "packages"))
    print(f"  {len(editable_files(SOL))} solution file(s) taken from {SOL}: {' '.join(editable_files(SOL))}")


# ------------------------------------------------------ forbidden constructs
def strip_rust(src):
    """Blank out comments and string literals, keeping line numbers."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
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
            out.append("\n" * src.count("\n", i, j))
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + "\n" * src.count("\n", i, j))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def strip_lean(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
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
            out.append("\n" * src.count("\n", i, j))
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + "\n" * src.count("\n", i, j))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|pub\s+fn|fn)\s+(\S+)")


def scan(files, strip, rules, holes):
    for rel in files:
        text = strip(open(os.path.join(WORK, rel)).read())
        decl = None
        for lineno, line in enumerate(text.splitlines(), 1):
            d = DECL.match(line)
            if d:
                decl = d.group(2).split("(")[0]
            for pat, why in holes:
                if re.search(pat, line):
                    problem("hole", f"{rel}:{lineno}: {why}" + (f" in {decl}" if decl else ""))
            for pat, why in rules:
                if re.search(pat, line):
                    problem("forbidden", f"{rel}:{lineno}: {why}: {line.strip()}")


def check_forbidden():
    section("holes and forbidden constructs")
    files = editable_files(WORK)
    rs = [f for f in files if f.endswith(".rs")]
    ln = [f for f in files if f.endswith(".lean")]
    scan(rs, strip_rust, [(r, w) for r, w in CFG["rust_forbidden"]], [(r, w) for r, w in CFG["rust_holes"]])
    scan(ln, strip_lean, [(r, w) for r, w in CFG["lean_forbidden"]], [(r, w) for r, w in CFG["lean_holes"]])


# ------------------------------------------------------------------- Rust
def check_rust():
    section("Rust: cargo test")
    env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(PKG, ".grade", "target"))
    code, out = run(["cargo", "test", "--offline", "--quiet", "--color", "never"], cwd=os.path.join(WORK, "rust"),
                    log=os.path.join(PKG, ".grade", "cargo.log"), env=env)
    for line in out.splitlines():
        if re.match(r"test result:|error(\[E\d+\])?:|test \S+ \.\.\. FAILED|failures:$", line):
            print(f"  {line}")
    if code != 0:
        failed = re.findall(r"^    (\S+)$", out, re.M)
        problem("tests", f"cargo test failed ({len(failed)} failing test(s): {' '.join(failed[:12])}{' ...' if len(failed) > 12 else ''}); see .grade/cargo.log")


# ------------------------------------------------------ translation + Lean
def translate():
    section("translation: charon -> aeneas -> Lean")
    code, out = run(["bash", os.path.join(WORK, "translate.sh"), WORK], cwd=WORK,
                    log=os.path.join(PKG, ".grade", "translate.log"))
    if code != 0:
        lines = [l for l in out.splitlines() if re.search(r"error|Error|panicked|external", l)] or out.splitlines()[-6:]
        for l in lines[:12]:
            print(f"  {l}")
        problem("translation", "charon/aeneas failed; see .grade/translate.log")
        return False
    print("  ok")
    return True


def lean_build():
    section("Lean: lake build")
    code, out = run(["lake", "build"], cwd=os.path.join(WORK, "lean"), log=os.path.join(PKG, ".grade", "lake.log"))
    # The holes themselves were named by the source scan; this only counts them.
    sorries = len(re.findall(r"declaration uses [`']sorry[`']", out))
    errors = re.findall(r"^error: .*$", out, re.M)
    if code != 0:
        for e in errors[:20]:
            print(f"  {e}")
        problem("lean", f"lake build failed ({len(errors)} error line(s)); see .grade/lake.log")
        return False
    print(f"  ok ({sorries} declaration(s) use sorry)")
    return True


def split_theorem(text):
    """`theorem NAME BINDERS : STMT := by` -> (NAME, BINDERS, STMT)."""
    m = re.search(r"\btheorem\s+(\S+)", text)
    body = text[m.end():]
    body = body[:body.rfind(":=")]
    depth, colon = 0, None
    for i, ch in enumerate(body):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and colon is None:
            colon = i
    return m.group(1), body[:colon].strip(), body[colon + 1:].strip()


def fixed_theorems():
    src = open(os.path.join(ORIG, CFG["properties"])).read()
    out = []
    for m in re.finditer(r"FIXED-BEGIN (\S+)\n(.*?)\n[^\n]*FIXED-END \1", src, re.S):
        if re.search(r"^theorem ", m.group(2), re.M):
            out.append(split_theorem(strip_lean(m.group(2))))
    return out


def check_statements():
    section("statements and axioms")
    thms = fixed_theorems()
    ns = CFG["namespace"]
    # Restate everything with the skeleton's own names opened, not inside the
    # namespace: a solution's declaration that shadows a name a statement uses
    # then makes the restatement ambiguous instead of silently changing it.
    lines = [f"import {CFG['lean_root']}", f"open Aeneas Aeneas.Std Result {ns}", ""]
    for name, typ in CFG.get("check_defs", {}).items():
        lines.append(f"example : {typ} := @{ns}.{name}")
    # FIXED theorems: restate each one here, where no solution code can change
    # how the statement elaborates, and check the solution's proof against it.
    for name, binders, stmt in thms:
        typ = f"∀ {binders}, {stmt}" if binders else stmt
        lines.append(f"example : {typ} := @{ns}.{name}")
    lines.append("")
    for name, _, _ in thms:
        lines.append(f"#print axioms {ns}.{name}")
    path = os.path.join(WORK, "lean", "GradeCheck.lean")
    open(path, "w").write("\n".join(lines) + "\n")
    code, out = run(["lake", "env", "lean", "GradeCheck.lean"], cwd=os.path.join(WORK, "lean"),
                    log=os.path.join(PKG, ".grade", "check.log"))
    for e in re.findall(r"^GradeCheck\.lean:\d+:\d+: error.*$", out, re.M)[:10]:
        problem("statement", e + " (a FIXED definition or statement no longer means what the skeleton says; see .grade/check.log)")
    if code != 0 and not any(k == "statement" for k, _ in problems):
        problem("statement", "checking the statements failed; see .grade/check.log")
    unproved, bad = [], 0
    for m in re.finditer(r"'(\S+)' depends on axioms: \[(.*?)\]", out, re.S):
        extra = sorted({a.strip() for a in m.group(2).split(",")} - ALLOWED_AXIOMS)
        if extra == ["sorryAx"]:
            unproved.append(m.group(1).split(".")[-1])
        elif extra:
            bad += 1
            problem("axioms", f"{m.group(1)} depends on {', '.join(extra)}")
    if unproved:
        problem("unproved", f"{len(unproved)} theorem(s) depend on sorryAx: {' '.join(unproved)}")
    print(f"  {len(thms)} FIXED theorem(s) restated; {len(unproved)} unproved; {bad} with disallowed axioms")


def main():
    print(f"grading {SOL} against {ORIG}")
    os.makedirs(os.path.join(PKG, ".grade"), exist_ok=True)
    counts = check_fixed()
    build_work()
    check_forbidden()
    check_rust()
    if translate() and lean_build():
        check_statements()
    kinds = {}
    for k, _ in problems:
        kinds[k] = kinds.get(k, 0) + 1
    size = f"solution size: {counts[1]} non-blank lines outside FIXED regions (skeleton {counts[0]})" if counts else "solution size: unknown"
    if problems:
        summary = ", ".join(f"{n} {k}" for k, n in sorted(kinds.items()))
        print(f"GRADE: FAIL ({summary}); {size}")
        return 1
    print(f"GRADE: PASS (builds, no holes or forbidden constructs, FIXED regions intact, all tests pass, every FIXED theorem proved); {size}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
