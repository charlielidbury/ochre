#!/usr/bin/env python3
"""Count code lines and tokens for the hashmap case study (notes/hashmap-case-study.md).

A code line is a line with something left after removing comments and whitespace.
Tokens: identifiers (letters, digits, _ and '), numbers, the common multi-character
operators as one token each, and every other non-space character as one token. The same
tokenizer is used for Ochr, F* and Rust, so the counts are comparable.

usage: hashmap-count.py LANG FILE [START-END ...]
  LANG is ochr | fstar | rust. Line ranges are 1-based and inclusive; without ranges the
  whole file is counted. For ochr, only the lines inside `ochr … { … }` blocks count (the
  Lean harness around the blocks is not Ochr code).
"""
import re
import sys

OPS = [r"==>", r"<==>", r"=>", r":=", r"->", r"<-", r"==", r"<>", r"<=", r">=", r"&&",
       r"\|\|", r"::", r"/\\", r"\\/", r"!=", r"\+\+"]
TOKEN = re.compile("|".join(OPS) + r"|[A-Za-z_][A-Za-z0-9_']*|\d+|\S")


def strip_comments(text, lang):
    """Replace comments by spaces, keeping line structure."""
    out = []
    i, n, depth = 0, len(text), 0
    if lang == "ochr":
        line_c, open_c, close_c = "--", "/-", "-/"
    elif lang == "fstar":
        line_c, open_c, close_c = "//", "(*", "*)"
    else:
        line_c, open_c, close_c = "//", "/*", "*/"
    while i < n:
        if depth == 0 and text.startswith(line_c, i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith(open_c, i) and not (lang == "fstar" and text.startswith("(*)", i)):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text.startswith(close_c, i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    lang, path, *ranges = sys.argv[1:]
    raw = open(path).read()
    lines = strip_comments(raw, lang).split("\n")
    keep = [False] * len(lines)
    if ranges:
        for r in ranges:
            a, b = (int(x) for x in r.split("-"))
            for k in range(a - 1, min(b, len(lines))):
                keep[k] = True
    else:
        keep = [True] * len(lines)
    if lang == "ochr":
        inside = False
        for k, l in enumerate(lines):
            if re.match(r"^ochr\s", l):
                inside = True
                keep[k] = False
                continue
            if inside and l.startswith("}"):
                inside = False
                keep[k] = False
                continue
            if not inside:
                keep[k] = False
    code = [l for k, l in enumerate(lines) if keep[k] and l.strip()]
    toks = sum(len(TOKEN.findall(l)) for l in code)
    print(f"{len(code)} lines, {toks} tokens")


if __name__ == "__main__":
    main()
