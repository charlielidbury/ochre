#!/usr/bin/env python3
"""Migrate the pre-dot Σ spelling: `Σ (x : A) → B` becomes `Σ (x : A). B`.

Kept in-tree for branches written before the dot became the ONLY Σ spelling —
`Σ (x : A) → B` no longer parses, so such a branch fails at merge with a parse
error. Run this over its new files:

    python3 dllbc/scripts/sigmadot.py --apply path/to/New.lean
    python3 dllbc/scripts/sigmadot.py path/to/New.lean       # dry run, lists hits

Do NOT hand-write the regex instead. A Σ domain routinely contains parentheses of
its own (`Σ (Hsp : SplitAL %pS k %mS (*%tS))`), so a non-nesting character class
stops at the first `)` and silently under-matches — on the original migration it
found 182 of 267 sites. This scans for a Σ/Σ0 head, walks the binder's parens to
their MATCHING close, then rewrites the `→` that follows and only that one. Π
arrows, `~>`, `->` and every other `→` are left alone by construction.

Line structure is preserved. Where the arrow opened a continuation line — the
corpus's tower style — the break and its indentation stay and the arrow is
dropped, so a tower stays a tower with the dot closing each line rather than
collapsing into one very long one.
"""
import sys, re

ARROW = "→"
SIG = "Σ"

def rewrite(text):
    out = []
    i = 0
    n = len(text)
    hits = []
    while i < n:
        if text[i] == SIG:
            j = i + 1
            head = SIG
            if j < n and text[j] == "0":
                head += "0"
                j += 1
            # whitespace then '('
            k = j
            while k < n and text[k] in " \t":
                k += 1
            if k < n and text[k] == "(":
                depth = 0
                m = k
                while m < n:
                    if text[m] == "(":
                        depth += 1
                    elif text[m] == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    m += 1
                if m < n and depth == 0:
                    # m is index of the matching ')'
                    p = m + 1
                    while p < n and text[p] in " \t\n\r":
                        p += 1
                    if p < n and text[p] == ARROW:
                        hits.append(text[i:p + 1].replace("\n", "\\n"))
                        gap = text[m + 1:p]
                        out.append(text[i:m + 1])
                        out.append(".")
                        i = p + 1
                        if "\n" in gap:
                            # Leading-arrow continuation style: the arrow opened
                            # its own line. Keep the line break and indentation,
                            # drop the arrow and the single space it carried, so
                            # the tower stays a tower instead of collapsing into
                            # one very long line.
                            out.append(gap)
                            if i < n and text[i] == " ":
                                i += 1
                        continue
        out.append(text[i])
        i += 1
    return "".join(out), hits

if __name__ == "__main__":
    apply = "--apply" in sys.argv
    files = [a for a in sys.argv[1:] if not a.startswith("--")]
    total = 0
    for f in files:
        src = open(f, encoding="utf-8").read()
        new, hits = rewrite(src)
        if hits:
            total += len(hits)
            print(f"{f}: {len(hits)}")
            for h in hits:
                print(f"    {h}")
            if apply:
                open(f, "w", encoding="utf-8").write(new)
    print(f"TOTAL {total}")
