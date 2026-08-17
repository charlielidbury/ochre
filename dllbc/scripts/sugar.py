"""Migrate DLLBC surface sites to the M34 sugars.

Three rewrites, each applied to a fixpoint:

  R1  match VAR { C(a, b) => BODY }        (single arm, final expr of its block)
        ->  let C(a, b) = VAR; BODY
      Term-IDENTICAL: VAR is a plain ident so the scrutinee path is unchanged and
      every id and name is preserved.

  R2  let X = RHS; let C(a, b) = X;        (X used nowhere else in scope)
        ->  let C(a, b) = RHS;
      Same ids; the binder X becomes the minted §m.

  R2m let X = RHS; match X { …arms… }      (X used nowhere else, final expr)
        ->  match RHS { …arms… }
      The multi-arm version of R2. Same ids; X becomes §m.

  R3  let C(a, q) = RHS; let D(b, c) = q;  (q used nowhere else in scope)
        ->  let C(a, D(b, c)) = RHS;
      Same ids; the intermediate q becomes the minted §pN.
"""
import re, sys

OPEN, CLOSE = '{([', '})]'


def skip_comment(t, i):
    """If a comment starts at i, return the index just past it, else i."""
    if t.startswith('--', i):
        j = t.find('\n', i)
        return len(t) if j < 0 else j
    if t.startswith('/-', i):
        j = t.find('-/', i)
        return len(t) if j < 0 else j + 2
    return i


def comment_mask(t):
    """A per-character mask: 1 where the character is inside a comment.

    Anchors are searched with plain regexes, which do not know that
    `match p { … }` in a doc comment is prose — and prose braces do not balance.
    """
    mask = bytearray(len(t))
    i = 0
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            for k in range(i, j):
                mask[k] = 1
            i = j
        else:
            i += 1
    return mask


def match_brace(t, i):
    """t[i] is an opener; return the index of its matching closer."""
    d = 0
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            i = j
            continue
        c = t[i]
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            d -= 1
            if d == 0:
                return i
        i += 1
    raise AssertionError('unbalanced')


def block_end(t, i):
    """From i (inside a block), the index of the '}' closing the enclosing block."""
    d = 0
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            i = j
            continue
        c = t[i]
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            if d == 0:
                return i
            d -= 1
        i += 1
    return len(t)


def split_top(t, sep=','):
    """Split at depth-0 separators, ignoring comments."""
    out, d, start, i = [], 0, 0, 0
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            i = j
            continue
        c = t[i]
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            d -= 1
        elif c == sep and d == 0:
            out.append(t[start:i])
            start = i + 1
        i += 1
    out.append(t[start:])
    return out


def indent_of(t, i):
    """Indentation of the line containing i."""
    line = t[t.rfind('\n', 0, i) + 1:]
    return len(line) - len(line.lstrip())


def line_start(t, i):
    return t.rfind('\n', 0, i) + 1


def dedent_body(body, first_col, target):
    """Re-lay `body` so its shallowest line sits at column `target`.

    `first_col` is the column the body's first character occupies in the source,
    which is not its line's indentation when the body starts after `=> {`. Every
    line keeps its offset from the shallowest one, so multi-line proof terms stay
    aligned under their heads."""
    lines = body.split('\n')
    if len(lines) > 1 and not lines[0].strip():
        lines, first_col = lines[1:], None
    cols, texts = [], []
    for k, l in enumerate(lines):
        if not l.strip():
            cols.append(None)
            texts.append('')
            continue
        lead = len(l) - len(l.lstrip())
        cols.append(lead + (first_col if k == 0 and first_col is not None else 0))
        texts.append(l.strip())
    # A body that starts mid-line (right after `=> `) is not a base the rest is
    # indented under — its continuations are indented under the MATCH. Re-base it
    # onto them, or every following line inherits the `=>`'s column.
    cont = [c for c in cols[1:] if c is not None]
    if cont and cols[0] is not None and cols[0] > min(cont):
        cols[0] = min(cont)
    shift = min(c for c in cols if c is not None) - target
    return '\n'.join('' if c is None else ' ' * max(0, c - shift) + x
                     for x, c in zip(texts, cols))


ARM = re.compile(r'^\s*([A-Z]\w*)\(([^()]*)\)\s*=>\s*', re.S)


def final_in_block(t, close):
    """Is the expression ending at index `close` the last one in its block?"""
    i = close + 1
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            i = j
            continue
        if t[i].isspace():
            i += 1
            continue
        return t[i] in CLOSE
    return True


def uses_after(t, name, frm):
    """Occurrences of `name` between frm and the end of its enclosing block."""
    return len(re.findall(r'(?<![\w])' + re.escape(name) + r'(?![\w])', t[frm:block_end(t, frm)]))


def r1(t):
    """match VAR { C(args) => BODY }  ->  let C(args) = VAR; BODY"""
    mask = comment_mask(t)
    for m in re.finditer(r'(?<![\w])match\s+([a-z_]\w*)\s*\{', t):
        if mask[m.start()]:
            continue
        ob = t.index('{', m.start())
        cb = match_brace(t, ob)
        arms = split_top(t[ob + 1:cb])
        if len(arms) != 1:
            continue
        a = ARM.match(arms[0])
        if not a:
            continue
        if not final_in_block(t, cb):
            continue
        b0 = ob + 1 + a.end()
        b1 = cb
        while t[b1 - 1].isspace():
            b1 -= 1
        raw = t[b0:b1]
        if raw.startswith('{') and match_brace(raw, 0) == len(raw) - 1:
            b0, b1 = b0 + 1, b1 - 1
            while t[b1 - 1].isspace():
                b1 -= 1
            raw = t[b0:b1]
        ind = indent_of(t, m.start())
        head = 'let %s(%s) = %s;' % (a.group(1), a.group(2), m.group(1))
        # A match that began MID-LINE keeps its body on that line. Breaking it
        # would put the body at the line's indentation, which is to the left of
        # the `let` that now binds it — `{ let Pair(k, H) = Zap(&m *w); () }` is
        # one statement sequence and reads as one.
        mid = t[line_start(t, m.start()):m.start()].strip() != ''
        if mid and '\n' not in raw:
            return t[:m.start()] + head + ' ' + raw.strip() + t[cb + 1:], True
        rep = '%s\n%s' % (head, dedent_body(raw, b0 - line_start(t, b0), ind))
        return t[:m.start()] + rep + t[cb + 1:], True
    return t, False


LET = r'(?<![\w])let\s+([a-z_]\w*)\s*=\s*'


def _rhs_from(t, start):
    """(rhs, index just past the ';') for a right-hand side beginning at `start`."""
    i, d = start, 0
    while i < len(t):
        j = skip_comment(t, i)
        if j != i:
            i = j
            continue
        c = t[i]
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            d -= 1
        elif c == ';' and d == 0:
            return t[start:i], i + 1
        i += 1
    return None


def r2(t):
    """let X = RHS; let C(args) = X;  ->  let C(args) = RHS;"""
    mask = comment_mask(t)
    for m in re.finditer(LET, t):
        if mask[m.start()]:
            continue
        r = _rhs_from(t, m.end())
        if not r:
            continue
        rhs, after = r
        nxt = re.match(r'\s*let\s+([A-Z]\w*)\(([^()]*)\)\s*=\s*' + re.escape(m.group(1)) + r'\s*;', t[after:])
        if not nxt:
            continue
        if uses_after(t, m.group(1), m.start()) != 2:
            continue
        rep = 'let %s(%s) = %s;' % (nxt.group(1), nxt.group(2), rhs)
        return t[:m.start()] + rep + t[after + nxt.end():], True
    return t, False


def r2m(t):
    """let X = RHS; match X { arms }  ->  match RHS { arms }"""
    mask = comment_mask(t)
    for m in re.finditer(LET, t):
        if mask[m.start()]:
            continue
        r = _rhs_from(t, m.end())
        if not r:
            continue
        rhs, after = r
        nxt = re.match(r'\s*match\s+' + re.escape(m.group(1)) + r'\s*\{', t[after:])
        if not nxt:
            continue
        ob = after + t[after:].index('{', nxt.start())
        cb = match_brace(t, ob)
        if not final_in_block(t, cb):
            continue
        if uses_after(t, m.group(1), m.start()) != 2:
            continue
        rep = 'match %s %s' % (rhs, t[ob:cb + 1])
        return t[:m.start()] + rep + t[cb + 1:], True
    return t, False


def read_pattern(t, i):
    """Read `Ctor(…)` at i, parentheses balanced; returns (text, end) or None."""
    m = re.compile(r'[A-Z]\w*\(').match(t, i)
    if not m:
        return None
    close = match_brace(t, m.end() - 1)
    return t[i:close + 1], close + 1


def r3(t):
    """let C(a, q) = RHS; let D(bs) = q;  ->  let C(a, D(bs)) = RHS;

    `q` is replaced wherever it sits in the pattern, not only at the top level,
    so a chain collapses all the way down rather than one level per shape."""
    mask = comment_mask(t)
    for m in re.finditer(r'(?<![\w])let\s+(?=[A-Z]\w*\()', t):
        if mask[m.start()]:
            continue
        pat = read_pattern(t, m.end())
        if not pat:
            continue
        outer, pe = pat
        eq = re.compile(r'\s*=\s*').match(t, pe)
        if not eq:
            continue
        r = _rhs_from(t, eq.end())
        if not r:
            continue
        rhs, after = r
        nx = re.compile(r'\s*let\s+(?=[A-Z]\w*\()').match(t, after)
        if not nx:
            continue
        ip = read_pattern(t, nx.end())
        if not ip:
            continue
        inner, ie = ip
        tail = re.compile(r'\s*=\s*([a-z_]\w*)\s*;').match(t, ie)
        if not tail:
            continue
        q = tail.group(1)
        occ = re.findall(r'(?<![\w])' + re.escape(q) + r'(?![\w])', outer)
        if len(occ) != 1 or uses_after(t, q, m.start()) != 2:
            continue
        new = re.sub(r'(?<![\w])' + re.escape(q) + r'(?![\w])', inner.replace('\\', '\\\\'), outer)
        return t[:m.start()] + 'let %s = %s;' % (new, rhs) + t[tail.end():], True
    return t, False


def run(path, rules):
    t = open(path).read()
    counts = {}
    for name, fn in rules:
        n = 0
        while True:
            t, ch = fn(t)
            if not ch:
                break
            n += 1
        counts[name] = n
    open(path, 'w').write(t)
    return counts


if __name__ == '__main__':
    which = {'r1': r1, 'r2': r2, 'r2m': r2m, 'r3': r3}
    names = sys.argv[2].split(',') if len(sys.argv) > 2 else ['r1', 'r2', 'r3']
    print(run(sys.argv[1], [(n, which[n]) for n in names]))
