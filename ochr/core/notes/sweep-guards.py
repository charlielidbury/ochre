#!/usr/bin/env python3
"""docs/07 final sweep: blocks are checked when elaborated, so the per-block verdict lines go.

In every example file:
  #eval IO.println (run "X" X).show          -> removed
  #guard (run "X" X).allAsExpected           -> removed
  #guard (run "X" X).count == N              -> #guard X.decls.length == N   (the count, no checker run)
  "-- every verdict as expected, and the exact number of declarations (a truncated file changes it)"
                                             -> "-- the exact number of declarations (a truncated file changes it)"
Registry.lean: the total counts declarations without running the checker; the all-as-expected
guard goes. Asserts, per file, one count line per `ochr` block and no `run` guard left.
"""
import re, sys, pathlib

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else '.')
ex = root / 'Ochr' / 'Examples'
EVAL = re.compile(r'^#eval IO\.println \(run "(\w+)" (\w+)\)\.show\s*$')
ALL = re.compile(r'^#guard \(run "(\w+)" (\w+)\)\.allAsExpected\s*$')
CNT = re.compile(r'^#guard \(run "(\w+)" (\w+)\)\.count == (\d+)\s*$')
# Units.lean's form: both in one guard
BOTH = re.compile(r'^#guard \(run "(\w+)" (\w+)\)\.allAsExpected && \(run "\w+" \w+\)\.count == (\d+)\s*$')
OLD_COMMENT = '-- every verdict as expected, and the exact number of declarations (a truncated file changes it)'
NEW_COMMENT = '-- the exact number of declarations (a truncated file changes it)'

total_counts = 0
for f in sorted(ex.glob('*.lean')):
    if f.name in ('Registry.lean', 'Ledger.lean', 'CaseStudyLedger.lean'):
        continue
    src = f.read_text()
    out = []
    counts = 0
    for line in src.split('\n'):
        if EVAL.match(line) or ALL.match(line):
            continue
        m = CNT.match(line) or BOTH.match(line)
        if m:
            out.append(f'#guard {m.group(2)}.decls.length == {m.group(3)}')
            counts += 1
            continue
        out.append(NEW_COMMENT if line == OLD_COMMENT else line)
    text = '\n'.join(out)
    text = re.sub(r'\n{3,}', '\n\n', text)
    blocks = len(re.findall(r'^ochr \w+', text, re.M))
    counts = len(re.findall(r'^#guard \w+\.decls\.length == \d+$', text, re.M))   # idempotent: swept before or now
    # 00Std also counts the Prelude block (defined in Ochr/Prelude.lean)
    assert counts == blocks + text.count('#guard Prelude.decls.length'), (f.name, counts, blocks)
    for l in text.split('\n'):
        assert not ((l.startswith('#guard (run') and '.rejectedWith' not in l) or l.startswith('#eval IO.println (run')), (f.name, l)
    f.write_text(text)
    total_counts += counts
    print(f'{f.name}: {blocks} blocks, {counts} count guards')

reg = ex / 'Registry.lean'
s = reg.read_text()
old_total = 'open Ochr.Registry Ochr.Test in\n#guard ((reports {}).map Report.count).foldl (· + ·) 0 == expectedTotal\n'
new_total = ('open Ochr.Registry Ochr.Test in\n'
             '#guard ((programs ++ caseStudies).map (·.2.decls.length)).foldl (· + ·) 0 == expectedTotal\n')
old_all = 'open Ochr.Registry Ochr.Test in\n#guard (reports {}).all Report.allAsExpected\n'
assert s.count(old_total) + s.count(new_total) == 1
s = s.replace(old_total, new_total).replace(old_all, '')
reg.write_text(s.rstrip('\n') + '\n')
print(f'Registry: total counts declarations; {total_counts} count guards in all')
