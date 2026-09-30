import sys
P = sys.argv[1]
def edit(f, pairs):
    s = open(P + f).read()
    for o, n in pairs:
        assert s.count(o) == 1, (f, o[:80], s.count(o))
        s = s.replace(o, n)
    open(P + f, 'w').write(s)
edit('sections/typing.typ', [
  ("The properties a kernel usually rests on are therefore stated about the machine: in place of a substitution lemma, the stability of the checker's decisions under refinement, and in place of subject reduction, naturality, the agreement of a symbolic run with every concrete one (@sec-meta-nat). Both are conjectures, and so is consistency.",
   "The properties a kernel usually rests on are therefore about the machine: in place of a substitution lemma, the stability of the checker's decisions under refinement, and in place of subject reduction, naturality, a symbolic run's agreement with every concrete one (@sec-meta-nat). Both, like consistency, are conjectures."),
  ("Nor can the ledger show that a rule is sound when switched on: the last closed `False` above needed two rules that the ledger classes as completeness rows.",
   "Nor does the ledger show a rule sound when on: the last closed `False` above needed two rules the ledger classes as completeness rows."),
])
s = open(P + 'sections/meta.typ').read()
i = s.index('// SLOT (lead): once fixed, M2'); j = s.index('\n', s.index('// SLOT (lead): once fixed, one sentence on Bad2'))
s = s[:i] + s[j+1:]
a = "An argument about a class of findings is not a proof."
assert s.count(a) == 1
s = s.replace(a, a + " Two later findings are fixed: an accepted function could fail when a borrowed local was dropped (now the [Drop] rule), and a match on a value of stuck type took its constructors from its patterns.")
open(P + 'sections/meta.typ', 'w').write(s)
print('ok')
