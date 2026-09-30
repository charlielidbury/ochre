# Restore the naturality wording 49801faf removed (lead: --drop 100 acceptance passed, D65 = the DropProbe/Bad2 fix).
import sys
P = sys.argv[1]
def edit(f, pairs):
    s = open(P + f).read()
    for o, n in pairs:
        assert s.count(o) == 1, (f, o[:80], s.count(o))
        s = s.replace(o, n)
    open(P + f, 'w').write(s)
edit('sections/meta.typ', [
  ("so an `Id` computed on abstract inputs holds on every concrete input where it computes.], [conjecture]",
   "so an `Id` computed on abstract inputs holds on every concrete input.], [conjecture]"),
  ("If the run of $t alpha$ at $Omega alpha$ ends as $chevron.l Omega'', v'' chevron.r$, then after every borrow is ended in both,",
   "If the run of $t alpha$ at $Omega alpha$ ends, it ends without error, as $chevron.l Omega'', v'' chevron.r$, and after every borrow is ended in both,"),
  ("In particular, an `Id` that computes to ⊤ at Ω computes to ⊤ at $Omega alpha$ whenever it computes there.",
   "In particular (adequacy), an `Id` that computes to ⊤ at Ω computes to ⊤ at $Omega alpha$."),
  ("The run of $t alpha$ can fail where the run of $t$ succeeds: ending a borrow early on the symbolic path can let a later [Drop] succeed that fails at the instance (`DropProbe`).",
   "Whether the run of $t alpha$ ends is property 7; the requirement that every definition be accepted is needed because a call closed off at Ω runs at $Omega alpha$, and only its own [Def] check says it runs without error there."),
])
s = open(P + 'sections/meta.typ').read()
i = s.index('// TODO(prop-paper): the DropProbe/Bad2 fix is amended D65'); j = s.index('\n', i)
s = s[:i] + s[j+1:]
open(P + 'sections/meta.typ', 'w').write(s)
edit('sections/discussion.typ', [
  (", though a probe has found one outside them (@sec-meta-nat).", " (@sec-meta-nat)."),
])
edit('sections/meta.typ', [("it covers both case splits and instantiation at a call site, where an argument's type need only be convertible with the parameter's.",
  "it covers case splits and call-site instantiation, where an argument's type need only convert to the parameter's.")])
print('ok')
