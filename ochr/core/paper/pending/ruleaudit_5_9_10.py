# rule-audit items 5 ([J-stuck]/[T-J-stuck], b89b591f), 9 (Id by the machine, aebb9f06), 10 (mixed-arm match, 35ae0de2).
# Apply only once those commits are on ochr-core. Text is rule-audit's, verbatim except where noted.
import sys
P = sys.argv[1] if len(sys.argv) > 1 else '/home/charlielidbury/repos/ochre-ochr-core/ochr/core/paper/'
f = P + 'sections/appendix.typ'
s = open(f).read()
def rep(o, n):
    global s
    assert s.count(o) == 1, (o[:80], s.count(o)); s = s.replace(o, n)

# item 5: [T-J] gains v_a ≡ v_b; [T-J-stuck] added after it
rep('ir(name: "T-J", pv($Omega tack.r A ev T "type" quad Omega tack.r a ev v_a : T_a equiv T quad Omega tack.r b ev v_b : T_b equiv T quad Omega tack.r P ev F : Pi$,',
    'ir(name: "T-J", pv($Omega tack.r A ev T "type" quad Omega tack.r a ev v_a : T_a equiv T quad Omega tack.r b ev v_b : T_b equiv T quad Omega tack.r P ev F : Pi quad v_a equiv v_b$,')
TJ_END = '$Omega tack.r ty("J")(A, a, b, P, h, t) ev v : P_b tack.l Omega\'$),'
rep(TJ_END, TJ_END + '\n  ir(name: "T-J-stuck", pv($Omega tack.r A ev T "type" quad Omega tack.r a ev v_a : T_a equiv T quad Omega tack.r b ev v_b : T_b equiv T quad v_a equiv.not v_b quad Omega tack.r P ev F : Pi$, $Omega tack.r h ev star : H equiv "eq"(T, v_a, v_b) quad Omega tack.r F(v_a) ev P_a : s quad Omega tack.r F(v_b) ev P_b : s quad Omega tack.r t ev v : T_t equiv P_a "on a private copy"$, $cfg(Omega, "block"(Omega, ty("J")(T, v_a, v_b, F, star, t), P_b, M)) ev cfg(Omega\', w)$), $Omega tack.r ty("J")(A, a, b, P, h, t) ev w : P_b tack.l Omega\'$),')
rep('`J` takes its endpoints explicitly, because `Eq A a a` computes to `⊤` and no longer records them.',
    '`J` takes its endpoints explicitly, because `Eq A a a` computes to `⊤` and no longer records them. When the endpoints are not convertible the machine is stuck ([J-stuck]), so typing checks `t` against `P(a)` on a private copy and closes the `J` off as a stuck block of type `P(b)` ([T-J-stuck]), as [Split] closes off a stuck match. `M` is the set of places `t`\'s run moves out of. The block\'s code embeds the endpoints, the motive and the equation as values, since they are erased and formed once, so it captures only `t`\'s places. Its sealed programs run `t` once a refinement makes the endpoints convertible.')
rep("Its motive may have any sort; with a motive into `Prop`, `J` is a proof and is erased.", "Its motive may have any sort; with a motive into `Prop`, `J` is a proof and is erased, and neither [T-J] nor [T-J-stuck] applies.")

# item 9
rep('A stuck match in `t` is closed off by [Split] (@app-typing), so an observation exists unless `t` has an error.',
    'A stuck match in `t` is closed off by [Split] (@app-typing), so an observation exists unless `t` has an error. This holds wherever `Id` is evaluated, the machine included (a callee\'s body, a sealed program\'s re-run). There the side\'s run is the machine\'s when it is not stuck, which is what typing computes; when it is stuck, the side is observed by the typing judgement.')

# item 10
rep("a `let`, sequence or match has its tail's, or each arm's;",
    "a `let`, sequence or match has its tail's, or each arm's; a match some of whose arms are proofs and some not has no declared type, and it is rejected wherever its declared type is read: in a type position ([Type-pos]), and by erasure, which reads every term's;")
open(f, 'w').write(s)
print('ok')
