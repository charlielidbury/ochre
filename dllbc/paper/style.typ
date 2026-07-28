// DLLBC paper — shared style + notation. ALL figure/section files import this.
// Notation is pinned here; do not define judgment syntax locally in section files.
#import "@preview/curryst:0.5.0": prooftree, rule

// ---------- Inference-rule helper (Och house style) ----------
#let irule(name, conclusion, ..premises) = {
  let prems = premises.pos()
  if prems.len() == 0 {
    prooftree(rule(name: smallcaps(name), $#conclusion$))
  } else {
    prooftree(rule(
      name: smallcaps(name),
      $#conclusion$,
      ..prems.map(p => $#p$),
    ))
  }
}

// ---------- Values ----------
#let vbot = $bot$                                  // the hole / vacant slot
#let loanm(l) = $"loan"_m #l$                      // loan marker
#let borrowm(l, v) = $"borrow"_m #l space #v$      // borrow carrying payload
#let ctorv(c, args) = $#c (#args)$                 // constructor value
#let sym(s) = $sigma_#s$                           // symbolic value

// ---------- The four arrows (doc §1.3). Ω is the runtime env; ⇝ is Ω-effect-free ----------
#let evR(om, t, v, om2) = $#om tack.r #t arrow.r.double #v tack.l #om2$        // ⇒ consume-read
#let wrR(om, p, v, om2) = $#om tack.r #p arrow.l.double #v tack.l #om2$        // ⇐ destructive write / fill
#let evC(om, t, v) = $#om tack.r #t arrow.r.squiggly #v$                        // ⇝ comptime read (no Ω′)
#let refi(st, x, t, st2) = $#st tack.r #x arrow.l.squiggly #t tack.l #st2$      // ⇜ refinement (over full state)

// ---------- Reorganization (nondeterministic; distinct squiggle to avoid ⇝ clash) ----------
#let reorg(om, om2) = $#om arrow.r.long.squiggly #om2$
#let reorgs(om, om2) = $#om arrow.r.long.squiggly^* #om2$

// ---------- Checker state (for figures needing more than Ω) ----------
// S = ⟨Ω ; Γσ ; O ; G ; R⟩ : env, σ-context, obligations, groups, pinned return type
#let St(om, sc, ob, gr, rt) = $angle.l #om ; #sc ; #ob ; #gr ; #rt angle.r$
#let sctx(s, t) = $#s : #t$                        // σ-context entry
#let oblig(x, l, S) = $(#x, #l, #S)$               // obligation entry
#let group(r, cap, iss) = $A(#r){#cap ; #iss}$     // loan group node
#let owed(l, t) = $#l scripts("")_(["owed" #t])$   // owed-annotated loan

// ---------- Types-as-terms / typing / conversion ----------
#let hasT(v, t) = $#v : #t$                        // value against type (hasType)
#let conv(a, b) = $#a equiv #b$                    // conversion
#let borrowT(s, t, S) = $amp"mut" (#s : #t arrow.r.curve #S)$  // the ↝ borrow type
#let sigT(x, A, B) = $Sigma (#x : #A). #B$
#let piT(x, A, B) = $Pi (#x : #A) arrow.r #B$

// ---------- Judgment-level audits / boundaries ----------
#let audit(st, d) = $#st tack.r.double "audit"(#d)$
#let checkFn(d) = $tack.r "fn" #d "ok"$

// ---------- Rule-name prefixes (pin: figure ↔ prefix) ----------
// F1 runtime ⇒/⇐:        R-…   (R-Copy, R-Move, R-Ctor, R-Let, R-Assign, R-Mint, R-Take, W-Fill, …)
// F2 reorganization:      G-…   (G-EndMut, G-Drop, G-EndOwed, G-EndGroup, G-DemandRead, …)
// F3 comptime ⇝/⇜:        C-…   (C-Beta, C-IotaNat, C-Snap, C-Deref, …)  and  X-… for ⇜ (X-Sol, X-Shape, X-Gen, …)
// F4 match:               M-…   (M-Owned, M-Borrow, M-SymSplit, M-Exhaust, M-ReflFlex, …)
// F5 boundaries/calls:    B-…   (B-Seed, B-Inst, B-Pin, B-Audit, B-Back0, B-Exempt, B-ExFalso, B-Call, …)
// F6 hasType/convert:     T-…   (T-Ctor, T-Sigma, T-Elim, T-Sym, T-Conv, …)

// Cross-reference table helper: rule ↔ implementing function ↔ exercising test
#let xref(..rows) = table(
  columns: (auto, auto, auto),
  align: left,
  table.header([*Rule*], [*Implementation*], [*Test*]),
  ..rows.pos().flatten()
)
