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
#let St(om, sc, ob, gr, rt) = $chevron.l #om ; #sc ; #ob ; #gr ; #rt chevron.r$
#let sctx(s, t) = $#s : #t$                        // σ-context entry
#let oblig(x, l, S) = $(#x, #l, #S)$               // obligation entry
#let group(r, cap, iss) = $A(#r){#cap ; #iss}$     // loan group node
#let groupb(r, cap, iss, f) = $A(#r){#cap ; #iss ; "back" thin #f}$  // …carrying a declared back
#let owed(l, t) = $#l scripts("")_(["owed" #t])$   // owed-annotated loan

// ---------- Reorganization auxiliaries (F2; premises of ⇐-overwrite and group ends) ----------
#let dropj(om, v, om2) = $#om tack.r "drop" thin #v tack.l #om2$                     // dropping a displaced value
#let surrj(om, l, ty, v, om2) = $Gamma_sigma ; #om tack.r owed(#l, #ty) arrow.b.double #v tack.l #om2$  // issued-borrow surrender
#let ownfree(v) = $"own-free"(#v)$                 // no loan/borrow node at any depth

// ---------- Types-as-terms / typing / conversion ----------
#let hasT(v, t) = $#v : #t$                        // value against type (hasType)
#let conv(a, b) = $#a equiv #b$                    // conversion
#let borrowT(s, t, S) = $amp"mut" (#s : #t arrow.r.curve #S)$  // the ↝ borrow type
#let sigT(x, A, B) = $Sigma (#x : #A). #B$
#let piT(x, A, B) = $Pi (#x : #A) arrow.r #B$

// ---------- Judgment-level audits / boundaries ----------
#let audit(st, d) = $#st tack.r.double "audit"(#d)$
#let checkFn(d) = $tack.r "fn" #d "ok"$

// ---------- Boundary-layer auxiliaries (F5: seeding, calls, the audit) ----------
// (Letter clash, inherited from the style pin: S is both the checker-state letter
// and the owed-type binder position in &mut (s : τ ↝ S). We render the state
// calligraphic (𝒮) and owed types italic; they never collide in a rule.)
#let cS = $cal(S)$
#let seedJ(S1, D, S2) = $#S1 tack.r "seed"(#D) tack.l #S2$                            // telescope seeding at entry
#let argsJ(S1, th, args, D, C, S2, th2) = $#S1 space.thin ; #th tack.r #args : #D arrow.r.double #C tack.l #S2 space.thin ; #th2$  // call arguments vs telescope
#let resJ(th, T, v, I, S2) = $#th tack.r #T arrow.r.double_("res") (#v space.thin ; #I) tack.l #S2$  // fresh result from return type
#let collJ(T, v, B) = $#T ⊳ #v arrow.r.double #B$                                     // collect result borrows at return
#let reachJ(a, b) = $#a ↠ #b$                                                         // loan reachability
#let obligJ(S, I, ob) = $#S space.thin ; #I tack.r.double #ob$                        // audit one obligation
#let backJ(S, I, d) = $#S tack.r.double "back"_(#I) (#d)$                             // declared-back callee check
#let resolve(I, v) = $"res"_(#I)(#v)$                                                 // suspension-tree resolution
#let hole(i) = $"%r"_(#i)$                                                            // issued-loan hole (de Bruijn)

// ---------- Status tags (one visual convention paper-wide) ----------
// green    = checked and green in the mechanization at the pin commit
// in flight = under construction in the mechanization
// proposed = design decided or planned, not yet mechanized
// open     = known gap, stated as such
#let status(tag) = {
  let palette = (
    "green": rgb("#1a7f37"),
    "in flight": rgb("#9a6700"),
    "proposed": rgb("#0550ae"),
    "open": rgb("#cf222e"),
  )
  let c = palette.at(tag, default: luma(80))
  box(
    stroke: 0.7pt + c,
    fill: c.transparentize(93%),
    inset: (x: 3.5pt, y: 2pt),
    radius: 2.5pt,
    baseline: 20%,
    text(size: 7pt, fill: c, weight: "semibold", tracking: 0.5pt, upper(tag)),
  )
}

// ---------- Rule-name prefixes (pin: figure ↔ prefix) ----------
// F1 runtime ⇒/⇐:        R-…   (R-Copy, R-Move, R-Ctor, R-Take, R-Mint, R-Let, R-Seq, R-Assign, R-Unit, R-Lift, R-Reorg)  and  W-Fill for ⇐
// F2 reorganization:      G-…   (G-EndMut, G-DropFree/Loan/Borrow, G-EndIssued, G-EndGroupOpaque, G-EndGroupBack, G-EndOwed)
// F3 comptime ⇝/⇜:        C-…   (C-Beta, C-IotaNatZ/S, C-IotaJ/K, C-Snap, C-Deref, C-Let)  and  X-… for ⇜ (X-Shape, X-Sol, X-SolRefl, X-Gen)
// F4 match:               M-…   (M-Owned, M-Borrow, M-OwnedSym, M-BorrowSym, M-Refl-Flex, M-Exhaust)
// F5 boundaries/calls:    B-…   (B-Seed, B-Pin, B-Inst, B-Res, B-Call, B-Coll, B-Reach, B-Exempt, B-Oblig-Conv, B-ExFalso, B-Audit, B-Back…, B-CheckFn)
// F6 hasType/convert:     T-…   (T-Type, T-Former, T-Sym, T-Ctor, T-Lam, T-ElimSynth, T-Spine, T-Conv)  and  C≡-… for conversion
// F7 the carve:           K-…   (K-Carve, K-Cite, K-Cite-Eq)

// Cross-reference table helper: rule ↔ implementing function ↔ exercising test
#let xref(..rows) = table(
  columns: (auto, auto, auto),
  align: left,
  table.header([*Rule*], [*Implementation*], [*Test*]),
  ..rows.pos().flatten()
)
