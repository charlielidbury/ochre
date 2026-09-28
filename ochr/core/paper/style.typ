// Shared style for the Ochr core paper.
#let paper(title: none, subtitle: none, authors: (), abstract: none, body) = {
  set document(title: title)
  set text(font: "New Computer Modern", size: 10pt)
  set page(paper: "us-letter", margin: (x: 2.2cm, y: 2.4cm), numbering: "1")
  set par(justify: true, leading: 0.62em, spacing: 0.9em)
  set heading(numbering: "1.1")
  show heading.where(level: 1): it => { v(0.8em); it; v(0.3em) }
  show raw: set text(font: "DejaVu Sans Mono", size: 8.6pt)
  show raw.where(block: true): it => block(width: 100%, inset: (x: 8pt, y: 6pt), fill: luma(246), radius: 2pt, it)
  show link: underline
  align(center, text(size: 16pt, weight: "bold", title))
  if subtitle != none { align(center, text(size: 11pt, subtitle)) }
  v(0.6em)
  if abstract != none {
    align(center, box(width: 88%, align(left, [*Abstract.* #abstract])))
    v(0.8em)
  }
  body
}

// Inference rule: premises over conclusion, with a name.
#let rule(name: none, ..premises, conclusion) = {
  let ps = premises.pos()
  box(inset: (x: 6pt, y: 4pt), stack(
    dir: ttb, spacing: 3pt,
    align(center, ps.map(p => $#p$).join(h(1.4em))),
    line(length: 100%, stroke: 0.5pt),
    align(center, $#conclusion$),
  ) + if name != none { place(right + horizon, dx: 3.2em, text(size: 8pt, smallcaps(name))) })
}

#let figure-rules(caption: none, body) = figure(kind: "rules", supplement: "Figure", caption: caption, block(width: 100%, inset: 6pt, stroke: (top: 0.4pt, bottom: 0.4pt), body))

// Notation helpers.
#let seal(t) = $lr(⌈ #t ⌉)$
#let obs(t) = $lr(⟦ #t ⟧)$

// Inference rule: premises (any number) over a conclusion, optional name on the right.
#let infer(name: none, ..args) = {
  let a = args.pos()
  let concl = a.last()
  let prems = a.slice(0, a.len() - 1)
  let tree = grid(
    columns: 1, align: center, row-gutter: 3pt,
    if prems.len() == 0 { [] } else { prems.join(h(1.6em)) },
    grid.hline(y: 1, stroke: 0.5pt),
    concl,
  )
  box(inset: (x: 4pt, y: 5pt), grid(columns: 2, column-gutter: 4pt, align: (center + bottom, left + horizon),
    tree, if name != none { text(size: 7.5pt, smallcaps(name)) } else { [] }))
}
#let rules(..rs) = align(center, rs.pos().join(h(1.2em, weak: true)))
#let cfg(o, t) = $chevron.l #o, #t chevron.r$
