import Ochr.Examples.DependentFields

/-!
# Where a label's record is a member: the checker's side (docs/31 D68)

A borrow records the content it borrowed as its label's member (`Steps/Records.lean`). The
record is a whole member of the borrow's type when the content is, and the checker makes it so:

* **A whole borrow of an open value is rejected** by [Repack] ("*v is borrowed whole, but it is
  open"), whether the index is written back before the borrow ends (`BorrowOpen`) or not
  (`BorrowOpen2`), and even when the index is written to a value the field's type would accept,
  since the field's type is the stuck `Fin1(σ1)` (`BorrowOpenSame`). The control borrows the same
  place whole with nothing written (`BorrowWhole`).
* **A borrow of the dependent field is accepted** (`BorrowField`): the field's content is a member
  of its field type at the earlier fields, which is the type it is held at. When the index is then
  rewritten, the borrow cannot end over the open value: [Repack] rejects the end
  (`BorrowFieldWrite`).

There is no syntactic shadow to sweep: the record is taken when the label is made, and a content
can become open only afterwards, by a write that [Repack] then checks at the end. The verdicts
below are the build's own check (every `def` accepted, every `reject def` rejected).
-/

ochr RecordSites uses DepFields {
  -- a whole borrow of an open value: the index written, then the pair borrowed whole
  reject def BorrowOpen (v : &V) : Unit := (match *v { MkV(n, x) => (n := Zero; let r = &*v; n := Succ(Zero); ()), })
  reject def BorrowOpen2 (v : &V) : Unit := (match *v { MkV(n, x) => (n := Zero; let r = &*v; ()), })
  reject def BorrowOpenSame (v : &V) : Unit := (match *v { MkV(n, x) => (n := Zero; n := Succ(Zero); let r = &*v; ()), })
  -- control: the same place borrowed whole, nothing written
  def BorrowWhole (v : &V) : Unit := (match *v { MkV(n, x) => (let r = &*v; ()), })
  -- a borrow of the dependent field, a member of its field type at the earlier fields
  def BorrowField (v : &V) : Unit := (match *v { MkV(n, x) => (let r = &x; ()), })
  -- the index rewritten while the field is borrowed: the end is over an open value
  reject def BorrowFieldWrite (v : &V) : Unit := (match *v { MkV(n, x) => (n := Zero; let r = &x; n := Succ(Zero); ()), })
}
