// The following function is safe and accepted by NLL.
fn f(cond: bool) {
    let mut a = 0;
    let mut b = 1;
    let c = 2;
    let mut x = &mut b;
    let mut y = &c;
    // a -> 0, b -> ML lb, c -> SL lc 2, x -> MB lb 1, y -> SB lc
    if cond {
        // At the end of this branch, `a` is a mutable loan.
        x = &mut a;
        // a -> ML l, b -> ML lb, c -> SL lc 2, x -> MB l 0, y -> SB lc,
        // _ -> MB lb 1
    }
    else {
        // At the end of this branch, `a` is a shared loan.
        y = &a;
        // a -> SL l' 0, b -> ML lb, c -> SL lc 2, x -> MB lb 1, y -> SB l',
        // _ -> SB lc
    }
    // TODO: compute the join according to the rules of the paper.
    *x = 3; // Is it allowed by LLBC#?

    // In any case, the only way to join a mutable is to declare `a` as a
    // mutable loan, that may be immutably borrowed by `y`. The trouble is that
    // now, reading `a` requires ending the mutable loans, and therefore
    // invalidating `y`.
    dbg!(a); // Any kind of read operation
    dbg!(*y); // <- Cannot currently be accepted by LLBC#.
}

fn main() {
    f(true);
    f(false);
}
