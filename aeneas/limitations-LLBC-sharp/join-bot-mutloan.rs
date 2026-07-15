fn f(mut a: Box<i32>, mut b: Box<i32>, cond: bool) {
    let mut x = &mut a;
    if cond {
        x = &mut b;
        // In this branch, `b` is mutably borrowed by `x`. It's value is $loan^m l v$
    }
    else {
        drop(b);
        // In this branch, `b` is invalid. It's value is $\bot$.
    }
    // Problem: it's actually not possible to join a mutable loan and a $\bot$
    // value. Indeed, the reference `x` is valid, so `b` should be marked as
    // borrowed. But `b` may be invalid, so its value cannot be a mutable loan.

    // Currently, the only way to make the program accepted by LLBC# until this
    // line is to kill the reference `x`, so to end the loan of `b`. But this
    // does not accepts the following line:
    dbg!(&x); // Accepted by the borrow-checker.
}
