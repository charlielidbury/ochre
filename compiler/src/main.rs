#[rustfmt::skip]
use std::mem;

use compiler_macros::ochre;

fn main() {
    // ochre! {
    //     Bool = 'true | 'false;
    //     p = ('true, 'true): (Bool, Bool);  p?;
    //     p.0 = 'false;                      p?;
    //     p.1 = 'false;                      p?;
    //     p = p: (Bool, Bool);               p?;

    //     'unit
    // }

    ochre! {
        Bool = 'true | 'false;

        x = 'true: Bool;
    }
}
