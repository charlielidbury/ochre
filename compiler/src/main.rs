use compiler_macros::ochre;

fn main() {
    ochre! {
        Bool = 'true | 'false;
        Pair = (Bool, Bool);
        Same = (Bool, L -> L);

        f = (x: &Pair) {
            x?;
            // *p.0 = 'true;
        };

        overwrite = (p: &mut Same) {
            *p.1 = 'false;
            f(&*p);
            *p.0 = 'false;
        };
    }
}
