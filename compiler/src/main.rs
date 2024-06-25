use compiler_macros::ochre;

fn main() {
    ochre! {
        Bool = 'true | 'false;
        Pair = (Bool, Bool);
        Same = (Bool, L -> L);

        f = (p: &Pair) {};

        overwrite = (p: &mut Same) {
            *p.1 = 'false;
            f(&*p);
            *p.0 = 'false;
        };

        pair = ('true, 'true);
        overwrite(&mut pair);
    }
}
