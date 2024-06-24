use compiler_macros::ochre;

fn main() {
    ochre! {
        Bool = 'true | 'false;
        Pair = (Bool, Bool);
        Same = (Bool, L -> L);

        overwrite = (p: &mut Same) {
            *p.1 = 'false;
            *p.0 = 'false;
        };

        pair = ('true, 'true);
        overwrite(&mut pair);
    }
}
