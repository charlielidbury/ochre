use compiler_macros::ochre;

fn main() {
    ochre! {
        Bool = 'true | 'false;
        Pair = (Bool, Bool);
        Same = (Bool, L -> L);
        p = ('true, 'false);
        // p.0 = 'false;
        p.1 = 'true;
        p: Same;
    }
}
