use compiler_macros::ochre;

fn main() {
    ochre! {

        Bool = 'true | 'false;
        Id = X -> X;

        not = (b: Bool) -> Bool {
            'true
        };

        x = not 'true : Id Bool;

        x?;
    }
}
