use compiler_macros::ochre;

fn main() {
    ochre! {
        'hello
    }

    // ochre! {
    //     let Nat
    //         = (l: 'zero, 'unit)
    //         | (x: 'succ, Nat: 'hello);
        
    //     'unit
    // }
    
    // let x = ochre! {
    //     Zero = ('zero, 'unit);
    //     Succ(x) = ('succ, x);
    //     Nat = Zero | Succ(Nat);

    //     // What I want
    //     add(x: Nat, y: Nat): Nat = {
    //         match x {
    //             Zero => y,
    //             Succ(px) => Succ(add(px, y))
    //         }
    //     };

    //     x: Nat = 5

    //     // What I have
    //     add: (Nat, Nat) -> Nat = (x: Nat, y: Nat) -> (
    //         match x.0 {
    //             'zero => y,
    //             'succ => ('succ, add(x.1, y))
    //         }
    //     );

    //     units(n: Nat) -> Vec () n = (
    //         match n {
    //             Zero => Nil,
    //             Succ(pn) => Cons((), units(pn))
    //         }
    //     )

    //     inc = (x: Nat) -> add(x, 1);
    // };

    // dbg!(x);
}




