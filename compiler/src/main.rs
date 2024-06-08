use compiler_macros::ochre;

fn main() {
    let result = ochre! {
        Nat = ('zero, 'unit);

        add = (x: Nat, y: Nat) -> Nat {
            case x.0 {
                'zero => y,
                'succ => ('succ, add(x.1, y))
            }
        };

        Vec = (A, n: Nat) -> case n.0 {
            'zero => 'unit,
            'succ => (A, Vec(A, n.1)),
        };

        List = A -> (Nat, n -> Vec(A, n));

        // end = (A, l: List(A)) -> 'hello {
        //     case l.0.0 {
        //         'zero => 'hello,
        //         'succ => end(A, (l.0.1, l.1.1)),
        //     }
        // };

        append = (A, lx: List(A), ly: List(A)) -> List(A) {
            case lx.0.0 {
                'zero => ly,
                'succ => {
                    (n, lxy) = append(A, lx.1.1, ly);
                    (('succ, n), (lx.1.0, lxy))
                }
            }
        }
    };

    dbg!(result);
}

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
