use compiler_macros::ochre;

fn _main() {
    ochre! {
        'hello
    }
}

// ochre! {
//     Nat = ('zero, *) | ('succ, Nat);

//     x = ('zero, _): Nat;
// }

// ochre! {
//     Bool = 'true | 'false;
//     Same = (Bool, L -> L);

//     overwrite = (p: &mut Same) -> * {
//                         p?;
//         *p.0 = 'false;  p?;
//         *p.1 = 'false;  p?;
//                         p?;
//     };

//     pair = ('true, 'true);
//     overwrite(&mut pair);
// }

// ochre! {
//     Bool = 'true | 'false;
//     Same = (Bool, L -> L);

//     overwrite = (p: &mut Same) -> * {
//                           p?;
//         *p.0 = 'true;     p?;
//         *p.1 = 'true;     p?;
//                           p?;
//     };

//     pair = ('false, 'false);
//     overwrite(&mut pair);
// };

// ochre! {
//     // p = ('a, 'a);
//     // p.0 = 'b;
//     // p?;

//     x = ('a, 'a);
//     rx = &mut x;
//     (*rx).0 = 'b;
//     x?;
// }

// ochre! {
//     Bool = 'true | 'false;

//     y = 'true: Bool; y?;

//     not = (x: Bool) -> Bool {
//         match x {
//             'false => 'true,
//             'true => 'false,
//         }
//     };

//     not?
// }

// ochre! {

//     Bool = 'true | 'false;
//     Id = X -> X;

//     not = (b: Bool) -> Bool {
//         'true
//     };

//     x = not 'true : Id Bool;

//     x?;
// }
