#[rustfmt::skip]
use std::mem;

use compiler_macros::ochre;

// fn ochreshittery() {
//     ochre! {
//         // numbers tings
//         Nat = ('zero, 'unit);

//         Swap = (T) -> (x: &mut T, y: &mut T) -> 'unit {
//             tmp = *x;
//             *x = *y;
//             *y = tmp;
//         }

//         // Adds
//         AddT = (x: Nat, y: Nat) -> Nat;
//         add_efficient: AddT = (x: Nat, y: Nat) -> Nat {
//             match &mut x {
//                 ('zero, 'unit) => y,
//                 ('succ, px) => (*px = add(*px, y); x),
//             }
//         };
//         AddT = (N: Nat, M: Nat) -> match N {
//             ('zero, 'unit) => y,
//             ('succ, px) => ('succ, AddT(px, y)),
//         }

//         // Vec
//         Vec = (A, N: Nat) -> match N {
//             ('zero, 'unit) => 'unit,
//             ('succ, Pn) => (A, Vec(A, Pn)),
//         };
//         VecAppendT = (A, N: Nat, M: Nat) -> (x: Vec(A, N), y: Vec(A, M)) -> Vec(A, AddT(N, M)) {
//             // wont work because narrowing N or M won't narrow x
//         }

//         // List
//         List = A -> (Nat, N -> Vec(A, N));
//         ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A);
//         ListAppend: ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A) {
//             match x.0.0 {
//                 'zero => y,
//                 'succ => { // { x |-> (('succ, tail_length), (head, tail)) }
//                     x_tail = (x.0.1, x.1.1);
//                     (z_length, z) = ListAppend(A)(x_tail, y);
//                     (('succ, z_length), (x.1.0, z)) // allocates list node
//                 }
//             }
//         }
//         ListAppendEfficient: ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A) {
//             match x.0.0 {
//                 'zero => y,
//                 'succ => { // { x |-> (('succ, tail_length), (head, tail)) }
//                     (x.0.1, x.1.1) = ListAppend(A)((x.0.1, x.1.1), y);
//                     x
//                 }
//             }
//         }
//         ListAppendEfficientEfficient: ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A) {
//             match x.0.0 { // this one doesnt use any allocations at all
//                 'zero => y,
//                 'succ => {                       // { x |-> (('succ, tail_length), (head       , tail  )) }
//                     head = x.1.0;                // { x |-> (('succ, tail_length), (head       , tail  )) }
//                     x.1.0 = x.0.1;               // { x |-> (('succ, _          ), (tail_length, tail  )) }
//                     x.1 = ListAppend(A)(x.1, y); // { x |-> (('succ, _          ), (z_length   , z_tail)) }
//                     x.0.1 = x.1.0;               // { x |-> (('succ, z_length   ), (_          , z_tail)) }
//                     x.1.0 = head;                // { x |-> (('succ, z_length   ), (head       , z_tail)) }
//                     x
//                 }
//             }
//         }

//         // this stuff
//     };

//     // deprecated
//     ochre! {
//         Nat = ('zero, 'unit) | ('succ, Nat);
//         AddType = (x: Nat, y: Nat) -> Nat;

//         add: AddType = (x: Nat, y: Nat) -> Nat {
//             match x {
//                 ('zero, 'unit) => y,
//                 ('succ, px) => ('succ, add(px, y))
//             }
//         }

//         add_no_alloc: AddType = (x: Nat, y: Nat) -> Nat {
//             match &mut x {
//                 ('zero, 'unit) => y,
//                 ('succ, px) => (
//                     *px = add(*px, y);
//                     x
//                 )
//             }
//         }

//         // List
//         List = A -> (Nat, N -> Vec(A, N));
//         ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A);
//         ListAppend: ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A) {
//             match x {
//                 (('zero, 'unit), 'unit) => y,
//                 (('succ, length_tail), (head, tail)) => {
//                     tail = (length_tail, tail);
//                     (length_z, z) = ListAppend(A)(tail, y);
//                     (('succ, length_z), (head, z)) // should work
//                     (length_z, (head, z)) // should error, but how?
//                 }
//             }
//         }
//         ListAppendEfficient: ListAppendT = (A) -> (x: List(A), y: List(A)) -> List(A) {
//             match &mut x {
//                 (('zero, 'unit), 'unit) => y,
//                 (('succ, length_tail), (_, tail)) => {
//                     (*length_tail, *tail) = ListAppendEfficient(A)((*length_tail, *tail), y);
//                     *length_tail = ('succ, *length_tail); // should make fail, but how?
//                     x
//                 }
//             }
//         }
//     };
// }

// enum Nat {
//     Zero,
//     Succ(Box<Nat>),
// }
// use Nat::*;

// fn add(mut x: Nat, y: Nat) -> Nat {
//     match &mut x {
//         Zero => y,
//         Succ(px) => {
//             let mut z = Zero;
//             mem::swap(&mut z, &mut **px);
//             **px = add(z, y);
//             x
//         }
//     }
// }

// fn swap<T>(x: &mut T, y: &mut T) {
//     let temp = *x;
//     *x = *y;
//     *y = temp;
// }

// fn add_mut(x: &mut Nat, y: &mut Nat) {
//     match x {
//         Zero => mem::swap(x, y),
//         Succ(px) => add_mut(px, y),
//     }
// }

fn main() {
    ochre! {
        // Bool = 'true | 'false;
        // Same = (Bool, L -> L);

        p = ('true, 'true); //: Same;
        p.0 = 'false;
        p.1 = 'false;
        p: ('false, 'false);
        // p: 'hello | 'world;

        'unit
    };
}
