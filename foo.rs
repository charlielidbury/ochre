

fn loop_fn<'a>(x: &mut i32, y: &mut &i32) {
    x += 1;
    y = &x;
}

fn main() {
    let mut x = 0;
    let mut y = &x;

    loop_fn(&mut x, &mut y);

    println!("{}", y);
}
