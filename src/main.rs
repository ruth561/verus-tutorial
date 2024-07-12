mod max;
mod all_zeros;

use max::compute_max;

fn main() {
    println!("Hello, world!");

    let x = 3;
    let y = 0;
    println!("max({x}, {y}) = {}", compute_max(x, y));
}
