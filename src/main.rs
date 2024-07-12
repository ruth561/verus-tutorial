mod max;
mod all_zeros;
mod binary_search;

use max::compute_max;

fn main() {
    println!("Hello, world!");

    let x = 3;
    let y = 0;
    println!("max({x}, {y}) = {}", compute_max(x, y));

    binary_search::test();
}
