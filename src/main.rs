mod max;
mod all_zeros;
mod binary_search;
mod strictly_increasing_sequence;
mod ext_int;
mod seq_ex;
mod forall_ex;

use max::*;

fn main() {
    println!("Hello, world!");

    let x = 3;
    let y = 0;
    println!("max({x}, {y}) = {}", compute_max(x, y));

    max_test();
    binary_search::test();
    ext_int::test();
    seq_ex::test();
}
