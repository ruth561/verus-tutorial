mod max;
mod all_zeros;
mod binary_search;
mod strictly_increasing_sequence;
mod ext_i64;
mod ext_int;
mod seq_ex;
mod subseq;
mod forall_ex;
mod dbm;
mod integers;
mod vec_i64_to_seq_int;
mod pptr;
mod set_ex;
mod linked_list_box;
mod max_vec;
mod map_ex;

use max::*;

fn main() {
    println!("Hello, world!");

    let x = 3;
    let y = 0;
    println!("max({x}, {y}) = {}", compute_max(x, y));

    max_test();
    binary_search::test();
    ext_i64::test();
    seq_ex::test();
    subseq::test();
    integers::test();
    pptr::test();
    max_vec::test();
}
