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
mod linked_list;
mod map_ex;


fn main() {
    max::test();
    binary_search::test();
    ext_i64::test();
    seq_ex::test();
    subseq::test();
    integers::test();
    pptr::test();
    max_vec::test();
    linked_list_box::test();
    linked_list::test();
}
