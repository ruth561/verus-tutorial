mod max;
mod all_zeros;
mod binary_search;
mod strictly_increasing_sequence;
mod ext_i64;
mod ext_int;
mod ex_seq;
mod subseq;
mod ex_forall;
mod dbm;
mod integers;
mod vec_i64_to_seq_int;
mod pptr;
mod ex_set;
mod linked_list_box;
mod max_vec;
mod linked_list;
mod ex_map;


fn main() {
    max::test();
    binary_search::test();
    ext_i64::test();
    ex_seq::test();
    subseq::test();
    integers::test();
    pptr::test();
    max_vec::test();
    linked_list_box::test();
    linked_list::test();
}
