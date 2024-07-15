use vstd::prelude::*;


verus! {

proof fn test_equality() {
    let a: Seq<int> = seq![1, 3, 5, 7];
    let b: Seq<int> = seq![1, 3, 5, 7];
    let c: Seq<int> = Seq::<int>::new(4, |i:int| 2 * i + 1);
    let mut d: Seq<int> = Seq::<int>::empty();
    d = d.push(1);
    d = d.push(3);
    d = d.push(5);
    d = d.push(7); 

    assert(a == b); // succeeded: 同じ構築方法の場合はただちに等価
    // assert(a == c); // failed: 構築方法が異なると等価の判断ができない
    // assert(a == d); // failed: 構築方法が異なると等価の判断ができない

    // 等価であることを言うためには、外部等価であることをSMTソルバに教えてあげる必要がある
    assert(a =~= c);
    assert(a =~= d);
    assert(a == c);
    assert(a == d);
}

proof fn test_subrange() {
    let a: Seq<int> = seq![1, 3, 5, 7];
    assert(a.subrange(1, 3) =~= seq![3, 5]);
}

proof fn test_skip() {
    let a: Seq<int> = seq![1, 3, 5, 7, 9, 11, 13, 15, 17];
    assert(a.skip(5) =~= seq![11, 13, 15, 17]); // 先頭5要素を取り除いたsubseqを返す
}

#[verifier::external_body]
pub fn test() {
    println!("=== seq_ex ===");
}

} // verus!
