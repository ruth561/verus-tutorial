// Usage Examples of forall
use vstd::prelude::*;


verus! {

// forall周りの挙動でよくわからない部分があるので、そこら辺の実行を試すもの

// forallから取り出すことができない例を探す。
pub open spec fn pow2(n: int) -> int { n * n }
pub open spec fn pow3(n: int) -> int { n * n * n }

// 平方数かつ立法数（例えば64など）
pub open spec fn property(i: int) -> bool {
    &&& exists|k:int| i == #[trigger] pow2(k)
    &&& exists|k:int| i == #[trigger] pow3(k)
}

proof fn lem_property(i: int)
    requires
        property(i),
    ensures
        exists|k:int| i == #[trigger] pow2(k),
{}

proof fn example() {
    assert(64 == pow2(8));
    assert(64 == pow3(4));
    assert(property(64));
    assert(exists|i:int| property(i));
}

pub open spec fn property2(a: Seq<int>) -> bool {
    forall|i:int| 0 < i < a.len() ==>  #[trigger] a[i-1] < a[i]
}

pub open spec fn property3(a: Seq<int>, n: int) -> bool {
    forall|i:int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] < n
}

pub open spec fn property4(a: Seq<int>, n: int) -> bool {
    &&& property2(a)
    &&& property3(a, n)
}

proof fn example4(n: int)
    requires
        exists|a:Seq<int>| property4(a, n),
{
    let a = choose|a:Seq<int>| property4(a, n);

    assert(property4(a, n));
    assert(property2(a));
    assert(property3(a, n));
}

use crate::strictly_increasing_sequence::*;

// 以下のように`property5`で囲ってあげると証明ができるが、
// 囲ってあげないと証明できない。
pub open spec fn property5(i:int, a:Seq<int>, s: Seq<int>, t: Seq<int>) -> bool {
    0 <= a[i] < t.len() && s[i] == t[a[i]]
}

pub open spec fn is_index_of_subseq(a: Seq<int>, s: Seq<int>, t: Seq<int>) -> bool {
    &&& a.len() == s.len()
    &&& strictly_increasing_sequence(a)
    &&& forall|i:int| 0 <= i < a.len() ==> property5(i, a, s, t)
}

proof fn lem_is_index_of_subseq(a: Seq<int>, s: Seq<int>, t: Seq<int>)
    requires
        is_index_of_subseq(a, s, t),
    ensures
        forall|i:int| 0 <= i < a.len() ==> property5(i, a, s, t),
{
    assert forall|i:int| 0 <= i < a.len() implies 0 <= a[i] < t.len() && s[i] == #[trigger] t[a[i]] by {
        assert(property5(i, a, s, t));
    }
}

} // verus!
