use vstd::prelude::*;


// Verusでは `i64` の `View` も `DeepView` も `i64` 自体となっている。
// これは、`i64` のデータを扱うならその値には境界条件があることを
// 忘れないようにする、という狙いがある。
//
// `i64` の値 `v` が `int` で定義された仕様 `property(int) -> bool` 
// を満たす、といった記述をしたいときは `property(v as int)` のように
// すればいい。
//
// しかし、`Vec<i64>` のような型の場合、そこから `Seq<int>` をモデルと
// して採用することは通常のやり方ではできない。これは `DeepView` が
// `Seq<i64>` のようになってしまうからだ。
//
// ただし、`Vec<i64>` を `Seq<int>` として扱いたいときはある。
// そのようなときは、ここで定義している `as_spec_int` のようなヘルパー
// 関数を利用するとよい。

verus! {

pub open spec fn spec_sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s.last() + spec_sum(s.drop_last())
    }
}

pub open spec fn as_seq_int(v: Vec<i64>) -> Seq<int> {
    v.view().map_values(|x| x as int)
}

fn checked_sum(v: &Vec<i64>) -> (result: Option<i64>)
    ensures
        result.is_some() ==> result.unwrap() == spec_sum(as_seq_int(*v)),
{
    let mut result = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result == spec_sum(as_seq_int(*v).subrange(0, i as int)),
    {
        result = v[i].checked_add(result)?;
        i += 1;
        assert(as_seq_int(*v).subrange(0, i as int).drop_last() == as_seq_int(*v).subrange(0, i as int - 1));
    }
    assert(as_seq_int(*v).subrange(0, v.len() as int) == as_seq_int(*v));
    Some(result)
}

} // verus!
