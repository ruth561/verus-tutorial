// Usage Examples of Set
use vstd::prelude::*;


verus! {

proof fn test_full()
{
    // 整数全体からなる集合を定義
    let s = Set::<int>::full();
    assert(forall|n:int| s.contains(n));
}

proof fn test_new()
{
    // 偶数からなる集合を定義
    let s = Set::<int>::new(|n:int| n % 2 == 0);
    assert( s.contains(4));
    assert(!s.contains(5));
}

proof fn test_choose()
{
    // 集合の要素から任意に1つの要素を取ってくる処理
    // evens.choose()という風にとってくることも可能だが、
    // verus-analyzerがエラーを表示してしまうため、以下のような
    // chooseを用いた書き方になっている。
    let evens = Set::<int>::new(|n:int| n % 2 == 0);
    assert(evens.contains(2));
    let n = choose|n:int| evens.contains(n);
    assert(n % 2 == 0);
}

proof fn test_intersect()
{
    // 偶数の集合と奇数の集合の積は空集合
    let evens = Set::<int>::new(|n:int| n % 2 == 0);
    let  odds = Set::<int>::new(|n:int| n % 2 == 1);
    assert(evens.intersect(odds) =~= Set::<int>::empty());
    assert(evens.intersect(odds).len() == 0);
}

} // verus!
