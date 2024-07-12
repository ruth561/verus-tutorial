use vstd::prelude::*;


verus! {

// memo: 外部からは実装の中身は見えないようにする
pub closed spec fn max(x: int, y: int) -> int
{
    if x <= y { y } else { x }
}

// memo: maxの仕様が満たしておいてほしい基本的な性質の証明
pub proof fn lem_max(x: int, y: int)
    ensures
        x <= max(x, y),
        y <= max(x, y),
        x == max(x, y) || y == max(x, y),
{}

// memo: テスト用（仕様を簡単にテストできるのありがたい）
proof fn test_max()
{
    assert(max(1, 2) == 2);
    assert(max(1, 1) == 1);
    assert(max(-1, 1) == 1);
}

// memo: 最大値を返す実体を持った関数
pub exec fn compute_max(x: i32, y: i32) -> (result: i32)
    ensures
        result as int == max(x as int, y as int),
{
    if x <= y { y } else { x }
}

} // verus!
