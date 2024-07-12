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

trait SeqIntegersMax<T> {
    spec fn get_max(&self) -> T;

    proof fn get_max_ensures(&self);
}

impl SeqIntegersMax<i32> for Seq<i32> {
    spec fn get_max(&self) -> i32
        decreases self.len(),
    {
        if self.len() == 1 {
            self[0]
        } else if self.len() == 0 {
            i32::MIN // 空の場合はデフォルト値的なものを返す？
        } else {
            let later_max = self.drop_first().get_max();
            if self[0] >= later_max {
                self[0]
            } else {
                later_max
            }
        }
    }

    proof fn get_max_ensures(&self)
        ensures
            forall|i:int| 0 <= i < self.len() ==> self[i] <= self.get_max(),
        decreases self.len(),
    {
        if self.len() == 1 {
            assert(self[0] == self.get_max());
            assert(forall|i:int| 0 <= i < self.len() ==> self[i] <= self.get_max());
        } else if self.len() == 0 {
            assert(self.get_max() == i32::MIN);
            assert(forall|i:int| 0 <= i < self.len() ==> self[i] <= self.get_max());
        } else {
            assert(2 <= self.len());
            let later_max = self.drop_first().get_max();
            self.drop_first().get_max_ensures();
            assert forall|i:int| 0 <= i < self.len() ==> self[i] <= later_max by {
                i == 0 || self[i] == self.drop_first()[i - 1];
                assert(forall|j: int|
                    0 <= j < self.drop_first().len() ==> self.drop_first()[j] <= later_max) by { self.drop_first().get_max_ensures() }
            };
        }
        assume(false);
    }
}

pub fn max_test()
{
    let mut v = Vec::new();
    v.push(2);
    v.push(3);
    v.push(5);
    v.push(7);
    v.push(11);
    v.push(1);
    v.push(4);
    v.push(6);
    v.push(8);
    v.push(9);
    
    assert(v[2] == 5);
    assert(v@.subrange(2, 4) =~= seq![5, 7]);
    assert(v.view().len() == 10); // この2つは
    assert(v@.len() == 10);       // 等価？？？
    assert(v@[0] == 2);
    // assert(v@.max() == 11);
}

} // verus!
