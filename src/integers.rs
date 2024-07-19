use vstd::prelude::*;
use vstd::view::View;
use vstd::view::DeepView;


// 通常のi64やu32などの整数型はViewやDeepViewを自分自身としている。
// そのため、spec関数やproofなどでも境界条件に気を使わなければならず、
// コードが煩雑になってしまう。
// そこで、ViewやDeepViewがintとなるような整数型を用意してあげることで、
// Vec<I64>やVec<Vec<I64>>などといったデータ型のdeep_viewが
// Seq<int>やSeq<Seq<I64>>となるようにする。
//
// 仕様はSeq<int>などのオーバーフローフリーなghost型で記述し、
// 実際のexecコードはVec<I64>などで実装する。このとき、execコードでは
// 加算でオーバーフローが発生しないかどうか、などを検知しておき、
// オーバーフローが発生しなかったならばSeq<int>の仕様を満たす、といった
// アプローチをとる。

verus! {

#[derive(Debug, Clone, Copy)]
pub struct I64(pub i64);

impl View for I64 {
    type V = int;
    open spec fn view(&self) -> int {
        self.0 as int
    }
}

impl DeepView for I64 {
    type V = int;
    open spec fn deep_view(&self) -> int {
        self.0 as int
    }
}

// Addition
impl I64 {
    // オーバーフローを検知する加算
    pub fn checked_add(self, rhs: I64) -> (result: Option<I64>) 
        ensures
            self@ + rhs@ < i64::MIN || i64::MAX < self@ + rhs@ ==> result.is_none(),
            i64::MIN <= self@ + rhs@ <= i64::MAX ==> result.is_some() && result.unwrap()@ == self@ + rhs@
    {
        Some(I64(self.0.checked_add(rhs.0)?))
    }

    // (x + y) + z
    fn add3_l(x: I64, y: I64, z: I64) -> Option<I64>
    {
        x.checked_add(y)?.checked_add(z)
    }

    // x + (y + z)
    fn add3_r(x: I64, y: I64, z: I64) -> Option<I64> {
        x.checked_add(y.checked_add(z)?)
    }

    // 計算の順序によってオーバーフローが発生する場合はNoneを返す。
    // 一方、計算の順序によらずにオーバーフローが発生しない場合は、
    // その計算結果をSomeでくるんで返す。
    // (x + y) + z == x + (y + z)
    pub fn add3(x: I64, y: I64, z: I64) -> Option<I64> {
        let l = x.checked_add(y)?.checked_add(z)?;
        let r = x.checked_add(y.checked_add(z)?)?;
        assert(l@ == r@);
        Some(l)
    }
}

#[verifier::external]
pub fn test()
{
    let x = I64(-10);
    let y = I64(3);
    let z = I64(i64::MAX);
    println!("{:?} + {:?} = {:?}", x, y, x.checked_add(y));
    println!("{:?} + {:?} = {:?}", x, z, x.checked_add(z));
    println!("{:?} + {:?} = {:?}", y, z, y.checked_add(z));

    println!("({:?} + {:?}) + {:?} = {:?}", x, y, z, I64::add3_l(x, y, z));
    println!("{:?} + ({:?} + {:?}) = {:?}", x, y, z, I64::add3_r(x, y, z));
    println!("{:?} + {:?} + {:?} = {:?}", x, y, z, I64::add3(x, y, z));
}

} // verus!
