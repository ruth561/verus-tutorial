use vstd::prelude::*;


verus! {

// ExtIntとは通常の整数型に無限遠点を追加して拡張した数体系の型.
// 現時点では整数値としてi64を採用しているが、i32とかu64とかにも
// 対応したい.

#[derive(Debug, Copy, Clone)]
enum ExtInt {
    Inf,
    Int(i64),
}

impl ExtInt {

    // return true if lhs + rhs cause overflow
    pub closed spec fn spec_check_add_overflow(self: ExtInt, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if n1 + n2 > i64::MAX {
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    // オーバーフローを検知したらNoneを返す
    pub closed spec fn spec_checked_add(self, rhs: ExtInt) -> Option<ExtInt> {
        match (self, rhs) {
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => Some(ExtInt::Inf),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    Some(ExtInt::Int((n1 + n2) as i64))
                } else { // treat as INF when overflow occurs
                    None
                }
            }
        }
    }

    pub fn checked_add(self, rhs: ExtInt) -> (result: Option<ExtInt>)
        ensures
            result == self.spec_checked_add(rhs),
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => Some(ExtInt::Inf),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                match ex_i64_checked_add(n1, n2) {
                    Some(n) => Some(ExtInt::Int(n)),
                    None => None,
                }
            }
        }
    }
}

// == i64 methods ==
// This implementations refer to the implementations at the following URL
// https://github.com/verus-lang/verus/blob/23a5b86e270939935df5997f9d4c8b9fcb5fddda/source/vstd/std_specs/num.rs#L244-L364

// オーバーフローを検知してくれる関数
// このコードはTrustedをマークしている
#[verifier::external_body]
pub fn ex_i64_checked_add(lhs: i64, rhs: i64) -> (result: Option<i64>)
    ensures
        lhs + rhs > i64::MAX || lhs + rhs < i64::MIN ==> result.is_None(),
        i64::MIN <= lhs + rhs <= i64::MAX ==> result == Some((lhs + rhs) as i64),
{
    lhs.checked_add(rhs)
}

#[verifier::external_body]
pub fn test() {
    
    let inf = ExtInt::Inf;
    assert(inf.checked_add(inf) == inf);
    let n = ExtInt::Int(7);

    let mut x;
    let mut y;

    x = inf;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.checked_add(y));

    x = inf;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.checked_add(y));

    x = n;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.checked_add(y));

    x = n;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.checked_add(y));

    x = ExtInt::Int(i64::MAX);
    println!("{:?} + {:?} = {:?}", x, x, x.checked_add(x));
}

} // verus!
