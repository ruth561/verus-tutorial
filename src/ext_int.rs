use std::cmp::Ordering;
use std::ops::Add;
use std::fmt;

use vstd::prelude::*;


verus! {

// ExtIntとは通常の整数型に無限遠点を追加して拡張した数体系の型.
// 現時点では整数値としてi64を採用しているが、i32とかu64とかにも
// 対応したい.

#[derive(Debug, Copy, Clone)]
pub enum ExtInt {
    Int(i64),
    Inf,
}

#[derive(Debug, Copy, Clone)]
pub enum ResultExtInt {
    Ok(ExtInt),
    Overflow,
}

impl ExtInt {

    // self + rhs がオーバーフローを引き起こすときはtrueを返す
    // return true iff lhs + rhs cause overflow
    pub closed spec fn spec_check_add_overflow(self, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => false,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    false
                } else {
                    true
                }
            }
        }
    }

    pub closed spec fn spec_checked_add(self, rhs: ExtInt) -> Option<ExtInt>
        recommends
            !self.spec_check_add_overflow(rhs)
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => Some(ExtInt::Inf),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    Some(ExtInt::Int((n1 + n2) as i64))
                } else {
                    None
                }
            }
        }
    }

    pub proof fn lem_checked_add(self, rhs: ExtInt)
        ensures
            self == ExtInt::Inf || rhs == ExtInt::Inf <==> self.spec_checked_add(rhs) == Some(ExtInt::Inf),
            self.spec_check_add_overflow(rhs) <==> self.spec_checked_add(rhs) == None::<ExtInt>,
    {}

    pub closed spec fn spec_lt(self, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Inf, ExtInt::Inf) => false,
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => true,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                n1 < n2
            }
        }
    }

    pub closed spec fn spec_le(self, rhs: ExtInt) -> bool {
        self.spec_lt(rhs) || self == rhs
    }

    pub closed spec fn spec_gt(self, rhs: ExtInt) -> bool {
        !self.spec_le(rhs)
    }

    pub closed spec fn spec_ge(self, rhs: ExtInt) -> bool {
        !self.spec_lt(rhs)
    }

    // オーバーフローを検査する加算
    pub fn checked_add(self, rhs: ExtInt) -> (result: Option<ExtInt>)
        ensures
            result == self.spec_checked_add(rhs),
            self.spec_check_add_overflow(rhs) <==> result == None::<ExtInt>,
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => Some(ExtInt::Inf),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                Some(ExtInt::Int(ex_i64_checked_add(n1, n2)?))
            }
        }
    }

}

impl Add for ExtInt {
    type Output = ResultExtInt;
    fn add(self, rhs: Self) -> Self::Output {
        match self.checked_add(rhs) {
            Some(n) => ResultExtInt::Ok(n),
            None => ResultExtInt::Overflow,
        }
    }
}

impl PartialEq for ExtInt {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (ExtInt::Inf, ExtInt::Inf) => true,
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => false,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                n1 == n2
            }
        }
    }
}

impl Eq for ExtInt {}

// VerusのソースにもExOrderingが定義されているが、そのExOrderingは
// core::sync::atomic::Orderingの方を言及しており、std::cmp::Ordering
// の方ではないため、ここで定義する必要がある。
#[verifier::external_type_specification]
pub struct ExOrdering(Ordering);

impl PartialOrd for ExtInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExtInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (*self, *other) {
            (ExtInt::Inf, ExtInt::Inf) => Ordering::Equal,
            (ExtInt::Inf, _) => Ordering::Greater,
            (_, ExtInt::Inf) => Ordering::Less,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if n1 == n2 {
                    Ordering::Equal
                } else if n1 < n2 {
                    Ordering::Less
                } else {
                    Ordering::Greater
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

proof fn test_spec()
{
    let a = ExtInt::Inf;
    let b = ExtInt::Int(1000);
    assert(a.spec_checked_add(b) == Some(ExtInt::Inf));
    assert(b.spec_checked_add(b) == Some(ExtInt::Int(2000)));
    assert(b.spec_checked_add(b) == Some(ExtInt::Int(2000)));

    assert(ExtInt::Int(0) < ExtInt::Inf);
    assert(ExtInt::Int(0) < ExtInt::Int(1));
    assert(ExtInt::Int(1) <= ExtInt::Int(1));
    assert(ExtInt::Inf <= ExtInt::Inf);

    assert(b < a);
}

#[verifier::external_body]
pub fn test() {
    let inf = ExtInt::Inf;
    let n = ExtInt::Int(7);

    let mut x;
    let mut y;

    x = inf;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x + y);
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = inf;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x + y);
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x + y);
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x + y);
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = ExtInt::Int(i64::MAX);
    println!("{:?} + {:?} = {:?}", x, x, x + x);
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    let a = ExtInt::Inf;
    let b = ExtInt::Int(1000);
    if a < b {
        println!("a is less than b");
    } else {
        println!("a is not less than b");
    }
}

} // verus!

impl fmt::Display for ExtInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExtInt::Int(n) => write!(f, "{}", *n),
            ExtInt::Inf => write!(f, "∞"),
        }
    }
}
