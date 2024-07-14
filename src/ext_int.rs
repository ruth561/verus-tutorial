use std::cmp::Ordering;
use std::ops::Add;
use std::fmt;

use vstd::prelude::*;


verus! {

// ExtIntとは通常の整数型に無限遠点を追加して拡張した数体系の型.
// 現時点では整数値としてi64を採用しているが、i32とかu64とかにも
// 対応したい.

#[derive(Debug, Copy, Clone)]
enum ExtInt {
    Int(i64),
    Inf,
    Overflow, // overflowed
}

impl ExtInt {

    pub closed spec fn is_overflow(self) -> bool {
        self == ExtInt::Overflow
    }

    // self + rhs がオーバーフローを引き起こすときはtrueを返す
    // return true iff lhs + rhs cause overflow
    pub closed spec fn spec_check_add_overflow(self, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Overflow, _) => true,
            (_, ExtInt::Overflow) => true,
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

    pub closed spec fn spec_add(self, rhs: ExtInt) -> ExtInt {
        match (self, rhs) {
            (ExtInt::Overflow, _) => ExtInt::Overflow,
            (_, ExtInt::Overflow) => ExtInt::Overflow,
            (ExtInt::Inf, _) => ExtInt::Inf,
            (_, ExtInt::Inf) => ExtInt::Inf,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    ExtInt::Int((n1 + n2) as i64)
                } else {
                    ExtInt::Overflow
                }
            }
        }
    }

    pub closed spec fn spec_lt(self, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Overflow, _) => false,
            (_, ExtInt::Overflow) => false,
            (ExtInt::Inf, ExtInt::Inf) => false,
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => true,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                n1 < n2
            }
        }
    }

}

impl Add for ExtInt {
    type Output = ExtInt;
    fn add(self, rhs: Self) -> (result: Self::Output)
        ensures
            result == self.spec_add(rhs),
    {
        match (self, rhs) {
            (ExtInt::Overflow, _) => ExtInt::Overflow,
            (_, ExtInt::Overflow) => ExtInt::Overflow,
            (ExtInt::Inf, _) => ExtInt::Inf,
            (_, ExtInt::Inf) => ExtInt::Inf,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                match ex_i64_checked_add(n1, n2) {
                    Some(n) => ExtInt::Int(n),
                    None => ExtInt::Overflow,
                }
            }
        }
    }
}

impl PartialEq for ExtInt {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (ExtInt::Overflow, _) => false,
            (_, ExtInt::Overflow) => false,
            (ExtInt::Inf, ExtInt::Inf) => true,
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => false,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                n1.eq(&n2)
            }
        }
    }
}

proof fn ext_int_cmp_inf(en1: ExtInt, en2: ExtInt)
    requires
        en1 == ExtInt::Inf,
        en1 < en2,
    // ensures
        // en2 == ExtInt::Inf,
{}


impl Eq for ExtInt {}

#[verifier::external_type_specification]
pub struct ExOrdering(Ordering);

// #[verifier::external]
impl PartialOrd for ExtInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (*self, *other) {
            (ExtInt::Overflow, _) => None,
            (_, ExtInt::Overflow) => None,
            (ExtInt::Inf, ExtInt::Inf) => Some(Ordering::Equal),
            (ExtInt::Inf, _) => Some(Ordering::Greater),
            (_, ExtInt::Inf) => Some(Ordering::Less),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                if n1 == n2 {
                    Some(Ordering::Equal)
                } else if n1 < n2 {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }
        }
    }
}

impl Ord for ExtInt {
    fn cmp(&self, other: &Self) -> Ordering {
        Ordering::Equal
    }
}

// impl core::cmp::Ord for int {
//     fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
//         unimplemented!()
//     }
// }

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

proof fn trait_test()
{
    let a = ExtInt::Inf;
    let b = ExtInt::Int(1000);
    assert(a.spec_add(b) == ExtInt::Inf);
    assert(b.spec_add(b) == ExtInt::Int(2000));
    assert(b + b == ExtInt::Int(2000));

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
    println!("{} + {} = {}", x, y, x + y);
    println!("{} < {} = {}", x, y, x < y);

    x = inf;
    y = n;
    println!("{} + {} = {}", x, y, x + y);
    println!("{} < {} = {}", x, y, x < y);

    x = n;
    y = inf;
    println!("{} + {} = {}", x, y, x + y);
    println!("{} < {} = {}", x, y, x < y);

    x = n;
    y = n;
    println!("{} + {} = {}", x, y, x + y);
    println!("{} < {} = {}", x, y, x < y);

    x = ExtInt::Int(i64::MAX);
    println!("{} + {} = {}", x, x, x + x);
    println!("{} < {} = {}", x, y, x < y);

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
            ExtInt::Overflow => write!(f, "Overflow"),
        }
    }
}
