use std::cmp::Ordering;
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

    // is_int
    #[verifier::inline]
    pub open spec fn spec_is_int(&self) -> bool {
        is_variant(self, "Int")
    }

    #[verifier::when_used_as_spec(spec_is_int)]
    pub fn is_int(&self) -> (b: bool)
        ensures
            b == self.is_int(),
    {
        match *self {
            ExtInt::Int(_) => true,
            _ => false,
        }
    }

    // is_inf
    #[verifier::inline]
    pub open spec fn spec_is_inf(&self) -> bool {
        is_variant(self, "Inf")
    }

    #[verifier::when_used_as_spec(spec_is_inf)]
    pub fn is_inf(&self) -> (b: bool)
        ensures
            b == self.is_inf(),
    {
        match *self {
            ExtInt::Inf => true,
            _ => false,
        }
    }

    // unwrap
    #[verifier::inline]
    pub open spec fn spec_unwrap(&self) -> i64
        recommends
            self.is_int()
    {
        get_variant_field(self, "Int", "0")
    }

    #[verifier::when_used_as_spec(spec_unwrap)] // spec関数で使われたときはspec_unwrapが使われる
    pub fn unwrap(&self) -> (result: i64)
        requires
            self.is_int(),
        ensures
            result == self.unwrap(),
    {
        if let ExtInt::Int(n) = *self {
            n
        } else {
            // 本来、ここには到達しないのだが、unreachableなどの明示するためのツールがVerusでは
            // 未対応なため、assert(false)によって到達しないことを確認したのち、適当な値を返す実装になっている。
            assert(false);
            0
        }
    }

    // check_add_overflow
    //   - if *self + *rhs causes overflow, then return true
    //   - otherwise false
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

    #[verifier::when_used_as_spec(spec_check_add_overflow)]
    pub fn check_add_overflow(self, rhs: ExtInt) -> (b: bool)
        ensures
            b == self.check_add_overflow(rhs),
    {
        if let ExtInt::Int(n1) = self {
            if let ExtInt::Int(n2) = rhs {
                let n = n1.checked_add(n2);
                if n.is_none() {
                    return true;
                }
            }
        }
        false
    }

    // checked_add
    pub closed spec fn spec_checked_add(self, rhs: ExtInt) -> Option<ExtInt> {
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

    #[verifier::when_used_as_spec(spec_checked_add)]
    pub fn checked_add(self, rhs: ExtInt) -> (result: Option<ExtInt>)
        ensures
            result == self.checked_add(rhs),
            result.is_none() == self.check_add_overflow(rhs),
            result.is_some() ==> (result.unwrap().is_inf() <==> self.is_inf() || rhs.is_inf()),
            result.is_some() && result.unwrap().is_int() ==> (result.unwrap().unwrap() == self.unwrap() + rhs.unwrap()),
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => Some(ExtInt::Inf),
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                Some(ExtInt::Int(n1.checked_add(n2)?))
            }
        }
    }

    pub proof fn lem_checked_add(self, rhs: ExtInt)
        ensures
            self == ExtInt::Inf || rhs == ExtInt::Inf <==> self.checked_add(rhs) == Some(ExtInt::Inf),
            self.check_add_overflow(rhs) <==> self.checked_add(rhs) == None::<ExtInt>,
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

    // add
    pub closed spec fn spec_add(self, rhs: ExtInt) -> (n: ExtInt)
        recommends
            !self.check_add_overflow(rhs),
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => ExtInt::Inf,
            (_, ExtInt::Inf) => ExtInt::Inf,
            (n1, n2) => ExtInt::Int((n1.unwrap() + n2.unwrap()) as i64),
        }
    }

    #[verifier::when_used_as_spec(spec_add)]
    pub fn add(self, rhs: ExtInt) -> (n: ExtInt)
        requires
            !self.check_add_overflow(rhs),
        ensures
            self.checked_add(rhs) == Some(n),
    {
        match (self, rhs) {
            (ExtInt::Inf, _) => ExtInt::Inf,
            (_, ExtInt::Inf) => ExtInt::Inf,
            (n1, n2) => ExtInt::Int(n1.unwrap() + n2.unwrap()),
        }
    }

    // TODO: checked_sumを、exec関数ではVec<ExtInt>に対して、spec関数ではSeq<ExtInt>に対して
    // 行うようにしたい。ただ、#[verifier::when_used_as_spec(...)]は関数のシグネチャが異なってしまうため、
    // うまくできなさそう。

    // checked_sum
    pub open spec fn seq_checked_sum(seq: Seq<ExtInt>) -> Option<ExtInt>
        decreases seq.len(),
    {
        if seq.len() == 0 {
            Some(ExtInt::Int(0))
        } else {
            match ExtInt::seq_checked_sum(seq.drop_last()) {
                Some(s) => s.checked_add(seq[seq.len()-1]),
                None => None,
            }
        }
    }

    pub fn vec_checked_sum(v: &Vec<ExtInt>) -> (result: Option<ExtInt>)
        ensures
            result == ExtInt::seq_checked_sum(v@),
    {
        let mut i = 0;
        let mut ans = Some(ExtInt::Int(0));
        while i < v.len()
            invariant
                i <= v.len() as int,
                ans == ExtInt::seq_checked_sum(v@.subrange(0, i as int)),
        {
            // seq_checked_sumの中で使われる外部等価性を提示してあげる必要がある。
            assert(v@.subrange(0, i as int) =~= v@.subrange(0, (i+1) as int).drop_last());
            if let Some(s) = ans {
                ans = s.checked_add(v[i]);
            }
            i += 1;
        }
        assert(v@.subrange(0, v.len() as int) =~= v@);
        ans
    }

}

// proof関数を実装していく場所
impl ExtInt {

    // rhsの符号に応じて加算結果の大小関係が変わる
    proof fn lem_add_and_cmp(self, rhs: ExtInt)
        requires
            !self.check_add_overflow(rhs),
        ensures
            rhs <  ExtInt::Int(0) ==> self.add(rhs) <= self,
            rhs >  ExtInt::Int(0) ==> self.add(rhs) >= self,
            rhs == ExtInt::Int(0) ==> self.add(rhs) == self,
    {}

    // 数列内にInfが1つもなく、checked_sumが何かしらの値を返すならば、その値はintである。
    proof fn lem_sum_of_all_int_seq_is_int(seq: Seq<ExtInt>)
        requires
            forall|i:int| 0 <= i < seq.len() ==> seq[i].is_int(),
            ExtInt::seq_checked_sum(seq).is_some(),
        ensures
            ExtInt::seq_checked_sum(seq).unwrap().is_int(),
        decreases
            seq.len(),
    {
        if seq.len() == 0 {
        } else {
            ExtInt::lem_sum_of_all_int_seq_is_int(seq.drop_last());
        }
    }

    // 列の中にInfが１つでもあれば、合計値もInfになる。
    proof fn lem_sum_of_seq_with_inf_is_inf(seq: Seq<ExtInt>)
        requires
            exists|i:int| 0 <= i < seq.len() && seq[i].is_inf(),
            ExtInt::seq_checked_sum(seq).is_some(),
        ensures
            ExtInt::seq_checked_sum(seq).unwrap().is_inf(),
        decreases
            seq.len(),
    {
        if seq.len() == 0 {
            // infの存在条件から-seq.len() == 0 となることはない
            assert(false);
        } else {
            let i = choose|i:int| 0 <= i < seq.len() && seq[i].is_inf();
            if i < seq.len() - 1 {
                assert(0 <= i < seq.drop_last().len() && seq.drop_last()[i].is_inf());
                assert(exists|i:int| #![auto] 0 <= i < seq.drop_last().len() && seq.drop_last()[i].is_inf());
                ExtInt::lem_sum_of_seq_with_inf_is_inf(seq.drop_last());
            }
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

// i64::checked_add(self, i64) 関数に仕様を追加する宣言
// オーバーフローを検知してくれる関数
// このコードはTrustedをマークしている
#[verifier::external_fn_specification]
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
    assert(a.checked_add(b) == Some(ExtInt::Inf));
    assert(b.checked_add(b) == Some(ExtInt::Int(2000)));
    assert(b.checked_add(b) == Some(ExtInt::Int(2000)));

    assert(ExtInt::Int(0) < ExtInt::Inf);
    assert(ExtInt::Int(0) < ExtInt::Int(1));
    assert(ExtInt::Int(1) <= ExtInt::Int(1));
    assert(ExtInt::Inf <= ExtInt::Inf);

    assert(b < a);
}

proof fn test_spec_2() {
    let inf = ExtInt::Inf;
    let num = ExtInt::Int(123);

    assert(!inf.is_int());
    assert( inf.is_inf());
    assert( num.is_int());
    assert(!num.is_inf());
    assert(num.unwrap() == 123);
}

proof fn test_spec_3() {
    let n = ExtInt::Int(i64::MAX);

    let m = n + n;
    assert(m.is_int());
}

fn test_exec() {
    let n = ExtInt::Int(1000);
    let m = n.add(n);
    assert(n < m);

    let x = ExtInt::Int(i64::MAX);
    // x.add(x); // オーバーフローの可能性は検証器が見つけてくれる。
}

fn test_exec_3() {
    let mut v = Vec::new();
    v.push(ExtInt::Int(2));
    v.push(ExtInt::Int(3));
    v.push(ExtInt::Int(5));
    
    reveal_with_fuel(ExtInt::seq_checked_sum, 4);
    let ans = ExtInt::vec_checked_sum(&v);
    assert(ans.is_some());
    assert(ans.unwrap() == ExtInt::Int(10));
}

fn test_exec_4() {
    let mut v = Vec::new();
    v.push(ExtInt::Int(2));
    v.push(ExtInt::Int(3));
    v.push(ExtInt::Int(5));

    let n = ExtInt::vec_checked_sum(&v);
    reveal_with_fuel(ExtInt::seq_checked_sum, 4);
    assert(n.is_some());
    proof { ExtInt::lem_sum_of_all_int_seq_is_int(v@); }
    assert(n.unwrap().is_int());

    v.push(ExtInt::Inf);
    v.push(ExtInt::Int(7));

    let n = ExtInt::vec_checked_sum(&v);
    reveal_with_fuel(ExtInt::seq_checked_sum, 10);
    assert(n.is_some());
    proof { ExtInt::lem_sum_of_seq_with_inf_is_inf(v@); }
    assert(n.unwrap().is_inf());
}

#[verifier::external_body]
pub fn test() {
    let inf = ExtInt::Inf;
    let n = ExtInt::Int(7);

    let mut x;
    let mut y;

    x = inf;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = inf;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    let a = ExtInt::Inf;
    let b = ExtInt::Int(1000);
    if a < b {
        println!("a is less than b");
    } else {
        println!("a is not less than b");
    }

    println!("{}.is_int() = {}", a, a.is_int());
    println!("{}.is_int() = {}", b, b.is_int());
    println!("{}.is_inf() = {}", a, a.is_inf());
    println!("{}.is_inf() = {}", b, b.is_inf());
    println!("{}.unwrap() = {}", b, b.unwrap());

    let mut v = Vec::new();
    v.push(ExtInt::Int(2));
    v.push(ExtInt::Int(3));
    v.push(ExtInt::Int(5));
    let ans = ExtInt::vec_checked_sum(&v).unwrap();
    println!("sum of {:?} is {:?}", v, ans);
    v.push(ExtInt::Inf);
    v.push(ExtInt::Int(7));
    let ans = ExtInt::vec_checked_sum(&v).unwrap();
    println!("sum of {:?} is {:?}", v, ans);
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
