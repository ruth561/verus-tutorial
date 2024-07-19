use std::cmp::Ordering;
use std::fmt;

use vstd::prelude::*;


verus! {

// ExtI64とは通常の整数型に無限遠点を追加して拡張した数体系の型.
// 現時点では整数値としてi64を採用しているが、i32とかu64とかにも
// 対応したい.

#[derive(Debug, Copy, Clone)]
pub enum ExtI64 {
    Int(i64),
    Inf,
}

#[derive(Debug, Copy, Clone)]
pub enum ResultExtI64 {
    Ok(ExtI64),
    Overflow,
}

impl ExtI64 {

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
            ExtI64::Int(_) => true,
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
            ExtI64::Inf => true,
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
        if let ExtI64::Int(n) = *self {
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
    pub open spec fn spec_check_add_overflow(self, rhs: ExtI64) -> bool {
        match (self, rhs) {
            (ExtI64::Inf, _) => false,
            (_, ExtI64::Inf) => false,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    false
                } else {
                    true
                }
            }
        }
    }

    #[verifier::when_used_as_spec(spec_check_add_overflow)]
    pub fn check_add_overflow(self, rhs: ExtI64) -> (b: bool)
        ensures
            b == self.check_add_overflow(rhs),
    {
        if let ExtI64::Int(n1) = self {
            if let ExtI64::Int(n2) = rhs {
                let n = n1.checked_add(n2);
                if n.is_none() {
                    return true;
                }
            }
        }
        false
    }

    // checked_add
    pub closed spec fn spec_checked_add(self, rhs: ExtI64) -> Option<ExtI64> {
        match (self, rhs) {
            (ExtI64::Inf, _) => Some(ExtI64::Inf),
            (_, ExtI64::Inf) => Some(ExtI64::Inf),
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                if i64::MIN <= n1 + n2 <= i64::MAX {
                    Some(ExtI64::Int((n1 + n2) as i64))
                } else {
                    None
                }
            }
        }
    }

    #[verifier::when_used_as_spec(spec_checked_add)]
    pub fn checked_add(self, rhs: ExtI64) -> (result: Option<ExtI64>)
        ensures
            result == self.checked_add(rhs),
            result.is_none() == self.check_add_overflow(rhs),
            result.is_some() ==> (result.unwrap().is_inf() <==> self.is_inf() || rhs.is_inf()),
            result.is_some() && result.unwrap().is_int() ==> (result.unwrap().unwrap() == self.unwrap() + rhs.unwrap()),
    {
        match (self, rhs) {
            (ExtI64::Inf, _) => Some(ExtI64::Inf),
            (_, ExtI64::Inf) => Some(ExtI64::Inf),
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                Some(ExtI64::Int(n1.checked_add(n2)?))
            }
        }
    }

    pub proof fn lem_checked_add(self, rhs: ExtI64)
        ensures
            self == ExtI64::Inf || rhs == ExtI64::Inf <==> self.checked_add(rhs) == Some(ExtI64::Inf),
            self.check_add_overflow(rhs) <==> self.checked_add(rhs) == None::<ExtI64>,
    {}

    pub open spec fn spec_lt(self, rhs: ExtI64) -> bool {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => false,
            (ExtI64::Inf, _) => false,
            (_, ExtI64::Inf) => true,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                n1 < n2
            }
        }
    }

    pub open spec fn spec_le(self, rhs: ExtI64) -> bool {
        self.spec_lt(rhs) || self == rhs
    }

    pub open spec fn spec_gt(self, rhs: ExtI64) -> bool {
        !self.spec_le(rhs)
    }

    pub open spec fn spec_ge(self, rhs: ExtI64) -> bool {
        !self.spec_lt(rhs)
    }

    // add
    pub open spec fn spec_add(self, rhs: ExtI64) -> (n: ExtI64)
        recommends
            !self.check_add_overflow(rhs),
    {
        match (self, rhs) {
            (ExtI64::Inf, _) => ExtI64::Inf,
            (_, ExtI64::Inf) => ExtI64::Inf,
            (n1, n2) => ExtI64::Int((n1.unwrap() + n2.unwrap()) as i64),
        }
    }

    #[verifier::when_used_as_spec(spec_add)]
    pub fn add(self, rhs: ExtI64) -> (n: ExtI64)
        requires
            !self.check_add_overflow(rhs),
        ensures
            self.checked_add(rhs) == Some(n),
    {
        match (self, rhs) {
            (ExtI64::Inf, _) => ExtI64::Inf,
            (_, ExtI64::Inf) => ExtI64::Inf,
            (n1, n2) => ExtI64::Int(n1.unwrap() + n2.unwrap()),
        }
    }

    // check_sub_overflow
    //   - if self - rhs causes overflow, then return true
    //   - otherwise false
    //
    // Causing overflow cases are
    //   - inf - inf
    //   - int - inf
    //   - int - int 
    pub open spec fn spec_check_sub_overflow(self, rhs: ExtI64) -> bool {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => true,
            (ExtI64::Inf, _) => false,
            (_, ExtI64::Inf) => true,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                if i64::MIN <= n1 - n2 <= i64::MAX {
                    false
                } else {
                    true
                }
            }
        }
    }

    #[verifier::when_used_as_spec(spec_check_sub_overflow)]
    pub fn check_sub_overflow(self, rhs: ExtI64) -> (b: bool)
        ensures
            b == self.check_sub_overflow(rhs),
    {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => true,
            (ExtI64::Inf, _) => false,
            (_, ExtI64::Inf) => true,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                let n = n1.checked_sub(n2);
                if n.is_none() {
                    true
                } else {
                    false
                }
            }
        }
    }

    // checked_sub
    pub open spec fn spec_checked_sub(self, rhs: ExtI64) -> Option<ExtI64> {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => None,
            (ExtI64::Inf, _) => Some(ExtI64::Inf),
            (_, ExtI64::Inf) => None,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                if i64::MIN <= n1 - n2 <= i64::MAX {
                    Some(ExtI64::Int((n1 - n2) as i64))
                } else {
                    None
                }
            }
        }
    }

    #[verifier::when_used_as_spec(spec_checked_sub)]
    pub fn checked_sub(self, rhs: ExtI64) -> (result: Option<ExtI64>)
        ensures
            result == self.checked_sub(rhs),
            result.is_none() == self.check_sub_overflow(rhs),
            result.is_some() ==> (result.unwrap().is_inf() <==> self.is_inf()),
            result.is_some() && result.unwrap().is_int() ==> (result.unwrap().unwrap() == self.unwrap() - rhs.unwrap()),
    {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => None,
            (ExtI64::Inf, _) => Some(ExtI64::Inf),
            (_, ExtI64::Inf) => None,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                Some(ExtI64::Int(n1.checked_sub(n2)?))
            }
        }
    }

    // sub
    pub open spec fn spec_sub(self, rhs: ExtI64) -> (n: ExtI64)
        recommends
            !self.check_sub_overflow(rhs),
    {
        // unreachable!()のような機能が使えないため、unreachableなコードに対してはこの値をIntで
        // くるんだ値を返すようにしている。
        let invalid_ext_int = ExtI64::Int((i64::MIN - 1) as i64);
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Inf) => invalid_ext_int,
            (ExtI64::Inf, _) => ExtI64::Inf,
            (_, ExtI64::Inf) => invalid_ext_int,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => ExtI64::Int((n1 - n2) as i64),
        }
    }

    #[verifier::when_used_as_spec(spec_sub)]
    pub fn sub(self, rhs: ExtI64) -> (n: ExtI64)
        requires
            !self.check_sub_overflow(rhs),
        ensures
            self.checked_sub(rhs) == Some(n),
    {
        match (self, rhs) {
            (ExtI64::Inf, ExtI64::Int(_)) => ExtI64::Inf,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => ExtI64::Int(n1 - n2),
            _ => {
                assert(false); // unreachable!()
                ExtI64::Int(i64::MIN)
            }
        }
    }

    // TODO: checked_sumを、exec関数ではVec<ExtI64>に対して、spec関数ではSeq<ExtI64>に対して
    // 行うようにしたい。ただ、#[verifier::when_used_as_spec(...)]は関数のシグネチャが異なってしまうため、
    // うまくできなさそう。

    // checked_sum
    pub open spec fn seq_checked_sum(seq: Seq<ExtI64>) -> Option<ExtI64>
        decreases seq.len(),
    {
        if seq.len() == 0 {
            Some(ExtI64::Int(0))
        } else {
            match ExtI64::seq_checked_sum(seq.drop_last()) {
                Some(s) => s.checked_add(seq[seq.len()-1]),
                None => None,
            }
        }
    }

    // sumでオーバーフローが発生するかどうか（オーバーフローするときにtrueを返す）
    // 健全なアプローチ
    pub open spec fn seq_check_sum_overflow(seq: Seq<ExtI64>) -> bool {
        let not_overflow =
            seq.len() <= i32::MAX &&
            forall|i:int| 0 <= i < seq.len() ==>
                seq[i].is_inf() || (seq[i].is_int() && i32::MIN <= seq[i].unwrap() <= i32::MAX);
        !not_overflow
    }

    pub fn vec_checked_sum(v: &Vec<ExtI64>) -> (result: Option<ExtI64>)
        ensures
            result == ExtI64::seq_checked_sum(v@),
    {
        let mut i = 0;
        let mut ans = Some(ExtI64::Int(0));
        while i < v.len()
            invariant
                i <= v.len() as int,
                ans == ExtI64::seq_checked_sum(v@.subrange(0, i as int)),
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

    // オーバーフローしないsum
    pub fn vec_sum(v: &Vec<ExtI64>) -> (result: ExtI64)
        requires
            !ExtI64::seq_check_sum_overflow(v@),
        ensures
            Some(result) == ExtI64::seq_checked_sum(v@),
    {
        assert(v.len() <= i32::MAX);

        let mut i = 0;
        let mut ans = ExtI64::Int(0);
        while i < v.len()
            invariant
                !ExtI64::seq_check_sum_overflow(v@),
                0 <= i <= v.len() as int,
                ans.is_inf() || i * i32::MIN <= ans.unwrap() <= i * i32::MAX,
                Some(ans) == ExtI64::seq_checked_sum(v@.subrange(0, i as int)),
        {
            // seq_checked_sumの中で使われる外部等価性を提示してあげる必要がある。
            assert(v@.subrange(0, i as int) =~= v@.subrange(0, (i+1) as int).drop_last());
            
            if ans.is_inf() {
                ans = ans.add(v[i]);
                assert(ans.is_inf());
            } else {
                if v[i].is_int() {
                    proof {
                        let m = ans.unwrap();
                        let k = v[i as int].unwrap();
                        assert(i * i32::MIN <= m <= i * i32::MAX);
                        assert(v.len() <= i32::MAX);
                        assert(0 <= i <= i32::MAX - 1);
                        assert((i32::MAX - 1) * i32::MIN <= m <= (i32::MAX - 1) * i32::MAX);
                        assert(i32::MIN <= k <= i32::MAX);
                        assert(i32::MAX * i32::MIN <= m + k <= i32::MAX * i32::MAX);
                    }
                }
                ans = ans.add(v[i]);
            }
            i += 1;
        }
        assert(v@.subrange(0, v.len() as int) =~= v@);
        ans
    }

}

// proof関数を実装していく場所
impl ExtI64 {

    // rhsの符号に応じて加算結果の大小関係が変わる
    proof fn lem_add_and_cmp(self, rhs: ExtI64)
        requires
            !self.check_add_overflow(rhs),
        ensures
            rhs <  ExtI64::Int(0) ==> self.add(rhs) <= self,
            rhs >  ExtI64::Int(0) ==> self.add(rhs) >= self,
            rhs == ExtI64::Int(0) ==> self.add(rhs) == self,
    {}

    // 数列内にInfが1つもなく、checked_sumが何かしらの値を返すならば、その値はintである。
    proof fn lem_sum_of_all_int_seq_is_int(seq: Seq<ExtI64>)
        requires
            forall|i:int| 0 <= i < seq.len() ==> seq[i].is_int(),
            ExtI64::seq_checked_sum(seq).is_some(),
        ensures
            ExtI64::seq_checked_sum(seq).unwrap().is_int(),
        decreases
            seq.len(),
    {
        if seq.len() == 0 {
        } else {
            ExtI64::lem_sum_of_all_int_seq_is_int(seq.drop_last());
        }
    }

    // 列の中にInfが１つでもあれば、合計値もInfになる。
    proof fn lem_sum_of_seq_with_inf_is_inf(seq: Seq<ExtI64>)
        requires
            exists|i:int| 0 <= i < seq.len() && seq[i].is_inf(),
            ExtI64::seq_checked_sum(seq).is_some(),
        ensures
            ExtI64::seq_checked_sum(seq).unwrap().is_inf(),
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
                ExtI64::lem_sum_of_seq_with_inf_is_inf(seq.drop_last());
            }
        }

    }

}

impl PartialEq for ExtI64 {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (ExtI64::Inf, ExtI64::Inf) => true,
            (ExtI64::Inf, _) => false,
            (_, ExtI64::Inf) => false,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
                n1 == n2
            }
        }
    }
}

impl Eq for ExtI64 {}

// VerusのソースにもExOrderingが定義されているが、そのExOrderingは
// core::sync::atomic::Orderingの方を言及しており、std::cmp::Ordering
// の方ではないため、ここで定義する必要がある。
#[verifier::external_type_specification]
pub struct ExOrdering(Ordering);

impl PartialOrd for ExtI64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExtI64 {
    fn cmp(&self, other: &Self) -> Ordering {
        match (*self, *other) {
            (ExtI64::Inf, ExtI64::Inf) => Ordering::Equal,
            (ExtI64::Inf, _) => Ordering::Greater,
            (_, ExtI64::Inf) => Ordering::Less,
            (ExtI64::Int(n1), ExtI64::Int(n2)) => {
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

// i64::checked_sub(self, i64)
#[verifier::external_fn_specification]
pub fn ex_i64_checked_sub(lhs: i64, rhs: i64) -> (result: Option<i64>)
    ensures
        lhs - rhs > i64::MAX || lhs - rhs < i64::MIN ==> result.is_None(),
        i64::MIN <= lhs - rhs <= i64::MAX ==> result == Some((lhs - rhs) as i64),
{
    lhs.checked_sub(rhs)
}

proof fn test_spec()
{
    let a = ExtI64::Inf;
    let b = ExtI64::Int(1000);
    assert(a.checked_add(b) == Some(ExtI64::Inf));
    assert(b.checked_add(b) == Some(ExtI64::Int(2000)));
    assert(b.checked_add(b) == Some(ExtI64::Int(2000)));

    assert(ExtI64::Int(0) < ExtI64::Inf);
    assert(ExtI64::Int(0) < ExtI64::Int(1));
    assert(ExtI64::Int(1) <= ExtI64::Int(1));
    assert(ExtI64::Inf <= ExtI64::Inf);

    assert(b < a);
}

proof fn test_spec_2() {
    let inf = ExtI64::Inf;
    let num = ExtI64::Int(123);

    assert(!inf.is_int());
    assert( inf.is_inf());
    assert( num.is_int());
    assert(!num.is_inf());
    assert(num.unwrap() == 123);
}

proof fn test_spec_3() {
    let n = ExtI64::Int(i64::MAX);

    let m = n + n;
    assert(m.is_int());
}

fn test_exec() {
    let n = ExtI64::Int(1000);
    let m = n.add(n);
    assert(n < m);

    let x = ExtI64::Int(i64::MAX);
    // x.add(x); // オーバーフローの可能性は検証器が見つけてくれる。
}

fn test_exec_3() {
    let mut v = Vec::new();
    v.push(ExtI64::Int(2));
    v.push(ExtI64::Int(3));
    v.push(ExtI64::Int(5));
    
    reveal_with_fuel(ExtI64::seq_checked_sum, 4);
    let ans = ExtI64::vec_checked_sum(&v);
    assert(ans.is_some());
    assert(ans.unwrap() == ExtI64::Int(10));
}

fn test_exec_4() {
    let mut v = Vec::new();
    v.push(ExtI64::Int(2));
    v.push(ExtI64::Int(3));
    v.push(ExtI64::Int(5));

    let n = ExtI64::vec_checked_sum(&v);
    reveal_with_fuel(ExtI64::seq_checked_sum, 4);
    assert(n.is_some());
    proof { ExtI64::lem_sum_of_all_int_seq_is_int(v@); }
    assert(n.unwrap().is_int());

    v.push(ExtI64::Inf);
    v.push(ExtI64::Int(7));

    let n = ExtI64::vec_checked_sum(&v);
    reveal_with_fuel(ExtI64::seq_checked_sum, 10);
    assert(n.is_some());
    proof { ExtI64::lem_sum_of_seq_with_inf_is_inf(v@); }
    assert(n.unwrap().is_inf());
}

fn test_exec_5() {
    let mut v = Vec::new();
    v.push(ExtI64::Int(99));
    v.push(ExtI64::Int(1729));
    v.push(ExtI64::Int(-33));
    v.push(ExtI64::Int(50001));
    v.push(ExtI64::Int(-7777));
    let s = ExtI64::vec_sum(&v);
    proof { ExtI64::lem_sum_of_all_int_seq_is_int(v@) }
    assert(s.is_int());
}

#[verifier::external_body]
pub fn test() {
    let inf = ExtI64::Inf;
    let n = ExtI64::Int(7);

    let mut x;
    let mut y;

    x = inf;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} - {:?} = {:?}", x, y, x.checked_sub(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = inf;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} - {:?} = {:?}", x, y, x.checked_sub(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = inf;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} - {:?} = {:?}", x, y, x.checked_sub(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    x = n;
    y = n;
    println!("{:?} + {:?} = {:?}", x, y, x.add(y));
    println!("{:?} - {:?} = {:?}", x, y, x.checked_sub(y));
    println!("{:?} < {:?} = {:?}", x, y, x < y);

    let a = ExtI64::Inf;
    let b = ExtI64::Int(1000);
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
    v.push(ExtI64::Int(2));
    v.push(ExtI64::Int(3));
    v.push(ExtI64::Int(5));
    let ans = ExtI64::vec_checked_sum(&v).unwrap();
    println!("sum of {:?} is {:?}", v, ans);
    v.push(ExtI64::Inf);
    v.push(ExtI64::Int(7));
    let ans = ExtI64::vec_checked_sum(&v).unwrap();
    println!("sum of {:?} is {:?}", v, ans);

    let mut v = Vec::new();
    v.push(ExtI64::Int(99));
    v.push(ExtI64::Int(1729));
    v.push(ExtI64::Int(-33));
    v.push(ExtI64::Int(50001));
    v.push(ExtI64::Int(-7777));
    let s = ExtI64::vec_sum(&v);
    println!("{}", s);
}

} // verus!

impl fmt::Display for ExtI64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExtI64::Int(n) => write!(f, "{}", *n),
            ExtI64::Inf => write!(f, "∞"),
        }
    }
}
