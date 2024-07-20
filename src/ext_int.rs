use vstd::prelude::*;


verus! {

pub enum ExtInt {
    Int(int),
    Inf,
}

impl ExtInt {

    // utils
    pub open spec fn is_int(&self) -> bool {
        is_variant(self, "Int")
    }

    pub open spec fn is_inf(&self) -> bool {
        is_variant(self, "Inf")
    }

    pub open spec fn unwrap(&self) -> int
        recommends
            self.is_int()
    {
        get_variant_field(self, "Int", "0")
    }


    // cmp
    pub open spec fn spec_lt(self, rhs: ExtInt) -> bool {
        match (self, rhs) {
            (ExtInt::Inf, ExtInt::Inf) => false,
            (ExtInt::Inf, _) => false,
            (_, ExtInt::Inf) => true,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => {
                n1 < n2
            }
        }
    }

    pub open spec fn spec_le(self, rhs: ExtInt) -> bool {
        self.spec_lt(rhs) || self == rhs
    }

    pub open spec fn spec_gt(self, rhs: ExtInt) -> bool {
        !self.spec_le(rhs)
    }

    pub open spec fn spec_ge(self, rhs: ExtInt) -> bool {
        !self.spec_lt(rhs)
    }


    // arith
    pub open spec fn spec_add(self, rhs: ExtInt) -> ExtInt {
        match (self, rhs) {
            (ExtInt::Inf, _) => ExtInt::Inf,
            (_, ExtInt::Inf) => ExtInt::Inf,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => ExtInt::Int(n1 + n2),
        }
    }
    
    pub open spec fn spec_sub(self, rhs: ExtInt) -> ExtInt
        recommends
            self.safe_to_sub(rhs),
    {
        let invalid_ans = ExtInt::Int(0xdeadbeef);
        match (self, rhs) {
            (_, ExtInt::Inf) => {
                // unreachable
                invalid_ans
            },
            (ExtInt::Inf, _) => ExtInt::Inf,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => ExtInt::Int(n1 - n2),
        }
    }

    pub open spec fn safe_to_sub(self, rhs: ExtInt) -> bool {
        rhs.is_int()
    }

    pub open spec fn checked_sub(self, rhs: ExtInt) -> Option<ExtInt> {
        match (self, rhs) {
            (ExtInt::Inf, ExtInt::Inf) => None,
            (ExtInt::Inf, _) => Some(ExtInt::Inf),
            (_, ExtInt::Inf) => None,
            (ExtInt::Int(n1), ExtInt::Int(n2)) => Some(ExtInt::Int(n1 - n2)),
        }
    }

    pub open spec fn seq_sum(seq: Seq<ExtInt>) -> ExtInt
        decreases seq.len(),
    {
        if seq.len() == 0 {
            ExtInt::Int(0)
        } else {
            seq[seq.len()-1] + ExtInt::seq_sum(seq.drop_last())
        }
    }

    pub open spec fn is_positive(self) -> bool {
        ExtInt::Int(0) < self
    }

    pub open spec fn is_negative(self) -> bool {
        ExtInt::Int(0) > self
    }

    pub open spec fn is_non_positive(self) -> bool {
        ExtInt::Int(0) >= self
    }

    pub open spec fn is_non_negative(self) -> bool {
        ExtInt::Int(0) <= self
    }

    pub open spec fn is_zero(self) -> bool {
        ExtInt::Int(0) == self
    }

}

// proof
impl ExtInt {

    // 数列内にInfが1つもなく、checked_sumが何かしらの値を返すならば、その値はintである。
    proof fn lem_sum_of_all_int_seq_is_int(seq: Seq<ExtInt>)
        requires
            forall|i:int| 0 <= i < seq.len() ==> #[trigger] seq[i].is_int(),
        ensures
            ExtInt::seq_sum(seq).is_int(),
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
            exists|i:int| 0 <= i < seq.len() && #[trigger] seq[i].is_inf(),
        ensures
            ExtInt::seq_sum(seq).is_inf(),
        decreases
            seq.len(),
    {
        if seq.len() == 0 {
            // infの存在条件から-seq.len() == 0 となることはない
            assert(false);
        } else {
            let i = choose|i:int| 0 <= i < seq.len() && #[trigger] seq[i].is_inf();
            if i < seq.len() - 1 {
                assert(0 <= i < seq.drop_last().len() && seq.drop_last()[i].is_inf());
                assert(exists|i:int| 0 <= i < seq.drop_last().len() && #[trigger] seq.drop_last()[i].is_inf());
                ExtInt::lem_sum_of_seq_with_inf_is_inf(seq.drop_last());
            }
        }
    }

}

proof fn test_ext_int()
{
    let inf = ExtInt::Inf;
    let zero = ExtInt::Int(0);
    let one = ExtInt::Int(1);
    let a = ExtInt::Int(100000);
    let b = ExtInt::Int(-99999);

    assert(a + b == one);
    assert( one + zero ==  one);
    assert(zero + zero == zero);
    assert( inf +    a ==  inf);
    assert(   a +  inf ==  inf);
    assert( inf +  inf ==  inf);
    assert( inf -    a ==  inf);
    assert( one - zero ==  one);
    assert(zero - b + one == a);

    assert(   a <  inf);
    assert(zero <  one);
    assert(   b < zero);

    assert( inf <=  inf);
    assert(zero <=  one);
    assert(zero <= zero);

    assert( inf.is_positive());
    assert( inf.is_non_negative());
    assert(!inf.is_negative());
    assert(!inf.is_non_positive());

    assert(!zero.is_positive());
    assert( zero.is_non_negative());
    assert(!zero.is_negative());
    assert( zero.is_non_positive());

    assert(!b.is_positive());
    assert(!b.is_non_negative());
    assert( b.is_negative());
    assert( b.is_non_positive());

    assert( a.is_positive());
    assert( a.is_non_negative());
    assert(!a.is_negative());
    assert(!a.is_non_positive());

    assert(!   a.is_zero());
    assert(!   b.is_zero());
    assert(! inf.is_zero());
    assert( zero.is_zero());
}

proof fn test_seq_ext_int()
{
    let mut s = seq![ExtInt::Int(2), ExtInt::Int(3), ExtInt::Int(5)];
    ExtInt::lem_sum_of_all_int_seq_is_int(s);
    assert(ExtInt::seq_sum(s).is_int());

    s = s.push(ExtInt::Inf);
    s = s.push(ExtInt::Int(7));
    s = s.push(ExtInt::Int(11));
    assert(s[3].is_inf());
    ExtInt::lem_sum_of_seq_with_inf_is_inf(s);
    assert(ExtInt::seq_sum(s).is_inf());
}

} // verus!
