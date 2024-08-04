use vstd::prelude::*;


verus! {

// m is the maximum of s
spec fn is_max(m: i64, s: Seq<i64>) -> bool {
    &&& forall|i:int| 0 <= i < s.len() ==> #[trigger] s[i] <= m
    &&& exists|i:int| 0 <= i < s.len() &&  #[trigger] s[i] == m
}

proof fn lem_is_max(s: Seq<i64>, m: i64, x: i64)
    requires
        is_max(m, s),
    ensures
        if m <= x { is_max(x, s.push(x)) }
        else      { is_max(m, s.push(x)) },
{
    let s_ = s.push(x);

    // assersions are needed for proof exists.
    if m <= x {
        let i = s_.len() - 1;
        assert(s_[i] == x);
    } else {
        let i = choose|i:int| 0 <= i < s.len() && s[i] == m;
        assert(s_[i] == m);
    }
}

fn max(v: &Vec<i64>) -> (result: i64)
    requires v.len() >= 1,
    ensures  is_max(result, v@),
{
    let mut i = 1;
    let mut m = v[0];
    let ghost mut s = v@.subrange(0, 1); // ghost variables
    assert(s[0] <= m); // need for existence
    while i < v.len()
        invariant i <= v.len(), s =~= v@.subrange(0, i as int), is_max(m, s),
    {
        proof {
            lem_is_max(s, m, v[i as int]);
            s = s.push(v[i as int]);
        }

        if v[i] >= m { m = v[i]; }
        i += 1;
    }
    assert(v@ == s);
    m
}

#[verifier::external_body]
pub fn test() {
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
    let m = max(&v);
    println!("max({:?}) = {}", v, max(&v));
}

} // verus!
