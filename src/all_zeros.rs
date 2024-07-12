use vstd::prelude::*;


verus! {

pub open spec fn is_zero(n: i32) -> bool
{
    n == 0
}

pub open spec fn all_zeros(s: Seq<i32>) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let head = s[0];
        let tail = s.drop_first();
        is_zero(head) && all_zeros(tail)
    }
}

proof fn lem_all_zeros(s: Seq<i32>)
    ensures
        all_zeros(s) <==> forall|i:int| 0 <= i < s.len() ==> #[trigger] is_zero(s[i]),
    decreases s.len(),
{
    if s.len() == 0 {
        // proof is not necessary
    } else {
        let result = all_zeros(s);
        let head = s[0];
        let tail = s.drop_first();
        if result { // the case of ==>
            lem_all_zeros(tail);
            assert forall|i:int| 0 <= i < s.len() implies #[trigger] is_zero(s[i]) by {
                if 1 <= i {
                    assert(s[i] == tail[i-1]);
                    assert(is_zero(s[i]));
                }
            }
        } else { // the case of <==
            if !is_zero(s[0]) {
            } else { // !all_zeros(tail)
                lem_all_zeros(tail);
            }
        }
    }
}

proof fn test()
{
    let s = seq![0, 0, 0, 0];
    assert(forall|i:int| 0 <= i < s.len() ==> #[trigger] is_zero(s[i]));

    let s = seq![0, 1, 2, 3];
    assert(!is_zero(s[1]));
    lem_all_zeros(s);
    assert(!all_zeros(s));
}

} // verus!
