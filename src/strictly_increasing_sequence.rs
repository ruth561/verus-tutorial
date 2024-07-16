use vstd::prelude::*;


verus! {

// returns true iff s[0] < s[1] < ... < s[n-1]
pub open spec fn strictly_increasing_sequence(s: Seq<int>) -> bool
    decreases s.len(),
{
    if s.len() <= 1 {
        true
    } else {
        s[0] < s[1] && strictly_increasing_sequence(s.drop_first())
    }
} 

// if strictly_increasing_sequence(s) then forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j]
proof fn lem_1_strictly_increasing_sequence(s: Seq<int>)
    requires
        strictly_increasing_sequence(s),
    ensures
        forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j],
    decreases s.len(),
{
    if s.len() <= 1 {
        // assert is not necessary
    } else {
        let t = s.drop_first();
        lem_1_strictly_increasing_sequence(t);
        assert forall|i:int, j:int| 0 <= i < j < s.len() implies s[i] < s[j] by {
            if i == 0 {
                if 2 <= j {
                    assert(t[0] < t[j-1]); // s[0] < s[1] (=t[0]) < s[j] (=t[j-1])
                }
            } else {
                assert(t[i-1] < t[j-1]); // s[i] (=t[i-1]) < s[j] (=t[j-1])
            }
        }
    }
}

// if forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j] then strictly_increasing_sequence(s)
proof fn lem_2_strictly_increasing_sequence(s: Seq<int>)
    requires
        forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j],
    ensures
        strictly_increasing_sequence(s),
    decreases s.len(),
{
    if 2 <= s.len() {
        lem_2_strictly_increasing_sequence(s.drop_first());
    }
}

pub proof fn lem_strictly_increasing_sequence(s: Seq<int>)
    ensures
        strictly_increasing_sequence(s) <==> forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j],
{
    // lhs ==> rhs
    if strictly_increasing_sequence(s) {
        lem_1_strictly_increasing_sequence(s);
        assert(forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j]);
    }

    // lhs <== rhs
    if forall|i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j] {
        lem_2_strictly_increasing_sequence(s);
        assert(strictly_increasing_sequence(s));
    }
}

} // verus!
