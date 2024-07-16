use vstd::prelude::*;
use vstd::slice::slice_subrange;
use crate::strictly_increasing_sequence::*;


verus! {

pub open spec fn is_subseq<T: Eq>(s: Seq<T>, t: Seq<T>) -> bool
    decreases t.len(),
{
    if s.len() == 0 {
        // s is empty
        true
    } else if t.len() == 0 {
        // s is not empty but t is empty
        false
    } else {
        if s.first() == t.first() {
            is_subseq(s.drop_first(), t.drop_first())
        } else {
            is_subseq(s, t.drop_first())
        }
    }
}

// s[i] == t[a[i]]
pub open spec fn match_elements<T: Eq>(i: int, a: Seq<int>, s: Seq<T>, t: Seq<T>) -> bool
{
    0 <= a[i] < t.len() && s[i] == t[a[i]]
}

pub open spec fn is_index_of_subseq<T: Eq>(a: Seq<int>, s: Seq<T>, t: Seq<T>) -> bool
{
    &&& a.len() == s.len()
    &&& strictly_increasing_sequence(a)
    &&& forall|i:int| 0 <= i < a.len() ==> #[trigger] match_elements(i, a, s, t)
}

proof fn lem_is_subseq_1<T: Eq>(s: Seq<T>, t: Seq<T>)
    requires
        is_subseq(s, t),
    ensures
        exists|a:Seq<int>| #[trigger] is_index_of_subseq(a, s, t),
    decreases t.len(),
{
    if s.len() == 0 {
        let a = Seq::<int>::empty();
        assert(is_index_of_subseq(a, s, t));
    } else { // 1 <= t.len()
        let s_tail = s.drop_first();
        let t_tail = t.drop_first();
        if s[0] == t[0] {
            lem_is_subseq_1(s_tail, t_tail);
            let a = choose|a:Seq<int>| is_index_of_subseq(a, s_tail, t_tail);

            // create index sequence of subseq(s, t)
            let b = Seq::<int>::new(a.len() + 1, |i:int| { if i == 0 { 0 } else { a[i-1]+1 }});

            // b is strictly increasing sequence
            assert forall|i:int, j:int| 0 <= i < j < b.len() implies b[i] < b[j] by {
                lem_strictly_increasing_sequence(a);
                assert(match_elements(j-1, a, s_tail, t_tail));
            };
            lem_strictly_increasing_sequence(b);

            // b is index of sebseq(s, t)
            assert forall|i:int| 0 <= i < b.len() implies #[trigger] match_elements(i, b, s, t) by {
                if 1 <= i {
                    assert(match_elements(i-1, a, s_tail, t_tail));
                }
            };

            assert(is_index_of_subseq(b, s, t));
        } else {
            lem_is_subseq_1(s, t_tail);
            let a = choose|a:Seq<int>| is_index_of_subseq(a, s, t_tail);

            // create index sequence of subseq(s, t)
            let b = a.map(|j:int, i:int| i+1);

            // b is strictly increasing sequence
            assert forall|i:int, j:int| 0 <= i < j < a.len() implies b[i] < b[j] by {
                lem_strictly_increasing_sequence(a);
            };
            lem_strictly_increasing_sequence(b);

            // b is index of sebseq(s, t)
            assert forall|i:int| 0 <= i < b.len() implies match_elements(i, b, s, t) by {
                assert(match_elements(i, a, s, t_tail));
            };

            assert(is_index_of_subseq(b, s, t));
        }
    }
}

proof fn lem_is_subseq_2<T: Eq>(s: Seq<T>, t: Seq<T>)
    requires
        exists|a:Seq<int>| #[trigger] is_index_of_subseq(a, s, t),
    ensures
        is_subseq(s, t),
    decreases t.len(),
{
    let a = choose|a:Seq<int>| is_index_of_subseq(a, s, t);
    if s.len() == 0 { // triv.
    } else if t.len() == 0 { // there not exists such index array
        assert(match_elements(0, a, s, t));
        assert(false);
    } else {
        let s_tail = s.drop_first();
        let t_tail = t.drop_first();
        if s.first() == t.first() {
            let b = a.drop_first().map(|j:int, i:int| i-1);

            // b is strictly increasing sequence
            assert forall|i:int, j:int| 0 <= i < j < b.len() implies b[i] < b[j] by {
                lem_strictly_increasing_sequence(a);
            };
            lem_strictly_increasing_sequence(b);

            // b is index of sebseq(s, t)
            assert forall|i:int| 0 <= i < b.len() implies match_elements(i, b, s_tail, t_tail) by {
                assert(match_elements(i, a, s, t));
                lem_strictly_increasing_sequence(a);
                assert(match_elements(i+1, a, s, t));
            };

            assert(is_index_of_subseq(b, s_tail, t_tail));
            lem_is_subseq_2(s_tail, t_tail);
        } else {
            // 1 <= a[0]
            assert(match_elements(0, a, s, t));
            assert(s[0] == t[a[0]]);

            let b = a.map(|j:int, i:int| i-1);

            // b is strictly increasing sequence
            assert forall|i:int, j:int| 0 <= i < j < b.len() implies b[i] < b[j] by {
                lem_strictly_increasing_sequence(a);
            };
            lem_strictly_increasing_sequence(b);

            // b is index of sebseq(s, t)
            assert forall|i:int| 0 <= i < b.len() implies match_elements(i, b, s, t_tail) by {
                assert(match_elements(i, a, s, t));
            };

            assert(is_index_of_subseq(b, s, t_tail));
            lem_is_subseq_2(s, t_tail);
        }
    }
}

pub proof fn lem_is_subseq<T: Eq>(s: Seq<T>, t: Seq<T>)
    ensures
        is_subseq(s, t) <==> exists|a:Seq<int>| #[trigger] is_index_of_subseq(a, s, t),
{
    if is_subseq(s, t) {
        lem_is_subseq_1(s, t);
    }
    
    if exists|a:Seq<int>| #[trigger] is_index_of_subseq(a, s, t) {
        lem_is_subseq_2(s, t);
    }
}

pub fn exec_is_subseq(s: &[i64], t: &[i64]) -> (b: bool)
    ensures
        b == is_subseq(s@, t@),
{
    if s.len() == 0 {
        true
    } else if t.len() == 0 {
        false
    } else {
        if s[0] == t[0] {
            exec_is_subseq(slice_subrange(s, 1, s.len()), slice_subrange(t, 1, t.len()))
        } else {
            exec_is_subseq(s, slice_subrange(t, 1, t.len()))
        }
    }
}

#[verifier::external_body]
pub fn test() {
    let s = vec![2, 3, 5];
    let t = vec![1, 2, 3, 4, 5, 6, 7];
    println!("Q. {:?} is subseq of {:?} ? \nA. {}", s, t, exec_is_subseq(&s, &t));

    let s = vec![2, 3, 5, 7];
    let t = vec![1, 2, 3, 4, 5, 6, 7];
    println!("Q. {:?} is subseq of {:?} ? \nA. {}", s, t, exec_is_subseq(&s, &t));

    let s = vec![2, 3, 5, 7, 11];
    let t = vec![1, 2, 3, 4, 5, 6, 7];
    println!("Q. {:?} is subseq of {:?} ? \nA. {}", s, t, exec_is_subseq(&s, &t));

    let s = vec![2, 99, 5];
    let t = vec![1, 2, 3, 4, 5, 6, 7];
    println!("Q. {:?} is subseq of {:?} ? \nA. {}", s, t, exec_is_subseq(&s, &t));
}

} // verus!
