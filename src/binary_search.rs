use vstd::prelude::*;


verus! {

pub fn binary_search(v: &Vec<i64>, k: i64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j], // sorted
        exists|i:int| 0 <= i < v.len() && v[i] == k,
    ensures
        r < v.len(),
        v[r as int] == k,
{
    
    let mut l = 0;
    let mut h = v.len();

    assert(1 <= v.len());
    if v.len() == 1 {
        return 0;
    }

    while 1 < h - l 
        invariant
            0 <= l < h <= v.len(),
            exists|i:int| l <= i < h && v[i] == k,
            forall|i:int, j:int| l <= i <= j < h ==> v[i] <= v[j],
    {
        let m = l + (h - l) / 2;
        if k < v[m] {
            h = m;
        } else {
            l = m;
        }
    }
    l
}

} // verus!

pub fn test()
{
    let v = vec![0, 1, 3, 9, 10, 10, 13, 99, 1729, 4649];

    let mut k = 99;
    println!("{} is at {} on {:?}.", k, binary_search(&v, k), v);
    k = 10;
    println!("{} is at {} on {:?}.", k, binary_search(&v, k), v);
    k = 0;
    println!("{} is at {} on {:?}.", k, binary_search(&v, k), v);
}
