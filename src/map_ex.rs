use vstd::prelude::*;


verus! {

// Map::total(fv)
// 全域関数を生成するコンストラクタ
proof fn ex_map_total() {
    // f:Z->Zであってf(i)=i+1となるようなもの
    let f = Map::<int, int>::total(|i:int| i + 1);
    assert(f[1] == 2);
    assert(f[-1] == 0);
    assert(f[999999999999999999999999] == 1000000000000000000000000);
}

// Map::new(fk, fv)
// 部分関数を生成するコンストラクタ
// fk: K->boolは定義域を定める写像
// fv: K->Vはマップの動作を定める写像
proof fn ex_map_new() {
    // f:{0,1,2,...,9}->Z
    let fk = |i:int| 0 <= i < 10;
    let fv = |i:int| i * i;
    let f = Map::<int, int>::new(fk, fv);
    assert(f[0] == 0);
    assert(f[5] == 25);
    assert(f[9] == 81);
    // assert(f[10] == 100); // 定義されていない
    // Map::dom()は定義域を意味するSetを返す
    assert(!f.dom().contains(10));
    assert(!f.dom().contains(-1));
}

// map![k => v, ...]
// Mapを作成するマクロ
proof fn ex_map_macro() {
    let f: Map<int, int> = map![1 => 2, 2 => 3, 3 => 4];
    assert(f.dom() =~= set![1, 2, 3]);

    let mut g = Map::<int, int>::empty();
    g = g.insert(1, 2);
    g = g.insert(2, 3);
    g = g.insert(3, 4);
    assert(f =~= g);
}

// Map::tracked_map_keys_in_place(&mut self, key_map)
// Mapの合成により新しいMapを作成するもの
proof fn ex_map_composition() {
    let tracked mut f = Map::<int, &'static str>::tracked_empty();
    f.tracked_insert(1, "ABC");
    f.tracked_insert(2, "DE");
    assert(f =~= map![1 => "ABC", 2 => "DE"]);

    let key_map = map![5 => 1, 7 => 2];
    f.tracked_map_keys_in_place(key_map);
    assert(f =~= map![5 => "ABC", 7 => "DE"]);
}

// Map<nat, V>をSeq<V>として見ることができればtrueを返すspec関数
spec fn can_be_seen_as_seq<V>(m: Map<nat, V>) -> bool {
    forall|i:nat| 0 <= i < m.len() <==> m.dom().contains(i)
}

// Map<nat, V>はある条件を満たすとSeq<V>として見ることができるようになる。
// TODO: 実装が途中
proof fn push_front_as_seq<V>(tracked m: &mut Map<nat, V>)
    requires
        can_be_seen_as_seq(*old(m)),
    ensures
        forall|i:nat| 0 <= i < old(m).len() ==> old(m)[i] == m[i + 1],
{
    // map![1 => 0, 2 => 1, 3 => 2, ...]
    let key_m = Map::<nat, nat>::new(
        |i:nat| 1 <= i <= m.dom().len(),
        |i:nat| (i - 1) as nat
    );
    assert(forall|i:nat| key_m.dom().contains(i) ==> #[trigger] m.dom().contains(key_m.index(i)));
    m.tracked_map_keys_in_place(key_m);
    assert(forall|i:nat| 1 <= i <= old(m).len() <==> m.dom().contains(i));
}

} // verus!
