use vstd::prelude::*;
use vstd::ptr::*;


verus! {

pub fn test()
{
    // 返される値と型は以下の通り.
    //   ptr: PPtr<i64>
    //   perm: PointsTo<i64>
    //   dealloc: Dealloc<i64>
    let (ptr, Tracked(perm), Tracked(dealloc)) = PPtr::<i64>::empty();

    assert(ptr.id() == perm@.pptr); // ポインタの値は一致している
    assert(perm@.value.is_none()); // ポインタは初期化されていない
    print_ptr(&ptr); // ポインタの値を出力（0x558158efdd70など）

    let tracked hoge = &perm;
    // ポインタの指す先の領域に値を書きこむ
    // permの可変参照が必要
    ptr.write(Tracked(&mut perm), 0xdeadbeef);

    // ポインタの指す先の領域から値を読み出す
    // permの不変参照が必要
    let val = ptr.read(Tracked(&perm));
    print_val(val);

    // disposeはいわゆるfreeの動作をするメソッド
    // disposeのpreconditionには「perm@.value === None」が含まれているため、
    // その前にpermの中身をleakしておく必要がある。
    proof {
        perm.leak_contents();
    }
    ptr.dispose(Tracked(perm), Tracked(dealloc));

    // 上でpermとdeallocの所有権が消滅したので、この後にptrから読み書きを
    // しようとしてもできない. つまり、UAFを防ぐことができる！！！
}

#[verifier::external_body]
fn print_ptr<V>(pptr: &PPtr<V>)
{
    println!("pptr: 0x{:x}", pptr.to_usize());
}

#[verifier::external_body]
fn print_val(n: i64)
{
    println!("val: 0x{:x}", n);
}

} // verus!
