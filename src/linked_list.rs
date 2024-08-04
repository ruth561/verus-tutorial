use std::fmt::Display;

use vstd::prelude::*;
use vstd::ptr::*;


verus! {

struct Node<V> {
    next: Option<PPtr<Node<V>>>,
    value: V,
}

type MemPerm<V> = (PointsTo<Node<V>>, Dealloc<Node<V>>);

// permsがMapとなっているのは、そもそも可変参照用のメソッドなどを実装しているのが
// Mapだけだから。Seqにはそのようなメソッドが用意されていないため、Trackedでくくっても
// 恩恵が得られない。
struct List<V> {
    ptrs:  Ghost<Seq<PPtr<Node<V>>>>, // Ghost
    perms: Tracked<Map<nat, MemPerm<V>>>, // Tracked
    head:  Option<PPtr<Node<V>>>,
}

impl<V> List<V> {
    // 単方向リストも数学的にはSeqとして見ることができる
    spec fn view(self) -> Seq<V> {
        Seq::new(self.ptrs@.len(), |i:int| self.perms@[i as nat].0@.value.unwrap().value)
    }

    // i番目のノードの次のノードを指すspec関数
    spec fn next_of(&self, i: nat) -> Option<PPtr<Node<V>>> {
        if i + 1 == self.ptrs@.len() {
            None
        } else {
            Some(self.ptrs@[i as int + 1])
        }
    }

    // i番目のパーミッションとi番目のポインタの関係性についての述語
    spec fn wf_perm(&self, i: nat) -> bool {
        &&& self.perms@.dom().contains(i)
        &&& self.perms@[i].0@.pptr == self.ptrs@[i as int].id() // PointsToとPPtrが対応していること
        &&& self.perms@[i].1@.pptr == self.ptrs@[i as int].id() // DeallocとPPtrが対応していること
        &&& match self.perms@[i].0@.value { // 対応するノードのnextが次のノードを指していること
                Some(node) => node.next == self.next_of(i),
                None => false,
            }
    }

    spec fn well_formed(&self) -> bool {
        &&& forall|i:nat| 0 <= i < self.ptrs@.len() <==> self.perms@.dom().contains(i)
        &&& forall|i:nat| 0 <= i < self.ptrs@.len() ==> self.wf_perm(i)
        &&& if self.ptrs@.len() == 0 {
                self.head.is_none()
            } else {
                self.head == Some(self.ptrs@[0])
            }
    } 

    fn empty() -> (result: List<V>)
        ensures
            result.well_formed(),
            result@.len() == 0,
    {
        let result = List::<V>{
            ptrs: Ghost(Seq::empty()),
            perms: Tracked(Map::tracked_empty()),
            head: None,
        };
        result
    }

    // pushするときは、seqの先頭に新しくアロケートしたポインタを追加する
    // mapに関しては特別に設定してあげる必要がある。というのも、
    // mapは<K=nat, V=Perm>であるため、iに対応したパーミッションは
    // i+1に移動する必要がある。
    fn push(&mut self, v: V)
        requires
            old(self).well_formed(),
        ensures
            self.well_formed(),
            self@ == seq![v].add(old(self)@)
    {
        if let Some(head_ptr) = self.head {
            let (pptr, Tracked(points_to), Tracked(dealloc)) = PPtr::new(Node{ next: Some(head_ptr.clone()), value: v });
            proof {
                // map![1 => 0, 2 => 1, 3 => 2, ...]
                let key_map = Map::<nat, nat>::new(
                    |j:nat| 1 <= j <= self.ptrs@.len(),
                    |j:nat| (j - 1) as nat
                );
                assert forall|j:nat| key_map.dom().contains(j) implies #[trigger] self.perms@.dom().contains(key_map.index(j)) by {
                    assert(self.wf_perm(key_map.index(j)));
                }
                self.perms.borrow_mut().tracked_map_keys_in_place(key_map);
                self.perms.borrow_mut().tracked_insert(0, (points_to, dealloc));

                // ptrsの先頭に新しいptrを追加する
                // self.ptrs = [pptr] + self.ptrs
                self.ptrs@ = seq![pptr].add(self.ptrs@);
            }
            self.head = Some(pptr);
            assert forall|i:nat| 0 <= i < self.ptrs@.len() implies self.wf_perm(i) by {
                if i > 0 {
                    assert(old(self).wf_perm((i - 1) as nat));
                }
            }
            assert(self@ =~= seq![v].add(old(self)@));
        } else {
            let (pptr, Tracked(points_to), Tracked(dealloc)) = PPtr::new(Node{ next: None, value: v });
            self.head = Some(pptr);
            assert(self.perms@.dom() =~= set![]);
            proof {
                self.perms.borrow_mut().tracked_insert(0, (points_to, dealloc));
                self.ptrs@ = seq![pptr];
            }
            assert(self@ =~= seq![v].add(old(self)@));
        }
    }
}

// まだDisplayの中身をVerusで検査することはできない？
// というか、副作用があるから検証は現実的ではない？
#[verifier::external]
impl<V: Display> Display for List<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.head {
            None => (),
            Some(mut head_ptr) => {
                let mut node_ptr = head_ptr;
                let ghost mut idx = 0;
                loop {
                    let node = node_ptr.borrow(Tracked(&self.perms@[idx].0));
                    write!(f, "{} :: ", node.value)?;
                    match node.next {
                        None => break,
                        Some(next_ptr) => {
                            node_ptr = next_ptr;
                            proof { idx = idx + 1 };
                        }
                    }
                }
            }
        }
        write!(f, "[]")
    }
}

fn test_push() {
    let mut l = List::<i64>::empty();
    assert(l@ =~= seq![]);
    l.push(2);
    assert(l@ =~= seq![2]);
    l.push(3);
    assert(l@ =~= seq![3, 2]);
    l.push(5);
    l.push(7);
    l.push(11);
    assert(l@ =~= seq![11, 7, 5, 3, 2]);
}

#[verifier::external_body]
pub fn test() {
    let mut l = List::<i64>::empty();
    l.push(2);
    l.push(3);
    l.push(5);
    println!("{}", l);
    l.push(7);
    l.push(11);
    println!("{}", l);
}

} // verus!
