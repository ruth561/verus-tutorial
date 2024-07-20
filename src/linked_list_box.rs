use vstd::prelude::*;
use vstd::seq::*;


verus! {

#[derive(Debug)]
struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

impl<T> Node<T> {

    // Is the length of `head` equal to `size`?
    spec fn valid_size(head: Option<Box<Node<T>>>, size: nat) -> bool
        decreases size,
    {
        match head {
            Some(node) => {
                if size == 0 {
                    false
                } else {
                    Self::valid_size(node.next, (size-1) as nat)
                }
            }
            None => {
                if size == 0 {
                    true
                } else {
                    false
                }
            }
        }
    }

}

#[derive(Debug)]
struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    size: usize,
}

impl<T> LinkedList<T> {

    spec fn well_formed(self) -> bool {
        Node::<T>::valid_size(self.head, self.size as nat)
    }

    spec fn view_int(head: Option<Box<Node<T>>>, n: nat) -> Seq<T>
        recommends
            Node::<T>::valid_size(head, n),
        decreases n,
    {
        if n == 0 {
            Seq::empty()
        } else {
            let node = head.unwrap();
            Seq::empty().push(node.value) + Self::view_int(node.next, (n-1) as nat)
        }
    }

    spec fn view(self) -> Seq<T>
    {
        Self::view_int(self.head, self.size as nat)
    }

    fn new() -> (result: Self)
        ensures
            result.well_formed(),
            result.size == 0,
            result@ == Seq::<T>::empty(),
    {
        Self {
            head: None,
            size: 0,
        }
    }

    fn push(&mut self, value: T)
        requires
            old(self).well_formed(),
            old(self).size < usize::MAX,
        ensures
            self.well_formed(),
            self.size == old(self).size + 1,
            self@.first() == value,
            self@.drop_first() == old(self)@,
    {
        let ghost old_s = self@;

        let head = self.head.take();
        let new_node = Box::new(Node {
            value,
            next: head,
        });
        self.head = Some(new_node);
        self.size = self.size + 1;

        let ghost s = self@;
        assert(s.drop_first() =~= old_s);
    }

    // not verified completely
    fn pop(&mut self) -> (opt: Option<T>)
        requires
            old(self).well_formed(),
        ensures
            self.well_formed(),
            opt.is_some() ==> self.size == old(self).size - 1,
            opt.is_none() ==> self.size == old(self).size,
    {
        let node = self.head.take()?;
        self.head = node.next;
        self.size = self.size - 1;
        Some(node.value)
    }

}

fn test_push()
{
    let mut l = LinkedList::<i64>::new();
    proof {
        assert(l.size == 0);
        assert(l.view().len() == 0);
    }
    l.push(2);
    proof {
        reveal_with_fuel(LinkedList::view_int, 5);
        assert(l.size == 1);
        assert(l.well_formed());
        assert(l@ =~= seq![2]);
    }
    l.push(3);
    proof {
        assert(l.size == 2);
        assert(l.well_formed());
        assert(l@ =~= seq![3, 2]);
    }
    l.push(5);
    proof {
        assert(l.size == 3);
        assert(l.well_formed());
        assert(l@ =~= seq![5, 3, 2]);
    }
}

#[verifier::external_body]
pub fn test()
{
    let mut l = LinkedList::<i64>::new();
    l.push(2);
    l.push(3);
    l.push(5);
    println!("l: {:?}", l);
    println!("pop: {:?}", l.pop());
    println!("pop: {:?}", l.pop());
    println!("l: {:?}", l);
}

} // verus!
