use crate::{define_id, DenseIdMap, IdVec, NumericId};

define_id!(pub(crate) Id, u32, "a unique id");

#[test]
#[should_panic]
fn id_out_of_bounds() {
    Id::from_usize(u32::MAX as usize + 5);
}

fn to_vec(map: &DenseIdMap<Id, &'static str>) -> Vec<(Id, &'static str)> {
    map.iter().map(|(x, y)| (x, *y)).collect::<Vec<_>>()
}

pub(crate) fn assert_free_list_invariants<K, V>(map: &DenseIdMap<K, V>) {
    use crate::{FreeListNode, Slot};

    // check that all free nodes point to free nodes
    let mut num_free = 0;
    for slot in &map.data {
        if let Slot::Free(node) = slot {
            num_free += 1;
            if let Some(prev) = node.prev {
                assert!(matches!(map.data[prev], Slot::Free(_)));
            }
            if let Some(next) = node.next {
                assert!(matches!(map.data[next], Slot::Free(_)));
            }
        }
    }

    // check that walking the free list is successful
    match &map.free {
        None => assert_eq!(num_free, 0),
        Some(free) => {
            let mut node = free.head;
            loop {
                match map.data[node] {
                    Slot::Full(_) => panic!(),
                    Slot::Free(FreeListNode { next, .. }) => match next {
                        None => break,
                        Some(next) => node = next,
                    },
                }
            }
            assert_eq!(node, free.last);
        }
    }
}

#[test]
fn push() {
    let mut map = DenseIdMap::<Id, &'static str>::new();
    let first = map.next_id();
    assert_eq!(first, map.push("zero"));
    let second = map.next_id();
    assert_eq!(second, map.push("one"));
    assert_eq!(to_vec(&map), vec![(first, "zero"), (second, "one")]);
    assert_free_list_invariants(&map);
}

#[test]
fn basic_id_map() {
    let mut map = DenseIdMap::<Id, &'static str>::new();
    map.insert(Id::from_usize(0), "zero");
    map.insert(Id::from_usize(4), "four");

    assert_eq!(
        to_vec(&map),
        vec![(Id::from_usize(0), "zero"), (Id::from_usize(4), "four")]
    );

    assert_eq!(map.unwrap_val(Id::from_usize(0)), "zero");

    assert_eq!(to_vec(&map), vec![(Id::from_usize(4), "four")]);

    map.insert(Id::from_usize(2), "two");
    assert_eq!(
        to_vec(&map),
        vec![(Id::from_usize(2), "two"), (Id::from_usize(4), "four")]
    );

    assert_free_list_invariants(&map);
}

#[test]
fn get_or_insert() {
    let mut map = DenseIdMap::<Id, &'static str>::new();
    let id = Id::from_usize(3);
    assert_eq!(map.get_or_default(id), &"");
    assert_eq!(
        map.get_or_insert(id, || panic!("this should not be called")),
        &""
    );

    map.get_or_insert(id, || "three");
    assert_eq!(to_vec(&map), vec![(id, "")]);

    assert_free_list_invariants(&map);
}

#[test]
fn basic_id_vec() {
    let mut v = IdVec::<Id, usize>::default();
    let id0 = v.push(0);
    let id1 = v.push(1);
    assert_eq!(0, v[id0]);
    assert_eq!(1, v[id1]);
    let mut i = 2;
    v.resize_with(100, || {
        let res = i;
        i += 1;
        res
    });
}
