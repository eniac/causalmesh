use crate::mergeable::Mergeable;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::hash::Hash;

pub trait VCTrait {
    // Lamport's "happens before" relationship
    fn is_equal(&self, other: &Self) -> bool;
    fn happens_before(&self, other: &Self) -> bool;
    fn happens_after(&self, other: &Self) -> bool {
        other.happens_before(self)
    }
    // !(a happens before b) && !(b happens before a)
    fn concurrent(&self, other: &Self) -> bool;
    // determinitically pick one if concurrent
    fn privilege(&self, other: &Self) -> bool;
    // increment the counter
    fn increment(&mut self, idx: usize);
}

// T has to be less than 32
// HOWTO: const generics where-restriction?
#[derive(Debug, Default, Hash, PartialEq, Eq, Clone, Deserialize, Serialize)]
pub struct DenseVC<const T: usize>(pub [i32; T])
where
    [i32; T]: Default + DeserializeOwned + Serialize;

impl<const T: usize> VCTrait for DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    fn concurrent(&self, other: &Self) -> bool {
        self.partial_cmp(other).is_none()
    }

    fn is_equal(&self, other: &Self) -> bool {
        self == other
    }

    fn happens_before(&self, other: &Self) -> bool {
        for i in 0..T {
            if self.0[i] > other.0[i] {
                return false;
            }
        }
        if self == other {
            return false;
        }
        true
    }

    fn privilege(&self, other: &Self) -> bool {
        debug_assert!(self.concurrent(other));
        for i in 0..T {
            if self.0[i] == other.0[i] {
                continue;
            }
            return self.0[i] > other.0[i];
        }
        panic!();
    }

    fn increment(&mut self, idx: usize) {
        debug_assert!(idx < T);
        self.0[idx] += 1;
    }
}

impl<const T: usize> PartialOrd for DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    // a < b iff a happens before b
    // a <= b iff a happens before or equal to b
    // !(a < b) iff a is concurrent with b or equal to b or b happens before a

    // CAUTION:
    // !(a < b) is not equivalent to a >= b
    // think of "<"" as happens before in your mind
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if self.happens_before(other) {
            Some(Ordering::Less)
        } else if other.happens_before(self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

impl<const T: usize> Mergeable for DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    fn merge_into(&mut self, other: &Self) {
        for i in 0..T {
            if self.0[i] < other.0[i] {
                self.0[i] = other.0[i];
            }
        }
    }
}

impl<const T: usize> DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    pub fn new(vc: [i32; T]) -> Self {
        Self(vc)
    }
}

#[derive(Debug, Default, Eq, Clone, Deserialize, Serialize)]
pub struct SparseVC(HashMap<usize, i32>);
impl VCTrait for SparseVC {
    fn concurrent(&self, other: &Self) -> bool {
        self.partial_cmp(other).is_none()
    }

    fn is_equal(&self, other: &Self) -> bool {
        self == other
    }

    fn happens_before(&self, other: &Self) -> bool {
        self < other
    }

    fn privilege(&self, other: &Self) -> bool {
        assert!(self.concurrent(other));
        let writers = self.0.keys().chain(other.0.keys()).collect::<HashSet<_>>();
        let mut writers = writers.into_iter().collect::<Vec<_>>();
        writers.sort();
        for writer in writers {
            let self_val = self.0.get(writer).unwrap_or(&0);
            let other_val = other.0.get(writer).unwrap_or(&0);
            if self_val == other_val {
                continue;
            }
            return self_val > other_val;
        }
        panic!();
    }

    fn increment(&mut self, idx: usize) {
        match self.0.entry(idx) {
            Entry::Occupied(mut entry) => {
                *entry.get_mut() += 1;
            }
            Entry::Vacant(entry) => {
                entry.insert(1);
            }
        }
    }
}

impl Hash for SparseVC {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.keys().collect::<Vec<_>>().hash(state);
        self.0.values().collect::<Vec<_>>().hash(state);
    }
}

impl PartialEq for SparseVC {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd for SparseVC {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let writers = self.0.keys().chain(other.0.keys()).collect::<HashSet<_>>();
        let mut earlier = false;
        let mut later = false;
        for writer in writers {
            let self_val = self.0.get(writer).unwrap_or(&0);
            let other_val = other.0.get(writer).unwrap_or(&0);
            match self_val.cmp(other_val) {
                Ordering::Less => earlier = true,
                Ordering::Greater => later = true,
                Ordering::Equal => {}
            }
        }
        if earlier && !later {
            Some(Ordering::Less)
        } else if !earlier && later {
            Some(Ordering::Greater)
        } else if earlier && later {
            None
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl Mergeable for SparseVC {
    fn merge_into(&mut self, other: &Self) {
        for (writer, val) in other.0.iter() {
            match self.0.entry(*writer) {
                Entry::Occupied(mut entry) => {
                    if *entry.get() < *val {
                        *entry.get_mut() = *val;
                    }
                }
                Entry::Vacant(entry) => {
                    entry.insert(*val);
                }
            }
        }
    }

    fn merge(&self, other: &Self) -> Self {
        let mut vc: Self = self.clone();
        vc.merge_into(other);
        vc
    }
}

impl<const T: usize> DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    pub fn to_sparse(&self) -> SparseVC {
        let mut map = HashMap::default();
        for i in 0..T {
            if self.0[i] > 0 {
                map.insert(i, self.0[i]);
            }
        }
        SparseVC(map)
    }
}

impl<const T: usize> From<[i32; T]> for DenseVC<T>
where
    [i32; T]: Default + DeserializeOwned + Serialize,
{
    fn from(vc: [i32; T]) -> Self {
        Self::new(vc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use DenseVC as VC;

    macro_rules! assert_all {
        ($a1:ident, $a2:ident, $b1:ident, $b2:ident) => {
            assert_eq!($a1 == $a2, $b1 == $b2);
            assert_eq!($a1 < $a2, $b1 < $b2);
            assert_eq!($a1 <= $a2, $b1 <= $b2);
            assert_eq!($a1 > $a2, $b1 > $b2);
            assert_eq!($a1 >= $a2, $b1 >= $b2);
            assert_eq!($a1.concurrent(&$a2), $b1.concurrent(&$b2));
        };
    }

    #[test]
    fn test1() {
        let a = VC([1, 2]);
        let b = VC([1, 2]);
        assert_eq!(a, b);
        assert_eq!(a < b, false);
        assert_eq!(a > b, false);
        assert_eq!(a <= b, true);
        assert_eq!(a >= b, true);
        assert_eq!(a.concurrent(&b), false);
    }

    #[test]
    fn test2() {
        let a = VC([1, 2]);
        let b = VC([1, 3]);
        assert_eq!(a == b, false);
        assert_eq!(a < b, true);
        assert_eq!(a > b, false);
        assert_eq!(a <= b, true);
        assert_eq!(a >= b, false);
        assert_eq!(a.concurrent(&b), false);
    }

    #[test]
    fn test3() {
        let a = VC([2, 1]);
        let b = VC([1, 3]);
        assert_eq!(a == b, false);
        assert_eq!(a < b, false);
        assert_eq!(a > b, false);
        assert_eq!(a <= b, false);
        assert_eq!(a >= b, false);
        assert_eq!(a.concurrent(&b), true);
    }

    #[test]
    fn test4() {
        let mut a = VC([2, 1]);
        let b = VC([1, 3]);
        let c = a.merge(&b);
        a.merge_into(&b);
        assert_eq!(a, c);
        assert_eq!(c, VC([2, 3]));
    }

    #[test]
    #[should_panic]
    fn test5() {
        let a = VC([1, 1]);
        let b = VC([1, 3]);
        a.privilege(&b);
    }

    #[test]
    fn test6() {
        let a = VC([2, 1]);
        let b = VC([1, 3]);
        assert_eq!(a.privilege(&b), true);
    }

    #[test]
    fn test7() {
        let a1 = VC([2, 0, 3]);
        let a2 = VC([0, 1, 3]);
        let b1 = a1.to_sparse();
        let b2 = a2.to_sparse();
        assert_all!(a1, a2, b1, b2);
    }

    #[test]
    fn test8() {
        let a1 = VC([2, 0, 3]);
        let a2 = VC([0, 0, 3]);
        let b1 = a1.to_sparse();
        let b2 = a2.to_sparse();
        assert_all!(a1, a2, b1, b2);
    }

    #[test]
    fn test9() {
        let a1 = VC([0, 1, 0]);
        let a2 = VC([0, 1, 3]);
        let b1 = a1.to_sparse();
        let b2 = a2.to_sparse();
        assert_all!(a1, a2, b1, b2);
    }

    #[test]
    fn test10() {
        let a1 = VC([2, 2, 0]);
        let a2 = VC([0, 1, 3]);
        let b1 = a1.to_sparse();
        let b2 = a2.to_sparse();
        let c = b1.merge(&b2);
        assert_eq!(c, VC([2, 2, 3]).to_sparse());
    }
}
