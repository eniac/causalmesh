use rustc_hash::FxHashMap as HashMap;
use std::collections::hash_map::Entry;

pub trait Mergeable {
    fn merge_into(&mut self, other: &Self);

    fn merge(&self, other: &Self) -> Self
    where
        Self: Clone,
    {
        let mut c: Self = self.clone();
        c.merge_into(other);
        c
    }
}

pub trait MergeableNoDeps: Mergeable {
    fn merge_into_no_deps(&mut self, other: &Self);

    fn no_deps(&self) -> Self;
}

// e.g. merge two deps
impl<K, V> Mergeable for HashMap<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Mergeable + Clone,
{
    fn merge_into(&mut self, other: &Self) {
        for (k, v) in other.iter() {
            match self.entry(k.clone()) {
                Entry::Vacant(e) => {
                    e.insert(v.clone());
                }
                Entry::Occupied(mut e) => {
                    e.get_mut().merge_into(v);
                }
            }
        }
    }
}

// e.g. White merges map of updates
impl<K, V> MergeableNoDeps for HashMap<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: MergeableNoDeps + Clone,
{
    fn merge_into_no_deps(&mut self, other: &Self) {
        for (k, v) in other.iter() {
            match self.entry(k.clone()) {
                Entry::Vacant(e) => {
                    // discard deps
                    e.insert(v.no_deps());
                }
                Entry::Occupied(mut e) => {
                    e.get_mut().merge_into_no_deps(v);
                }
            }
        }
    }

    fn no_deps(&self) -> Self {
        todo!()
    }
}

pub trait InsertOrMerge<K, V>
where
    K: Eq + std::hash::Hash,
    V: Mergeable,
{
    fn insert_or_merge_ref(&mut self, k: K, v: &V)
    where
        V: Clone;
    fn insert_or_merge(&mut self, k: K, v: V);
}

impl<K, V> InsertOrMerge<K, V> for HashMap<K, V>
where
    K: Eq + std::hash::Hash,
    V: Mergeable,
{
    fn insert_or_merge_ref(&mut self, k: K, v: &V)
    where
        V: Clone,
    {
        match self.entry(k) {
            Entry::Vacant(e) => {
                e.insert(v.clone());
            }
            Entry::Occupied(mut e) => {
                e.get_mut().merge_into(v);
            }
        }
    }

    fn insert_or_merge(&mut self, k: K, v: V) {
        match self.entry(k) {
            Entry::Vacant(e) => {
                e.insert(v);
            }
            Entry::Occupied(mut e) => {
                e.get_mut().merge_into(&v);
            }
        }
    }
}

pub trait InsertOrMergeNoDeps<K, V>
where
    K: Eq + std::hash::Hash,
    V: MergeableNoDeps,
{
    fn insert_or_merge_no_deps(&mut self, k: K, v: V);
}

impl<K, V> InsertOrMergeNoDeps<K, V> for HashMap<K, V>
where
    K: Eq + std::hash::Hash,
    V: MergeableNoDeps,
{
    fn insert_or_merge_no_deps(&mut self, k: K, v: V) {
        match self.entry(k) {
            Entry::Vacant(e) => {
                e.insert(v.no_deps());
            }
            Entry::Occupied(mut e) => {
                e.get_mut().merge_into_no_deps(&v);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::*;
    use DenseVC as VC;

    #[test]
    fn test1() {
        let vc1 = VC([0, 1, 2]);
        let vc2 = VC([1, 0, 1]);
        let mut m: HashMap<i32, VC<3>> = HashMap::default();
        m.insert_or_merge(1, vc1);
        m.insert_or_merge_ref(1, &vc2);
        assert_eq!(m.len(), 1);
        assert_eq!(*m.get(&1).unwrap(), VC([1, 1, 2]));
    }

    #[test]
    fn test2() {
        let mut m1: HashMap<i32, VC<3>> = HashMap::default();
        let vc1 = VC([0, 1, 2]);
        let vc2 = VC([1, 0, 1]);
        m1.insert_or_merge_ref(1, &vc1);
        m1.insert_or_merge_ref(3, &vc2);
        let mut m2: HashMap<i32, VC<3>> = HashMap::default();
        m2.insert_or_merge(1, vc2);
        m2.insert_or_merge(2, vc1);
        let m3 = m1.merge(&m2);
        m1.merge_into(&m2);
        assert_eq!(m1, m3);
        assert_eq!(m1.len(), 3);
        assert_eq!(*m1.get(&1).unwrap(), VC([1, 1, 2]));
        assert_eq!(*m1.get(&2).unwrap(), VC([0, 1, 2]));
        assert_eq!(*m1.get(&3).unwrap(), VC([1, 0, 1]));
    }
}
